//! Ties decoding, classification and the Brillig scan together, applies
//! source provenance and justification markers, and decides the exit
//! status. Rendering is in `render`, baselines in `baseline`.

use std::collections::BTreeMap;

use crate::analysis::{self, Class, Context, Item, Kind, Origin};
use crate::artifact::{Artifact, EntryParam, Location, SourceFile};
use crate::brillig::{self, BrilligReport};

/// Marker that justifies a reported item when it appears in a `//`
/// comment followed by a reason. A marker after code justifies items on
/// that line only; a marker on a comment line justifies the statement that
/// directly follows the comment block it is in. It counts in a frame of
/// the item's call stack, and only in files the circuit author controls:
/// the entry package's source directory (minus any library tree) and
/// directories given with --allow-src. A dependency therefore cannot
/// justify its own items or the caller's.
pub const JUSTIFY_MARKER: &str = "total-lint: allow";

/// Justification text for entry-parameter range checks under
/// --allow-entry-ranges.
pub const ENTRY_RANGES_REASON: &str =
    "typed entry parameter (--allow-entry-ranges: the caller encodes inputs by the ABI)";

/// How a run treats provenance and justification.
#[derive(Clone, Debug, Default)]
pub struct Options {
    /// Absolute library source directories whose hint-class constraints
    /// are whitelisted.
    pub lib_dirs: Vec<String>,
    /// Extra absolute directories whose justification markers count.
    pub allow_dirs: Vec<String>,
    /// Justify the compiler's range checks on typed entry parameters.
    pub allow_entry_ranges: bool,
}

/// A justification marker in an honoured file.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MarkerRef {
    pub file: u32,
    /// 1-based line of the marker.
    pub line: usize,
}

/// Why a reported item or abort site does not count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Justification {
    pub reason: String,
    /// The marker that gave it; None for --allow-entry-ranges.
    pub marker: Option<MarkerRef>,
}

pub struct Reported {
    pub item: Item,
    /// Call stack, outermost frame first.
    pub stack: Vec<Location>,
    /// Index into `stack` of the frame that decided the provenance.
    pub attributed: Option<usize>,
    pub justified: Option<Justification>,
    /// Accepted by the baseline file.
    pub baselined: bool,
}

impl Reported {
    /// Counts towards the exit status: reported, unjustified, not in the
    /// baseline.
    pub fn counts(&self) -> bool {
        self.unjustified() && !self.baselined
    }

    pub fn unjustified(&self) -> bool {
        self.item.class.is_reported() && self.justified.is_none()
    }
}

/// Call stack and provenance of one ACIR opcode.
struct Frame {
    stack: Vec<Location>,
    origin: Origin,
    attributed: Option<usize>,
}

pub struct TrapReport {
    pub site: brillig::TrapSite,
    pub stack: Vec<Location>,
    pub attributed: Option<usize>,
    pub origin: Origin,
    pub justified: Option<Justification>,
    pub baselined: bool,
}

impl TrapReport {
    /// A reachable site outside the library, or of a kind the library
    /// does not whitelist (note-width).
    pub fn reported(&self) -> bool {
        !self.site.guarded_by_callers
            && (self.origin != Origin::Library || !self.site.kind.whitelisted_in_library())
    }

    /// A reported site with no justification.
    pub fn unjustified(&self) -> bool {
        self.reported() && self.justified.is_none()
    }

    pub fn counts(&self) -> bool {
        self.unjustified() && !self.baselined
    }
}

pub struct MpcOpReport {
    pub site: brillig::MpcOpSite,
    pub stack: Vec<Location>,
    pub attributed: Option<usize>,
    pub origin: Origin,
}

/// What one library directory matched among the artifact's source files.
pub struct LibMatch {
    pub dir: String,
    pub files: usize,
}

/// A marker in an honoured file and how many items it justified.
#[derive(Clone, Debug)]
pub struct MarkerUse {
    pub at: MarkerRef,
    pub path: String,
    pub reason: String,
    pub items: usize,
}

pub struct Outcome<'a> {
    pub artifact: &'a Artifact,
    pub options: Options,
    pub lib_matches: Vec<LibMatch>,
    /// Problems with the arguments that do not stop the run.
    pub warnings: Vec<String>,
    /// Directory of the entry function's source file; markers there count.
    pub root_src: Option<String>,
    pub items: Vec<Reported>,
    pub brillig_calls: Vec<analysis::BrilligCallSite>,
    pub acir_calls: Vec<analysis::AcirCallSite>,
    pub traps: Vec<TrapReport>,
    pub brillig_stats: BrilligReport,
    /// Brillig opcodes co-noir's MPC VM cannot execute (--brillig-ops).
    pub mpc_ops: Vec<MpcOpReport>,
    /// Every marker in an honoured file, with the items it justified here.
    pub markers: Vec<MarkerUse>,
}

/// Offsets of the `if` keyword and its `{` for the block of `source` that
/// holds offset `after`, walking out of `else` blocks to the `if` that owns
/// them; None unless that block opens with an `if ... {` line whose brace
/// lies past offset `before`.
fn if_keyword(source: &str, before: usize, after: usize) -> Option<(usize, usize)> {
    let src = source.as_bytes();
    let mut at = after.min(src.len());
    loop {
        let brace = open_brace(src, at)?;
        if brace <= before {
            return None;
        }
        let line_start = source[..brace].rfind('\n').map_or(0, |i| i + 1);
        let head = &source[line_start..brace];
        if let Some(kw) = last_word(head, "if") {
            return Some((line_start + kw, brace));
        }
        // `} else {`: go on from the closing brace before `else`.
        if head.trim() != "} else" {
            return None;
        }
        at = line_start + head.find('}')?;
    }
}

/// Offset of the unmatched `{` that opens the block holding offset `at`.
fn open_brace(src: &[u8], at: usize) -> Option<usize> {
    let mut depth = 0usize;
    for i in (0..at).rev() {
        match src[i] {
            b'}' => depth += 1,
            b'{' if depth == 0 => return Some(i),
            b'{' => depth -= 1,
            _ => {}
        }
    }
    None
}

/// Byte offset of the last occurrence of `word` in `text` as a whole word.
fn last_word(text: &str, word: &str) -> Option<usize> {
    let ident = |c: char| c.is_alphanumeric() || c == '_';
    text.match_indices(word)
        .filter(|(i, _)| {
            let before = text[..*i].chars().next_back();
            let after = text[i + word.len()..].chars().next();
            !before.is_some_and(ident) && !after.is_some_and(ident)
        })
        .map(|(i, _)| i)
        .last()
}

pub(crate) fn is_std(path: &str) -> bool {
    path.starts_with("std/") || path == "std"
}

impl<'a> Outcome<'a> {
    /// Provenance of a call stack: the innermost frame outside std decides.
    fn attribute(
        artifact: &Artifact,
        lib_dirs: &[String],
        stack: &[Location],
    ) -> (Origin, Option<usize>) {
        for (i, loc) in stack.iter().enumerate().rev() {
            let Some(file) = artifact.files.get(&loc.file) else {
                continue;
            };
            if is_std(&file.path) {
                continue;
            }
            let lib = lib_dirs.iter().any(|d| under_dir(&file.path, d));
            return (if lib { Origin::Library } else { Origin::User }, Some(i));
        }
        (Origin::Compiler, None)
    }

    /// The `if` a ConditionalMov comes from, as a call stack, when the
    /// debug info gives the cmov no location of its own: `before` is the
    /// stack of the nearest located opcode before it, `after` that of the
    /// first one after it. Found in the source: the innermost block that
    /// holds an `after` frame must open with `if ... {` (or an `else`
    /// block of one) after the matching `before` frame begins, in the same
    /// function frame. None when that does not hold; the caller keeps
    /// `before`.
    fn enclosing_if(
        artifact: &Artifact,
        before: &[Location],
        after: &[Location],
    ) -> Option<Vec<Location>> {
        for k in (0..after.len()).rev() {
            let a = after[k];
            if before.len() <= k || before[..k] != after[..k] {
                continue;
            }
            let b = before[k];
            if b.file != a.file || b.start >= a.start {
                continue;
            }
            let Some(file) = artifact.files.get(&a.file) else {
                continue;
            };
            if let Some((start, _)) = if_keyword(&file.source, b.start as usize, a.start as usize) {
                let mut stack = after[..k].to_vec();
                stack.push(Location {
                    file: a.file,
                    start: start as u32,
                });
                return Some(stack);
            }
        }
        None
    }

    pub(crate) fn acir_stack(artifact: &Artifact, function: usize, opcode: usize) -> Vec<Location> {
        let Some(d) = artifact.debug.get(function) else {
            return Vec::new();
        };
        d.acir_locations
            .get(&opcode)
            .map(|id| d.call_stack(*id))
            .unwrap_or_default()
    }

    fn brillig_stack(artifact: &Artifact, brillig: u32, pc: usize) -> Vec<Location> {
        for d in &artifact.debug {
            if let Some(id) = d.brillig_locations.get(&brillig).and_then(|m| m.get(&pc)) {
                return d.call_stack(*id);
            }
        }
        Vec::new()
    }

    /// Directory holding the entry function's own source: the file of the
    /// outermost frame of the first located opcode of function 0.
    fn root_src_dir(artifact: &Artifact) -> Option<String> {
        let d = artifact.debug.first()?;
        let path = d.acir_locations.values().find_map(|id| {
            let stack = d.call_stack(*id);
            let first = stack.first()?;
            artifact.files.get(&first.file).map(|f| f.path.clone())
        })?;
        if is_std(&path) {
            return None;
        }
        let (dir, _) = path.rsplit_once('/')?;
        Some(dir.to_string())
    }

    fn marker_allowed(&self, path: &str) -> bool {
        let in_root = self.root_src.as_deref().is_some_and(|r| under_dir(path, r))
            && !self.options.lib_dirs.iter().any(|l| under_dir(path, l));
        in_root || self.options.allow_dirs.iter().any(|d| under_dir(path, d))
    }

    /// The marker justifying a stack: the innermost honoured frame whose
    /// line carries a marker after code, or whose statement follows a
    /// comment block holding one.
    fn justification(&self, stack: &[Location]) -> Option<Justification> {
        for loc in stack.iter().rev() {
            let Some(file) = self.artifact.files.get(&loc.file) else {
                continue;
            };
            if !self.marker_allowed(&file.path) {
                continue;
            }
            let (line, _) = file.line_col(loc.start);
            if let Some((at, reason)) = marker_for_line(file, line) {
                return Some(Justification {
                    reason,
                    marker: Some(MarkerRef {
                        file: loc.file,
                        line: at,
                    }),
                });
            }
        }
        None
    }

    /// Run with the given library directories (absolute) and no other
    /// options.
    pub fn run(artifact: &'a Artifact, lib_dirs: Vec<String>) -> Outcome<'a> {
        Self::run_with(
            artifact,
            Options {
                lib_dirs,
                ..Options::default()
            },
        )
    }

    /// Call stack and provenance of every ACIR opcode.
    fn frames(artifact: &Artifact, lib_dirs: &[String]) -> Vec<Vec<Frame>> {
        artifact
            .program
            .functions
            .iter()
            .enumerate()
            .map(|(f, circuit)| {
                (0..circuit.opcodes.len())
                    .map(|op| {
                        let stack = Self::acir_stack(artifact, f, op);
                        let (origin, attributed) = Self::attribute(artifact, lib_dirs, &stack);
                        Frame {
                            stack,
                            origin,
                            attributed,
                        }
                    })
                    .collect()
            })
            .collect()
    }

    fn classify(artifact: &Artifact, frames: &[Vec<Frame>]) -> analysis::Analysis {
        let messages = |sel: u64| artifact.error_message(sel);
        let origin = |f: usize, op: usize| {
            frames
                .get(f)
                .and_then(|v| v.get(op))
                .map_or(Origin::Compiler, |x| x.origin)
        };
        let entry_params: BTreeMap<u32, EntryParam> = artifact
            .entry_params()
            .into_iter()
            .enumerate()
            .map(|(i, p)| (i as u32, p))
            .collect();
        let directives = analysis::directives(&artifact.program);
        let ctx = Context {
            program: &artifact.program,
            entry_params: &entry_params,
            messages: &messages,
            origin: &origin,
            directives: &directives,
        };
        analysis::analyse(&ctx)
    }

    fn option_warnings(artifact: &Artifact, options: &Options) -> (Vec<LibMatch>, Vec<String>) {
        let mut warnings = Vec::new();
        let lib_matches: Vec<LibMatch> = options
            .lib_dirs
            .iter()
            .map(|d| LibMatch {
                dir: d.clone(),
                files: artifact
                    .files
                    .values()
                    .filter(|f| under_dir(&f.path, d))
                    .count(),
            })
            .collect();
        for m in &lib_matches {
            if m.files == 0 {
                warnings.push(format!(
                    "library directory {} holds no source file of this artifact",
                    m.dir
                ));
            }
        }
        for d in &options.allow_dirs {
            if !artifact.files.values().any(|f| under_dir(&f.path, d)) {
                warnings.push(format!(
                    "--allow-src {d}: no source file of this artifact lies under it"
                ));
            }
        }
        (lib_matches, warnings)
    }

    pub fn run_with(artifact: &'a Artifact, options: Options) -> Outcome<'a> {
        let frames = Self::frames(artifact, &options.lib_dirs);
        let analysis = Self::classify(artifact, &frames);
        let (lib_matches, warnings) = Self::option_warnings(artifact, &options);
        let mut outcome = Outcome {
            artifact,
            root_src: Self::root_src_dir(artifact),
            options,
            lib_matches,
            warnings,
            items: Vec::new(),
            brillig_calls: Vec::new(),
            acir_calls: Vec::new(),
            traps: Vec::new(),
            brillig_stats: BrilligReport::default(),
            mpc_ops: Vec::new(),
            markers: Vec::new(),
        };
        outcome.items = analysis
            .items
            .into_iter()
            .map(|item| {
                let (stack, attributed) = frames
                    .get(item.function)
                    .and_then(|v| v.get(item.opcode))
                    .map(|x| (x.stack.clone(), x.attributed))
                    .unwrap_or_default();
                let justified = outcome.item_justification(&item, &stack);
                Reported {
                    item,
                    stack,
                    attributed,
                    justified,
                    baselined: false,
                }
            })
            .collect();
        outcome.scan_brillig(&analysis.brillig_calls);
        outcome.brillig_calls = analysis.brillig_calls;
        outcome.acir_calls = analysis.acir_calls;
        outcome.markers = outcome.marker_uses();
        outcome
    }

    fn item_justification(&self, item: &Item, stack: &[Location]) -> Option<Justification> {
        if !item.class.is_reported() {
            return None;
        }
        if item.entry_param && item.kind == Kind::Range && self.options.allow_entry_ranges {
            return Some(Justification {
                reason: ENTRY_RANGES_REASON.to_string(),
                marker: None,
            });
        }
        self.justification(stack)
    }

    /// Abort sites and the opcodes co-noir cannot execute, with their
    /// stacks and provenance.
    fn scan_brillig(&mut self, calls: &[analysis::BrilligCallSite]) {
        let artifact = self.artifact;
        let lib_dirs = self.options.lib_dirs.clone();
        let selectors: BTreeMap<u64, String> = artifact.error_selectors().into_iter().collect();
        let functions: Vec<(String, &[acir::brillig::Opcode<acir::FieldElement>])> = artifact
            .program
            .unconstrained_functions
            .iter()
            .map(|b| (b.function_name.clone(), b.bytecode.as_slice()))
            .collect();
        let has_location = |id: u32, pc: usize| {
            artifact.debug.iter().any(|d| {
                d.brillig_locations
                    .get(&id)
                    .is_some_and(|m| m.contains_key(&pc))
            })
        };
        let scan = brillig::scan(&functions, calls, &selectors, &has_location);
        self.traps = scan
            .sites
            .iter()
            .map(|site| {
                let stack = site
                    .location_pc
                    .map(|pc| Self::brillig_stack(artifact, site.brillig, pc))
                    .unwrap_or_default();
                let (origin, attributed) = Self::attribute(artifact, &lib_dirs, &stack);
                TrapReport {
                    site: site.clone(),
                    justified: self.justification(&stack),
                    stack,
                    attributed,
                    origin,
                    baselined: false,
                }
            })
            .collect();
        self.mpc_ops = brillig::mpc_unsupported_ops(&functions, &has_location)
            .into_iter()
            .map(|site| {
                let stack = site
                    .location_pc
                    .map(|pc| Self::brillig_stack(artifact, site.brillig, pc))
                    .unwrap_or_default();
                let stack = site
                    .next_location_pc
                    .and_then(|pc| {
                        let after = Self::brillig_stack(artifact, site.brillig, pc);
                        Self::enclosing_if(artifact, &stack, &after)
                    })
                    .unwrap_or(stack);
                let (origin, attributed) = Self::attribute(artifact, &lib_dirs, &stack);
                MpcOpReport {
                    site,
                    stack,
                    attributed,
                    origin,
                }
            })
            .collect();
        self.brillig_stats = scan;
    }

    /// Every marker in an honoured file, with the number of reported items
    /// and abort sites it justified.
    fn marker_uses(&self) -> Vec<MarkerUse> {
        let mut used: BTreeMap<MarkerRef, usize> = BTreeMap::new();
        let refs = self
            .items
            .iter()
            .filter_map(|r| r.justified.as_ref())
            .chain(self.traps.iter().filter_map(|t| t.justified.as_ref()))
            .filter_map(|j| j.marker);
        for m in refs {
            *used.entry(m).or_default() += 1;
        }
        let mut out = Vec::new();
        for (id, file) in self.artifact.files.iter() {
            if !self.marker_allowed(&file.path) {
                continue;
            }
            for line in 1..=file.line_count() {
                if let Some(reason) = marker_reason(file.line_text(line)) {
                    let at = MarkerRef { file: *id, line };
                    out.push(MarkerUse {
                        at,
                        path: file.path.clone(),
                        reason,
                        items: used.get(&at).copied().unwrap_or(0),
                    });
                }
            }
        }
        out
    }

    pub fn marker_dirs(&self) -> Vec<String> {
        let mut dirs: Vec<String> = self.root_src.iter().cloned().collect();
        dirs.extend(self.options.allow_dirs.iter().cloned());
        dirs
    }

    pub fn class_counts(&self) -> BTreeMap<Class, usize> {
        let mut m: BTreeMap<Class, usize> = Class::ALL.iter().map(|c| (*c, 0)).collect();
        for r in &self.items {
            *m.entry(r.item.class).or_default() += 1;
        }
        m
    }

    /// Reported ACIR items without a justification (baselined or not).
    pub fn unjustified(&self) -> usize {
        self.items.iter().filter(|r| r.unjustified()).count()
    }

    pub fn justified(&self) -> usize {
        self.items
            .iter()
            .filter(|r| r.item.class.is_reported() && r.justified.is_some())
            .count()
    }

    /// Reported abort sites (reachable, outside the library or of a kind
    /// it does not whitelist) without a justification.
    pub fn unjustified_traps(&self) -> usize {
        self.traps.iter().filter(|t| t.unjustified()).count()
    }

    pub fn baselined(&self) -> usize {
        self.items.iter().filter(|r| r.baselined).count()
            + self.traps.iter().filter(|t| t.baselined).count()
    }

    /// Items and abort sites that count towards the exit status.
    pub fn failures(&self) -> usize {
        self.items.iter().filter(|r| r.counts()).count()
            + self.traps.iter().filter(|t| t.counts()).count()
    }

    pub fn exit_code(&self) -> i32 {
        if self.failures() > 0 { 1 } else { 0 }
    }

    /// Reachable opcodes co-noir's MPC VM cannot execute.
    pub(crate) fn live_mpc_ops(&self) -> usize {
        self.mpc_ops.iter().filter(|o| o.site.reachable).count()
    }

    /// Exit status of the --brillig-ops report: 1 when any reachable
    /// opcode co-noir's MPC VM cannot execute remains.
    pub fn mpc_ops_exit_code(&self) -> i32 {
        if self.live_mpc_ops() > 0 { 1 } else { 0 }
    }

    pub(crate) fn live_traps(&self) -> usize {
        self.traps
            .iter()
            .filter(|t| !t.site.guarded_by_callers)
            .count()
    }
}

/// `path` lies inside directory `dir`.
pub fn under_dir(path: &str, dir: &str) -> bool {
    let dir = dir.trim_end_matches('/');
    path.strip_prefix(dir)
        .is_some_and(|rest| rest.starts_with('/'))
}

/// Absolute form of a directory argument, without `.`/`..` parts or a
/// trailing slash; relative arguments resolve against the current
/// directory.
pub fn normalise_dir(dir: &str) -> Option<String> {
    let p = std::path::Path::new(dir);
    let abs = if p.is_absolute() {
        p.to_path_buf()
    } else {
        std::env::current_dir().ok()?.join(p)
    };
    let mut parts: Vec<String> = Vec::new();
    for c in abs.components() {
        match c {
            std::path::Component::Normal(s) => parts.push(s.to_string_lossy().into_owned()),
            std::path::Component::ParentDir => {
                parts.pop();
            }
            _ => {}
        }
    }
    Some(format!("/{}", parts.join("/")))
}

/// Resolve a directory argument: absolute, normalised, and existing.
pub fn resolve_dir(flag: &str, dir: &str) -> Result<String, String> {
    let n = normalise_dir(dir)
        .ok_or_else(|| format!("{flag} {dir:?}: no current directory to resolve it against"))?;
    if !std::path::Path::new(&n).is_dir() {
        return Err(format!("{flag} {dir:?}: {n} is not a directory"));
    }
    Ok(n)
}

/// The reason after a justification marker, when the marker sits in a `//`
/// comment (not inside a string literal) and a reason follows it.
pub(crate) fn marker_reason(line: &str) -> Option<String> {
    let comment = comment_start(line).map(|i| &line[i + 2..])?;
    let pos = comment.find(JUSTIFY_MARKER)?;
    let reason = comment[pos + JUSTIFY_MARKER.len()..]
        .trim()
        .trim_start_matches(':')
        .trim();
    (!reason.is_empty()).then(|| reason.to_string())
}

/// Byte offset of the `//` that starts a comment, outside string literals.
fn comment_start(line: &str) -> Option<usize> {
    let bytes = line.as_bytes();
    let mut in_str = false;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'\\' if in_str => i += 1,
            b'"' => in_str = !in_str,
            b'/' if !in_str && bytes.get(i + 1) == Some(&b'/') => return Some(i),
            _ => {}
        }
        i += 1;
    }
    None
}

/// The line with its comment removed, trimmed.
fn code_part(line: &str) -> &str {
    match comment_start(line) {
        Some(i) => line[..i].trim(),
        None => line.trim(),
    }
}

/// How far up a statement's first line is searched for.
const MAX_STATEMENT_LINES: usize = 32;

/// The marker that justifies code on `line`: one after code on the line
/// itself, or one in the comment block directly above the statement that
/// contains the line. A statement starts after a line ending in `;`, `{`
/// or `}`, a blank line, or a comment line.
fn marker_for_line(file: &SourceFile, line: usize) -> Option<(usize, String)> {
    if let Some(reason) = marker_reason(file.line_text(line)) {
        return Some((line, reason));
    }
    let mut start = line;
    for _ in 0..MAX_STATEMENT_LINES {
        if start <= 1 {
            break;
        }
        let prev = code_part(file.line_text(start - 1));
        if prev.is_empty() || prev.ends_with(';') || prev.ends_with('{') || prev.ends_with('}') {
            break;
        }
        start -= 1;
    }
    let mut k = start;
    while k > 1 {
        k -= 1;
        let text = file.line_text(k);
        if !text.trim_start().starts_with("//") {
            break;
        }
        if let Some(reason) = marker_reason(text) {
            return Some((k, reason));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::{
        if_keyword, marker_for_line, marker_reason, normalise_dir, resolve_dir, under_dir,
    };
    use crate::artifact::SourceFile;

    #[test]
    fn if_keyword_finds_the_if_between_two_statements() {
        let src = "fn f() {\n    let bit = !r.lt(d);\n    if bit {\n        r = r - d;\n    }\n}\n";
        let before = src.find("let bit").unwrap();
        let after = src.find("r = r - d").unwrap();
        let (kw, brace) = if_keyword(src, before, after).unwrap();
        assert_eq!(&src[kw..=brace], "if bit {");
        // The `if` must come after the preceding statement.
        assert_eq!(if_keyword(src, after - 1, after), None);
        // An else block belongs to its `if`.
        let src =
            "    let c = x;\n    if c {\n        a = 1;\n    } else {\n        a = { 2 };\n    }\n";
        let before = src.find("let c").unwrap();
        let after = src.find("a = {").unwrap();
        let (kw, _) = if_keyword(src, before, after).unwrap();
        assert_eq!(&src[kw..kw + 4], "if c");
        // A loop body is not an `if`.
        let src = "    let c = x;\n    for i in 0..3 {\n        a = i;\n    }\n";
        let after = src.find("a = i").unwrap();
        assert_eq!(if_keyword(src, 0, after), None);
        // `iffy` is not the keyword.
        let src = "    let c = x;\n    let iffy = {\n        a\n    };\n";
        assert_eq!(if_keyword(src, 0, src.find("a\n").unwrap()), None);
    }

    #[test]
    fn markers_count_only_in_comments() {
        assert_eq!(
            marker_reason("    // total-lint: allow checked by caller").as_deref(),
            Some("checked by caller")
        );
        assert_eq!(
            marker_reason("assert(x == 1); // total-lint: allow: ok").as_deref(),
            Some("ok")
        );
        assert_eq!(
            marker_reason("    assert(x != 9, \"total-lint: allow fake\");"),
            None
        );
        assert_eq!(
            marker_reason("    let s = \"// total-lint: allow fake\";"),
            None
        );
        assert_eq!(marker_reason("    // total-lint: allow"), None);
        assert_eq!(
            marker_reason("    let s = \"a\\\"b\"; // total-lint: allow real"),
            Some("real".to_string())
        );
    }

    fn file(src: &str) -> SourceFile {
        SourceFile::new("/p/src/main.nr".into(), src.into())
    }

    #[test]
    fn a_trailing_marker_justifies_only_its_own_line() {
        let f = file(
            "fn main(x: Field, y: Field) {\n    assert(x != 0); // total-lint: allow x is never zero\n    assert(y != 0);\n}\n",
        );
        assert_eq!(
            marker_for_line(&f, 2),
            Some((2, "x is never zero".to_string()))
        );
        assert_eq!(marker_for_line(&f, 3), None);
    }

    #[test]
    fn a_comment_marker_justifies_the_next_statement_only() {
        let f = file(concat!(
            "fn main(x: Field, y: Field) {\n",
            "    // total-lint: allow reviewed\n",
            "    // (more words)\n",
            "    assert(\n",
            "        x != 0,\n",
            "    );\n",
            "    assert(y != 0);\n",
            "}\n",
        ));
        assert_eq!(marker_for_line(&f, 4), Some((2, "reviewed".to_string())));
        assert_eq!(marker_for_line(&f, 5), Some((2, "reviewed".to_string())));
        assert_eq!(marker_for_line(&f, 7), None);
        // A blank line ends the comment block's reach.
        let f = file("    // total-lint: allow reviewed\n\n    assert(x != 0);\n");
        assert_eq!(marker_for_line(&f, 3), None);
    }

    #[test]
    fn directories_match_whole_components() {
        assert!(under_dir("/a/pkg/src/main.nr", "/a/pkg/src"));
        assert!(under_dir("/a/pkg/src/main.nr", "/a/pkg/src/"));
        assert!(!under_dir("/a/pkg/src2/main.nr", "/a/pkg/src"));
        assert!(!under_dir("/a/pkg/src", "/a/pkg/src"));
        assert!(!under_dir("/x/vendor/total/src/lib.nr", "/repo/total/src"));
        assert_eq!(normalise_dir("/a/b/../c/./d/").as_deref(), Some("/a/c/d"));
    }

    #[test]
    fn library_directories_must_exist() {
        let here = env!("CARGO_MANIFEST_DIR");
        assert_eq!(resolve_dir("--lib-src", here).as_deref(), Ok(here));
        let err = resolve_dir("--lib-src", &format!("{here}/no-such-dir")).unwrap_err();
        assert!(err.contains("is not a directory"), "{err}");
    }
}
