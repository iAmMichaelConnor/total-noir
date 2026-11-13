//! Human and JSON rendering of outcomes.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use serde_json::{Value, json};

use crate::analysis::{Class, Origin, Pattern};
use crate::artifact::Location;
use crate::brillig::TrapKind;
use crate::report::{Justification, MarkerUse, Outcome, Reported, TrapReport};

/// What to show.
#[derive(Clone, Debug, Default)]
pub struct View {
    /// One line per opcode instead of one per source line and class.
    pub verbose: bool,
    pub explain: bool,
    /// Counts only.
    pub summary: bool,
    /// Classes listed; None lists every class but definition and
    /// neutralised.
    pub classes: Option<BTreeSet<Class>>,
}

impl View {
    pub fn shows(&self, c: Class) -> bool {
        match &self.classes {
            Some(set) => set.contains(&c),
            None => !matches!(c, Class::Definition | Class::Neutralised),
        }
    }
}

fn origin_name(o: Origin) -> &'static str {
    match o {
        Origin::Library => "library",
        Origin::User => "user",
        Origin::Compiler => "compiler",
    }
}

pub fn display_path(path: &str) -> String {
    if let Ok(cwd) = std::env::current_dir()
        && let Ok(rest) = std::path::Path::new(path).strip_prefix(&cwd)
    {
        return rest.display().to_string();
    }
    path.to_string()
}

/// `name[3].x[0]` -> `name[*].x[*]`: entry parameters of one array group.
fn group_label(label: &str) -> String {
    let mut out = String::new();
    let mut in_index = false;
    for c in label.chars() {
        match c {
            '[' => {
                in_index = true;
                out.push_str("[*");
            }
            ']' => {
                in_index = false;
                out.push(']');
            }
            c if in_index && c.is_ascii_digit() => {}
            c => out.push(c),
        }
    }
    out
}

fn trap_why(kind: TrapKind, detail: &str, origin: Origin) -> String {
    let base = match kind {
        TrapKind::Trap => {
            "an explicit trap (failed assert, overflow or bounds check, or unreachable code) that the walk could not rule out; whether some argument reaches it is not decided"
        }
        TrapKind::DivisionByZero => "division aborts witness generation when the divisor is zero",
        TrapKind::CurveOperation => "a curve operation aborts on invalid points",
        TrapKind::Oracle => "an oracle call aborts when the executor cannot answer it",
        TrapKind::Radix => {
            "a radix decomposition aborts when the input needs more limbs than requested"
        }
        TrapKind::NoteWidth => {
            "a pending note wider than aztec-nr v6's MAX_NOTE_PACKED_LEN makes the PXE refuse every later getNotes answer at its storage slot in the same transaction, failing an honest reader; the #[note] macro refuses such widths, so only hand-written note code emits one"
        }
    };
    let who = match origin {
        Origin::Library if !kind.whitelisted_in_library() => {
            "; in library code, where this kind of site is not whitelisted"
        }
        Origin::Library => "; in library hint code, which must be abort-free for every argument",
        Origin::User => "",
        Origin::Compiler => "; compiler-generated code with no package source location",
    };
    format!("{base} ({detail}){who}")
}

/// Status of a finding, most severe first.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Status {
    Fails,
    Baselined,
    Justified(String),
    Listed,
}

impl Status {
    fn of(reported: bool, justified: &Option<Justification>, baselined: bool) -> Status {
        match justified {
            Some(j) => Status::Justified(j.reason.clone()),
            None if !reported => Status::Listed,
            None if baselined => Status::Baselined,
            None => Status::Fails,
        }
    }

    fn text(&self) -> String {
        match self {
            Status::Fails | Status::Listed => String::new(),
            Status::Baselined => "  [baseline]".into(),
            Status::Justified(r) => format!("  [justified: {r}]"),
        }
    }
}

/// One output line of the grouped listing.
struct Group {
    count: usize,
    kinds: BTreeMap<&'static str, usize>,
    message: Option<String>,
}

impl Outcome<'_> {
    fn loc_text(&self, loc: &Location) -> String {
        let Some(file) = self.artifact.files.get(&loc.file) else {
            return format!("<file {}>", loc.file);
        };
        let (line, col) = file.line_col(loc.start);
        format!("{}:{line}:{col}", display_path(&file.path))
    }

    /// `path:line` and the trimmed source line of a location.
    fn line_ref(&self, loc: &Location) -> (String, String) {
        let Some(file) = self.artifact.files.get(&loc.file) else {
            return (format!("<file {}>", loc.file), String::new());
        };
        let (line, _) = file.line_col(loc.start);
        (
            format!("{}:{line}", display_path(&file.path)),
            file.line_text(line).trim().to_string(),
        )
    }

    fn source_line(&self, loc: &Location) -> String {
        let Some(file) = self.artifact.files.get(&loc.file) else {
            return String::new();
        };
        let (line, _) = file.line_col(loc.start);
        format!("{line:>6} | {}", file.line_text(line).trim_end())
    }

    fn path(&self, file: u32) -> String {
        self.artifact
            .files
            .get(&file)
            .map(|f| f.path.clone())
            .unwrap_or_else(|| format!("<file {file}>"))
    }

    fn loc_json(&self, loc: &Location) -> Value {
        let (line, col) = self
            .artifact
            .files
            .get(&loc.file)
            .map(|f| f.line_col(loc.start))
            .unwrap_or((0, 0));
        json!({ "file": self.path(loc.file), "line": line, "column": col })
    }

    fn justification_json(&self, j: &Option<Justification>) -> Value {
        match j {
            None => Value::Null,
            Some(j) => json!({
                "reason": j.reason,
                "marker": j.marker.map(|m| json!({ "file": self.path(m.file), "line": m.line })),
            }),
        }
    }

    /// Location lines for one stack: the innermost frame, plus the frame
    /// that decided provenance when that is a different one.
    fn where_lines(&self, stack: &[Location], attributed: Option<usize>, out: &mut String) {
        let Some(inner) = stack.last() else {
            let _ = writeln!(out, "         (no source location)");
            return;
        };
        let _ = writeln!(out, "{}", self.source_line(inner));
        if let Some(a) = attributed
            && a + 1 != stack.len()
        {
            let _ = writeln!(out, "         from {}", self.loc_text(&stack[a]));
            let _ = writeln!(out, "{}", self.source_line(&stack[a]));
        }
    }

    fn opcode_count(&self) -> usize {
        self.artifact
            .program
            .functions
            .iter()
            .map(|f| f.opcodes.len())
            .sum()
    }

    fn header(&self, out: &mut String) {
        let program = &self.artifact.program;
        let _ = writeln!(out, "noir {}", self.artifact.noir_version);
        let libs: Vec<String> = self
            .lib_matches
            .iter()
            .map(|m| format!("{} ({} file(s))", m.dir, m.files))
            .collect();
        let _ = writeln!(
            out,
            "library directories (hint-class constraints whitelisted): {}",
            if libs.is_empty() {
                "none".to_string()
            } else {
                libs.join(", ")
            }
        );
        let dirs = self.marker_dirs();
        let _ = writeln!(
            out,
            "justification markers honoured under: {}",
            if dirs.is_empty() {
                "(none)".to_string()
            } else {
                dirs.join(", ")
            }
        );
        if self.options.allow_entry_ranges {
            let _ = writeln!(
                out,
                "typed entry-parameter range checks: justified (--allow-entry-ranges)"
            );
        }
        let _ = writeln!(
            out,
            "{} ACIR function(s), {} opcodes; {} Brillig function(s)",
            program.functions.len(),
            self.opcode_count(),
            program.unconstrained_functions.len()
        );
    }

    /// Items grouped by the source line that decided provenance and by
    /// class, one line each.
    fn grouped_items(&self, view: &View, out: &mut String) {
        let mut groups: BTreeMap<(Status, Class, String, String), Group> = BTreeMap::new();
        for r in self.items.iter().filter(|r| view.shows(r.item.class)) {
            let it = &r.item;
            let status = Status::of(it.class.is_reported(), &r.justified, r.baselined);
            let (loc, text) = match r.attributed.map(|i| r.stack[i]).or(r.stack.last().copied()) {
                Some(l) => self.line_ref(&l),
                None if it.entry_param => (
                    "(entry-point ABI check)".to_string(),
                    group_label(&it.label),
                ),
                None => ("(no location)".to_string(), group_label(&it.label)),
            };
            let g = groups
                .entry((status, it.class, loc, text))
                .or_insert(Group {
                    count: 0,
                    kinds: BTreeMap::new(),
                    message: None,
                });
            g.count += 1;
            *g.kinds.entry(it.kind.name()).or_default() += 1;
            if g.message.is_none() {
                g.message = it.message.clone();
            }
        }
        let _ = writeln!(
            out,
            "\nitems ({} line(s); one per source line and class, --verbose for every opcode):",
            groups.len()
        );
        for ((status, class, loc, text), g) in &groups {
            let kinds: Vec<String> = g.kinds.iter().map(|(k, n)| format!("{k} {n}")).collect();
            let mut line = format!(
                "{:>6}  {:<25} {loc}  ({})",
                g.count,
                class.name(),
                kinds.join(", ")
            );
            if !text.is_empty() {
                let _ = write!(line, "  {text}");
            }
            if let Some(m) = &g.message {
                let _ = write!(line, "  {m:?}");
            }
            line.push_str(&status.text());
            let _ = writeln!(out, "{line}");
        }
    }

    fn verbose_items(&self, view: &View, out: &mut String) {
        let _ = writeln!(out, "\nitems (every opcode):");
        for r in self.items.iter().filter(|r| view.shows(r.item.class)) {
            self.verbose_item(r, view.explain, out);
        }
    }

    fn verbose_item(&self, r: &Reported, explain: bool, out: &mut String) {
        let it = &r.item;
        let mut line = format!(
            "f{} #{:<5} {:<17} {:<26}",
            it.function,
            it.opcode,
            it.kind.name(),
            it.class.name()
        );
        let _ = write!(line, " {}", it.label);
        if let Some(p) = &it.predicate {
            let _ = write!(line, " predicate={p}");
        }
        if let Some(m) = &it.message {
            let _ = write!(line, " {m:?}");
        }
        line.push_str(&Status::of(it.class.is_reported(), &r.justified, r.baselined).text());
        match r.stack.last() {
            Some(loc) => {
                let _ = write!(line, "  {}", self.loc_text(loc));
            }
            None if it.entry_param => line.push_str("  (entry-point ABI check)"),
            None => line.push_str("  (no location)"),
        }
        let _ = writeln!(out, "{line}");
        if !(it.entry_param && r.stack.is_empty()) {
            self.where_lines(&r.stack, r.attributed, out);
        }
        if explain {
            for w in &it.why {
                let _ = writeln!(out, "         why: {w}");
            }
            let _ = writeln!(out, "         opcode: {}", it.text);
            if r.stack.len() > 1 {
                let frames: Vec<String> = r.stack.iter().rev().map(|l| self.loc_text(l)).collect();
                let _ = writeln!(out, "         stack: {}", frames.join(" <- "));
            }
        }
    }

    fn call_lists(&self, out: &mut String) {
        let _ = writeln!(out, "\nbrillig calls ({}):", self.brillig_calls.len());
        for c in &self.brillig_calls {
            let name = self.artifact.brillig_name(c.callee).unwrap_or("?");
            let loc = Self::acir_stack(self.artifact, c.function, c.opcode)
                .last()
                .map(|l| self.loc_text(l))
                .unwrap_or_else(|| "(no location)".into());
            let skipped = if c.predicate_zero { " (skipped)" } else { "" };
            let _ = writeln!(
                out,
                "f{} #{:<5} brillig {} {} predicate={}{}  {}",
                c.function, c.opcode, c.callee, name, c.predicate, skipped, loc
            );
        }
        if !self.acir_calls.is_empty() {
            let _ = writeln!(out, "\nacir calls ({}):", self.acir_calls.len());
            for c in &self.acir_calls {
                let loc = Self::acir_stack(self.artifact, c.function, c.opcode)
                    .last()
                    .map(|l| self.loc_text(l))
                    .unwrap_or_else(|| "(no location)".into());
                let _ = writeln!(
                    out,
                    "f{} #{:<5} call f{} predicate={}  {}",
                    c.function, c.opcode, c.callee, c.predicate, loc
                );
            }
        }
    }

    fn trap_status(t: &TrapReport) -> (&'static str, Status) {
        let reachable = if t.site.guarded_by_callers {
            "guarded"
        } else {
            "reachable"
        };
        (
            reachable,
            Status::of(t.reported(), &t.justified, t.baselined),
        )
    }

    fn trap_list(&self, view: &View, out: &mut String) {
        let unreachable: usize = self
            .brillig_stats
            .stats
            .values()
            .map(|s| s.traps_unreachable)
            .sum();
        let _ = writeln!(
            out,
            "\nbrillig abort sites ({} reachable, of which {} unjustified outside the library; {} guarded by callers; {} trap opcodes proved unreachable):",
            self.live_traps(),
            self.unjustified_traps(),
            self.traps.len() - self.live_traps(),
            unreachable
        );
        let mut groups: BTreeMap<(Status, String), usize> = BTreeMap::new();
        for t in &self.traps {
            let s = &t.site;
            let (reachable, status) = Self::trap_status(t);
            let mut line = format!(
                "{:<9} {:<9} {:<8} brillig {} {}",
                s.kind.name(),
                reachable,
                origin_name(t.origin),
                s.brillig,
                s.function_name,
            );
            if view.verbose {
                let _ = write!(line, " pc {}", s.pc);
            }
            if let Some(m) = &s.message {
                let _ = write!(line, " {m:?}");
            }
            match t.attributed.map(|i| t.stack[i]).or(t.stack.last().copied()) {
                Some(loc) => {
                    let (at, text) = self.line_ref(&loc);
                    let _ = write!(line, "  {at}  {text}");
                }
                None => line.push_str("  (no location)"),
            }
            if view.verbose || view.explain {
                let mut text = format!("{line}{}", status.text());
                if view.explain {
                    let _ = write!(
                        text,
                        "\n         why: {}",
                        trap_why(s.kind, &s.detail, t.origin)
                    );
                }
                let _ = writeln!(out, "{:>6}  {text}", 1);
            } else {
                *groups.entry((status, line)).or_default() += 1;
            }
        }
        for ((status, line), n) in groups {
            let _ = writeln!(out, "{n:>6}  {line}{}", status.text());
        }
    }

    fn marker_list(markers: &[MarkerUse], out: &mut String) {
        if markers.is_empty() {
            return;
        }
        let unused = markers.iter().filter(|m| m.items == 0).count();
        let _ = writeln!(
            out,
            "\njustification markers ({}, {unused} justified nothing):",
            markers.len()
        );
        for m in markers {
            let used = if m.items == 0 {
                "justified nothing".to_string()
            } else {
                format!("{} item(s)", m.items)
            };
            let _ = writeln!(
                out,
                "  {}:{}  {used}  {:?}",
                display_path(&m.path),
                m.at.line,
                m.reason
            );
        }
    }

    fn summary_lines(&self, out: &mut String) {
        let _ = writeln!(out, "\nsummary:");
        for (c, n) in &self.class_counts() {
            let _ = writeln!(out, "  {:<26} {n}", c.name());
        }
        let _ = writeln!(
            out,
            "  brillig calls              {}",
            self.brillig_calls.len()
        );
        let _ = writeln!(
            out,
            "  brillig abort sites        {} reachable ({} unjustified outside the library), {} guarded",
            self.live_traps(),
            self.unjustified_traps(),
            self.traps.len() - self.live_traps()
        );
        let _ = writeln!(
            out,
            "  reported (unjustified)     {} (+{} justified)",
            self.unjustified(),
            self.justified()
        );
        if self.baselined() > 0 {
            let _ = writeln!(out, "  accepted by the baseline   {}", self.baselined());
        }
        let _ = writeln!(out, "  failing (items and abort sites) {}", self.failures());
    }

    /// The report for one function, without the marker list and the
    /// exit status (see render_human).
    pub fn render_function(&self, view: &View) -> String {
        let mut out = String::new();
        self.header(&mut out);
        if !view.summary {
            if view.verbose {
                self.verbose_items(view, &mut out);
                self.call_lists(&mut out);
            } else {
                self.grouped_items(view, &mut out);
            }
            self.trap_list(view, &mut out);
        }
        self.summary_lines(&mut out);
        out
    }

    pub fn render_json(&self, view: &View) -> Value {
        let counts: serde_json::Map<String, Value> = self
            .class_counts()
            .into_iter()
            .map(|(c, n)| (c.name().to_string(), json!(n)))
            .collect();
        let summary = json!({
            "opcodes": self.opcode_count(),
            "classes": counts,
            "reported_unjustified": self.unjustified(),
            "justified": self.justified(),
            "baselined": self.baselined(),
            "brillig_calls": self.brillig_calls.len(),
            "brillig_abort_sites_reachable": self.live_traps(),
            "brillig_abort_sites_unjustified": self.unjustified_traps(),
            "brillig_abort_sites_guarded": self.traps.len() - self.live_traps(),
            "failures": self.failures(),
            "exit_code": self.exit_code(),
        });
        let lib: Vec<Value> = self
            .lib_matches
            .iter()
            .map(|m| json!({ "directory": m.dir, "files": m.files }))
            .collect();
        let mut v = json!({
            "function": self.artifact.name,
            "noir_version": self.artifact.noir_version,
            "lib_dirs": lib,
            "allow_entry_ranges": self.options.allow_entry_ranges,
            "warnings": self.warnings,
            "marker_dirs": self.marker_dirs(),
            "summary": summary,
        });
        if view.summary {
            return v;
        }
        v["items"] = self
            .items
            .iter()
            .filter(|r| view.shows(r.item.class))
            .map(|r| self.item_json(r))
            .collect();
        v["brillig_calls"] = self
            .brillig_calls
            .iter()
            .map(|c| {
                let stack = Self::acir_stack(self.artifact, c.function, c.opcode);
                json!({
                    "function": c.function,
                    "opcode": c.opcode,
                    "callee": c.callee,
                    "name": self.artifact.brillig_name(c.callee),
                    "predicate": c.predicate,
                    "skipped": c.predicate_zero,
                    "location": stack.last().map(|l| self.loc_json(l)),
                })
            })
            .collect();
        v["acir_calls"] = self
            .acir_calls
            .iter()
            .map(|c| json!({ "function": c.function, "opcode": c.opcode, "callee": c.callee, "predicate": c.predicate, "skipped": c.predicate_zero }))
            .collect();
        v["brillig_abort_sites"] = self.traps.iter().map(|t| self.trap_json(t)).collect();
        v["brillig_functions"] = self
            .brillig_stats
            .stats
            .iter()
            .map(|(id, s)| {
                json!({
                    "id": id,
                    "name": self.artifact.brillig_name(*id),
                    "opcodes": s.opcodes,
                    "reachable": s.reachable,
                    "trap_opcodes": s.traps_total,
                    "trap_opcodes_unreachable": s.traps_unreachable,
                })
            })
            .collect();
        v
    }

    fn item_json(&self, r: &Reported) -> Value {
        let it = &r.item;
        json!({
            "function": it.function,
            "opcode": it.opcode,
            "kind": it.kind.name(),
            "label": it.label,
            "class": it.class.name(),
            "reported": it.class.is_reported(),
            "justified": self.justification_json(&r.justified),
            "baselined": r.baselined,
            "counts": r.counts(),
            "entry_parameter": it.entry_param,
            "predicate": it.predicate,
            "message": it.message,
            "origin": origin_name(it.origin),
            "location": r.stack.last().map(|l| self.loc_json(l)),
            "attributed_location": r.attributed.map(|a| self.loc_json(&r.stack[a])),
            "stack": r.stack.iter().map(|l| self.loc_json(l)).collect::<Vec<_>>(),
            "why": it.why,
            "text": it.text,
        })
    }

    fn trap_json(&self, t: &TrapReport) -> Value {
        let s = &t.site;
        json!({
            "brillig": s.brillig,
            "name": s.function_name,
            "pc": s.pc,
            "kind": s.kind.name(),
            "guarded_by_callers": s.guarded_by_callers,
            "message": s.message,
            "origin": origin_name(t.origin),
            "detail": s.detail,
            "justified": self.justification_json(&t.justified),
            "baselined": t.baselined,
            "counts": t.counts(),
            "location": t.stack.last().map(|l| self.loc_json(l)),
        })
    }

    /// The --brillig-ops report: every integer And/Or/Xor/Shl/Shr,
    /// ConditionalMov and black box other than ToRadix per Brillig
    /// function, with its source location.
    pub fn render_mpc_ops_human(&self, summary_only: bool) -> String {
        let mut out = String::new();
        let program = &self.artifact.program;
        let mut per_fn: BTreeMap<u32, (usize, usize)> = BTreeMap::new();
        for o in &self.mpc_ops {
            let e = per_fn.entry(o.site.brillig).or_default();
            if o.site.reachable {
                e.0 += 1;
            } else {
                e.1 += 1;
            }
        }
        if !summary_only {
            let _ = writeln!(
                out,
                "\nbrillig ops co-noir's MPC VM cannot execute ({} reachable, {} proved unreachable):",
                self.live_mpc_ops(),
                self.mpc_ops.len() - self.live_mpc_ops()
            );
            for o in &self.mpc_ops {
                let s = &o.site;
                let op = if s.bit_size > 0 {
                    format!("{} u{}", s.op, s.bit_size)
                } else {
                    s.op.to_string()
                };
                let status = if s.reachable {
                    "reachable"
                } else {
                    "unreachable"
                };
                let mut line = format!(
                    "brillig {} {} pc {:<5} {:<9} {:<11} {:<8}",
                    s.brillig,
                    s.function_name,
                    s.pc,
                    op,
                    status,
                    origin_name(o.origin)
                );
                match o.stack.last() {
                    Some(loc) => {
                        let _ = write!(line, "  {}", self.loc_text(loc));
                    }
                    None => line.push_str("  (no location)"),
                }
                let _ = writeln!(out, "{line}");
                if !o.stack.is_empty() {
                    self.where_lines(&o.stack, o.attributed, &mut out);
                }
            }
        }
        let _ = writeln!(out, "\nbrillig ops summary:");
        let _ = writeln!(
            out,
            "  brillig functions          {}",
            program.unconstrained_functions.len()
        );
        for (id, (live, dead)) in &per_fn {
            let name = self.artifact.brillig_name(*id).unwrap_or("?");
            let _ = writeln!(
                out,
                "  brillig {id} {name}: {live} reachable, {dead} unreachable"
            );
        }
        let _ = writeln!(
            out,
            "  unsupported ops            {} reachable, {} unreachable",
            self.live_mpc_ops(),
            self.mpc_ops.len() - self.live_mpc_ops()
        );
        let _ = writeln!(
            out,
            "  exit code                  {}",
            self.mpc_ops_exit_code()
        );
        out
    }

    pub fn render_mpc_ops_json(&self) -> Value {
        let ops: Vec<Value> = self
            .mpc_ops
            .iter()
            .map(|o| {
                let s = &o.site;
                json!({
                    "brillig": s.brillig,
                    "name": s.function_name,
                    "pc": s.pc,
                    "op": s.op,
                    "bit_size": s.bit_size,
                    "reachable": s.reachable,
                    "origin": origin_name(o.origin),
                    "location": o.stack.last().map(|l| self.loc_json(l)),
                })
            })
            .collect();
        let functions: Vec<Value> = self
            .artifact
            .program
            .unconstrained_functions
            .iter()
            .map(|b| json!(b.function_name))
            .collect();
        json!({
            "function": self.artifact.name,
            "brillig_functions": functions,
            "mpc_unsupported_ops": ops,
            "reachable": self.live_mpc_ops(),
            "exit_code": self.mpc_ops_exit_code(),
        })
    }
}

/// Markers of several functions merged by location, with their item
/// counts added up.
pub fn merge_markers(outcomes: &[Outcome]) -> Vec<MarkerUse> {
    let mut merged: BTreeMap<(String, usize), MarkerUse> = BTreeMap::new();
    for o in outcomes {
        for m in &o.markers {
            merged
                .entry((m.path.clone(), m.at.line))
                .and_modify(|e| e.items += m.items)
                .or_insert_with(|| m.clone());
        }
    }
    merged.into_values().collect()
}

/// Exit status over several outcomes: 1 when more items and abort sites
/// fail than `max` allows.
pub fn exit_code(outcomes: &[Outcome], max: usize) -> i32 {
    let failures: usize = outcomes.iter().map(|o| o.failures()).sum();
    if failures > max { 1 } else { 0 }
}

/// The whole human report: each function, the marker list, the totals.
pub fn render_human(outcomes: &[Outcome], view: &View, max: usize, contract: bool) -> String {
    let mut out = String::new();
    for o in outcomes {
        if contract {
            let _ = writeln!(out, "\n=== function {}", o.artifact.name);
        }
        out.push_str(&o.render_function(view));
    }
    let markers = merge_markers(outcomes);
    if view.summary {
        let unused = markers.iter().filter(|m| m.items == 0).count();
        if unused > 0 {
            let _ = writeln!(
                out,
                "\n{unused} justification marker(s) justified nothing (run without --summary to list them)"
            );
        }
    } else {
        Outcome::marker_list(&markers, &mut out);
    }
    let failures: usize = outcomes.iter().map(|o| o.failures()).sum();
    let _ = writeln!(out);
    if contract {
        let per: Vec<String> = outcomes
            .iter()
            .map(|o| format!("{} {}", o.artifact.name, o.failures()))
            .collect();
        let _ = writeln!(out, "failing per function: {}", per.join(", "));
    }
    let _ = writeln!(out, "failing in total: {failures} (allowed: {max})");
    let _ = writeln!(out, "exit code: {}", exit_code(outcomes, max));
    if view.explain {
        out.push_str(&explain_text());
    }
    out
}

/// The whole JSON report.
pub fn render_json(outcomes: &[Outcome], view: &View, max: usize, warnings: &[String]) -> Value {
    let markers: Vec<Value> = merge_markers(outcomes)
        .iter()
        .map(|m| json!({ "file": m.path, "line": m.at.line, "reason": m.reason, "items": m.items }))
        .collect();
    json!({
        "warnings": warnings,
        "functions": outcomes.iter().map(|o| o.render_json(view)).collect::<Vec<_>>(),
        "markers": markers,
        "failures": outcomes.iter().map(|o| o.failures()).sum::<usize>(),
        "max_unjustified": max,
        "exit_code": exit_code(outcomes, max),
    })
}

/// The --explain appendix: recognised compiler patterns and limits.
pub fn explain_text() -> String {
    let mut out = String::from("\ncompiler hint patterns treated as hint-compiler:\n");
    for p in Pattern::ALL {
        let _ = writeln!(out, "  - {}: {}", p.name(), p.explain());
    }
    out.push_str(LIMITS);
    out
}

pub const LIMITS: &str = "
what this lint cannot decide statically:
  - hint-satisfiability: a constraint touching a hint witness holds only if
    the honest hint satisfies it for every input. The lint proves this only
    for the compiler-directive patterns above; it whitelists other such
    constraints by library provenance and reports the rest as
    hint-unreviewed.
  - determinedness: a witness computed from hints but forced by
    constraints (a comparison result, an ok flag) still counts as a hint.
    Equating one to a constant is reported as hint-pinned whatever the
    provenance, as that is how an asserted comparison or flag lowers; so
    is a Brillig output equated to a constant under a branch condition
    computed from inputs only. Other asserts on such a witness (two flags
    compared with each other, a hint-derived branch condition, a pinned
    value reached through a definition under a branch) are input-
    falsifiable in truth but reported as hint-unreviewed outside the
    library and whitelisted inside it, so reviewers must catch them.
  - flattened branch predicates: an assert inside an if is multiplied
    through by the branch condition into one AssertZero. The lint cannot
    separate predicate from payload; it classifies the whole expression
    and notes a candidate factor when every term shares one.
  - predicates folded into operands (RANGE on c*v, memory index c*i): the
    lint notes when every term of the checked witness's definition shares
    a factor but does not assume that factor is a predicate. ACIR memory
    operations carry no predicate field at all; the compiler folds the
    branch condition into the index.
  - provenance is a directory test on the innermost call-stack frame
    outside std. Library whitelisting trusts that reviewers checked every
    hint-class constraint and every abort site in those directories,
    including std code they call.
  - a marker on a call line justifies every item under that call,
    including items a dependency adds later; the marker list counts them.
  - backend-defined opcodes: ECDSA verification returns false for a bad
    signature at witness generation, but the ACIR spec lets the proving
    backend fail when the public key is not on the curve. The lint lists
    these opcodes and does not count them in the exit code; whether a
    given backend fails is not checked.
  - radix decompositions in Brillig (to_le_bits, to_le_bytes) are proved
    abort-free only when the limb count and radix are constants and the
    limbs cover the whole field or a known integer width of the input.
    Pointer writes are assumed not to overwrite registers, as in compiler
    output.
  - called ACIR functions are classified with their parameters treated as
    inputs; a caller passing hint values would make some of those items
    hint-class instead.
  - note-width sites compare the packed note of aztec_prv_notifyCreatedNote
    with aztec-nr v6.0.0's MAX_NOTE_PACKED_LEN (8), hard-coded; another
    aztec-nr version may use another limit. The site is the oracle call in
    Brillig (for aztec-nr's notify_created_note, its wrapper in
    oracle/notes.nr), not the constrained call that reaches it, so only a
    marker on the Brillig line or a baseline entry accepts it. A packed
    note passed as a vector of unknown length is reported.
  - Brillig abort sites: the walk uses constant propagation, a value's
    zero test along the branch it takes, and, for a divisor, the
    straight-line code that computed it (x + (x == 0) is nonzero). A
    reachable trap or division is not proof that any argument reaches it;
    non-termination is not detected.
  - silent truncation (Field as uN) emits no constraint, so nothing here
    can see it.
";
