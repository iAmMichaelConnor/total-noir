//! Baselines: the set of unjustified items a project has accepted, so a
//! run fails only on new ones.
//!
//! A baseline file is JSON written by `--write-baseline`:
//! `{"total_lint_baseline": 1, "entries": [{function, class, label, file,
//! text, count}]}`. An entry names a source line by its file and its
//! trimmed text rather than its number, so edits elsewhere in the file do
//! not invalidate it. Paths in a git dependency start at the host
//! directory (`github.com/...`); other paths are relative to the baseline
//! file's directory, so a baseline checked in next to a script keeps
//! working in another checkout.

use std::collections::BTreeMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::artifact::Location;
use crate::report::{Outcome, normalise_dir};

pub const FORMAT_VERSION: u32 = 1;

/// Findings by index, with their keys.
pub type Keyed = Vec<(usize, Key)>;

/// What identifies an unjustified item or abort site across runs.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Key {
    /// `main`, or the contract function.
    pub function: String,
    /// The class, or `brillig-<kind>` for an abort site.
    pub class: String,
    /// The item's label, or the Brillig function of an abort site.
    pub label: String,
    /// Portable path of the source line; empty without a location.
    pub file: String,
    /// The source line, trimmed; empty without a location.
    pub text: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Entry {
    #[serde(flatten)]
    pub key: Key,
    pub count: usize,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct BaselineFile {
    pub total_lint_baseline: u32,
    pub entries: Vec<Entry>,
}

/// Hosts nargo's git dependency cache names directories after.
const GIT_HOSTS: [&str; 4] = ["github.com", "gitlab.com", "bitbucket.org", "codeberg.org"];

/// A path that means the same in another checkout or on another machine.
pub fn portable_path(path: &str, base: &str) -> String {
    let parts: Vec<&str> = path.split('/').collect();
    if let Some(i) = parts.iter().position(|p| GIT_HOSTS.contains(p)) {
        return parts[i..].join("/");
    }
    if !path.starts_with('/') {
        return path.to_string();
    }
    relative_to(path, base)
}

/// `path` relative to directory `base`, both absolute.
fn relative_to(path: &str, base: &str) -> String {
    let p: Vec<&str> = path.split('/').filter(|s| !s.is_empty()).collect();
    let b: Vec<&str> = base.split('/').filter(|s| !s.is_empty()).collect();
    let common = p.iter().zip(&b).take_while(|(x, y)| x == y).count();
    let mut out: Vec<&str> = std::iter::repeat_n("..", b.len() - common).collect();
    out.extend(&p[common..]);
    out.join("/")
}

/// Directory a baseline file's paths are relative to.
pub fn base_dir(baseline_path: &str) -> Result<String, String> {
    let abs = normalise_dir(baseline_path)
        .ok_or_else(|| format!("{baseline_path}: no current directory"))?;
    Ok(Path::new(&abs)
        .parent()
        .map(|p| p.to_string_lossy().into_owned())
        .unwrap_or_else(|| "/".into()))
}

impl Outcome<'_> {
    /// File and line text of the frame a finding is shown at.
    fn key_location(
        &self,
        stack: &[Location],
        attributed: Option<usize>,
        base: &str,
    ) -> (String, String) {
        let loc = attributed.map(|i| stack[i]).or(stack.last().copied());
        let Some(loc) = loc else {
            return (String::new(), String::new());
        };
        let Some(file) = self.artifact.files.get(&loc.file) else {
            return (String::new(), String::new());
        };
        let (line, _) = file.line_col(loc.start);
        (
            portable_path(&file.path, base),
            file.line_text(line).trim().to_string(),
        )
    }

    /// Keys of the unjustified items (index into items) and abort sites
    /// (index into traps).
    pub fn finding_keys(&self, base: &str) -> (Keyed, Keyed) {
        let items = self
            .items
            .iter()
            .enumerate()
            .filter(|(_, r)| r.unjustified())
            .map(|(i, r)| {
                let (file, text) = self.key_location(&r.stack, r.attributed, base);
                (
                    i,
                    Key {
                        function: self.artifact.name.clone(),
                        class: r.item.class.name().to_string(),
                        label: r.item.label.clone(),
                        file,
                        text,
                    },
                )
            })
            .collect();
        let traps = self
            .traps
            .iter()
            .enumerate()
            .filter(|(_, t)| t.unjustified())
            .map(|(i, t)| {
                let (file, text) = self.key_location(&t.stack, t.attributed, base);
                (
                    i,
                    Key {
                        function: self.artifact.name.clone(),
                        class: format!("brillig-{}", t.site.kind.name()),
                        label: t.site.function_name.clone(),
                        file,
                        text,
                    },
                )
            })
            .collect();
        (items, traps)
    }

    /// Mark the findings the baseline accepts, using up its counts.
    pub fn apply_baseline(&mut self, remaining: &mut BTreeMap<Key, usize>, base: &str) {
        let (items, traps) = self.finding_keys(base);
        let mut take = |k: &Key| match remaining.get_mut(k) {
            Some(n) if *n > 0 => {
                *n -= 1;
                true
            }
            _ => false,
        };
        for (i, k) in items {
            self.items[i].baselined = take(&k);
        }
        for (i, k) in traps {
            self.traps[i].baselined = take(&k);
        }
    }
}

/// Read a baseline file into remaining counts per key.
pub fn read(path: &str) -> Result<BTreeMap<Key, usize>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let file: BaselineFile = serde_json::from_str(&text)
        .map_err(|e| format!("{path}: not a total-lint baseline: {e}"))?;
    if file.total_lint_baseline != FORMAT_VERSION {
        return Err(format!(
            "{path}: baseline format {} (this total-lint reads {FORMAT_VERSION})",
            file.total_lint_baseline
        ));
    }
    let mut out = BTreeMap::new();
    for e in file.entries {
        *out.entry(e.key).or_insert(0) += e.count;
    }
    Ok(out)
}

/// The baseline accepting every unjustified finding of these outcomes.
pub fn build(outcomes: &[Outcome], base: &str) -> BaselineFile {
    let mut counts: BTreeMap<Key, usize> = BTreeMap::new();
    for o in outcomes {
        let (items, traps) = o.finding_keys(base);
        for (_, k) in items.into_iter().chain(traps) {
            *counts.entry(k).or_default() += 1;
        }
    }
    BaselineFile {
        total_lint_baseline: FORMAT_VERSION,
        entries: counts
            .into_iter()
            .map(|(key, count)| Entry { key, count })
            .collect(),
    }
}

pub fn write(path: &str, file: &BaselineFile) -> Result<(), String> {
    let text = serde_json::to_string_pretty(file).map_err(|e| e.to_string())?;
    std::fs::write(path, text + "\n").map_err(|e| format!("{path}: {e}"))
}

#[cfg(test)]
mod tests {
    use super::portable_path;

    #[test]
    fn paths_are_portable() {
        assert_eq!(
            portable_path(
                "/home/u/nargo/github.com/org/repo/v1/aztec/src/lib.nr",
                "/ci/checkout/examples/x"
            ),
            "github.com/org/repo/v1/aztec/src/lib.nr"
        );
        assert_eq!(
            portable_path(
                "/r/noir/total_aztec/src/init.nr",
                "/r/noir/total_aztec_driver"
            ),
            "../total_aztec/src/init.nr"
        );
        assert_eq!(portable_path("/r/a/src/main.nr", "/r/a"), "src/main.nr");
        assert_eq!(
            portable_path("std/field/mod.nr", "/r/a"),
            "std/field/mod.nr"
        );
    }
}
