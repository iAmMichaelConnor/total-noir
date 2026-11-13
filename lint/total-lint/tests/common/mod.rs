//! Compiles a fixture under lint/fixtures with the pinned nargo at test
//! time and decodes the artifact.
//!
//! The fixture tree is copied to a directory of its own under
//! CARGO_TARGET_TMPDIR per test binary, so compiling leaves no target/
//! inside lint/fixtures, and the relative path dependencies between
//! fixtures (review_demo on review_vendor) keep working. The copy keeps
//! the `fixtures/<name>` path suffix the tests check.
//!
//! nargo comes from NARGO or PATH and must be NARGO_VERSION: the tests
//! assert the exact lowering of that compiler. Without it the fixture
//! tests skip with a message, unless TOTAL_LINT_REQUIRE_NARGO is set (to
//! anything but empty or 0), in which case they fail.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};

use total_lint::artifact::Artifact;

pub const NARGO_VERSION: &str = "1.0.0-rc.3";

enum Setup {
    Ready(PathBuf),
    Skip(String),
}

fn nargo() -> PathBuf {
    std::env::var_os("NARGO")
        .map(PathBuf::from)
        .unwrap_or_else(|| "nargo".into())
}

fn required() -> bool {
    std::env::var("TOTAL_LINT_REQUIRE_NARGO").is_ok_and(|v| !v.is_empty() && v != "0")
}

/// Copy `from` to `to`, leaving out build output.
fn copy_tree(from: &Path, to: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(to)?;
    for entry in std::fs::read_dir(from)? {
        let entry = entry?;
        let path = entry.path();
        if entry.file_type()?.is_dir() {
            if entry.file_name() != "target" {
                copy_tree(&path, &to.join(entry.file_name()))?;
            }
        } else {
            std::fs::copy(&path, to.join(entry.file_name()))?;
        }
    }
    Ok(())
}

/// Check nargo's version and copy the fixtures, once per test binary.
fn setup() -> &'static Setup {
    static SETUP: OnceLock<Setup> = OnceLock::new();
    SETUP.get_or_init(|| {
        let out = match Command::new(nargo()).arg("--version").output() {
            Ok(o) if o.status.success() => String::from_utf8_lossy(&o.stdout).into_owned(),
            _ => {
                return Setup::Skip(format!(
                    "nargo not found (put nargo {NARGO_VERSION} on PATH or set NARGO)"
                ));
            }
        };
        let version = out
            .lines()
            .find_map(|l| l.strip_prefix("nargo version = "))
            .unwrap_or("")
            .trim();
        if !version.starts_with(NARGO_VERSION) {
            return Setup::Skip(format!(
                "nargo is {version:?} but the fixtures need {NARGO_VERSION}"
            ));
        }
        let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("../fixtures");
        let root = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join("total-lint-fixtures")
            .join(env!("CARGO_CRATE_NAME"));
        let dest = root.join("fixtures");
        if root.exists() {
            std::fs::remove_dir_all(&root).expect("clear the previous fixture copy");
        }
        copy_tree(&source, &dest).expect("copy lint/fixtures");
        Setup::Ready(dest)
    })
}

/// Compile `fixture` (once per test binary) and return the path of its
/// artifact `file` under target/. None, after printing why, when the
/// pinned nargo is unavailable and not required.
#[allow(dead_code)]
pub fn artifact_path(fixture: &str, file: &str) -> Option<PathBuf> {
    static COMPILED: Mutex<BTreeSet<String>> = Mutex::new(BTreeSet::new());
    let mut compiled = COMPILED.lock().unwrap_or_else(|e| e.into_inner());
    let dir = match setup() {
        Setup::Ready(fixtures) => fixtures.join(fixture),
        Setup::Skip(why) => {
            assert!(!required(), "TOTAL_LINT_REQUIRE_NARGO is set: {why}");
            eprintln!("skipping fixture test: {why}");
            return None;
        }
    };
    if !compiled.contains(fixture) {
        let out = Command::new(nargo())
            .args(["compile", "--silence-warnings"])
            .current_dir(&dir)
            .output()
            .expect("run nargo compile");
        assert!(
            out.status.success(),
            "nargo compile in {}:\n{}",
            dir.display(),
            String::from_utf8_lossy(&out.stderr)
        );
        compiled.insert(fixture.to_string());
    }
    Some(dir.join("target").join(file))
}

/// Compile `fixture` (once per test binary) and decode its artifact. Each
/// call returns a fresh artifact, so a test may modify it. None, after
/// printing why, when the pinned nargo is unavailable and not required.
#[allow(dead_code)]
pub fn compile(fixture: &str) -> Option<Artifact> {
    let path = artifact_path(fixture, &format!("{fixture}.json"))?;
    let artifact = path.to_str().expect("utf-8 path");
    Some(Artifact::from_path(artifact).unwrap_or_else(|e| panic!("decode {artifact}: {e}")))
}
