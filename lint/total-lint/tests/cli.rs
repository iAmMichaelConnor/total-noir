//! Drives the built total-lint binary on fixtures compiled at test time
//! (see common/mod.rs): exit codes, library directories, markers,
//! baselines, contract artifacts, and malformed input.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::Value;

mod common;

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_total-lint"))
}

/// Run the binary with `args` in directory `cwd`.
fn run(cwd: &Path, args: &[&str]) -> Output {
    bin()
        .args(args)
        .current_dir(cwd)
        .output()
        .expect("run total-lint")
}

fn code(o: &Output) -> i32 {
    o.status.code().expect("exit code")
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// The compiled artifact of a bin fixture and the fixture's directory.
fn fixture(name: &str) -> Option<(PathBuf, PathBuf)> {
    let path = common::artifact_path(name, &format!("{name}.json"))?;
    let dir = path.parent()?.parent()?.to_path_buf();
    Some((path, dir))
}

fn s(p: &Path) -> &str {
    p.to_str().expect("utf-8 path")
}

/// A scratch directory of this test binary.
fn scratch(name: &str) -> PathBuf {
    let d = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("total-lint-cli")
        .join(name);
    if d.exists() {
        std::fs::remove_dir_all(&d).expect("clear scratch dir");
    }
    std::fs::create_dir_all(&d).expect("create scratch dir");
    d
}

fn json(o: &Output) -> Value {
    serde_json::from_slice(&o.stdout).expect("json output")
}

#[test]
fn a_reachable_brillig_abort_fails_the_run() {
    let Some((art, dir)) = fixture("fn1_brillig_abort") else {
        return;
    };
    let o = run(&dir, &[s(&art), "--json"]);
    assert_eq!(code(&o), 1, "{}", stdout(&o));
    let v = json(&o);
    let f = &v["functions"][0];
    assert_eq!(f["summary"]["reported_unjustified"], 0);
    assert_eq!(f["summary"]["brillig_abort_sites_unjustified"], 1);
    let sites = f["brillig_abort_sites"].as_array().unwrap();
    let assert_site = sites.iter().find(|t| t["name"] == "f").unwrap();
    assert_eq!(assert_site["kind"], "trap");
    assert_eq!(assert_site["counts"], true);
    // The division in quot carries a marker, which counts one item.
    let div = sites.iter().find(|t| t["name"] == "quot").unwrap();
    assert_eq!(div["kind"], "division");
    assert!(div["justified"]["reason"].is_string());
    assert_eq!(div["counts"], false);
    assert_eq!(v["markers"][0]["items"], 1);
}

#[test]
fn library_directories_are_absolute_and_never_matched_by_name() {
    let Some((art, dir)) = fixture("fn2_impostor") else {
        return;
    };
    // No library: the vendored helper's hint-class asserts are reported.
    let o = run(&dir, &[s(&art), "--summary"]);
    assert_eq!(code(&o), 1);
    assert!(stdout(&o).contains("library directories (hint-class constraints whitelisted): none"));
    // A relative pattern that names no directory is an error, not a
    // whitelist of every directory called total.
    let o = run(&dir, &[s(&art), "--lib-src", "total/src/"]);
    assert_eq!(code(&o), 2);
    assert!(stderr(&o).contains("is not a directory"), "{}", stderr(&o));
    // An existing directory named total/src elsewhere does not cover the
    // vendored one, and the run says it matched nothing.
    let cwd = scratch("impostor");
    std::fs::create_dir_all(cwd.join("total/src")).unwrap();
    let o = run(&cwd, &[s(&art), "--lib-src", "total/src/", "--summary"]);
    assert_eq!(code(&o), 1);
    assert!(stderr(&o).contains("holds no source file of this artifact"));
    assert!(stderr(&o).contains("library directories whitelisted:"));
    // Passing the vendored directory itself whitelists it, visibly.
    let o = run(&dir, &[s(&art), "--lib-src", "vendor/total/src"]);
    assert_eq!(code(&o), 0, "{}", stdout(&o));
    assert!(stdout(&o).contains("vendor/total/src (1 file(s))"));
    assert!(stdout(&o).contains("hint-library"));
}

#[test]
fn a_trailing_marker_justifies_its_own_line_only() {
    let Some((art, dir)) = fixture("fn3_trailing_marker") else {
        return;
    };
    let o = run(&dir, &[s(&art)]);
    assert_eq!(code(&o), 1);
    let out = stdout(&o);
    assert!(out.contains("assert(y != 0);"), "{out}");
    assert!(out.contains("[justified: x is never zero]"));
    assert!(
        out.contains("src/main.nr:5  1 item(s)  \"x is never zero\""),
        "{out}"
    );
    assert!(out.contains("src/main.nr:7  justified nothing"), "{out}");
    let v = json(&run(&dir, &[s(&art), "--json"]));
    assert_eq!(v["functions"][0]["summary"]["reported_unjustified"], 1);
    assert_eq!(v["functions"][0]["summary"]["justified"], 1);
}

#[test]
fn a_total_circuit_exits_zero() {
    let Some((art, dir)) = fixture("clean_total") else {
        return;
    };
    // The typed parameters' range checks are the only reported items left.
    let o = run(&dir, &[s(&art), "--json", "--summary"]);
    assert_eq!(code(&o), 1);
    let f = &json(&o)["functions"][0];
    assert_eq!(f["summary"]["reported_unjustified"], 2);
    assert_eq!(f["summary"]["classes"]["hint-unreviewed"], 33);
    let o = run(&dir, &[s(&art), "--allow-entry-ranges"]);
    assert_eq!(code(&o), 0, "{}", stdout(&o));
    let out = stdout(&o);
    assert!(out.contains("33 item(s)"), "{out}");
    assert!(out.contains("hint-compiler"));
}

#[test]
fn the_class_filter_and_the_verbose_listing() {
    let Some((art, dir)) = fixture("clean_total") else {
        return;
    };
    let o = run(&dir, &[s(&art), "--class", "hint-unreviewed"]);
    let out = stdout(&o);
    let listed: Vec<&str> = out
        .lines()
        .skip_while(|l| !l.starts_with("items"))
        .skip(1)
        .take_while(|l| !l.is_empty())
        .collect();
    assert_eq!(listed.len(), 1, "{out}");
    assert!(listed[0].contains("33  hint-unreviewed"));
    let o = run(&dir, &[s(&art), "--verbose", "--class", "hint-unreviewed"]);
    assert_eq!(stdout(&o).matches("hint-unreviewed ").count(), 33 + 1);
    let o = run(&dir, &[s(&art), "--class", "no-such-class"]);
    assert_eq!(code(&o), 2);
}

#[test]
fn a_baseline_fails_only_on_new_items() {
    let Some((art, dir)) = fixture("fn3_trailing_marker") else {
        return;
    };
    let work = scratch("baseline");
    let file = work.join("baseline.json");
    let o = run(&dir, &[s(&art), "--write-baseline", s(&file), "--summary"]);
    assert_eq!(code(&o), 0, "{}", stderr(&o));
    let written: Value = serde_json::from_str(&std::fs::read_to_string(&file).unwrap()).unwrap();
    let entries = written["entries"].as_array().unwrap();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0]["text"], "assert(y != 0);");
    // Paths are relative to the baseline file's directory.
    assert_eq!(
        entries[0]["file"],
        format!("{}/src/main.nr", relative(&work, &dir))
    );
    let o = run(&dir, &[s(&art), "--baseline", s(&file), "--summary"]);
    assert_eq!(code(&o), 0, "{}", stdout(&o));
    assert!(stdout(&o).contains("accepted by the baseline   1"));
    // A baseline with the entry's count used up fails again.
    let mut emptied = written.clone();
    emptied["entries"][0]["count"] = 0.into();
    std::fs::write(&file, emptied.to_string()).unwrap();
    assert_eq!(code(&run(&dir, &[s(&art), "--baseline", s(&file)])), 1);
    // An entry that no longer occurs is reported as stale.
    let mut stale = written.clone();
    stale["entries"][0]["text"] = "assert(gone);".into();
    std::fs::write(&file, stale.to_string()).unwrap();
    let o = run(&dir, &[s(&art), "--baseline", s(&file)]);
    assert_eq!(code(&o), 1);
    assert!(stderr(&o).contains("no longer occur"), "{}", stderr(&o));
    // --max-unjustified allows a count instead.
    assert_eq!(code(&run(&dir, &[s(&art), "--max-unjustified", "1"])), 0);
    assert_eq!(code(&run(&dir, &[s(&art), "--max-unjustified", "0"])), 1);
}

#[test]
fn a_created_note_wider_than_the_limit_is_reported() {
    let Some((art, dir)) = fixture("note_width") else {
        return;
    };
    let sites_of = |v: &Value| v["functions"][0]["brillig_abort_sites"].clone();
    let find = |sites: &Value, name: &str, kind: &str| -> Vec<Value> {
        sites
            .as_array()
            .unwrap()
            .iter()
            .filter(|t| t["name"] == name && t["kind"] == kind)
            .cloned()
            .collect()
    };
    let o = run(&dir, &[s(&art), "--json"]);
    assert_eq!(code(&o), 1);
    let sites = sites_of(&json(&o));
    let wide = find(&sites, "notify_wide", "note-width");
    assert_eq!(wide.len(), 1, "{sites}");
    assert_eq!(wide[0]["counts"], true);
    let detail = wide[0]["detail"].as_str().unwrap();
    for part in [
        "aztec_prv_notifyCreatedNote",
        "packed note of 9 fields",
        "MAX_NOTE_PACKED_LEN of 8",
    ] {
        assert!(detail.contains(part), "{detail}");
    }
    // Every call is an oracle site; the one at the limit is nothing more.
    for name in ["notify_wide", "notify_at_limit", "notify_justified"] {
        assert_eq!(find(&sites, name, "oracle").len(), 1, "{name}");
    }
    assert!(find(&sites, "notify_at_limit", "note-width").is_empty());
    // A marker on the call's line justifies it.
    let justified = &find(&sites, "notify_justified", "note-width")[0];
    assert_eq!(justified["counts"], false);
    assert!(justified["justified"]["reason"].is_string());
    // With the fixture as a library its oracle sites are whitelisted (and
    // its marker no longer honoured), but note-width sites still count.
    let o = run(&dir, &[s(&art), "--lib-src", "src", "--json"]);
    assert_eq!(code(&o), 1);
    let counting: Vec<(String, String)> = sites_of(&json(&o))
        .as_array()
        .unwrap()
        .iter()
        .filter(|t| t["counts"] == true)
        .map(|t| (t["name"].to_string(), t["kind"].to_string()))
        .collect();
    assert_eq!(
        counting,
        [
            ("\"notify_wide\"".into(), "\"note-width\"".into()),
            ("\"notify_justified\"".into(), "\"note-width\"".into())
        ]
    );
    // A baseline accepts it under its own class; without that entry the
    // run fails again.
    let work = scratch("note_width");
    let file = work.join("baseline.json");
    let o = run(&dir, &[s(&art), "--write-baseline", s(&file), "--summary"]);
    assert_eq!(code(&o), 0, "{}", stderr(&o));
    assert_eq!(code(&run(&dir, &[s(&art), "--baseline", s(&file)])), 0);
    let mut written: Value =
        serde_json::from_str(&std::fs::read_to_string(&file).unwrap()).unwrap();
    let entries = written["entries"].as_array_mut().unwrap();
    let before = entries.len();
    entries.retain(|e| e["class"] != "brillig-note-width");
    assert_eq!(entries.len(), before - 1);
    std::fs::write(&file, written.to_string()).unwrap();
    assert_eq!(code(&run(&dir, &[s(&art), "--baseline", s(&file)])), 1);
}

/// `to` relative to `from`, both absolute directories.
fn relative(from: &Path, to: &Path) -> String {
    let f: Vec<_> = from.components().collect();
    let t: Vec<_> = to.components().collect();
    let common = f.iter().zip(&t).take_while(|(a, b)| a == b).count();
    let mut parts: Vec<String> = std::iter::repeat_n("..".to_string(), f.len() - common).collect();
    parts.extend(
        t[common..]
            .iter()
            .map(|c| c.as_os_str().to_string_lossy().into_owned()),
    );
    parts.join("/")
}

#[test]
fn contract_artifacts_lint_each_constrained_function() {
    let Some(art) = common::artifact_path("contract_demo", "contract_demo-Demo.json") else {
        return;
    };
    let dir = art.parent().unwrap().parent().unwrap().to_path_buf();
    let o = run(&dir, &[s(&art), "--summary"]);
    assert_eq!(code(&o), 1);
    let out = stdout(&o);
    assert!(out.contains(
        "contract Demo: 2 constrained function(s) linted; unconstrained, not linted: view"
    ));
    assert!(out.contains("failing per function: bad 1, ok 0"), "{out}");
    assert_eq!(code(&run(&dir, &[s(&art), "--function", "ok"])), 0);
    assert_eq!(code(&run(&dir, &[s(&art), "--function", "bad"])), 1);
    let o = run(&dir, &[s(&art), "--function", "view"]);
    assert_eq!(code(&o), 2);
    assert!(stderr(&o).contains("unconstrained"));
    assert_eq!(code(&run(&dir, &[s(&art), "--function", "nope"])), 2);
    let v = json(&run(&dir, &[s(&art), "--json", "--summary"]));
    let names: Vec<&str> = v["functions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|f| f["function"].as_str().unwrap())
        .collect();
    assert_eq!(names, ["bad", "ok"]);
}

/// The fixture's artifact as JSON, to be modified and written elsewhere.
fn artifact_json(name: &str) -> Option<Value> {
    let (art, _) = fixture(name)?;
    Some(serde_json::from_str(&std::fs::read_to_string(art).unwrap()).unwrap())
}

#[test]
fn a_huge_abi_array_is_a_clean_error() {
    let Some(mut v) = artifact_json("fn3_trailing_marker") else {
        return;
    };
    v["abi"]["parameters"][0]["type"] = serde_json::json!({
        "kind": "array",
        "length": 1_000_000_000_000u64,
        "type": { "kind": "field" }
    });
    let work = scratch("abi");
    let file = work.join("huge.json");
    std::fs::write(&file, v.to_string()).unwrap();
    let o = run(&work, &[s(&file)]);
    assert_eq!(code(&o), 2);
    assert!(
        stderr(&o).contains("abi: parameters flatten to more than"),
        "{}",
        stderr(&o)
    );
}

#[test]
fn another_noir_version_is_warned_about() {
    let Some(mut v) = artifact_json("fn3_trailing_marker") else {
        return;
    };
    v["noir_version"] = "1.0.0-beta.3+abc".into();
    let work = scratch("version");
    let file = work.join("old.json");
    std::fs::write(&file, v.to_string()).unwrap();
    let o = run(&work, &[s(&file), "--json", "--summary"]);
    assert!(
        stderr(&o).contains("tested against 1.0.0-rc.3 only"),
        "{}",
        stderr(&o)
    );
    let warnings = json(&o)["warnings"].clone();
    assert!(warnings[0].as_str().unwrap().contains("1.0.0-beta.3"));
}

#[test]
fn usage_errors_exit_two() {
    let here = Path::new(env!("CARGO_MANIFEST_DIR"));
    assert_eq!(code(&run(here, &[])), 2);
    assert_eq!(code(&run(here, &["a.json", "b.json"])), 2);
    assert_eq!(code(&run(here, &["a.json", "--bogus"])), 2);
    assert_eq!(code(&run(here, &["no-such-file.json"])), 2);
    let o = run(here, &["--help"]);
    assert_eq!(code(&o), 0);
    assert!(stdout(&o).contains("--allow-entry-ranges"));
}
