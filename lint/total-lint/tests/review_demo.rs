//! Regression checks on the review_demo fixture, compiled at test time
//! (see common/mod.rs), which depends on the review_vendor stand-in
//! library:
//! - justification markers count only in the entry package's own files;
//! - a marker inside a string literal does not count;
//! - a hint whose radix decomposition can abort is an abort site, and a
//!   full-width decomposition is not;
//! - an asserted comparison in the library is reported as hint-pinned;
//! - ECDSA stays visible as backend-defined.

use total_lint::analysis::{Class, Kind, Origin};
use total_lint::artifact::Artifact;
use total_lint::brillig::TrapKind;
use total_lint::render::View;
use total_lint::report::{Options, Outcome, Reported};

mod common;

fn load() -> Option<Artifact> {
    common::compile("review_demo")
}

/// The vendor's source directory exactly as the artifact records it. The
/// artifact stores absolute paths of the directory it was compiled in, so
/// deriving the directory from it keeps the test independent of that
/// location.
fn vendor_src(a: &Artifact) -> String {
    let lib = a
        .files
        .values()
        .map(|f| f.path.as_str())
        .find(|p| p.ends_with("review_vendor/src/lib.nr"))
        .expect("artifact records the review_vendor library file");
    lib.strip_suffix("lib.nr").unwrap().to_string()
}

fn vendor_lib(a: &Artifact) -> Vec<String> {
    vec![vendor_src(a)]
}

/// The item whose provenance frame is on a source line containing `text`.
fn item<'o>(o: &'o Outcome, text: &str) -> &'o Reported {
    o.items
        .iter()
        .find(|r| {
            r.item.class != Class::Definition
                && r.attributed.is_some_and(|i| {
                    let loc = r.stack[i];
                    let f = &o.artifact.files[&loc.file];
                    f.line_text(f.line_col(loc.start).0).contains(text)
                })
        })
        .unwrap_or_else(|| panic!("no item at a line containing {text:?}"))
}

#[test]
fn markers_from_dependencies_do_not_justify() {
    let Some(a) = load() else {
        return;
    };
    let o = Outcome::run(&a, vendor_lib(&a));
    assert!(
        o.root_src
            .as_deref()
            .is_some_and(|r| r.ends_with("fixtures/review_demo/src"))
    );

    // The vendor marks its own input assert: still reported, not justified.
    let vendor = item(&o, "assert(x == 3)");
    assert_eq!(vendor.item.class, Class::LibraryInputFalsifiable);
    assert_eq!(vendor.justified, None);

    // The vendor marks the call of a caller-supplied function: the caller's
    // assert inside that function is not justified by it.
    let cb = item(&o, "assert(v == 7)");
    assert_eq!(cb.item.class, Class::InputFalsifiable);
    assert_eq!(cb.item.origin, Origin::User);
    assert!(
        cb.stack
            .iter()
            .any(|l| a.files[&l.file].path.contains("review_vendor/src/"))
    );
    assert_eq!(cb.justified, None);

    // The author's own marker counts.
    let own = item(&o, "assert(z != 5)");
    assert_eq!(own.item.class, Class::InputFalsifiable);
    assert_eq!(
        own.justified.as_ref().map(|j| j.reason.as_str()),
        Some("the caller guarantees z != 5")
    );

    // A marker inside the assert's message string does not.
    let msg = item(&o, "assert(w != 9");
    assert_eq!(msg.item.class, Class::InputFalsifiable);
    assert_eq!(msg.justified, None);

    assert_eq!(o.justified(), 1);
    assert_eq!(o.exit_code(), 1);
}

#[test]
fn allow_src_opts_a_directory_in() {
    let Some(a) = load() else {
        return;
    };
    let o = Outcome::run_with(
        &a,
        Options {
            lib_dirs: vendor_lib(&a),
            allow_dirs: vec![vendor_src(&a)],
            ..Options::default()
        },
    );
    assert!(item(&o, "assert(x == 3)").justified.is_some());
    assert!(item(&o, "assert(v == 7)").justified.is_some());
    assert_eq!(o.justified(), 3);
}

#[test]
fn markers_do_not_follow_the_library_setting() {
    // With the default library trees the vendor is plain user code, but its
    // files are still outside the entry package, so its markers still do
    // not count.
    let Some(a) = load() else {
        return;
    };
    let o = Outcome::run(&a, Vec::new());
    let vendor = item(&o, "assert(x == 3)");
    assert_eq!(vendor.item.class, Class::InputFalsifiable);
    assert_eq!(vendor.justified, None);
    assert_eq!(o.justified(), 1);
}

#[test]
fn short_hint_decomposition_is_an_abort_site() {
    let Some(a) = load() else {
        return;
    };
    let o = Outcome::run(&a, vendor_lib(&a));
    let radix: Vec<_> = o
        .traps
        .iter()
        .filter(|t| t.site.kind == TrapKind::Radix)
        .collect();
    assert_eq!(
        radix.len(),
        1,
        "{:?}",
        o.traps.iter().map(|t| &t.site).collect::<Vec<_>>()
    );
    assert_eq!(radix[0].site.function_name, "low_byte");
    assert_eq!(radix[0].origin, Origin::Library);
    assert!(!radix[0].site.guarded_by_callers);
    // The full-width to_le_bits hint is not listed.
    assert!(
        o.traps
            .iter()
            .all(|t| t.site.function_name != "full_low_bit")
    );
}

#[test]
fn ecdsa_is_listed_as_backend_defined() {
    let Some(a) = load() else {
        return;
    };
    let o = Outcome::run(&a, vendor_lib(&a));
    let ecdsa: Vec<_> = o
        .items
        .iter()
        .filter(|r| r.item.kind == Kind::BlackBox)
        .collect();
    assert_eq!(ecdsa.len(), 1);
    assert_eq!(ecdsa[0].item.class, Class::BackendDefined);
    assert_eq!(ecdsa[0].item.label, "ecdsa_secp256k1");
    let v = o.render_json(&View::default());
    assert_eq!(v["summary"]["classes"]["backend-defined"], 1);
    assert!(
        v["items"]
            .as_array()
            .unwrap()
            .iter()
            .any(|i| i["class"] == "backend-defined")
    );
    let human = o.render_function(&View {
        verbose: true,
        explain: true,
        ..View::default()
    });
    assert!(human.contains("backend-defined"));
}

#[test]
fn asserted_comparisons_in_the_library_stay_reported() {
    // The vendor is the whitelisted library, and every constraint
    // `assert(a < b)` lowers to touches the comparison's hint; the pin of
    // that hint to a constant is still reported, and so is the pin under
    // the `if c` branch.
    let Some(a) = load() else {
        return;
    };
    let o = Outcome::run(&a, vendor_lib(&a));
    let line = |r: &Reported| {
        let loc = r.stack[r.attributed.expect("located")];
        let f = &a.files[&loc.file];
        f.line_text(f.line_col(loc.start).0).trim().to_string()
    };
    let pinned: Vec<&Reported> = o
        .items
        .iter()
        .filter(|r| r.item.class == Class::HintPinned)
        .collect();
    let lines: Vec<String> = pinned.iter().map(|r| line(r)).collect();
    assert_eq!(lines, ["assert(a < b);", "assert(a <= b);"]);
    for r in &pinned {
        assert_eq!(r.item.origin, Origin::Library);
        assert!(r.item.class.is_reported());
        assert_eq!(r.justified, None);
    }
    // The comparison's integer-quotient range checks and identity are
    // hint-compiler items: they hold for every input.
    assert!(
        o.items
            .iter()
            .any(|r| r.item.class == Class::HintCompiler && line(r) == "assert(a < b);")
    );
    assert!(!Class::HintCompiler.is_reported());
    // With the vendor as plain user code the pins keep their class.
    let user = Outcome::run(&a, Vec::new());
    let user_pins = user
        .items
        .iter()
        .filter(|r| r.item.class == Class::HintPinned)
        .count();
    assert_eq!(user_pins, 2);
}
