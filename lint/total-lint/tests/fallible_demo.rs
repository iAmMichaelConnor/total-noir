//! End-to-end check on the fallible_demo fixture, compiled at test time
//! (see common/mod.rs): every planted failure source is found,
//! classified, and located.

use std::sync::Arc;
use total_lint::analysis::{Class, Kind};
use total_lint::artifact::Artifact;

use total_lint::render::{self, View};
use total_lint::report::{Outcome, Reported};

mod common;

fn load() -> Option<Artifact> {
    common::compile("fallible_demo")
}

/// No library directory: every hint-class item is reported.
fn default_lib() -> Vec<String> {
    Vec::new()
}

/// The fixture's own source directory, as the artifact records it.
fn own_src(a: &Artifact) -> String {
    let main = a
        .files
        .values()
        .map(|f| f.path.as_str())
        .find(|p| p.ends_with("fallible_demo/src/main.nr"))
        .expect("artifact records main.nr");
    main.strip_suffix("/main.nr").unwrap().to_string()
}

/// (line, source text) of the frame that decided provenance.
fn attributed_line(a: &Artifact, r: &Reported) -> Option<(usize, String)> {
    let loc = r.stack[r.attributed?];
    let file = &a.files[&loc.file];
    let (line, _) = file.line_col(loc.start);
    Some((line, file.line_text(line).to_string()))
}

#[test]
fn decodes_bytecode_and_debug_symbols() {
    let Some(a) = load() else {
        return;
    };
    assert_eq!(a.program.functions.len(), 1);
    assert_eq!(a.program.unconstrained_functions.len(), 2);
    assert_eq!(a.debug.len(), 1);
    assert!(a.noir_version.starts_with("1.0.0-rc.3"));
    let params = a.entry_params();
    let names: Vec<&str> = params.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(
        names,
        [
            "a", "b", "x", "y", "d", "table[0]", "table[1]", "table[2]", "table[3]", "idx", "c"
        ]
    );
    assert!(
        a.files
            .values()
            .any(|f| f.path.ends_with("fallible_demo/src/main.nr"))
    );
}

#[test]
fn every_planted_failure_source_is_classified() {
    let Some(a) = load() else {
        return;
    };
    let o = Outcome::run(&a, default_lib());
    let fallible: Vec<&Reported> = o
        .items
        .iter()
        .filter(|r| r.item.class != Class::Definition)
        .collect();

    // (kind, class, source line, text the source line must contain)
    let expect: Vec<(Kind, Class, Option<usize>, &str)> = vec![
        (Kind::Range, Class::InputFalsifiable, None, "a: u64"),
        (Kind::Range, Class::InputFalsifiable, None, "b: u64"),
        (Kind::Range, Class::InputFalsifiable, None, "c: bool"),
        (
            Kind::Assert,
            Class::InputFalsifiable,
            Some(16),
            "assert(x == y + 1",
        ),
        (Kind::Range, Class::InputFalsifiable, Some(18), "a + b"),
        (
            Kind::MemoryRead,
            Class::InputFalsifiable,
            Some(20),
            "table[idx]",
        ),
        (Kind::Assert, Class::InputFalsifiable, Some(22), "x / d"),
        (Kind::Assert, Class::InputFalsifiable, Some(24), "a / b"),
        (Kind::Range, Class::HintUnreviewed, Some(24), "a / b"),
        (Kind::Range, Class::HintUnreviewed, Some(24), "a / b"),
        (Kind::Range, Class::HintUnreviewed, Some(24), "a / b"),
        (Kind::Assert, Class::HintUnreviewed, Some(24), "a / b"),
        (
            Kind::Range,
            Class::InputFalsifiable,
            Some(26),
            "assert_max_bit_size::<32>",
        ),
        (
            Kind::Assert,
            Class::InputFalsifiable,
            Some(29),
            "assert(y == 3",
        ),
    ];
    assert_eq!(
        fallible.len(),
        expect.len(),
        "items: {:?}",
        fallible
            .iter()
            .map(|r| (r.item.opcode, r.item.kind, r.item.class))
            .collect::<Vec<_>>()
    );
    for (r, (kind, class, line, text)) in fallible.iter().zip(&expect) {
        assert_eq!(
            (r.item.kind, r.item.class),
            (*kind, *class),
            "opcode {}",
            r.item.opcode
        );
        match line {
            None => {
                assert!(
                    r.item.entry_param,
                    "opcode {} should be an entry-parameter check",
                    r.item.opcode
                );
                assert!(r.stack.is_empty());
                assert!(r.item.label.contains(text), "{}", r.item.label);
            }
            Some(l) => {
                let (got, src) = attributed_line(&a, r).expect("location");
                assert_eq!(got, *l, "opcode {}", r.item.opcode);
                assert!(src.contains(text), "line {got}: {src}");
            }
        }
    }

    // Assertion messages come through from the ABI error types.
    let msg = |op: usize| {
        o.items
            .iter()
            .find(|r| r.item.opcode == op)
            .and_then(|r| r.item.message.clone())
    };
    assert_eq!(msg(3).as_deref(), Some("x must be y + 1"));
    assert_eq!(msg(5).as_deref(), Some("attempt to add with overflow"));

    // The branch assert is multiplied through by c (w10) and says so.
    let branch = fallible.last().unwrap();
    assert!(
        branch
            .item
            .why
            .iter()
            .any(|w| w.contains("every term contains w10"))
    );
    // The x / d check is recognised as a nonzero check on an input.
    assert!(
        fallible[6]
            .item
            .why
            .iter()
            .any(|w| w.contains("nonzero check"))
    );
    // The assert_max_bit_size RANGE is innermost in std, attributed to main.
    let amb = &fallible[12];
    assert!(
        a.files[&amb.stack.last().unwrap().file]
            .path
            .starts_with("std/")
    );

    assert_eq!(o.unjustified(), 14);
    assert_eq!(o.exit_code(), 1);
}

#[test]
fn brillig_calls_and_abort_sites() {
    let Some(a) = load() else {
        return;
    };
    let o = Outcome::run(&a, default_lib());
    assert_eq!(o.brillig_calls.len(), 3);
    assert!(o.brillig_calls.iter().all(|c| c.predicate == "1"));
    // The integer-quotient directive divides by its second argument; every
    // call passes b, which the preceding b != 0 check forces nonzero. The
    // inverse directive skips the division when its argument is zero.
    assert_eq!(o.traps.len(), 1);
    assert!(o.traps[0].site.guarded_by_callers);
    assert_eq!(o.traps[0].site.function_name, "directive_integer_quotient");
}

#[test]
fn library_whitelist_never_hides_input_falsifiable_items() {
    // Pretend the demo's own source is the library: hint-class items become
    // whitelisted, input-only items get the library class and stay
    // reported, and entry-parameter checks stay plain input-falsifiable.
    let Some(a) = load() else {
        return;
    };
    let o = Outcome::run(&a, vec![own_src(&a)]);
    let counts = o.class_counts();
    assert_eq!(counts[&Class::HintLibrary], 4);
    assert_eq!(counts[&Class::HintUnreviewed], 0);
    assert_eq!(counts[&Class::LibraryInputFalsifiable], 7);
    assert_eq!(counts[&Class::InputFalsifiable], 3);
    assert_eq!(o.unjustified(), 10);
}

#[test]
fn justification_marker_clears_an_item() {
    let Some(mut a) = load() else {
        return;
    };
    let file = Arc::make_mut(&mut a.files)
        .values_mut()
        .find(|f| f.path.ends_with("src/main.nr"))
        .unwrap();
    // Replace the comment above the top-level assert with a marker of the
    // same byte length, so every span stays valid.
    let old = "    // Top-level assert on inputs.";
    let mut new = "    // total-lint: allow demo".to_string();
    while new.len() < old.len() {
        new.push('.');
    }
    assert!(file.source.contains(old));
    let source = file.source.replacen(old, &new, 1);
    *file = total_lint::artifact::SourceFile::new(file.path.clone(), source);
    let o = Outcome::run(&a, default_lib());
    let item = o.items.iter().find(|r| r.item.opcode == 3).unwrap();
    assert!(
        item.justified
            .as_ref()
            .is_some_and(|j| j.reason.starts_with("demo"))
    );
    assert_eq!(o.unjustified(), 13);
    assert_eq!(o.justified(), 1);
}

#[test]
fn json_output_is_complete() {
    let Some(a) = load() else {
        return;
    };
    let o = Outcome::run(&a, default_lib());
    let v = o.render_json(&View::default());
    assert_eq!(v["summary"]["exit_code"], 1);
    assert_eq!(v["summary"]["classes"]["input-falsifiable"], 10);
    assert_eq!(v["items"].as_array().unwrap().len(), 14);
    assert_eq!(v["brillig_calls"].as_array().unwrap().len(), 3);
    let first_located = v["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|i| !i["location"].is_null())
        .unwrap();
    assert_eq!(first_located["location"]["line"], 16);
    let view = View {
        explain: true,
        ..View::default()
    };
    let human = render::render_human(std::slice::from_ref(&o), &view, 0, false);
    assert!(human.contains("what this lint cannot decide statically"));
    assert!(human.contains("RANGE 64 on entry parameter a: u64"));
}
