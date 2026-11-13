//! The hint-compiler class on the compiler_patterns fixture, compiled at
//! test time (see common/mod.rs): the compiler's directives are recognised
//! by their exact rc.3 bytecode, ordinary total operations are whitelisted,
//! and operations that can fail, or a user hint named like a directive,
//! keep their classes.

use std::collections::{BTreeMap, BTreeSet};

use total_lint::analysis::{Class, Directive};
use total_lint::report::Outcome;

mod common;

/// Classes per attributed source line (trimmed).
fn by_line(o: &Outcome) -> BTreeMap<String, BTreeSet<Class>> {
    let mut out: BTreeMap<String, BTreeSet<Class>> = BTreeMap::new();
    for r in &o.items {
        if r.item.class == Class::Definition {
            continue;
        }
        let Some(i) = r.attributed else { continue };
        let loc = r.stack[i];
        let f = &o.artifact.files[&loc.file];
        let text = f.line_text(f.line_col(loc.start).0).trim().to_string();
        out.entry(text).or_default().insert(r.item.class);
    }
    out
}

#[test]
fn directives_are_recognised_by_bytecode() {
    let Some(a) = common::compile("compiler_patterns") else {
        return;
    };
    let found: BTreeMap<String, Directive> = total_lint::analysis::directives(&a.program)
        .into_iter()
        .map(|(id, d)| (a.brillig_name(id).unwrap().to_string(), d))
        .collect();
    assert_eq!(
        found.get("directive_integer_quotient"),
        Some(&Directive::IntegerQuotient)
    );
    assert_eq!(found.get("directive_to_radix"), Some(&Directive::ToRadix));
    // Two functions are named directive_invert: the compiler's and the
    // fixture's own; only one is recognised.
    let named = a
        .program
        .unconstrained_functions
        .iter()
        .filter(|f| f.function_name == "directive_invert")
        .count();
    assert_eq!(named, 2);
    assert_eq!(
        found.values().filter(|d| **d == Directive::Invert).count(),
        1
    );
}

#[test]
fn total_operations_are_hint_compiler_and_others_are_not() {
    let Some(a) = common::compile("compiler_patterns") else {
        return;
    };
    let o = Outcome::run(&a, Vec::new());
    let lines = by_line(&o);
    let only_compiler: BTreeSet<Class> = [Class::HintCompiler].into();
    for text in [
        "let eq = x == 5;",
        "let byte = i as u8;",
        "let small = byte < 7;",
        "let s = t as u32;",
        "let masked = s & 3;",
        "let half = s / 2;",
        "let le: [u8; 4] = (s as Field).to_le_bytes();",
    ] {
        assert_eq!(lines.get(text), Some(&only_compiler), "{text}: {lines:?}");
    }
    // One byte of an unbounded Field: the digit is in range, the
    // recomposition fails for x >= 256.
    let short = &lines["let short: [u8; 1] = w.to_le_bytes();"];
    assert!(short.contains(&Class::HintCompiler) && short.contains(&Class::HintUnreviewed));
    // Division by a witness: the divisor check is input-falsifiable and
    // the quotient's constraints stay unreviewed.
    let q = &lines["let q = s / d;"];
    assert!(q.contains(&Class::InputFalsifiable) && q.contains(&Class::HintUnreviewed));
    assert!(!q.contains(&Class::HintCompiler));
    // The fake directive's "is-zero" pin is not whitelisted.
    assert_eq!(
        lines.get("assert(w * y == 0);"),
        Some(&[Class::HintUnreviewed].into())
    );
}

#[test]
fn booleanity_of_a_hint_is_reported_and_of_computed_bits_is_not() {
    let Some(a) = common::compile("hint_booleanity") else {
        return;
    };
    let o = Outcome::run(&a, Vec::new());
    let lines = by_line(&o);
    // aztec-nr's `Packable for bool` check on a value a hint supplies,
    // directly or selected through a compiler comparison.
    for text in ["assert(v * v == v);", "assert(w * w == w);"] {
        assert_eq!(
            lines.get(text),
            Some(&[Class::HintUnreviewed].into()),
            "{text}: {lines:?}"
        );
    }
    // Bits computed from the compiler's own directives.
    for text in ["assert(e * e == e);", "assert(k * k == k);"] {
        assert_eq!(
            lines.get(text),
            Some(&[Class::HintCompiler].into()),
            "{text}: {lines:?}"
        );
    }
}
