//! Checks `--brillig-ops` on the mpc_ops_demo fixture, compiled at test
//! time (see common/mod.rs), whose hints hold Brillig opcodes co-noir's
//! MPC VM cannot run:
//! - a black box other than ToRadix (blake2s) is listed, reachable, at
//!   the hint's call to it;
//! - a ConditionalMov, which has no debug location of its own, is
//!   reported at the `if` it comes from, not at the statement before it;
//! - a rolled loop dividing by a constant hoisted above it (bit
//!   decomposition by `% 2` and `/ 2` at E = 126) holds no abort site and
//!   no unsupported op;
//! - two shapes of a guarded u128 division hint hold no abort site: a
//!   remainder inside the else of `b == 0` (its `0 < b` check is known
//!   true) and a quotient by b + (b == 0).

use total_lint::artifact::Artifact;
use total_lint::report::{MpcOpReport, Outcome};

mod common;

fn load() -> Option<Artifact> {
    common::compile("mpc_ops_demo")
}

fn run(a: &Artifact) -> Outcome<'_> {
    Outcome::run(a, Vec::new())
}

/// (file name, line, source text) of the innermost frame the report prints.
fn reported_line(a: &Artifact, o: &MpcOpReport) -> (String, usize, String) {
    let loc = o.stack.last().expect("located");
    let file = &a.files[&loc.file];
    let (line, _) = file.line_col(loc.start);
    let name = file.path.rsplit('/').next().unwrap().to_string();
    (name, line, file.line_text(line).trim().to_string())
}

fn ops<'o>(o: &'o Outcome, function: &str) -> Vec<&'o MpcOpReport> {
    o.mpc_ops
        .iter()
        .filter(|r| r.site.function_name == function)
        .collect()
}

#[test]
fn black_box_other_than_to_radix_is_listed() {
    let Some(a) = load() else {
        return;
    };
    let o = run(&a);
    let digest = ops(&o, "hint_digest");
    assert_eq!(digest.len(), 1);
    assert_eq!(digest[0].site.op, "blake2s");
    assert_eq!(digest[0].site.bit_size, 0);
    assert!(digest[0].site.reachable);
    let (file, _, text) = reported_line(&a, digest[0]);
    assert_eq!(file, "main.nr");
    assert_eq!(text, "std::hash::blake2s([a, b])");
    assert_eq!(o.mpc_ops_exit_code(), 1);
}

#[test]
fn hoisted_constant_divisor_in_a_rolled_loop_cannot_abort() {
    let Some(a) = load() else {
        return;
    };
    let o = run(&a);
    let hint = a
        .program
        .unconstrained_functions
        .iter()
        .position(|f| f.function_name == "hint_low_bits")
        .expect("hint_low_bits is compiled") as u32;
    // The loop stays rolled: the hint holds a Div and a back edge.
    let code = &a.program.unconstrained_functions[hint as usize].bytecode;
    assert!(code.iter().any(|op| matches!(
        op,
        acir::brillig::Opcode::BinaryIntOp {
            op: acir::brillig::BinaryIntOp::Div,
            ..
        }
    )));
    assert!(
        code.iter().enumerate().any(
            |(pc, op)| matches!(op, acir::brillig::Opcode::Jump { location } if *location < pc)
        )
    );
    assert!(o.traps.iter().all(|t| t.site.brillig != hint));
    assert!(ops(&o, "hint_low_bits").is_empty());
}

#[test]
fn conditional_mov_is_reported_at_its_if() {
    let Some(a) = load() else {
        return;
    };
    let o = run(&a);
    let cmov = ops(&o, "hint_sub_if_ge");
    assert_eq!(cmov.len(), 1);
    assert_eq!(cmov[0].site.op, "cmov");
    assert!(cmov[0].site.reachable);
    // nargo gives the cmov no location; the nearest located opcode before
    // it belongs to `let ge = !r.lt(d);`.
    assert_ne!(cmov[0].site.location_pc, Some(cmov[0].site.pc));
    let (file, _, text) = reported_line(&a, cmov[0]);
    assert_eq!(file, "main.nr");
    assert_eq!(text, "if ge {");
    assert_eq!(cmov[0].stack.len(), 1);
}

/// Index of the unconstrained function named `name`.
fn hint(a: &Artifact, name: &str) -> u32 {
    a.program
        .unconstrained_functions
        .iter()
        .position(|f| f.function_name == name)
        .unwrap_or_else(|| panic!("{name} is compiled")) as u32
}

#[test]
fn guarded_u128_divisions_cannot_abort() {
    let Some(a) = load() else {
        return;
    };
    let o = run(&a);
    for name in ["hint_div_branch", "hint_div_branch_free"] {
        let id = hint(&a, name);
        let code = &a.program.unconstrained_functions[id as usize].bytecode;
        assert!(code.iter().any(|op| matches!(
            op,
            acir::brillig::Opcode::BinaryIntOp {
                op: acir::brillig::BinaryIntOp::Div,
                ..
            }
        )));
        assert!(o.traps.iter().all(|t| t.site.brillig != id), "{name}");
    }
    // The remainder's divisor-zero trap is there, and proved unreachable.
    let id = hint(&a, "hint_div_branch");
    let code = &a.program.unconstrained_functions[id as usize].bytecode;
    assert!(
        code.iter()
            .any(|op| matches!(op, acir::brillig::Opcode::Trap { .. }))
    );
}
