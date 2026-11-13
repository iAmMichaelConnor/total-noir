//! A static private call whose returns are read as Fields and decoded
//! with flags, so that nothing the callee returns within the interface can
//! fail the caller.
//!
//! What remains outside the flag (each fails the caller's transaction):
//! the callee's own failures (its class's code; lib.nr on upgrades), an
//! unknown target contract or a selector its class does not define (the
//! PXE has no function to run, and the kernel checks the function against
//! the target's class), a callee returning another number of Fields than
//! M + 1 (the returns-preimage check, "Preimage mismatch" or a hint length
//! error: the return arity is part of the interface), a callee that emits
//! side effects under the static call (the kernel rejects the
//! transaction), and the shared per-call and per-transaction budgets.

use aztec::context::PrivateContext;
use aztec::protocol::{abis::function_selector::FunctionSelector, address::AztecAddress};
use total::{bool_or, select_field};

/// Static call of target's private function selector with args, for a
/// callee that returns M value Fields followed by one flag Field:
/// (values, ok). ok is true exactly when the last return Field is 1; on
/// ok = false every value is 0. The callee's returns are read as
/// [Field; M + 1], so no typed decoding can fail; decode the values with
/// flagged conversions (total::convert) and fold those flags into ok.
///
/// Constraints: aztec-nr's call request (one of the 8 nested calls a call
/// holds) and the returns preimage check (hash_args of the hinted returns
/// equals the call's returns hash: hint-satisfiable when the callee
/// returns M + 1 Fields, the honest PXE supplies them); total::bool_or on
/// the flag Field (determined); one select per value. Determined, given
/// the callee's returns.
///
/// Not total by itself: the module header lists what fails the caller,
/// and every item depends on the target and on the calling function (the
/// callee's class, its return arity, the calls made before this one).
/// So this carries no lint marker: total-lint reports the call request
/// and the preimage check in every function that calls it, and the call
/// site justifies them with a total-lint justification marker naming who
/// chooses the target (examples/total_caller: the caller's argument).
///
/// DEV DECISION: a static call, so the callee cannot add note hashes,
/// nullifiers, logs or non-static calls to the caller's transaction (a
/// nullifier that already exists would fail it). Use a plain call
/// (context.call_private_function) where the callee's side effects are
/// wanted.
pub fn static_call_flagged_or<let A: u32, let M: u32>(
    context: &mut PrivateContext,
    target: AztecAddress,
    selector: FunctionSelector,
    args: [Field; A],
) -> ([Field; M], bool) {
    let ret: [Field; M + 1] =
        context.static_call_private_function(target, selector, args).get_preimage();
    decode_flagged_or(ret)
}

/// The decoding half of static_call_flagged_or: the last Field as a flag
/// (exactly 1), the others masked to 0 unless it holds. total::bool_or and
/// one select per value; no assert.
pub fn decode_flagged_or<let M: u32>(ret: [Field; M + 1]) -> ([Field; M], bool) {
    let (flag, is_bool) = bool_or(ret[M]);
    let ok = flag & is_bool;
    let mut out = [0; M];
    for i in 0..M {
        out[i] = select_field(ok, ret[i], 0);
    }
    (out, ok)
}

mod tests {
    use super::decode_flagged_or;

    #[test]
    fn the_flag_is_exactly_one() {
        assert_eq(decode_flagged_or::<2>([7, 8, 1]), ([7, 8], true));
        assert_eq(decode_flagged_or::<2>([7, 8, 0]), ([0, 0], false));
        assert_eq(decode_flagged_or::<2>([7, 8, 2]), ([0, 0], false));
        assert_eq(decode_flagged_or::<2>([7, 8, -1]), ([0, 0], false));
    }
}
