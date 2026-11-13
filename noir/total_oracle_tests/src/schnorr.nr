//! schnorr_inputs_ok and schnorr_verify against a TypeScript model of
//! noir-lang/schnorr v0.4.0's scheme: R = [s]G + [e]P on Grumpkin, accept
//! when P is on the curve, s and e are canonical limb pairs below the group
//! order q and nonzero, R is not infinity, and
//! Poseidon2(SCHNORR_CHALLENGE_DST, R.x, P.x, P.y, msg) == e mod p, with
//! Barretenberg's Poseidon2. Wherever e < p the server also asks
//! Barretenberg's native Schnorr verifier (bb.js) and stops with an error if
//! the two references disagree.
//!
//! Seeded cases: signatures made in TypeScript under random keys and the
//! keys G and -G, unchanged or with a wrong message, a flipped bit in s or
//! e, s or e zero, s + q, e + q, e = q or q - 1, a scalar split
//! non-canonically ((lo + 2^128, hi - 1), or hi = 2^128), e + p (the same
//! challenge as a Field), the negated signature (q - s, q - e), an off-curve
//! key, the key (0, 0), the negated key, a random pair, bb 6.0.0's MSM
//! offset generators o_1, o_2, o_3 and -(1/15) o_2 as keys, s chosen so that R
//! is infinity, s = e = q - 1, random limbs up to the Field modulus, and a
//! signature checked under another key.

use total::schnorr::{schnorr_inputs_ok, schnorr_verify};

pub struct SchnorrCase {
    pk_x: Field,
    pk_y: Field,
    sig: [Field; 4],
    msg: Field,
    inputs_ok: bool,
    valid: bool,
}

#[oracle(schnorr_case)]
unconstrained fn schnorr_case_oracle(seed: Field) -> SchnorrCase {}

unconstrained fn schnorr_case(seed: Field) -> SchnorrCase {
    schnorr_case_oracle(seed)
}

#[test]
fn schnorr_verify_matches_reference(seed: Field) {
    // Safety: the oracle only supplies the case and the expected answers.
    let c = unsafe { schnorr_case(seed) };
    assert_eq(schnorr_inputs_ok(c.pk_x, c.pk_y, c.sig), c.inputs_ok);
    assert_eq(schnorr_verify(c.pk_x, c.pk_y, c.sig, c.msg), c.valid);
}
