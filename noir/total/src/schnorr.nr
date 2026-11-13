//! Schnorr over Grumpkin as noir-lang/schnorr v0.4.0 implements it (the
//! pin Aztec v6.0.0 account contracts use), computed over total's own
//! primitives so that every input gives a flag and a provable witness.
//!
//! The scheme: a public key is a Grumpkin point P; a signature is two
//! Grumpkin scalars (s, e), each as two 128-bit limbs; the message is one
//! Field. The library's verify_signature computes R = [s]G + [e]P with
//! the MSM black box, e' = Poseidon2(SCHNORR_CHALLENGE_DST, R.x, P.x, P.y,
//! message), and accepts when P is on the curve, s and e are nonzero, R is
//! not infinity, and e' == e.lo + 2^128 * e.hi (a Field equation, so
//! mod p).
//!
//! Failure sources of the library's verify_signature, read from the v0.4.0
//! source (src/lib.nr) and its poseidon v0.3.0 dependency:
//! - multi_scalar_mul([G, P], [s, e]), predicated on s != 0 and e != 0.
//!   The ACVM solver aborts witness generation when P is neither (0, 0)
//!   nor on the curve, when any of the four limbs is >= 2^128, or when
//!   lo + 2^128*hi >= q for either scalar (q is the Grumpkin group order,
//!   which exceeds the Field modulus p). All three are reachable from the
//!   library's public inputs: an off-curve key, a non-canonical limb split
//!   such as (lo + 2^128, hi - 1), or a scalar in [q, 2^256). Called
//!   directly, the library fails `nargo execute` (nargo 1.0.0-rc.3) on
//!   each.
//! - The same black box in bb 6.0.0: P is a witness base, and bb's MSM
//!   gadget asserts x-coordinate distinctness against public points of its
//!   own (ec::msm_or describes both families of assertions). A valid key
//!   in a known relation to those points, such as one of them (o_2) or
//!   -(1/15) o_2, passes the solver with any nonzero s and e and has no
//!   proof. Whoever chooses the key can make an honest prover's
//!   verification unprovable.
//! - The rest is total: is_on_curve (the curve equation and an inversion
//!   gadget), the scalar != 0 tests (inversion gadgets), Poseidon2::hash
//!   on a fixed 5-element array (permutation black boxes and additions;
//!   the sponge's asserts are in absorb/squeeze, which hash() does not
//!   call), R.is_infinite(), the limb recombination and the final
//!   equality. There are no byte decompositions and no variable lengths.
//!
//! schnorr_verify therefore does not call verify_signature. It computes
//! the same function with ec::msm_or for R (input validation, then the
//! blinded black box, provable for every input), hash::p2_hash for the
//! challenge and the library's SCHNORR_CHALLENGE_DST. p2_hash on five
//! Fields equals the library's Poseidon2::hash(input, 5) (test
//! generated_signatures_verify: signatures made with p2_hash are accepted
//! by the library). The tests compare schnorr_verify with verify_signature
//! on every vector where both run.
//!
//! Malleability:
//! - s and e must be canonical limb pairs below q, so the only encodings
//!   of a scalar the wrapper accepts are the canonical ones; s + q,
//!   e + q, and split limbs give ok = false (tests below).
//! - The challenge is compared as a Field, so e and e + p encode the
//!   same challenge when e + p < q, i.e. e < q - p (about 2^126.8). The
//!   wrapper accepts what the library accepts here. Reusing a valid
//!   (s, e) with e + p changes R, so a third party cannot exploit it; a
//!   signer holding the key can produce a second valid encoding
//!   (s - p*x, e + p) only for the rare signature whose challenge is
//!   below q - p (probability about 2^-127 per signature). Callers that
//!   need a unique encoding per signature can additionally require
//!   e < p.
//! - (q - s, q - e) yields R' = -R, which has the same x, but the
//!   challenge q - e differs from e mod p, so it fails (test below).
//!
//! Verified on nargo 1.0.0-rc.3 and bb 6.0.0: the tests below; the oracle
//! tests in noir/total_oracle_tests (a TypeScript model checked against
//! bb.js's native Schnorr verifier, with off-curve, infinity and offset-
//! generator keys among the cases); and noir/total_prove_check, which
//! proves and verifies schnorr_verify with bb on the library's pinned
//! vectors and on the keys o_2 and -(1/15) o_2.
//!
//! Cost (bb 6.0.0 circuit size of a program calling it on entry-point
//! Fields): schnorr_verify 5481 gates. The library's
//! verify_signature alone is 4178 gates, with no input flags and no proof
//! for the keys above.
//!
//! Lint (total-lint): schnorr_verify reaches no function of the schnorr
//! package, only its SCHNORR_CHALLENGE_DST constant; its hints are
//! msm_or's and the inversion gadgets', all in this library.

use crate::core::{eq, is_zero, TWO_POW_128};
use crate::ec::{msm_or, on_curve_flag, Point, scalar_limbs_or};
use crate::hash::p2_hash;
use schnorr::SCHNORR_CHALLENGE_DST;

/// Flag: (pk, sig) is an input the library's MSM accepts. pk is on the
/// Grumpkin curve (which excludes std's (0, 0) infinity encoding, since
/// (0, 0) is not on the curve), and each of s = (sig[0], sig[1]) and
/// e = (sig[2], sig[3]) is a canonical limb pair: both limbs below 2^128
/// and lo + 2^128*hi below q. Equal to the flag schnorr_verify gets from
/// ec::msm_or (test inputs_ok_is_msm_flag).
///
/// Constraints: ec::on_curve_flag (arithmetic definitions and one
/// inversion gadget) and ec::scalar_limbs_or twice (core::fits_128 on each
/// limb, core::lt_bounded::<128> twice and an eq gadget on the clamped
/// limbs). All hint-satisfiable for every input; no hints of its own.
/// Determined: every flag it ANDs is.
pub fn schnorr_inputs_ok(pk_x: Field, pk_y: Field, sig: [Field; 4]) -> bool {
    let (_, _, s_ok) = scalar_limbs_or(sig[0], sig[1]);
    let (_, _, e_ok) = scalar_limbs_or(sig[2], sig[3]);
    on_curve_flag(pk_x, pk_y) & s_ok & e_ok
}

/// Schnorr verification over Grumpkin, total for every input. sig is
/// [s_lo, s_hi, e_lo, e_hi], the layout Aztec v6 account contracts read
/// from the auth witness. Returns true exactly when schnorr_inputs_ok
/// holds and noir-lang/schnorr v0.4.0 verify_signature accepts
/// (pk, (s, e), msg). Off-curve or infinity keys, out-of-range or split
/// limbs, scalars >= q, zero scalars, and wrong signatures all give false.
///
/// How: (R, ok_in) = ec::msm_or([G, P], [s, e]) with P the finite Point
/// (pk_x, pk_y). msm_or's flag is schnorr_inputs_ok: G is well-formed, a
/// finite Point is well-formed exactly when it is on the curve, and each
/// scalar passes scalar_limbs_or. On ok_in = false R is infinity. The
/// result is ok_in AND s != 0 AND e != 0 (both limbs zero, as the
/// library's EmbeddedCurveScalar comparison) AND R is not infinity AND
/// p2_hash([SCHNORR_CHALLENGE_DST, R.x, pk_x, pk_y, msg]) equals
/// e_lo + 2^128 e_hi as a Field. Under ok_in each term is the library's.
///
/// Constraints: ec::msm_or (hint-satisfiable for every input, see its doc
/// comment), four is_zero gadgets, p2_hash on five Fields (two Poseidon2
/// permutation black boxes and additions), one eq gadget and bool
/// arithmetic. No hints of its own beyond msm_or's and the gadgets'.
/// Determined: msm_or's point and flag are, and the rest are gadgets on
/// them.
pub fn schnorr_verify(pk_x: Field, pk_y: Field, sig: [Field; 4], msg: Field) -> bool {
    let pk = Point { x: pk_x, y: pk_y, inf: false };
    let (r, ok_in) = msm_or([Point::generator(), pk], [sig[0], sig[2]], [sig[1], sig[3]]);
    let s_nz = !(is_zero(sig[0]) & is_zero(sig[1]));
    let e_nz = !(is_zero(sig[2]) & is_zero(sig[3]));
    let challenge = p2_hash([SCHNORR_CHALLENGE_DST, r.x, pk_x, pk_y, msg]);
    ok_in & s_nz & e_nz & !r.inf & eq(challenge, sig[2] + sig[3] * TWO_POW_128)
}

mod tests {
    use crate::core::TWO_POW_128;
    use crate::ec::{msm_or, Point};
    use crate::ec::{ORDER_HI, ORDER_LO};
    use crate::hash::p2_hash;
    use crate::test_support::wit as w;
    use super::{schnorr_inputs_ok, schnorr_verify};
    use schnorr::{SCHNORR_CHALLENGE_DST, verify_signature};
    use std::embedded_curve_ops::{EmbeddedCurvePoint, EmbeddedCurveScalar, multi_scalar_mul};
    use std::ops::Neg;

    // Low and high limbs of the Field modulus p.
    global PLO: Field = 53438638232309528389504892708671455233;
    global PHI: Field = 64323764613183177041862057485226039389;

    // pinned_vector_large from the library's tests.
    global L_PK_X: Field = 0x065812e335a97c2108ea8cf4ccfe2f9dd6b117a0714f5e18461575be93f61da6;
    global L_PK_Y: Field = 0x1a915003e8ec534f9a15d926a7ded478e178468ccc4f28e236e67450a55ac622;
    global L_SIG: [Field; 4] = [
        0xf3bc3b7147acb9c621fd9f72dbf15ffa,
        0x08599f379f0301dfefdbd0272554454d,
        0x97065383ebbbd76620398792bd259bc2,
        0x2ceaee87f45b7a417f0ffb05451a8c92,
    ];
    global L_MSG: Field = 0x0123456789abcdef0fedcba9876543210123456789abcdef0fedcba987654321;

    // pinned_vector_small from the library's tests (src/lib.nr, mirroring
    // the C++ test schnorr.pinned_test_vector_small): a valid signature on
    // message 0x2bc.
    global SMALL_PK_X: Field = 0x2c39bbbde2d0ffcb5c4317dcbfa1771cf554a2f33c647446632fa707a5bf5f3f;
    global SMALL_PK_Y: Field = 0x2b9c81935298af5ebe22f1a7279bb76781e6cadba3fb6c5c41ed942392dc687c;
    global SMALL_S_LO: Field = 0x5fd1ac0ad411110674830c54cb506212;
    global SMALL_S_HI: Field = 0x281906862cdb4e0efec7226d757fe803;
    global SMALL_E_LO: Field = 0x6c368959f958e525d761d06c47fd2ad6;
    global SMALL_E_HI: Field = 0x013f6a902c6c0efafdadbd4de409690d;
    global SMALL_MSG: Field = 0x2bc;

    global S_SIG: [Field; 4] = [SMALL_S_LO, SMALL_S_HI, SMALL_E_LO, SMALL_E_HI];

    // bb 6.0.0's MSM offset generators o_1, o_2, o_3 and -(1/15) o_2 (see
    // ec::msm_or): keys the library's black-box call cannot prove.
    global OFFGEN_KEYS: [(Field, Field); 4] = [
        (
            0x07ecf4931ea0257c089816cfc3ed44c9172b22622539fdad7535401a7a99fb4b,
            0x0f8bf0d676c12c8e10ea1f8fe9e5100db24b89ef3006b321f2178adc6281ec74,
        ),
        (
            0x0fb76e5904e203fe96cf620f86739e685c85c56774b23c1e7c86fba3290ae42b,
            0x2a32122a08e2dcc594f4b657eb5e2e4f84cb67f06ab4b2d432c5f61c22330a3f,
        ),
        (
            0x2e09e700d6472d6d69189b06ddde8a0c0a559603086c619abc217c43534866f6,
            0x0ff3c9ddfc6aaa740822422a0cf194a98d6a06ec2c433435b5bae6a172d56b5f,
        ),
        (
            0x23d26cbbc30f73d118577822621b815c5237a7e239312ff1d197ba4948a2ee9a,
            0x3029dcebcc17d09a134832fe0eafa83f5b8d09b522ac9c352475441c24ed6c02,
        ),
    ];

    fn w4(a: [Field; 4]) -> [Field; 4] {
        [w(a[0]), w(a[1]), w(a[2]), w(a[3])]
    }

    /// The library's verify_signature on the same inputs.
    fn library(pk_x: Field, pk_y: Field, sig: [Field; 4], msg: Field) -> bool {
        verify_signature(
            EmbeddedCurvePoint::new(pk_x, pk_y),
            (EmbeddedCurveScalar::new(sig[0], sig[1]), EmbeddedCurveScalar::new(sig[2], sig[3])),
            msg,
        )
    }

    /// schnorr_verify on runtime witnesses, checked against the library
    /// wherever the library's solver accepts the inputs (schnorr_inputs_ok).
    fn verify_w(pk_x: Field, pk_y: Field, sig: [Field; 4], msg: Field) -> bool {
        let v = schnorr_verify(w(pk_x), w(pk_y), w4(sig), w(msg));
        if schnorr_inputs_ok(pk_x, pk_y, sig) {
            assert_eq(v, library(pk_x, pk_y, sig, msg));
        }
        v
    }

    fn limbs_of(x: Field) -> (Field, Field) {
        let s = EmbeddedCurveScalar::from_field(x);
        (s.lo, s.hi)
    }

    /// Sign msg under the key 1 (public key G) with nonce p - 1:
    /// R = [p - 1]G, e = challenge, s = (p - 1) - e. No reduction mod q is
    /// needed because e <= p - 1. Trap-free.
    unconstrained fn sign_key_one(msg: Field) -> (Field, Field, [Field; 4]) {
        let g = EmbeddedCurvePoint::generator();
        let k: Field = 0 - 1;
        let r = multi_scalar_mul([g], [EmbeddedCurveScalar::from_field(k)]);
        let e = p2_hash([SCHNORR_CHALLENGE_DST, r.x, g.x, g.y, msg]);
        let (s_lo, s_hi) = limbs_of(k - e);
        let (e_lo, e_hi) = limbs_of(e);
        (g.x, g.y, [s_lo, s_hi, e_lo, e_hi])
    }

    /// Sign msg under the key q - 1 (public key -G) with nonce 1: R = G,
    /// s = 1 + e mod q = 1 + e as an integer (below p + 1 <= q). Assumes
    /// e != p - 1 (else the Field sum wraps; the test would then fail, not
    /// pass). Trap-free.
    unconstrained fn sign_key_minus_one(msg: Field) -> (Field, Field, [Field; 4]) {
        let g = EmbeddedCurvePoint::generator();
        let pk = g.neg();
        let e = p2_hash([SCHNORR_CHALLENGE_DST, g.x, pk.x, pk.y, msg]);
        let (s_lo, s_hi) = limbs_of(1 + e);
        let (e_lo, e_hi) = limbs_of(e);
        (pk.x, pk.y, [s_lo, s_hi, e_lo, e_hi])
    }

    // --- positive ---

    #[test]
    fn small_vector_verifies() {
        assert(library(SMALL_PK_X, SMALL_PK_Y, S_SIG, SMALL_MSG));
        assert(schnorr_inputs_ok(SMALL_PK_X, SMALL_PK_Y, S_SIG));
        assert(verify_w(SMALL_PK_X, SMALL_PK_Y, S_SIG, SMALL_MSG));
    }

    #[test]
    fn large_vector_verifies() {
        assert(verify_w(L_PK_X, L_PK_Y, L_SIG, L_MSG));
        assert(schnorr_verify(L_PK_X, L_PK_Y, L_SIG, L_MSG));
    }

    // Signatures generated in unconstrained code with total::hash::p2_hash
    // as the challenge hash; the library accepting them also pins that
    // p2_hash matches the library's Poseidon2 on 5 inputs. Keys G and -G
    // put two points with the same x into the MSM.
    #[test]
    fn generated_signatures_verify() {
        for m in [0, 1, 0x2bc, 0 - 1] {
            // Safety: test-only signing.
            let (x, y, sig) = unsafe { sign_key_one(m) };
            assert(verify_w(x, y, sig, m));
            assert(!verify_w(x, y, sig, m + 1));
            // Safety: test-only signing.
            let (x2, y2, sig2) = unsafe { sign_key_minus_one(m) };
            assert(verify_w(x2, y2, sig2, m));
            assert(!verify_w(x, y, sig2, m));
        }
    }

    // --- wrong signatures: well-formed, rejected by the scheme ---

    #[test]
    fn wrong_message_or_scalars_rejected() {
        assert(!verify_w(L_PK_X, L_PK_Y, L_SIG, L_MSG + 1));
        assert(
            !verify_w(
                L_PK_X,
                L_PK_Y,
                [L_SIG[0] + 1, L_SIG[1], L_SIG[2], L_SIG[3]],
                L_MSG,
            ),
        );
        assert(
            !verify_w(
                L_PK_X,
                L_PK_Y,
                [L_SIG[0], L_SIG[1], L_SIG[2] + 1, L_SIG[3]],
                L_MSG,
            ),
        );
        // the other vector's signature under this key
        assert(!verify_w(L_PK_X, L_PK_Y, S_SIG, L_MSG));
        // the small vector's key with the large vector's signature
        assert(!verify_w(SMALL_PK_X, SMALL_PK_Y, L_SIG, SMALL_MSG));
    }

    /// Trap-free: a Field comparison.
    unconstrained fn lt_hint(a: Field, b: Field) -> bool {
        a.lt(b)
    }

    /// (a + b) as limbs for limb pairs with every limb below 2^128.
    fn add_limbs(a_lo: Field, a_hi: Field, b_lo: Field, b_hi: Field) -> (Field, Field) {
        let sum = a_lo + b_lo;
        // Safety: test-only; the carry is checked by the value test below.
        let carry = !unsafe { lt_hint(sum, TWO_POW_128) };
        let c = carry as Field;
        (sum - c * TWO_POW_128, a_hi + b_hi + c)
    }

    /// q - (lo + 2^128 hi) as limbs, for a value below q.
    fn q_minus(lo: Field, hi: Field) -> (Field, Field) {
        // Safety: test-only; a borrow is needed exactly when lo > ORDER_LO.
        let borrow = unsafe { lt_hint(ORDER_LO, lo) };
        let b = borrow as Field;
        (ORDER_LO + b * TWO_POW_128 - lo, ORDER_HI - b - hi)
    }

    #[test]
    fn negated_signature_rejected() {
        // (q - s, q - e): R' = -R has the same x, but the challenge differs
        let (s_lo, s_hi) = q_minus(L_SIG[0], L_SIG[1]);
        let (e_lo, e_hi) = q_minus(L_SIG[2], L_SIG[3]);
        let sig = [s_lo, s_hi, e_lo, e_hi];
        assert(schnorr_inputs_ok(L_PK_X, L_PK_Y, sig));
        assert(!verify_w(L_PK_X, L_PK_Y, sig, L_MSG));
    }

    // --- malformed keys: the library would abort; the wrapper flags ---

    #[test]
    fn off_curve_key_rejected() {
        assert(!schnorr_inputs_ok(L_PK_X, L_PK_Y + 1, L_SIG));
        assert(!verify_w(L_PK_X, L_PK_Y + 1, L_SIG, L_MSG));
        assert(!verify_w(L_PK_X + 1, L_PK_Y, L_SIG, L_MSG));
        assert(!verify_w(1, 1, L_SIG, L_MSG));
        assert(!verify_w(0 - 1, 0 - 1, L_SIG, L_MSG));
        // the small vector's key with one coordinate changed
        assert(!verify_w(SMALL_PK_X, SMALL_PK_Y + 1, S_SIG, SMALL_MSG));
    }

    #[test]
    fn infinity_key_rejected() {
        assert(!schnorr_inputs_ok(0, 0, L_SIG));
        assert(!verify_w(0, 0, L_SIG, L_MSG));
        assert(!verify_w(0, 0, [0, 0, 0, 0], 0));
    }

    // --- zero and out-of-range scalars ---

    #[test]
    fn zero_scalars_rejected() {
        assert(!verify_w(L_PK_X, L_PK_Y, [0, 0, L_SIG[2], L_SIG[3]], L_MSG));
        assert(!verify_w(L_PK_X, L_PK_Y, [L_SIG[0], L_SIG[1], 0, 0], L_MSG));
        assert(!verify_w(L_PK_X, L_PK_Y, [0, 0, 0, 0], L_MSG));
        // a zero scalar is well-formed: the library itself says false
        assert(schnorr_inputs_ok(L_PK_X, L_PK_Y, [0, 0, 0, 0]));
    }

    #[test]
    fn limb_out_of_range_rejected() {
        let t = TWO_POW_128;
        // non-canonical split of the same integer s: (lo + 2^128, hi - 1)
        let split = [L_SIG[0] + t, L_SIG[1] - 1, L_SIG[2], L_SIG[3]];
        assert(!schnorr_inputs_ok(L_PK_X, L_PK_Y, split));
        assert(!verify_w(L_PK_X, L_PK_Y, split, L_MSG));
        let split_e = [L_SIG[0], L_SIG[1], L_SIG[2] + t, L_SIG[3] - 1];
        assert(!verify_w(L_PK_X, L_PK_Y, split_e, L_MSG));
        // limbs at and around 2^128, and p - 1
        assert(!verify_w(L_PK_X, L_PK_Y, [t, 0, L_SIG[2], L_SIG[3]], L_MSG));
        assert(!verify_w(L_PK_X, L_PK_Y, [L_SIG[0], t, L_SIG[2], L_SIG[3]], L_MSG));
        assert(!verify_w(L_PK_X, L_PK_Y, [0 - 1, 0, L_SIG[2], L_SIG[3]], L_MSG));
        assert(!verify_w(L_PK_X, L_PK_Y, [L_SIG[0], L_SIG[1], 0 - 1, 0 - 1], L_MSG));
        // 2^128 - 1 limbs are in range; the value is >= q via the high limb
        assert(!verify_w(L_PK_X, L_PK_Y, [t - 1, t - 1, L_SIG[2], L_SIG[3]], L_MSG));
    }

    #[test]
    fn scalar_order_boundary() {
        // q itself and q - 1 for s; q - 1 is well-formed
        assert(!schnorr_inputs_ok(L_PK_X, L_PK_Y, [ORDER_LO, ORDER_HI, 1, 0]));
        assert(
            !verify_w(
                L_PK_X,
                L_PK_Y,
                [ORDER_LO, ORDER_HI, L_SIG[2], L_SIG[3]],
                L_MSG,
            ),
        );
        assert(
            schnorr_inputs_ok(
                L_PK_X,
                L_PK_Y,
                [ORDER_LO - 1, ORDER_HI, ORDER_LO - 1, ORDER_HI],
            ),
        );
        assert(
            !verify_w(
                L_PK_X,
                L_PK_Y,
                [ORDER_LO - 1, ORDER_HI, ORDER_LO - 1, ORDER_HI],
                L_MSG,
            ),
        );
        // q + 1 for e
        assert(
            !verify_w(
                L_PK_X,
                L_PK_Y,
                [L_SIG[0], L_SIG[1], ORDER_LO + 1, ORDER_HI],
                L_MSG,
            ),
        );
    }

    // Results at infinity: well-formed inputs whose R = [s]G + [e]P is the
    // point at infinity. The MSM returns (0, 0) and the library says false.
    #[test]
    fn result_at_infinity_rejected() {
        let g = EmbeddedCurvePoint::generator();
        // P = G, s = 5, e = q - 5
        let sig = [5, 0, ORDER_LO - 5, ORDER_HI];
        assert(schnorr_inputs_ok(g.x, g.y, sig));
        assert(!verify_w(g.x, g.y, sig, 7));
        // P = -G, s = e = 5
        let n = g.neg();
        assert(!verify_w(n.x, n.y, [5, 0, 5, 0], 7));
    }

    // --- malleated encodings of a valid signature ---

    #[test]
    fn malleated_encodings_rejected() {
        // s + q and e + q: canonical limbs below 2^128, value >= q
        let (s_lo, s_hi) = add_limbs(L_SIG[0], L_SIG[1], ORDER_LO, ORDER_HI);
        let s_q = [s_lo, s_hi, L_SIG[2], L_SIG[3]];
        assert(!schnorr_inputs_ok(L_PK_X, L_PK_Y, s_q));
        assert(!verify_w(L_PK_X, L_PK_Y, s_q, L_MSG));
        let (e_lo, e_hi) = add_limbs(L_SIG[2], L_SIG[3], ORDER_LO, ORDER_HI);
        assert(!verify_w(L_PK_X, L_PK_Y, [L_SIG[0], L_SIG[1], e_lo, e_hi], L_MSG));
        // e + p: the same Field challenge, but for both pinned vectors
        // e >= q - p, so e + p >= q is out of range for the MSM
        let (p_lo, p_hi) = add_limbs(L_SIG[2], L_SIG[3], PLO, PHI);
        assert_eq(p_lo + p_hi * TWO_POW_128, L_SIG[2] + L_SIG[3] * TWO_POW_128);
        let e_p = [L_SIG[0], L_SIG[1], p_lo, p_hi];
        assert(!schnorr_inputs_ok(L_PK_X, L_PK_Y, e_p));
        assert(!verify_w(L_PK_X, L_PK_Y, e_p, L_MSG));
        let (d_lo, d_hi) = add_limbs(S_SIG[2], S_SIG[3], PLO, PHI);
        assert(
            !verify_w(
                SMALL_PK_X,
                SMALL_PK_Y,
                [S_SIG[0], S_SIG[1], d_lo, d_hi],
                SMALL_MSG,
            ),
        );
        // s + p: a different scalar mod q (p is not a multiple of q)
        let (sp_lo, sp_hi) = add_limbs(S_SIG[0], S_SIG[1], PLO, PHI);
        assert(
            !verify_w(
                SMALL_PK_X,
                SMALL_PK_Y,
                [sp_lo, sp_hi, S_SIG[2], S_SIG[3]],
                SMALL_MSG,
            ),
        );
    }

    // The input flags pick out exactly the inputs the MSM accepts.
    #[test]
    fn inputs_ok_flags() {
        let g = EmbeddedCurvePoint::generator();
        assert(schnorr_inputs_ok(g.x, g.y, [0, 0, 0, 0]));
        assert(schnorr_inputs_ok(g.x, g.y, [TWO_POW_128 - 1, 0, 0, ORDER_HI - 1]));
        assert(!schnorr_inputs_ok(g.x, g.y, [0, 0, 0, TWO_POW_128]));
        assert(!schnorr_inputs_ok(g.x, 0 - g.y + 1, [0, 0, 0, 0]));
    }

    // msm_or's flag inside schnorr_verify is schnorr_inputs_ok.
    #[test]
    fn inputs_ok_is_msm_flag() {
        let g = EmbeddedCurvePoint::generator();
        let t = TWO_POW_128;
        let keys = [(L_PK_X, L_PK_Y), (L_PK_X, L_PK_Y + 1), (0, 0), (g.x, g.y), (1, 1)];
        let sigs = [
            L_SIG,
            [0, 0, 0, 0],
            [ORDER_LO, ORDER_HI, 1, 0],
            [ORDER_LO - 1, ORDER_HI, ORDER_LO - 1, ORDER_HI],
            [L_SIG[0] + t, L_SIG[1] - 1, L_SIG[2], L_SIG[3]],
            [1, 0, 0, t],
        ];
        for i in 0..5 {
            for j in 0..6 {
                let (x, y) = keys[i];
                let s = sigs[j];
                let pk = Point { x: w(x), y: w(y), inf: false };
                let (_, ok) = msm_or(
                    [Point::generator(), pk],
                    [w(s[0]), w(s[2])],
                    [w(s[1]), w(s[3])],
                );
                assert_eq(ok, schnorr_inputs_ok(w(x), w(y), w4(s)));
            }
        }
    }

    // Keys at bb's offset generators: on the curve, so the flags pass, and
    // no signature verifies (nobody knows their discrete logs). The
    // library's answer agrees; noir/total_prove_check proves o_2 and
    // -(1/15) o_2 with bb.
    #[test]
    fn offset_generator_keys_rejected() {
        for i in 0..4 {
            let (x, y) = OFFGEN_KEYS[i];
            assert(schnorr_inputs_ok(x, y, L_SIG));
            assert(!verify_w(x, y, L_SIG, L_MSG));
            assert(!verify_w(x, y, [5, 0, 7, 0], 0));
            assert(!verify_w(x, y, [ORDER_LO - 1, ORDER_HI, ORDER_LO - 1, ORDER_HI], 1));
        }
    }
}
