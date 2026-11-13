//! ECDSA over secp256k1 and secp256r1 through the std black boxes
//! (std::ecdsa_secp256k1::verify_signature and the r1 variant), wrapped so
//! that every input gives a flag instead of an unprovable circuit.
//!
//! What the black box does, on this toolchain (nargo 1.0.0-rc.3, bb
//! 6.0.0). Verified with probe programs that call the std function
//! directly (not included in this repository), each case run through
//! `nargo execute` (the ACVM solver) and then `bb prove --verify` on the
//! solver's witness (the backend's constraints). Sources read:
//! acvm-repo/blackbox_solver/src/ecdsa at noir 5a7ee9b, and barretenberg
//! dsl/acir_format/ecdsa_constraints.cpp, stdlib/encryption/ecdsa/
//! ecdsa_impl.hpp and stdlib/primitives/biggroup at aztec-packages v6.0.0.
//! - The ACIR is one ECDSA black-box opcode over 160 byte witnesses plus
//!   the output. The std function adds no RANGE of its own; the byte
//!   arrays are u8-typed, so their range comes from wherever the caller
//!   created them. bb range-checks each byte to 8 bits inside the gadget,
//!   which every u8 satisfies.
//! - The ACVM solver never aborts: zero or out-of-range r or s, a high s
//!   (s > n/2, BIP-62), an off-curve key, the all-zero key, and
//!   coordinates >= p all return false. Its only error path ("Unexpected
//!   coordinate encoding") is unreachable for uncompressed points.
//! - bb's gadget is flag-based too: coordinate-range, infinity and
//!   on-curve flags, r and s range and zero flags. It replaces the key by
//!   2G before the multiplication only when the key is infinity or has a
//!   coordinate >= p. secp256r1 also replaces an off-curve key; secp256k1
//!   does not, and runs the multiplication on the off-curve point (class 3
//!   below). For the other malformed inputs (zero or out-of-range r or s,
//!   high s, coordinates >= p, the all-zero key, a random off-curve key)
//!   the probe proves and verifies with output false, on both curves.
//!   Also proved: keys G, -G and 2G, u1 = u2 with key G, hash 0, hash = n,
//!   hash + n and hash 2^256 - 1 (the hash is reduced mod n by both
//!   sides), and r = s + n.
//! - Three input classes make the solver and bb disagree, and then no
//!   proof exists for the solver's witness ("Builder failure when we have
//!   real witnesses", verification fails). Classes 1 and 2 are easy to
//!   build for anyone who chooses the public key (pick R and the
//!   signature, solve for the key); class 3 is a choice of key bytes:
//!   1. Both curves: r < p - n with R = u1 G + u2 P having R.x = r + n.
//!      The solver requires R.x < n and R.x == r, so it returns false;
//!      bb checks R.x == r mod n (the textbook rule), so its circuit
//!      requires true. p - n is about 2^128.3 (k1) and 2^126.1 (r1).
//!   2. secp256r1 only: u2 = r/s in {1, -1} mod n, i.e. r == s or
//!      r + s == n. The solver computes the real result (true for a
//!      textbook-valid signature); bb's fake-GLV multiplication cannot
//!      handle u2 in {0, 1, -1} and reports false. secp256k1 uses a real
//!      endomorphism and agrees with the solver here (probed: true and
//!      provable).
//!   3. secp256k1 only: a key with coordinates < p that is not on the
//!      curve and has small order on its own curve y^2 = x^3 + b'
//!      (b' = y^2 - x^3; the addition formulas do not use b). (0, y) has
//!      order 3 there and (x, 0) order 2, so building the multiplication's
//!      4-bit table (P, 3P, ..., 15P) divides by zero. Probed: keys
//!      (0, 1), (0, 2) and (5, 0) execute with output false and bb prove
//!      fails. Other small orders would fail the same way; a random
//!      off-curve key proves.
//!   u1 = z/s in {1, -1} is not a further class: bb computes u1 G with
//!   fixed-base tables, and only u2 goes through the fake-GLV path.
//!   Probed on both curves (s = 1, hash 1 or n - 1): the solver and bb
//!   both say true for the raw std function and the typed wrapper (test
//!   unit_u1_verifies).
//! - Where solver and bb agree, bb's multiplication u1 G + u2 P can still
//!   have no proof, because it is built from incomplete additions that
//!   assert distinct x-coordinates and from divisions that assert a
//!   non-zero divisor (docs/ecdsa-totality.md, section 3):
//!   - Exact collisions. secp256k1 (secp256k1_ecdsa_mul): each of the 96
//!     additions of its ladder asserts x(A) != x(P) and x(A) != x(A + P)
//!     for the accumulator A and the table point P (a multiple of G,
//!     lambda G, P or lambda P). A key solved for one of these relations
//!     fails, and so do inputs with R = u1 G + u2 P a short multiple of G
//!     (R at infinity: P = -(z/r) G) and suitable trailing digits of u2.
//!     secp256r1 (secp256r1_ecdsa_mul): u1 G is a chain of 37 incomplete
//!     additions over fixed-base table points offset by one generator,
//!     and u2 P is checked by a 128-bit two-point multiplication that
//!     starts from a second generator H: keys in fixed relations with H
//!     fail for the matching u2, such as -(1/4) H or (1/4) H with u2 = 5,
//!     and H itself.
//!   - Aliasing. bb's non-equality check (bigfield::assert_is_not_equal)
//!     compares the two integers modulo the circuit's native modulus N
//!     only, so it also fails for values that differ by k p + j N. Every
//!     x-check above has this form, and so has the divisor check of every
//!     doubling and of every "complete" addition. An input whose final
//!     point R has x(R) = x(-lambda G) + N, with a u2 whose halves are
//!     odd, fails in the skew addition that closes the secp256k1
//!     multiplication for half of all u1.
//!   These depend on relations of the key or of R that no cheap flag on
//!   the bytes can see, and an honest input meets them only with
//!   negligible probability; but whoever chooses the inputs can make them.
//!   So the raw std function is NOT total on this toolchain: an attacker
//!   who controls the key can make the honest prover fail.
//! - A fourth class the wrappers gate: r >= n. It is never a valid
//!   signature (solver and bb both say false), but r == 0 mod n would
//!   leave u1 = z'/s the same for every blind (class 4).
//!
//! The wrappers do two things.
//! 1. They exclude classes 1-4 and route them through the select-to-dummy
//!    pattern (see lib.nr). Classes 1, 2 and 4 are flagged from the
//!    signature bytes alone (ecdsa_*_sig_admissible): class 1 by requiring
//!    r >= p - n (then R.x = r + n would be >= p, impossible), class 2 by
//!    requiring r != s and r + s != n, class 4 by requiring r < n (which
//!    rejects no valid signature). An honest signature lands in an
//!    excluded class with probability about 2^-128 (k1) and 2^-130 (r1),
//!    so these gates reject valid signatures only negligibly often; the
//!    inputs they do reject are not provable with the raw function anyway.
//!    Class 3 is excluded by validating the key in Noir on both curves
//!    (total::secp: x < p, y < p and y^2 == x^3 + ax + b mod p, by hinted
//!    non-native reduction, determined): when it fails, every input is
//!    replaced by the dummy before the black box runs. Both curves have
//!    cofactor 1, so every key that passes has order n and is outside
//!    class 3. The dummy is the std test vector of each curve.
//! 2. They blind the key (ecdsa/blind.nr). The black box runs on
//!    (Q', r, s, z') with Q' = Q + beta G and z' = z - r beta mod n, for a
//!    blind beta the prover chooses: then (z'/s) G + (r/s) Q' = R, so the
//!    black box decides exactly what it would decide on (Q, r, s, z).
//!    beta G and the sum Q + beta G are computed and checked in-circuit (a
//!    fixed-base sum over public tables and non-native field identities,
//!    about 19,300 gates), so the verdict does not depend on the prover's
//!    choice. Every non-zero beta with beta G != +-Q is available, and
//!    r != 0 mod n (class 4), so the prover can give the black box any
//!    scalar u1 = z'/s. The honest hint (ecdsa/blind_hint.nr) draws u1
//!    from Poseidon2 of the inputs, emulates bb's multiplication for it
//!    (ecdsa/k1_emul.nr, ecdsa/r1_emul.nr) and moves to the next candidate
//!    when the emulation finds a failing assertion.
//!
//! What that means for the guarantees:
//! - Soundness of ok = true is the black box's: bb checks the blinded key
//!   is on the curve with canonical coordinates, r and s in range, low s,
//!   and the verification equation, all in-circuit, and blind.nr's
//!   constraints make the blinded call's verdict equal the verdict on the
//!   inputs for every hint they accept. The gates only make ok stricter.
//! - Totality, for the black box: it only ever sees an on-curve key with
//!   canonical coordinates and a signature outside classes 1, 2 and 4.
//!   docs/ecdsa-totality.md states and proves what holds: for every
//!   such input a blind exists for which bb's gadget is satisfied (T1),
//!   and the honest hint finds one except with negligible probability
//!   (T2: below 2^-90 on secp256k1 in the random-oracle model). The proof
//!   is by counting over the scalars u1, from bb 6.0.0's source, with
//!   finite computations redone by scripts/ecdsa_totality_checks.py and
//!   scripts/ecdsa_alias_multiplicity.py. It rests on one named
//!   assumption about bb (aliasing between two x-coordinates that both
//!   move with the key is negligible: the same heuristic bb relies on
//!   for honest inputs), on the hint's emulation matching bb (tested by
//!   scripts/ecdsa_differential.py against bb prove, in both
//!   directions), and on bb behaving as its source reads. The emulation
//!   of secp256r1 leaves out the two-point multiplication, where every
//!   assertion compares points that move with the key.
//!   noir/total_ecdsa_prove_check proves inputs from every failing
//!   family above on each curve.
//! - Another backend, or a later bb, could differ: soundness does not
//!   depend on bb's internals, but totality does. On any bb change the
//!   proof, the emulations and the differential run must be redone
//!   (CONTRIBUTING.md, "Bumping bb").
//! - Any further solver/backend disagreement class or gadget assertion
//!   that the probes and the source reading did not find would be a
//!   totality hole these gates cannot see.
//! - ok = false is one bool; the doc comment of ecdsa_k1_verify says
//!   how a caller tells its causes apart with the two public flags.
//!
//! Malleability: a high s (n - s) gives false (the std functions require
//! low s); r + n and s + n give false (out of range); hash + n verifies
//! like hash, since both sides reduce the hash mod n (an ECDSA property,
//! the hash is the caller's input, not part of the signature).
//!
//! Probe matrix, on the typed wrappers before the blind covered every
//! residue, 28 cases per curve (nargo execute, bb prove, bb verify,
//! verdict compared with a Python reference; scripts/ecdsa_differential.py
//! now reruns these classes and the failing families at scale): valid, wrong hash, wrong s, wrong key, high s, r = 0,
//! s = 0, r = n, s = n, all-0xff signature, hash + n, hash 0, all-0xff
//! hash, keys G, -G and 2G, the off-curve keys (0, 1), (0, 2), (5, 0) and
//! a bit-flipped key, (0, 0) and all-0xff keys, class 1, r = s, r + s = n,
//! a result at infinity, a result at G, and u2 = 2: all 56 prove and
//! verify with the reference verdict. noir/total_ecdsa_prove_check adds
//! the multiplication-collision inputs above; the raw std function fails
//! to prove each of them.
//!
//! Cost, measured on programs that call one entry each (ACIR opcodes from
//! nargo info rc.3, bb 6.0.0 circuit size). The programs for the typed
//! entries take u8 entry-point parameters, so their counts include the
//! parameters' 160 entry RANGEs; those for the raw-Field variants take
//! Fields.
//!
//! | entry                              | ACIR opcodes | bb gates |
//! |------------------------------------|--------------|----------|
//! | std secp256k1 black box alone      | 162          | 42892    |
//! | ecdsa_k1_verify                    | 7869         | 62769    |
//! | ecdsa_k1_verify_fields             | 11549        | 69889    |
//! | std secp256r1 black box alone      | 162          | 46000    |
//! | ecdsa_r1_verify                    | 7898         | 65925    |
//! | ecdsa_r1_verify_fields             | 11578        | 73045    |
//!
//! Over the black box, about 700 (k1) and 750 (r1) gates are the gates:
//! 446 for the key check (total::secp) on each curve, the rest for the
//! signature flags; the blinding costs about 19,200 gates on either
//! curve (blind.nr's header). The raw-Field variants add about 7100 gates
//! for the 160 to_u8_or conversions.
//!
//! Hint cost (the honest hint of blind_hint.nr; wall time of nargo
//! execute on a program calling one entry, of which about 1.1 s is
//! start-up): 1.6 s on secp256k1 and 2.1 s on secp256r1 for an input whose
//! first candidate is accepted, which is every honest input; each further
//! candidate costs about 0.2 s (k1) or 0.8 s (r1), the emulation's share.
//! On secp256k1 an adversarial input can make each candidate fail with
//! probability up to about 0.57 (docs/ecdsa-totality.md), about two
//! candidates on average; the cap is 256 candidates.
//!
//! Lint (total-lint), on a program calling both raw-Field variants: exit
//! 0. Its 3,938 reachable Brillig abort sites are all in the blind hint
//! (one copy per curve): 3,924 u128 divisions by the constant 2^64 in
//! bignum.nr's and k1_emul.nr's limb arithmetic, four radix
//! decompositions and ten overflow and bounds checks, which bignum.nr and
//! blind_hint.nr argue never fire; --lib-src whitelists them.
//! --brillig-ops reports 1,515 opcodes there that co-noir's VM cannot run
//! (integer shifts, Or, ConditionalMov and the Poseidon2 black box; these
//! entries cannot run there anyway, below). A program calling the typed
//! entries also reports its own 160 u8 entry-parameter RANGEs, and four
//! library-input-falsifiable RANGEs of core::implied_range on the
//! signature's 128-bit halves (sums of 16 entry bytes, below 2^128 by
//! those bytes' own RANGEs, which the lint does not carry over). Inside
//! the wrappers the ECDSA opcode is classed hint-library (its inputs
//! depend on hinted values), not backend-defined, so the lint's
//! backend-defined listing does not show it; the backend behaviour is
//! covered by the cases above.
//!
//! Raw-Field variants (ecdsa_k1_verify_fields, ecdsa_r1_verify_fields)
//! take every byte as a Field and convert it with
//! total::convert::to_u8_or; a value >= 256 gives false and is clamped to
//! 0 before the typed wrapper runs.
//!
//! co-noir: co-acvm does not solve the ECDSA black boxes, so these
//! entries do not run in co-noir's witness extension (docs/co-noir.md).

use crate::cmp::{eq, lt};
use crate::convert::{from_u128, to_u8_or};
use crate::core::{eq as field_eq, TWO_POW_128};
use crate::ctl::Select;
use crate::encode::u128_from_be_bytes;
use crate::secp::{secp256k1_on_curve, secp256r1_on_curve};
use blind::{blind, Secp256k1, Secp256r1};

/// n as (high, low) u128 limbs, per curve.
global K1_ORDER_HI: u128 = 0xfffffffffffffffffffffffffffffffe;
global K1_ORDER_LO: u128 = 0xbaaedce6af48a03bbfd25e8cd0364141;
global R1_ORDER_HI: u128 = 0xffffffff00000000ffffffffffffffff;
global R1_ORDER_LO: u128 = 0xbce6faada7179e84f3b9cac2fc632551;
/// secp256k1 p - n, high 128-bit limb.
global K1_GAP_HI: u128 = 0x1;
/// secp256k1 p - n, low 128-bit limb.
global K1_GAP_LO: u128 = 0x4551231950b75fc4402da1722fc9baee;
/// secp256r1 p - n, high 128-bit limb.
global R1_GAP_HI: u128 = 0x0;
/// secp256r1 p - n, low 128-bit limb.
global R1_GAP_LO: u128 = 0x4319055358e8617b0c46353d039cdaae;
/// secp256r1 group order n, high 128-bit limb.
global R1_N_HI: Field = 0xffffffff00000000ffffffffffffffff;
/// secp256r1 group order n, low 128-bit limb.
global R1_N_LO: Field = 0xbce6faada7179e84f3b9cac2fc632551;

// Dummies: the std test vectors (noir_stdlib ecdsa_secp256k1.nr and
// ecdsa_secp256r1.nr, test `verify`). Each is a valid low-s signature;
// the tests dummy_k1_verifies / dummy_r1_verifies pin that the black box
// accepts it and that it passes the gates.

global K1_DUMMY_PK_X: [u8; 32] = [
    0xa0, 0x43, 0x4d, 0x9e, 0x47, 0xf3, 0xc8, 0x62, 0x35, 0x47, 0x7c, 0x7b, 0x1a, 0xe6, 0xae, 0x5d,
    0x34, 0x42, 0xd4, 0x9b, 0x19, 0x43, 0xc2, 0xb7, 0x52, 0xa6, 0x8e, 0x2a, 0x47, 0xe2, 0x47, 0xc7,
];
global K1_DUMMY_PK_Y: [u8; 32] = [
    0x89, 0x3a, 0xba, 0x42, 0x54, 0x19, 0xbc, 0x27, 0xa3, 0xb6, 0xc7, 0xe6, 0x93, 0xa2, 0x4c, 0x69,
    0x6f, 0x79, 0x4c, 0x2e, 0xd8, 0x77, 0xa1, 0x59, 0x3c, 0xbe, 0xe5, 0x3b, 0x03, 0x73, 0x68, 0xd7,
];
global K1_DUMMY_SIG: [u8; 64] = [
    0xe5, 0x08, 0x1c, 0x80, 0xab, 0x42, 0x7d, 0xc3, 0x70, 0x34, 0x6f, 0x4a, 0x0e, 0x31, 0xaa, 0x2b,
    0xad, 0x8d, 0x97, 0x98, 0xc3, 0x80, 0x61, 0xdb, 0x9a, 0xe5, 0x5a, 0x4e, 0x8d, 0xf4, 0x54, 0xfd,
    0x28, 0x11, 0x98, 0x94, 0x34, 0x4e, 0x71, 0xb7, 0x87, 0x70, 0xcc, 0x93, 0x1d, 0x61, 0xf4, 0x80,
    0xec, 0xbb, 0x0b, 0x89, 0xd6, 0xeb, 0x69, 0x69, 0x01, 0x61, 0xe4, 0x9a, 0x71, 0x5f, 0xcd, 0x55,
];
global K1_DUMMY_HASH: [u8; 32] = [
    0x3a, 0x73, 0xf4, 0x12, 0x3a, 0x5c, 0xd2, 0x12, 0x1f, 0x21, 0xcd, 0x7e, 0x8d, 0x35, 0x88, 0x35,
    0x47, 0x69, 0x49, 0xd0, 0x35, 0xd9, 0xc2, 0xda, 0x68, 0x06, 0xb4, 0x63, 0x3a, 0xc8, 0xc1, 0xe2,
];

global R1_DUMMY_PK_X: [u8; 32] = [
    85, 15, 71, 16, 3, 243, 223, 151, 195, 223, 80, 106, 199, 151, 246, 114, 31, 177, 161, 251, 123,
    143, 111, 131, 210, 36, 73, 138, 101, 200, 142, 36,
];
global R1_DUMMY_PK_Y: [u8; 32] = [
    19, 96, 147, 215, 1, 46, 80, 154, 115, 113, 92, 189, 11, 0, 163, 204, 15, 244, 181, 192, 27, 63,
    250, 25, 106, 177, 251, 50, 112, 54, 184, 230,
];
global R1_DUMMY_SIG: [u8; 64] = [
    44, 112, 168, 208, 132, 182, 43, 252, 92, 224, 54, 65, 202, 249, 247, 42, 212, 218, 140, 129,
    191, 230, 236, 148, 135, 187, 94, 27, 239, 98, 161, 50, 24, 173, 158, 226, 158, 175, 53, 31,
    220, 80, 241, 82, 12, 66, 94, 155, 144, 138, 7, 39, 139, 67, 176, 236, 123, 135, 39, 120, 193,
    78, 7, 132,
];
global R1_DUMMY_HASH: [u8; 32] = [
    84, 112, 91, 163, 186, 175, 219, 223, 186, 140, 95, 154, 112, 247, 168, 155, 238, 152, 217, 6,
    181, 62, 49, 7, 77, 167, 186, 236, 220, 13, 169, 173,
];

/// The 32-byte big-endian integer at sig[OFF..OFF + 32] as (high, low)
/// u128 limbs. Constraints: two encode::u128_from_be_bytes (an exact sum
/// of bytes, then convert's exact cast: a hinted u128, its 128-bit RANGE
/// and an equality with the sum, hint-satisfiable because the sum of 16
/// bytes is below 2^128). Determined.
fn be_limbs<let OFF: u32>(sig: [u8; 64]) -> (u128, u128) {
    let mut hi = [0; 16];
    let mut lo = [0; 16];
    for i in 0..16 {
        hi[i] = sig[OFF + i];
        lo[i] = sig[OFF + 16 + i];
    }
    (u128_from_be_bytes(hi), u128_from_be_bytes(lo))
}

/// Flag: (hi, lo) < (gap_hi, gap_lo) as 256-bit integers. Native u128
/// compares and equalities through total::cmp (total for every pair of
/// u128 values: a hinted borrow split with RANGEs, and the inversion
/// gadget). Determined.
fn lt_256(hi: u128, lo: u128, gap_hi: u128, gap_lo: u128) -> bool {
    lt(hi, gap_hi) | (eq(hi, gap_hi) & lt(lo, gap_lo))
}

/// Flag: the secp256k1 signature bytes are outside the class where the
/// ACVM solver and bb disagree (module header, class 1), and r is a
/// scalar: p - n <= r < n. r >= n is never a valid signature (the solver
/// and bb both say false); gating it keeps r != 0 mod n for the blind
/// (module header, class 4).
/// Constraints: be_limbs and lt_256 twice (see those); hint-satisfiable
/// for every byte array; determined.
pub fn ecdsa_k1_sig_admissible(sig: [u8; 64]) -> bool {
    let (r_hi, r_lo) = be_limbs::<0>(sig);
    !lt_256(r_hi, r_lo, K1_GAP_HI, K1_GAP_LO) & lt_256(r_hi, r_lo, K1_ORDER_HI, K1_ORDER_LO)
}

/// Flag: the secp256r1 signature bytes are outside disagreement classes
/// 1 and 2 (module header) and r is a scalar (class 4): p - n <= r < n,
/// r != s and r + s != n as integers. r + s == n is decided on limbs: with lo = r_lo + s_lo and
/// hi = r_hi + s_hi (each below 2^129, so the Field sums are exact),
/// r + s == n iff (lo == n_lo and hi == n_hi) or (lo == n_lo + 2^128 and
/// hi + 1 == n_hi), because lo - n_lo lies in (-2^128, 2^129).
///
/// Constraints: be_limbs twice, lt_256, two u128 equalities, Field
/// arithmetic definitions and four core::eq inversion gadgets. All
/// hint-satisfiable for every byte array; determined.
pub fn ecdsa_r1_sig_admissible(sig: [u8; 64]) -> bool {
    let (r_hi, r_lo) = be_limbs::<0>(sig);
    let (s_hi, s_lo) = be_limbs::<32>(sig);
    let r_eq_s = eq(r_hi, s_hi) & eq(r_lo, s_lo);
    let lo = from_u128(r_lo) + from_u128(s_lo);
    let hi = from_u128(r_hi) + from_u128(s_hi);
    let sum_is_n = (field_eq(lo, R1_N_LO) & field_eq(hi, R1_N_HI))
        | (field_eq(lo, R1_N_LO + TWO_POW_128) & field_eq(hi + 1, R1_N_HI));
    !lt_256(r_hi, r_lo, R1_GAP_HI, R1_GAP_LO)
        & lt_256(r_hi, r_lo, R1_ORDER_HI, R1_ORDER_LO)
        & !r_eq_s
        & !sum_is_n
}

/// Byte-wise select: c ? t : f. ctl::Select on u8, which lowers to
/// arithmetic with no constraint. Total.
fn select_bytes<let N: u32>(c: bool, t: [u8; N], f: [u8; N]) -> [u8; N] {
    let mut out = [0; N];
    for i in 0..N {
        out[i] = u8::select(c, t[i], f[i]);
    }
    out
}

/// Every Field converted with total::convert::to_u8_or: (bytes, ok) with
/// ok = every value is below 256 and each failing value clamped to 0.
/// Constraints: N to_u8_or (core::limbs set, a split, is_zero gadgets
/// and an exact cast each; hint-satisfiable for every Field). Determined.
fn bytes_or<let N: u32>(x: [Field; N]) -> ([u8; N], bool) {
    let mut out = [0; N];
    let mut ok = true;
    for i in 0..N {
        let (b, k) = to_u8_or(x[i]);
        out[i] = b;
        ok = ok & k;
    }
    (out, ok)
}

/// ECDSA secp256k1 verification, total for every byte input. pk_x and
/// pk_y are the big-endian affine coordinates, sig is r || s big-endian,
/// hash is the 32-byte message hash (reduced mod n by the verifier).
/// Returns true exactly when secp256k1_on_curve(pk_x, pk_y) holds,
/// ecdsa_k1_sig_admissible(sig) holds and the std black box accepts (low
/// s required).
///
/// What false means: exactly one of these holds.
/// 1. secp::secp256k1_on_curve(pk_x, pk_y) is false: the key is not a
///    curve point with coordinates below p (the signature was not looked
///    at).
/// 2. The key is valid and ecdsa_k1_sig_admissible(sig) is false: r is
///    in the excluded class r < p - n (module header). A signature made by
///    an honest signer lands there with probability about 2^-128.
/// 3. Both flags hold and the signature does not verify: r or s is zero
///    or >= n, s is high (s > n/2), or the verification equation fails.
/// Both flags are public, determined and cheap next to the black box, so
/// a caller that must tell the cases apart calls them on the same bytes.
///
/// How: ok = secp256k1_on_curve(pk_x, pk_y) & ecdsa_k1_sig_admissible(sig);
/// every input byte is selected between the real input (ok) and the std
/// test vector (not ok); the selected key and hash are blinded
/// (blind.nr: Q' = Q + b' G, z' = z - r b' mod n); the black box runs on
/// (Q', selected signature, z'); the result is ANDed with ok.
///
/// Why no input can make the circuit unprovable: the solver returns a
/// value for every byte input, and bb's gadget agrees with it except on
/// disagreement classes 1 and 3 (module header), which ok excludes; the
/// dummy is outside both (tests dummy_k1_verifies,
/// vector_keys_on_curve), and blinding keeps the key on the curve and
/// (r, s) unchanged. Of bb's multiplication assertions, the honest hint
/// picks a blind none of them meets (module header; the argument and its
/// assumptions are in k1_emul.nr).
///
/// Constraints: secp256k1_on_curve and ecdsa_k1_sig_admissible (each
/// hint-satisfiable for every input and determined), 160 byte selects
/// (definitions), blind.nr's constraints C1-C5 (satisfiable by the honest
/// hint for every input), one ECDSA black-box opcode (satisfiable as
/// argued), two ANDs. Determined: ok is determined, the selected bytes
/// are functions of it, the blinded call's verdict equals the verdict on
/// the selected inputs for every accepted hint (blind.nr), and bb
/// constrains the black-box output to the in-circuit verification
/// result.
pub fn ecdsa_k1_verify(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> bool {
    let ok = secp256k1_on_curve(pk_x, pk_y) & ecdsa_k1_sig_admissible(sig);
    let sg = select_bytes(ok, sig, K1_DUMMY_SIG);
    let (bx, by, bz) = blind(
        Secp256k1 {},
        select_bytes(ok, pk_x, K1_DUMMY_PK_X),
        select_bytes(ok, pk_y, K1_DUMMY_PK_Y),
        sg,
        select_bytes(ok, hash, K1_DUMMY_HASH),
    );
    ok & std::ecdsa_secp256k1::verify_signature(bx, by, sg, bz)
}

/// ECDSA secp256r1 verification, total for every byte input. Same layout
/// and pattern as ecdsa_k1_verify, with secp256r1_on_curve(pk_x, pk_y)
/// and ecdsa_r1_sig_admissible(sig) as the gate (classes 1 and 2 of the
/// module header, and key validation in Noir rather than bb's) and the
/// std r1 test vector as the dummy (test dummy_r1_verifies).
///
/// What false means: exactly one of these holds.
/// 1. secp::secp256r1_on_curve(pk_x, pk_y) is false: the key is not a
///    P-256 point with coordinates below p.
/// 2. The key is valid and ecdsa_r1_sig_admissible(sig) is false: r < p - n,
///    r == s or r + s == n (about 2^-130 for an honest signer).
/// 3. Both flags hold and the signature does not verify (r or s zero or
///    >= n, high s, or the equation fails).
///
/// Constraints: secp256r1_on_curve and ecdsa_r1_sig_admissible (each
/// hint-satisfiable for every input and determined), 160 byte selects,
/// blind.nr's constraints C1-C5, one ECDSA black-box opcode, two ANDs.
/// Determined, as for k1. The honest hint takes the first candidate blind
/// with x(B) != x(Q); secp256r1's multiplication has no assertion that
/// depends on R (module header).
pub fn ecdsa_r1_verify(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> bool {
    let ok = secp256r1_on_curve(pk_x, pk_y) & ecdsa_r1_sig_admissible(sig);
    let sg = select_bytes(ok, sig, R1_DUMMY_SIG);
    let (bx, by, bz) = blind(
        Secp256r1 {},
        select_bytes(ok, pk_x, R1_DUMMY_PK_X),
        select_bytes(ok, pk_y, R1_DUMMY_PK_Y),
        sg,
        select_bytes(ok, hash, R1_DUMMY_HASH),
    );
    ok & std::ecdsa_secp256r1::verify_signature(bx, by, sg, bz)
}

/// ecdsa_k1_verify for inputs given as one Field per byte, the form
/// to use at a trust boundary. ok additionally requires every value to
/// be below 256.
///
/// Constraints: 160 to_u8_or conversions (hint-satisfiable for every
/// Field), then ecdsa_k1_verify on the clamped bytes, which is total
/// for every byte array. Determined.
pub fn ecdsa_k1_verify_fields(
    pk_x: [Field; 32],
    pk_y: [Field; 32],
    sig: [Field; 64],
    hash: [Field; 32],
) -> bool {
    let (x, ok_x) = bytes_or(pk_x);
    let (y, ok_y) = bytes_or(pk_y);
    let (s, ok_s) = bytes_or(sig);
    let (h, ok_h) = bytes_or(hash);
    ok_x & ok_y & ok_s & ok_h & ecdsa_k1_verify(x, y, s, h)
}

/// ecdsa_r1_verify for inputs given as one Field per byte. Same
/// constraints and argument as ecdsa_k1_verify_fields.
pub fn ecdsa_r1_verify_fields(
    pk_x: [Field; 32],
    pk_y: [Field; 32],
    sig: [Field; 64],
    hash: [Field; 32],
) -> bool {
    let (x, ok_x) = bytes_or(pk_x);
    let (y, ok_y) = bytes_or(pk_y);
    let (s, ok_s) = bytes_or(sig);
    let (h, ok_h) = bytes_or(hash);
    ok_x & ok_y & ok_s & ok_h & ecdsa_r1_verify(x, y, s, h)
}

/// Diagnostic, unconstrained: whether bb 6.0.0 has no proof for the raw
/// std::ecdsa_secp256k1::verify_signature call on these inputs because
/// its multiplication fails an assertion (ecdsa/k1_emul.nr), for a key on
/// the curve. Not used by the wrappers, which blind first; it exposes the
/// hint's emulation so that scripts/ecdsa_differential.py can compare it
/// with bb.
pub unconstrained fn ecdsa_k1_raw_unprovable(
    pk_x: [u8; 32],
    pk_y: [u8; 32],
    sig: [u8; 64],
    hash: [u8; 32],
) -> bool {
    blind_hint::raw_bad::<Secp256k1>(pk_x, pk_y, sig, hash)
}

/// The same for std::ecdsa_secp256r1::verify_signature, restricted to the
/// parts ecdsa/r1_emul.nr follows (the fixed-base chain, the offset
/// subtraction and the final addition; not the two-point multiplication).
pub unconstrained fn ecdsa_r1_raw_unprovable(
    pk_x: [u8; 32],
    pk_y: [u8; 32],
    sig: [u8; 64],
    hash: [u8; 32],
) -> bool {
    blind_hint::raw_bad::<Secp256r1>(pk_x, pk_y, sig, hash)
}

mod bignum;
mod blind;
mod blind_hint;
mod blind_tests;
mod k1_emul;
mod r1_emul;
mod table_k1;
mod table_r1;
mod vectors;

mod tests {
    use crate::secp::{secp256k1_on_curve, secp256r1_on_curve};
    use crate::test_support::wit as w;
    use super::{
        ecdsa_k1_sig_admissible, ecdsa_k1_verify, ecdsa_k1_verify_fields, ecdsa_r1_sig_admissible,
        ecdsa_r1_verify, ecdsa_r1_verify_fields, K1_DUMMY_HASH, K1_DUMMY_PK_X, K1_DUMMY_PK_Y,
        K1_DUMMY_SIG, R1_DUMMY_HASH, R1_DUMMY_PK_X, R1_DUMMY_PK_Y, R1_DUMMY_SIG,
    };
    use super::vectors::{
        K1_GAP, K1_GAP_MINUS_1, K1_N, K1_PK_IS_MINUS_G_HASH, K1_PK_IS_MINUS_G_PK_X,
        K1_PK_IS_MINUS_G_PK_Y, K1_PK_IS_MINUS_G_SIG, K1_PK_X_PLUS_P_PK_X, K1_PK_X_PLUS_P_PK_Y,
        K1_RX_ABOVE_N_HASH, K1_RX_ABOVE_N_PK_X, K1_RX_ABOVE_N_PK_Y, K1_RX_ABOVE_N_SIG,
        K1_S_HIGH_SIG, K1_U1_MINUS_ONE_HASH, K1_U1_MINUS_ONE_PK_X, K1_U1_MINUS_ONE_PK_Y,
        K1_U1_MINUS_ONE_SIG, K1_U1_ONE_HASH, K1_U1_ONE_PK_X, K1_U1_ONE_PK_Y, K1_U1_ONE_SIG,
        K1_U2_ONE_HASH, K1_U2_ONE_PK_X, K1_U2_ONE_PK_Y, K1_U2_ONE_SIG, K1_Z_PLUS_N_HASH,
        K1_Z_PLUS_N_PK_X, K1_Z_PLUS_N_PK_Y, K1_Z_PLUS_N_SIG, R1_GAP, R1_GAP_MINUS_1, R1_N,
        R1_PK_IS_MINUS_G_HASH, R1_PK_IS_MINUS_G_PK_X, R1_PK_IS_MINUS_G_PK_Y, R1_PK_IS_MINUS_G_SIG,
        R1_PK_X_PLUS_P_PK_X, R1_PK_X_PLUS_P_PK_Y, R1_RX_ABOVE_N_HASH, R1_RX_ABOVE_N_PK_X,
        R1_RX_ABOVE_N_PK_Y, R1_RX_ABOVE_N_SIG, R1_S_HIGH_SIG, R1_SUM_N_CARRY, R1_SUM_N_NOCARRY,
        R1_SUM_N_PLUS_1, R1_U1_MINUS_ONE_HASH, R1_U1_MINUS_ONE_PK_X, R1_U1_MINUS_ONE_PK_Y,
        R1_U1_MINUS_ONE_SIG, R1_U1_ONE_HASH, R1_U1_ONE_PK_X, R1_U1_ONE_PK_Y, R1_U1_ONE_SIG,
        R1_U2_MINUS_ONE_HASH, R1_U2_MINUS_ONE_PK_X, R1_U2_MINUS_ONE_PK_Y, R1_U2_MINUS_ONE_SIG,
        R1_U2_ONE_HASH, R1_U2_ONE_PK_X, R1_U2_ONE_PK_Y, R1_U2_ONE_SIG, R1_Z_PLUS_N_HASH,
        R1_Z_PLUS_N_PK_X, R1_Z_PLUS_N_PK_Y, R1_Z_PLUS_N_SIG,
    };

    fn k1(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> bool {
        ecdsa_k1_verify(w(pk_x), w(pk_y), w(sig), w(hash))
    }

    fn r1(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> bool {
        ecdsa_r1_verify(w(pk_x), w(pk_y), w(sig), w(hash))
    }

    /// The raw std black boxes on witnesses: the solver's answer.
    fn k1_raw(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> bool {
        std::ecdsa_secp256k1::verify_signature(w(pk_x), w(pk_y), w(sig), w(hash))
    }

    fn r1_raw(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> bool {
        std::ecdsa_secp256r1::verify_signature(w(pk_x), w(pk_y), w(sig), w(hash))
    }

    fn with_r(sig: [u8; 64], r: [u8; 32]) -> [u8; 64] {
        let mut out = sig;
        for i in 0..32 {
            out[i] = r[i];
        }
        out
    }

    fn with_s(sig: [u8; 64], s: [u8; 32]) -> [u8; 64] {
        let mut out = sig;
        for i in 0..32 {
            out[32 + i] = s[i];
        }
        out
    }

    fn fields<let N: u32>(b: [u8; N]) -> [Field; N] {
        let mut out = [0; N];
        for i in 0..N {
            out[i] = b[i] as Field;
        }
        out
    }

    // --- dummies and known-answer vectors ---

    #[test]
    fn dummy_k1_verifies() {
        assert(std::ecdsa_secp256k1::verify_signature(
            K1_DUMMY_PK_X,
            K1_DUMMY_PK_Y,
            K1_DUMMY_SIG,
            K1_DUMMY_HASH,
        ));
        assert(ecdsa_k1_sig_admissible(K1_DUMMY_SIG));
        assert(k1(K1_DUMMY_PK_X, K1_DUMMY_PK_Y, K1_DUMMY_SIG, K1_DUMMY_HASH));
    }

    #[test]
    fn dummy_r1_verifies() {
        assert(std::ecdsa_secp256r1::verify_signature(
            R1_DUMMY_PK_X,
            R1_DUMMY_PK_Y,
            R1_DUMMY_SIG,
            R1_DUMMY_HASH,
        ));
        assert(ecdsa_r1_sig_admissible(R1_DUMMY_SIG));
        assert(r1(R1_DUMMY_PK_X, R1_DUMMY_PK_Y, R1_DUMMY_SIG, R1_DUMMY_HASH));
    }

    #[test]
    fn generated_valid_signatures_verify() {
        // key -G (secret n - 1)
        assert(k1(
            K1_PK_IS_MINUS_G_PK_X,
            K1_PK_IS_MINUS_G_PK_Y,
            K1_PK_IS_MINUS_G_SIG,
            K1_PK_IS_MINUS_G_HASH,
        ));
        assert(r1(
            R1_PK_IS_MINUS_G_PK_X,
            R1_PK_IS_MINUS_G_PK_Y,
            R1_PK_IS_MINUS_G_SIG,
            R1_PK_IS_MINUS_G_HASH,
        ));
        // secp256k1 with r == s (u2 = 1): valid, and provable on bb. The raw
        // black box says true on both toolchains (k1 uses a real
        // endomorphism, so this is not a disagreement class there).
        assert(
            k1_raw(
                K1_U2_ONE_PK_X,
                K1_U2_ONE_PK_Y,
                K1_U2_ONE_SIG,
                K1_U2_ONE_HASH,
            ),
        );
        assert(ecdsa_k1_sig_admissible(K1_U2_ONE_SIG));
        assert(
            k1(
                K1_U2_ONE_PK_X,
                K1_U2_ONE_PK_Y,
                K1_U2_ONE_SIG,
                K1_U2_ONE_HASH,
            ),
        );
    }

    // u1 = z/s = +1 and -1 (s = 1, hash 1 or n - 1): valid and admissible
    // on both curves, and the raw black box agrees, so u1 in {1, -1} is
    // not a disagreement class (module header).
    #[test]
    fn unit_u1_verifies() {
        assert(
            k1_raw(
                K1_U1_ONE_PK_X,
                K1_U1_ONE_PK_Y,
                K1_U1_ONE_SIG,
                K1_U1_ONE_HASH,
            ),
        );
        assert(
            k1(
                K1_U1_ONE_PK_X,
                K1_U1_ONE_PK_Y,
                K1_U1_ONE_SIG,
                K1_U1_ONE_HASH,
            ),
        );
        assert(k1_raw(
            K1_U1_MINUS_ONE_PK_X,
            K1_U1_MINUS_ONE_PK_Y,
            K1_U1_MINUS_ONE_SIG,
            K1_U1_MINUS_ONE_HASH,
        ));
        assert(k1(
            K1_U1_MINUS_ONE_PK_X,
            K1_U1_MINUS_ONE_PK_Y,
            K1_U1_MINUS_ONE_SIG,
            K1_U1_MINUS_ONE_HASH,
        ));
        assert(
            r1_raw(
                R1_U1_ONE_PK_X,
                R1_U1_ONE_PK_Y,
                R1_U1_ONE_SIG,
                R1_U1_ONE_HASH,
            ),
        );
        assert(
            r1(
                R1_U1_ONE_PK_X,
                R1_U1_ONE_PK_Y,
                R1_U1_ONE_SIG,
                R1_U1_ONE_HASH,
            ),
        );
        assert(r1_raw(
            R1_U1_MINUS_ONE_PK_X,
            R1_U1_MINUS_ONE_PK_Y,
            R1_U1_MINUS_ONE_SIG,
            R1_U1_MINUS_ONE_HASH,
        ));
        assert(r1(
            R1_U1_MINUS_ONE_PK_X,
            R1_U1_MINUS_ONE_PK_Y,
            R1_U1_MINUS_ONE_SIG,
            R1_U1_MINUS_ONE_HASH,
        ));
        // a wrong hash still fails: u1 = 1 is not a free pass
        assert(
            !k1(
                K1_U1_ONE_PK_X,
                K1_U1_ONE_PK_Y,
                K1_U1_ONE_SIG,
                K1_U1_MINUS_ONE_HASH,
            ),
        );
        assert(
            !r1(
                R1_U1_ONE_PK_X,
                R1_U1_ONE_PK_Y,
                R1_U1_ONE_SIG,
                R1_U1_MINUS_ONE_HASH,
            ),
        );
    }

    // --- wrong signatures ---

    #[test]
    fn wrong_hash_or_signature_rejected() {
        let mut h = K1_DUMMY_HASH;
        h[0] = 0;
        assert(!k1(K1_DUMMY_PK_X, K1_DUMMY_PK_Y, K1_DUMMY_SIG, h));
        let mut s = K1_DUMMY_SIG;
        s[40] ^= 1;
        assert(!k1(K1_DUMMY_PK_X, K1_DUMMY_PK_Y, s, K1_DUMMY_HASH));
        let mut h2 = R1_DUMMY_HASH;
        h2[0] = 0;
        assert(!r1(R1_DUMMY_PK_X, R1_DUMMY_PK_Y, R1_DUMMY_SIG, h2));
        let mut s2 = R1_DUMMY_SIG;
        s2[40] ^= 1;
        assert(!r1(R1_DUMMY_PK_X, R1_DUMMY_PK_Y, s2, R1_DUMMY_HASH));
        // a curve's valid vector under the other curve
        assert(!k1(R1_DUMMY_PK_X, R1_DUMMY_PK_Y, R1_DUMMY_SIG, R1_DUMMY_HASH));
        assert(!r1(K1_DUMMY_PK_X, K1_DUMMY_PK_Y, K1_DUMMY_SIG, K1_DUMMY_HASH));
    }

    // --- malformed keys: rejected by the key check before the black box ---

    #[test]
    fn malformed_keys_rejected() {
        assert(!secp256k1_on_curve(K1_PK_X_PLUS_P_PK_X, K1_PK_X_PLUS_P_PK_Y));
        assert(!secp256r1_on_curve(R1_PK_X_PLUS_P_PK_X, R1_PK_X_PLUS_P_PK_Y));
        let mut y = K1_DUMMY_PK_Y;
        y[31] ^= 1;
        assert(!k1(K1_DUMMY_PK_X, y, K1_DUMMY_SIG, K1_DUMMY_HASH));
        assert(!k1([0; 32], [0; 32], K1_DUMMY_SIG, K1_DUMMY_HASH));
        assert(!k1([0xff; 32], [0xff; 32], K1_DUMMY_SIG, K1_DUMMY_HASH));
        assert(
            !k1(
                K1_PK_X_PLUS_P_PK_X,
                K1_PK_X_PLUS_P_PK_Y,
                K1_DUMMY_SIG,
                K1_DUMMY_HASH,
            ),
        );
        let mut y2 = R1_DUMMY_PK_Y;
        y2[31] ^= 1;
        assert(!r1(R1_DUMMY_PK_X, y2, R1_DUMMY_SIG, R1_DUMMY_HASH));
        assert(!r1([0; 32], [0; 32], R1_DUMMY_SIG, R1_DUMMY_HASH));
        assert(!r1([0xff; 32], [0xff; 32], R1_DUMMY_SIG, R1_DUMMY_HASH));
        assert(
            !r1(
                R1_PK_X_PLUS_P_PK_X,
                R1_PK_X_PLUS_P_PK_Y,
                R1_DUMMY_SIG,
                R1_DUMMY_HASH,
            ),
        );
    }

    fn small(v: u8) -> [u8; 32] {
        let mut out = [0; 32];
        out[31] = v;
        out
    }

    // Off-curve keys of order 3, 3 and 2 on their own curves y^2 = x^3 + b'
    // (module header, class 3): the raw secp256k1 black box executes with
    // false on them but bb cannot prove that witness. The wrappers replace
    // them by the dummy, so they give false and prove on both curves.
    #[test]
    fn small_order_off_curve_keys_rejected() {
        let keys = [(small(0), small(1)), (small(0), small(2)), (small(5), small(0))];
        for i in 0..3 {
            let (x, y) = keys[i];
            assert(!secp256k1_on_curve(x, y));
            assert(!secp256r1_on_curve(x, y));
            assert(!k1(x, y, K1_DUMMY_SIG, K1_DUMMY_HASH));
            assert(!r1(x, y, R1_DUMMY_SIG, R1_DUMMY_HASH));
            assert(
                !ecdsa_k1_verify_fields(
                    fields(x),
                    fields(y),
                    fields(K1_DUMMY_SIG),
                    fields(K1_DUMMY_HASH),
                ),
            );
            assert(
                !ecdsa_r1_verify_fields(
                    fields(x),
                    fields(y),
                    fields(R1_DUMMY_SIG),
                    fields(R1_DUMMY_HASH),
                ),
            );
        }
    }

    // Every key in the vectors and both dummies are on their curve.
    #[test]
    fn vector_keys_on_curve() {
        assert(secp256k1_on_curve(K1_DUMMY_PK_X, K1_DUMMY_PK_Y));
        assert(secp256k1_on_curve(K1_RX_ABOVE_N_PK_X, K1_RX_ABOVE_N_PK_Y));
        assert(secp256k1_on_curve(K1_U2_ONE_PK_X, K1_U2_ONE_PK_Y));
        assert(secp256k1_on_curve(K1_Z_PLUS_N_PK_X, K1_Z_PLUS_N_PK_Y));
        assert(secp256k1_on_curve(K1_PK_IS_MINUS_G_PK_X, K1_PK_IS_MINUS_G_PK_Y));
        assert(secp256k1_on_curve(K1_U1_ONE_PK_X, K1_U1_ONE_PK_Y));
        assert(secp256k1_on_curve(K1_U1_MINUS_ONE_PK_X, K1_U1_MINUS_ONE_PK_Y));
        assert(secp256r1_on_curve(R1_DUMMY_PK_X, R1_DUMMY_PK_Y));
        assert(secp256r1_on_curve(R1_RX_ABOVE_N_PK_X, R1_RX_ABOVE_N_PK_Y));
        assert(secp256r1_on_curve(R1_U2_ONE_PK_X, R1_U2_ONE_PK_Y));
        assert(secp256r1_on_curve(R1_U2_MINUS_ONE_PK_X, R1_U2_MINUS_ONE_PK_Y));
        assert(secp256r1_on_curve(R1_Z_PLUS_N_PK_X, R1_Z_PLUS_N_PK_Y));
        assert(secp256r1_on_curve(R1_PK_IS_MINUS_G_PK_X, R1_PK_IS_MINUS_G_PK_Y));
        assert(secp256r1_on_curve(R1_U1_ONE_PK_X, R1_U1_ONE_PK_Y));
        assert(secp256r1_on_curve(R1_U1_MINUS_ONE_PK_X, R1_U1_MINUS_ONE_PK_Y));
    }

    // The three causes of false, told apart with the two public flags.
    #[test]
    fn false_causes_distinguishable() {
        // invalid key: key flag false, signature flag true
        let mut y = K1_DUMMY_PK_Y;
        y[31] ^= 1;
        assert(!k1(K1_DUMMY_PK_X, y, K1_DUMMY_SIG, K1_DUMMY_HASH));
        assert(!secp256k1_on_curve(K1_DUMMY_PK_X, y));
        assert(ecdsa_k1_sig_admissible(K1_DUMMY_SIG));
        // excluded signature class: key flag true, signature flag false
        assert(
            !k1(
                K1_RX_ABOVE_N_PK_X,
                K1_RX_ABOVE_N_PK_Y,
                K1_RX_ABOVE_N_SIG,
                K1_RX_ABOVE_N_HASH,
            ),
        );
        assert(secp256k1_on_curve(K1_RX_ABOVE_N_PK_X, K1_RX_ABOVE_N_PK_Y));
        assert(!ecdsa_k1_sig_admissible(K1_RX_ABOVE_N_SIG));
        // signature does not verify: both flags true
        let mut h = R1_DUMMY_HASH;
        h[0] = 0;
        assert(!r1(R1_DUMMY_PK_X, R1_DUMMY_PK_Y, R1_DUMMY_SIG, h));
        assert(secp256r1_on_curve(R1_DUMMY_PK_X, R1_DUMMY_PK_Y));
        assert(ecdsa_r1_sig_admissible(R1_DUMMY_SIG));
    }

    // --- zero and out-of-range scalars ---

    #[test]
    fn zero_and_out_of_range_scalars_rejected() {
        assert(!k1(K1_DUMMY_PK_X, K1_DUMMY_PK_Y, [0; 64], K1_DUMMY_HASH));
        assert(!k1(K1_DUMMY_PK_X, K1_DUMMY_PK_Y, [0xff; 64], K1_DUMMY_HASH));
        assert(
            !k1(
                K1_DUMMY_PK_X,
                K1_DUMMY_PK_Y,
                with_r(K1_DUMMY_SIG, K1_N),
                K1_DUMMY_HASH,
            ),
        );
        assert(
            !k1(
                K1_DUMMY_PK_X,
                K1_DUMMY_PK_Y,
                with_s(K1_DUMMY_SIG, K1_N),
                K1_DUMMY_HASH,
            ),
        );
        assert(
            !k1(
                K1_DUMMY_PK_X,
                K1_DUMMY_PK_Y,
                with_s(K1_DUMMY_SIG, [0; 32]),
                K1_DUMMY_HASH,
            ),
        );
        assert(!r1(R1_DUMMY_PK_X, R1_DUMMY_PK_Y, [0; 64], R1_DUMMY_HASH));
        assert(!r1(R1_DUMMY_PK_X, R1_DUMMY_PK_Y, [0xff; 64], R1_DUMMY_HASH));
        assert(
            !r1(
                R1_DUMMY_PK_X,
                R1_DUMMY_PK_Y,
                with_r(R1_DUMMY_SIG, R1_N),
                R1_DUMMY_HASH,
            ),
        );
        assert(
            !r1(
                R1_DUMMY_PK_X,
                R1_DUMMY_PK_Y,
                with_s(R1_DUMMY_SIG, R1_N),
                R1_DUMMY_HASH,
            ),
        );
        assert(
            !r1(
                R1_DUMMY_PK_X,
                R1_DUMMY_PK_Y,
                with_r(R1_DUMMY_SIG, [0; 32]),
                R1_DUMMY_HASH,
            ),
        );
    }

    // --- malleated encodings ---

    #[test]
    fn malleated_encodings() {
        // high s: (r, n - s) is textbook-valid but rejected (low s rule)
        assert(!k1(K1_DUMMY_PK_X, K1_DUMMY_PK_Y, K1_S_HIGH_SIG, K1_DUMMY_HASH));
        assert(!r1(R1_DUMMY_PK_X, R1_DUMMY_PK_Y, R1_S_HIGH_SIG, R1_DUMMY_HASH));
        // hash + n verifies like hash: both sides reduce the hash mod n
        assert(
            k1(
                K1_Z_PLUS_N_PK_X,
                K1_Z_PLUS_N_PK_Y,
                K1_Z_PLUS_N_SIG,
                K1_Z_PLUS_N_HASH,
            ),
        );
        assert(
            r1(
                R1_Z_PLUS_N_PK_X,
                R1_Z_PLUS_N_PK_Y,
                R1_Z_PLUS_N_SIG,
                R1_Z_PLUS_N_HASH,
            ),
        );
    }

    // --- the two solver/backend disagreement classes ---

    // R.x = r + n with r < p - n (class 1). Textbook-valid. The test pins
    // the wrapper's verdict, which is false on every toolchain: the gate
    // rejects the class before the black box runs. It does not assert the
    // raw black box, whose answer depends on the ACVM that solves it: the
    // nargo 1.0.0-rc.3 solver says false (and bb cannot prove that
    // witness); the nargo 1.0.0 solver reduces R.x mod n like bb (noir
    // commit 328684c, #14109), says true, and bb 6.0.0 proves it.
    #[test]
    fn rx_above_n_gated() {
        assert(!ecdsa_k1_sig_admissible(K1_RX_ABOVE_N_SIG));
        assert(
            !k1(
                K1_RX_ABOVE_N_PK_X,
                K1_RX_ABOVE_N_PK_Y,
                K1_RX_ABOVE_N_SIG,
                K1_RX_ABOVE_N_HASH,
            ),
        );
        assert(!ecdsa_r1_sig_admissible(R1_RX_ABOVE_N_SIG));
        assert(
            !r1(
                R1_RX_ABOVE_N_PK_X,
                R1_RX_ABOVE_N_PK_Y,
                R1_RX_ABOVE_N_SIG,
                R1_RX_ABOVE_N_HASH,
            ),
        );
    }

    // secp256r1, u2 = r/s in {1, -1} (class 2). Textbook-valid and the
    // solver says true on both toolchains; bb reports false and cannot
    // prove the solver's witness. The raw assertions hold on both.
    #[test]
    fn r1_unit_u2_gated() {
        assert(
            r1_raw(
                R1_U2_ONE_PK_X,
                R1_U2_ONE_PK_Y,
                R1_U2_ONE_SIG,
                R1_U2_ONE_HASH,
            ),
        );
        assert(!ecdsa_r1_sig_admissible(R1_U2_ONE_SIG));
        assert(
            !r1(
                R1_U2_ONE_PK_X,
                R1_U2_ONE_PK_Y,
                R1_U2_ONE_SIG,
                R1_U2_ONE_HASH,
            ),
        );
        assert(r1_raw(
            R1_U2_MINUS_ONE_PK_X,
            R1_U2_MINUS_ONE_PK_Y,
            R1_U2_MINUS_ONE_SIG,
            R1_U2_MINUS_ONE_HASH,
        ));
        assert(!ecdsa_r1_sig_admissible(R1_U2_MINUS_ONE_SIG));
        assert(
            !r1(
                R1_U2_MINUS_ONE_PK_X,
                R1_U2_MINUS_ONE_PK_Y,
                R1_U2_MINUS_ONE_SIG,
                R1_U2_MINUS_ONE_HASH,
            ),
        );
    }

    #[test]
    fn gate_boundaries() {
        // r = p - n passes the gate, r = p - n - 1 does not
        assert(ecdsa_k1_sig_admissible(with_r(K1_DUMMY_SIG, K1_GAP)));
        assert(!ecdsa_k1_sig_admissible(with_r(K1_DUMMY_SIG, K1_GAP_MINUS_1)));
        assert(ecdsa_r1_sig_admissible(with_r(R1_DUMMY_SIG, R1_GAP)));
        assert(!ecdsa_r1_sig_admissible(with_r(R1_DUMMY_SIG, R1_GAP_MINUS_1)));
        // r >= n is outside the gate (class 4)
        assert(!ecdsa_k1_sig_admissible(with_r(K1_DUMMY_SIG, K1_N)));
        assert(!ecdsa_k1_sig_admissible(with_r(K1_DUMMY_SIG, [0xff; 32])));
        assert(!ecdsa_r1_sig_admissible(with_r(R1_DUMMY_SIG, R1_N)));
        assert(!ecdsa_r1_sig_admissible(with_r(R1_DUMMY_SIG, [0xff; 32])));
        assert(!ecdsa_k1_sig_admissible([0; 64]));
        assert(!ecdsa_k1_sig_admissible([0xff; 64]));
        // r + s == n, both limb-carry branches; and one off
        assert(!ecdsa_r1_sig_admissible(R1_SUM_N_NOCARRY));
        assert(!ecdsa_r1_sig_admissible(R1_SUM_N_CARRY));
        assert(ecdsa_r1_sig_admissible(R1_SUM_N_PLUS_1));
        // r == s with r large
        assert(
            !ecdsa_r1_sig_admissible(with_s(
                R1_DUMMY_SIG,
                [
                    R1_DUMMY_SIG[0],
                    R1_DUMMY_SIG[1],
                    R1_DUMMY_SIG[2],
                    R1_DUMMY_SIG[3],
                    R1_DUMMY_SIG[4],
                    R1_DUMMY_SIG[5],
                    R1_DUMMY_SIG[6],
                    R1_DUMMY_SIG[7],
                    R1_DUMMY_SIG[8],
                    R1_DUMMY_SIG[9],
                    R1_DUMMY_SIG[10],
                    R1_DUMMY_SIG[11],
                    R1_DUMMY_SIG[12],
                    R1_DUMMY_SIG[13],
                    R1_DUMMY_SIG[14],
                    R1_DUMMY_SIG[15],
                    R1_DUMMY_SIG[16],
                    R1_DUMMY_SIG[17],
                    R1_DUMMY_SIG[18],
                    R1_DUMMY_SIG[19],
                    R1_DUMMY_SIG[20],
                    R1_DUMMY_SIG[21],
                    R1_DUMMY_SIG[22],
                    R1_DUMMY_SIG[23],
                    R1_DUMMY_SIG[24],
                    R1_DUMMY_SIG[25],
                    R1_DUMMY_SIG[26],
                    R1_DUMMY_SIG[27],
                    R1_DUMMY_SIG[28],
                    R1_DUMMY_SIG[29],
                    R1_DUMMY_SIG[30],
                    R1_DUMMY_SIG[31],
                ],
            )),
        );
    }

    // --- raw-Field variants ---

    #[test]
    fn fields_variants() {
        let (x, y, s, h) = (
            fields(K1_DUMMY_PK_X), fields(K1_DUMMY_PK_Y), fields(K1_DUMMY_SIG),
            fields(K1_DUMMY_HASH),
        );
        assert(ecdsa_k1_verify_fields(x, y, s, h));
        let (x2, y2, s2, h2) = (
            fields(R1_DUMMY_PK_X), fields(R1_DUMMY_PK_Y), fields(R1_DUMMY_SIG),
            fields(R1_DUMMY_HASH),
        );
        assert(ecdsa_r1_verify_fields(x2, y2, s2, h2));
        // a byte value of 256 that would wrap to 0, and the Field p - 1
        let mut bad = s;
        bad[63] = 256 + bad[63];
        assert(!ecdsa_k1_verify_fields(x, y, bad, h));
        let mut bad_x = x2;
        bad_x[0] = 0 - 1;
        assert(!ecdsa_r1_verify_fields(bad_x, y2, s2, h2));
        let mut bad_h = h;
        bad_h[5] = 0x100;
        assert(!ecdsa_k1_verify_fields(x, y, s, bad_h));
        // boundary 255 is a byte
        let mut ok_y = y;
        ok_y[0] = 255;
        assert(!ecdsa_k1_verify_fields(x, ok_y, s, h));
    }
}
