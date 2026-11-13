//! Flagged curve-membership checks for secp256k1 and secp256r1 public
//! keys given as 32-byte big-endian affine coordinates:
//! secp256k1_on_curve(x, y) is true exactly when x < p, y < p and
//! y^2 == x^3 + 7 (mod p), p the secp256k1 base-field modulus;
//! secp256r1_on_curve(x, y) the same for y^2 == x^3 - 3x + b (mod p) over
//! the P-256 modulus. Total for every byte input; the flag is determined.
//!
//! Neither base field is the circuit Field (both moduli are above 2^255,
//! the circuit modulus r is about 2^253.6), so the arithmetic is done on
//! integers held as four 64-bit limbs, least significant first.
//!
//! Method. After the coordinate range flag (both coordinates below p;
//! out-of-range coordinates are replaced by 0 so every later value has
//! its honest bounds), two hinted reductions:
//! 1. x*x == q1*p + t, giving t = x^2 mod p;
//! 2. y*y - t*x + c*x - b + 2^256*p == q2*p + rem, with c = -a (0 for
//!    secp256k1, 3 for secp256r1) and 2^256*p a constant multiple of p
//!    that keeps the left side nonnegative.
//! So rem == y^2 - x^3 - a*x - b (mod p), and the point is on the curve
//! iff rem is a multiple of p. rem is range-checked below 2^256 < 2p, so
//! the multiples it can be are 0 and p, and the flag is
//! rem == 0 or rem == p. A dishonest prover may present p instead of 0
//! (with q2 - 1), which gives the same flag.
//!
//! Each reduction is an integer identity F == 0 in limbs. Writing F by
//! powers of 2^64 gives eight columns f_0..f_7 (sums of limb products and
//! limbs). The constraint half checks it as follows (constrain_columns):
//! - carries c_k = (f_k + c_(k-1)) / 2^64 for k = 0..4, each a Field
//!   multiple of the constant 1/2^64 (no hint), each RANGEd: c_k + 2^69 to
//!   70 bits;
//! - the top part c_4 + f_5 + f_6*2^64 + f_7*2^128 == 0 in the Field.
//! With every limb below 2^64 (the top quotient limb below 2^65) each
//! |f_k| < 2^132, so each carry equation is an integer one and
//! F = 2^320 * (c_4 + f_5 + f_6*2^64 + f_7*2^128) over the integers. The
//! ranges also give |F| < 2^515, so the bracket is below 2^195 < r in
//! absolute value; it is 0 mod r, hence 0, hence F = 0.
//!
//! Hints (hint_square and hint_curve, built on hint_normalize and
//! hint_divmod) use Field arithmetic, Field comparison,
//! to_le_bits/to_be_bits and constant indices only: no integer bit
//! operation, no division, no branch on a value derived from the inputs.
//! They are trap-free for every argument and run in co-noir's Brillig VM
//! (total-lint --brillig-ops: no unsupported op; no reachable abort site).
//!
//! Cost: about 450 bb gates per check (bb 6.0.0; 446 on each curve inside
//! the ecdsa wrappers, see ecdsa.nr).

use crate::core::{eq, INV_TWO_POW_64, is_zero, lt_bounded, two_pow, TWO_POW_128, TWO_POW_64};

/// secp256k1 base-field modulus p = 2^256 - 2^32 - 977, 64-bit limbs.
global K1_P: [Field; 4] =
    [0xfffffffefffffc2f, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff];
/// secp256k1: y^2 = x^3 + 7, so -a = 0 and b = 7.
global K1_NEG_A: Field = 0;
global K1_B: [Field; 4] = [7, 0, 0, 0];

/// P-256 base-field modulus p = 2^256 - 2^224 + 2^192 + 2^96 - 1.
global R1_P: [Field; 4] = [0xffffffffffffffff, 0xffffffff, 0x0, 0xffffffff00000001];
/// P-256: y^2 = x^3 - 3x + b.
global R1_NEG_A: Field = 3;
global R1_B: [Field; 4] =
    [0x3bce3c3e27d2604b, 0x651d06b0cc53b0f6, 0xb3ebbd55769886bc, 0x5ac635d8aa3a93e7];

/// Flag: (x, y) is an affine point of secp256k1 with canonical
/// coordinates: x < p, y < p and y^2 == x^3 + 7 (mod p). x and y are
/// 32-byte big-endian integers. Total for every input; determined.
/// Constraints: see on_curve.
pub fn secp256k1_on_curve(x: [u8; 32], y: [u8; 32]) -> bool {
    on_curve(x, y, K1_P, K1_NEG_A, K1_B)
}

/// Flag: (x, y) is an affine point of secp256r1 (P-256) with canonical
/// coordinates: x < p, y < p and y^2 == x^3 - 3x + b (mod p). Total for
/// every input; determined. Constraints: see on_curve.
pub fn secp256r1_on_curve(x: [u8; 32], y: [u8; 32]) -> bool {
    on_curve(x, y, R1_P, R1_NEG_A, R1_B)
}

/// The shared check, for a modulus 2^255 < p < 2^256, neg_a in {0, 3} and
/// b < p (the two curves above).
///
/// Constraints, in order:
/// 1. Two be_limbs64 (linear sums of bytes, no constraint).
/// 2. below_p on each coordinate (hint-satisfiable for every byte input,
///    determined; see there). in_range is their AND.
/// 3. Limb selects xs = in_range ? x : 0, ys likewise (arithmetic).
/// 4. constrain_square_mod(xs, p, q1, t) on hint_square's output.
/// 5. constrain_curve_mod(xs, ys, t, p, neg_a, b, q2, rem) on
///    hint_curve's output.
/// 6. is_zero on rem_0 + rem_1 + rem_2 + rem_3 (no wrap: below 2^66) and
///    two core::eq on rem's 128-bit halves against p's (no wrap: each
///    half is below 2^128 by its limb ranges).
///
/// Hint-satisfiable: xs, ys < p by 2-3, so the honest q1 = floor(xs^2/p)
/// is below p and t = xs^2 mod p is below p, which meets every range in
/// 4; with t < p the honest left side of step 2 lies in
/// (0, 2^256*p + p^2 + 3p), so the honest q2 is below 2^256 + p + 3 <
/// 2^257 and rem below p, which meets every range in 5. Both identities
/// are Euclid's. The equality gadgets in 6 are satisfiable for every value.
///
/// Determined: in_range, xs and ys are determined by 2. Every witness
/// that passes 4 has t == xs^2 (mod p) and every witness that passes 5 has
/// rem == ys^2 - xs^3 - a*xs - b (mod p) with 0 <= rem < 2^256 < 2p, so
/// "rem is 0 or p" is "the congruence class is 0", a function of the
/// input. When in_range is false the flag is false whatever rem is.
fn on_curve(x: [u8; 32], y: [u8; 32], p: [Field; 4], neg_a: Field, b: [Field; 4]) -> bool {
    let xl = be_limbs64(x);
    let yl = be_limbs64(y);
    let in_range = below_p(xl, p) & below_p(yl, p);
    let xs = select_limbs(in_range, xl);
    let ys = select_limbs(in_range, yl);
    // Safety: constrain_square_mod pins t to a value congruent to xs^2
    // mod p and below 2^256 (its doc comment has the argument).
    let (q1, t) = unsafe { hint_square(xs, p) };
    constrain_square_mod(xs, p, q1, t);
    // Safety: constrain_curve_mod pins rem to a value below 2^256
    // congruent to ys^2 - t*xs - a*xs - b mod p.
    let (q2, rem) = unsafe { hint_curve(xs, ys, t, p, neg_a, b) };
    constrain_curve_mod(xs, ys, t, p, neg_a, b, q2, rem);
    let rem_lo = rem[0] + rem[1] * TWO_POW_64;
    let rem_hi = rem[2] + rem[3] * TWO_POW_64;
    let p_lo = p[0] + p[1] * TWO_POW_64;
    let p_hi = p[2] + p[3] * TWO_POW_64;
    let rem_zero = is_zero(rem[0] + rem[1] + rem[2] + rem[3]);
    let rem_p = eq(rem_lo, p_lo) & eq(rem_hi, p_hi);
    in_range & (rem_zero | rem_p)
}

/// The 32-byte big-endian integer as four 64-bit limbs, least
/// significant first: limb i is the sum of bytes 8(3 - i) .. 8(3 - i) + 7
/// with weights 2^56 .. 1. Linear in the bytes, no constraint; each limb
/// is below 2^64 because the bytes are u8.
pub(crate) fn be_limbs64(bytes: [u8; 32]) -> [Field; 4] {
    let mut out = [0; 4];
    for i in 0..4 {
        let mut v: Field = 0;
        for j in 0..8 {
            v = v * 256 + bytes[8 * (3 - i) + j] as Field;
        }
        out[i] = v;
    }
    out
}

/// Flag: the integer with limbs l (each below 2^64) is below the one with
/// limbs p. Compares the 128-bit halves: hi < p_hi, or hi == p_hi and
/// lo < p_lo. Constraints: two core::lt_bounded::<128> (a hinted bit and
/// one 128-bit RANGE each; the precondition holds because every half is
/// a sum of two limbs below 2^128) and one core::eq. Hint-satisfiable for
/// every input; determined.
fn below_p(l: [Field; 4], p: [Field; 4]) -> bool {
    let lo = l[0] + l[1] * TWO_POW_64;
    let hi = l[2] + l[3] * TWO_POW_64;
    let p_lo = p[0] + p[1] * TWO_POW_64;
    let p_hi = p[2] + p[3] * TWO_POW_64;
    lt_bounded::<128>(hi, p_hi) | (eq(hi, p_hi) & lt_bounded::<128>(lo, p_lo))
}

/// c ? l : 0 limb-wise. Arithmetic, no constraint; each output is below
/// 2^64 when the input limb is.
fn select_limbs(c: bool, l: [Field; 4]) -> [Field; 4] {
    let mut out = [0; 4];
    for i in 0..4 {
        out[i] = (c as Field) * l[i];
    }
    out
}

/// The seven 2^64-columns of a*b: column k is the sum of a_i*b_j over
/// i + j = k. Arithmetic, no constraint. For limbs below 2^64 (and one
/// operand's top limb below 2^65) every column is below 5*2^128.
/// Written out term by term so the hints that call it index only
/// constants.
pub(crate) fn mul_columns(a: [Field; 4], b: [Field; 4]) -> [Field; 7] {
    [
        a[0] * b[0],
        a[0] * b[1] + a[1] * b[0],
        a[0] * b[2] + a[1] * b[1] + a[2] * b[0],
        a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0],
        a[1] * b[3] + a[2] * b[2] + a[3] * b[1],
        a[2] * b[3] + a[3] * b[2],
        a[3] * b[3],
    ]
}

/// The eight 2^64-columns of the left side of step 2 (module header),
/// y*y - t*x + neg_a*x - b + 2^256*p. Arithmetic, no constraint.
fn curve_columns(
    x: [Field; 4],
    y: [Field; 4],
    t: [Field; 4],
    p: [Field; 4],
    neg_a: Field,
    b: [Field; 4],
) -> [Field; 8] {
    let yy = mul_columns(y, y);
    let tx = mul_columns(t, x);
    let mut f = [0; 8];
    for k in 0..4 {
        f[k] = yy[k] - tx[k] + neg_a * x[k] - b[k];
    }
    f[4] = yy[4] - tx[4] + p[0];
    f[5] = yy[5] - tx[5] + p[1];
    f[6] = yy[6] - tx[6] + p[2];
    f[7] = p[3];
    f
}

/// RANGE q's limbs (64, 64, 64, 65 bits) and rem's limbs (64 bits each).
fn constrain_quotient_remainder(q: [Field; 4], rem: [Field; 4]) {
    for i in 0..3 {
        q[i].assert_max_bit_size::<64>();
    }
    q[3].assert_max_bit_size::<65>();
    for i in 0..4 {
        rem[i].assert_max_bit_size::<64>();
    }
}

/// Checks that F = sum of f_k * 2^(64k) is 0 over the integers, given
/// |f_k| < 2^132 for every k and |F| < 2^515 (PRECONDITIONS, which every
/// caller meets by its limb ranges: the two reductions below and the
/// canonical-coordinate check of ecdsa/blind.nr). Emits:
/// 1. For k = 0..4: c_k = (f_k + c_(k-1)) * (1/2^64) in the Field
///    (c_(-1) = 0; a linear combination, no witness of its own) and RANGE
///    c_k + 2^69 to 70 bits.
/// 2. c_4 + f_5 + f_6*2^64 + f_7*2^128 == 0 in the Field.
/// Honest witness (F = 0): each prefix sum of f_k*2^(64k) over k <= m is
/// minus the rest of F, a multiple of 2^(64(m+1)), so each c_k is the
/// integer prefix sum / 2^(64(k+1)), and |c_k| < (2^132 + 2^69)/2^64 <
/// 2^69 passes 1; then 2 is F / 2^320 = 0.
/// Sound: by induction c_(k-1) is an integer in [-2^69, 2^69); the range
/// makes c_k one too, and c_k*2^64 == f_k + c_(k-1) holds in the Field
/// between values of absolute value below 2^134 < r, so over the
/// integers. Hence the sum of f_k*2^(64k) for k <= 4 is c_4*2^320 and
/// F = 2^320*B with B the bracket in 2. |B| = |F|/2^320 < 2^195 < r and
/// B == 0 mod r, so B = 0 and F = 0.
pub(crate) fn constrain_columns(f: [Field; 8]) {
    let mut c: Field = 0;
    for k in 0..5 {
        c = (f[k] + c) * INV_TWO_POW_64;
        (c + two_pow::<69>()).assert_max_bit_size::<70>();
    }
    assert(c + f[5] + f[6] * TWO_POW_64 + f[7] * TWO_POW_128 == 0, "secp: reduction identity");
}

/// Constraint half of step 1: x*x == q*p + t over the integers, for x
/// with limbs below 2^64 (PRECONDITION; on_curve passes byte sums,
/// selected). Emits constrain_quotient_remainder(q, t) and
/// constrain_columns on the columns of x*x - q*p - t.
/// Column bound: x*x and q*p columns are below 4*2^128 and 5*2^128, t's
/// below 2^64, so |f_k| < 2^132; |F| < 2^512 + 2^513 + 2^256 < 2^515. So
/// constrain_columns applies, and every passing witness has x^2 == q*p + t
/// exactly with 0 <= t < 2^256, so t == x^2 (mod p). The honest hint
/// (x < p: q = floor(x^2/p) < p < 2^256, t = x^2 mod p) passes every
/// check.
fn constrain_square_mod(x: [Field; 4], p: [Field; 4], q: [Field; 4], t: [Field; 4]) {
    constrain_quotient_remainder(q, t);
    let xx = mul_columns(x, x);
    let qp = mul_columns(q, p);
    let mut f = [0; 8];
    for k in 0..7 {
        f[k] = xx[k] - qp[k];
    }
    for k in 0..4 {
        f[k] -= t[k];
    }
    constrain_columns(f);
}

/// Constraint half of step 2: y*y - t*x + neg_a*x - b + 2^256*p ==
/// q*p + rem over the integers, for x, y, t with limbs below 2^64 and
/// neg_a in {0, 3}, b < p (PRECONDITIONS; t's limbs are RANGEd by
/// constrain_square_mod). Emits constrain_quotient_remainder(q, rem) and
/// constrain_columns on the columns of the difference.
/// Column bound: y*y, t*x below 4*2^128 each, q*p below 5*2^128, the
/// linear terms below 2^66, so |f_k| < 2^132; |F| < 2^512 (y^2) +
/// 2^512 (t*x) + 2^513 (q*p) + 2^512 (2^256*p) + 2^259 < 2^515. So every
/// passing witness has the identity exactly, with 0 <= rem < 2^256. The
/// honest hint passes for x, y, t < p (on_curve's argument).
fn constrain_curve_mod(
    x: [Field; 4],
    y: [Field; 4],
    t: [Field; 4],
    p: [Field; 4],
    neg_a: Field,
    b: [Field; 4],
    q: [Field; 4],
    rem: [Field; 4],
) {
    constrain_quotient_remainder(q, rem);
    let qp = mul_columns(q, p);
    let mut f = curve_columns(x, y, t, p, neg_a, b);
    for k in 0..7 {
        f[k] -= qp[k];
    }
    for k in 0..4 {
        f[k] -= rem[k];
    }
    constrain_columns(f);
}

/// The integer sum of bits[i] * 2^(i - lo) for lo <= i < hi. Field
/// arithmetic on constant ranges; trap-free (every call passes
/// hi <= 254).
unconstrained fn bits_value(bits: [bool; 254], lo: u32, hi: u32) -> Field {
    let mut v: Field = 0;
    let mut pw: Field = 1;
    for i in lo..hi {
        v = v + (bits[i] as Field) * pw;
        pw = pw * 2;
    }
    v
}

/// Signed 2^64-columns to 64-bit limbs: limb k = (col_k + carry) mod 2^64,
/// carry' = floor((col_k + carry) / 2^64), with the final carry dropped.
/// Each step adds the offset 2^140 (a multiple of 2^64) before
/// to_le_bits so a negative column sum is handled by the same split, and
/// removes 2^76 from the carry. Trap-free for every argument (Field
/// arithmetic, to_le_bits of any Field, constant indices). Exact when
/// every |col_k + carry| < 2^140 and the total is a nonnegative integer
/// below 2^(64N); the callers' columns are below 2^132 with carries below
/// 2^69, and their totals below 2^515 < 2^576.
unconstrained fn hint_normalize<let N: u32>(cols: [Field; N]) -> [Field; N] {
    let mut out = [0; N];
    let mut carry: Field = 0;
    for k in 0..N {
        let bits: [bool; 254] = (cols[k] + carry + two_pow::<140>()).to_le_bits();
        out[k] = bits_value(bits, 0, 64);
        carry = bits_value(bits, 64, 254) - two_pow::<76>();
    }
    out
}

/// One 64-bit limb of binary restoring division by p: for a running
/// remainder (r_lo, r_hi) below p and a limb below 2^64, returns the
/// remainder of r*2^64 + limb and the 64 quotient bits, most significant
/// first. The remainder is held as two 128-bit Field halves and stays
/// below p, so 2*r + 1 < 2^257 and each half stays below 2^129. Each step
/// is arithmetic (subtract ge*p with a borrow formed from a comparison),
/// so there is no branch on the data. The limb's bits are read from a
/// 254-bit big-endian decomposition at the constant positions 190..253.
/// Trap-free for every argument: Field arithmetic and comparison,
/// to_be_bits of any Field, constant indices.
unconstrained fn divmod_limb(
    r_lo: Field,
    r_hi: Field,
    limb: Field,
    p_lo: Field,
    p_hi: Field,
) -> (Field, Field, Field) {
    let bits: [bool; 254] = limb.to_be_bits();
    let mut lo = r_lo;
    let mut hi = r_hi;
    let mut acc: Field = 0;
    for k in 190..254 {
        let lo2 = lo * 2 + (bits[k] as Field);
        let carry = (!lo2.lt(TWO_POW_128)) as Field;
        let lo2 = lo2 - carry * TWO_POW_128;
        let hi2 = hi * 2 + carry;
        let lo_below = lo2.lt(p_lo) as Field;
        let ge = (p_hi.lt(hi2) as Field) + ((hi2 == p_hi) as Field) * (1 - lo_below);
        let borrow = ge * lo_below;
        lo = lo2 - ge * p_lo + borrow * TWO_POW_128;
        hi = hi2 - ge * p_hi - borrow;
        acc = acc * 2 + ge;
    }
    (lo, hi, acc)
}

/// (q, rem) with d = q*p + rem and 0 <= rem < p, for d given as nine
/// 64-bit limbs (least significant first) and p as four, 2^255 < p < 2^256:
/// divmod_limb over the limbs from the top, written out so every index
/// is a constant. q is returned in the four-limb form the constraints
/// take, the top limb holding q_3 + q_4*2^64 (q < 2^257 for the callers,
/// so q_5..q_8 are 0 and dropped). Trap-free for every argument (see
/// divmod_limb); exact when every limb of d is below 2^64.
unconstrained fn hint_divmod(d: [Field; 9], p: [Field; 4]) -> ([Field; 4], [Field; 4]) {
    let p_lo = p[0] + p[1] * TWO_POW_64;
    let p_hi = p[2] + p[3] * TWO_POW_64;
    let (lo, hi, _) = divmod_limb(0, 0, d[8], p_lo, p_hi);
    let (lo, hi, _) = divmod_limb(lo, hi, d[7], p_lo, p_hi);
    let (lo, hi, _) = divmod_limb(lo, hi, d[6], p_lo, p_hi);
    let (lo, hi, _) = divmod_limb(lo, hi, d[5], p_lo, p_hi);
    let (lo, hi, q4) = divmod_limb(lo, hi, d[4], p_lo, p_hi);
    let (lo, hi, q3) = divmod_limb(lo, hi, d[3], p_lo, p_hi);
    let (lo, hi, q2) = divmod_limb(lo, hi, d[2], p_lo, p_hi);
    let (lo, hi, q1) = divmod_limb(lo, hi, d[1], p_lo, p_hi);
    let (lo, hi, q0) = divmod_limb(lo, hi, d[0], p_lo, p_hi);
    let lo_bits: [bool; 254] = lo.to_le_bits();
    let hi_bits: [bool; 254] = hi.to_le_bits();
    let rem = [
        bits_value(lo_bits, 0, 64),
        bits_value(lo_bits, 64, 254),
        bits_value(hi_bits, 0, 64),
        bits_value(hi_bits, 64, 254),
    ];
    ([q0, q1, q2, q3 + q4 * TWO_POW_64], rem)
}

/// Hint for step 1: (floor(x^2/p), x^2 mod p). Trap-free (hint_normalize
/// and hint_divmod are); exact for x < 2^256 with limbs below 2^64.
unconstrained fn hint_square(x: [Field; 4], p: [Field; 4]) -> ([Field; 4], [Field; 4]) {
    let c = mul_columns(x, x);
    let mut cols = [0; 9];
    for k in 0..7 {
        cols[k] = c[k];
    }
    hint_divmod(hint_normalize(cols), p)
}

/// Hint for step 2: quotient and remainder of
/// y*y - t*x + neg_a*x - b + 2^256*p by p. Trap-free; exact for x, y,
/// t < p (the left side is then a nonnegative integer below 2^513).
unconstrained fn hint_curve(
    x: [Field; 4],
    y: [Field; 4],
    t: [Field; 4],
    p: [Field; 4],
    neg_a: Field,
    b: [Field; 4],
) -> ([Field; 4], [Field; 4]) {
    let c = curve_columns(x, y, t, p, neg_a, b);
    let mut cols = [0; 9];
    for k in 0..8 {
        cols[k] = c[k];
    }
    hint_divmod(hint_normalize(cols), p)
}

mod tests {
    use crate::core::TWO_POW_64;
    use crate::test_support::wit as w;
    use super::{
        be_limbs64, bits_value, constrain_curve_mod, constrain_square_mod, curve_columns,
        hint_curve, hint_normalize, hint_square, K1_B, K1_NEG_A, K1_P, mul_columns, R1_B, R1_NEG_A,
        R1_P, secp256k1_on_curve, secp256r1_on_curve,
    };

    // Points generated with Python's integer arithmetic. G and 2G are the
    // standard generators and their doubles. *_X_PLUS_P_X is x0 + p for an
    // on-curve point (x0, *_X_PLUS_P_Y) with small x0, so it reduces onto
    // the curve; K1_Y_PLUS_P_* likewise in y. *_XMAX_* has x = p - 3, the
    // largest on-curve x. R1_XP_Y makes (0, R1_XP_Y) a P-256 point, so
    // (p, R1_XP_Y) reduces onto the curve. *_OFF_* are random coordinates
    // below p that are not on the curve.
    global K1_GX: [u8; 32] = [
        0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0, 0x62, 0x95, 0xce, 0x87, 0x0b,
        0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9, 0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8,
        0x17, 0x98,
    ];
    global K1_GY: [u8; 32] = [
        0x48, 0x3a, 0xda, 0x77, 0x26, 0xa3, 0xc4, 0x65, 0x5d, 0xa4, 0xfb, 0xfc, 0x0e, 0x11, 0x08,
        0xa8, 0xfd, 0x17, 0xb4, 0x48, 0xa6, 0x85, 0x54, 0x19, 0x9c, 0x47, 0xd0, 0x8f, 0xfb, 0x10,
        0xd4, 0xb8,
    ];
    global K1_2GX: [u8; 32] = [
        0xc6, 0x04, 0x7f, 0x94, 0x41, 0xed, 0x7d, 0x6d, 0x30, 0x45, 0x40, 0x6e, 0x95, 0xc0, 0x7c,
        0xd8, 0x5c, 0x77, 0x8e, 0x4b, 0x8c, 0xef, 0x3c, 0xa7, 0xab, 0xac, 0x09, 0xb9, 0x5c, 0x70,
        0x9e, 0xe5,
    ];
    global K1_2GY: [u8; 32] = [
        0x1a, 0xe1, 0x68, 0xfe, 0xa6, 0x3d, 0xc3, 0x39, 0xa3, 0xc5, 0x84, 0x19, 0x46, 0x6c, 0xea,
        0xee, 0xf7, 0xf6, 0x32, 0x65, 0x32, 0x66, 0xd0, 0xe1, 0x23, 0x64, 0x31, 0xa9, 0x50, 0xcf,
        0xe5, 0x2a,
    ];
    global K1_X_PLUS_P_X: [u8; 32] = [
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xff, 0xff,
        0xfc, 0x30,
    ];
    global K1_X_PLUS_P_Y: [u8; 32] = [
        0x42, 0x18, 0xf2, 0x0a, 0xe6, 0xc6, 0x46, 0xb3, 0x63, 0xdb, 0x68, 0x60, 0x58, 0x22, 0xfb,
        0x14, 0x26, 0x4c, 0xa8, 0xd2, 0x58, 0x7f, 0xdd, 0x6f, 0xbc, 0x75, 0x0d, 0x58, 0x7e, 0x76,
        0xa7, 0xee,
    ];
    global K1_Y_PLUS_P_X: [u8; 32] = [
        0x1f, 0xe1, 0xe5, 0xef, 0x3f, 0xce, 0xb5, 0xc1, 0x35, 0xab, 0x77, 0x41, 0x33, 0x3c, 0xe5,
        0xa6, 0xe8, 0x0d, 0x68, 0x16, 0x76, 0x53, 0xf6, 0xb2, 0xb2, 0x4b, 0xcb, 0xcf, 0xaa, 0xaf,
        0xf5, 0x07,
    ];
    global K1_XMAX_X: [u8; 32] = [
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xff, 0xff,
        0xfc, 0x2c,
    ];
    global K1_XMAX_Y: [u8; 32] = [
        0x0e, 0x99, 0x4b, 0x14, 0xea, 0x72, 0xf8, 0xc3, 0xeb, 0x95, 0xc7, 0x1e, 0xf6, 0x92, 0x57,
        0x5e, 0x77, 0x50, 0x58, 0x33, 0x2d, 0x7e, 0x52, 0xd0, 0x99, 0x5c, 0xf8, 0x03, 0x88, 0x71,
        0xb6, 0x7d,
    ];
    global K1_OFF_X: [u8; 32] = [
        0xd2, 0x3f, 0x08, 0x24, 0x12, 0x8b, 0x2f, 0x33, 0x0c, 0x5c, 0x7f, 0xd0, 0xa6, 0xa3, 0xa4,
        0x50, 0x65, 0x13, 0x27, 0x0e, 0x26, 0x9e, 0x0d, 0x37, 0xf2, 0xa7, 0x4d, 0xe4, 0x52, 0xe6,
        0xb4, 0x38,
    ];
    global K1_OFF_Y: [u8; 32] = [
        0x36, 0xf6, 0x75, 0xcc, 0x81, 0xe7, 0x4e, 0xf5, 0xe8, 0xe2, 0x5d, 0x94, 0x0e, 0xd9, 0x04,
        0x75, 0x95, 0x31, 0x98, 0x5d, 0x5d, 0x9d, 0xc9, 0xf8, 0x18, 0x18, 0xe8, 0x11, 0x89, 0x2f,
        0x90, 0x2b,
    ];
    global R1_GX: [u8; 32] = [
        0x6b, 0x17, 0xd1, 0xf2, 0xe1, 0x2c, 0x42, 0x47, 0xf8, 0xbc, 0xe6, 0xe5, 0x63, 0xa4, 0x40,
        0xf2, 0x77, 0x03, 0x7d, 0x81, 0x2d, 0xeb, 0x33, 0xa0, 0xf4, 0xa1, 0x39, 0x45, 0xd8, 0x98,
        0xc2, 0x96,
    ];
    global R1_GY: [u8; 32] = [
        0x4f, 0xe3, 0x42, 0xe2, 0xfe, 0x1a, 0x7f, 0x9b, 0x8e, 0xe7, 0xeb, 0x4a, 0x7c, 0x0f, 0x9e,
        0x16, 0x2b, 0xce, 0x33, 0x57, 0x6b, 0x31, 0x5e, 0xce, 0xcb, 0xb6, 0x40, 0x68, 0x37, 0xbf,
        0x51, 0xf5,
    ];
    global R1_2GX: [u8; 32] = [
        0x7c, 0xf2, 0x7b, 0x18, 0x8d, 0x03, 0x4f, 0x7e, 0x8a, 0x52, 0x38, 0x03, 0x04, 0xb5, 0x1a,
        0xc3, 0xc0, 0x89, 0x69, 0xe2, 0x77, 0xf2, 0x1b, 0x35, 0xa6, 0x0b, 0x48, 0xfc, 0x47, 0x66,
        0x99, 0x78,
    ];
    global R1_2GY: [u8; 32] = [
        0x07, 0x77, 0x55, 0x10, 0xdb, 0x8e, 0xd0, 0x40, 0x29, 0x3d, 0x9a, 0xc6, 0x9f, 0x74, 0x30,
        0xdb, 0xba, 0x7d, 0xad, 0xe6, 0x3c, 0xe9, 0x82, 0x29, 0x9e, 0x04, 0xb7, 0x9d, 0x22, 0x78,
        0x73, 0xd1,
    ];
    global R1_X_PLUS_P_X: [u8; 32] = [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x04,
    ];
    global R1_X_PLUS_P_Y: [u8; 32] = [
        0x45, 0x92, 0x43, 0xb9, 0xaa, 0x58, 0x18, 0x06, 0xfe, 0x91, 0x3b, 0xce, 0x99, 0x81, 0x7a,
        0xde, 0x11, 0xca, 0x50, 0x3c, 0x64, 0xd9, 0xa3, 0xc5, 0x33, 0x41, 0x5c, 0x08, 0x32, 0x48,
        0xfb, 0xcc,
    ];
    global R1_XP_Y: [u8; 32] = [
        0x66, 0x48, 0x5c, 0x78, 0x0e, 0x2f, 0x83, 0xd7, 0x24, 0x33, 0xbd, 0x5d, 0x84, 0xa0, 0x6b,
        0xb6, 0x54, 0x1c, 0x2a, 0xf3, 0x1d, 0xae, 0x87, 0x17, 0x28, 0xbf, 0x85, 0x6a, 0x17, 0x4f,
        0x93, 0xf4,
    ];
    global R1_XMAX_X: [u8; 32] = [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xfc,
    ];
    global R1_XMAX_Y: [u8; 32] = [
        0x19, 0x71, 0x9b, 0xeb, 0xf6, 0xae, 0xa1, 0x3f, 0x25, 0xc9, 0x6d, 0xfd, 0x7c, 0x71, 0xf5,
        0x22, 0x5d, 0x4c, 0x8f, 0xc0, 0x9e, 0xb5, 0xa0, 0xab, 0x9f, 0x39, 0xe9, 0x17, 0x8e, 0x55,
        0xc1, 0x21,
    ];
    global R1_OFF_X: [u8; 32] = [
        0x8d, 0x11, 0x6e, 0xce, 0x17, 0x38, 0xf7, 0xd9, 0x3d, 0x9c, 0x17, 0x24, 0x11, 0xe2, 0x0b,
        0x8f, 0x6b, 0x0d, 0x54, 0x9b, 0x6f, 0x03, 0x67, 0x5a, 0x16, 0x00, 0xa3, 0x5a, 0x09, 0x99,
        0x50, 0xd8,
    ];
    global R1_OFF_Y: [u8; 32] = [
        0xa1, 0x70, 0xb3, 0x38, 0x39, 0x26, 0x30, 0x59, 0xf2, 0x8c, 0x10, 0x5d, 0x1f, 0xb1, 0x7c,
        0x23, 0x90, 0xc1, 0x92, 0xcf, 0xd3, 0xac, 0x94, 0xaf, 0x0f, 0x21, 0xdd, 0xb6, 0x6c, 0xad,
        0x4a, 0x26,
    ];
    /// The circuit modulus r as 64-bit limbs.
    global BN_R: [Field; 4] =
        [0x43e1f593f0000001, 0x2833e84879b97091, 0xb85045b68181585d, 0x30644e72e131a029];

    fn k1(x: [u8; 32], y: [u8; 32]) -> bool {
        secp256k1_on_curve(w(x), w(y))
    }

    fn r1(x: [u8; 32], y: [u8; 32]) -> bool {
        secp256r1_on_curve(w(x), w(y))
    }

    /// The 32-byte big-endian encoding of a small integer.
    fn small(v: u8) -> [u8; 32] {
        let mut out = [0; 32];
        out[31] = v;
        out
    }

    /// The field value of four limbs: sum of l_i * 2^(64i) mod r.
    fn value(l: [Field; 4]) -> Field {
        l[0]
            + l[1] * TWO_POW_64
            + l[2] * TWO_POW_64 * TWO_POW_64
            + l[3] * TWO_POW_64 * TWO_POW_64 * TWO_POW_64
    }

    /// The canonical 64-bit limbs of a Field element (below 2^254).
    unconstrained fn field_limbs(v: Field) -> [Field; 4] {
        let bits: [bool; 254] = v.to_le_bits();
        [
            bits_value(bits, 0, 64),
            bits_value(bits, 64, 128),
            bits_value(bits, 128, 192),
            bits_value(bits, 192, 254),
        ]
    }

    /// Every limb below 2^64, except the top one below 2^65 when top65.
    unconstrained fn limbs_in_range(l: [Field; 4], top65: bool) -> bool {
        let top = if top65 { 2 * TWO_POW_64 } else { TWO_POW_64 };
        l[0].lt(TWO_POW_64) & l[1].lt(TWO_POW_64) & l[2].lt(TWO_POW_64) & l[3].lt(top)
    }

    /// The step-1 identity checked in the circuit field only.
    fn square_native(x: [Field; 4], p: [Field; 4], q: [Field; 4], t: [Field; 4]) -> bool {
        value(x) * value(x) == value(q) * value(p) + value(t)
    }

    /// The step-2 identity checked in the circuit field only.
    fn curve_native(
        x: [Field; 4],
        y: [Field; 4],
        t: [Field; 4],
        p: [Field; 4],
        neg_a: Field,
        b: [Field; 4],
        q: [Field; 4],
        rem: [Field; 4],
    ) -> bool {
        let f = curve_columns(x, y, t, p, neg_a, b);
        let mut lhs: Field = 0;
        let mut w: Field = 1;
        for k in 0..8 {
            lhs += f[k] * w;
            w *= TWO_POW_64;
        }
        lhs == value(q) * value(p) + value(rem)
    }

    // --- valid keys ---

    #[test]
    fn generators_and_doubles_on_curve() {
        assert(k1(K1_GX, K1_GY));
        assert(k1(K1_2GX, K1_2GY));
        assert(r1(R1_GX, R1_GY));
        assert(r1(R1_2GX, R1_2GY));
        // the largest on-curve x, p - 3
        assert(k1(K1_XMAX_X, K1_XMAX_Y));
        assert(r1(R1_XMAX_X, R1_XMAX_Y));
        // the other curve's points are not on this one
        assert(!k1(R1_GX, R1_GY));
        assert(!r1(K1_GX, K1_GY));
    }

    // --- off-curve keys ---

    // (0, 1), (0, 2) and (5, 0): off both curves, and of order 3, 3 and 2
    // on their own curves y^2 = x^3 + b'.
    #[test]
    fn small_order_off_curve_keys_rejected() {
        assert(!k1(small(0), small(1)));
        assert(!k1(small(0), small(2)));
        assert(!k1(small(5), small(0)));
        assert(!r1(small(0), small(1)));
        assert(!r1(small(0), small(2)));
        assert(!r1(small(5), small(0)));
    }

    #[test]
    fn zero_coordinates_rejected() {
        assert(!k1([0; 32], [0; 32]));
        assert(!k1(K1_GX, [0; 32]));
        assert(!k1([0; 32], K1_GY));
        assert(!r1([0; 32], [0; 32]));
        assert(!r1(R1_GX, [0; 32]));
        assert(!r1([0; 32], R1_GY));
    }

    #[test]
    fn random_off_curve_rejected() {
        assert(!k1(K1_OFF_X, K1_OFF_Y));
        assert(!r1(R1_OFF_X, R1_OFF_Y));
        // one bit off a valid point
        let mut y = K1_GY;
        y[31] ^= 1;
        assert(!k1(K1_GX, y));
        let mut y2 = R1_GY;
        y2[31] ^= 1;
        assert(!r1(R1_GX, y2));
    }

    // Coordinates >= p that are congruent to an on-curve point: the
    // arithmetic alone would accept them, the range flag does not.
    #[test]
    fn coordinates_at_or_above_p_rejected() {
        assert(k1(small(1), K1_X_PLUS_P_Y));
        assert(!k1(K1_X_PLUS_P_X, K1_X_PLUS_P_Y));
        assert(k1(K1_Y_PLUS_P_X, small(1)));
        // K1_X_PLUS_P_X is p + 1 and serves as y = p + 1 here
        assert(!k1(K1_Y_PLUS_P_X, K1_X_PLUS_P_X));
        assert(r1(small(5), R1_X_PLUS_P_Y));
        assert(!r1(R1_X_PLUS_P_X, R1_X_PLUS_P_Y));
        assert(r1(small(0), R1_XP_Y));
        let mut p_bytes = [0; 32];
        for i in 0..32 {
            p_bytes[i] = R1_XMAX_X[i];
        }
        p_bytes[31] = 0xff; // p = (p - 3) + 3, no carry out of the last byte
        assert(!r1(p_bytes, R1_XP_Y));
        assert(!k1([0xff; 32], [0xff; 32]));
        assert(!r1([0xff; 32], [0xff; 32]));
    }

    // --- hints and constraint halves ---

    /// Honest hints for the step-1 and step-2 constraint halves of (x, y).
    unconstrained fn honest(
        x: [u8; 32],
        y: [u8; 32],
        p: [Field; 4],
        neg_a: Field,
        b: [Field; 4],
    ) -> ([Field; 4], [Field; 4], [Field; 4], [Field; 4], [Field; 4], [Field; 4]) {
        let xl = be_limbs64(x);
        let yl = be_limbs64(y);
        let (q1, t) = hint_square(xl, p);
        let (q2, rem) = hint_curve(xl, yl, t, p, neg_a, b);
        (xl, yl, q1, t, q2, rem)
    }

    #[test]
    fn honest_hints_pass_constraint_halves() {
        // Safety: test-only; the constraint halves below check the hints.
        let (x, y, q1, t, q2, rem) = unsafe { honest(K1_GX, K1_GY, K1_P, K1_NEG_A, K1_B) };
        constrain_square_mod(x, K1_P, q1, t);
        constrain_curve_mod(x, y, t, K1_P, K1_NEG_A, K1_B, q2, rem);
        assert_eq(rem, [0; 4]);
        // Safety: as above.
        let (x2, y2, q12, t2, q22, rem2) =
            unsafe { honest(R1_OFF_X, R1_OFF_Y, R1_P, R1_NEG_A, R1_B) };
        constrain_square_mod(x2, R1_P, q12, t2);
        constrain_curve_mod(x2, y2, t2, R1_P, R1_NEG_A, R1_B, q22, rem2);
        assert(rem2 != [0; 4]);
    }

    // rem = p with q2 - 1 is the other witness for an on-curve point. It
    // passes, and the flag counts it as a multiple of p, so the flag does
    // not depend on which of the two the prover presents.
    #[test]
    fn remainder_p_witness_accepted() {
        // Safety: test-only; checked by the constraint half below.
        let (x, y, _, t, q2, rem) = unsafe { honest(R1_GX, R1_GY, R1_P, R1_NEG_A, R1_B) };
        assert_eq(rem, [0; 4]);
        assert(q2[0] != 0);
        let q_alt = [q2[0] - 1, q2[1], q2[2], q2[3]];
        constrain_curve_mod(x, y, t, R1_P, R1_NEG_A, R1_B, q_alt, R1_P);
    }

    // Off by one: the first carry is no longer an integer.
    #[test(should_fail)]
    fn wrong_square_remainder_rejected() {
        // Safety: test-only; the hint is altered on purpose.
        let (x, _, q1, t, _, _) = unsafe { honest(K1_GX, K1_GY, K1_P, K1_NEG_A, K1_B) };
        constrain_square_mod(x, K1_P, q1, [t[0] + 1, t[1], t[2], t[3]]);
    }

    /// t with 2^64 moved from limb 1 into limb 0: the same integer, limb 0
    /// out of range.
    unconstrained fn noncanonical(t: [Field; 4]) -> [Field; 4] {
        [t[0] + TWO_POW_64, t[1] - 1, t[2], t[3]]
    }

    #[test]
    fn noncanonical_limbs_are_the_same_integer() {
        // Safety: test-only.
        let (x, _, q1, t, _, _) = unsafe { honest(K1_GX, K1_GY, K1_P, K1_NEG_A, K1_B) };
        assert(t[1] != 0);
        // Safety: test-only.
        let t_bad = unsafe { noncanonical(t) };
        assert(square_native(x, K1_P, q1, t_bad));
        // Safety: test-only.
        assert(!unsafe { limbs_in_range(t_bad, false) });
    }

    // The limb RANGEs are load-bearing: this witness meets the identity
    // and every carry, and only limb 0's RANGE rejects it.
    #[test(should_fail)]
    fn noncanonical_limbs_rejected() {
        // Safety: test-only; the hint is altered on purpose.
        let (x, _, q1, t, _, _) = unsafe { honest(K1_GX, K1_GY, K1_P, K1_NEG_A, K1_B) };
        // Safety: test-only.
        constrain_square_mod(x, K1_P, q1, unsafe { noncanonical(t) });
    }

    /// t + r as limbs: congruent to t mod the circuit modulus, a different
    /// integer.
    unconstrained fn plus_bn_r(t: [Field; 4]) -> [Field; 5] {
        hint_normalize(
            [t[0] + BN_R[0], t[1] + BN_R[1], t[2] + BN_R[2], t[3] + BN_R[3], 0],
        )
    }

    #[test]
    fn circuit_field_wrap_witness_is_well_formed() {
        // Safety: test-only.
        let (x, _, q1, t, _, _) = unsafe { honest(K1_GX, K1_GY, K1_P, K1_NEG_A, K1_B) };
        // Safety: test-only.
        let s = unsafe { plus_bn_r(t) };
        assert_eq(s[4], 0);
        let t_wrap = [s[0], s[1], s[2], s[3]];
        assert(square_native(x, K1_P, q1, t_wrap));
        // Safety: test-only.
        assert(unsafe { limbs_in_range(t_wrap, false) });
    }

    // The carries are load-bearing: t + r has in-range limbs and meets the
    // identity in the circuit field, and only the carry RANGEs reject it.
    #[test(should_fail)]
    fn circuit_field_wrap_witness_rejected() {
        // Safety: test-only; the hint is altered on purpose.
        let (x, _, q1, t, _, _) = unsafe { honest(K1_GX, K1_GY, K1_P, K1_NEG_A, K1_B) };
        // Safety: test-only.
        let s = unsafe { plus_bn_r(t) };
        constrain_square_mod(x, K1_P, q1, [s[0], s[1], s[2], s[3]]);
    }

    /// A step-2 witness that claims rem = 0 for an off-curve point: q is
    /// chosen so that q*p == q2*p + rem holds in the circuit field, with
    /// canonical limbs (q < r < 2^254).
    unconstrained fn flag_flip(q2: [Field; 4], rem: [Field; 4], p: [Field; 4]) -> [Field; 4] {
        field_limbs(value(q2) + value(rem) / value(p))
    }

    #[test]
    fn flag_flip_witness_is_well_formed() {
        // Safety: test-only.
        let (x, y, _, t, q2, rem) = unsafe { honest(K1_OFF_X, K1_OFF_Y, K1_P, K1_NEG_A, K1_B) };
        assert(rem != [0; 4]);
        // Safety: test-only.
        let q = unsafe { flag_flip(q2, rem, K1_P) };
        assert(curve_native(x, y, t, K1_P, K1_NEG_A, K1_B, q, [0; 4]));
        // Safety: test-only.
        assert(unsafe { limbs_in_range(q, true) });
    }

    // An off-curve point cannot be passed off as on-curve: the witness
    // above meets the circuit-field identity and the limb RANGEs, and the
    // carries reject it.
    #[test(should_fail)]
    fn flag_flip_witness_rejected() {
        // Safety: test-only; the hint is altered on purpose.
        let (x, y, _, t, q2, rem) = unsafe { honest(K1_OFF_X, K1_OFF_Y, K1_P, K1_NEG_A, K1_B) };
        // Safety: test-only.
        let q = unsafe { flag_flip(q2, rem, K1_P) };
        constrain_curve_mod(x, y, t, K1_P, K1_NEG_A, K1_B, q, [0; 4]);
    }

    // --- hints on hostile arguments ---

    // The hints return for out-of-precondition arguments (limbs far above
    // 2^64, a zero modulus): no trap.
    #[test]
    unconstrained fn hints_do_not_trap() {
        let big = [0 - 1, 0 - 1, 0 - 1, 0 - 1];
        let _ = hint_square(big, K1_P);
        let _ = hint_square(big, [0; 4]);
        let _ = hint_curve(big, big, big, R1_P, R1_NEG_A, R1_B);
        let _ = hint_curve(big, big, big, [0; 4], 0, [0; 4]);
        let _ = hint_normalize(mul_columns(big, big));
    }

    // hint_divmod's quotient and remainder recombine to the dividend, for
    // the largest dividends the callers produce.
    #[test]
    unconstrained fn hint_square_at_the_top() {
        let m = 0xffffffffffffffff;
        let x = [m, m, m, m];
        let (q, t) = hint_square(x, K1_P);
        assert(limbs_in_range(q, true));
        assert(limbs_in_range(t, false));
        // (2^256 - 1)^2 = q*p + t, checked through the constraint half,
        // whose honest q here has a 65-bit top limb
        constrain_square_mod(x, K1_P, q, t);
        assert(square_native(x, K1_P, q, t));
    }
}
