//! Total arithmetic on the native signed types i8, i16, i32, i64.
//!
//! Native signed operators fail in constrained code: + - * on overflow,
//! unary minus of MIN, / and % by zero, MIN / -1 and MIN % -1. The
//! facades here (TotalArith, Saturating and TotalMulDiv from arith.nr,
//! plus TotalSigned) return a value and a determined flag instead, or a
//! value alone where nothing can fail (saturating_*, signum).
//!
//! Representation. `iN as Field` is a compile error ("Only unsigned
//! integer types may be casted to Field"). `iN as uN` reinterprets the
//! bits, so the pattern (x as uN) as Field is the two's complement bit
//! pattern in [0, 2^N): -1i8 -> 255, i8::MIN -> 128, 127i8 -> 127,
//! -1i64 -> 2^64 - 1, i64::MIN -> 2^63. The way back is `p as uN as iN`
//! (255 -> -1, 128 -> -128), applied only after p is range-checked to N
//! bits, so the cast is exact. Patterns of typed values are below 2^N by
//! the type invariant, which discharges the core gadget preconditions.
//!
//! With H = 2^(N-1) and real value x in [-H, H - 1]:
//! - biased value u = x + H = pattern XOR H, in [0, 2^N). XOR with H is
//!   its own inverse, so core::bias maps pattern to biased and back.
//! - sign and magnitude: negative iff pattern >= H; magnitude in [0, H].
//!
//! Semantics match the native operators wherever those succeed: / and %
//! round toward zero and the remainder takes the dividend's sign
//! (-7 / 2 = -3, -7 % 2 = -1, 7 % -2 = 1). div_floor_or rounds toward
//! negative infinity (-7 / 2 = -4); div_euclid_or and rem_euclid_or give
//! the pair with 0 <= r < |d| (-7 = -4*2 + 1, -7 = 4*(-2) + 1). On
//! ok = false every value is 0 (a select on the pattern before the cast,
//! or a dividend selected to 0 before the division); the wrapped results
//! of + - * are std's wrapping_add/sub/mul.

use crate::arith::{Saturating, TotalArith, TotalMulDiv};
use crate::convert::{cast_i16, cast_i32, cast_i64, cast_i8, cast_u16, cast_u32, cast_u64, cast_u8};
use crate::core::{
    bias, div_split, eq, is_zero, lt_bounded, mul_div_split, mul_split, select_field, split_at,
    two_pow,
};

/// Signed operations beyond the operators, for i8, i16, i32, i64.
/// - neg_or, abs_or: flagged at MIN, the only failing input.
/// - signum: -1, 0 or 1. Total.
/// - div_floor_or(a, d): floor(a / d), rounding toward negative
///   infinity.
/// - div_euclid_or(a, d), rem_euclid_or(a, d): the Euclidean pair
///   a = q*d + r with 0 <= r < |d|.
/// The three divisions are flagged on d = 0 and on MIN with d = -1 (for
/// rem_euclid_or too, like native % and mod_or, although the remainder
/// would be 0). On ok = false the value is 0.
pub trait TotalSigned {
    fn neg_or(self) -> (Self, bool);
    fn abs_or(self) -> (Self, bool);
    fn signum(self) -> Self;
    fn div_floor_or(self, other: Self) -> (Self, bool);
    fn div_euclid_or(self, other: Self) -> (Self, bool);
    fn rem_euclid_or(self, other: Self) -> (Self, bool);
}

// ---------------------------------------------------------------------
// Width-N gadgets on patterns below 2^N (2 <= N <= 64 here; each
// caller's operands are typed, so the bound holds by the type
// invariant). Every returned pattern is below 2^N for every satisfying
// witness; the facades cast it back with convert::cast_iN, whose
// implied range check makes the cast exact.
// ---------------------------------------------------------------------

/// (negative, magnitude) of a pattern p < 2^N. Constraint:
/// core::lt_bounded. The magnitude is 2^N - p for negative patterns and
/// p otherwise, so it lies in [0, H].
fn sign_mag<let N: u32>(p: Field) -> (bool, Field) {
    let neg = !lt_bounded::<N>(p, two_pow::<N - 1>());
    (neg, select_field(neg, two_pow::<N>() - p, p))
}

/// Pattern of -m, i.e. (2^N - m) mod 2^N, for 0 <= m < 2^N. Constraint:
/// is_zero (inversion gadget, hint-satisfiable, determined). Output
/// below 2^N.
fn neg_pattern<let N: u32>(m: Field) -> Field {
    select_field(is_zero(m), 0, two_pow::<N>() - m)
}

/// Pattern of the signed value with sign neg and magnitude m, for
/// 0 <= m < 2^N: m, or neg_pattern(m) when neg. A negative zero is 0.
fn signed_pattern<let N: u32>(neg: bool, m: Field) -> Field {
    select_field(neg, neg_pattern::<N>(m), m)
}

/// Signed addition before the failure select: (wrapped pattern, hi).
/// t = u_a + u_b + H is the biased sum shifted up by 2^N: the biased
/// result u_a + u_b - H lies in [0, 2^N) exactly when t lies in
/// [2^N, 2^(N+1)). t is in [H, 2^(N+1) + H - 2], below 2^(N+2) <= 2^66,
/// so core::split_at::<N, 2> applies: t = lo + hi*2^N with lo < 2^N and
/// hi < 4 (in fact hi in {0, 1, 2}): hi = 1 is in range, hi = 0 is below
/// MIN, hi = 2 above MAX. In every case lo is the biased result mod 2^N,
/// so bias(lo) is the wrapped pattern.
/// Constraints: three lt_bounded (two biases, one unbias) and the split
/// (RANGE lo to N bits, RANGE hi to 2 bits, the reconstruction;
/// hint-satisfiable since t < 2^(N+2), and unique). All determined.
fn s_add_parts<let N: u32>(pa: Field, pb: Field) -> (Field, Field) {
    let h = two_pow::<N - 1>();
    let t = bias::<N>(pa) + bias::<N>(pb) + h;
    let (lo, hi) = split_at::<N, 2>(t);
    (bias::<N>(lo), hi)
}

/// Signed subtraction before the failure select. The biased result is
/// u_a - u_b + H, in range iff it lies in [0, 2^N). Shift by 2^N to keep
/// the split operand non-negative: t = u_a - u_b + 2^N + H. Since
/// u_a - u_b lies in [-(2^N - 1), 2^N - 1], t lies in
/// [H + 1, 2^(N+1) + H - 1], positive and below 2^(N+2); hi is read as
/// in s_add_parts, and lo is the biased result mod 2^N. Same constraints
/// as s_add_parts.
fn s_sub_parts<let N: u32>(pa: Field, pb: Field) -> (Field, Field) {
    let h = two_pow::<N - 1>();
    let t = bias::<N>(pa) - bias::<N>(pb) + two_pow::<N>() + h;
    let (lo, hi) = split_at::<N, 2>(t);
    (bias::<N>(lo), hi)
}

/// a + b: (pattern, ok) with ok = (hi == 1) and the pattern zeroed on
/// ok = false. Constraints: s_add_parts, one is_zero (eq) and a select.
fn s_add<let N: u32>(pa: Field, pb: Field) -> (Field, bool) {
    let (p, hi) = s_add_parts::<N>(pa, pb);
    let ok = eq(hi, 1);
    (select_field(ok, p, 0), ok)
}

/// a - b: as s_add on s_sub_parts.
fn s_sub<let N: u32>(pa: Field, pb: Field) -> (Field, bool) {
    let (p, hi) = s_sub_parts::<N>(pa, pb);
    let ok = eq(hi, 1);
    (select_field(ok, p, 0), ok)
}

/// The saturated pattern for hi from s_add_parts or s_sub_parts: the
/// wrapped pattern when hi = 1, MIN (pattern H) when hi = 0, MAX
/// (pattern H - 1) when hi = 2. Constraints: two is_zero and selects.
fn saturate<let N: u32>(p: Field, hi: Field) -> Field {
    let h = two_pow::<N - 1>();
    select_field(eq(hi, 1), p, select_field(is_zero(hi), h, h - 1))
}

/// saturating a + b: s_add_parts and saturate. Total.
fn s_sat_add<let N: u32>(pa: Field, pb: Field) -> Field {
    let (p, hi) = s_add_parts::<N>(pa, pb);
    saturate::<N>(p, hi)
}

/// saturating a - b: s_sub_parts and saturate. Total.
fn s_sat_sub<let N: u32>(pa: Field, pb: Field) -> Field {
    let (p, hi) = s_sub_parts::<N>(pa, pb);
    saturate::<N>(p, hi)
}

/// Signed multiplication before the failure select: (wrapped pattern,
/// fits, negative). Via sign and magnitude: M = m_a*m_b with magnitudes
/// at most H; core::mul_split::<N> gives M = lo + hi*2^N. The result fits
/// iff hi == 0 and lo <= H - 1 (positive result) or lo <= H (negative
/// result), i.e. lo < H + neg: one lt_bounded::<N> (H + 1 < 2^N for
/// N >= 2). The wrapped pattern is lo or its negation mod 2^N.
/// Constraints: two lt_bounded (signs), mul_split, is_zero(hi), one
/// lt_bounded (bound), is_zero (negation). All hint-satisfiable and
/// determined.
fn s_mul_parts<let N: u32>(pa: Field, pb: Field) -> (Field, bool, bool) {
    let (sa, ma) = sign_mag::<N>(pa);
    let (sb, mb) = sign_mag::<N>(pb);
    let neg = sa ^ sb;
    let (lo, hi) = mul_split::<N>(ma, mb);
    let fits = is_zero(hi) & lt_bounded::<N>(lo, two_pow::<N - 1>() + (neg as Field));
    (signed_pattern::<N>(neg, lo), fits, neg)
}

/// a * b: (pattern, fits), the pattern zeroed when it does not fit.
fn s_mul<let N: u32>(pa: Field, pb: Field) -> (Field, bool) {
    let (p, fits, _) = s_mul_parts::<N>(pa, pb);
    (select_field(fits, p, 0), fits)
}

/// saturating a * b: the product when it fits, else MIN for a negative
/// exact product and MAX for a positive one (an overflowing product is
/// nonzero, so its sign is the sign flag). Total.
fn s_sat_mul<let N: u32>(pa: Field, pb: Field) -> Field {
    let (p, fits, neg) = s_mul_parts::<N>(pa, pb);
    let h = two_pow::<N - 1>();
    select_field(fits, p, select_field(neg, h, h - 1))
}

/// Shared division core: (sa, sb, qm, rm, mb, nz) with the signs and
/// magnitudes of both operands, nz = divisor nonzero, and (qm, rm) the
/// Euclidean division of the magnitudes, |a| = qm*|b| + rm. When the
/// divisor is zero, the divisor magnitude is selected to 1 and the
/// dividend magnitude to 0 BEFORE core::div_split runs, so the hint
/// cannot divide by zero and qm = rm = 0. Magnitudes lie in [0, H], below
/// 2^N, which with the select discharges div_split's preconditions.
/// Constraints: two lt_bounded, is_zero(mb), two selects, div_split
/// (RANGE qm, rm to N bits, reconstruction, RANGE d - rm - 1). All
/// hint-satisfiable; determined.
fn s_div_parts<let N: u32>(pa: Field, pb: Field) -> (bool, bool, Field, Field, Field, bool) {
    let (sa, ma) = sign_mag::<N>(pa);
    let (sb, mb) = sign_mag::<N>(pb);
    let nz = !is_zero(mb);
    let (qm, rm) = div_split::<N>(select_field(nz, ma, 0), select_field(nz, mb, 1));
    (sa, sb, qm, rm, mb, nz)
}

/// A signed quotient of sign neg and magnitude m <= H: (pattern, ok)
/// with ok = nz and the quotient representable, zeroed on ok = false.
/// The only magnitude past the range is H with a positive sign (from
/// MIN / -1), detected by eq(m, H). Constraints: eq, is_zero (negation),
/// selects.
fn quotient<let N: u32>(neg: bool, m: Field, nz: bool) -> (Field, bool) {
    let ok = nz & !(eq(m, two_pow::<N - 1>()) & !neg);
    (select_field(ok, signed_pattern::<N>(neg, m), 0), ok)
}

/// Signed division and remainder, rounding toward zero: q has sign
/// sa ^ sb and magnitude qm; r has the dividend's sign and magnitude rm.
/// ok = divisor nonzero and not MIN / -1. On ok = false both are 0: for
/// a zero divisor because the dividend was selected to 0, and for
/// MIN / -1 the remainder is 0 and the quotient is selected to 0.
/// Constraints: s_div_parts, quotient, is_zero (remainder negation).
fn s_divmod<let N: u32>(pa: Field, pb: Field) -> (Field, Field, bool) {
    let (sa, sb, qm, rm, _, nz) = s_div_parts::<N>(pa, pb);
    let (q, ok) = quotient::<N>(sa ^ sb, qm, nz);
    (q, signed_pattern::<N>(sa, rm), ok)
}

/// floor(a / d): the truncated quotient, moved one away from zero when
/// the remainder is nonzero and the quotient is negative, so its
/// magnitude is qm + (rm != 0 & neg). That magnitude is at most H: a
/// nonzero remainder needs |d| >= 2, so qm <= H/2. The only
/// unrepresentable case is MIN / -1, as for truncation. Constraints:
/// s_div_parts, is_zero(rm), quotient.
fn s_div_floor<let N: u32>(pa: Field, pb: Field) -> (Field, bool) {
    let (sa, sb, qm, rm, _, nz) = s_div_parts::<N>(pa, pb);
    let neg = sa ^ sb;
    let adj = !is_zero(rm) & neg;
    quotient::<N>(neg, qm + (adj as Field), nz)
}

/// The Euclidean pair (q, r, ok) with a = q*d + r and 0 <= r < |d|. The
/// truncated remainder is negative exactly when a < 0 and rm != 0
/// (adj); then r = |d| - rm and q moves one away from zero: magnitude
/// qm + 1 with the truncated sign (for d > 0, q_t - 1 with q_t <= 0; for
/// d < 0, q_t + 1 with q_t >= 0). Otherwise r = rm and q = q_t. The
/// magnitude stays at most H/2 + 1 when adj (|d| >= 2), so the only
/// unrepresentable case is MIN / -1. r lies in [0, |d|) with |d| <= H,
/// a non-negative pattern below H. On ok = false both are 0 (r is 0
/// there without a select: rm = 0 and adj is false).
/// Constraints: s_div_parts, is_zero(rm), quotient, a select for r.
fn s_div_euclid<let N: u32>(pa: Field, pb: Field) -> (Field, Field, bool) {
    let (sa, sb, qm, rm, mb, nz) = s_div_parts::<N>(pa, pb);
    let adj = sa & !is_zero(rm);
    let (q, ok) = quotient::<N>(sa ^ sb, qm + (adj as Field), nz);
    (q, select_field(adj, mb - rm, rm), ok)
}

/// Signed negation: pattern (2^N - p) mod 2^N; ok = p != H (not MIN), and
/// 0 on ok = false. Constraints: two is_zero gadgets and a select.
/// Determined.
fn s_neg<let N: u32>(p: Field) -> (Field, bool) {
    let ok = !eq(p, two_pow::<N - 1>());
    (select_field(ok, neg_pattern::<N>(p), 0), ok)
}

/// Absolute value: the magnitude; ok = p != H (MIN's magnitude H is not
/// representable), and 0 on ok = false. Constraints: lt_bounded, is_zero
/// and a select. Determined.
fn s_abs<let N: u32>(p: Field) -> (Field, bool) {
    let (_, m) = sign_mag::<N>(p);
    let ok = !eq(p, two_pow::<N - 1>());
    (select_field(ok, m, 0), ok)
}

/// signum: the pattern of -1 (2^N - 1) for a negative pattern, else
/// 1 - is_zero(p). Constraints: lt_bounded (sign) and is_zero. Total.
fn s_signum<let N: u32>(p: Field) -> Field {
    let neg = !lt_bounded::<N>(p, two_pow::<N - 1>());
    select_field(neg, two_pow::<N>() - 1, 1 - (is_zero(p) as Field))
}

/// Fused a*b / d on signed values, truncating toward zero:
/// (q, r, ok) with q = trunc(a*b / d), r = a*b - q*d (the sign of a*b),
/// ok = d != 0 and q representable. The exact product never overflows.
/// Via magnitudes: core::mul_div_split::<N, N> on |a|, |b| (at most H,
/// below 2^N) and |d| selected to 1 when zero, with |a| selected to 0
/// then, BEFORE the hint runs (so qm = rm = 0 on d = 0):
/// qm = floor(|a||b| / |d|), rm = |a||b| mod |d|, and fits = qm < 2^N.
/// The quotient's sign is sa ^ sb ^ sd and it is representable iff
/// fits and qm < H + neg (one lt_bounded::<N>: qm is range-checked to N
/// bits and H + 1 < 2^N). The remainder's magnitude is below |d| <= H,
/// always representable, with sign sa ^ sb. Both zeroed on ok = false.
/// Constraints: three lt_bounded (signs), is_zero(|d|), two selects,
/// mul_div_split (core::constrain_mul_div: RANGE q_lo and q_hi to N bits,
/// is_zero(q_hi), RANGE rm and |d| - rm - 1 to N bits, the identity),
/// lt_bounded (bound), two is_zero (negations), two selects. The
/// preconditions hold (operands below 2^N, divisor in [1, 2^N), N <= 84),
/// so every assert is hint-satisfiable; all outputs determined.
fn s_mul_div_parts<let N: u32>(
    pa: Field,
    pb: Field,
    pd: Field,
) -> (bool, Field, Field, bool, bool) {
    let (sa, ma) = sign_mag::<N>(pa);
    let (sb, mb) = sign_mag::<N>(pb);
    let (sd, md) = sign_mag::<N>(pd);
    let nz = !is_zero(md);
    let (qm, rm, fits) =
        mul_div_split::<N, N>(select_field(nz, ma, 0), mb, select_field(nz, md, 1));
    (sa ^ sb ^ sd, qm, rm, sa ^ sb, nz & fits)
}

/// See s_mul_div_parts.
fn s_mul_div<let N: u32>(pa: Field, pb: Field, pd: Field) -> (Field, Field, bool) {
    let (neg_q, qm, rm, neg_r, ok_in) = s_mul_div_parts::<N>(pa, pb, pd);
    let ok = ok_in & lt_bounded::<N>(qm, two_pow::<N - 1>() + (neg_q as Field));
    (
        select_field(ok, signed_pattern::<N>(neg_q, qm), 0),
        select_field(ok, signed_pattern::<N>(neg_r, rm), 0), ok,
    )
}

/// ceil(a*b / d) on signed values: (c, ok). From s_mul_div_parts: a
/// nonzero remainder means the exact quotient is not an integer, and
/// ceil moves the truncated one up exactly when the exact quotient is
/// positive (sign flag false; a nonzero remainder implies a nonzero
/// product, so the flag is the true sign). The magnitude is
/// cm = qm + (rm != 0 & !neg), below 2^N + 1; ok = d != 0, fits, and
/// cm < H + neg, one lt_bounded::<N + 1> (both sides below 2^(N+1)).
/// When neg the increment is 0, so cm = qm < 2^N and the negation is
/// defined; the value is zeroed on ok = false before the cast.
/// Constraints: those of s_mul_div_parts, is_zero(rm), lt_bounded,
/// is_zero (negation), selects. All determined.
fn s_mul_div_ceil<let N: u32>(pa: Field, pb: Field, pd: Field) -> (Field, bool) {
    let (neg, qm, rm, _, ok_in) = s_mul_div_parts::<N>(pa, pb, pd);
    let cm = qm + ((!is_zero(rm) & !neg) as Field);
    let ok = ok_in & lt_bounded::<N + 1>(cm, two_pow::<N - 1>() + (neg as Field));
    (select_field(ok, signed_pattern::<N>(neg, cm), 0), ok)
}

// ---------------------------------------------------------------------
// Facades. pat_iN widens (exact: iN as uN reinterprets, uN as Field is
// exact); convert::cast_iN range-checks a pattern that is already below
// 2^N for every satisfying witness (core::implied_range) and casts back
// exactly.
// ---------------------------------------------------------------------

fn pat_i8(x: i8) -> Field {
    (x as u8) as Field
}
fn pat_i16(x: i16) -> Field {
    (x as u16) as Field
}
fn pat_i32(x: i32) -> Field {
    (x as u32) as Field
}
fn pat_i64(x: i64) -> Field {
    (x as u64) as Field
}

impl TotalArith for i8 {
    fn add_or(self, other: i8) -> (i8, bool) {
        let (p, ok) = s_add::<8>(pat_i8(self), pat_i8(other));
        (cast_i8(p), ok)
    }
    fn sub_or(self, other: i8) -> (i8, bool) {
        let (p, ok) = s_sub::<8>(pat_i8(self), pat_i8(other));
        (cast_i8(p), ok)
    }
    fn mul_or(self, other: i8) -> (i8, bool) {
        let (p, ok) = s_mul::<8>(pat_i8(self), pat_i8(other));
        (cast_i8(p), ok)
    }
    fn div_or(self, other: i8) -> (i8, bool) {
        let (q, _, ok) = s_divmod::<8>(pat_i8(self), pat_i8(other));
        (cast_i8(q), ok)
    }
    fn div_rem_or(self, other: i8) -> (i8, i8, bool) {
        let (q, r, ok) = s_divmod::<8>(pat_i8(self), pat_i8(other));
        (cast_i8(q), cast_i8(r), ok)
    }
    fn mod_or(self, other: i8) -> (i8, bool) {
        let (_, r, ok) = s_divmod::<8>(pat_i8(self), pat_i8(other));
        (cast_i8(r), ok)
    }
}

impl TotalArith for i16 {
    fn add_or(self, other: i16) -> (i16, bool) {
        let (p, ok) = s_add::<16>(pat_i16(self), pat_i16(other));
        (cast_i16(p), ok)
    }
    fn sub_or(self, other: i16) -> (i16, bool) {
        let (p, ok) = s_sub::<16>(pat_i16(self), pat_i16(other));
        (cast_i16(p), ok)
    }
    fn mul_or(self, other: i16) -> (i16, bool) {
        let (p, ok) = s_mul::<16>(pat_i16(self), pat_i16(other));
        (cast_i16(p), ok)
    }
    fn div_or(self, other: i16) -> (i16, bool) {
        let (q, _, ok) = s_divmod::<16>(pat_i16(self), pat_i16(other));
        (cast_i16(q), ok)
    }
    fn div_rem_or(self, other: i16) -> (i16, i16, bool) {
        let (q, r, ok) = s_divmod::<16>(pat_i16(self), pat_i16(other));
        (cast_i16(q), cast_i16(r), ok)
    }
    fn mod_or(self, other: i16) -> (i16, bool) {
        let (_, r, ok) = s_divmod::<16>(pat_i16(self), pat_i16(other));
        (cast_i16(r), ok)
    }
}

impl TotalArith for i32 {
    fn add_or(self, other: i32) -> (i32, bool) {
        let (p, ok) = s_add::<32>(pat_i32(self), pat_i32(other));
        (cast_i32(p), ok)
    }
    fn sub_or(self, other: i32) -> (i32, bool) {
        let (p, ok) = s_sub::<32>(pat_i32(self), pat_i32(other));
        (cast_i32(p), ok)
    }
    fn mul_or(self, other: i32) -> (i32, bool) {
        let (p, ok) = s_mul::<32>(pat_i32(self), pat_i32(other));
        (cast_i32(p), ok)
    }
    fn div_or(self, other: i32) -> (i32, bool) {
        let (q, _, ok) = s_divmod::<32>(pat_i32(self), pat_i32(other));
        (cast_i32(q), ok)
    }
    fn div_rem_or(self, other: i32) -> (i32, i32, bool) {
        let (q, r, ok) = s_divmod::<32>(pat_i32(self), pat_i32(other));
        (cast_i32(q), cast_i32(r), ok)
    }
    fn mod_or(self, other: i32) -> (i32, bool) {
        let (_, r, ok) = s_divmod::<32>(pat_i32(self), pat_i32(other));
        (cast_i32(r), ok)
    }
}

impl TotalArith for i64 {
    fn add_or(self, other: i64) -> (i64, bool) {
        let (p, ok) = s_add::<64>(pat_i64(self), pat_i64(other));
        (cast_i64(p), ok)
    }
    fn sub_or(self, other: i64) -> (i64, bool) {
        let (p, ok) = s_sub::<64>(pat_i64(self), pat_i64(other));
        (cast_i64(p), ok)
    }
    fn mul_or(self, other: i64) -> (i64, bool) {
        let (p, ok) = s_mul::<64>(pat_i64(self), pat_i64(other));
        (cast_i64(p), ok)
    }
    fn div_or(self, other: i64) -> (i64, bool) {
        let (q, _, ok) = s_divmod::<64>(pat_i64(self), pat_i64(other));
        (cast_i64(q), ok)
    }
    fn div_rem_or(self, other: i64) -> (i64, i64, bool) {
        let (q, r, ok) = s_divmod::<64>(pat_i64(self), pat_i64(other));
        (cast_i64(q), cast_i64(r), ok)
    }
    fn mod_or(self, other: i64) -> (i64, bool) {
        let (_, r, ok) = s_divmod::<64>(pat_i64(self), pat_i64(other));
        (cast_i64(r), ok)
    }
}

impl Saturating for i8 {
    fn saturating_add(self, other: i8) -> i8 {
        cast_i8(s_sat_add::<8>(pat_i8(self), pat_i8(other)))
    }
    fn saturating_sub(self, other: i8) -> i8 {
        cast_i8(s_sat_sub::<8>(pat_i8(self), pat_i8(other)))
    }
    fn saturating_mul(self, other: i8) -> i8 {
        cast_i8(s_sat_mul::<8>(pat_i8(self), pat_i8(other)))
    }
}

impl Saturating for i16 {
    fn saturating_add(self, other: i16) -> i16 {
        cast_i16(s_sat_add::<16>(pat_i16(self), pat_i16(other)))
    }
    fn saturating_sub(self, other: i16) -> i16 {
        cast_i16(s_sat_sub::<16>(pat_i16(self), pat_i16(other)))
    }
    fn saturating_mul(self, other: i16) -> i16 {
        cast_i16(s_sat_mul::<16>(pat_i16(self), pat_i16(other)))
    }
}

impl Saturating for i32 {
    fn saturating_add(self, other: i32) -> i32 {
        cast_i32(s_sat_add::<32>(pat_i32(self), pat_i32(other)))
    }
    fn saturating_sub(self, other: i32) -> i32 {
        cast_i32(s_sat_sub::<32>(pat_i32(self), pat_i32(other)))
    }
    fn saturating_mul(self, other: i32) -> i32 {
        cast_i32(s_sat_mul::<32>(pat_i32(self), pat_i32(other)))
    }
}

impl Saturating for i64 {
    fn saturating_add(self, other: i64) -> i64 {
        cast_i64(s_sat_add::<64>(pat_i64(self), pat_i64(other)))
    }
    fn saturating_sub(self, other: i64) -> i64 {
        cast_i64(s_sat_sub::<64>(pat_i64(self), pat_i64(other)))
    }
    fn saturating_mul(self, other: i64) -> i64 {
        cast_i64(s_sat_mul::<64>(pat_i64(self), pat_i64(other)))
    }
}

impl TotalSigned for i8 {
    fn neg_or(self) -> (i8, bool) {
        let (p, ok) = s_neg::<8>(pat_i8(self));
        (cast_i8(p), ok)
    }
    fn abs_or(self) -> (i8, bool) {
        let (p, ok) = s_abs::<8>(pat_i8(self));
        (cast_i8(p), ok)
    }
    fn signum(self) -> i8 {
        cast_i8(s_signum::<8>(pat_i8(self)))
    }
    fn div_floor_or(self, other: i8) -> (i8, bool) {
        let (q, ok) = s_div_floor::<8>(pat_i8(self), pat_i8(other));
        (cast_i8(q), ok)
    }
    fn div_euclid_or(self, other: i8) -> (i8, bool) {
        let (q, _, ok) = s_div_euclid::<8>(pat_i8(self), pat_i8(other));
        (cast_i8(q), ok)
    }
    fn rem_euclid_or(self, other: i8) -> (i8, bool) {
        let (_, r, ok) = s_div_euclid::<8>(pat_i8(self), pat_i8(other));
        (cast_i8(r), ok)
    }
}

impl TotalSigned for i16 {
    fn neg_or(self) -> (i16, bool) {
        let (p, ok) = s_neg::<16>(pat_i16(self));
        (cast_i16(p), ok)
    }
    fn abs_or(self) -> (i16, bool) {
        let (p, ok) = s_abs::<16>(pat_i16(self));
        (cast_i16(p), ok)
    }
    fn signum(self) -> i16 {
        cast_i16(s_signum::<16>(pat_i16(self)))
    }
    fn div_floor_or(self, other: i16) -> (i16, bool) {
        let (q, ok) = s_div_floor::<16>(pat_i16(self), pat_i16(other));
        (cast_i16(q), ok)
    }
    fn div_euclid_or(self, other: i16) -> (i16, bool) {
        let (q, _, ok) = s_div_euclid::<16>(pat_i16(self), pat_i16(other));
        (cast_i16(q), ok)
    }
    fn rem_euclid_or(self, other: i16) -> (i16, bool) {
        let (_, r, ok) = s_div_euclid::<16>(pat_i16(self), pat_i16(other));
        (cast_i16(r), ok)
    }
}

impl TotalSigned for i32 {
    fn neg_or(self) -> (i32, bool) {
        let (p, ok) = s_neg::<32>(pat_i32(self));
        (cast_i32(p), ok)
    }
    fn abs_or(self) -> (i32, bool) {
        let (p, ok) = s_abs::<32>(pat_i32(self));
        (cast_i32(p), ok)
    }
    fn signum(self) -> i32 {
        cast_i32(s_signum::<32>(pat_i32(self)))
    }
    fn div_floor_or(self, other: i32) -> (i32, bool) {
        let (q, ok) = s_div_floor::<32>(pat_i32(self), pat_i32(other));
        (cast_i32(q), ok)
    }
    fn div_euclid_or(self, other: i32) -> (i32, bool) {
        let (q, _, ok) = s_div_euclid::<32>(pat_i32(self), pat_i32(other));
        (cast_i32(q), ok)
    }
    fn rem_euclid_or(self, other: i32) -> (i32, bool) {
        let (_, r, ok) = s_div_euclid::<32>(pat_i32(self), pat_i32(other));
        (cast_i32(r), ok)
    }
}

impl TotalSigned for i64 {
    fn neg_or(self) -> (i64, bool) {
        let (p, ok) = s_neg::<64>(pat_i64(self));
        (cast_i64(p), ok)
    }
    fn abs_or(self) -> (i64, bool) {
        let (p, ok) = s_abs::<64>(pat_i64(self));
        (cast_i64(p), ok)
    }
    fn signum(self) -> i64 {
        cast_i64(s_signum::<64>(pat_i64(self)))
    }
    fn div_floor_or(self, other: i64) -> (i64, bool) {
        let (q, ok) = s_div_floor::<64>(pat_i64(self), pat_i64(other));
        (cast_i64(q), ok)
    }
    fn div_euclid_or(self, other: i64) -> (i64, bool) {
        let (q, _, ok) = s_div_euclid::<64>(pat_i64(self), pat_i64(other));
        (cast_i64(q), ok)
    }
    fn rem_euclid_or(self, other: i64) -> (i64, bool) {
        let (_, r, ok) = s_div_euclid::<64>(pat_i64(self), pat_i64(other));
        (cast_i64(r), ok)
    }
}

impl TotalMulDiv for i8 {
    fn mul_div_or(self, b: i8, d: i8) -> (i8, i8, bool) {
        let (q, r, ok) = s_mul_div::<8>(pat_i8(self), pat_i8(b), pat_i8(d));
        (cast_i8(q), cast_i8(r), ok)
    }
    fn mul_div_ceil_or(self, b: i8, d: i8) -> (i8, bool) {
        let (c, ok) = s_mul_div_ceil::<8>(pat_i8(self), pat_i8(b), pat_i8(d));
        (cast_i8(c), ok)
    }
}

impl TotalMulDiv for i16 {
    fn mul_div_or(self, b: i16, d: i16) -> (i16, i16, bool) {
        let (q, r, ok) = s_mul_div::<16>(pat_i16(self), pat_i16(b), pat_i16(d));
        (cast_i16(q), cast_i16(r), ok)
    }
    fn mul_div_ceil_or(self, b: i16, d: i16) -> (i16, bool) {
        let (c, ok) = s_mul_div_ceil::<16>(pat_i16(self), pat_i16(b), pat_i16(d));
        (cast_i16(c), ok)
    }
}

impl TotalMulDiv for i32 {
    fn mul_div_or(self, b: i32, d: i32) -> (i32, i32, bool) {
        let (q, r, ok) = s_mul_div::<32>(pat_i32(self), pat_i32(b), pat_i32(d));
        (cast_i32(q), cast_i32(r), ok)
    }
    fn mul_div_ceil_or(self, b: i32, d: i32) -> (i32, bool) {
        let (c, ok) = s_mul_div_ceil::<32>(pat_i32(self), pat_i32(b), pat_i32(d));
        (cast_i32(c), ok)
    }
}

impl TotalMulDiv for i64 {
    fn mul_div_or(self, b: i64, d: i64) -> (i64, i64, bool) {
        let (q, r, ok) = s_mul_div::<64>(pat_i64(self), pat_i64(b), pat_i64(d));
        (cast_i64(q), cast_i64(r), ok)
    }
    fn mul_div_ceil_or(self, b: i64, d: i64) -> (i64, bool) {
        let (c, ok) = s_mul_div_ceil::<64>(pat_i64(self), pat_i64(b), pat_i64(d));
        (cast_i64(c), ok)
    }
}

/// |x| as the unsigned type of the same width. Total with no flag: the
/// magnitude is at most 2^(N-1), so it always fits. Constraint:
/// lt_bounded (sign) and the implied range check before the exact cast.
pub fn unsigned_abs_i8(x: i8) -> u8 {
    let (_, m) = sign_mag::<8>(pat_i8(x));
    cast_u8(m)
}

/// See unsigned_abs_i8.
pub fn unsigned_abs_i16(x: i16) -> u16 {
    let (_, m) = sign_mag::<16>(pat_i16(x));
    cast_u16(m)
}

/// See unsigned_abs_i8.
pub fn unsigned_abs_i32(x: i32) -> u32 {
    let (_, m) = sign_mag::<32>(pat_i32(x));
    cast_u32(m)
}

/// See unsigned_abs_i8.
pub fn unsigned_abs_i64(x: i64) -> u64 {
    let (_, m) = sign_mag::<64>(pat_i64(x));
    cast_u64(m)
}

mod tests {
    use crate::arith::{Saturating, TotalArith, TotalMulDiv};
    use crate::core::two_pow;
    use crate::test_support::witnesses;
    use super::{TotalSigned, unsigned_abs_i16, unsigned_abs_i32, unsigned_abs_i64, unsigned_abs_i8};
    use std::ops::{WrappingAdd, WrappingMul, WrappingSub};

    /// Real value of a signed integer as a Field (negative values wrap
    /// mod p), for the reference checks.
    trait Real {
        fn real(self) -> Field;
    }
    impl Real for i8 {
        fn real(self) -> Field {
            let p = (self as u8) as Field;
            if self < 0 {
                p - 256
            } else {
                p
            }
        }
    }
    impl Real for i16 {
        fn real(self) -> Field {
            let p = (self as u16) as Field;
            if self < 0 {
                p - 65536
            } else {
                p
            }
        }
    }
    impl Real for i32 {
        fn real(self) -> Field {
            let p = (self as u32) as Field;
            if self < 0 {
                p - 0x100000000
            } else {
                p
            }
        }
    }
    impl Real for i64 {
        fn real(self) -> Field {
            let p = (self as u64) as Field;
            if self < 0 {
                p - 0x10000000000000000
            } else {
                p
            }
        }
    }

    /// The real result s is representable on N bits iff s + H lies in
    /// [0, 2^N); negative s + H wraps to near p and fails the lt.
    fn fits<let N: u32>(s: Field) -> bool {
        (s + two_pow::<N - 1>()).lt(two_pow::<N>())
    }

    /// Check every pair from a boundary set against the native operators
    /// where they succeed and against the documented values where they
    /// would fail.
    fn check_signed<T, let N: u32, let K: u32>(vals: [T; K], min: T, minus_one: T)
    where
        T: TotalArith + TotalSigned + Saturating + Real + WrappingAdd + WrappingSub + WrappingMul + Eq + Ord + std::ops::Add + std::ops::Sub + std::ops::Mul + std::ops::Div + std::ops::Rem + std::ops::Neg + std::default::Default,
    {
        let zero: T = std::default::Default::default();
        let one = -minus_one;
        let max = min.wrapping_sub(one);
        for i in 0..K {
            let a = vals[i];
            let not_min = a != min;
            let neg_a = if not_min { -a } else { zero };
            assert(a.neg_or() == (neg_a, not_min));
            assert(a.abs_or() == (if a < zero { neg_a } else { a }, not_min));
            let sig = if a < zero {
                minus_one
            } else if a == zero {
                zero
            } else {
                one
            };
            assert(a.signum() == sig);
            for j in 0..K {
                let b = vals[j];
                let add_ok = fits::<N>(a.real() + b.real());
                let sub_ok = fits::<N>(a.real() - b.real());
                let mul_ok = fits::<N>(a.real() * b.real());
                assert(a.add_or(b) == (if add_ok { a + b } else { zero }, add_ok));
                assert(a.sub_or(b) == (if sub_ok { a - b } else { zero }, sub_ok));
                assert(a.mul_or(b) == (if mul_ok { a * b } else { zero }, mul_ok));
                // an overflowing sum has the sign of a; a difference the
                // sign of a; a product the sign of a*b
                let add_sat = if add_ok {
                    a + b
                } else if a < zero {
                    min
                } else {
                    max
                };
                let sub_sat = if sub_ok {
                    a - b
                } else if a < zero {
                    min
                } else {
                    max
                };
                let mul_sat = if mul_ok {
                    a * b
                } else if (a < zero) != (b < zero) {
                    min
                } else {
                    max
                };
                assert(a.saturating_add(b) == add_sat);
                assert(a.saturating_sub(b) == sub_sat);
                assert(a.saturating_mul(b) == mul_sat);
                let div_ok = (b != zero) & !((a == min) & (b == minus_one));
                let d = if div_ok { b } else { minus_one };
                let n = if div_ok { a } else { zero };
                let q = n / d;
                let r = n % d;
                assert(a.div_or(b) == (q, div_ok));
                assert(a.mod_or(b) == (r, div_ok));
                assert(a.div_rem_or(b) == (q, r, div_ok));
                // r has the sign of n; a nonzero remainder needs |d| >= 2,
                // so q +- 1 cannot overflow
                let floor = if (r != zero) & ((r < zero) != (d < zero)) {
                    q + minus_one
                } else {
                    q
                };
                let (eq_, er) = if r < zero {
                    if d > zero {
                        (q + minus_one, r + d)
                    } else {
                        (q + one, r - d)
                    }
                } else {
                    (q, r)
                };
                assert(a.div_floor_or(b) == (floor, div_ok));
                assert(a.div_euclid_or(b) == (eq_, div_ok));
                assert(a.rem_euclid_or(b) == (er, div_ok));
            }
        }
    }

    #[test]
    fn sign_cast_semantics() {
        // iN as uN as Field is the two's complement pattern; Field as uN
        // as iN reverses it. Typed bindings matter: in `-1 as i8` the
        // literal is the Field p - 1 and the cast truncates it to 0 (the
        // compiler warns about this form).
        let m1: i8 = -1;
        let min8: i8 = -128;
        let max8: i8 = 127;
        let m1_64: i64 = -1;
        let min64: i64 = -9223372036854775808;
        assert_eq((m1 as u8) as Field, 255);
        assert_eq((min8 as u8) as Field, 128);
        assert_eq((max8 as u8) as Field, 127);
        assert_eq((m1_64 as u64) as Field, 0xffffffffffffffff);
        assert_eq((min64 as u64) as Field, 0x8000000000000000);
        let f: Field = 255;
        assert_eq((f as u8) as i8, -1);
        let g: Field = 128;
        assert_eq((g as u8) as i8, -128);
    }

    global I8_CORNERS: [i8; 9] = [-128, -127, -2, -1, 0, 1, 2, 126, 127];
    global I16_CORNERS: [i16; 9] = [-32768, -32767, -2, -1, 0, 1, 2, 32766, 32767];
    global I32_CORNERS: [i32; 9] =
        [-2147483648, -2147483647, -2, -1, 0, 1, 2, 2147483646, 2147483647];
    global I64_CORNERS: [i64; 11] = [
        -9223372036854775808,
        -9223372036854775807,
        -4294967296,
        -2,
        -1,
        0,
        1,
        2,
        4294967296,
        9223372036854775806,
        9223372036854775807,
    ];

    #[test]
    fn i8_all_corners() {
        check_signed::<i8, 8, 9>(I8_CORNERS, -128, -1);
    }

    #[test]
    fn i8_exhaustive_small() {
        // every pair from [-8, 7] plus the bounds, a denser sweep
        let mut vals: [i8; 18] = [0; 18];
        for k in 0..16 {
            vals[k] = (k as i8) - 8;
        }
        vals[16] = -128;
        vals[17] = 127;
        check_signed::<i8, 8, 18>(vals, -128, -1);
    }

    #[test]
    fn i16_all_corners() {
        check_signed::<i16, 16, 9>(I16_CORNERS, -32768, -1);
    }

    #[test]
    fn i32_all_corners() {
        check_signed::<i32, 32, 9>(I32_CORNERS, -2147483648, -1);
    }

    #[test]
    fn i64_all_corners() {
        check_signed::<i64, 64, 11>(I64_CORNERS, -9223372036854775808, -1);
    }

    // The same checks with every operand a witness, so the gadgets'
    // constraints (bias, sign_mag, the splits, cast_iN) are solved by the
    // ACVM instead of being folded at compile time.

    #[test]
    fn i8_corners_on_witnesses() {
        check_signed::<i8, 8, 9>(witnesses(I8_CORNERS), -128, -1);
    }

    #[test]
    fn i16_corners_on_witnesses() {
        check_signed::<i16, 16, 9>(witnesses(I16_CORNERS), -32768, -1);
    }

    #[test]
    fn i32_corners_on_witnesses() {
        check_signed::<i32, 32, 9>(witnesses(I32_CORNERS), -2147483648, -1);
    }

    #[test]
    fn i64_corners_on_witnesses() {
        check_signed::<i64, 64, 11>(witnesses(I64_CORNERS), -9223372036854775808, -1);
    }

    #[test]
    fn rounding_toward_zero() {
        let (m7, p7, m2, p2, min, m1, zero, one): (i8, i8, i8, i8, i8, i8, i8, i8) =
            (-7, 7, -2, 2, -128, -1, 0, 1);
        assert_eq(m7.div_or(p2), (-3, true));
        assert_eq(m7.mod_or(p2), (-1, true));
        assert_eq(p7.div_or(m2), (-3, true));
        assert_eq(p7.mod_or(m2), (1, true));
        assert_eq(m7.div_or(m2), (3, true));
        assert_eq(m7.mod_or(m2), (-1, true));
        assert_eq(min.div_or(m1), (0, false));
        assert_eq(min.mod_or(m1), (0, false));
        assert_eq(min.div_or(one), (-128, true));
        assert_eq(min.div_or(zero), (0, false));
        assert_eq(p7.mod_or(zero), (0, false));
    }

    #[test]
    fn floor_and_euclid() {
        let (m7, p7, m2, p2, min, m1, zero): (i8, i8, i8, i8, i8, i8, i8) =
            (-7, 7, -2, 2, -128, -1, 0);
        assert_eq(m7.div_floor_or(p2), (-4, true));
        assert_eq(p7.div_floor_or(m2), (-4, true));
        assert_eq(m7.div_floor_or(m2), (3, true));
        assert_eq(p7.div_floor_or(p2), (3, true));
        assert_eq(m7.div_euclid_or(p2), (-4, true));
        assert_eq(m7.rem_euclid_or(p2), (1, true));
        assert_eq(p7.div_euclid_or(m2), (-3, true));
        assert_eq(p7.rem_euclid_or(m2), (1, true));
        assert_eq(m7.div_euclid_or(m2), (4, true));
        assert_eq(m7.rem_euclid_or(m2), (1, true));
        assert_eq(min.div_floor_or(m1), (0, false));
        assert_eq(min.div_euclid_or(m1), (0, false));
        assert_eq(min.rem_euclid_or(m1), (0, false));
        assert_eq(p7.div_floor_or(zero), (0, false));
        assert_eq(p7.rem_euclid_or(zero), (0, false));
        // MIN by MIN and by MAX
        let max: i8 = 127;
        assert_eq(min.div_floor_or(min), (1, true));
        assert_eq(min.div_euclid_or(max), (-2, true));
        assert_eq(min.rem_euclid_or(max), (126, true));
        assert_eq(min.rem_euclid_or(min), (0, true));
        let max64: i64 = 9223372036854775807;
        let min64: i64 = -9223372036854775808;
        assert_eq(min64.rem_euclid_or(max64), (9223372036854775806, true));
        assert_eq(min64.div_floor_or(2), (-4611686018427387904, true));
    }

    #[test]
    fn mul_bounds_are_asymmetric() {
        // -2^(N-1) is reachable, +2^(N-1) is not
        let (m64, p64, m2, p2, min, m1, zero, one): (i8, i8, i8, i8, i8, i8, i8, i8) =
            (-64, 64, -2, 2, -128, -1, 0, 1);
        assert_eq(m64.mul_or(p2), (-128, true));
        assert_eq(p64.mul_or(m2), (-128, true));
        assert_eq(p64.mul_or(p2), (0, false));
        assert_eq(m64.mul_or(m2), (0, false));
        assert_eq(min.mul_or(one), (-128, true));
        assert_eq(min.mul_or(m1), (0, false));
        assert_eq(m1.mul_or(m1), (1, true));
        assert_eq(m1.mul_or(zero), (0, true));
        assert_eq(p64.saturating_mul(p2), 127);
        assert_eq(m64.saturating_mul(m2), 127);
        assert_eq(min.saturating_mul(m1), 127);
        assert_eq(p64.saturating_mul(m2), -128);
        assert_eq(min.saturating_mul(p2), -128);
        let (min32, m1_32): (i32, i32) = (-2147483648, -1);
        assert_eq(min32.mul_or(m1_32), (0, false));
        let (a64, b64, c64): (i64, i64, i64) = (-4294967296, 2147483648, 4294967296);
        assert_eq(a64.mul_or(b64), (-9223372036854775808, true));
        assert_eq(c64.mul_or(b64), (0, false));
        assert_eq(c64.saturating_mul(b64), 9223372036854775807);
    }

    #[test]
    fn saturating_add_sub_edges() {
        let (min, max, m1, one): (i8, i8, i8, i8) = (-128, 127, -1, 1);
        assert_eq(max.saturating_add(one), 127);
        assert_eq(min.saturating_add(m1), -128);
        assert_eq(min.saturating_add(max), -1);
        assert_eq(min.saturating_sub(one), -128);
        assert_eq(max.saturating_sub(m1), 127);
        assert_eq(m1.saturating_sub(max), -128);
        assert_eq(min.saturating_sub(min), 0);
        let (min64, max64): (i64, i64) = (-9223372036854775808, 9223372036854775807);
        assert_eq(max64.saturating_add(max64), max64);
        assert_eq(min64.saturating_sub(max64), min64);
        assert_eq(max64.saturating_sub(min64), max64);
    }

    /// i64 value of a narrower signed integer, through its real value.
    fn wide<T>(x: T) -> i64
    where
        T: Real + Ord + std::default::Default,
    {
        let zero: T = std::default::Default::default();
        if x < zero {
            -(((0 - x.real()) as u64) as i64)
        } else {
            (x.real() as u64) as i64
        }
    }

    /// mul_div_or and mul_div_ceil_or against i64 arithmetic for the
    /// narrower types: every pair from vals with every divisor from vals.
    fn check_mul_div<T, let K: u32>(vals: [T; K], min: T, max: T)
    where
        T: TotalMulDiv + Real + Ord + std::default::Default,
    {
        let (lo, hi) = (wide(min), wide(max));
        for i in 0..K {
            for j in 0..K {
                for k in 0..K {
                    let (a, b, d) = (vals[i], vals[j], vals[k]);
                    let dw = wide(d);
                    let p = wide(a) * wide(b);
                    let dd = if dw == 0 { 1 } else { dw };
                    let q = p / dd;
                    let r = p % dd;
                    let ok = (dw != 0) & (q >= lo) & (q <= hi);
                    let (gq, gr, gok) = a.mul_div_or(b, d);
                    assert_eq(gok, ok);
                    if ok {
                        assert_eq((wide(gq), wide(gr)), (q, r));
                    } else {
                        assert_eq((wide(gq), wide(gr)), (0, 0));
                    }
                    // ceil moves up when the exact quotient is positive
                    let up = (r != 0) & ((p < 0) == (dd < 0));
                    let c = if up { q + 1 } else { q };
                    let cok = (dw != 0) & (c >= lo) & (c <= hi);
                    let (gc, gcok) = a.mul_div_ceil_or(b, d);
                    assert_eq(gcok, cok);
                    assert_eq(wide(gc), if cok { c } else { 0 });
                }
            }
        }
    }

    #[test]
    fn mul_div_i8_against_i64() {
        let vals: [i8; 8] = [-128, -127, -3, -1, 0, 1, 7, 127];
        check_mul_div(vals, -128, 127);
    }

    #[test]
    fn mul_div_on_witnesses() {
        let v8: [i8; 5] = [-128, -5, 0, 3, 127];
        check_mul_div(witnesses(v8), -128, 127);
        let v16: [i16; 4] = [-32768, -7, 2, 32767];
        check_mul_div(witnesses(v16), -32768, 32767);
        let v32: [i32; 4] = [-2147483648, -1, 0, 2147483647];
        check_mul_div(witnesses(v32), -2147483648, 2147483647);
    }

    #[test]
    fn mul_div_i64_edges() {
        let min: i64 = -9223372036854775808;
        let max: i64 = 9223372036854775807;
        let ops: [i64; 4] = witnesses([min, max, -1, 0]);
        let (min, max, m1, zero) = (ops[0], ops[1], ops[2], ops[3]);
        // the exact product never overflows
        assert_eq(min.mul_div_or(min, min), (min, 0, true));
        assert_eq(max.mul_div_or(max, max), (max, 0, true));
        assert_eq(min.mul_div_or(max, max), (min, 0, true));
        assert_eq(min.mul_div_or(m1, m1), (min, 0, true));
        // MIN * -1 / 1 = 2^63: one past MAX
        assert_eq(min.mul_div_or(m1, 1), (0, 0, false));
        assert_eq(min.mul_div_or(1, m1), (0, 0, false));
        assert_eq(min.mul_div_or(1, 1), (min, 0, true));
        assert_eq(max.mul_div_or(3, zero), (0, 0, false));
        assert_eq(max.mul_div_ceil_or(3, zero), (0, false));
        // truncation toward zero; ceil toward +infinity
        assert_eq(max.mul_div_or(2, 3), (6148914691236517204, 2, true));
        assert_eq(max.mul_div_ceil_or(2, 3), (6148914691236517205, true));
        assert_eq(max.mul_div_or(m1 * 2, 3), (-6148914691236517204, -2, true));
        assert_eq(max.mul_div_ceil_or(m1 * 2, 3), (-6148914691236517204, true));
        // (MAX - 1)(d + 1) = MAX*d + (MAX - d - 1): for d = 2^62 + 5 the
        // quotient lies in (MAX, MAX + 1), so its ceiling does not fit
        let (b, d): (i64, i64) = (4611686018427387910, 4611686018427387909);
        assert_eq((max - 1).mul_div_or(b, d), (max, 4611686018427387897, true));
        assert_eq((max - 1).mul_div_ceil_or(b, d), (0, false));
        // negated, it lies in (-MAX - 1, -MAX) and ceil rounds toward zero
        assert_eq((min + 2).mul_div_or(b, d), (min + 1, -4611686018427387897, true));
        assert_eq((min + 2).mul_div_ceil_or(b, d), (min + 1, true));
        assert_eq(zero.mul_div_or(min, m1), (0, 0, true));
    }

    #[test]
    fn unsigned_abs_values() {
        assert_eq(unsigned_abs_i8(-128), 128);
        assert_eq(unsigned_abs_i8(127), 127);
        assert_eq(unsigned_abs_i8(-1), 1);
        assert_eq(unsigned_abs_i8(0), 0);
        assert_eq(unsigned_abs_i16(-32768), 32768);
        assert_eq(unsigned_abs_i32(-2147483648), 2147483648);
        assert_eq(unsigned_abs_i64(-9223372036854775808), 9223372036854775808);
        assert_eq(unsigned_abs_i64(9223372036854775807), 9223372036854775807);
    }
}
