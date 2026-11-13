//! Total arithmetic: every entry is defined for every input, and every
//! failure (out-of-range input, overflow, division by zero, non-square)
//! is reported as a determined flag instead of a failing constraint.
//!
//! Value on failure. An entry whose name ends in _or returns its values
//! and then ok. On ok = false every value it returns is 0 (one select
//! per value, or a dividend selected to 0 before the division), so a
//! caller that forgets the flag reads 0, never a plausible wrong number.
//! The wrapping_ and saturating_ entries return what their name says
//! for every in-range input; their ok reports only the input ranges.
//!
//! Three layers.
//!
//! Width-N Field domain. Inputs are arbitrary Field elements. Each input
//! is clamped first (range::clamp_bits_or: the value if it is below 2^N,
//! else 0) and its in-range flag folds into ok, so no gadget
//! precondition leaks to the caller. Families:
//! - add_or/sub_or/mul_or: ok also requires the exact result to fit N
//!   bits.
//! - wrapping_add_or/sub_or/mul_or: value is the result mod 2^N; ok
//!   reports only the input ranges.
//! - saturating_add_or/sub_or/mul_or: value is the result clamped to
//!   [0, 2^N - 1]; ok reports only the input ranges.
//! - div_or, div_rem_or, mod_or, neg_or, wrapping_neg_or, pow_or.
//! - mul_div_or, mul_div_to_or, mul_div_wide_or, mul_div_wide_to_or:
//!   floor(a*b / d) with the double-width product kept exact.
//!
//! The field itself. Native Field + - * and unary minus are total: they
//! are arithmetic definitions that wrap mod p by design, with no
//! constraint an input can falsify. Native Field == is total (it lowers
//! to the inversion gadget, see core::is_zero). Native Field / is NOT
//! total: a / b lowers to a hinted inverse w with the constraint
//! b*w == 1, which no witness satisfies when b = 0. Use field_div_or.
//! Also inverse_or, sqrt_or, sqrt_canonical_or. sqrt_or and
//! sqrt_canonical_or are the only entries of this library whose own hint
//! is not co-noir-compatible (core.nr's header has the rule;
//! docs/co-noir.md lists every entry co-noir cannot run).
//!
//! Native unsigned facades. Trait TotalArith (add_or, sub_or, mul_or,
//! div_or, div_rem_or, mod_or), trait Saturating (saturating_add/sub/mul),
//! trait TotalMulDiv (mul_div_or, mul_div_ceil_or) and trait
//! TotalUnsigned (widening_mul, pow_or, isqrt, abs_diff, div_ceil_or)
//! for u8, u16, u32, u64, u128. Native + - * / % on these types are NOT
//! total in constrained code (overflow and division by zero fail an
//! assertion). The facades widen to Field (uN as Field is exact), run a
//! core gadget, and cast back with `as uN` only on a value that carries
//! a range check of at most N bits, so the cast is exact and the
//! compiler emits no truncation for it. A value zeroed on ok = false is
//! zeroed after the cast with `if ok { v } else { 0 }`, which lowers to
//! the arithmetic definition ok*v with no range check. The operands are
//! below 2^N by the type invariant (the compiler range-checks every
//! integer value where it is created), which discharges the core
//! preconditions, so the facades skip the clamp. u128 add and sub are
//! core::add_split and sub_split at N = 128. u128 mul and div cannot use
//! the width-N gadgets, whose field identity would reach p: mul_128_full
//! hints the low half over 64-bit limbs and div_128 hints the quotient
//! limbs, each proved with one carry range (the argument is in
//! constrain_mul_128 and constrain_div_128). The same two gadgets carry
//! the Field-domain mul and div at N = 127 and 128.
//!
//! Native wrapping arithmetic is already total in std: the traits
//! std::ops::{WrappingAdd, WrappingSub, WrappingMul} compute in Field
//! and truncate with a cast (u128 multiplication goes through 64-bit
//! limbs whose only assert is on hinted limbs). This file does not
//! duplicate them; the tests run them at the boundary values.
//!
//! Exact casts on computed values. Where a value is bound below 2^N by
//! earlier constraints but has no range check of its own (a select of
//! two in-range values, a recombination of range-checked limbs),
//! implied_range::<N> range-checks it once before the cast. The check
//! holds for every witness that satisfies the earlier constraints, so it
//! adds no failure source; without it, `as uN` on a Field emits a
//! 254-bit truncation: a hinted split at bit N with range checks on both
//! parts, and a check that the split is canonical (another wide range
//! check and an inversion).
//!
//! Widths, per family:
//! - add_or, sub_or, mul_or and their wrapping_ and saturating_ forms;
//!   div_or, div_rem_or, mod_or: 1 <= N <= 128.
//! - pow_or: 1 <= N <= 128, exponent width 1 <= E <= 126.
//! - wrapping_neg_or, neg_or: 1 <= N <= 127.
//! - mul_div_or, mul_div_to_or: 1 <= N <= 84, quotient width
//!   1 <= M <= 2N.
//! - mul_div_wide_or: 85 <= N <= 128.
//! - mul_div_wide_to_or: 128-bit operands, quotient width 1 <= M <= 253.
//! - Facades: the native types u8, u16, u32, u64, u128.
//! Every public generic entry rejects other widths at compile time with
//! a static_assert naming the entry and its range.

use crate::core::{
    add_split, div_split, implied_range, INV_TWO_POW_128, INV_TWO_POW_64, is_zero, limbs,
    MUL_DIV_MAX_BITS, mul_div_split, MUL_DIV_WIDE_MAX_BITS, mul_div_wide_split, mul_split,
    select_field, split_128_at, split_at, sub_split, two_pow, TWO_POW_128, TWO_POW_64,
    U128_MAX_FIELD,
};
use crate::range::clamp_bits_or;
use std::default::Default;
use std::static_assert;

/// A fixed quadratic non-residue of the bn254 scalar field, used by
/// sqrt_or. 5 is the conventional multiplicative generator of this
/// field, and a generator cannot be a square. The test
/// sqrt_non_residue_is_verified checks Euler's criterion
/// 5^((p-1)/2) == -1 in unconstrained code instead of trusting this.
pub global SQRT_NON_RESIDUE: Field = 5;

// ---------------------------------------------------------------------
// Internal gadgets
// ---------------------------------------------------------------------

/// v when ok, else the zero value of T. On the native integer types the
/// `if` lowers to the arithmetic definition ok*(v - 0) + 0 with no range
/// check: the result is one of two values that already satisfy the
/// type's range.
fn or_zero<T>(ok: bool, v: T) -> T
where
    T: Default,
{
    if ok {
        v
    } else {
        T::default()
    }
}

/// Hint for mul_128: the low 128 bits of a*b, formed from the 64-bit
/// limbs. s = a0*b0 + (a0*b1 + a1*b0)*2^64 is below 2^194 < p for limbs
/// below 2^64, so the Field value is the integer (the Field product a*b
/// itself can wrap mod p, which is why the hint does not use it), and
/// the cast keeps its low 128 bits, which are those of a*b. Field
/// arithmetic and a truncating cast only: trap-free for every argument.
pub(crate) unconstrained fn hint_mul_lo_128(a0: Field, a1: Field, b0: Field, b1: Field) -> Field {
    ((a0 * b0 + (a0 * b1 + a1 * b0) * TWO_POW_64) as u128) as Field
}

/// Constraint half of mul_128, split out so tests can feed wrong hints.
/// For limbs a0, a1, b0, b1 already constrained below 2^64
/// (PRECONDITION) and the hinted low half lo, it emits:
/// 1. RANGE lo to 128 bits.
/// 2. The carry c = (s - lo) / 2^128 with s = a0*b0 + (a0*b1 + a1*b0)*2^64
///    (a linear combination: a field multiple of the constant 1/2^128),
///    and RANGE c to 70 bits (core's width rule).
/// It returns hi = c + a1*b1.
/// Integer identity: a*b = s + a1*b1*2^128, and s < 2^194.
/// Hint-satisfiable: the honest lo = s mod 2^128 passes 1, and then
/// c = floor(s / 2^128) < 2^66 passes 2.
/// Determined: c*2^128 = s - lo holds in the field with c*2^128 in
/// [0, 2^198) and s - lo in (-2^128, 2^194), so the two sides differ by
/// less than 2^199 < p and the equality is an integer one. With
/// 0 <= lo < 2^128 that makes (lo, c) the Euclidean split of s by 2^128,
/// so lo = a*b mod 2^128 and hi = c + a1*b1 = floor(a*b / 2^128), an
/// integer below 2^128 whose Field value is exact. Load-bearing: without
/// 2, lo + 1 passes with a non-integer c; without 1, lo + 2^128 passes
/// with c - 1 whenever c >= 1.
pub(crate) fn constrain_mul_128(a0: Field, a1: Field, b0: Field, b1: Field, lo: Field) -> Field {
    lo.assert_max_bit_size::<128>();
    let c = (a0 * b0 + (a0 * b1 + a1 * b0) * TWO_POW_64 - lo) * INV_TWO_POW_128;
    c.assert_max_bit_size::<70>();
    c + a1 * b1
}

/// (a*b mod 2^128, floor(a*b / 2^128)) for a, b < 2^128 (PRECONDITION).
/// Constraints: core::split_128_at::<64> on a and b (64-bit RANGEs on the
/// limbs and the reconstructions, hint-satisfiable under the
/// precondition) and constrain_mul_128 (the range-checked low half and
/// one carry). The low half carries its own 128-bit RANGE, so a caller's
/// `as u128` on it is exact; the high half is bound below 2^128 by the
/// argument in constrain_mul_128 but has no RANGE of its own.
/// Determined: the limbs, lo and hi are (constrain_mul_128).
pub(crate) fn mul_128_full(a: Field, b: Field) -> (Field, Field) {
    let (a0, a1) = split_128_at::<64>(a);
    let (b0, b1) = split_128_at::<64>(b);
    // Safety: constrain_mul_128 pins lo to a*b mod 2^128 (its range and
    // the 70-bit carry).
    let lo = unsafe { hint_mul_lo_128(a0, a1, b0, b1) };
    let hi = constrain_mul_128(a0, a1, b0, b1, lo);
    (lo, hi)
}

/// (a*b) mod 2^128 and whether the exact product fits 128 bits, for
/// a, b < 2^128 (PRECONDITION): mul_128_full and is_zero on the high
/// half (fits iff floor(a*b / 2^128) = 0).
fn mul_128(a: Field, b: Field) -> (Field, bool) {
    let (lo, hi) = mul_128_full(a, b);
    (lo, is_zero(hi))
}

/// (a*b mod 2^N, floor(a*b / 2^N)) for a, b < 2^N (PRECONDITION),
/// 1 <= N <= 128. The low part is range-checked to N bits in every
/// layout; the high part is below 2^N.
/// - N <= 126: core::mul_split (two N-bit RANGEs and a*b == lo + hi*2^N,
///   no wrap since the product is below 2^252).
/// - N = 128: mul_128_full.
/// - N = 127: mul_128_full, then core::split_128_at::<127> of its low
///   half (RANGE 127 and 1 on the parts, hint-satisfiable because the
///   low half is below 2^128) into (low, top); the high part is
///   2*hi + top, below 2^127 because a*b < 2^254.
/// All hint-satisfiable under the precondition; the outputs are
/// determined (each gadget's argument).
fn mul_full<let N: u32>(a: Field, b: Field) -> (Field, Field) {
    if N <= 126 {
        mul_split::<N>(a, b)
    } else {
        let (lo, hi) = mul_128_full(a, b);
        if N == 128 {
            (lo, hi)
        } else {
            let (low, top) = split_128_at::<127>(lo);
            (low, hi * 2 + top)
        }
    }
}

/// Hint for div_128: (q mod 2^64, q >> 64, r) for the u128 quotient
/// q = a / b1 and r = a mod b1 of the truncated operands. A zero
/// truncated divisor is made nonzero without a branch (d = bi + z with
/// z = 1 exactly when bi = 0, formed in the field and cast back, so d is
/// in [1, 2^128)) and the results are multiplied by 1 - z, so it returns
/// (0, 0, 0) there; callers select the divisor to 1 first, so this is
/// defensive. The remainder ai - q*bi is formed in the field
/// (0 <= ai - q*bi < bi < 2^128 when bi >= 1, so no wrap) and the
/// quotient limbs by division and remainder by the constant 2^64.
/// Trap-free for every argument: the divisors are d >= 1 and 2^64.
unconstrained fn hint_div_128(a: Field, b1: Field) -> (Field, Field, Field) {
    let ai = a as u128;
    let bi = b1 as u128;
    let z = (bi == 0) as Field;
    let d = ((bi as Field) + z) as u128;
    let q = ((ai / d) as Field) * (1 - z);
    let qi = q as u128;
    let w = TWO_POW_64 as u128;
    ((qi % w) as Field, (qi / w) as Field, ((ai as Field) - q * (bi as Field)) * (1 - z))
}

/// Constraint half of the 128-bit division, split out so tests can feed
/// wrong hints. For a < 2^128 and 1 <= b1 < 2^128 (PRECONDITIONS) and the
/// hinted quotient limbs q0, q1 and remainder r, with q = q0 + q1*2^64,
/// it emits:
/// 1. RANGE q0 and q1 to 64 bits (so 0 <= q < 2^128).
/// 2. RANGE r to 128 bits.
/// 3. RANGE b1 - r - 1 to 128 bits: r < b1.
/// 4. The carry c = (a - r - q0*b1) / 2^64 (a linear combination) and
///    RANGE c to 70 bits (core's width rule).
/// 5. a == q*b1 + r in the field.
/// It returns q.
/// Hint-satisfiable: the honest Euclidean pair has q < 2^128 and
/// r < b1 < 2^128 (1-3), satisfies 5, and gives
/// a - r - q0*b1 = q1*b1*2^64 with q1*b1*2^64 <= q*b1 <= a < 2^128, so
/// c = q1*b1 < 2^64 (4).
/// Determined: G = a - r - q0*b1 lies in (-2^192, 2^128) and c*2^64 in
/// [0, 2^134), so c*2^64 = G in the field is an integer identity (the
/// difference is below 2^193 < p). Then the integer
/// Z = a - q*b1 - r = G - q1*b1*2^64 = 2^64*(c - q1*b1), and by 5 Z is a
/// multiple of p; p is odd, so p divides c - q1*b1, whose magnitude is
/// below 2^192 < p, so c = q1*b1 and Z = 0. a = q*b1 + r over the
/// integers with 0 <= r < b1, so Euclid makes (q, r) unique, and the split
/// of q at bit 64 is unique. Load-bearing: without 4 a quotient with
/// q*b1 + r = a + p passes 1-3 and 5; without 2 a "negative" remainder
/// passes 3; without 3, (q - 1, r + b1) passes; without 1 the field
/// quotient a/b1 with r = 0 passes 5.
pub(crate) fn constrain_div_128(a: Field, b1: Field, q0: Field, q1: Field, r: Field) -> Field {
    q0.assert_max_bit_size::<64>();
    q1.assert_max_bit_size::<64>();
    r.assert_max_bit_size::<128>();
    (b1 - r - 1).assert_max_bit_size::<128>();
    let c = (a - r - q0 * b1) * INV_TWO_POW_64;
    c.assert_max_bit_size::<70>();
    let q = q0 + q1 * TWO_POW_64;
    assert(a == q * b1 + r);
    q
}

/// Euclidean division at 128 bits; PRECONDITIONS as constrain_div_128.
pub(crate) fn div_128(a: Field, b1: Field) -> (Field, Field) {
    // Safety: constrain_div_128 pins (q, r) to the unique Euclidean pair.
    let (q0, q1, r) = unsafe { hint_div_128(a, b1) };
    let q = constrain_div_128(a, b1, q0, q1, r);
    (q, r)
}

/// Euclidean division for a < 2^N and 1 <= d < 2^N (PRECONDITIONS),
/// 1 <= N <= 128: core::div_split for N <= 126 (RANGE q, r to N bits,
/// a == q*d + r, RANGE d - r - 1 to N bits), div_128 above (its five
/// checks). Both are hint-satisfiable under the preconditions and pin
/// the unique Euclidean pair; q and r are below 2^N.
fn div_n<let N: u32>(a: Field, d: Field) -> (Field, Field) {
    if N <= 126 {
        div_split::<N>(a, d)
    } else {
        div_128(a, d)
    }
}

/// Clamp both operands to N bits (1 <= N <= 253 by clamp_bits_or; the
/// callers state their own range): (a1, b1, both_in_range).
fn clamp_pair<let N: u32>(a: Field, b: Field) -> (Field, Field, bool) {
    let (a1, oka) = clamp_bits_or::<N>(a);
    let (b1, okb) = clamp_bits_or::<N>(b);
    (a1, b1, oka & okb)
}

// ---------------------------------------------------------------------
// Width-N Field domain: add, sub, mul
// ---------------------------------------------------------------------
//
// add and sub take every width to 128: core::add_split and sub_split
// are sound to 128 bits (the clamped operands are below 2^N, so
// a1 + b1 < 2^129 and a1 - b1 lies in (-2^128, 2^128), far from p, and
// their range argument needs only p - 2^N >= 2^N). mul takes N <= 126
// through core::mul_split and N = 127, 128 through mul_128_full
// (mul_full has the dispatch).

/// a + b on N-bit unsigned values (1 <= N <= 128). ok = both inputs are
/// below 2^N and the sum is below 2^N; the value is the sum when ok and
/// 0 otherwise.
/// Constraints: two clamp_bits_or (range.nr, hint-satisfiable for every
/// Field, determined), core::add_split (N-bit RANGE on the low part plus
/// the carry's booleanity, hint-satisfiable given the clamps), and a
/// select. The clamps discharge add_split's precondition; every flag is
/// determined.
pub fn add_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "add_or: N must be in 1..=128");
    let (a1, b1, ok_in) = clamp_pair::<N>(a, b);
    let (lo, carry) = add_split::<N>(a1, b1);
    let ok = ok_in & !carry;
    (select_field(ok, lo, 0), ok)
}

/// (a + b) mod 2^N; ok = both inputs below 2^N (1 <= N <= 128). An
/// out-of-range input is clamped to 0 first. Same constraints as add_or
/// without the select.
pub fn wrapping_add_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert(
        (N >= 1) & (N <= 128),
        "wrapping_add_or: N must be in 1..=128",
    );
    let (a1, b1, ok_in) = clamp_pair::<N>(a, b);
    let (lo, _) = add_split::<N>(a1, b1);
    (lo, ok_in)
}

/// min(a + b, 2^N - 1); ok = both inputs below 2^N (1 <= N <= 128). An
/// out-of-range input is clamped to 0 first. Same constraints as add_or.
pub fn saturating_add_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert(
        (N >= 1) & (N <= 128),
        "saturating_add_or: N must be in 1..=128",
    );
    let (a1, b1, ok_in) = clamp_pair::<N>(a, b);
    let (lo, carry) = add_split::<N>(a1, b1);
    (select_field(carry, two_pow::<N>() - 1, lo), ok_in)
}

/// a - b on N-bit unsigned values (1 <= N <= 128). ok = both inputs
/// below 2^N and a >= b; the value is the difference when ok and 0
/// otherwise.
/// Constraints: two clamp_bits_or, sub_split (a hinted borrow bit and
/// one N-bit RANGE on diff = a1 - b1 + borrow*2^N) and a select. The
/// clamps discharge sub_split's precondition; sub_split's doc comment
/// proves the borrow is determined and the honest hint always satisfies
/// the range check.
pub fn sub_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "sub_or: N must be in 1..=128");
    let (a1, b1, ok_in) = clamp_pair::<N>(a, b);
    let (diff, borrow) = sub_split::<N>(a1, b1);
    let ok = ok_in & !borrow;
    (select_field(ok, diff, 0), ok)
}

/// (a - b) mod 2^N; ok = both inputs below 2^N (1 <= N <= 128). Same
/// constraints as sub_or without the select.
pub fn wrapping_sub_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert(
        (N >= 1) & (N <= 128),
        "wrapping_sub_or: N must be in 1..=128",
    );
    let (a1, b1, ok_in) = clamp_pair::<N>(a, b);
    let (diff, _) = sub_split::<N>(a1, b1);
    (diff, ok_in)
}

/// max(a - b, 0); ok = both inputs below 2^N (1 <= N <= 128). Same
/// constraints as sub_or.
pub fn saturating_sub_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert(
        (N >= 1) & (N <= 128),
        "saturating_sub_or: N must be in 1..=128",
    );
    let (a1, b1, ok_in) = clamp_pair::<N>(a, b);
    let (diff, borrow) = sub_split::<N>(a1, b1);
    (select_field(borrow, 0, diff), ok_in)
}

/// a * b on N-bit unsigned values (1 <= N <= 128). ok = both inputs
/// below 2^N and the product below 2^N; the value is the product when ok
/// and 0 otherwise.
/// Constraints: two clamp_bits_or, mul_full (core::mul_split for
/// N <= 126: two N-bit RANGEs and a1*b1 == lo + hi*2^N, no wrap since the
/// product is below 2^252; mul_128_full for N = 127, 128: limb splits,
/// the range-checked low half and one carry, plus a split of the low half
/// at N = 127), is_zero(hi) and a select. All hint-satisfiable given the
/// clamps; determined.
pub fn mul_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "mul_or: N must be in 1..=128");
    let (a1, b1, ok_in) = clamp_pair::<N>(a, b);
    let (lo, hi) = mul_full::<N>(a1, b1);
    let ok = ok_in & is_zero(hi);
    (select_field(ok, lo, 0), ok)
}

/// (a * b) mod 2^N; ok = both inputs below 2^N (1 <= N <= 128). Same
/// constraints as mul_or without the is_zero and the select.
pub fn wrapping_mul_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert(
        (N >= 1) & (N <= 128),
        "wrapping_mul_or: N must be in 1..=128",
    );
    let (a1, b1, ok_in) = clamp_pair::<N>(a, b);
    let (lo, _) = mul_full::<N>(a1, b1);
    (lo, ok_in)
}

/// min(a * b, 2^N - 1); ok = both inputs below 2^N (1 <= N <= 128). Same
/// constraints as mul_or.
pub fn saturating_mul_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert(
        (N >= 1) & (N <= 128),
        "saturating_mul_or: N must be in 1..=128",
    );
    let (a1, b1, ok_in) = clamp_pair::<N>(a, b);
    let (lo, hi) = mul_full::<N>(a1, b1);
    (select_field(is_zero(hi), lo, two_pow::<N>() - 1), ok_in)
}

// ---------------------------------------------------------------------
// Width-N Field domain: division, negation, power
// ---------------------------------------------------------------------

/// Euclidean division on N-bit unsigned values (1 <= N <= 128):
/// (q, r, ok) with ok = both inputs below 2^N and b != 0. On ok = false
/// the divisor is selected to 1 and the dividend to 0 BEFORE the
/// division hint runs, so the hint never divides by zero and the result
/// is (0, 0).
/// Constraints: two clamp_bits_or, is_zero(b1) (inversion gadget), two
/// selects, and div_n: core::div_split for N <= 126 (RANGE q, r to N
/// bits, a1 == q*d + r, RANGE d - r - 1 to N bits), div_128 for N = 127,
/// 128 (64-bit RANGEs on the quotient limbs, RANGE r and d - r - 1 to
/// 128 bits, one carry RANGE and the field identity). The clamps and the
/// selects discharge the preconditions (dividend below 2^N,
/// 1 <= d < 2^N); all hint-satisfiable, determined.
pub fn div_rem_or<let N: u32>(a: Field, b: Field) -> (Field, Field, bool) {
    static_assert((N >= 1) & (N <= 128), "div_rem_or: N must be in 1..=128");
    let (a1, b1, ok_in) = clamp_pair::<N>(a, b);
    let ok = ok_in & !is_zero(b1);
    let (q, r) = div_n::<N>(select_field(ok, a1, 0), select_field(ok, b1, 1));
    (q, r, ok)
}

/// a / b on N-bit unsigned values (1 <= N <= 128): (q, ok) from
/// div_rem_or; q = 0 on ok = false.
pub fn div_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "div_or: N must be in 1..=128");
    let (q, _, ok) = div_rem_or::<N>(a, b);
    (q, ok)
}

/// a mod b on N-bit unsigned values (1 <= N <= 128): (r, ok) from
/// div_rem_or; r = 0 on ok = false.
pub fn mod_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "mod_or: N must be in 1..=128");
    let (_, r, ok) = div_rem_or::<N>(a, b);
    (r, ok)
}

// ---------------------------------------------------------------------
// Width-N Field domain: fused multiply-divide
// ---------------------------------------------------------------------

/// floor(a*b / d) on N-bit unsigned values in one gadget, with the
/// double-width product never leaving the field (1 <= N <= 84):
/// (q, r, ok) with ok = a, b and d all below 2^N and d != 0. On ok the
/// result is the exact Euclidean pair, q = floor(a*b/d) < 2^(2N) and
/// r = a*b mod d. On ok = false it is (0, 0): an out-of-range a or b is
/// clamped to 0, and an out-of-range or zero d is selected to 1 with the
/// dividend selected to 0, both BEFORE the hint runs, so the hint never
/// sees a zero divisor.
///
/// This is mul_div_to_or::<N, 2N>: the quotient is range-checked to the
/// full 2N bits, so it is always usable downstream as a 2N-bit value and
/// no quotient flag is needed. For the u8..u64 types use TotalMulDiv,
/// which skips the input clamps.
///
/// Constraints: three clamp_bits_or (range.nr, hint-satisfiable for every
/// Field, determined), is_zero on the clamped divisor (inversion gadget,
/// determined), two selects (arithmetic), and core::mul_div_split with
/// M = 2N: RANGE q to 2N bits, RANGE r to N bits, RANGE d1 - r - 1 to N
/// bits (r < d1), and a*b == q*d1 + r. The clamps and the selects
/// discharge mul_div_split's preconditions, so all of its asserts are
/// hint-satisfiable for every input (core::constrain_mul_div has the
/// argument, and the N <= 84 bound, core::MUL_DIV_MAX_BITS, that makes
/// the identity hold over the integers). ok and both outputs are
/// determined. ok folds the range flags of a and b and the nonzero flag
/// of the clamped divisor (which is false whenever d is out of range).
pub fn mul_div_or<let N: u32>(a: Field, b: Field, d: Field) -> (Field, Field, bool) {
    static_assert(
        (N >= 1) & (N <= MUL_DIV_MAX_BITS),
        "mul_div_or: N must be in 1..=84",
    );
    mul_div_to_or::<N, 2 * N>(a, b, d)
}

/// mul_div_or with the quotient's width declared by the caller,
/// 1 <= N <= 84 and 1 <= M <= 2N: (q, r, ok) where ok additionally
/// requires floor(a*b/d) < 2^M, and q is range-checked to M bits, so on
/// ok it can feed an M-bit gadget or an exact cast without a second
/// flag. On ok = false both values are 0 (for a too-wide quotient, by a
/// select on the quotient flag after the gadget).
///
/// DEV DECISION: the quotient width M. Default (mul_div_or): M = 2N, the
/// full width of the product, so a valid request never fails on the
/// quotient. A smaller M (M = N for "the result must be another N-bit
/// amount") turns a too-large quotient into ok = false instead of a
/// value the caller has to range-check itself; pick it when the next
/// step needs the narrower value. The quotient check is a split of the
/// hinted quotient at bit M (two RANGEs whose widths sum to 2N, and an
/// is_zero on the high part) in place of the single 2N-bit RANGE, so it
/// costs one is_zero, one more range check and two selects.
///
/// Constraints: as mul_div_or, with core::mul_div_split's RANGE q_lo to
/// M bits, RANGE q_hi to 2N - M bits and is_zero(q_hi) in place of the
/// 2N-bit RANGE when M < 2N, and the two selects on its flag.
/// Classification and determinedness as mul_div_or: the honest quotient
/// is below 2^(2N), so both split ranges hold for it, and the split is
/// unique.
pub fn mul_div_to_or<let N: u32, let M: u32>(a: Field, b: Field, d: Field) -> (Field, Field, bool) {
    static_assert(
        (N >= 1) & (N <= MUL_DIV_MAX_BITS),
        "mul_div_to_or: N must be in 1..=84",
    );
    static_assert(
        (M >= 1) & (M <= 2 * N),
        "mul_div_to_or: M must be in 1..=2N",
    );
    let (a1, b1, ok_in) = clamp_pair::<N>(a, b);
    let (dc, _) = clamp_bits_or::<N>(d);
    let d_ok = !is_zero(dc);
    // M % (2N + 1) is M on the legal range; past it, it keeps the gadget's
    // width 2N - M non-negative, so the static_assert above is the error
    // reported rather than a generic-arithmetic overflow.
    let (q, r, fits) = mul_div_split::<N, M % (2 * N + 1)>(
        select_field(d_ok, a1, 0),
        b1,
        select_field(d_ok, dc, 1),
    );
    (select_field(fits, q, 0), select_field(fits, r, 0), ok_in & d_ok & fits)
}

/// floor(a*b / d) on N-bit unsigned values past the 84-bit bound,
/// 85 <= N <= 128, in one gadget: (q_lo, q_hi, r, ok) with ok = a, b and
/// d all below 2^N and d != 0. On ok the result is the exact Euclidean
/// pair, q = floor(a*b/d) = q_lo + q_hi*2^128 (q_lo < 2^128,
/// q_hi < 2^(2N - 128); the quotient can need 2N > 253 bits, so it comes
/// back in two limbs) and r = a*b mod d. On ok = false it is (0, 0, 0):
/// an out-of-range a or b is clamped to 0, and an out-of-range or zero d
/// is selected to 1 with the dividend selected to 0, both BEFORE the
/// hint runs. Same preconditions-as-flags and ok semantics as
/// mul_div_or.
///
/// DEV DECISION: which multiply-divide entry. N <= 84: mul_div_or /
/// mul_div_to_or, which check a*b == q*d + r in the field alone (the
/// static_asserts reject N <= 84 here and N > 84 there, so the cheaper
/// path is the only one that compiles). 85 <= N <= 128: this one, or
/// mul_div_wide_to_or::<M> for 128-bit operands when the quotient must
/// fit M <= 253 bits (one Field instead of two limbs), or
/// TotalMulDiv on u128 for typed operands (no input clamps). The wide
/// check costs more than the 84-bit one (a carry range check, and for
/// N >= 125 the 64-bit limb splits of the operands and the quotient).
///
/// Constraints: three range::clamp_bits_or::<N> (core::clamp_bits_or for
/// N <= 127, core::clamp_128_or at N = 128; hint-satisfiable for every
/// Field, determined), is_zero on the clamped divisor, two selects, and
/// core::mul_div_wide_split: for N <= 124 RANGE q_lo to 128 bits, RANGE
/// q_hi to 2N - 128, RANGE r and d1 - r - 1 to N, one carry RANGE
/// showing a*b - q_lo*d1 - r is a multiple of 2^128, and
/// a*b == q*d1 + r in the field; for N >= 125 the same with every
/// operand and quotient limb split at bit 64 and a second carry
/// (core::constrain_mul_div_wide_unsplit and _split have the lists and
/// the uniqueness argument). The clamps and the selects discharge its
/// preconditions, so every assert is hint-satisfiable for every input;
/// ok and all outputs are determined.
pub fn mul_div_wide_or<let N: u32>(a: Field, b: Field, d: Field) -> (Field, Field, Field, bool) {
    static_assert(
        (N > MUL_DIV_MAX_BITS) & (N <= MUL_DIV_WIDE_MAX_BITS),
        "mul_div_wide_or: N must be in 85..=128 (for N <= 84 use mul_div_or)",
    );
    let (a1, b1, ok_in) = clamp_pair::<N>(a, b);
    let (dc, _) = clamp_bits_or::<N>(d);
    let d_ok = !is_zero(dc);
    let (q_lo, q_hi, r) =
        mul_div_wide_split::<N>(select_field(d_ok, a1, 0), b1, select_field(d_ok, dc, 1));
    (q_lo, q_hi, r, ok_in & d_ok)
}

/// Fused floor(a*b / d) on 128-bit operands with the quotient narrowed
/// to M bits, 1 <= M <= 253: (q, r, ok) with ok = a, b and d all below
/// 2^128, d != 0, and floor(a*b/d) < 2^M. On ok, q = floor(a*b/d) as one
/// Field (M <= 253 keeps it below p) and r = a*b mod d; on ok = false
/// both are 0. This is mul_div_wide_or::<128> with the two quotient
/// limbs folded into one value: use it when a 128-bit amount times a
/// factor over a divisor may exceed 2^128 before a later cap, so the
/// caller needs more than 128 quotient bits but fewer than the full 256.
///
/// DEV DECISION: the quotient width M. Default: none; the caller states
/// the bound its next step needs (M = 128 for "the result is another
/// u128 amount", larger for an intermediate that is capped later). M is
/// capped at 253 because the result is one Field; a 256-bit quotient
/// needs mul_div_wide_or::<128>'s two limbs. The operand width is fixed
/// at 128 bits; for narrower Field operands clamp them first (the flags
/// then also cover the narrower bound) or use mul_div_wide_or::<N>. The
/// width check costs one split of a 128-bit limb (RANGE K and 128 - K)
/// and one is_zero, except at M = 128, where it is is_zero(q_hi) alone,
/// plus two selects.
///
/// Constraints: those of mul_div_wide_or::<128> (three clamp_128_or, is_zero
/// on the clamped divisor, two selects, core::constrain_mul_div_wide_split:
/// the limb splits, two carries and the field identity), then the width
/// check: for M < 128 core::split_128_at::<M>(q_lo) and
/// is_zero(q_lo >> M + q_hi); for M = 128 is_zero(q_hi); for
/// 128 < M <= 253 core::split_128_at::<M - 128>(q_hi), the value
/// q_lo + (q_hi mod 2^(M - 128))*2^128 (below 2^253, no wrap) and
/// is_zero(q_hi >> (M - 128)); then two selects on the width flag. q_lo
/// and q_hi are bound below 2^128 by their limb splits, which is the
/// splits' precondition, so the splits are hint-satisfiable; a sum of
/// two values below 2^128 is zero iff both are. Uniqueness is the wide
/// gadget's (it pins the whole quotient below 2^256 and the remainder;
/// core::constrain_mul_div_wide_split has the argument), and the split
/// of a determined value is unique, so q, r and ok are determined.
pub fn mul_div_wide_to_or<let M: u32>(a: Field, b: Field, d: Field) -> (Field, Field, bool) {
    static_assert(
        (M >= 1) & (M <= 253),
        "mul_div_wide_to_or: M must be in 1..=253",
    );
    let (q_lo, q_hi, r, ok) = mul_div_wide_or::<128>(a, b, d);
    // The split width is M below 128 and M - 128 above it; M % 128 is
    // both, and keeps the branch not taken free of a negative width.
    let (q, fits) = if M < 128 {
        let (low, above) = split_128_at::<M % 128>(q_lo);
        (low, is_zero(above + q_hi))
    } else if M == 128 {
        (q_lo, is_zero(q_hi))
    } else {
        let (h, above) = split_128_at::<M % 128>(q_hi);
        (q_lo + h * TWO_POW_128, is_zero(above))
    };
    (select_field(fits, q, 0), select_field(fits, r, 0), ok & fits)
}

/// Two's complement negation on the N-bit domain (1 <= N <= 127):
/// value (2^N - a) mod 2^N, ok = a below 2^N (an out-of-range a is
/// clamped to 0, whose negation is 0). Constraints: clamp_bits_or and
/// is_zero (both hint-satisfiable, determined) plus arithmetic.
pub fn wrapping_neg_or<let N: u32>(a: Field) -> (Field, bool) {
    static_assert(
        (N >= 1) & (N <= 127),
        "wrapping_neg_or: N must be in 1..=127",
    );
    let (a1, ok) = clamp_bits_or::<N>(a);
    (select_field(is_zero(a1), 0, two_pow::<N>() - a1), ok)
}

/// Unsigned negation (1 <= N <= 127): representable only for 0, so
/// ok = a below 2^N and a == 0, and the value is 0 in every case (the
/// negation of 0 when ok, the failure value otherwise). Constraints:
/// clamp_bits_or and is_zero (hint-satisfiable, determined).
pub fn neg_or<let N: u32>(a: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 127), "neg_or: N must be in 1..=127");
    let (a1, ok) = clamp_bits_or::<N>(a);
    (0, ok & is_zero(a1))
}

/// Hint for the exponent bits: bit i of the truncated value is its
/// remainder by 2 after i halvings (remainder and quotient by the
/// constant 2). Trap-free: the cast truncates, the divisor is a nonzero
/// constant, and nothing can overflow.
pub(crate) unconstrained fn hint_low_bits<let E: u32>(x: Field) -> [bool; E] {
    let mut v = x as u128;
    let mut bits = [false; E];
    for i in 0..E {
        bits[i] = (v % 2) == 1;
        v = v / 2;
    }
    bits
}

/// Constraint half of the exponent split: sum bits[i]*2^i == x. The
/// booleanity of each bit is the compiler's type constraint on the
/// hint's [bool; E] return. Given x < 2^E (E <= 126) the binary
/// representation exists and is unique and the sum cannot wrap, so the
/// bits are determined and the honest hint satisfies the equation.
pub(crate) fn constrain_low_bits<let E: u32>(x: Field, bits: [bool; E]) {
    let mut acc: Field = 0;
    let mut pw: Field = 1;
    for i in 0..E {
        acc += (bits[i] as Field) * pw;
        pw *= 2;
    }
    assert(acc == x);
}

/// (b^e mod 2^N, spill) for b < 2^N and e < 2^E (PRECONDITIONS),
/// 1 <= N <= 128, 1 <= E <= 126, with spill = 0 iff b^e < 2^N and
/// 0^0 = 1.
/// E = 1: e is 0 or 1, the power is the select e*(b - 1) + 1 and the
/// spill is 0; no hint and no constraint.
/// E >= 2: square-and-multiply from the most significant exponent bit;
/// every step is mul_full::<N>, so the running value stays below 2^N
/// (range-checked low part) and the steps compute the power mod 2^N
/// exactly. Every intermediate is b^k with k <= e (for b >= 1; b = 0
/// never overflows), so some step overflows iff the final power does:
/// spill sums the high parts of all steps (each below 2^128, at most 250
/// of them, so the sum is below 2^136 and cannot wrap).
/// Constraints for E >= 2: the exponent split (E hinted bits,
/// booleanity, one reconstruction equation, determined because e is
/// below 2^E) and 2(E - 1) mul_full. All hint-satisfiable under the
/// preconditions; both outputs determined.
fn pow_bits<let N: u32, let E: u32>(b: Field, e: Field) -> (Field, Field) {
    if E <= 1 {
        (e * (b - 1) + 1, 0)
    } else {
        // Safety: constrain_low_bits checks the weighted sum against e,
        // which is below 2^E, so the bits are unique.
        let bits = unsafe { hint_low_bits::<E>(e) };
        constrain_low_bits::<E>(e, bits);
        let mut acc = select_field(bits[E - 1], b, 1);
        let mut spill: Field = 0;
        for i in 1..E {
            let (sq, sq_hi) = mul_full::<N>(acc, acc);
            let m = select_field(bits[E - 1 - i], b, 1);
            let (pr, pr_hi) = mul_full::<N>(sq, m);
            spill += sq_hi + pr_hi;
            acc = pr;
        }
        (acc, spill)
    }
}

/// base^exp on N-bit unsigned values with an exponent of at most
/// E bits (1 <= N <= 128, 1 <= E <= 126). ok = base below 2^N, exp
/// below 2^E, and base^exp below 2^N; the value is base^exp when ok and
/// 0 otherwise. 0^0 = 1.
/// Constraints: clamp_bits_or on base and exp, pow_bits (for E = 1 a
/// select and nothing else; for E >= 2 the exponent split and 2(E - 1)
/// mul_full), one is_zero on the spill and a select. All
/// hint-satisfiable for every input; ok determined.
pub fn pow_or<let N: u32, let E: u32>(base: Field, exp: Field) -> (Field, bool) {
    static_assert(
        (N >= 1) & (N <= 128) & (E >= 1) & (E <= 126),
        "pow_or: N must be in 1..=128 and E in 1..=126",
    );
    let (b1, okb) = clamp_bits_or::<N>(base);
    let (e1, oke) = clamp_bits_or::<E>(exp);
    let (acc, spill) = pow_bits::<N, E>(b1, e1);
    let ok = okb & oke & is_zero(spill);
    (select_field(ok, acc, 0), ok)
}

// ---------------------------------------------------------------------
// The field itself
// ---------------------------------------------------------------------

/// Hint for inverse_or: (1/x, false) for x != 0 and (0, true) for x = 0.
/// The divisor is made nonzero without a branch: x + z with z = 1 exactly
/// when x = 0, and the quotient is then multiplied by 1 - z. Trap-free for
/// every x: the divisor x + z is never zero.
unconstrained fn hint_inverse(x: Field) -> (Field, bool) {
    let z = x == 0;
    let zf = z as Field;
    ((1 / (x + zf)) * (1 - zf), z)
}

/// Constraint half of inverse_or: x*z == 0 and x*inv == 1 - z, with z
/// boolean (the compiler's type constraint on the hint's bool return).
/// For x != 0 the first forces z = 0 and the second forces inv = 1/x;
/// for x = 0 the second forces z = 1 and leaves inv free, which
/// inverse_or masks. Hint-satisfiable for every x (x = 0: z = 1,
/// inv = 0; else z = 0, inv = 1/x); z determined.
pub(crate) fn constrain_inverse(x: Field, inv: Field, z: bool) {
    assert(x * (z as Field) == 0);
    assert(x * inv == 1 - (z as Field));
}

/// Field inverse: (1/x, true) for x != 0 and (0, false) for x = 0.
/// Constraints: constrain_inverse (two equations, hint-satisfiable for
/// every x) plus the mask inv*(1 - z). Both outputs determined: the mask
/// removes the only free value (inv at x = 0).
pub fn inverse_or(x: Field) -> (Field, bool) {
    // Safety: constrain_inverse forces z to (x == 0) and inv to 1/x when
    // x != 0; the returned value is masked to 0 when x = 0.
    let (inv, z) = unsafe { hint_inverse(x) };
    constrain_inverse(x, inv, z);
    (select_field(z, 0, inv), !z)
}

/// Field division: (a/b, true) for b != 0 and (0, false) for b = 0.
/// Constraints: inverse_or on b plus one multiplication (the masked
/// inverse is 0 at b = 0, so the value is too). Total, unlike native
/// a / b.
pub fn field_div_or(a: Field, b: Field) -> (Field, bool) {
    let (inv, ok) = inverse_or(b);
    (a * inv, ok)
}

/// b^e in unconstrained code, for any Field exponent. Trap-free: Field
/// arithmetic and to_le_bits of any Field are defined.
unconstrained fn pow_field(b: Field, e: Field) -> Field {
    let bits: [bool; 254] = e.to_le_bits();
    let mut r: Field = 1;
    for i in 0..254 {
        r = r * r;
        if bits[253 - i] {
            r = r * b;
        }
    }
    r
}

/// Euler's criterion x^((p-1)/2): 1 for nonzero squares, p - 1 for
/// non-squares, 0 for 0. (p-1)/2 is computed as -1/2 in the field, which
/// is the integer (p-1)/2 because 2*((p-1)/2) = p - 1 = -1 mod p.
/// Trap-free: division by the constant 2.
unconstrained fn euler(x: Field) -> Field {
    pow_field(x, (0 - 1) / 2)
}

/// Tonelli-Shanks square root of a nonzero square y in the bn254 scalar
/// field, where p - 1 = 2^28 * t with t odd. Trap-free: Field arithmetic
/// with divisions by nonzero constants only, loops bounded by 28, u32
/// counters below 60. On a non-square input it returns some value
/// without trapping (the caller only passes squares).
unconstrained fn tonelli_shanks(y: Field) -> Field {
    let t = (0 - 1) / 268435456; // (p-1) / 2^28, exact as in euler()
    let mut m: u32 = 28;
    let mut c = pow_field(SQRT_NON_RESIDUE, t);
    let mut tt = pow_field(y, t);
    let mut r = pow_field(y, (t + 1) / 2);
    for _ in 0..28 {
        if tt != 1 {
            let mut i: u32 = 0;
            let mut s = tt;
            for _ in 0..28 {
                if s != 1 {
                    s = s * s;
                    i += 1;
                }
            }
            let mut b = c;
            for k in 0..28 {
                if k + i + 1 < m {
                    b = b * b;
                }
            }
            m = i;
            c = b * b;
            tt = tt * c;
            r = r * b;
        }
    }
    r
}

/// Hint for sqrt_or: (r, q, inv) with q = (x is a square, including 0),
/// r a root of x when q holds and of g*x otherwise (g =
/// SQRT_NON_RESIDUE), and inv = 1/x for x != 0 (0 for x = 0). Trap-free:
/// zero is tested before inverting; see euler and tonelli_shanks. Not
/// co-noir-compatible: tonelli_shanks branches on values derived from x
/// (see the module header).
unconstrained fn hint_sqrt(x: Field) -> (Field, bool, Field) {
    if x == 0 {
        (0, true, 0)
    } else if euler(x) == 1 {
        (tonelli_shanks(x), true, 1 / x)
    } else {
        (tonelli_shanks(SQRT_NON_RESIDUE * x), false, 1 / x)
    }
}

/// Constraint half of sqrt_or, split out so tests can feed wrong hints.
/// With q boolean (the compiler's type constraint on the hint's bool
/// return) and g = SQRT_NON_RESIDUE it emits:
/// 1. r*r == x*(g + q*(1 - g)): r*r = x when q = 1, r*r = g*x when q = 0.
/// 2. (1 - q)*(x*inv - 1) == 0: q = 0 requires x*inv = 1, so x != 0.
/// Hint-satisfiable for every x: x = 0 takes q = 1, r = 0; a nonzero
/// square takes q = 1 and a root; a non-square takes q = 0, a root of g*x
/// (g*x is a square because g is a non-residue) and inv = 1/x.
/// Determined: for x != 0 exactly one of x, g*x is a square, so exactly
/// one q admits an r in 1; for x = 0, 2 rules out q = 0, and 1 forces
/// r = 0. So q is determined everywhere, and r up to sign when q = 1.
pub(crate) fn constrain_sqrt(x: Field, r: Field, q: bool, inv: Field) {
    let qf = q as Field;
    assert(r * r == x * (SQRT_NON_RESIDUE + qf * (1 - SQRT_NON_RESIDUE)));
    assert((1 - qf) * (x * inv - 1) == 0);
}

/// Square root in the bn254 scalar field: (r, true) with r*r == x when x
/// is a square (including 0), else (0, false). ok = q is determined
/// (constrain_sqrt). The root is determined only up to sign: a prover
/// may return r or -r. Use sqrt_canonical_or when the choice matters.
/// Constraints: constrain_sqrt (two equations) and the product q*r for
/// the value (r when ok, 0 otherwise). All hint-satisfiable for every x.
pub fn sqrt_or(x: Field) -> (Field, bool) {
    // Safety: constrain_sqrt forces q, forces r*r to x when q holds, and
    // the value is masked to 0 when q is false.
    let (r, q, inv) = unsafe { hint_sqrt(x) };
    constrain_sqrt(x, r, q, inv);
    ((q as Field) * r, q)
}

/// Square root with the sign fixed: the even one of {r, p - r} (p is
/// odd, so for r != 0 exactly one is even), else (0, false). Fully
/// determined. Extra constraints over sqrt_or: core::limbs on the root
/// and a split of its low limb at bit 1 (all hint-satisfiable for every
/// Field), then r*(1 - 2*bit0), which negates an odd root.
pub fn sqrt_canonical_or(x: Field) -> (Field, bool) {
    let (r, ok) = sqrt_or(x);
    let (lo, _) = limbs(r);
    let (bit0, _) = split_128_at::<1>(lo);
    (r * (1 - 2 * bit0), ok)
}

// ---------------------------------------------------------------------
// Native unsigned facades
// ---------------------------------------------------------------------

/// Total replacements for the native operators. Each method returns
/// (value, ok) and never fails a constraint. ok = false on overflow (the
/// exact result does not fit the type), on a zero divisor, and on signed
/// types for MIN / -1 and MIN % -1; every value is then 0. div_rem_or
/// returns both from one division. The wrapped results of + - * are
/// std's wrapping_add/sub/mul (total already); the clamped ones are
/// trait Saturating. Signed impls live in signed.nr.
pub trait TotalArith {
    fn add_or(self, other: Self) -> (Self, bool);
    fn sub_or(self, other: Self) -> (Self, bool);
    fn mul_or(self, other: Self) -> (Self, bool);
    fn div_or(self, other: Self) -> (Self, bool);
    fn div_rem_or(self, other: Self) -> (Self, Self, bool);
    fn mod_or(self, other: Self) -> (Self, bool);
}

/// Saturating arithmetic for the native integer types (unsigned here,
/// signed in signed.nr); total, no flag (there is nothing left to fail
/// once the operands are typed).
pub trait Saturating {
    fn saturating_add(self, other: Self) -> Self;
    fn saturating_sub(self, other: Self) -> Self;
    fn saturating_mul(self, other: Self) -> Self;
}

/// Further unsigned operations for u8, u16, u32, u64, u128.
/// - widening_mul(a, b): (lo, hi) with a*b = lo + hi*2^N. Total.
/// - pow_or(base, exp): base^exp, flagged on overflow; 0^0 = 1.
/// - isqrt(x): floor(sqrt(x)). Total.
/// - abs_diff(a, b): |a - b|. Total.
/// - div_ceil_or(a, d): ceil(a / d), flagged on d = 0 (the quotient
///   cannot overflow: for d >= 2 it is at most ceil(MAX / 2)).
/// The constraints are listed at each shared body below.
pub trait TotalUnsigned {
    fn widening_mul(self, other: Self) -> (Self, Self);
    fn pow_or(self, exp: u32) -> (Self, bool);
    fn isqrt(self) -> Self;
    fn abs_diff(self, other: Self) -> Self;
    fn div_ceil_or(self, d: Self) -> (Self, bool);
}

// Shared bodies for u8..u128, on operands below 2^N by the type
// invariant. Each returns a value that is range-checked to at most N
// bits (by the core gadget or by implied_range), so the caller's
// `as uN` is exact; the caller zeroes it on ok = false with or_zero.

fn uadd<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    let (lo, carry) = add_split::<N>(a, b);
    (lo, !carry)
}

fn usub<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    let (diff, borrow) = sub_split::<N>(a, b);
    (diff, !borrow)
}

fn umul<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    let (lo, hi) = mul_full::<N>(a, b);
    (lo, is_zero(hi))
}

/// Division with the divisor selected to 1 and the dividend to 0 when
/// the divisor is zero, before the hint runs: (q, r, nz), and
/// (0, 0, false) for a zero divisor. div_n is core::div_split for
/// N <= 64 and div_128 for u128. The u128 quotient is bound below 2^128
/// by its 64-bit limb ranges, so implied_range::<128> holds for every
/// satisfying witness; at N <= 64 div_split range-checks q itself.
fn udiv<let N: u32>(a: Field, b: Field) -> (Field, Field, bool) {
    let nz = !is_zero(b);
    let (q, r) = div_n::<N>(select_field(nz, a, 0), select_field(nz, b, 1));
    let q = if N == 128 { implied_range::<128>(q) } else { q };
    (q, r, nz)
}

// Saturating values: a select of two values below 2^N, so implied_range
// holds for every satisfying witness.

fn usat_add<let N: u32>(a: Field, b: Field) -> Field {
    let (lo, carry) = add_split::<N>(a, b);
    implied_range::<N>(select_field(carry, two_pow::<N>() - 1, lo))
}

fn usat_sub<let N: u32>(a: Field, b: Field) -> Field {
    let (diff, borrow) = sub_split::<N>(a, b);
    implied_range::<N>(select_field(borrow, 0, diff))
}

fn usat_mul<let N: u32>(a: Field, b: Field) -> Field {
    let (lo, hi) = mul_full::<N>(a, b);
    implied_range::<N>(select_field(is_zero(hi), lo, two_pow::<N>() - 1))
}

/// widening_mul on N-bit operands (N in {8, 16, 32, 64, 128}): mul_full,
/// whose low part is range-checked to N bits. The high part is
/// range-checked by mul_split's N-bit RANGE for N <= 64; for N = 128 it
/// is bound below 2^128 by constrain_mul_128's argument, so
/// implied_range::<128> holds for every satisfying witness. Both casts
/// are then exact. Determined: mul_full's outputs are.
fn uwide<let N: u32>(a: Field, b: Field) -> (Field, Field) {
    let (lo, hi) = mul_full::<N>(a, b);
    let hi = if N == 128 {
        implied_range::<128>(hi)
    } else {
        hi
    };
    (lo, hi)
}

/// Hint for abs_diff: a < b on the low 128 bits. Trap-free: casts
/// truncate and a u128 compare cannot trap; exact for a, b < 2^128.
unconstrained fn hint_lt_128(a: Field, b: Field) -> bool {
    (a as u128) < (b as u128)
}

/// Constraint half of abs_diff, split out so tests can feed wrong hints.
/// For a, b < 2^N (PRECONDITION, N <= 128) and the hinted bit c (its
/// booleanity is the compiler's type constraint on the hint's bool
/// return) it emits RANGE d to N bits, d = c ? b - a : a - b, and
/// returns d.
/// Hint-satisfiable: the honest c = (a < b) makes d = |a - b| < 2^N.
/// Determined (the output; c itself is free when a = b, where both
/// choices give d = 0): if a > b and c = 1, d = b - a is p - k with
/// 1 <= k < 2^N, at least p - 2^N >= 2^N for N <= 252, so the range
/// fails; if a < b and c = 0, the same for a - b. So every satisfying
/// witness has d = |a - b|. Load-bearing: without the range, the wrong c
/// passes with d = -(a - b) mod p.
pub(crate) fn constrain_abs_diff<let N: u32>(a: Field, b: Field, c: bool) -> Field {
    let d = select_field(c, b - a, a - b);
    d.assert_max_bit_size::<N>();
    d
}

/// |a - b| for a, b < 2^N: one hinted bit and one N-bit RANGE
/// (constrain_abs_diff). The output carries the RANGE, so its cast is
/// exact.
fn uabs_diff<let N: u32>(a: Field, b: Field) -> Field {
    // Safety: constrain_abs_diff range-checks the selected difference,
    // which rules out the wrong bit except at a = b, where d = 0 either
    // way.
    let c = unsafe { hint_lt_128(a, b) };
    constrain_abs_diff::<N>(a, b, c)
}

/// Hint for isqrt: floor(sqrt(x)) for the low 128 bits of x, bit by bit
/// from 2^(H - 1) down: take a bit when (r + 2^k)^2 <= x. The test is a
/// Field comparison and the take is the arithmetic r + take*2^k (no
/// branch on x), and every square is below 2^(2H) <= 2^128, so nothing
/// wraps. Trap-free for every argument: Field arithmetic, a truncating
/// cast, and constant indices. For x < 2^(2H) the result is the integer
/// square root, below 2^H.
pub(crate) unconstrained fn hint_isqrt<let H: u32>(x: Field) -> Field {
    let xl = (x as u128) as Field;
    let mut pws = [0; H];
    let mut pw: Field = 1;
    for i in 0..H {
        pws[i] = pw;
        pw *= 2;
    }
    let mut r: Field = 0;
    for i in 0..H {
        let w = pws[H - 1 - i];
        let c = r + w;
        let take = !xl.lt(c * c);
        r += (take as Field) * w;
    }
    r
}

/// Constraint half of isqrt, split out so tests can feed wrong hints.
/// For x < 2^N (PRECONDITION, N even, 2 <= N <= 128) and the hinted root
/// r it emits:
/// 1. RANGE r to N/2 bits.
/// 2. RANGE x - r*r to N bits: r*r <= x.
/// 3. RANGE (r + 1)^2 - x - 1 to N bits: x < (r + 1)^2.
/// Hint-satisfiable: the honest r = floor(sqrt(x)) is below 2^(N/2)
/// because x < 2^N; x - r*r lies in [0, x] and (r + 1)^2 - x - 1 in
/// [0, 2r] (from x >= r^2), both below 2^N.
/// No overflow: by 1, r*r < 2^N and (r + 1)^2 <= 2^N, far below p, so the
/// expressions in 2 and 3 are the integers they name.
/// Determined: if r*r > x, the value in 2 is p - k with
/// 1 <= k < 2^N, at least p - 2^N >= 2^N, so 2 fails; if (r + 1)^2 <= x,
/// the value in 3 is p - k with 1 <= k <= 2^N, so 3 fails. So
/// r*r <= x < (r + 1)^2, which fixes r. Load-bearing: without 1, 2 and 3
/// pin r only as a field element with 2r = u + v for their two values,
/// and at the wide widths an odd u + v gives a root near p/2 (the test
/// isqrt_field_root_rejected has one at N = 128, x = 0); without 2,
/// r + 1 passes; without 3, r - 1 (for r >= 1).
pub(crate) fn constrain_isqrt<let N: u32>(x: Field, r: Field) {
    r.assert_max_bit_size::<N / 2>();
    (x - r * r).assert_max_bit_size::<N>();
    ((r + 1) * (r + 1) - x - 1).assert_max_bit_size::<N>();
}

/// floor(sqrt(x)) for x < 2^N: the hinted root and constrain_isqrt. The
/// root carries an N/2-bit RANGE, so its cast to the type is exact.
fn uisqrt<let N: u32>(x: Field) -> Field {
    // Safety: constrain_isqrt pins r to the unique integer with
    // r*r <= x < (r + 1)^2.
    let r = unsafe { hint_isqrt::<N / 2>(x) };
    constrain_isqrt::<N>(x, r);
    r
}

/// ceil(a / d) for a, d < 2^N: (c, d != 0), and (0, false) for d = 0.
/// udiv, then c = q + (r != 0) (one is_zero) and implied_range::<N>(c):
/// for r != 0, d >= 2 and q <= (2^N - 1)/2, so c < 2^N for every
/// satisfying witness, and the range adds no failure source.
fn udiv_ceil<let N: u32>(a: Field, d: Field) -> (Field, bool) {
    let (q, r, nz) = udiv::<N>(a, d);
    (implied_range::<N>(q + (!is_zero(r) as Field)), nz)
}

/// base^exp for base < 2^N and a u32 exponent: (value, ok) with
/// ok = base^exp < 2^N, and value base^exp when ok (the caller zeroes it
/// otherwise). K is the number of exponent bits the square-and-multiply
/// runs on, with 2^K > N.
/// The exponent is split at bit K with core::split_at::<K, 32 - K>
/// (RANGE K and 32 - K and the reconstruction; hint-satisfiable because
/// exp < 2^32 by its type). A high part e_hi != 0 means exp >= 2^K > N,
/// so base^exp >= 2^exp >= 2^N for base >= 2, while 0^exp = 0 and
/// 1^exp = 1: the result is base, flagged unless base is 0 or 1. That
/// case runs the loop on the exponent 1 (one select before the bits are
/// hinted), so its value base still comes out of the loop with the low
/// part's RANGE. Otherwise the loop runs on the low K bits. Constraints:
/// the split, is_zero(e_hi), a select, pow_bits::<N, K> (K hinted bits
/// and 2(K - 1) mul_full), is_zero(base*(base - 1)) (a field product is
/// zero iff a factor is, and base < p), is_zero(spill), and boolean
/// selects. The loop's last mul_full leaves the value range-checked to
/// N bits, so the caller's cast is exact. Determined: every part is.
fn upow<let N: u32, let K: u32>(base: Field, exp: Field) -> (Field, bool) {
    let (e_lo, e_hi) = split_at::<K, 32 - K>(exp);
    let big = !is_zero(e_hi);
    let (acc, spill) = pow_bits::<N, K>(base, select_field(big, 1, e_lo));
    let small_base = is_zero(base * (base - 1));
    let ok = (big & small_base) | (!big & is_zero(spill));
    (acc, ok)
}

impl TotalArith for u8 {
    fn add_or(self, other: u8) -> (u8, bool) {
        let (v, ok) = uadd::<8>(self as Field, other as Field);
        (or_zero(ok, v as u8), ok)
    }
    fn sub_or(self, other: u8) -> (u8, bool) {
        let (v, ok) = usub::<8>(self as Field, other as Field);
        (or_zero(ok, v as u8), ok)
    }
    fn mul_or(self, other: u8) -> (u8, bool) {
        let (v, ok) = umul::<8>(self as Field, other as Field);
        (or_zero(ok, v as u8), ok)
    }
    fn div_or(self, other: u8) -> (u8, bool) {
        let (q, _, ok) = udiv::<8>(self as Field, other as Field);
        (q as u8, ok)
    }
    fn div_rem_or(self, other: u8) -> (u8, u8, bool) {
        let (q, r, ok) = udiv::<8>(self as Field, other as Field);
        (q as u8, r as u8, ok)
    }
    fn mod_or(self, other: u8) -> (u8, bool) {
        let (_, r, ok) = udiv::<8>(self as Field, other as Field);
        (r as u8, ok)
    }
}

impl TotalArith for u16 {
    fn add_or(self, other: u16) -> (u16, bool) {
        let (v, ok) = uadd::<16>(self as Field, other as Field);
        (or_zero(ok, v as u16), ok)
    }
    fn sub_or(self, other: u16) -> (u16, bool) {
        let (v, ok) = usub::<16>(self as Field, other as Field);
        (or_zero(ok, v as u16), ok)
    }
    fn mul_or(self, other: u16) -> (u16, bool) {
        let (v, ok) = umul::<16>(self as Field, other as Field);
        (or_zero(ok, v as u16), ok)
    }
    fn div_or(self, other: u16) -> (u16, bool) {
        let (q, _, ok) = udiv::<16>(self as Field, other as Field);
        (q as u16, ok)
    }
    fn div_rem_or(self, other: u16) -> (u16, u16, bool) {
        let (q, r, ok) = udiv::<16>(self as Field, other as Field);
        (q as u16, r as u16, ok)
    }
    fn mod_or(self, other: u16) -> (u16, bool) {
        let (_, r, ok) = udiv::<16>(self as Field, other as Field);
        (r as u16, ok)
    }
}

impl TotalArith for u32 {
    fn add_or(self, other: u32) -> (u32, bool) {
        let (v, ok) = uadd::<32>(self as Field, other as Field);
        (or_zero(ok, v as u32), ok)
    }
    fn sub_or(self, other: u32) -> (u32, bool) {
        let (v, ok) = usub::<32>(self as Field, other as Field);
        (or_zero(ok, v as u32), ok)
    }
    fn mul_or(self, other: u32) -> (u32, bool) {
        let (v, ok) = umul::<32>(self as Field, other as Field);
        (or_zero(ok, v as u32), ok)
    }
    fn div_or(self, other: u32) -> (u32, bool) {
        let (q, _, ok) = udiv::<32>(self as Field, other as Field);
        (q as u32, ok)
    }
    fn div_rem_or(self, other: u32) -> (u32, u32, bool) {
        let (q, r, ok) = udiv::<32>(self as Field, other as Field);
        (q as u32, r as u32, ok)
    }
    fn mod_or(self, other: u32) -> (u32, bool) {
        let (_, r, ok) = udiv::<32>(self as Field, other as Field);
        (r as u32, ok)
    }
}

impl TotalArith for u64 {
    fn add_or(self, other: u64) -> (u64, bool) {
        let (v, ok) = uadd::<64>(self as Field, other as Field);
        (or_zero(ok, v as u64), ok)
    }
    fn sub_or(self, other: u64) -> (u64, bool) {
        let (v, ok) = usub::<64>(self as Field, other as Field);
        (or_zero(ok, v as u64), ok)
    }
    fn mul_or(self, other: u64) -> (u64, bool) {
        let (v, ok) = umul::<64>(self as Field, other as Field);
        (or_zero(ok, v as u64), ok)
    }
    fn div_or(self, other: u64) -> (u64, bool) {
        let (q, _, ok) = udiv::<64>(self as Field, other as Field);
        (q as u64, ok)
    }
    fn div_rem_or(self, other: u64) -> (u64, u64, bool) {
        let (q, r, ok) = udiv::<64>(self as Field, other as Field);
        (q as u64, r as u64, ok)
    }
    fn mod_or(self, other: u64) -> (u64, bool) {
        let (_, r, ok) = udiv::<64>(self as Field, other as Field);
        (r as u64, ok)
    }
}

/// u128: add via add_split::<128>, sub via sub_split::<128>, mul via
/// mul_128_full (its low half carries its own 128-bit RANGE, so the cast
/// is exact), and div/mod via div_128 (udiv at N = 128).
impl TotalArith for u128 {
    fn add_or(self, other: u128) -> (u128, bool) {
        let (v, ok) = uadd::<128>(self as Field, other as Field);
        (or_zero(ok, v as u128), ok)
    }
    fn sub_or(self, other: u128) -> (u128, bool) {
        let (v, ok) = usub::<128>(self as Field, other as Field);
        (or_zero(ok, v as u128), ok)
    }
    fn mul_or(self, other: u128) -> (u128, bool) {
        let (v, ok) = umul::<128>(self as Field, other as Field);
        (or_zero(ok, v as u128), ok)
    }
    fn div_or(self, other: u128) -> (u128, bool) {
        let (q, _, ok) = udiv::<128>(self as Field, other as Field);
        (q as u128, ok)
    }
    fn div_rem_or(self, other: u128) -> (u128, u128, bool) {
        let (q, r, ok) = udiv::<128>(self as Field, other as Field);
        (q as u128, r as u128, ok)
    }
    fn mod_or(self, other: u128) -> (u128, bool) {
        let (_, r, ok) = udiv::<128>(self as Field, other as Field);
        (r as u128, ok)
    }
}

impl Saturating for u8 {
    fn saturating_add(self, other: u8) -> u8 {
        usat_add::<8>(self as Field, other as Field) as u8
    }
    fn saturating_sub(self, other: u8) -> u8 {
        usat_sub::<8>(self as Field, other as Field) as u8
    }
    fn saturating_mul(self, other: u8) -> u8 {
        usat_mul::<8>(self as Field, other as Field) as u8
    }
}

impl Saturating for u16 {
    fn saturating_add(self, other: u16) -> u16 {
        usat_add::<16>(self as Field, other as Field) as u16
    }
    fn saturating_sub(self, other: u16) -> u16 {
        usat_sub::<16>(self as Field, other as Field) as u16
    }
    fn saturating_mul(self, other: u16) -> u16 {
        usat_mul::<16>(self as Field, other as Field) as u16
    }
}

impl Saturating for u32 {
    fn saturating_add(self, other: u32) -> u32 {
        usat_add::<32>(self as Field, other as Field) as u32
    }
    fn saturating_sub(self, other: u32) -> u32 {
        usat_sub::<32>(self as Field, other as Field) as u32
    }
    fn saturating_mul(self, other: u32) -> u32 {
        usat_mul::<32>(self as Field, other as Field) as u32
    }
}

impl Saturating for u64 {
    fn saturating_add(self, other: u64) -> u64 {
        usat_add::<64>(self as Field, other as Field) as u64
    }
    fn saturating_sub(self, other: u64) -> u64 {
        usat_sub::<64>(self as Field, other as Field) as u64
    }
    fn saturating_mul(self, other: u64) -> u64 {
        usat_mul::<64>(self as Field, other as Field) as u64
    }
}

impl Saturating for u128 {
    fn saturating_add(self, other: u128) -> u128 {
        let (lo, carry) = add_split::<128>(self as Field, other as Field);
        implied_range::<128>(select_field(carry, U128_MAX_FIELD, lo)) as u128
    }
    fn saturating_sub(self, other: u128) -> u128 {
        let (diff, borrow) = sub_split::<128>(self as Field, other as Field);
        implied_range::<128>(select_field(borrow, 0, diff)) as u128
    }
    fn saturating_mul(self, other: u128) -> u128 {
        let (lo, fits) = mul_128(self as Field, other as Field);
        implied_range::<128>(select_field(fits, lo, U128_MAX_FIELD)) as u128
    }
}

impl TotalUnsigned for u8 {
    fn widening_mul(self, other: u8) -> (u8, u8) {
        let (lo, hi) = uwide::<8>(self as Field, other as Field);
        (lo as u8, hi as u8)
    }
    fn pow_or(self, exp: u32) -> (u8, bool) {
        let (v, ok) = upow::<8, 4>(self as Field, exp as Field);
        (or_zero(ok, v as u8), ok)
    }
    fn isqrt(self) -> u8 {
        uisqrt::<8>(self as Field) as u8
    }
    fn abs_diff(self, other: u8) -> u8 {
        uabs_diff::<8>(self as Field, other as Field) as u8
    }
    fn div_ceil_or(self, d: u8) -> (u8, bool) {
        let (c, ok) = udiv_ceil::<8>(self as Field, d as Field);
        (c as u8, ok)
    }
}

impl TotalUnsigned for u16 {
    fn widening_mul(self, other: u16) -> (u16, u16) {
        let (lo, hi) = uwide::<16>(self as Field, other as Field);
        (lo as u16, hi as u16)
    }
    fn pow_or(self, exp: u32) -> (u16, bool) {
        let (v, ok) = upow::<16, 5>(self as Field, exp as Field);
        (or_zero(ok, v as u16), ok)
    }
    fn isqrt(self) -> u16 {
        uisqrt::<16>(self as Field) as u16
    }
    fn abs_diff(self, other: u16) -> u16 {
        uabs_diff::<16>(self as Field, other as Field) as u16
    }
    fn div_ceil_or(self, d: u16) -> (u16, bool) {
        let (c, ok) = udiv_ceil::<16>(self as Field, d as Field);
        (c as u16, ok)
    }
}

impl TotalUnsigned for u32 {
    fn widening_mul(self, other: u32) -> (u32, u32) {
        let (lo, hi) = uwide::<32>(self as Field, other as Field);
        (lo as u32, hi as u32)
    }
    fn pow_or(self, exp: u32) -> (u32, bool) {
        let (v, ok) = upow::<32, 6>(self as Field, exp as Field);
        (or_zero(ok, v as u32), ok)
    }
    fn isqrt(self) -> u32 {
        uisqrt::<32>(self as Field) as u32
    }
    fn abs_diff(self, other: u32) -> u32 {
        uabs_diff::<32>(self as Field, other as Field) as u32
    }
    fn div_ceil_or(self, d: u32) -> (u32, bool) {
        let (c, ok) = udiv_ceil::<32>(self as Field, d as Field);
        (c as u32, ok)
    }
}

impl TotalUnsigned for u64 {
    fn widening_mul(self, other: u64) -> (u64, u64) {
        let (lo, hi) = uwide::<64>(self as Field, other as Field);
        (lo as u64, hi as u64)
    }
    fn pow_or(self, exp: u32) -> (u64, bool) {
        let (v, ok) = upow::<64, 7>(self as Field, exp as Field);
        (or_zero(ok, v as u64), ok)
    }
    fn isqrt(self) -> u64 {
        uisqrt::<64>(self as Field) as u64
    }
    fn abs_diff(self, other: u64) -> u64 {
        uabs_diff::<64>(self as Field, other as Field) as u64
    }
    fn div_ceil_or(self, d: u64) -> (u64, bool) {
        let (c, ok) = udiv_ceil::<64>(self as Field, d as Field);
        (c as u64, ok)
    }
}

impl TotalUnsigned for u128 {
    fn widening_mul(self, other: u128) -> (u128, u128) {
        let (lo, hi) = uwide::<128>(self as Field, other as Field);
        (lo as u128, hi as u128)
    }
    fn pow_or(self, exp: u32) -> (u128, bool) {
        let (v, ok) = upow::<128, 8>(self as Field, exp as Field);
        (or_zero(ok, v as u128), ok)
    }
    fn isqrt(self) -> u128 {
        uisqrt::<128>(self as Field) as u128
    }
    fn abs_diff(self, other: u128) -> u128 {
        uabs_diff::<128>(self as Field, other as Field) as u128
    }
    fn div_ceil_or(self, d: u128) -> (u128, bool) {
        let (c, ok) = udiv_ceil::<128>(self as Field, d as Field);
        (c as u128, ok)
    }
}

/// Fused multiply-divide on the native integer types u8..u128 (here) and
/// i8..i64 (signed.nr), with the product formed in the field at double
/// width, so a*b never overflows; only the quotient can, and only when d
/// is small (for |d| >= max(|a|, |b|) it always fits).
/// - mul_div_or(a, b, d): (q, r, ok) with ok = d != 0 and the quotient
///   fits the type; on ok, q = floor(a*b/d) and r = a*b mod d (signed:
///   q truncated toward zero, r with the sign of a*b, like native / and %
///   on the exact product).
/// - mul_div_ceil_or(a, b, d): (c, ok) with c = ceil(a*b/d) and ok =
///   d != 0 and c fits the type.
/// On ok = false every value is 0. For d = 0 the divisor is selected to
/// 1 and the dividend to 0 before the hint runs.
///
/// The u128 impl is the wide gadget, whose constraints differ: see
/// mul_div_wide_or.
///
/// Constraints for u8..u64 (mul_div_or): is_zero(d) (inversion gadget),
/// two selects, and core::mul_div_split::<N, N>: RANGE q_lo and q_hi to N
/// bits each, is_zero(q_hi), RANGE r to N bits, RANGE d1 - r - 1 to N
/// bits, and a*b == (q_lo + q_hi*2^N)*d1 + r. The operands are below 2^N
/// by the type invariant and d1 is in [1, 2^N) by the select, which
/// discharges mul_div_split's preconditions, so no input clamp is
/// needed; every assert is hint-satisfiable and every output determined
/// (see core::constrain_mul_div). q_lo and r are range-checked to N
/// bits, so their casts back to the type are exact, and they are zeroed
/// after the cast. mul_div_ceil_or adds is_zero(r) and
/// core::add_split::<N>(q_lo, r != 0) (its N-bit RANGE on the sum and the
/// carry, hint-satisfiable since both are below 2^N; the carry is the
/// ceiling's overflow).
pub trait TotalMulDiv {
    fn mul_div_or(self, b: Self, d: Self) -> (Self, Self, bool);
    fn mul_div_ceil_or(self, b: Self, d: Self) -> (Self, bool);
}

/// Shared body for the u8..u64 TotalMulDiv impls, on operands below 2^N
/// by the type invariant: (q, r, ok) before zeroing.
fn umul_div<let N: u32>(a: Field, b: Field, d: Field) -> (Field, Field, bool) {
    let nz = !is_zero(d);
    let (q, r, fits) = mul_div_split::<N, N>(select_field(nz, a, 0), b, select_field(nz, d, 1));
    (q, r, nz & fits)
}

/// Shared body of the u128 TotalMulDiv impl, on operands below 2^128 by
/// the type invariant: the wide gadget at N = 128 (split layout), with
/// the divisor selected to 1 and the dividend to 0 when d = 0, before the
/// hint runs. ok = d != 0 and the quotient fits 128 bits (is_zero on the
/// high quotient limb). q_lo gets implied_range::<128> (it is bound below
/// 2^128 by its 64-bit limb split) so its cast is exact; r is
/// range-checked to 128 bits by the gadget.
fn umul_div_wide(a: Field, b: Field, d: Field) -> (Field, Field, bool) {
    let nz = !is_zero(d);
    let (q_lo, q_hi, r) =
        mul_div_wide_split::<128>(select_field(nz, a, 0), b, select_field(nz, d, 1));
    (implied_range::<128>(q_lo), r, nz & is_zero(q_hi))
}

/// ceil from a floor pair: (q + (r != 0), ok & no carry), for q < 2^N
/// (range-checked by the gadget that produced it). add_split::<N> gives
/// the sum range-checked to N bits and its carry.
fn ceil_of<let N: u32>(q: Field, r: Field, ok: bool) -> (Field, bool) {
    let (c, carry) = add_split::<N>(q, !is_zero(r) as Field);
    (c, ok & !carry)
}

impl TotalMulDiv for u8 {
    fn mul_div_or(self, b: u8, d: u8) -> (u8, u8, bool) {
        let (q, r, ok) = umul_div::<8>(self as Field, b as Field, d as Field);
        (or_zero(ok, q as u8), or_zero(ok, r as u8), ok)
    }
    fn mul_div_ceil_or(self, b: u8, d: u8) -> (u8, bool) {
        let (q, r, ok) = umul_div::<8>(self as Field, b as Field, d as Field);
        let (c, ok) = ceil_of::<8>(q, r, ok);
        (or_zero(ok, c as u8), ok)
    }
}

impl TotalMulDiv for u16 {
    fn mul_div_or(self, b: u16, d: u16) -> (u16, u16, bool) {
        let (q, r, ok) = umul_div::<16>(self as Field, b as Field, d as Field);
        (or_zero(ok, q as u16), or_zero(ok, r as u16), ok)
    }
    fn mul_div_ceil_or(self, b: u16, d: u16) -> (u16, bool) {
        let (q, r, ok) = umul_div::<16>(self as Field, b as Field, d as Field);
        let (c, ok) = ceil_of::<16>(q, r, ok);
        (or_zero(ok, c as u16), ok)
    }
}

impl TotalMulDiv for u32 {
    fn mul_div_or(self, b: u32, d: u32) -> (u32, u32, bool) {
        let (q, r, ok) = umul_div::<32>(self as Field, b as Field, d as Field);
        (or_zero(ok, q as u32), or_zero(ok, r as u32), ok)
    }
    fn mul_div_ceil_or(self, b: u32, d: u32) -> (u32, bool) {
        let (q, r, ok) = umul_div::<32>(self as Field, b as Field, d as Field);
        let (c, ok) = ceil_of::<32>(q, r, ok);
        (or_zero(ok, c as u32), ok)
    }
}

impl TotalMulDiv for u64 {
    fn mul_div_or(self, b: u64, d: u64) -> (u64, u64, bool) {
        let (q, r, ok) = umul_div::<64>(self as Field, b as Field, d as Field);
        (or_zero(ok, q as u64), or_zero(ok, r as u64), ok)
    }
    fn mul_div_ceil_or(self, b: u64, d: u64) -> (u64, bool) {
        let (q, r, ok) = umul_div::<64>(self as Field, b as Field, d as Field);
        let (c, ok) = ceil_of::<64>(q, r, ok);
        (or_zero(ok, c as u64), ok)
    }
}

impl TotalMulDiv for u128 {
    fn mul_div_or(self, b: u128, d: u128) -> (u128, u128, bool) {
        let (q, r, ok) = umul_div_wide(self as Field, b as Field, d as Field);
        (or_zero(ok, q as u128), or_zero(ok, r as u128), ok)
    }
    fn mul_div_ceil_or(self, b: u128, d: u128) -> (u128, bool) {
        let (q, r, ok) = umul_div_wide(self as Field, b as Field, d as Field);
        let (c, ok) = ceil_of::<128>(q, r, ok);
        (or_zero(ok, c as u128), ok)
    }
}

mod tests;
mod mul_div_tests;
mod mul_div_wide_tests;
mod hint_tests;
mod unsigned_tests;
