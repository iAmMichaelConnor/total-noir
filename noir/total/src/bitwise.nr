//! Bitwise operations and shifts.
//!
//! Native operators on typed integers:
//! - `&` and `^` lower to the AND and XOR black boxes at the type's bit
//!   width (8 for u8 and i8, 128 for u128). The black box constrains its
//!   inputs to that width, which typed values meet by the type
//!   invariant, and defines its output. Total on typed values.
//! - `|` lowers to !(!a & !b): one AND plus arithmetic definitions. `!`
//!   is the arithmetic definition (2^N - 1) - x. Total.
//! - `<<` and `>>` are NOT total: a shift amount at or above the bit
//!   width fails "attempt to bit-shift with overflow" (u8 << 8, u8 >> 8,
//!   u8 >> 200 and u128 >> 128 all fail). Below the width, `<<` drops
//!   the bits shifted out without failing (255u8 << 7 = 128). For a
//!   shift amount that is not known to be in range, use TotalShift
//!   below on the typed value, or the Field-domain forms.
//!
//! Field domain, all returning (value, ok) with ok determined:
//! - and_bits_or, or_bits_or, xor_bits_or, not_bits_or::<N> for 1 <= N <= 128: clamp
//!   each input to N bits (ok = all inputs in range), cast exactly to
//!   the smallest native type that holds N bits (u8, u16, u32, u64 or
//!   u128), apply the native operator, widen back. The value is 0 when
//!   ok is false.
//! - shl_exact_or, shl_or, shr_or, rotate_left_or, rotate_right_or::<N>
//!   for 1 <= N <= 128: the shift amount s is any Field, flagged when
//!   s >= N. For N <= 16 an eq-scan over j in 0..N gives flags
//!   e_j = (s == j) whose OR is s < N; for N >= 17 the amount is clamped
//!   to K = ceil(log2 N) bits, compared with N, and split into K bits
//!   (amount_split), the cheaper front at each width. Each entry
//!   multiplies the clamped value a1 by 2^s for the left forms or
//!   2^((N - s) mod N) for the right forms, and splits the product at
//!   bit N (mul_pow2 below has the identity and the no-wrap bound for
//!   each width). shl_or drops the bits shifted out, like native <<;
//!   shl_exact_or also flags when any is lost.
//!
//! Typed, trait TotalShift for u8, u16, u32, u64 and u128: shl_or,
//! shl_exact_or and shr_or, with the same contracts as the Field-domain
//! functions of those names. shl_or and shr_or are the total replacements
//! for native << and >>: flagged only on a shift amount at or above the
//! bit width (the one failure the native operators have), with the bits
//! shifted out dropped as native << drops them. shl_exact_or also flags
//! a lost bit.
//!
//! On ok = false every entry here returns 0.
//!
//! Not provided: shifts on signed types.

use crate::arith::{constrain_low_bits, constrain_mul_128, div_128, hint_low_bits, hint_mul_lo_128};
use crate::collections::index_flags_or;
use crate::core::{
    div_split, implied_range, is_zero, lt_bounded, mul_split, mul_split_short, select_field,
    split_128_at, two_pow,
};
use crate::range::clamp_bits_or;
use std::ops::{BitAnd, BitOr, BitXor};
use std::static_assert;

global OP_AND: u32 = 0;
global OP_OR: u32 = 1;
global OP_XOR: u32 = 2;

fn apply<T, let OP: u32>(x: T, y: T) -> T
where
    T: BitAnd + BitOr + BitXor,
{
    if OP == OP_AND {
        x & y
    } else if OP == OP_OR {
        x | y
    } else {
        x ^ y
    }
}

/// The native operator on two values range-checked to N bits, in the
/// smallest native type of at least N bits. The casts are exact (both
/// inputs are below 2^N <= 2^width) and free (the inputs carry an N-bit
/// range check). & | ^ of N-bit values are N-bit, so the widened result
/// is below 2^N.
fn native_op<let N: u32, let OP: u32>(a: Field, b: Field) -> Field {
    if N <= 8 {
        apply::<u8, OP>(a as u8, b as u8) as Field
    } else if N <= 16 {
        apply::<u16, OP>(a as u16, b as u16) as Field
    } else if N <= 32 {
        apply::<u32, OP>(a as u32, b as u32) as Field
    } else if N <= 64 {
        apply::<u64, OP>(a as u64, b as u64) as Field
    } else {
        apply::<u128, OP>(a as u128, b as u128) as Field
    }
}

/// Shared body of and_bits_or, or_bits_or, xor_bits_or. Constraints: two clamps
/// (core, hint-satisfiable for every Field, determined); implied_range
/// on each clamped value (it is below 2^N whenever the clamp's
/// constraints hold, since the clamp's flag is determined); one AND or
/// XOR black box at the native width (inputs in range by the previous
/// range check); arithmetic definitions; the final mask.
fn bitwise<let N: u32, let OP: u32>(a: Field, b: Field) -> (Field, bool) {
    let (a0, oka) = clamp_bits_or::<N>(a);
    let (b0, okb) = clamp_bits_or::<N>(b);
    let a1 = implied_range::<N>(a0);
    let b1 = implied_range::<N>(b0);
    let ok = oka & okb;
    (select_field(ok, native_op::<N, OP>(a1, b1), 0), ok)
}

/// a AND b on N-bit values (1 <= N <= 128); ok = both below 2^N; value 0
/// when ok is false. Constraints as described on the module: clamps,
/// implied range checks, one AND black box. Total; ok determined.
pub fn and_bits_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "and_bits_or: N must be in 1..=128");
    bitwise::<N, OP_AND>(a, b)
}

/// a OR b on N-bit values; same contract and constraints as and_bits_or
/// (the native | is one AND plus arithmetic).
pub fn or_bits_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "or_bits_or: N must be in 1..=128");
    bitwise::<N, OP_OR>(a, b)
}

/// a XOR b on N-bit values; same contract as and_bits_or with one XOR black
/// box.
pub fn xor_bits_or<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "xor_bits_or: N must be in 1..=128");
    bitwise::<N, OP_XOR>(a, b)
}

/// NOT a on N bits: (2^N - 1 - a, ok) with ok = a below 2^N; value 0 when
/// ok is false. Constraints: one clamp; the rest is arithmetic. Total.
pub fn not_bits_or<let N: u32>(a: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "not_bits_or: N must be in 1..=128");
    let (a1, ok) = clamp_bits_or::<N>(a);
    (select_field(ok, two_pow::<N>() - 1 - a1, 0), ok)
}

// ---------------------------------------------------------------------
// Field-domain shifts and rotations
// ---------------------------------------------------------------------

/// The exponent a shift amount j selects: j for the left forms, and
/// (N - j) mod N for the right forms (a right rotation by j is a left
/// rotation by N - j). A compile-time constant for constant j.
fn exponent<let N: u32>(j: u32, right: bool) -> u32 {
    if right {
        (N - j) % N
    } else {
        j
    }
}

/// Eq-scan amount front, used for N <= 16: (pw, s == 0, s < N) with
/// pw = 2^exponent(s) when s < N and 0 otherwise. Constraints:
/// collections::index_flags_or::<N>(s) (N eq gadgets and an OR chain,
/// hint-satisfiable for every Field s, determined; at most one flag is
/// set and their OR is s < N); pw is a linear combination of the flags
/// with constant coefficients 2^exponent(j) <= 2^(N - 1). No failure
/// source of its own.
fn amount_scan<let N: u32>(s: Field, right: bool) -> (Field, bool, bool) {
    let (flags, ok) = index_flags_or::<N>(s);
    let mut pw: Field = 0;
    let mut t: Field = 1;
    let mut table = [0; N];
    for j in 0..N {
        table[j] = t;
        t *= 2;
    }
    for j in 0..N {
        pw += (flags[j] as Field) * table[exponent::<N>(j, right)];
    }
    (pw, flags[0], ok)
}

/// 2^K as a u32 constant, for K <= 7.
fn pow2_u32<let K: u32>() -> u32 {
    let mut r: u32 = 1;
    for _ in 0..K {
        r = r * 2;
    }
    r
}

/// Log-split amount front for a Field amount, used for N >= 17, with
/// K = ceil(log2 N) (so N <= 2^K <= 2N): returns (p0, p1, s == 0, s < N)
/// where p0 + p1 * 2^64 = 2^e for e = exponent(s) when s < N, and both
/// are 0 otherwise; p1 = 0 for N < 128, and p0, p1 < 2^64 for N = 128.
///
/// Constraints, in order:
/// 1. (s1, in_k) = range::clamp_bits_or::<K>(s): canonical limbs and one
///    split, hint-satisfiable for every Field (p - 1 included), with
///    in_k = (s < 2^K) and s1 = s or 0, determined. This is what carries
///    the split over to a Field amount: the typed forms' range on
///    (s - low) / 2^K (constrain_shift_amount) presumes s < 2^128 and
///    would be input-falsifiable for a larger Field.
/// 2. When N < 2^K, ok = in_k & core::lt_bounded::<K>(s1, N): both
///    operands below 2^K, its precondition, so hint-satisfiable and
///    determined. When N = 2^K, ok = in_k.
/// 3. s0 = is_zero(s1) (the inversion gadget, determined).
/// 4. e = s1 for the left forms; e = select(ok & !s0, N - s1, 0) for the
///    right forms, in [1, N) when selected, so e < 2^K either way.
/// 5. K hinted bits of e (arith::hint_low_bits, trap-free for every
///    argument) pinned by arith::constrain_low_bits::<K> (booleanity from
///    the [bool; K] return type and sum bits[i] * 2^i == e): e < 2^K, so
///    the bits exist, are unique and the sum cannot wrap.
/// 6. ok * prod_i select(bits[i], 2^(2^i), 1) (bit_pow): 2^e, or 0 when
///    ok is false. For N = 128 bits 0..5 give 2^(e mod 64), and bit 6
///    moves it to the high limb.
/// Determined: every step is a function of determined values.
fn amount_split<let N: u32, let K: u32>(s: Field, right: bool) -> (Field, Field, bool, bool) {
    let (s1, in_k) = clamp_bits_or::<K>(s);
    let ok = if N == pow2_u32::<K>() {
        in_k
    } else {
        in_k & lt_bounded::<K>(s1, N as Field)
    };
    let s0 = is_zero(s1);
    let e = if right {
        select_field(ok & !s0, (N as Field) - s1, 0)
    } else {
        s1
    };
    // Safety: constrain_low_bits pins the bits (step 5 above).
    let bits = unsafe { hint_low_bits::<K>(e) };
    constrain_low_bits::<K>(e, bits);
    if N == 128 {
        let low = bit_pow::<K, 6>(bits, ok);
        let p1 = (bits[6 % K] as Field) * low;
        (low - p1, p1, s0, ok)
    } else {
        (bit_pow::<K, K>(bits, ok), 0, s0, ok)
    }
}

/// amount_split with K = ceil(log2 N), chosen at compile time.
fn amount_log<let N: u32>(s: Field, right: bool) -> (Field, Field, bool, bool) {
    if N <= 32 {
        amount_split::<N, 5>(s, right)
    } else if N <= 64 {
        amount_split::<N, 6>(s, right)
    } else {
        amount_split::<N, 7>(s, right)
    }
}

/// a1 * 2^e split at bit N, for the multiplier 2^e = p0 + p1 * 2^64
/// (or 0) from an amount front: returns (lo, hi) with the integer
/// identity a1 * 2^e = lo + hi * 2^N, 0 <= lo < 2^N, and hi < 2^e <=
/// 2^(N - 1). PRECONDITIONS: a1 < 2^N (the caller's clamp), e <= N - 1,
/// p1 = 0 for N < 128 and p0, p1 < 2^64 for N = 128 (the fronts above).
/// std::as_witness makes the multiplier (or each limb) one witness, so
/// the products below have one term.
///
/// The split gadget, chosen at compile time by N:
/// - N <= 126: core::mul_split::<N> (RANGE lo and hi to N bits,
///   a1*2^e == lo + hi*2^N). No wrap: both sides are below 2^(2N) <= 2^252.
/// - N = 127: core::mul_split_short::<127> (RANGE lo to 127 bits, hi to 126
///   bits, the same equation). No wrap: a1*2^e < 2^(127 + 126) = 2^253 and
///   lo + hi*2^127 < 2^253, both below p. mul_split's 127-bit range on hi
///   would let lo + hi*2^127 reach 2^254 > p.
/// - N = 128: a1*2^e reaches 2^255 > p, so no single field equation pins
///   it. a1 is split into 64-bit limbs (core::split_128_at::<64>: two
///   64-bit RANGEs and a1 == a0 + ah*2^64, hint-satisfiable since
///   a1 < 2^128), and arith::constrain_mul_128 emits a 128-bit RANGE on the
///   hinted lo and a 70-bit RANGE on the carry
///   c = (a0*p0 + (a0*p1 + ah*p0)*2^64 - lo) / 2^128, and returns
///   hi = c + ah*p1. Its argument: the column sum is below 2^194 and
///   c*2^128 below 2^198, so the carry equation is an integer one (the
///   difference is below 2^199 < p), which makes lo = a1*2^e mod 2^128
///   and hi = floor(a1*2^e / 2^128) as integers.
/// Every gadget is hint-satisfiable for every input under the
/// preconditions, and lo and hi are determined.
fn mul_pow2<let N: u32>(a1: Field, p0: Field, p1: Field) -> (Field, Field) {
    std::as_witness(p0);
    if N == 128 {
        std::as_witness(p1);
        let (a0, ah) = split_128_at::<64>(a1);
        // Safety: constrain_mul_128 pins lo to a1*2^e mod 2^128 (its
        // 128-bit range and the 70-bit carry).
        let lo = unsafe { hint_mul_lo_128(a0, ah, p0, p1) };
        let hi = constrain_mul_128(a0, ah, p0, p1, lo);
        (lo, hi)
    } else if N == 127 {
        // The literal width (not N - 1 arithmetic on N) keeps an
        // out-of-range N reporting the entry's own static_assert.
        mul_split_short::<127>(a1, p0)
    } else {
        mul_split::<N>(a1, p0)
    }
}

/// Shared front of the shifts: clamp a to N bits, read the amount, and
/// split a1 * 2^exponent(s) at bit N. Returns (lo, hi, s == 0,
/// a_in_range, s_in_range). Constraints: clamp_bits_or::<N> on a
/// (hint-satisfiable for every Field, determined); the amount front,
/// amount_scan for N <= 16 and amount_split for N >= 17 (the cheaper at
/// each width, measured with bb 6.0.0 as the gates one more shl_or adds
/// to a circuit: 74 against 101 at N = 8, 102 against 104 at N = 16, 155
/// against 108 at N = 32, 265 against 115 at N = 64, 480 against 119 at
/// N = 128); mul_pow2. With s >= N the multiplier is 0, so lo = hi = 0.
fn shift<let N: u32>(a: Field, s: Field, right: bool) -> (Field, Field, bool, bool, bool) {
    let (a1, oka) = clamp_bits_or::<N>(a);
    let (p0, p1, s0, oks) = if N <= 16 {
        let (pw, s0, oks) = amount_scan::<N>(s, right);
        (pw, 0, s0, oks)
    } else {
        amount_log::<N>(s, right)
    };
    let (lo, hi) = mul_pow2::<N>(a1, p0, p1);
    (lo, hi, s0, oka, oks)
}

/// a << s on N-bit values (1 <= N <= 128) with no bit lost: value
/// (a << s), ok = a below 2^N, s < N, and the bits shifted out are all
/// zero. On ok = false the value is 0.
/// Integer identity: a1 * 2^s = lo + hi * 2^N; lo is the value and hi
/// holds the bits shifted out.
/// Constraints: shift (clamp, amount front, mul_pow2 with multiplier
/// 2^s); is_zero on hi; one select. Determined.
pub fn shl_exact_or<let N: u32>(a: Field, s: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "shl_exact_or: N must be in 1..=128");
    let (lo, hi, _, oka, oks) = shift::<N>(a, s, false);
    let ok = oka & oks & is_zero(hi);
    (select_field(ok, lo, 0), ok)
}

/// a << s dropping the bits shifted out, like native << below the width:
/// value (a << s) mod 2^N; ok = a below 2^N and s < N; value 0 when ok is
/// false. Same constraints as shl_exact_or without the is_zero and the
/// select (lo is already 0 when ok is false).
pub fn shl_or<let N: u32>(a: Field, s: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "shl_or: N must be in 1..=128");
    let (lo, _, _, oka, oks) = shift::<N>(a, s, false);
    (lo, oka & oks)
}

/// a >> s on N-bit values (1 <= N <= 128): value floor(a / 2^s);
/// ok = a below 2^N and s < N; value 0 when ok is false.
/// Integer identity: for 1 <= s < N, a1 * 2^(N - s) = lo + hi * 2^N with
/// hi = floor(a1 / 2^s), so hi is the value. For s = 0 the multiplier is
/// 2^0 = 1, so lo = a1 and hi = 0, and the value hi + [s == 0]*lo is a1.
/// For s >= N both parts are 0.
/// Constraints: shift (clamp, amount front, mul_pow2 with multiplier
/// 2^((N - s) mod N)) and one product. No division, so no divisor needs
/// selecting. Determined.
pub fn shr_or<let N: u32>(a: Field, s: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "shr_or: N must be in 1..=128");
    let (lo, hi, s0, oka, oks) = shift::<N>(a, s, true);
    (hi + (s0 as Field) * lo, oka & oks)
}

/// Rotate left by s on N bits (1 <= N <= 128): ok = a below 2^N and
/// s < N; value 0 when ok is false.
/// Integer identity: a1 * 2^s = lo + hi * 2^N, where lo holds the bits
/// that stay (its low s bits are zero) and hi < 2^s the bits shifted out,
/// so lo + hi < 2^N is the rotation. Same constraints as shl_or.
/// Determined.
pub fn rotate_left_or<let N: u32>(a: Field, s: Field) -> (Field, bool) {
    static_assert(
        (N >= 1) & (N <= 128),
        "rotate_left_or: N must be in 1..=128",
    );
    let (lo, hi, _, oka, oks) = shift::<N>(a, s, false);
    (lo + hi, oka & oks)
}

/// Rotate right by s on N bits (1 <= N <= 128): rotate left by
/// (N - s) mod N, the same product as shr_or. ok = a below 2^N and s < N;
/// value 0 when ok is false. Same constraints as shr_or without the
/// product. Determined.
pub fn rotate_right_or<let N: u32>(a: Field, s: Field) -> (Field, bool) {
    static_assert(
        (N >= 1) & (N <= 128),
        "rotate_right_or: N must be in 1..=128",
    );
    let (lo, hi, _, oka, oks) = shift::<N>(a, s, true);
    (lo + hi, oka & oks)
}

// ---------------------------------------------------------------------
// Typed shifts
// ---------------------------------------------------------------------

/// Total replacements for native << and >> on the unsigned types, with
/// the shift amount of the same type as the native operators take it.
/// shl_or and shr_or return (value, ok) with ok = s below the bit width
/// N, the only case in which the native operator fails, and on ok the
/// native result: shl_or drops the bits shifted out, as native << does.
/// shl_exact_or has ok = s < N and no set bit shifted out, so on ok its
/// value is the exact product a * 2^s. On ok = false every method returns
/// 0. The same names in the Field domain (shl_or, shl_exact_or, shr_or)
/// have the same contracts.
///
/// The shift amount is split as s = low + rest * 2^K with K = log2(N),
/// low < 2^K from K hinted bits, and rest a linear combination
/// (s - low) / 2^K with a range check (constrain_shift_amount); then
/// ok = (rest == 0) and 2^low is a product of K selects. This costs a few
/// dozen gates where an eq-scan of s would cost N equality gadgets.
pub trait TotalShift {
    /// a << s dropping the bits shifted out; ok = s < N.
    fn shl_or(self, s: Self) -> (Self, bool);
    /// a << s with no bit lost; ok = s < N and (a << s) >> s == a.
    fn shl_exact_or(self, s: Self) -> (Self, bool);
    /// a >> s; ok = s < N.
    fn shr_or(self, s: Self) -> (Self, bool);
}

/// Constraint half of the shift-amount split, split out so tests can feed
/// wrong hints. For s < 2^W (PRECONDITION: the type invariant of the
/// shift amount, W <= 128) and hinted bits, with low = sum bits[i]*2^i:
/// 1. booleanity of each bit (the compiler's type constraint on the
///    hint's [bool; K] return);
/// 2. rest = (s - low) / 2^K, a field multiple of the constant 1/2^K (a
///    linear combination, not a witness of its own), and RANGE rest to
///    R bits, with R >= W - K rounded up to a multiple of 14 (core's
///    width rule).
/// Returns ok = is_zero(rest) (the inversion gadget).
/// Integer identity: s = low + rest * 2^K with 0 <= low < 2^K.
/// Hint-satisfiable: the honest bits are the low K bits of s, so rest is
/// floor(s / 2^K) < 2^(W - K) <= 2^R.
/// Determined (no wrap): rest*2^K = s - low holds in the field with
/// rest*2^K in [0, 2^(R + K)) and s - low in (-2^K, 2^W), so the two sides
/// differ by less than 2^(R + K + 1) <= 2^134 < p and the equality is an
/// integer one. Euclidean division by 2^K then makes (low, rest) unique,
/// and binary representation makes the bits unique; ok = (s < 2^K).
/// Load-bearing: without the range, bits of any low' != low pass with the
/// non-integer rest' = (s - low') / 2^K, and the flag could be dropped.
pub(crate) fn constrain_shift_amount<let K: u32, let R: u32>(s: Field, bits: [bool; K]) -> bool {
    let mut low: Field = 0;
    let mut pw: Field = 1;
    for i in 0..K {
        low += (bits[i] as Field) * pw;
        pw *= 2;
    }
    let rest = (s - low) * (1 / two_pow::<K>());
    rest.assert_max_bit_size::<R>();
    is_zero(rest)
}

/// The low K bits of a typed shift amount and the flag s < 2^K.
/// PRECONDITION: s < 2^W with R >= W - K (the caller's type). The hint
/// is arith::hint_low_bits (remainder and quotient by the constant 2 on
/// the truncated value): trap-free for every argument and exact for
/// s < 2^128.
fn amount<let K: u32, let R: u32>(s: Field) -> ([bool; K], bool) {
    // Safety: constrain_shift_amount pins the bits (its argument).
    let bits = unsafe { hint_low_bits::<K>(s) };
    let ok = constrain_shift_amount::<K, R>(s, bits);
    (bits, ok)
}

/// ok * prod_{i < L} (bits[i] ? 2^(2^i) : 1): 2^(low L bits) when ok, 0
/// otherwise. L - 1 products of selects with constant arms; no failure
/// source.
fn bit_pow<let K: u32, let L: u32>(bits: [bool; K], ok: bool) -> Field {
    let mut p = ok as Field;
    let mut f: Field = 2;
    for i in 0..L {
        p = p * select_field(bits[i], f, 1);
        f = f * f;
    }
    p
}

/// a << s for a < 2^N and a shift amount s < 2^N of the same type
/// (N = 2^K <= 64): (lo, hi, ok) with a * 2^s = lo + hi * 2^N when ok,
/// and lo = hi = 0 otherwise. Constraints: the amount split, then
/// core::mul_split::<N>(a, 2^s or 0), whose preconditions hold (a < 2^N
/// by the type, the power at most 2^(N - 1)). lo carries its N-bit
/// RANGE, so the caller's cast is exact.
fn ushl<let N: u32, let K: u32, let R: u32>(a: Field, s: Field) -> (Field, Field, bool) {
    let (bits, ok) = amount::<K, R>(s);
    let (lo, hi) = mul_split::<N>(a, bit_pow::<K, K>(bits, ok));
    (lo, hi, ok)
}

/// shl_exact_or from the parts of a left shift on N-bit values:
/// ok' = ok & (hi == 0) (one inversion gadget), value select(ok', lo, 0).
/// The value is lo (below 2^N by its RANGE) or 0, so implied_range::<N>
/// holds for every satisfying witness and makes the caller's cast exact.
fn exact<let N: u32>(lo: Field, hi: Field, ok: bool) -> (Field, bool) {
    let ok2 = ok & is_zero(hi);
    (implied_range::<N>(select_field(ok2, lo, 0)), ok2)
}

/// a >> s for the same types: (q, ok). The divisor is 2^s on ok and 1
/// otherwise, and the dividend is 0 when ok is false, both selected
/// before the division hint runs. Constraints: the amount split, then
/// core::div_split::<N> (preconditions: dividend < 2^N, divisor in
/// [1, 2^(N - 1)]). q carries its N-bit RANGE, so the cast is exact.
fn ushr<let N: u32, let K: u32, let R: u32>(a: Field, s: Field) -> (Field, bool) {
    let (bits, ok) = amount::<K, R>(s);
    let d = bit_pow::<K, K>(bits, ok) + 1 - (ok as Field);
    let (q, _) = div_split::<N>(select_field(ok, a, 0), d);
    (q, ok)
}

/// The u128 shift amount: (p0, p1, ok) with p0 + p1*2^64 = 2^s when
/// s < 128 and 0 otherwise, p0, p1 < 2^64. Bit 6 of s picks the limb.
/// Constraints: the amount split with K = 7, R = 126 (>= 121); bool and
/// select arithmetic.
fn u128_amount(s: Field) -> (Field, Field, bool) {
    let (bits, ok) = amount::<7, 126>(s);
    let low = bit_pow::<7, 6>(bits, ok);
    let p1 = (bits[6] as Field) * low;
    (low - p1, p1, ok)
}

impl TotalShift for u8 {
    fn shl_or(self, s: u8) -> (u8, bool) {
        let (v, _, ok) = ushl::<8, 3, 14>(self as Field, s as Field);
        (v as u8, ok)
    }
    fn shl_exact_or(self, s: u8) -> (u8, bool) {
        let (lo, hi, ok) = ushl::<8, 3, 14>(self as Field, s as Field);
        let (v, ok) = exact::<8>(lo, hi, ok);
        (v as u8, ok)
    }
    fn shr_or(self, s: u8) -> (u8, bool) {
        let (v, ok) = ushr::<8, 3, 14>(self as Field, s as Field);
        (v as u8, ok)
    }
}

impl TotalShift for u16 {
    fn shl_or(self, s: u16) -> (u16, bool) {
        let (v, _, ok) = ushl::<16, 4, 14>(self as Field, s as Field);
        (v as u16, ok)
    }
    fn shl_exact_or(self, s: u16) -> (u16, bool) {
        let (lo, hi, ok) = ushl::<16, 4, 14>(self as Field, s as Field);
        let (v, ok) = exact::<16>(lo, hi, ok);
        (v as u16, ok)
    }
    fn shr_or(self, s: u16) -> (u16, bool) {
        let (v, ok) = ushr::<16, 4, 14>(self as Field, s as Field);
        (v as u16, ok)
    }
}

impl TotalShift for u32 {
    fn shl_or(self, s: u32) -> (u32, bool) {
        let (v, _, ok) = ushl::<32, 5, 28>(self as Field, s as Field);
        (v as u32, ok)
    }
    fn shl_exact_or(self, s: u32) -> (u32, bool) {
        let (lo, hi, ok) = ushl::<32, 5, 28>(self as Field, s as Field);
        let (v, ok) = exact::<32>(lo, hi, ok);
        (v as u32, ok)
    }
    fn shr_or(self, s: u32) -> (u32, bool) {
        let (v, ok) = ushr::<32, 5, 28>(self as Field, s as Field);
        (v as u32, ok)
    }
}

impl TotalShift for u64 {
    fn shl_or(self, s: u64) -> (u64, bool) {
        let (v, _, ok) = ushl::<64, 6, 70>(self as Field, s as Field);
        (v as u64, ok)
    }
    fn shl_exact_or(self, s: u64) -> (u64, bool) {
        let (lo, hi, ok) = ushl::<64, 6, 70>(self as Field, s as Field);
        let (v, ok) = exact::<64>(lo, hi, ok);
        (v as u64, ok)
    }
    fn shr_or(self, s: u64) -> (u64, bool) {
        let (v, ok) = ushr::<64, 6, 70>(self as Field, s as Field);
        (v as u64, ok)
    }
}

/// a * 2^s for a u128 a: (lo, hi, ok) with lo = a*2^s mod 2^128 and
/// hi = floor(a*2^s / 2^128) when ok, both 0 otherwise. a*2^s reaches
/// 2^255 > p, so a is split into 64-bit limbs (core::split_128_at::<64>,
/// hint-satisfiable since a < 2^128 by the type) and
/// arith::constrain_mul_128 runs against the power's limbs from
/// u128_amount: lo is range-checked to 128 bits, so its cast is exact (the
/// argument is at mul_pow2).
fn u128_shl(a: u128, s: u128) -> (Field, Field, bool) {
    let (p0, p1, ok) = u128_amount(s as Field);
    let (a0, ah) = split_128_at::<64>(a as Field);
    // Safety: constrain_mul_128 pins lo to a*2^s mod 2^128.
    let lo = unsafe { hint_mul_lo_128(a0, ah, p0, p1) };
    let hi = constrain_mul_128(a0, ah, p0, p1, lo);
    (lo, hi, ok)
}

/// u128: shl_or and shl_exact_or through u128_shl. shr_or runs
/// arith::div_128 (the 128-bit Euclidean division: 64-bit RANGEs on the
/// quotient limbs, 128-bit RANGEs on r and d - r - 1, a 70-bit carry, and
/// the identity) with the divisor 2^s on ok and 1 otherwise and the
/// dividend 0 when ok is false, both selected before the hint runs. The
/// quotient is below 2^128 by its limb ranges, so implied_range::<128>
/// before its cast holds for every satisfying witness.
impl TotalShift for u128 {
    fn shl_or(self, s: u128) -> (u128, bool) {
        let (lo, _, ok) = u128_shl(self, s);
        (lo as u128, ok)
    }
    fn shl_exact_or(self, s: u128) -> (u128, bool) {
        let (lo, hi, ok) = u128_shl(self, s);
        let (v, ok) = exact::<128>(lo, hi, ok);
        (v as u128, ok)
    }
    fn shr_or(self, s: u128) -> (u128, bool) {
        let (p0, p1, ok) = u128_amount(s as Field);
        let d = p0 + p1 * two_pow::<64>() + 1 - (ok as Field);
        let (q, _) = div_128(select_field(ok, self as Field, 0), d);
        (implied_range::<128>(q) as u128, ok)
    }
}

mod tests {
    use crate::arith::{constrain_low_bits, constrain_mul_128};
    use crate::core::{two_pow, TWO_POW_128, U128_MAX_FIELD};
    use crate::test_support::wit;
    use super::{
        and_bits_or, constrain_shift_amount, not_bits_or, or_bits_or, rotate_left_or,
        rotate_right_or, shl_exact_or, shl_or, shr_or, TotalShift, xor_bits_or,
    };
    use std::ops::{Shl, Shr};

    fn bounds<let N: u32>() -> [Field; 6] {
        let m = two_pow::<N>();
        [0, 1, m - 1, m, m + 1, 0 - 1]
    }

    fn check_logic<let N: u32>() {
        let m = two_pow::<N>();
        let vals = bounds::<N>();
        // a mixed bit pattern below 2^N, to exercise all three operators
        let mixed = ((0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5 as u128) >> (128 - N as u128)) as Field;
        let mut xs = [0; 7];
        for k in 0..6 {
            xs[k] = vals[k];
        }
        xs[6] = mixed;
        for i in 0..7 {
            let a = xs[i];
            let oka = a.lt(m);
            let ai = if oka { a as u128 } else { 0 };
            let (nv, nok) = not_bits_or::<N>(wit(a));
            assert_eq(nok, oka);
            assert_eq(nv, if oka { m - 1 - a } else { 0 });
            for j in 0..7 {
                let b = xs[j];
                let ok = oka & b.lt(m);
                let bi = if b.lt(m) { b as u128 } else { 0 };
                assert_eq(
                    and_bits_or::<N>(wit(a), wit(b)),
                    (if ok { (ai & bi) as Field } else { 0 }, ok),
                );
                assert_eq(
                    or_bits_or::<N>(wit(a), wit(b)),
                    (if ok { (ai | bi) as Field } else { 0 }, ok),
                );
                assert_eq(
                    xor_bits_or::<N>(wit(a), wit(b)),
                    (if ok { (ai ^ bi) as Field } else { 0 }, ok),
                );
            }
        }
    }

    #[test]
    fn logic_small_widths() {
        check_logic::<1>();
        check_logic::<5>();
        check_logic::<8>();
        check_logic::<16>();
    }

    #[test]
    fn logic_large_widths() {
        check_logic::<32>();
        check_logic::<64>();
        check_logic::<100>();
        check_logic::<128>();
    }

    #[test]
    fn logic_fixed_patterns() {
        assert_eq(and_bits_or::<16>(wit(0xf0f0), wit(0x0ff0)), (0x00f0, true));
        assert_eq(or_bits_or::<16>(wit(0xf0f0), wit(0x0ff0)), (0xfff0, true));
        assert_eq(xor_bits_or::<16>(wit(0xf0f0), wit(0x0ff0)), (0xff00, true));
        assert_eq(not_bits_or::<16>(wit(0xf0f0)), (0x0f0f, true));
        let max = two_pow::<128>() - 1;
        assert_eq(
            and_bits_or::<128>(wit(max), wit(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0)),
            (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, true),
        );
        assert_eq(xor_bits_or::<128>(wit(max), wit(max)), (0, true));
        assert_eq(not_bits_or::<128>(wit(max)), (0, true));
        assert_eq(not_bits_or::<128>(wit(0)), (max, true));
        assert_eq(and_bits_or::<128>(wit(two_pow::<128>()), wit(1)), (0, false));
        // a value in range for u8 but out of range for N = 5
        assert_eq(or_bits_or::<5>(wit(32), wit(1)), (0, false));
    }

    /// Shift reference on N <= 128 bits through native u128 with constant
    /// shift amounts from `amounts` (each below N); also checks the
    /// out-of-range shift amounts N, N + 1, 255 and p - 1.
    fn check_shift_amounts<let N: u32, let K: u32>(amounts: [u32; K]) {
        let m = two_pow::<N>();
        let mask = (m - 1) as u128;
        let vals = bounds::<N>();
        let mixed = ((0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a as u128) >> (128 - N as u128)) as Field;
        let mut xs = [0; 7];
        for k in 0..6 {
            xs[k] = vals[k];
        }
        xs[6] = mixed;
        for i in 0..7 {
            let a = xs[i];
            let oka = a.lt(m);
            let ai = if oka { a as u128 } else { 0 };
            for t in 0..K {
                let s = amounts[t];
                let lo = ((ai << (s as u128)) & mask) as Field;
                let hi = if s == 0 {
                    0
                } else {
                    (ai >> ((N - s) as u128)) as Field
                };
                let sf = s as Field;
                let exact_ok = oka & (hi == 0);
                assert_eq(
                    shl_exact_or::<N>(wit(a), wit(sf)),
                    (if exact_ok { lo } else { 0 }, exact_ok),
                );
                assert_eq(shl_or::<N>(wit(a), wit(sf)), (lo, oka));
                assert_eq(shr_or::<N>(wit(a), wit(sf)), ((ai >> (s as u128)) as Field, oka));
                assert_eq(rotate_left_or::<N>(wit(a), wit(sf)), (lo + hi, oka));
                let back = (N - s) % N;
                let lo_r = ((ai << (back as u128)) & mask) as Field;
                let hi_r = if back == 0 {
                    0
                } else {
                    (ai >> ((N - back) as u128)) as Field
                };
                assert_eq(rotate_right_or::<N>(wit(a), wit(sf)), (lo_r + hi_r, oka));
            }
            // shift amounts at and beyond the width, and p - 1
            let bad: [Field; 4] = [N as Field, (N + 1) as Field, 255, 0 - 1];
            for k in 0..4 {
                let s = bad[k];
                assert_eq(shl_exact_or::<N>(wit(a), wit(s)), (0, false));
                assert_eq(shl_or::<N>(wit(a), wit(s)), (0, false));
                assert_eq(shr_or::<N>(wit(a), wit(s)), (0, false));
                assert_eq(rotate_left_or::<N>(wit(a), wit(s)), (0, false));
                assert_eq(rotate_right_or::<N>(wit(a), wit(s)), (0, false));
            }
        }
    }

    /// check_shift_amounts over every amount 0..N.
    fn check_shifts<let N: u32>() {
        let mut all = [0; N];
        for s in 0..N {
            all[s] = s;
        }
        check_shift_amounts::<N, N>(all);
    }

    #[test]
    fn shifts_width_1_and_8() {
        check_shifts::<1>();
        check_shifts::<8>();
    }

    #[test]
    fn shifts_width_13_and_16() {
        check_shifts::<13>();
        check_shifts::<16>();
    }

    // Widths 17 and up take the log-split amount front.

    #[test]
    fn shifts_width_17_and_20() {
        check_shifts::<17>();
        check_shifts::<20>();
    }

    #[test]
    fn shifts_width_32_and_64_edges() {
        check_shift_amounts::<32, 6>([0, 1, 15, 16, 30, 31]);
        check_shift_amounts::<64, 6>([0, 1, 31, 32, 33, 63]);
    }

    #[test]
    fn log_split_amounts_between_n_and_the_next_power_of_two() {
        // N = 20 splits the amount in 5 bits: 20..31 fit the bits but not N
        for s in [20, 21, 31, 32, 33] {
            assert_eq(shl_or::<20>(wit(1), wit(s)), (0, false));
            assert_eq(shl_exact_or::<20>(wit(1), wit(s)), (0, false));
            assert_eq(shr_or::<20>(wit(1), wit(s)), (0, false));
            assert_eq(rotate_left_or::<20>(wit(1), wit(s)), (0, false));
            assert_eq(rotate_right_or::<20>(wit(1), wit(s)), (0, false));
        }
        assert_eq(shl_or::<20>(wit(1), wit(19)), (0x80000, true));
        assert_eq(rotate_right_or::<20>(wit(1), wit(19)), (2, true));
        assert_eq(shr_or::<20>(wit(0xfffff), wit(19)), (1, true));
        // N = 100 in 7 bits: 100..127 are out of range, as are 128 and p - 1
        for s in [100, 101, 127, 128, TWO_POW_128, 0 - 1] {
            assert_eq(rotate_left_or::<100>(wit(1), wit(s)), (0, false));
            assert_eq(shr_or::<100>(wit(1), wit(s)), (0, false));
        }
        assert_eq(rotate_left_or::<100>(wit(two_pow::<99>()), wit(1)), (1, true));
        assert_eq(rotate_right_or::<100>(wit(1), wit(99)), (2, true));
        assert_eq(shr_or::<100>(wit(two_pow::<100>() - 1), wit(99)), (1, true));
    }

    // Wrong hints for the bit split of the log front: e = 22 in 5 bits.

    #[test]
    fn amount_bits_honest_accepted() {
        constrain_low_bits::<5>(wit(22), wit([false, true, true, false, true]));
    }

    #[test(should_fail)]
    fn amount_bits_off_by_one_rejected() {
        constrain_low_bits::<5>(22, [true, true, true, false, true]);
    }

    #[test(should_fail)]
    fn amount_bits_of_another_amount_rejected() {
        constrain_low_bits::<5>(22, [false, true, true, false, false]);
    }

    #[test]
    fn shifts_width_126_edges() {
        check_shift_amounts::<126, 6>([0, 1, 62, 63, 64, 125]);
    }

    #[test]
    fn shifts_width_127_edges() {
        check_shift_amounts::<127, 7>([0, 1, 63, 64, 65, 125, 126]);
    }

    #[test]
    fn shifts_width_128_edges() {
        check_shift_amounts::<128, 8>([0, 1, 63, 64, 65, 126, 127, 100]);
    }

    #[test]
    fn shift_edges_wide() {
        let m64 = two_pow::<64>();
        assert_eq(shl_exact_or::<64>(wit(1), wit(63)), (two_pow::<63>(), true));
        assert_eq(shl_exact_or::<64>(wit(2), wit(63)), (0, false));
        assert_eq(shl_or::<64>(wit(m64 - 1), wit(63)), (two_pow::<63>(), true));
        assert_eq(shr_or::<64>(wit(m64 - 1), wit(63)), (1, true));
        assert_eq(shr_or::<64>(wit(m64 - 1), wit(64)), (0, false));
        assert_eq(rotate_left_or::<64>(wit(two_pow::<63>()), wit(1)), (1, true));
        assert_eq(rotate_right_or::<64>(wit(1), wit(1)), (two_pow::<63>(), true));
        assert_eq(rotate_right_or::<64>(wit(0x8001), wit(0)), (0x8001, true));
        assert_eq(shl_exact_or::<64>(wit(m64), wit(0)), (0, false));
        let m126 = two_pow::<126>();
        assert_eq(shl_exact_or::<126>(wit(1), wit(125)), (two_pow::<125>(), true));
        assert_eq(shl_exact_or::<126>(wit(m126 - 1), wit(0)), (m126 - 1, true));
        assert_eq(shl_exact_or::<126>(wit(m126 - 1), wit(1)), (0, false));
        assert_eq(shr_or::<126>(wit(m126 - 1), wit(125)), (1, true));
        assert_eq(rotate_left_or::<126>(wit(m126 - 2), wit(1)), (m126 - 3, true));
        assert_eq(shr_or::<126>(wit(m126 - 1), wit(126)), (0, false));
        assert_eq(shl_exact_or::<126>(wit(0 - 1), wit(3)), (0, false));
    }

    #[test]
    fn shift_edges_127_and_128() {
        let max = U128_MAX_FIELD;
        let m127 = two_pow::<127>();
        // the largest products each width allows: (2^N - 1) * 2^(N - 1)
        assert_eq(shl_or::<128>(wit(max), wit(127)), (m127, true));
        assert_eq(shl_exact_or::<128>(wit(max), wit(127)), (0, false));
        assert_eq(rotate_left_or::<128>(wit(max), wit(127)), (max, true));
        assert_eq(shl_or::<127>(wit(m127 - 1), wit(126)), (two_pow::<126>(), true));
        assert_eq(rotate_left_or::<127>(wit(m127 - 1), wit(126)), (m127 - 1, true));
        // shift 0, 127 and 128, huge amounts, values 0, 1 and 2^128 - 1
        assert_eq(shl_exact_or::<128>(wit(1), wit(127)), (m127, true));
        assert_eq(shl_exact_or::<128>(wit(1), wit(128)), (0, false));
        assert_eq(shl_exact_or::<128>(wit(0), wit(127)), (0, true));
        assert_eq(shl_exact_or::<128>(wit(max), wit(0)), (max, true));
        assert_eq(shl_exact_or::<128>(wit(max), wit(1)), (0, false));
        assert_eq(shr_or::<128>(wit(max), wit(0)), (max, true));
        assert_eq(shr_or::<128>(wit(max), wit(127)), (1, true));
        assert_eq(shr_or::<128>(wit(max), wit(128)), (0, false));
        assert_eq(shr_or::<128>(wit(max), wit(255)), (0, false));
        assert_eq(shr_or::<128>(wit(max), wit(max)), (0, false));
        assert_eq(shr_or::<128>(wit(1), wit(0)), (1, true));
        assert_eq(shr_or::<128>(wit(1), wit(1)), (0, true));
        assert_eq(shr_or::<128>(wit(0), wit(127)), (0, true));
        assert_eq(rotate_right_or::<128>(wit(1), wit(1)), (m127, true));
        assert_eq(rotate_right_or::<128>(wit(1), wit(127)), (2, true));
        assert_eq(rotate_right_or::<128>(wit(max), wit(64)), (max, true));
        assert_eq(rotate_left_or::<128>(wit(m127), wit(1)), (1, true));
        assert_eq(rotate_left_or::<128>(wit(1), wit(128)), (0, false));
        assert_eq(shl_or::<128>(wit(two_pow::<128>()), wit(0)), (0, false));
        assert_eq(shr_or::<127>(wit(m127 - 1), wit(126)), (1, true));
        assert_eq(shr_or::<127>(wit(m127), wit(0)), (0, false));
        assert_eq(shl_exact_or::<127>(wit(1), wit(127)), (0, false));
        assert_eq(rotate_right_or::<127>(wit(1), wit(1)), (two_pow::<126>(), true));
    }

    // Wrong hints for the 128-bit split: a = 2^128 - 1 shifted by 127, so
    // a0 = ah = 2^64 - 1, p0 = 0, p1 = 2^63, and a*2^127 = 2^255 - 2^127:
    // lo = 2^127, hi = 2^127 - 1.

    #[test]
    fn honest_128_bit_shift_split_accepted() {
        let m64 = two_pow::<64>() - 1;
        let hi = constrain_mul_128(
            wit(m64),
            wit(m64),
            wit(0),
            wit(two_pow::<63>()),
            wit(two_pow::<127>()),
        );
        assert_eq(hi, two_pow::<127>() - 1);
    }

    #[test(should_fail)]
    fn shift_128_low_half_off_by_one_rejected() {
        let m64 = two_pow::<64>() - 1;
        let _ = constrain_mul_128(m64, m64, 0, two_pow::<63>(), two_pow::<127>() + 1);
    }

    #[test(should_fail)]
    fn shift_128_low_half_past_2_128_rejected() {
        // lo + 2^128 with the carry one lower: the 128-bit RANGE on lo fails
        let m64 = two_pow::<64>() - 1;
        let _ = constrain_mul_128(m64, m64, 0, two_pow::<63>(), two_pow::<127>() + TWO_POW_128);
    }

    #[test(should_fail)]
    fn shift_128_field_wrapped_split_rejected() {
        // lo' + hi'*2^128 = a*2^127 - p, a split of the field element
        // a*2^127 mod p with both halves below 2^128 (lo' = 2^127 minus
        // p mod 2^128). It satisfies a*b == lo' + hi'*2^128 in the field,
        // but its carry (s - lo') / 2^128 is not an integer, so the 70-bit
        // carry RANGE fails.
        let m64 = two_pow::<64>() - 1;
        let p_lo: Field = 0x2833e84879b9709143e1f593f0000001;
        let _ = constrain_mul_128(m64, m64, 0, two_pow::<63>(), two_pow::<127>() - p_lo);
    }

    // The typed shift-amount split.

    #[test]
    fn honest_shift_amount_bits_accepted() {
        assert(constrain_shift_amount::<3, 14>(wit(5), wit([true, false, true])));
        assert(!constrain_shift_amount::<3, 14>(wit(8), wit([false, false, false])));
        assert(!constrain_shift_amount::<3, 14>(wit(255), wit([true, true, true])));
        let ones = [true; 7];
        assert(constrain_shift_amount::<7, 126>(wit(127), wit(ones)));
        assert(!constrain_shift_amount::<7, 126>(wit(U128_MAX_FIELD), wit(ones)));
        assert(!constrain_shift_amount::<7, 126>(wit(128), wit([false; 7])));
    }

    #[test(should_fail)]
    fn shift_amount_bits_off_by_one_rejected() {
        let _ = constrain_shift_amount::<3, 14>(5, [false, true, true]);
    }

    #[test(should_fail)]
    fn shift_amount_flag_cannot_be_forced_true() {
        // s = 130 is out of range; bits of 127 leave rest = 3/128
        let _ = constrain_shift_amount::<7, 126>(130, [true; 7]);
    }

    #[test(should_fail)]
    fn shift_amount_flag_cannot_be_forced_false() {
        // s = 3 is in range; bits of 127 leave rest = -124/128
        let _ = constrain_shift_amount::<7, 126>(3, [true; 7]);
    }

    #[test(should_fail)]
    fn shift_amount_wrong_bits_at_max_rejected() {
        // s = 2^128 - 1: low 7 bits are all ones; claiming zero leaves
        // rest = (2^128 - 1)/128, not an integer
        let _ = constrain_shift_amount::<7, 126>(U128_MAX_FIELD, [false; 7]);
    }

    // Typed shifts against the native operators.

    unconstrained fn native_ref<T>(x: T, s: T, n: T, zero: T) -> (T, T, bool, bool)
    where
        T: Shl + Shr + Ord + Eq,
    {
        if s < n {
            let l = x << s;
            (l, x >> s, true, (l >> s) == x)
        } else {
            (zero, zero, false, false)
        }
    }

    fn check_typed<T, let K: u32, let L: u32>(xs: [T; K], ss: [T; L], n: T, zero: T)
    where
        T: TotalShift + Shl + Shr + Ord + Eq,
    {
        for i in 0..K {
            for j in 0..L {
                // Safety: test reference
                let (l, r, ok, exact_ok) = unsafe { native_ref(xs[i], ss[j], n, zero) };
                assert(xs[i].shl_or(wit(ss[j])) == (l, ok));
                assert(xs[i].shr_or(wit(ss[j])) == (r, ok));
                let le = if exact_ok { l } else { zero };
                assert(xs[i].shl_exact_or(wit(ss[j])) == (le, exact_ok));
            }
        }
    }

    #[test]
    fn typed_u8_u16() {
        check_typed(
            [0 as u8, 1, 0xa5, 255],
            [0 as u8, 1, 3, 7, 8, 9, 200, 255],
            8,
            0,
        );
        check_typed(
            [0 as u16, 1, 0xa55a, 65535],
            [0 as u16, 1, 8, 15, 16, 255, 65535],
            16,
            0,
        );
    }

    #[test]
    fn typed_u32_u64() {
        check_typed(
            [0 as u32, 1, 0xa55aa55a, 4294967295],
            [0 as u32, 1, 16, 31, 32, 255, 4294967295],
            32,
            0,
        );
        check_typed(
            [0 as u64, 1, 0xa55aa55aa55aa55a, 18446744073709551615],
            [0 as u64, 1, 32, 63, 64, 255, 18446744073709551615],
            64,
            0,
        );
    }

    #[test]
    fn typed_u128() {
        let max: u128 = 0xffffffffffffffffffffffffffffffff;
        check_typed(
            [0 as u128, 1, 0xa55aa55aa55aa55aa55aa55aa55aa55a, max],
            [0 as u128, 1, 63, 64, 65, 127, 128, 255, max],
            128,
            0,
        );
        assert_eq(wit(max).shl_or(wit(127)), (0x80000000000000000000000000000000, true));
        assert_eq(wit(max).shr_or(wit(127)), (1, true));
        assert_eq((1 as u128).shl_or(wit(128)), (0, false));
        assert_eq(wit(max).shr_or(wit(max)), (0, false));
        assert_eq((1 as u128).shl_exact_or(wit(127)), (0x80000000000000000000000000000000, true));
        assert_eq((3 as u128).shl_exact_or(wit(127)), (0, false));
        assert_eq(wit(max).shl_exact_or(wit(0)), (max, true));
        assert_eq((255 as u8).shl_exact_or(wit(1)), (0, false));
        assert_eq((127 as u8).shl_exact_or(wit(1)), (254, true));
    }
}
