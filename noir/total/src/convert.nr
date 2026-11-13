//! Conversions with flags instead of silent truncation or asserts.
//!
//! Field to integer: to_uN_or / to_iN_or return (value, ok) with ok a
//! determined range flag and value 0 when ok is false. They replace
//! `x as uN`, which is total but silently keeps the low N bits.
//!
//! Integer to Field: from_* widenings, total and exact. Signed values have
//! two Field readings, and both are offered: the bit pattern (from_iN,
//! the inverse of to_iN_or) and the signed value with negatives as p - k
//! (from_iN_signed, the inverse of to_iN_from_signed_or).
//!
//! Between native integer types: the TotalNarrow trait, for narrowing and
//! for every sign change, whose target may not hold the source value. Widenings within one signedness
//! (`x as u64` for x: u8, `x as i64` for x: i8) are exact and total:
//! unsigned widening emits nothing; signed widening is the
//! compiler's sign extension (an unsigned compare against 2^(N-1) and
//! unchecked arithmetic), hint-satisfiable for every value of the source
//! type. They need no wrapper.
//!
//! Field to bits and bytes: full-width decompositions with canonicity
//! enforced (to_le_bits_total and friends), flagged bounded ones up to 253
//! bits or 31 bytes (to_le_bits_or::<N> and friends), the parity bit
//! (sgn0), and flagged decoders (from_le_bytes_or and friends) whose ok is
//! the canonical-encoding flag, value < p.
//!
//! Status of the std conversions:
//! - `x as uN` (x: Field): total. It lowers to a Euclidean division of the
//!   canonical integer by 2^N: hinted q, r; RANGEs; the reconstruction;
//!   q <= floor(p / 2^N) and, when q equals that bound, r below the
//!   matching remainder of p. The honest hint satisfies all of them for
//!   every Field. The result is the low N bits of the canonical integer,
//!   with no signal that bits were dropped: use to_uN_or or truncate_or.
//!   The same holds for a negative literal: `-1 as i16` is the Field
//!   p - 1 cast, whose low 16 bits are 0, so it evaluates to 0, not -1
//!   (the compiler warns). Write `-1i16` or use to_i16_from_signed_or.
//! - Field::to_le_bits::<N> / to_be_bits::<N>, N < 254: input-falsifiable.
//!   The decomposition must reconstruct x from N bits, which fails for
//!   x >= 2^N. Use to_le_bits_or::<N>.
//! - Field::to_le_bits::<254> / to_be_bits::<254>: total and canonical. The
//!   builtin decomposition (hinted bits, booleanity RANGEs, reconstruction
//!   mod p) admits x + p as well when x + p < 2^254, but std then walks the
//!   bits from the top against the modulus bits under the predicate "no
//!   difference yet", asserts the first difference has a 1 in the modulus,
//!   and asserts a difference was found. The honest hint is the canonical
//!   decomposition, which is below p, so every assert holds for every x;
//!   any other decomposition is >= p and fails, so the bits are determined.
//!   This module still builds its full-width forms from the limbs (below)
//!   because that costs fewer gates. The tests check both agree.
//! - Field::to_le_bytes::<N> / to_be_bytes::<N>: input-falsifiable for
//!   N < 32 (x >= 2^(8N) cannot be reconstructed); total and canonical for
//!   N = 32 by the same top-down argument with byte compares.
//! - Field::from_le_bytes::<N> / from_be_bytes::<N>: total (arithmetic
//!   only). Exact for N <= 31, since 256^31 < p. For N = 32 an encoding of
//!   an integer >= p wraps silently: use from_le_bytes_or.
//! - Field::from_le_bytes_checked / from_be_bytes_checked:
//!   input-falsifiable (assert value < p). Use from_le_bytes_or.
//! - Field::assert_max_bit_size: input-falsifiable. Use range::fits_bits.
//!
//! There is no u1 type (bits are bool), so the 1-bit conversion is
//! bool_or.

use crate::core::{
    bias, eq, implied_range, is_zero, limbs, low_bit, lt_bounded, select_field, split_128_at,
    two_pow, TWO_POW_128,
};
use crate::range::clamp_bits_or;
use std::static_assert;

/// Low 128-bit limb of the field modulus p.
pub global PLO: Field = 53438638232309528389504892708671455233;
/// High 128-bit limb of the field modulus p (PHI < 2^126).
pub global PHI: Field = 64323764613183177041862057485226039389;

// ---------------------------------------------------------------------
// Exact casts of an already-bounded Field to a native type
// ---------------------------------------------------------------------
//
// Each cast takes v that earlier constraints bound below 2^N for every
// satisfying witness (PRECONDITION; pub(crate)), range-checks it to N
// bits with core::implied_range (which therefore adds no failure
// source), and casts with `as`. The truncation is the identity on a value
// below 2^N, and after the range check the compiler emits nothing for it.
// For iN the cast goes through uN: `uN as iN` reinterprets the bit
// pattern and emits nothing.

pub(crate) fn cast_u8(v: Field) -> u8 {
    implied_range::<8>(v) as u8
}
pub(crate) fn cast_u16(v: Field) -> u16 {
    implied_range::<16>(v) as u16
}
pub(crate) fn cast_u32(v: Field) -> u32 {
    implied_range::<32>(v) as u32
}
pub(crate) fn cast_u64(v: Field) -> u64 {
    implied_range::<64>(v) as u64
}
pub(crate) fn cast_u128(v: Field) -> u128 {
    implied_range::<128>(v) as u128
}
/// The iN whose bit pattern is v, for v below 2^N (PRECONDITION).
pub(crate) fn cast_i8(v: Field) -> i8 {
    (implied_range::<8>(v) as u8) as i8
}
pub(crate) fn cast_i16(v: Field) -> i16 {
    (implied_range::<16>(v) as u16) as i16
}
pub(crate) fn cast_i32(v: Field) -> i32 {
    (implied_range::<32>(v) as u32) as i32
}
pub(crate) fn cast_i64(v: Field) -> i64 {
    (implied_range::<64>(v) as u64) as i64
}

// ---------------------------------------------------------------------
// Field -> unsigned
// ---------------------------------------------------------------------

/// (x as u8, true) when x < 2^8, else (0, false). The total replacement
/// for `x as u8`, which silently keeps the low 8 bits.
///
/// Constraints: range::clamp_bits_or::<8> (the core::limbs set, a split of
/// the low limb, is_zero gadgets; hint-satisfiable for every Field), then
/// the exact cast of the clamped value (cast_u8: an 8-bit RANGE on it).
/// The clamped value is below 2^8 for every satisfying witness, so that
/// RANGE adds no failure source. No input-falsifiable constraint.
/// Determined: ok is the determined range flag, and the clamped value and
/// its cast are functions of x and ok.
pub fn to_u8_or(x: Field) -> (u8, bool) {
    let (v, ok) = clamp_bits_or::<8>(x);
    (cast_u8(v), ok)
}

/// As to_u8_or for 16 bits.
pub fn to_u16_or(x: Field) -> (u16, bool) {
    let (v, ok) = clamp_bits_or::<16>(x);
    (cast_u16(v), ok)
}

/// As to_u8_or for 32 bits.
pub fn to_u32_or(x: Field) -> (u32, bool) {
    let (v, ok) = clamp_bits_or::<32>(x);
    (cast_u32(v), ok)
}

/// As to_u8_or for 64 bits.
pub fn to_u64_or(x: Field) -> (u64, bool) {
    let (v, ok) = clamp_bits_or::<64>(x);
    (cast_u64(v), ok)
}

/// As to_u8_or for 128 bits; the range flag is core::fits_128 (the limbs
/// set and is_zero on the high limb).
pub fn to_u128_or(x: Field) -> (u128, bool) {
    let (v, ok) = clamp_bits_or::<128>(x);
    (cast_u128(v), ok)
}

// ---------------------------------------------------------------------
// Field -> signed
// ---------------------------------------------------------------------

/// BIT-PATTERN reading: x is taken as an 8-bit two's complement pattern.
/// ok iff x < 2^8; the result is the i8 with that pattern, so 255 gives
/// -1 and 128 gives -128. The Field p - 1 (which Field arithmetic writes
/// as -1) is NOT -1 here: it is out of range, giving (0, false). For the
/// signed-value reading use to_i8_from_signed_or. Inverse of from_i8.
///
/// Constraints: range::clamp_bits_or::<8> as in to_u8_or, then the exact
/// cast of the clamped pattern (cast_i8: an 8-bit RANGE, then a
/// reinterpreting cast). All hint-satisfiable for every x; ok and the
/// value are determined as in to_u8_or.
pub fn to_i8_or(x: Field) -> (i8, bool) {
    let (v, ok) = clamp_bits_or::<8>(x);
    (cast_i8(v), ok)
}

/// Bit-pattern reading for 16 bits; see to_i8_or.
pub fn to_i16_or(x: Field) -> (i16, bool) {
    let (v, ok) = clamp_bits_or::<16>(x);
    (cast_i16(v), ok)
}

/// Bit-pattern reading for 32 bits; see to_i8_or.
pub fn to_i32_or(x: Field) -> (i32, bool) {
    let (v, ok) = clamp_bits_or::<32>(x);
    (cast_i32(v), ok)
}

/// Bit-pattern reading for 64 bits; see to_i8_or.
pub fn to_i64_or(x: Field) -> (i64, bool) {
    let (v, ok) = clamp_bits_or::<64>(x);
    (cast_i64(v), ok)
}

/// Signed-value reading for width N: x is k for 0 <= k < 2^(N-1) and
/// p - k for 1 <= k <= 2^(N-1). Returns (pattern of that value, ok) with
/// pattern 0 when ok is false. Shared by the to_iN_from_signed_or entries.
///
/// Constraints: range::clamp_bits_or::<N> on s = x + 2^(N-1) (s < 2^N iff x
/// is in the signed range, mod p), then core::bias::<N> on the clamped s,
/// whose precondition (below 2^N) the clamp establishes; bias maps the
/// shifted value back to the two's complement pattern (it is an
/// involution on N-bit values). All hint-satisfiable for every x;
/// determined.
fn signed_pattern_or<let N: u32>(x: Field) -> (Field, bool) {
    let (s, ok) = clamp_bits_or::<N>(x + two_pow::<N - 1>());
    (select_field(ok, bias::<N>(s), 0), ok)
}

/// SIGNED-VALUE reading: x in [0, 128) gives itself, x in [p - 128, p)
/// (Field -1 ..= -128) gives the negative i8; anything else gives
/// (0, false). Inverse of from_i8_signed.
///
/// Constraints: signed_pattern_or::<8> (see there) and the exact i8 cast
/// of the resulting pattern, which is below 2^8 by construction. All
/// hint-satisfiable for every x; ok and the value are determined.
pub fn to_i8_from_signed_or(x: Field) -> (i8, bool) {
    let (v, ok) = signed_pattern_or::<8>(x);
    (cast_i8(v), ok)
}

/// Signed-value reading for 16 bits; see to_i8_from_signed_or.
pub fn to_i16_from_signed_or(x: Field) -> (i16, bool) {
    let (v, ok) = signed_pattern_or::<16>(x);
    (cast_i16(v), ok)
}

/// Signed-value reading for 32 bits; see to_i8_from_signed_or.
pub fn to_i32_from_signed_or(x: Field) -> (i32, bool) {
    let (v, ok) = signed_pattern_or::<32>(x);
    (cast_i32(v), ok)
}

/// Signed-value reading for 64 bits; see to_i8_from_signed_or.
pub fn to_i64_from_signed_or(x: Field) -> (i64, bool) {
    let (v, ok) = signed_pattern_or::<64>(x);
    (cast_i64(v), ok)
}

// ---------------------------------------------------------------------
// Native -> Field widenings
// ---------------------------------------------------------------------

/// b as Field: 0 or 1. Total; emits no constraint.
pub fn from_bool(b: bool) -> Field {
    b as Field
}

/// x as Field, exact. Total; emits no constraint (the value already lies
/// below 2^8 by the type invariant).
pub fn from_u8(x: u8) -> Field {
    x as Field
}

/// x as Field, exact. Total; emits no constraint.
pub fn from_u16(x: u16) -> Field {
    x as Field
}

/// x as Field, exact. Total; emits no constraint.
pub fn from_u32(x: u32) -> Field {
    x as Field
}

/// x as Field, exact. Total; emits no constraint.
pub fn from_u64(x: u64) -> Field {
    x as Field
}

/// x as Field, exact. Total; emits no constraint.
pub fn from_u128(x: u128) -> Field {
    x as Field
}

/// BIT PATTERN of x as a Field: (x as u8) as Field, so -1 gives 255.
/// Inverse of to_i8_or. Total; emits no constraint (same-width
/// reinterpretation, then an exact widening). For the signed value (-1
/// as p - 1) use from_i8_signed.
pub fn from_i8(x: i8) -> Field {
    (x as u8) as Field
}

/// Bit pattern of x as a Field; see from_i8.
pub fn from_i16(x: i16) -> Field {
    (x as u16) as Field
}

/// Bit pattern of x as a Field; see from_i8.
pub fn from_i32(x: i32) -> Field {
    (x as u32) as Field
}

/// Bit pattern of x as a Field; see from_i8.
pub fn from_i64(x: i64) -> Field {
    (x as u64) as Field
}

/// SIGNED VALUE of x as a Field: x for x >= 0, p - |x| for x < 0, so -1
/// gives the Field -1. Inverse of to_i8_from_signed_or.
///
/// Constraints: core::bias::<8> on the pattern (one lt_bounded::<8>; its
/// precondition is the type invariant pattern < 2^8), then subtraction of
/// 2^7. Hint-satisfiable for every i8; determined.
pub fn from_i8_signed(x: i8) -> Field {
    bias::<8>((x as u8) as Field) - two_pow::<7>()
}

/// Signed value of x as a Field; see from_i8_signed.
pub fn from_i16_signed(x: i16) -> Field {
    bias::<16>((x as u16) as Field) - two_pow::<15>()
}

/// Signed value of x as a Field; see from_i8_signed.
pub fn from_i32_signed(x: i32) -> Field {
    bias::<32>((x as u32) as Field) - two_pow::<31>()
}

/// Signed value of x as a Field; see from_i8_signed.
pub fn from_i64_signed(x: i64) -> Field {
    bias::<64>((x as u64) as Field) - two_pow::<63>()
}

// ---------------------------------------------------------------------
// Native -> native narrowing
// ---------------------------------------------------------------------

/// Conversion between native integer types whose target may not hold
/// every source value: returns (value, true) when the source value is
/// representable in T, else (0, false). Usage:
/// `let (v, ok): (u8, bool) = x.narrow_or();`
///
/// Implemented for unsigned narrowing (u16/u32/u64/u128 to every smaller
/// unsigned width), signed narrowing (i16/i32/i64 to every smaller signed
/// width), and every sign change between i8..i64 and u8..u128, same width
/// or not. A sign change into a wider signed type (u8 to i16, ..., u32 to
/// i64) always fits and returns ok = true; it is offered so that generic
/// code can use one trait. Same-signedness widenings are plain `as`.
///
/// Constraints, narrowing impls: the native truncating cast `self as T` (a
/// Euclidean division of the source pattern by 2^N with hinted quotient
/// and remainder, RANGEs on both, and the reconstruction; hint-satisfiable
/// for every value of the source type, and determined), a native widening
/// back to the source type (none for unsigned; the compiler's sign
/// extension for signed, an unsigned compare and unchecked arithmetic,
/// both hint-satisfiable), native `==` (inversion gadget), and a typed
/// select (arithmetic). ok is "round trip is exact", which is determined
/// because the truncation and the widening are.
///
/// Same-width sign changes: one native `<` against 2^(N-1) on the
/// unsigned pattern (see cmp.nr for its lowering) and a typed select.
///
/// Cross-width sign changes, source of M bits: the value is representable
/// iff the source pattern p (p < 2^M by the type invariant) is below a
/// bound 2^K: K = N for iM to a narrower uN (0 <= value < 2^N), K = M - 1
/// for iM to a wider uN (value >= 0), K = N - 1 for uM to an iN no wider
/// (value < 2^(N-1)). pattern_below_or::<M, K> emits lt_bounded::<M>
/// against 2^K and selects p or 0; the selected value is below 2^K, so the
/// exact cast to the target (cast_uN, cast_iN: an N-bit RANGE that adds no
/// failure source, then a reinterpretation for iN) gives that value. All
/// hint-satisfiable for every source value; ok and the value are
/// determined. uM to a wider iN is the native widening `self as iN` (zero
/// extension, no constraint) with ok = true.
pub trait TotalNarrow<T> {
    fn narrow_or(self) -> (T, bool);
}

// Unsigned narrowing: ok iff the truncation round-trips. Constraints as
// documented on TotalNarrow.
impl TotalNarrow<u8> for u16 {
    fn narrow_or(self) -> (u8, bool) {
        let t = self as u8;
        let ok = (t as u16) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<u8> for u32 {
    fn narrow_or(self) -> (u8, bool) {
        let t = self as u8;
        let ok = (t as u32) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<u16> for u32 {
    fn narrow_or(self) -> (u16, bool) {
        let t = self as u16;
        let ok = (t as u32) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<u8> for u64 {
    fn narrow_or(self) -> (u8, bool) {
        let t = self as u8;
        let ok = (t as u64) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<u16> for u64 {
    fn narrow_or(self) -> (u16, bool) {
        let t = self as u16;
        let ok = (t as u64) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<u32> for u64 {
    fn narrow_or(self) -> (u32, bool) {
        let t = self as u32;
        let ok = (t as u64) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<u8> for u128 {
    fn narrow_or(self) -> (u8, bool) {
        let t = self as u8;
        let ok = (t as u128) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<u16> for u128 {
    fn narrow_or(self) -> (u16, bool) {
        let t = self as u16;
        let ok = (t as u128) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<u32> for u128 {
    fn narrow_or(self) -> (u32, bool) {
        let t = self as u32;
        let ok = (t as u128) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<u64> for u128 {
    fn narrow_or(self) -> (u64, bool) {
        let t = self as u64;
        let ok = (t as u128) == self;
        (if ok { t } else { 0 }, ok)
    }
}
// Signed narrowing: ok iff truncation then sign extension round-trips.
// Constraints as documented on TotalNarrow.
impl TotalNarrow<i8> for i16 {
    fn narrow_or(self) -> (i8, bool) {
        let t = self as i8;
        let ok = (t as i16) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<i8> for i32 {
    fn narrow_or(self) -> (i8, bool) {
        let t = self as i8;
        let ok = (t as i32) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<i16> for i32 {
    fn narrow_or(self) -> (i16, bool) {
        let t = self as i16;
        let ok = (t as i32) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<i8> for i64 {
    fn narrow_or(self) -> (i8, bool) {
        let t = self as i8;
        let ok = (t as i64) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<i16> for i64 {
    fn narrow_or(self) -> (i16, bool) {
        let t = self as i16;
        let ok = (t as i64) == self;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<i32> for i64 {
    fn narrow_or(self) -> (i32, bool) {
        let t = self as i32;
        let ok = (t as i64) == self;
        (if ok { t } else { 0 }, ok)
    }
}
// Same-width sign changes: ok iff the pattern is below 2^(N-1), checked
// with one native unsigned `<`. Constraints as documented on TotalNarrow.
impl TotalNarrow<u8> for i8 {
    fn narrow_or(self) -> (u8, bool) {
        let t = self as u8;
        let ok = t < 0x80;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<i8> for u8 {
    fn narrow_or(self) -> (i8, bool) {
        let ok = self < 0x80;
        let t = self as i8;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<u16> for i16 {
    fn narrow_or(self) -> (u16, bool) {
        let t = self as u16;
        let ok = t < 0x8000;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<i16> for u16 {
    fn narrow_or(self) -> (i16, bool) {
        let ok = self < 0x8000;
        let t = self as i16;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<u32> for i32 {
    fn narrow_or(self) -> (u32, bool) {
        let t = self as u32;
        let ok = t < 0x80000000;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<i32> for u32 {
    fn narrow_or(self) -> (i32, bool) {
        let ok = self < 0x80000000;
        let t = self as i32;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<u64> for i64 {
    fn narrow_or(self) -> (u64, bool) {
        let t = self as u64;
        let ok = t < 0x8000000000000000;
        (if ok { t } else { 0 }, ok)
    }
}
impl TotalNarrow<i64> for u64 {
    fn narrow_or(self) -> (i64, bool) {
        let ok = self < 0x8000000000000000;
        let t = self as i64;
        (if ok { t } else { 0 }, ok)
    }
}

// Cross-width sign changes. Each is one pattern_below_or on the source
// bit pattern and an exact cast of the selected value, or, where every
// source value fits, a plain widening. Constraints as documented on
// TotalNarrow.
impl TotalNarrow<u16> for i8 {
    fn narrow_or(self) -> (u16, bool) {
        let (v, ok) = pattern_below_or::<8, 7>((self as u8) as Field);
        (cast_u16(v), ok)
    }
}
impl TotalNarrow<u32> for i8 {
    fn narrow_or(self) -> (u32, bool) {
        let (v, ok) = pattern_below_or::<8, 7>((self as u8) as Field);
        (cast_u32(v), ok)
    }
}
impl TotalNarrow<u64> for i8 {
    fn narrow_or(self) -> (u64, bool) {
        let (v, ok) = pattern_below_or::<8, 7>((self as u8) as Field);
        (cast_u64(v), ok)
    }
}
impl TotalNarrow<u128> for i8 {
    fn narrow_or(self) -> (u128, bool) {
        let (v, ok) = pattern_below_or::<8, 7>((self as u8) as Field);
        (cast_u128(v), ok)
    }
}
impl TotalNarrow<u8> for i16 {
    fn narrow_or(self) -> (u8, bool) {
        let (v, ok) = pattern_below_or::<16, 8>((self as u16) as Field);
        (cast_u8(v), ok)
    }
}
impl TotalNarrow<u32> for i16 {
    fn narrow_or(self) -> (u32, bool) {
        let (v, ok) = pattern_below_or::<16, 15>((self as u16) as Field);
        (cast_u32(v), ok)
    }
}
impl TotalNarrow<u64> for i16 {
    fn narrow_or(self) -> (u64, bool) {
        let (v, ok) = pattern_below_or::<16, 15>((self as u16) as Field);
        (cast_u64(v), ok)
    }
}
impl TotalNarrow<u128> for i16 {
    fn narrow_or(self) -> (u128, bool) {
        let (v, ok) = pattern_below_or::<16, 15>((self as u16) as Field);
        (cast_u128(v), ok)
    }
}
impl TotalNarrow<u8> for i32 {
    fn narrow_or(self) -> (u8, bool) {
        let (v, ok) = pattern_below_or::<32, 8>((self as u32) as Field);
        (cast_u8(v), ok)
    }
}
impl TotalNarrow<u16> for i32 {
    fn narrow_or(self) -> (u16, bool) {
        let (v, ok) = pattern_below_or::<32, 16>((self as u32) as Field);
        (cast_u16(v), ok)
    }
}
impl TotalNarrow<u64> for i32 {
    fn narrow_or(self) -> (u64, bool) {
        let (v, ok) = pattern_below_or::<32, 31>((self as u32) as Field);
        (cast_u64(v), ok)
    }
}
impl TotalNarrow<u128> for i32 {
    fn narrow_or(self) -> (u128, bool) {
        let (v, ok) = pattern_below_or::<32, 31>((self as u32) as Field);
        (cast_u128(v), ok)
    }
}
impl TotalNarrow<u8> for i64 {
    fn narrow_or(self) -> (u8, bool) {
        let (v, ok) = pattern_below_or::<64, 8>((self as u64) as Field);
        (cast_u8(v), ok)
    }
}
impl TotalNarrow<u16> for i64 {
    fn narrow_or(self) -> (u16, bool) {
        let (v, ok) = pattern_below_or::<64, 16>((self as u64) as Field);
        (cast_u16(v), ok)
    }
}
impl TotalNarrow<u32> for i64 {
    fn narrow_or(self) -> (u32, bool) {
        let (v, ok) = pattern_below_or::<64, 32>((self as u64) as Field);
        (cast_u32(v), ok)
    }
}
impl TotalNarrow<u128> for i64 {
    fn narrow_or(self) -> (u128, bool) {
        let (v, ok) = pattern_below_or::<64, 63>((self as u64) as Field);
        (cast_u128(v), ok)
    }
}
impl TotalNarrow<i16> for u8 {
    fn narrow_or(self) -> (i16, bool) {
        (self as i16, true)
    }
}
impl TotalNarrow<i32> for u8 {
    fn narrow_or(self) -> (i32, bool) {
        (self as i32, true)
    }
}
impl TotalNarrow<i64> for u8 {
    fn narrow_or(self) -> (i64, bool) {
        (self as i64, true)
    }
}
impl TotalNarrow<i8> for u16 {
    fn narrow_or(self) -> (i8, bool) {
        let (v, ok) = pattern_below_or::<16, 7>(self as Field);
        (cast_i8(v), ok)
    }
}
impl TotalNarrow<i32> for u16 {
    fn narrow_or(self) -> (i32, bool) {
        (self as i32, true)
    }
}
impl TotalNarrow<i64> for u16 {
    fn narrow_or(self) -> (i64, bool) {
        (self as i64, true)
    }
}
impl TotalNarrow<i8> for u32 {
    fn narrow_or(self) -> (i8, bool) {
        let (v, ok) = pattern_below_or::<32, 7>(self as Field);
        (cast_i8(v), ok)
    }
}
impl TotalNarrow<i16> for u32 {
    fn narrow_or(self) -> (i16, bool) {
        let (v, ok) = pattern_below_or::<32, 15>(self as Field);
        (cast_i16(v), ok)
    }
}
impl TotalNarrow<i64> for u32 {
    fn narrow_or(self) -> (i64, bool) {
        (self as i64, true)
    }
}
impl TotalNarrow<i8> for u64 {
    fn narrow_or(self) -> (i8, bool) {
        let (v, ok) = pattern_below_or::<64, 7>(self as Field);
        (cast_i8(v), ok)
    }
}
impl TotalNarrow<i16> for u64 {
    fn narrow_or(self) -> (i16, bool) {
        let (v, ok) = pattern_below_or::<64, 15>(self as Field);
        (cast_i16(v), ok)
    }
}
impl TotalNarrow<i32> for u64 {
    fn narrow_or(self) -> (i32, bool) {
        let (v, ok) = pattern_below_or::<64, 31>(self as Field);
        (cast_i32(v), ok)
    }
}
impl TotalNarrow<i8> for u128 {
    fn narrow_or(self) -> (i8, bool) {
        let (v, ok) = pattern_below_or::<128, 7>(self as Field);
        (cast_i8(v), ok)
    }
}
impl TotalNarrow<i16> for u128 {
    fn narrow_or(self) -> (i16, bool) {
        let (v, ok) = pattern_below_or::<128, 15>(self as Field);
        (cast_i16(v), ok)
    }
}
impl TotalNarrow<i32> for u128 {
    fn narrow_or(self) -> (i32, bool) {
        let (v, ok) = pattern_below_or::<128, 31>(self as Field);
        (cast_i32(v), ok)
    }
}
impl TotalNarrow<i64> for u128 {
    fn narrow_or(self) -> (i64, bool) {
        let (v, ok) = pattern_below_or::<128, 63>(self as Field);
        (cast_i64(v), ok)
    }
}

/// (ok ? p : 0, ok) with ok = p < 2^K, for a bit pattern p already below
/// 2^M (PRECONDITION: the type invariant of the M-bit source type),
/// 1 <= K < M <= 128. Constraints: core::lt_bounded::<M>(p, 2^K), whose
/// precondition holds (p < 2^M, 2^K < 2^M): a hinted flag and an M-bit
/// RANGE, hint-satisfiable for every such p and determined; then select
/// arithmetic. The value is below 2^K, so an exact cast to any type of K
/// bits or more adds no failure source.
fn pattern_below_or<let M: u32, let K: u32>(p: Field) -> (Field, bool) {
    let ok = lt_bounded::<M>(p, two_pow::<K>());
    (select_field(ok, p, 0), ok)
}

// ---------------------------------------------------------------------
// Truncation that reports what it dropped
// ---------------------------------------------------------------------

/// Split the canonical integer value of x at bit N, 1 <= N <= 253:
/// returns (lo, dropped, ok) with lo = x mod 2^N, dropped = x >> N (as a
/// Field holding that integer exactly), ok = (dropped == 0) = x < 2^N.
/// lo is exactly what native `x as uN` returns for N in {8, 16, 32, 64,
/// 128}: that cast also keeps the low bits of the canonical integer (see
/// the module header; pinned by tests at p - 1 and across the limb
/// boundary).
///
/// Constraints: the core::limbs set (lo, hi) (hint-satisfiable for every
/// Field), then by width:
/// - N < 128: core::split_128_at::<N> on the low limb (RANGE N and
///   RANGE 128 - N on the hinted parts, the reconstruction; its
///   precondition lo < 2^128 is the limbs RANGE), and
///   dropped = rest + hi * 2^(128 - N), below 2^(128-N) + 2^(254-N) < p.
/// - N = 128: lo and dropped = hi as they are.
/// - 129 <= N <= 253: core::split_128_at::<N - 128> on the high limb
///   (same shape; precondition hi < 2^128 from the limbs RANGE), giving
///   (hlow, rest) with hi = hlow + rest * 2^(N-128); the low part is
///   lo + hlow * 2^128 < 2^N <= 2^253 < p and dropped = rest.
/// and the is_zero gadget on dropped. In every case the sums cannot wrap,
/// so lo and dropped are the integers x mod 2^N and x >> N, and dropped
/// is zero iff x is below 2^N. Determined: limbs and the split are unique.
pub fn truncate_or<let N: u32>(x: Field) -> (Field, Field, bool) {
    static_assert((N >= 1) & (N <= 253), "truncate_or: N must be in 1..=253");
    let (lo, hi) = limbs(x);
    // N % 128 keeps the widths of the branches not taken non-negative (see
    // range::fits_bits).
    if N == 128 {
        (lo, hi, is_zero(hi))
    } else if N < 128 {
        let (low, rest) = split_128_at::<N % 128>(lo);
        let dropped = rest + hi * two_pow::<128 - N % 128>();
        (low, dropped, is_zero(dropped))
    } else {
        let (hlow, rest) = split_128_at::<N % 128>(hi);
        (lo + hlow * TWO_POW_128, rest, is_zero(rest))
    }
}

// ---------------------------------------------------------------------
// Full-width bits and bytes
// ---------------------------------------------------------------------

/// The 254 little-endian bits of the canonical integer value of x. Every
/// Field has exactly one such decomposition below p, and this returns it.
///
/// Constraints: the core::limbs set, which gives the canonical limbs
/// (lo, hi) with lo < 2^128 and hi <= PHI < 2^126 (hint-satisfiable for
/// every Field); std to_le_bits::<128> on lo and to_le_bits::<126> on hi:
/// each is the builtin decomposition (hinted bits, booleanity RANGEs, the
/// reconstruction), and std's canonicity loop is compiled out because the
/// width is below 254. Each reconstruction sums below 2^128 < p, so it is
/// an integer identity: hint-satisfiable for the limb bounds above, and
/// the bits are unique. Determined.
pub fn to_le_bits_total(x: Field) -> [bool; 254] {
    let (lo, hi) = limbs(x);
    let lo_bits: [bool; 128] = lo.to_le_bits();
    let hi_bits: [bool; 126] = hi.to_le_bits();
    let mut out = [false; 254];
    for i in 0..128 {
        out[i] = lo_bits[i];
    }
    for i in 0..126 {
        out[128 + i] = hi_bits[i];
    }
    out
}

/// Big-endian form of to_le_bits_total (index 0 is bit 253). Same
/// constraints; array reversal is free.
pub fn to_be_bits_total(x: Field) -> [bool; 254] {
    let le = to_le_bits_total(x);
    let mut out = [false; 254];
    for i in 0..254 {
        out[i] = le[253 - i];
    }
    out
}

/// The 32 little-endian bytes of the canonical integer value of x.
///
/// Constraints: the core::limbs set; std to_le_bytes::<16> on each limb:
/// the builtin radix-256 decomposition (hinted bytes, 8-bit RANGEs, the
/// reconstruction), with std's canonicity loop compiled out because the
/// length is below 32. Each limb is below 2^128 = 256^16, so the
/// decomposition exists and, summing below p, is unique. Determined.
pub fn to_le_bytes_total(x: Field) -> [u8; 32] {
    let (lo, hi) = limbs(x);
    let lo_bytes: [u8; 16] = lo.to_le_bytes();
    let hi_bytes: [u8; 16] = hi.to_le_bytes();
    let mut out = [0; 32];
    for i in 0..16 {
        out[i] = lo_bytes[i];
        out[16 + i] = hi_bytes[i];
    }
    out
}

/// Big-endian form of to_le_bytes_total. Same constraints.
pub fn to_be_bytes_total(x: Field) -> [u8; 32] {
    let le = to_le_bytes_total(x);
    let mut out = [0; 32];
    for i in 0..32 {
        out[i] = le[31 - i];
    }
    out
}

// ---------------------------------------------------------------------
// Bounded bits and bytes
// ---------------------------------------------------------------------

/// (bits, ok): the N little-endian bits of x when x < 2^N, else all false
/// with ok = false; 1 <= N <= 253. The total replacement for
/// x.to_le_bits::<N>(), which is input-falsifiable for x >= 2^N.
///
/// Constraints: range::clamp_bits_or::<N> (hint-satisfiable for every
/// Field; for N > 128 its condition is on the high limb), then std
/// to_le_bits::<N> on the clamped value: hinted bits, booleanity RANGEs,
/// the reconstruction (canonicity loop compiled out for N < 254). The
/// clamped value is below 2^N, and the reconstruction sums below
/// 2^N <= 2^253 < p, so it is an integer identity: the decomposition
/// exists and is unique. Determined.
pub fn to_le_bits_or<let N: u32>(x: Field) -> ([bool; N], bool) {
    static_assert((N >= 1) & (N <= 253), "to_le_bits_or: N must be in 1..=253");
    let (v, ok) = clamp_bits_or::<N>(x);
    (v.to_le_bits(), ok)
}

/// Big-endian form of to_le_bits_or. Same constraints.
pub fn to_be_bits_or<let N: u32>(x: Field) -> ([bool; N], bool) {
    static_assert((N >= 1) & (N <= 253), "to_be_bits_or: N must be in 1..=253");
    let (v, ok) = clamp_bits_or::<N>(x);
    (v.to_be_bits(), ok)
}

/// (bytes, ok): the N little-endian bytes of x when x < 2^(8N), else all
/// zero with ok = false; 1 <= N <= 31. The total replacement for
/// x.to_le_bytes::<N>(), which is input-falsifiable for x >= 2^(8N).
///
/// Constraints: range::clamp_bits_or::<8N>, then std to_le_bytes::<N> on
/// the clamped value (hinted bytes, 8-bit RANGEs, the reconstruction,
/// which sums below 2^(8N) <= 2^248 < p; the canonicity loop is compiled
/// out for N < 32). Hint-satisfiable for every Field; determined.
pub fn to_le_bytes_or<let N: u32>(x: Field) -> ([u8; N], bool) {
    static_assert((N >= 1) & (N <= 31), "to_le_bytes_or: N must be in 1..=31");
    let (v, ok) = clamp_bits_or::<N * 8>(x);
    (v.to_le_bytes(), ok)
}

/// Big-endian form of to_le_bytes_or. Same constraints.
pub fn to_be_bytes_or<let N: u32>(x: Field) -> ([u8; N], bool) {
    static_assert((N >= 1) & (N <= 31), "to_be_bytes_or: N must be in 1..=31");
    let (v, ok) = clamp_bits_or::<N * 8>(x);
    (v.to_be_bytes(), ok)
}

/// The low bit of the canonical integer value of x: true iff it is odd
/// (sgn0 in the hash-to-curve and square-root conventions). Bit 0 of
/// to_le_bits_total(x), for far fewer constraints.
///
/// Constraints: the core::limbs set (hint-satisfiable for every Field),
/// then core::low_bit on the low limb: a hinted bit (bool, so the
/// compiler's booleanity constraint) and upper part, RANGE 127 on the
/// upper part, and lo == bit + 2*upper; its precondition lo < 2^128 is
/// the limbs RANGE, and the sum is below 2^128 < p. Hint-satisfiable for
/// every Field; the canonical limbs and the split are unique, so the bit
/// is determined.
pub fn sgn0(x: Field) -> bool {
    let (lo, _) = limbs(x);
    low_bit(lo)
}

// ---------------------------------------------------------------------
// Canonical decoding of full-width encodings
// ---------------------------------------------------------------------

/// Flag: the integer lo + 2^128 * hi is below p, for lo, hi already
/// constrained below 2^128. PRECONDITION; pub(crate).
///
/// Constraints: core::lt_bounded::<128>(hi, PHI), the core::eq gadget on
/// hi - PHI, and lt_bounded::<128>(lo, PLO); every lt_bounded
/// precondition holds (PHI, PLO < 2^128 and
/// the caller's bounds). Result: hi < PHI | (hi == PHI & lo < PLO), the
/// lexicographic compare against the modulus limbs. Hint-satisfiable
/// under the precondition; determined.
pub(crate) fn limbs_below_modulus(lo: Field, hi: Field) -> bool {
    let hi_lt = lt_bounded::<128>(hi, PHI);
    let hi_eq = eq(hi, PHI);
    let lo_lt = lt_bounded::<128>(lo, PLO);
    hi_lt | (hi_eq & lo_lt)
}

/// Decode 32 little-endian bytes. Returns (value, ok) where ok says the
/// encoded integer is below p (the encoding is canonical); when ok is
/// false the value is 0. Never asserts canonicity: the total replacement
/// for Field::from_le_bytes_checked, and the flagged form of
/// Field::from_le_bytes, which wraps silently.
///
/// Constraints: the two 16-byte limb sums (arithmetic; each is below 2^128
/// by the u8 type invariant), limbs_below_modulus on them (two lt_bounded and
/// one eq gadget, hint-satisfiable because the limb bounds hold), and
/// select arithmetic. Determined: the limb sums are functions of the
/// bytes and the compare flags are determined.
pub fn from_le_bytes_or(bytes: [u8; 32]) -> (Field, bool) {
    let mut lo: Field = 0;
    let mut hi: Field = 0;
    let mut pw: Field = 1;
    for i in 0..16 {
        lo = lo + (bytes[i] as Field) * pw;
        hi = hi + (bytes[16 + i] as Field) * pw;
        pw = pw * 256;
    }
    let ok = limbs_below_modulus(lo, hi);
    (select_field(ok, lo + hi * TWO_POW_128, 0), ok)
}

/// Big-endian form of from_le_bytes_or (bytes[0] is the most significant).
/// Same constraints.
pub fn from_be_bytes_or(bytes: [u8; 32]) -> (Field, bool) {
    let mut le = [0; 32];
    for i in 0..32 {
        le[i] = bytes[31 - i];
    }
    from_le_bytes_or(le)
}

/// Decode 254 little-endian bits. Returns (value, ok) where ok says the
/// encoded integer is below p; when ok is false the value is 0.
///
/// Constraints: the 128-bit and 126-bit limb sums (arithmetic over bools,
/// so lo < 2^128 and hi < 2^126 hold by construction),
/// limbs_below_modulus, select arithmetic. Hint-satisfiable for every
/// input; determined.
pub fn from_le_bits_or(bits: [bool; 254]) -> (Field, bool) {
    let mut lo: Field = 0;
    let mut hi: Field = 0;
    let mut pw: Field = 1;
    for i in 0..128 {
        lo = lo + (bits[i] as Field) * pw;
        pw = pw * 2;
    }
    pw = 1;
    for i in 128..254 {
        hi = hi + (bits[i] as Field) * pw;
        pw = pw * 2;
    }
    let ok = limbs_below_modulus(lo, hi);
    (select_field(ok, lo + hi * TWO_POW_128, 0), ok)
}

/// Big-endian form of from_le_bits_or (bits[0] is bit 253). Same
/// constraints.
pub fn from_be_bits_or(bits: [bool; 254]) -> (Field, bool) {
    let mut le = [false; 254];
    for i in 0..254 {
        le[i] = bits[253 - i];
    }
    from_le_bits_or(le)
}

// ---------------------------------------------------------------------
// bool
// ---------------------------------------------------------------------

/// (x == 1, x == 0 | x == 1): the total replacement for treating a Field
/// as a bool (or for a bool-typed entry-point parameter, whose booleanity
/// check is input-falsifiable). For x outside {0, 1} the value is false.
///
/// Constraints: two core::eq inversion gadgets; hint-satisfiable for every
/// x and determined.
pub fn bool_or(x: Field) -> (bool, bool) {
    let one = eq(x, 1);
    (one, one | is_zero(x))
}

mod tests;
