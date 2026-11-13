//! Comparison flags. Every function returns a bool, or a value that is
//! defined for every input; none emits an input-falsifiable constraint,
//! and every flag is determined.
//!
//! Surfaces:
//! - Generic comparisons over the `TotalOrd` trait: eq, neq, lt, lte, gt,
//!   gte, min, max, clamp. Implemented for Field (the order of canonical
//!   integer values 0..p-1), bool, u8, u16, u32, u64, u128, i8, i16, i32
//!   and i64.
//! - cmp_bits::<N>(a, b) for raw Fields with a declared width N <= 253:
//!   both operands are range-flagged first, so no precondition leaks to
//!   the caller, and the comparison flags are folded with the range flags.
//! - is_zero on Field.
//!
//! How each type compares:
//! - Field: lexicographic compare of the canonical 128-bit limbs from
//!   core::limbs, using core::lt_bounded::<126> on the high limbs and
//!   core::lt_bounded::<128> on the low limbs. std::field::bn254::lt is also total
//!   (see field_lt); this form costs fewer gates.
//! - uN: the native operators. Native `a < b` on uN lowers to a Euclidean
//!   division of 2^N + a - b by the constant 2^N: a hinted quotient bit and
//!   remainder, a 1-bit RANGE on the quotient, an N-bit RANGE on the
//!   remainder, and the reconstruction. When both operands are below 2^N
//!   (the type invariant) the honest quotient and remainder satisfy all of
//!   them. The quotient bit is 1 iff a >= b, and the flag is 1 - quotient;
//!   the reconstruction determines the quotient, so the flag is determined.
//!   Native `==` lowers to the inversion gadget, total and determined.
//! - iN: each operand's bit pattern is mapped to the biased domain
//!   u = pattern XOR 2^(N-1), where signed order is unsigned order, and the
//!   biased values are compared with core::lt_bounded::<N>. Native signed
//!   `<` is also total: the compiler expands it to same-width unsigned
//!   casts, two divisions by 2^(N-1) for the sign bits, an unsigned `<`,
//!   and two xors, all hint-satisfiable for in-range operands. The biased
//!   form is used so the argument rests on core.
//! - bool: lt(a, b) = !a & b; pure boolean arithmetic.
//!
//! Signed cast semantics, pinned by the tests below: `x as uN` for
//! x: iN of the same width reinterprets the two's complement bit pattern
//! and emits no constraint (-1 as u8 is 255, -128 as u8 is 128); `uN as
//! Field` widens exactly; `iN as Field` is a compile error ("Only unsigned
//! integer types may be casted to Field"). So the pattern of x: iN as a
//! Field is `(x as uN) as Field`.
//!
//! The typed impls rely on the type invariant: a value of type uN or iN
//! has a bit pattern below 2^N. The compiler establishes the invariant
//! where a typed value is created (range checks on entry-point parameters
//! and on hint returns, overflow checks on arithmetic, truncation on
//! casts). Those creation-time checks are outside this module; a typed
//! value that exists satisfies them.
//!
//! min, max and clamp select with ctl::Select, which TotalOrd requires:
//! select arithmetic on values already computed, no constraint (ctl.nr
//! lists the shape per type).

use crate::core::{bias, eq as core_eq, limbs, lt_bounded, split_128_at};
use crate::ctl::Select;
use crate::range::clamp_bits_or;
use std::static_assert;

// ---------------------------------------------------------------------
// Crate-internal comparison gadgets
// ---------------------------------------------------------------------

/// Signed less-than on two N-bit two's complement patterns, both below
/// 2^N: core::bias maps each to the biased domain, whose values are below
/// 2^N, so lt_bounded::<N> applies. PRECONDITION as core::bias;
/// pub(crate).
pub(crate) fn signed_lt<let N: u32>(pa: Field, pb: Field) -> bool {
    lt_bounded::<N>(bias::<N>(pa), bias::<N>(pb))
}

/// Full-field less-than on canonical integer values.
///
/// Constraints: two core::limbs sets (hint-satisfiable for every Field,
/// including p - 1); core::lt_bounded::<126> on the high limbs, whose
/// precondition holds because limbs() forces (lo, hi) < (PLO, PHI) and so
/// hi <= PHI < 2^126; the is_zero gadget on the high-limb difference; and
/// core::lt_bounded::<128> on the low limbs, whose precondition holds
/// because limbs() range-checks both low limbs to 128 bits. Result: hi_lt | (hi_eq & lo_lt).
/// Determined: canonical limbs are unique and each sub-flag is determined.
///
/// std::field::bn254::lt is total too: gt(a, b) returns false under `a == b`, otherwise takes the
/// unconstrained field_less_than hint and, in the predicated branch the
/// hint selects, asserts the ordering with two decompose() calls and
/// assert_gt_limbs. The honest hint picks the branch whose assert is true;
/// the other branch's constraints are disabled by its predicate (RANGEs
/// under a predicate are applied to predicate * value). A dishonest hint
/// enables the branch whose assert is false, so the flag is determined.
fn field_lt(a: Field, b: Field) -> bool {
    let (alo, ahi) = limbs(a);
    let (blo, bhi) = limbs(b);
    limbs_lt(alo, ahi, blo, bhi)
}

/// Lexicographic less-than on canonical limb pairs from core::limbs:
/// lt_bounded::<126> on the high limbs (hi <= PHI < 2^126), the is_zero
/// gadget on their difference, lt_bounded::<128> on the low limbs (the
/// limbs RANGE). Every precondition holds for limbs of any Field.
fn limbs_lt(alo: Field, ahi: Field, blo: Field, bhi: Field) -> bool {
    let hi_lt = lt_bounded::<126>(ahi, bhi);
    let hi_eq = core_eq(ahi, bhi);
    let lo_lt = lt_bounded::<128>(alo, blo);
    hi_lt | (hi_eq & lo_lt)
}

// ---------------------------------------------------------------------
// TotalOrd: the generic comparison surface
// ---------------------------------------------------------------------

/// A total order whose primitives emit no input-falsifiable constraint.
/// Implementors provide a determined less-than flag and a determined
/// equality flag, and the type's ctl::Select gives the constraint-free
/// select; the free functions below derive the rest. To add a type,
/// implement Select and the two methods with the same guarantees and
/// document them.
pub trait TotalOrd: Select {
    /// Determined flag: self < other.
    fn total_lt(self, other: Self) -> bool;
    /// Determined flag: self == other.
    fn total_eq(self, other: Self) -> bool;
}

/// Field: the order of canonical integer values 0 <= x < p. See field_lt
/// for the constraints. Equality is the core::eq inversion gadget.
impl TotalOrd for Field {
    fn total_lt(self, other: Self) -> bool {
        field_lt(self, other)
    }
    fn total_eq(self, other: Self) -> bool {
        core_eq(self, other)
    }
}

/// bool: false < true. lt = !a & b, eq = !(a ^ b): boolean arithmetic
/// only, no assert.
impl TotalOrd for bool {
    fn total_lt(self, other: Self) -> bool {
        !self & other
    }
    fn total_eq(self, other: Self) -> bool {
        !(self ^ other)
    }
}

/// u8: native `<` and `==`; see the module header for the lowering and
/// why it is hint-satisfiable for every pair of u8 values.
impl TotalOrd for u8 {
    fn total_lt(self, other: Self) -> bool {
        self < other
    }
    fn total_eq(self, other: Self) -> bool {
        self == other
    }
}

/// u16: as u8.
impl TotalOrd for u16 {
    fn total_lt(self, other: Self) -> bool {
        self < other
    }
    fn total_eq(self, other: Self) -> bool {
        self == other
    }
}

/// u32: as u8.
impl TotalOrd for u32 {
    fn total_lt(self, other: Self) -> bool {
        self < other
    }
    fn total_eq(self, other: Self) -> bool {
        self == other
    }
}

/// u64: as u8.
impl TotalOrd for u64 {
    fn total_lt(self, other: Self) -> bool {
        self < other
    }
    fn total_eq(self, other: Self) -> bool {
        self == other
    }
}

/// u128: as u8. The quotient-and-remainder split is over 129 bits, well
/// below the field size, so the lowering argument holds unchanged.
impl TotalOrd for u128 {
    fn total_lt(self, other: Self) -> bool {
        self < other
    }
    fn total_eq(self, other: Self) -> bool {
        self == other
    }
}

/// i8: signed order via the biased domain on the u8 bit pattern
/// (signed_lt::<8>); the pattern is below 2^8 by the type invariant, so
/// the lt_bounded preconditions hold. Equality is native `==` on the
/// pattern (inversion gadget).
impl TotalOrd for i8 {
    fn total_lt(self, other: Self) -> bool {
        signed_lt::<8>((self as u8) as Field, (other as u8) as Field)
    }
    fn total_eq(self, other: Self) -> bool {
        self == other
    }
}

/// i16: as i8 with N = 16.
impl TotalOrd for i16 {
    fn total_lt(self, other: Self) -> bool {
        signed_lt::<16>((self as u16) as Field, (other as u16) as Field)
    }
    fn total_eq(self, other: Self) -> bool {
        self == other
    }
}

/// i32: as i8 with N = 32.
impl TotalOrd for i32 {
    fn total_lt(self, other: Self) -> bool {
        signed_lt::<32>((self as u32) as Field, (other as u32) as Field)
    }
    fn total_eq(self, other: Self) -> bool {
        self == other
    }
}

/// i64: as i8 with N = 64.
impl TotalOrd for i64 {
    fn total_lt(self, other: Self) -> bool {
        signed_lt::<64>((self as u64) as Field, (other as u64) as Field)
    }
    fn total_eq(self, other: Self) -> bool {
        self == other
    }
}

/// Determined equality flag. Constraints: the type's total_eq (for Field
/// and the integer types, the inversion gadget: hinted inverse and flag,
/// hint-satisfiable for every pair, determined both ways).
pub fn eq<T: TotalOrd>(a: T, b: T) -> bool {
    a.total_eq(b)
}

/// Determined inequality flag: !eq(a, b). Constraints as eq.
pub fn neq<T: TotalOrd>(a: T, b: T) -> bool {
    !a.total_eq(b)
}

/// Determined flag a < b. Constraints: the type's total_lt (see the impl
/// docs); all hint-satisfiable for every pair of values of the type.
pub fn lt<T: TotalOrd>(a: T, b: T) -> bool {
    a.total_lt(b)
}

/// Determined flag a <= b, computed as !(b < a). Constraints as lt.
pub fn lte<T: TotalOrd>(a: T, b: T) -> bool {
    !b.total_lt(a)
}

/// Determined flag a > b, computed as b < a. Constraints as lt.
pub fn gt<T: TotalOrd>(a: T, b: T) -> bool {
    b.total_lt(a)
}

/// Determined flag a >= b, computed as !(a < b). Constraints as lt.
pub fn gte<T: TotalOrd>(a: T, b: T) -> bool {
    !a.total_lt(b)
}

/// The smaller of a and b (a when equal). Constraints: one lt plus the
/// type's select (no assert). Determined: a function of a determined flag.
pub fn min<T: TotalOrd>(a: T, b: T) -> T {
    T::select(b.total_lt(a), b, a)
}

/// The larger of a and b (a when equal). Constraints as min.
pub fn max<T: TotalOrd>(a: T, b: T) -> T {
    T::select(a.total_lt(b), b, a)
}

/// min(max(x, lo), hi). Defined for every input: when lo > hi the result
/// is hi (the upper bound wins), never a failure. Constraints: two lt and
/// two selects. Determined.
pub fn clamp<T: TotalOrd>(x: T, lo: T, hi: T) -> T {
    min(max(x, lo), hi)
}

// Determined zero flag on Field, defined in core (inversion gadget; the
// flag's booleanity is implied by its equations, not emitted).
pub use crate::core::is_zero;

// ---------------------------------------------------------------------
// Bounded-width comparison of raw Fields
// ---------------------------------------------------------------------

/// Result of cmp_bits. lt, eq and gt are the comparison of a and b when
/// both are in range, and all three are false otherwise (exactly one of
/// them is true iff ok()). a_ok and b_ok say which operand was in range.
pub struct CmpFlags {
    pub lt: bool,
    pub eq: bool,
    pub gt: bool,
    pub a_ok: bool,
    pub b_ok: bool,
}

impl CmpFlags {
    /// Both operands were in range.
    pub fn ok(self) -> bool {
        self.a_ok & self.b_ok
    }
    /// a <= b with both in range.
    pub fn lte(self) -> bool {
        self.lt | self.eq
    }
    /// a >= b with both in range.
    pub fn gte(self) -> bool {
        self.gt | self.eq
    }
    /// a != b with both in range.
    pub fn neq(self) -> bool {
        self.lt | self.gt
    }
}

/// Compare two raw Fields declared to be N-bit values, 1 <= N <= 253,
/// without trusting the declaration.
///
/// Constraints for N <= 128: range::clamp_bits_or::<N> on each operand
/// (the core::limbs set, the low-limb split, is_zero gadgets:
/// hint-satisfiable for every Field); then, on the clamped values, which
/// are below 2^N by construction, core::lt_bounded::<N> (one hinted flag
/// and an N-bit RANGE) and the core::eq inversion gadget. The lt_bounded
/// precondition is discharged by the clamp, so no precondition reaches
/// the caller.
///
/// Constraints for 129 <= N <= 253, where lt_bounded::<N> is not
/// available (its hint compares as u128): the core::limbs set on each
/// operand; core::split_128_at::<N - 128> on each high limb (precondition
/// hi < 2^128 from the limbs RANGE) and is_zero on its upper part, which
/// is the range flag (x < 2^N iff hi < 2^(N-128), as in
/// range::fits_bits); limbs_lt on the two limb pairs (lt_bounded::<126>
/// on the high limbs, whose precondition hi <= PHI < 2^126 holds for
/// every Field, an is_zero gadget, lt_bounded::<128> on the low limbs);
/// and the core::eq gadget on a and b. The order of canonical values is
/// the integer order, so on in-range operands these are the N-bit
/// comparison; on others they are masked by the range flags. All
/// hint-satisfiable for every Field.
///
/// Determined: the range flags are determined, the clamped values are
/// functions of them, canonical limbs and their splits are unique, and
/// lt/eq on bounded values are determined; the folded flags are boolean
/// functions of these.
pub fn cmp_bits<let N: u32>(a: Field, b: Field) -> CmpFlags {
    static_assert((N >= 1) & (N <= 253), "cmp_bits: N must be in 1..=253");
    if N <= 128 {
        // N % 129 is N here; in the branch not taken it keeps the widths
        // in range (see range::fits_bits).
        let (ac, a_ok) = clamp_bits_or::<N % 129>(a);
        let (bc, b_ok) = clamp_bits_or::<N % 129>(b);
        let ok = a_ok & b_ok;
        let lt_c = lt_bounded::<N % 129>(ac, bc);
        let eq_c = core_eq(ac, bc);
        CmpFlags { lt: lt_c & ok, eq: eq_c & ok, gt: !lt_c & !eq_c & ok, a_ok, b_ok }
    } else {
        let (alo, ahi) = limbs(a);
        let (blo, bhi) = limbs(b);
        let (_, a_rest) = split_128_at::<N % 128>(ahi);
        let (_, b_rest) = split_128_at::<N % 128>(bhi);
        let a_ok = is_zero(a_rest);
        let b_ok = is_zero(b_rest);
        let ok = a_ok & b_ok;
        let lt_c = limbs_lt(alo, ahi, blo, bhi);
        let eq_c = core_eq(a, b);
        CmpFlags { lt: lt_c & ok, eq: eq_c & ok, gt: !lt_c & !eq_c & ok, a_ok, b_ok }
    }
}

mod tests {
    use crate::convert::PHI;
    use crate::core::{bias, constrain_lt_bounded, lt_bounded, two_pow, TWO_POW_128};
    use crate::test_support::wit;
    use super::{clamp, cmp_bits, eq, gt, gte, is_zero, lt, lte, max, min, neq, signed_lt};

    #[test]
    fn signed_cast_semantics() {
        let m1 = wit((255 as u8) as i8);
        assert(m1 == -1);
        assert_eq((m1 as u8) as Field, 255);
        let m128 = wit((128 as u8) as i8);
        assert(m128 == -128);
        assert_eq((m128 as u8) as Field, 128);
        let c: i8 = -1;
        assert_eq((c as u8) as Field, 255);
        let n = wit((0xffffffffffffffff as u64) as i64);
        assert(n == -1);
        assert_eq((n as u64) as Field, 0xffffffffffffffff);
        let min64: i64 = -9223372036854775808;
        assert_eq((min64 as u64) as Field, 0x8000000000000000);
    }

    #[test]
    fn lt_bounded_128_cases() {
        assert(lt_bounded::<128>(wit(0), wit(1)));
        assert(!lt_bounded::<128>(wit(1), wit(0)));
        assert(!lt_bounded::<128>(wit(7), wit(7)));
        assert(lt_bounded::<128>(wit(TWO_POW_128 - 2), wit(TWO_POW_128 - 1)));
        assert(!lt_bounded::<128>(wit(TWO_POW_128 - 1), wit(TWO_POW_128 - 1)));
        assert(!lt_bounded::<128>(wit(TWO_POW_128 - 1), wit(0)));
        assert(lt_bounded::<128>(wit(0), wit(TWO_POW_128 - 1)));
    }

    #[test]
    fn lt_bounded_at_wide_widths() {
        assert(lt_bounded::<8>(wit(254), wit(255)));
        assert(!lt_bounded::<8>(wit(255), wit(254)));
        assert(lt_bounded::<127>(wit(two_pow::<127>() - 2), wit(two_pow::<127>() - 1)));
        assert(lt_bounded::<128>(wit(0), wit(TWO_POW_128 - 1)));
        assert(!lt_bounded::<128>(wit(TWO_POW_128 - 1), wit(TWO_POW_128 - 1)));
    }

    #[test]
    fn bias_maps_sign_bit() {
        // i8 patterns: 0 -> 128, 127 -> 255, 128 (-128) -> 0, 255 (-1) -> 127
        assert_eq(bias::<8>(wit(0)), 128);
        assert_eq(bias::<8>(wit(127)), 255);
        assert_eq(bias::<8>(wit(128)), 0);
        assert_eq(bias::<8>(wit(255)), 127);
        assert(signed_lt::<8>(wit(128), wit(127))); // -128 < 127
        assert(signed_lt::<8>(wit(255), wit(0))); // -1 < 0
        assert(!signed_lt::<8>(wit(0), wit(255))); // 0 < -1 is false
        assert(!signed_lt::<8>(wit(5), wit(5)));
    }

    #[test(should_fail)]
    fn wrong_lt_bounded_128_hint_rejected() {
        constrain_lt_bounded::<128>(1, 2, false);
    }

    #[test(should_fail)]
    fn equal_lt_bounded_128_hint_rejected() {
        constrain_lt_bounded::<128>(TWO_POW_128 - 1, TWO_POW_128 - 1, true);
    }

    #[test(should_fail)]
    fn wrong_lt_bounded_128_hint_at_top_rejected() {
        constrain_lt_bounded::<128>(TWO_POW_128 - 1, 0, true);
    }

    #[test]
    fn field_order_small() {
        assert(lt(wit(0), wit(1)));
        assert(!lt(wit(1), wit(0)));
        assert(!lt(wit(1), wit(1)));
        assert(lte(wit(1), wit(1)));
        assert(gte(wit(1), wit(1)));
        assert(gt(wit(2), wit(1)));
        assert(!gt(wit(1), wit(2)));
        assert(eq(wit(3), wit(3)));
        assert(neq(wit(3), wit(4)));
        assert(!neq(wit(3), wit(3)));
        assert(is_zero(wit(0)));
        assert(!is_zero(wit(1)));
        assert(!is_zero(wit(0 - 1)));
    }

    #[test]
    fn field_order_limb_boundary() {
        // 2^128 - 1 has hi = 0; 2^128 has hi = 1, lo = 0
        assert(lt(wit(TWO_POW_128 - 1), wit(TWO_POW_128)));
        assert(!lt(wit(TWO_POW_128), wit(TWO_POW_128 - 1)));
        assert(lt(wit(TWO_POW_128), wit(TWO_POW_128 + 1)));
        // larger hi wins even with a smaller lo
        assert(lt(wit(TWO_POW_128 - 1), wit(2 * TWO_POW_128)));
        assert(gt(wit(2 * TWO_POW_128), wit(TWO_POW_128 + (TWO_POW_128 - 1))));
    }

    #[test]
    fn field_order_modulus_edge() {
        let pm1 = 0 - 1;
        assert(lt(wit(0), wit(pm1)));
        assert(!lt(wit(pm1), wit(0)));
        assert(lt(wit(pm1 - 1), wit(pm1)));
        assert(!lt(wit(pm1), wit(pm1)));
        // hi = PHI, lo = 0 is just below p - 1 (hi = PHI, lo = PLO - 1)
        assert(lt(wit(PHI * TWO_POW_128), wit(pm1)));
        assert(lt(wit(PHI * TWO_POW_128 - 1), wit(PHI * TWO_POW_128)));
        assert_eq(max(wit(pm1), wit(0)), pm1);
        assert_eq(min(wit(pm1), wit(0)), 0);
    }

    #[test]
    fn field_order_runtime_witnesses() {
        let a = wit(0 - 1);
        let b = wit(TWO_POW_128);
        assert(lt(wit(b), wit(a)));
        assert(gt(wit(a), wit(b)));
        assert(!lt(wit(a), wit(a)));
        assert(lte(wit(a), wit(a)));
        assert_eq(min(wit(a), wit(b)), b);
        assert_eq(max(wit(a), wit(b)), a);
    }

    #[test]
    fn field_min_max_clamp() {
        assert_eq(min(wit(3), wit(5)), 3);
        assert_eq(min(wit(5), wit(3)), 3);
        assert_eq(max(wit(3), wit(5)), 5);
        assert_eq(max(wit(5), wit(5)), 5);
        assert_eq(clamp(wit(7), wit(2), wit(5)), 5);
        assert_eq(clamp(wit(1), wit(2), wit(5)), 2);
        assert_eq(clamp(wit(4), wit(2), wit(5)), 4);
        assert_eq(clamp(wit(0 - 1), wit(2), wit(5)), 5);
        // lo > hi: the result is hi, defined, no failure
        assert_eq(clamp(wit(4), wit(9), wit(2)), 2);
    }

    #[test]
    fn bool_order() {
        assert(lt(wit(false), wit(true)));
        assert(!lt(wit(true), wit(false)));
        assert(!lt(wit(true), wit(true)));
        assert(!lt(wit(false), wit(false)));
        assert(eq(wit(true), wit(true)));
        assert(neq(wit(true), wit(false)));
        assert_eq(min(wit(true), wit(false)), false);
        assert_eq(max(wit(true), wit(false)), true);
        assert_eq(clamp(wit(false), wit(true), wit(true)), true);
    }

    #[test]
    fn unsigned_order_boundaries() {
        assert(lt(wit(0 as u8), wit(255 as u8)));
        assert(!lt(wit(255 as u8), wit(255 as u8)));
        assert(lte(wit(255 as u8), wit(255 as u8)));
        assert_eq(max(wit(0 as u8), wit(255 as u8)), 255);
        assert(lt(wit(0xfffe as u16), wit(0xffff as u16)));
        assert(gt(wit(0xffffffff as u32), wit(0 as u32)));
        assert(lt(wit(0 as u64), wit(0xffffffffffffffff as u64)));
        let m: u128 = 0xffffffffffffffffffffffffffffffff;
        assert(lt(wit(m - 1), wit(m)));
        assert(!lt(wit(m), wit(0)));
        assert_eq(min(wit(m), wit(0)), 0);
        assert_eq(clamp(wit(m), wit(1), wit(9)), 9);
    }

    #[test]
    fn signed_order_i8_corners() {
        let (lo, hi, m1, z) = (
            wit((0x80 as u8) as i8), wit((0x7f as u8) as i8), wit((0xff as u8) as i8),
            wit((0 as u8) as i8),
        );
        assert(lt(wit(lo), wit(hi)));
        assert(!lt(wit(hi), wit(lo)));
        assert(lt(wit(lo), wit(m1)));
        assert(lt(wit(m1), wit(z)));
        assert(!lt(wit(z), wit(m1)));
        assert(lt(wit(z), wit(hi)));
        assert(!lt(wit(lo), wit(lo)));
        assert(lte(wit(lo), wit(lo)));
        assert(gte(wit(hi), wit(m1)));
        assert_eq(min(wit(m1), wit(z)), m1);
        assert_eq(max(wit(m1), wit(z)), z);
        assert_eq(max(wit(lo), wit(hi)), hi);
        assert_eq(clamp(wit(lo), wit(m1), wit(hi)), m1);
        assert(eq(wit(m1), wit(m1)));
        assert(neq(wit(m1), wit(z)));
    }

    #[test]
    fn signed_order_runtime_witnesses() {
        let lo = wit((128 as u8) as i8);
        let hi = wit((127 as u8) as i8);
        let m1 = wit((255 as u8) as i8);
        assert(lt(wit(lo), wit(hi)));
        assert(lt(wit(m1), wit(hi)));
        assert(lt(wit(lo), wit(m1)));
        assert(!lt(wit(hi), wit(m1)));
        let a = wit((0x8000000000000000 as u64) as i64);
        let b = wit((0x7fffffffffffffff as u64) as i64);
        assert(lt(wit(a), wit(b)));
        assert(!lt(wit(b), wit(a)));
        assert_eq(min(wit(a), wit(b)), a);
    }

    #[test]
    fn signed_order_wider() {
        let (a, b, m1, z) = (
            wit((0x8000 as u16) as i16), wit((0x7fff as u16) as i16), wit((0xffff as u16) as i16),
            wit((0 as u16) as i16),
        );
        assert(lt(wit(a), wit(b)));
        assert(!lt(wit(b), wit(a)));
        assert(lt(wit(m1), wit(z)));
        assert(lt(wit(a), wit(m1)));
        assert_eq(min(wit(m1), wit(z)), m1);
        let (c, d, m5, m4) = (
            wit((0x80000000 as u32) as i32), wit((0x7fffffff as u32) as i32),
            wit((0xfffffffb as u32) as i32), wit((0xfffffffc as u32) as i32),
        );
        assert(lt(wit(c), wit(d)));
        assert(!lt(wit(d), wit(c)));
        assert(lt(wit(m5), wit(m4)));
        assert(gte(wit(m4), wit(m5)));
        assert_eq(clamp(wit(c), wit(m5), wit(d)), m5);
        let (e, f, m2, m1) = (
            wit((0x8000000000000000 as u64) as i64), wit((0x7fffffffffffffff as u64) as i64),
            wit((0xfffffffffffffffe as u64) as i64), wit((0xffffffffffffffff as u64) as i64),
        );
        assert(lt(wit(e), wit(f)));
        assert(gt(wit(f), wit(e)));
        assert(lt(wit(m2), wit(m1)));
        assert(!lt(wit(m1), wit(m2)));
        assert_eq(max(wit(m2), wit(m1)), m1);
        assert(neq(wit(m2), wit(m1)));
        assert(eq(wit(m1), wit(m1)));
    }

    #[test]
    fn cmp_bits_in_range() {
        let f = cmp_bits::<8>(wit(3), wit(200));
        assert(f.ok());
        assert(f.lt & !f.eq & !f.gt);
        assert(f.lte() & !f.gte() & f.neq());
        let g = cmp_bits::<8>(wit(255), wit(255));
        assert(g.ok() & g.eq & !g.lt & !g.gt);
        assert(g.lte() & g.gte() & !g.neq());
        let h = cmp_bits::<8>(wit(255), wit(0));
        assert(h.ok() & h.gt & !h.lt & !h.eq);
        let k = cmp_bits::<1>(wit(0), wit(1));
        assert(k.ok() & k.lt);
    }

    #[test]
    fn cmp_bits_out_of_range() {
        // b = 2^8 is out of range: all ordering flags false, b_ok false
        let f = cmp_bits::<8>(wit(3), wit(256));
        assert(f.a_ok);
        assert(!f.b_ok);
        assert(!f.ok());
        assert(!f.lt & !f.eq & !f.gt);
        assert(!f.lte() & !f.gte() & !f.neq());
        // p - 1 against 0: a out of range, no false eq from the clamp
        let g = cmp_bits::<8>(wit(0 - 1), wit(0));
        assert(!g.a_ok & g.b_ok);
        assert(!g.eq & !g.lt & !g.gt);
        let h = cmp_bits::<64>(wit(0x10000000000000001), wit(0x10000000000000001));
        assert(!h.a_ok & !h.b_ok & !h.eq);
    }

    #[test]
    fn cmp_bits_wide() {
        let f = cmp_bits::<128>(wit(TWO_POW_128 - 2), wit(TWO_POW_128 - 1));
        assert(f.ok() & f.lt);
        let g = cmp_bits::<128>(wit(TWO_POW_128), wit(0));
        assert(!g.a_ok & g.b_ok & !g.gt);
        let h = cmp_bits::<127>(wit(two_pow::<127>() - 1), wit(two_pow::<127>()));
        assert(h.a_ok & !h.b_ok & !h.lt);
        let k = cmp_bits::<126>(wit(two_pow::<126>() - 1), wit(0));
        assert(k.ok() & k.gt);
    }

    // cmp_bits::<N> on the witnesses 0, 2^N - 1, 2^N and p - 1, pairwise.
    fn check_cmp_wide<let N: u32>() {
        let t = two_pow::<N>();
        let xs = [wit(0), wit(t - 1), wit(t), wit(0 - 1)];
        let in_range = [true, true, false, false];
        for i in 0..4 {
            for j in 0..4 {
                let f = cmp_bits::<N>(wit(xs[i]), wit(xs[j]));
                let ok = in_range[i] & in_range[j];
                assert_eq(f.a_ok, in_range[i]);
                assert_eq(f.b_ok, in_range[j]);
                assert_eq(f.lt, ok & (i < j));
                assert_eq(f.eq, ok & (i == j));
                assert_eq(f.gt, ok & (i > j));
            }
        }
    }

    #[test]
    fn cmp_bits_wide_widths() {
        check_cmp_wide::<129>();
        check_cmp_wide::<160>();
        check_cmp_wide::<248>();
        check_cmp_wide::<253>();
        // same high limb, the low limb decides
        let f = cmp_bits::<160>(wit(TWO_POW_128 + 5), wit(TWO_POW_128 + 4));
        assert(f.ok() & f.gt);
        // larger high limb wins over a larger low limb
        let g = cmp_bits::<160>(wit(TWO_POW_128 + (TWO_POW_128 - 1)), wit(2 * TWO_POW_128));
        assert(g.ok() & g.lt);
    }
}
