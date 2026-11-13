//! Range flags: the total counterparts of `assert_max_bit_size` and of the
//! range check the compiler puts on every integer-typed entry-point
//! parameter. Both of those are input-falsifiable: an input outside the
//! range makes the circuit unsatisfiable. The functions here return a
//! determined flag instead, and the clamps return a value that always
//! satisfies the range.
//!
//! Widths: 1 <= N <= 253. Every Field is below 2^254, so a range flag for
//! N >= 254 would be the constant true. For N <= 128 the condition is on
//! the low canonical limb (and a zero high limb); for 129 <= N <= 253 it
//! is on the high limb alone.
//!
//! Canonicity of a Field is not a range question: a Field witness is its
//! residue mod p, so there is no second representation to rule out. The
//! canonicity of byte and bit encodings is a range question on the
//! encoded integer and lives in convert.nr (from_le_bytes_or and friends).

use crate::core;
use std::static_assert;

/// True iff the canonical integer value of x is below 2^N, for
/// 1 <= N <= 253.
///
/// Constraints: for N <= 127, core::fits_bits::<N>: the core::limbs set
/// (two 128-bit RANGEs on the hinted limbs, the reconstruction, and the
/// borrow-bit compare against the modulus limbs with two more 128-bit
/// RANGEs), one split of the low limb at bit N (RANGE N and RANGE 128 - N
/// on hinted parts plus the reconstruction), and two is_zero gadgets. For
/// N = 128, core::fits_128: the limbs set and one is_zero gadget. For
/// 129 <= N <= 253, core::fits_bits_wide::<N - 128>: the limbs set, one
/// split of the high limb at bit N - 128 (same shape as the low-limb
/// split), and one is_zero gadget on the high limb's upper part.
/// Classification: every assert is hint-satisfiable for every Field,
/// including p - 1 (canonical limbs and the split of a 128-bit limb always
/// exist). Hint rule: the honest hints are the canonical limbs and the
/// exact split. Determined: canonical limbs and the split are unique, and
/// the is_zero flags are determined, so the flag is fixed by x.
pub fn fits_bits<let N: u32>(x: Field) -> bool {
    static_assert((N >= 1) & (N <= 253), "fits_bits: N must be in 1..=253");
    // N % 128 is N on 1..=127 and N - 128 on 129..=253. In the branches
    // not taken it keeps every width non-negative (128 - N in the
    // low-limb split): nargo checks generic arithmetic before any
    // static_assert, so a negative width would hide this message, and
    // those of callers such as mul_div_wide_or, behind a generic-overflow
    // error. The same in the dispatch below.
    if N == 128 {
        core::fits_128(x)
    } else if N < 128 {
        core::fits_bits::<N % 128>(x)
    } else {
        core::fits_bits_wide::<N % 128>(x)
    }
}

/// (value, ok) with ok = fits_bits::<N>(x) and value = ok ? x : 0, for
/// 1 <= N <= 253. The value always satisfies the N-bit range, so it can
/// feed a gadget whose precondition is that range.
///
/// Constraints: those of fits_bits::<N> plus select arithmetic (no
/// assert). Classification and hint rule as fits_bits. Determined: ok is
/// determined and the value is a function of x and ok.
pub fn clamp_bits_or<let N: u32>(x: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 253), "clamp_bits_or: N must be in 1..=253");
    if N == 128 {
        core::clamp_128_or(x)
    } else if N < 128 {
        core::clamp_bits_or::<N % 128>(x)
    } else {
        let ok = core::fits_bits_wide::<N % 128>(x);
        (core::select_field(ok, x, 0), ok)
    }
}

/// True iff x is 0 or 1. Same constraints and argument as fits_bits::<1>.
/// convert::bool_or turns the same test into a bool value.
pub fn fits_u1(x: Field) -> bool {
    fits_bits::<1>(x)
}

/// True iff x < 2^8: the flag form of the range check a u8 entry-point
/// parameter gets. Constraints and argument as fits_bits::<8>.
pub fn fits_u8(x: Field) -> bool {
    fits_bits::<8>(x)
}

/// True iff x < 2^16. Constraints and argument as fits_bits::<16>.
pub fn fits_u16(x: Field) -> bool {
    fits_bits::<16>(x)
}

/// True iff x < 2^32. Constraints and argument as fits_bits::<32>.
pub fn fits_u32(x: Field) -> bool {
    fits_bits::<32>(x)
}

/// True iff x < 2^64. Constraints and argument as fits_bits::<64>.
pub fn fits_u64(x: Field) -> bool {
    fits_bits::<64>(x)
}

/// True iff x < 2^128. Constraints and argument as fits_bits::<128>.
pub fn fits_u128(x: Field) -> bool {
    fits_bits::<128>(x)
}

mod tests {
    use crate::convert::PHI;
    use crate::core::{two_pow, TWO_POW_128};
    use crate::test_support::wit;
    use super::{
        clamp_bits_or, fits_bits, fits_u1, fits_u128, fits_u16, fits_u32, fits_u64, fits_u8,
    };

    #[test]
    fn fits_u1_boundaries() {
        assert(fits_u1(wit(0)));
        assert(fits_u1(wit(1)));
        assert(!fits_u1(wit(2)));
        assert(!fits_u1(wit(3)));
        assert(!fits_u1(wit(0 - 1)));
        assert(!fits_u1(wit(TWO_POW_128)));
    }

    #[test]
    fn fits_u8_boundaries() {
        assert(fits_u8(wit(0)));
        assert(fits_u8(wit(1)));
        assert(fits_u8(wit(255)));
        assert(!fits_u8(wit(256)));
        assert(!fits_u8(wit(257)));
        assert(!fits_u8(wit(0 - 1)));
        assert(!fits_u8(wit(TWO_POW_128)));
        assert(!fits_u8(wit(TWO_POW_128 + 1)));
    }

    #[test]
    fn fits_u16_boundaries() {
        assert(fits_u16(wit(0)));
        assert(fits_u16(wit(1)));
        assert(fits_u16(wit(0xffff)));
        assert(!fits_u16(wit(0x10000)));
        assert(!fits_u16(wit(0x10001)));
        assert(!fits_u16(wit(0 - 1)));
        assert(!fits_u16(wit(TWO_POW_128)));
    }

    #[test]
    fn fits_u32_boundaries() {
        assert(fits_u32(wit(0)));
        assert(fits_u32(wit(1)));
        assert(fits_u32(wit(0xffffffff)));
        assert(!fits_u32(wit(0x100000000)));
        assert(!fits_u32(wit(0x100000001)));
        assert(!fits_u32(wit(0 - 1)));
        assert(!fits_u32(wit(TWO_POW_128)));
    }

    #[test]
    fn fits_u64_boundaries() {
        assert(fits_u64(wit(0)));
        assert(fits_u64(wit(1)));
        assert(fits_u64(wit(0xffffffffffffffff)));
        assert(!fits_u64(wit(0x10000000000000000)));
        assert(!fits_u64(wit(0x10000000000000001)));
        assert(!fits_u64(wit(0 - 1)));
        assert(!fits_u64(wit(TWO_POW_128)));
    }

    #[test]
    fn fits_u128_boundaries() {
        assert(fits_u128(wit(0)));
        assert(fits_u128(wit(1)));
        assert(fits_u128(wit(TWO_POW_128 - 1)));
        assert(!fits_u128(wit(TWO_POW_128)));
        assert(!fits_u128(wit(TWO_POW_128 + 1)));
        assert(!fits_u128(wit(0 - 1)));
        // high limb nonzero but low limb zero
        assert(!fits_u128(wit(TWO_POW_128 * 5)));
    }

    #[test]
    fn fits_bits_odd_widths() {
        assert(fits_bits::<127>(wit(two_pow::<127>() - 1)));
        assert(!fits_bits::<127>(wit(two_pow::<127>())));
        assert(fits_bits::<3>(wit(7)));
        assert(!fits_bits::<3>(wit(8)));
        // p - 1 is a large canonical integer, never small
        assert(!fits_bits::<127>(wit(0 - 1)));
        assert(!fits_bits::<128>(wit(0 - 1)));
    }

    // fits_bits and clamp_bits_or::<N> on the witnesses 0, 2^N - 1, 2^N and
    // p - 1.
    fn check_wide<let N: u32>() {
        let t = two_pow::<N>();
        let xs = [wit(0), wit(t - 1), wit(t), wit(0 - 1)];
        let expect = [true, true, false, false];
        for i in 0..4 {
            assert_eq(fits_bits::<N>(wit(xs[i])), expect[i]);
            let (v, ok) = clamp_bits_or::<N>(wit(xs[i]));
            assert_eq(ok, expect[i]);
            assert_eq(v, if expect[i] { xs[i] } else { 0 });
        }
    }

    #[test]
    fn fits_bits_wide_widths() {
        check_wide::<129>();
        check_wide::<160>();
        check_wide::<248>();
        check_wide::<253>();
        // the high limb at its largest, PHI * 2^128, is at least 2^253
        assert(!fits_bits::<253>(wit(PHI * TWO_POW_128)));
        // a nonzero low limb does not matter above 128 bits
        assert(fits_bits::<129>(wit(TWO_POW_128 + (TWO_POW_128 - 1))));
        assert(!fits_bits::<129>(wit(TWO_POW_128 * 2)));
    }

    #[test]
    fn clamp_bits_in_and_out() {
        let (v, ok) = clamp_bits_or::<8>(wit(255));
        assert(ok);
        assert_eq(v, 255);
        let (v, ok) = clamp_bits_or::<8>(wit(256));
        assert(!ok);
        assert_eq(v, 0);
        let (v, ok) = clamp_bits_or::<128>(wit(TWO_POW_128 - 1));
        assert(ok);
        assert_eq(v, TWO_POW_128 - 1);
        let (v, ok) = clamp_bits_or::<128>(wit(TWO_POW_128));
        assert(!ok);
        assert_eq(v, 0);
        let (v, ok) = clamp_bits_or::<128>(wit(0 - 1));
        assert(!ok);
        assert_eq(v, 0);
        let (v, ok) = clamp_bits_or::<1>(wit(0 - 1));
        assert(!ok);
        assert_eq(v, 0);
    }
}
