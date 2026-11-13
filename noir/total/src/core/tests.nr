use crate::test_support::wit;
use super::{
    add_split, clamp_bits_or, constrain_add_split, constrain_div_split, constrain_low_bit,
    constrain_lt_bounded, constrain_mul_split, constrain_mul_split_short, constrain_split_128_at,
    constrain_split_at, constrain_sub_split, div_split, eq, fits_128, fits_bits, fits_bits_wide,
    is_zero, limbs, low_bit, lt_bounded, mul_split, mul_split_short, select_field, split_128_at,
    split_at, sub_split, two_pow, TWO_POW_128,
};

#[test]
fn two_pow_values() {
    assert_eq(two_pow::<0>(), 1);
    assert_eq(two_pow::<1>(), 2);
    assert_eq(two_pow::<64>(), 0x10000000000000000);
    assert_eq(two_pow::<128>(), TWO_POW_128);
}

#[test]
fn is_zero_flags() {
    assert(is_zero(wit(0)));
    assert(!is_zero(wit(1)));
    assert(!is_zero(wit(0 - 1)));
    assert(eq(wit(5), wit(5)));
    assert(!eq(wit(5), wit(6)));
}

#[test]
fn select_picks_sides() {
    assert_eq(select_field(wit(true), wit(7), wit(9)), 7);
    assert_eq(select_field(wit(false), wit(7), wit(9)), 9);
}

#[test]
fn limbs_of_edges() {
    let (lo, hi) = limbs(wit(0));
    assert_eq(lo, 0);
    assert_eq(hi, 0);
    let (lo2, hi2) = limbs(wit(TWO_POW_128));
    assert_eq(lo2, 0);
    assert_eq(hi2, 1);
    // p - 1 decomposes to the modulus limbs minus one on the low limb
    let (lo3, hi3) = limbs(wit(0 - 1));
    assert_eq(lo3 + TWO_POW_128 * hi3, 0 - 1);
    assert(!is_zero(wit(hi3)));
}

#[test]
fn fits_bits_boundaries() {
    assert(fits_bits::<64>(wit(0)));
    assert(fits_bits::<64>(wit(1)));
    assert(fits_bits::<64>(wit(0xffffffffffffffff)));
    assert(!fits_bits::<64>(wit(0x10000000000000000)));
    assert(!fits_bits::<64>(wit(0x10000000000000001)));
    assert(!fits_bits::<64>(wit(0 - 1)));
    assert(fits_bits::<1>(wit(1)));
    assert(!fits_bits::<1>(wit(2)));
    assert(fits_bits::<127>(wit(two_pow::<127>() - 1)));
    assert(!fits_bits::<127>(wit(two_pow::<127>())));
    assert(fits_128(wit(TWO_POW_128 - 1)));
    assert(!fits_128(wit(TWO_POW_128)));
    assert(!fits_128(wit(0 - 1)));
}

#[test]
fn clamp_keeps_or_zeroes() {
    let (v, ok) = clamp_bits_or::<8>(wit(255));
    assert(ok);
    assert_eq(v, 255);
    let (v2, ok2) = clamp_bits_or::<8>(wit(256));
    assert(!ok2);
    assert_eq(v2, 0);
}

#[test]
fn split_round_trips() {
    let (lo, rest) = split_128_at::<64>(wit(0x123456789abcdef0fedcba9876543210));
    assert_eq(lo, 0xfedcba9876543210);
    assert_eq(rest, 0x123456789abcdef0);
    let (lo1, rest1) = split_128_at::<1>(wit(3));
    assert_eq(lo1, 1);
    assert_eq(rest1, 1);
}

#[test]
fn lt_bounded_cases() {
    assert(lt_bounded::<64>(wit(0), wit(1)));
    assert(!lt_bounded::<64>(wit(1), wit(0)));
    assert(!lt_bounded::<64>(wit(5), wit(5)));
    assert(lt_bounded::<64>(wit(0xfffffffffffffffe), wit(0xffffffffffffffff)));
}

#[test]
fn add_split_boundaries() {
    let (lo, c) = add_split::<64>(wit(0xffffffffffffffff), wit(0xffffffffffffffff));
    assert(c);
    assert_eq(lo, 0xfffffffffffffffe);
    let (lo2, c2) = add_split::<64>(wit(0), wit(0));
    assert(!c2);
    assert_eq(lo2, 0);
}

#[test]
fn mul_split_boundaries() {
    let m = 0xffffffffffffffff;
    let (lo, hi) = mul_split::<64>(wit(m), wit(m));
    // (2^64 - 1)^2 = 2^128 - 2^65 + 1
    assert_eq(lo, 1);
    assert_eq(hi, 0xfffffffffffffffe);
    let (lo2, hi2) = mul_split::<64>(wit(m), wit(0));
    assert_eq(lo2, 0);
    assert_eq(hi2, 0);
}

#[test]
fn div_split_cases() {
    let (q, r) = div_split::<64>(wit(17), wit(5));
    assert_eq(q, 3);
    assert_eq(r, 2);
    let (q2, r2) = div_split::<64>(wit(0), wit(1));
    assert_eq(q2, 0);
    assert_eq(r2, 0);
    let (q3, r3) = div_split::<64>(wit(0xffffffffffffffff), wit(1));
    assert_eq(q3, 0xffffffffffffffff);
    assert_eq(r3, 0);
    let (q4, r4) = div_split::<64>(wit(5), wit(0xffffffffffffffff));
    assert_eq(q4, 0);
    assert_eq(r4, 5);
}

// Wrong-hint tests: the soundness constraints must reject a
// dishonest prover's hints.

#[test(should_fail)]
fn wrong_split_hint_rejected() {
    constrain_split_128_at::<64>(0x1_0000000000000000, 0, 0);
}

#[test(should_fail)]
fn wrong_lt_hint_rejected() {
    constrain_lt_bounded::<64>(1, 2, false);
}

#[test(should_fail)]
fn equal_lt_hint_rejected() {
    constrain_lt_bounded::<64>(5, 5, true);
}

#[test(should_fail)]
fn wrong_carry_rejected() {
    let _ = constrain_add_split::<64>(1, 1, true);
}

#[test(should_fail)]
fn wrong_mul_split_rejected() {
    constrain_mul_split::<64>(3, 5, 16, 0);
}

#[test(should_fail)]
fn div_remainder_too_big_rejected() {
    // 17 = 2*5 + 7 reconstructs, but r >= b1 must be rejected
    constrain_div_split::<64>(17, 5, 2, 7);
}

// The 128-bit caps of add_split, sub_split and lt_bounded, and split_at
// with a two-bit high part.

global M128: Field = 0xffffffffffffffffffffffffffffffff;

#[test]
fn add_sub_lt_at_128_bits_honest() {
    assert_eq(add_split::<128>(wit(M128), wit(M128)), (M128 - 1, true));
    assert_eq(add_split::<128>(wit(M128), wit(0)), (M128, false));
    assert_eq(add_split::<128>(wit(two_pow::<127>()), wit(two_pow::<127>())), (0, true));
    assert_eq(sub_split::<128>(wit(0), wit(M128)), (1, true));
    assert_eq(sub_split::<128>(wit(M128), wit(M128)), (0, false));
    assert_eq(sub_split::<128>(wit(0), wit(1)), (M128, true));
    assert(lt_bounded::<128>(wit(M128 - 1), wit(M128)));
    assert(!lt_bounded::<128>(wit(M128), wit(0)));
    assert(lt_bounded::<127>(wit(0), wit(two_pow::<127>() - 1)));
    assert_eq(
        add_split::<127>(wit(two_pow::<127>() - 1), wit(two_pow::<127>() - 1)),
        (two_pow::<127>() - 2, true),
    );
}

#[test(should_fail)]
fn add_128_missing_carry_rejected() {
    let _ = constrain_add_split::<128>(M128, M128, false);
}

#[test(should_fail)]
fn add_128_spurious_carry_rejected() {
    let _ = constrain_add_split::<128>(1, 2, true);
}

#[test(should_fail)]
fn sub_128_missing_borrow_rejected() {
    let _ = constrain_sub_split::<128>(0, M128, false);
}

#[test(should_fail)]
fn lt_127_wrong_flag_rejected() {
    constrain_lt_bounded::<127>(two_pow::<127>() - 1, 0, true);
}

#[test]
fn split_at_two_bit_high_part_honest() {
    // the largest operand of the form 255 + 255 + 128 = 638 = 2*256 + 126
    assert_eq(split_at::<8, 2>(wit(638)), (126, 2));
    assert_eq(split_at::<8, 2>(wit(128)), (128, 0));
    assert_eq(split_at::<8, 2>(wit(1023)), (255, 3));
    assert_eq(split_at::<64, 2>(wit(two_pow::<66>() - 1)), (two_pow::<64>() - 1, 3));
}

#[test(should_fail)]
fn split_at_high_part_too_big_rejected() {
    // hi = 3 needs lo = 638 - 768 < 0, which wraps past the 8-bit range
    constrain_split_at::<8, 2>(638, 638 - 768, 3);
}

#[test(should_fail)]
fn split_at_high_part_past_its_width_rejected() {
    constrain_split_at::<8, 2>(638 + 256, 126, 4);
}

#[test(should_fail)]
fn split_at_low_part_with_borrow_rejected() {
    constrain_split_at::<8, 2>(638, 126 + 256, 1);
}

// mul_split_short at its widest, N = 127, where the high part is one bit
// narrower than the low part.

/// p mod 2^127 and p >> 127 (about 2^126.6): a split of the field's zero
/// with the low part below 2^127 and the high part below 2^127 but not
/// below 2^126.
global P_LO_127: Field = 0x2833e84879b9709143e1f593f0000001;
global P_HI_127: Field = 0x60c89ce5c263405370a08b6d0302b0ba;

#[test]
fn mul_split_short_honest_extremes() {
    let m = two_pow::<127>();
    // the largest product the precondition allows: (2^127 - 1) * 2^126
    assert_eq(
        mul_split_short::<127>(wit(m - 1), wit(two_pow::<126>())),
        (m - two_pow::<126>(), two_pow::<126>() - 1),
    );
    assert_eq(mul_split_short::<127>(wit(m - 1), wit(1)), (m - 1, 0));
    assert_eq(mul_split_short::<127>(wit(0), wit(two_pow::<126>())), (0, 0));
    assert_eq(mul_split_short::<127>(wit(3), wit(two_pow::<126>())), (two_pow::<126>(), 1));
    assert_eq(mul_split_short::<2>(wit(3), wit(2)), (2, 1));
}

#[test]
fn split_of_p_has_a_high_part_past_126_bits() {
    // the alias below passes the ranges a 127-bit high part would have;
    // the 126-bit range of mul_split_short is what rejects it
    assert_eq(P_LO_127 + P_HI_127 * two_pow::<127>(), 0);
    constrain_mul_split::<127>(wit(0), wit(0), wit(P_LO_127), wit(P_HI_127));
}

#[test(should_fail)]
fn mul_split_short_p_alias_rejected() {
    constrain_mul_split_short::<127>(0, 0, P_LO_127, P_HI_127);
}

#[test(should_fail)]
fn mul_split_short_low_part_off_by_one_rejected() {
    let m = two_pow::<127>();
    constrain_mul_split_short::<127>(
        m - 1,
        two_pow::<126>(),
        m - two_pow::<126>() + 1,
        two_pow::<126>() - 1,
    );
}

#[test(should_fail)]
fn mul_split_short_low_part_past_its_width_rejected() {
    // move one unit of 2^127 from the high part into the low part
    let m = two_pow::<127>();
    constrain_mul_split_short::<127>(
        m - 1,
        two_pow::<126>(),
        2 * m - two_pow::<126>(),
        two_pow::<126>() - 2,
    );
}

#[test(should_fail)]
fn mul_split_short_negative_high_part_rejected() {
    // a*b = 2^126: hi' = -1 with lo' = 2^126 + 2^127 fails both ranges
    let m = two_pow::<127>();
    constrain_mul_split_short::<127>(1, two_pow::<126>(), two_pow::<126>() + m, 0 - 1);
}

#[test]
fn fits_bits_wide_boundaries() {
    // K = N - 128
    assert(fits_bits_wide::<1>(wit(two_pow::<129>() - 1)));
    assert(!fits_bits_wide::<1>(wit(two_pow::<129>())));
    assert(fits_bits_wide::<125>(wit(two_pow::<253>() - 1)));
    assert(!fits_bits_wide::<125>(wit(two_pow::<253>())));
    // p - 1 is above 2^253
    assert(!fits_bits_wide::<125>(wit(0 - 1)));
    assert(fits_bits_wide::<32>(wit(0)));
}

#[test]
fn low_bit_cases() {
    assert(!low_bit(wit(0)));
    assert(low_bit(wit(1)));
    assert(!low_bit(wit(TWO_POW_128 - 2)));
    assert(low_bit(wit(TWO_POW_128 - 1)));
    constrain_low_bit(wit(5), wit(true), wit(2));
    constrain_low_bit(wit(TWO_POW_128 - 1), wit(true), wit(two_pow::<127>() - 1));
}

#[test(should_fail)]
fn low_bit_flipped_bit_rejected() {
    constrain_low_bit(5, false, 2);
}

#[test(should_fail)]
fn low_bit_flipped_bit_compensated_rejected() {
    // 0 + 2*(2 + 1/2) = 5 in the field: only the 127-bit range on the
    // upper part rules out the half-integer witness
    constrain_low_bit(5, false, 2 + 1 / 2);
}

#[test(should_fail)]
fn low_bit_p_alias_rejected() {
    // 1 + 2*(p - 1)/2 = p = 0: the alias of an even 0 with bit 1
    constrain_low_bit(0, true, (0 - 1) / 2);
}
