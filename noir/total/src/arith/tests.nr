use crate::core::{constrain_add_split, constrain_sub_split, two_pow, TWO_POW_128, TWO_POW_64};
use crate::test_support::wit;
use super::{
    add_or, constrain_div_128, constrain_inverse, constrain_low_bits, constrain_mul_128,
    constrain_sqrt, div_128, div_or, div_rem_or, euler, field_div_or, hint_div_128, hint_mul_lo_128,
    hint_sqrt, inverse_or, mod_or, mul_128, mul_or, neg_or, pow_or, Saturating, saturating_add_or,
    saturating_mul_or, saturating_sub_or, sqrt_canonical_or, SQRT_NON_RESIDUE, sqrt_or, sub_or,
    TotalArith, wrapping_add_or, wrapping_mul_or, wrapping_neg_or, wrapping_sub_or,
};
use std::ops::{WrappingAdd, WrappingMul, WrappingSub};

/// The testing-rule boundaries for width N: 0, 1, 2^N - 1, 2^N,
/// 2^N + 1, p - 1.
fn bounds<let N: u32>() -> [Field; 6] {
    let m = two_pow::<N>();
    [0, 1, m - 1, m, m + 1, 0 - 1]
}

fn clamp_ref(x: Field, m: Field) -> Field {
    if x.lt(m) {
        x
    } else {
        0
    }
}

fn check_add_sub<let N: u32>() {
    let m = two_pow::<N>();
    let vals = bounds::<N>();
    for i in 0..6 {
        for j in 0..6 {
            let (a, b) = (vals[i], vals[j]);
            let ok_in = a.lt(m) & b.lt(m);
            let (a1, b1) = (clamp_ref(a, m), clamp_ref(b, m));
            let s = a1 + b1;
            let carry = !s.lt(m);
            let lo = if carry { s - m } else { s };
            let add_ok = ok_in & !carry;
            assert_eq(add_or::<N>(wit(a), wit(b)), (if add_ok { lo } else { 0 }, add_ok));
            assert_eq(wrapping_add_or::<N>(wit(a), wit(b)), (lo, ok_in));
            assert_eq(
                saturating_add_or::<N>(wit(a), wit(b)),
                (if carry { m - 1 } else { lo }, ok_in),
            );
            let borrow = a1.lt(b1);
            let diff = if borrow { a1 - b1 + m } else { a1 - b1 };
            let sub_ok = ok_in & !borrow;
            assert_eq(sub_or::<N>(wit(a), wit(b)), (if sub_ok { diff } else { 0 }, sub_ok));
            assert_eq(wrapping_sub_or::<N>(wit(a), wit(b)), (diff, ok_in));
            assert_eq(
                saturating_sub_or::<N>(wit(a), wit(b)),
                (if borrow { 0 } else { diff }, ok_in),
            );
        }
    }
}

fn check_mul<let N: u32>() {
    let m = two_pow::<N>();
    let vals = bounds::<N>();
    for i in 0..6 {
        for j in 0..6 {
            let (a, b) = (vals[i], vals[j]);
            let ok_in = a.lt(m) & b.lt(m);
            let (a1, b1) = (clamp_ref(a, m), clamp_ref(b, m));
            // The clamped boundary values are 0, 1 and m - 1; the only
            // overflowing product is (m - 1)^2 = (m - 2)*m + 1 (for N >= 2;
            // at N = 128 it is past p, so it is not formed here).
            let over = (N > 1) & (a1 == m - 1) & (b1 == m - 1);
            let lo = if over { 1 } else { a1 * b1 };
            let mul_ok = ok_in & !over;
            assert_eq(mul_or::<N>(wit(a), wit(b)), (if mul_ok { lo } else { 0 }, mul_ok));
            assert_eq(wrapping_mul_or::<N>(wit(a), wit(b)), (lo, ok_in));
            assert_eq(
                saturating_mul_or::<N>(wit(a), wit(b)),
                (if over { m - 1 } else { lo }, ok_in),
            );
        }
    }
}

fn check_div<let N: u32>() {
    let m = two_pow::<N>();
    let vals = bounds::<N>();
    for i in 0..6 {
        for j in 0..6 {
            let (a, b) = (vals[i], vals[j]);
            let (a1, b1) = (clamp_ref(a, m), clamp_ref(b, m));
            let ok = a.lt(m) & b.lt(m) & (b1 != 0);
            let d = if ok { b1 } else { 1 };
            let n = if ok { a1 } else { 0 };
            let q = ((n as u128) / (d as u128)) as Field;
            let r = ((n as u128) % (d as u128)) as Field;
            assert_eq(div_rem_or::<N>(wit(a), wit(b)), (q, r, ok));
            assert_eq(div_or::<N>(wit(a), wit(b)), (q, ok));
            assert_eq(mod_or::<N>(wit(a), wit(b)), (r, ok));
        }
    }
}

#[test]
fn add_sub_boundaries_all_widths() {
    check_add_sub::<1>();
    check_add_sub::<8>();
    check_add_sub::<64>();
    check_add_sub::<126>();
    check_add_sub::<127>();
    check_add_sub::<128>();
}

#[test]
fn mul_boundaries_all_widths() {
    check_mul::<1>();
    check_mul::<8>();
    check_mul::<64>();
    check_mul::<126>();
    check_mul::<127>();
    check_mul::<128>();
}

#[test]
fn div_boundaries_all_widths() {
    check_div::<1>();
    check_div::<8>();
    check_div::<64>();
    check_div::<126>();
    check_div::<127>();
    check_div::<128>();
}

#[test]
fn mid_range_values_match_native() {
    let a: u64 = 0xdeadbeefcafebabe;
    let b: u64 = 0x123456789;
    let (v, ok) = wrapping_mul_or::<64>(wit(a as Field), wit(b as Field));
    assert(ok);
    assert_eq(v, a.wrapping_mul(b) as Field);
    assert(!mul_or::<64>(wit(a as Field), wit(b as Field)).1);
    let (v2, ok2) = add_or::<64>(wit(a as Field), wit(b as Field));
    assert(ok2);
    assert_eq(v2, (a + b) as Field);
    let (q, r, ok3) = div_rem_or::<64>(wit(a as Field), wit(b as Field));
    assert(ok3);
    assert_eq(q, (a / b) as Field);
    assert_eq(r, (a % b) as Field);
    // 126-bit: (2^125 + 3) * 2 overflows 126 bits by exactly one carry
    let h = two_pow::<125>();
    let (v3, ok3) = mul_or::<126>(wit(h + 3), wit(2));
    assert(!ok3);
    assert_eq(v3, 0);
    assert_eq(wrapping_mul_or::<126>(wit(h + 3), wit(2)), (6, true));
    let (v4, ok4) = mul_or::<126>(wit(h - 1), wit(2));
    assert(ok4);
    assert_eq(v4, two_pow::<126>() - 2);
}

#[test]
fn neg_on_the_n_bit_domain() {
    assert_eq(wrapping_neg_or::<8>(wit(0)), (0, true));
    assert_eq(wrapping_neg_or::<8>(wit(1)), (255, true));
    assert_eq(wrapping_neg_or::<8>(wit(255)), (1, true));
    assert_eq(wrapping_neg_or::<8>(wit(256)), (0, false));
    assert_eq(wrapping_neg_or::<8>(wit(257)), (0, false));
    assert_eq(wrapping_neg_or::<8>(wit(0 - 1)), (0, false));
    assert_eq(neg_or::<8>(wit(0)), (0, true));
    assert_eq(neg_or::<8>(wit(1)), (0, false));
    assert_eq(neg_or::<127>(wit(two_pow::<127>() - 1)), (0, false));
    assert_eq(wrapping_neg_or::<127>(wit(1)), (two_pow::<127>() - 1, true));
    assert_eq(neg_or::<8>(wit(0 - 1)), (0, false));
    assert_eq(wrapping_neg_or::<126>(wit(1)), (two_pow::<126>() - 1, true));
    assert_eq(wrapping_neg_or::<126>(wit(two_pow::<126>())), (0, false));
}

#[test]
fn pow_cases() {
    assert_eq(pow_or::<8, 8>(wit(2), wit(7)), (128, true));
    assert_eq(pow_or::<8, 8>(wit(2), wit(8)), (0, false));
    assert_eq(pow_or::<8, 8>(wit(3), wit(5)), (243, true));
    assert_eq(pow_or::<8, 8>(wit(3), wit(6)), (0, false));
    // 0^0 = 1
    assert_eq(pow_or::<8, 8>(wit(0), wit(0)), (1, true));
    assert_eq(pow_or::<8, 8>(wit(0), wit(255)), (0, true));
    assert_eq(pow_or::<8, 8>(wit(1), wit(255)), (1, true));
    assert_eq(pow_or::<8, 8>(wit(255), wit(1)), (255, true));
    assert_eq(pow_or::<8, 8>(wit(255), wit(2)), (0, false));
    // an out-of-range base or exponent: flagged, value 0
    assert_eq(pow_or::<8, 8>(wit(256), wit(3)), (0, false));
    assert_eq(pow_or::<8, 8>(wit(0 - 1), wit(3)), (0, false));
    assert_eq(pow_or::<8, 8>(wit(2), wit(256)), (0, false));
    assert_eq(pow_or::<8, 8>(wit(2), wit(0 - 1)), (0, false));
    assert_eq(pow_or::<1, 1>(wit(0 - 1), wit(0 - 1)), (0, false));
    // 64 bits: 255^8 < 2^64 <= 256^8; 2^63 fits, 2^64 does not
    assert_eq(pow_or::<64, 7>(wit(255), wit(8)), (17878103347812890625, true));
    assert_eq(pow_or::<64, 7>(wit(256), wit(8)), (0, false));
    assert_eq(pow_or::<64, 7>(wit(2), wit(63)), (two_pow::<63>(), true));
    assert_eq(pow_or::<64, 7>(wit(2), wit(64)), (0, false));
    // a single exponent bit (no hint)
    assert_eq(pow_or::<126, 1>(wit(two_pow::<126>() - 1), wit(1)), (two_pow::<126>() - 1, true));
    assert_eq(pow_or::<64, 1>(wit(7), wit(0)), (1, true));
    assert_eq(pow_or::<64, 1>(wit(0), wit(0)), (1, true));
    assert_eq(pow_or::<64, 1>(wit(0), wit(1)), (0, true));
    assert_eq(pow_or::<64, 1>(wit(7), wit(2)), (0, false));
    assert_eq(pow_or::<64, 1>(wit(two_pow::<64>()), wit(1)), (0, false));
    // 127 and 128 bits: the multiply runs through mul_128_full
    assert_eq(pow_or::<128, 8>(wit(2), wit(127)), (two_pow::<127>(), true));
    assert_eq(pow_or::<128, 8>(wit(2), wit(128)), (0, false));
    assert_eq(pow_or::<127, 8>(wit(2), wit(126)), (two_pow::<126>(), true));
    assert_eq(pow_or::<127, 8>(wit(2), wit(127)), (0, false));
    assert_eq(
        pow_or::<128, 2>(wit(0xffffffffffffffff), wit(2)),
        (0xfffffffffffffffe0000000000000001, true),
    );
    assert_eq(pow_or::<128, 2>(wit(0x10000000000000000), wit(2)), (0, false));
}

#[test]
fn field_inverse_and_division() {
    assert_eq(inverse_or(wit(0)), (0, false));
    assert_eq(inverse_or(wit(1)), (1, true));
    assert_eq(inverse_or(wit(0 - 1)), (0 - 1, true));
    let (i2, ok2) = inverse_or(wit(2));
    assert(ok2);
    assert_eq(i2 * 2, 1);
    let (ib, okb) = inverse_or(wit(two_pow::<128>()));
    assert(okb);
    assert_eq(ib * two_pow::<128>(), 1);
    assert_eq(field_div_or(wit(6), wit(3)), (2, true));
    assert_eq(field_div_or(wit(5), wit(0)), (0, false));
    assert_eq(field_div_or(wit(0 - 1), wit(0 - 1)), (1, true));
    // The inversion gadget leaves inv free at x = 0; inverse_or masks it.
    constrain_inverse(wit(0), wit(12345), wit(true));
}

#[test]
unconstrained fn sqrt_non_residue_is_verified() {
    // Euler's criterion: g^((p-1)/2) == -1 iff g is a non-residue.
    assert_eq(euler(SQRT_NON_RESIDUE), 0 - 1);
    assert_eq(euler(4), 1);
    assert_eq(euler(0), 0);
    // p = 1 mod 8, so -1 and 2 are squares
    assert_eq(euler(0 - 1), 1);
    assert_eq(euler(2), 1);
    // (p-1)/2 computed as -1/2 is the integer (p-1)/2
    assert_eq(((0 - 1) / 2) * 2, 0 - 1);
    // p - 1 = 2^28 * t with t odd
    let t = (0 - 1) / 268435456;
    let tb: [bool; 254] = t.to_le_bits();
    assert(tb[0]);
    assert_eq(t * 268435456, 0 - 1);
}

#[test]
unconstrained fn sqrt_hint_roots() {
    let xs: [Field; 6] = [1, 4, 0 - 1, 2, 0x1234567890abcdef1234567890abcdef, 0 - 7];
    for i in 0..6 {
        let x = xs[i];
        let (r, q, inv) = hint_sqrt(x);
        assert_eq(x * inv, 1);
        if q {
            assert_eq(r * r, x);
            assert_eq(euler(x), 1);
        } else {
            assert_eq(r * r, SQRT_NON_RESIDUE * x);
            assert_eq(euler(x), 0 - 1);
        }
    }
}

#[test]
fn sqrt_cases() {
    assert_eq(sqrt_or(wit(0)), (0, true));
    let (r4, ok4) = sqrt_or(wit(4));
    assert(ok4);
    assert_eq(r4 * r4, 4);
    let (rm1, okm1) = sqrt_or(wit(0 - 1));
    assert(okm1);
    assert_eq(rm1 * rm1, 0 - 1);
    let (r2, ok2) = sqrt_or(wit(2));
    assert(ok2);
    assert_eq(r2 * r2, 2);
    // non-squares: g and g*4
    assert_eq(sqrt_or(wit(SQRT_NON_RESIDUE)), (0, false));
    assert_eq(sqrt_or(wit(SQRT_NON_RESIDUE * 4)), (0, false));
    // canonical root is the even one
    let (c4, okc4) = sqrt_canonical_or(wit(4));
    assert(okc4);
    assert_eq(c4, 2);
    let (cm1, okcm1) = sqrt_canonical_or(wit(0 - 1));
    assert(okcm1);
    assert_eq(cm1 * cm1, 0 - 1);
    let bits: [bool; 254] = cm1.to_le_bits();
    assert(!bits[0]);
    assert_eq(sqrt_canonical_or(wit(0)), (0, true));
    assert_eq(sqrt_canonical_or(wit(SQRT_NON_RESIDUE)), (0, false));
}

/// Native facade check over a boundary set: values and flags against
/// the native operators where they succeed, and against std's
/// wrapping operators where they would fail.
fn check_native<T, let K: u32>(vals: [T; K], max: T)
where
    T: TotalArith + Saturating + WrappingAdd + WrappingSub + WrappingMul + Eq + Ord + std::ops::Add + std::ops::Sub + std::ops::Mul + std::ops::Div + std::ops::Rem + std::default::Default,
{
    let zero: T = std::default::Default::default();
    for i in 0..K {
        for j in 0..K {
            let (a, b) = (vals[i], vals[j]);
            let add_ok = a <= max - b;
            assert(wit(a).add_or(wit(b)) == (if add_ok { a + b } else { zero }, add_ok));
            assert(wit(a).saturating_add(wit(b)) == if add_ok { a + b } else { max });
            let sub_ok = a >= b;
            assert(wit(a).sub_or(wit(b)) == (if sub_ok { a - b } else { zero }, sub_ok));
            assert(wit(a).saturating_sub(wit(b)) == if sub_ok { a - b } else { zero });
            let mul_ok = (b == zero) | (a <= max / (if b == zero { max } else { b }));
            assert(wit(a).mul_or(wit(b)) == (if mul_ok { a * b } else { zero }, mul_ok));
            assert(wit(a).saturating_mul(wit(b)) == if mul_ok { a * b } else { max });
            let div_ok = b != zero;
            let d = if div_ok { b } else { max };
            assert(wit(a).div_or(wit(b)) == (if div_ok { a / d } else { zero }, div_ok));
            assert(wit(a).mod_or(wit(b)) == (if div_ok { a % d } else { zero }, div_ok));
        }
    }
}

#[test]
fn native_u8_u16() {
    check_native([0 as u8, 1, 2, 3, 15, 16, 127, 128, 254, 255], 255);
    check_native(
        [0 as u16, 1, 2, 255, 256, 0x7fff, 0x8000, 0xfffe, 0xffff],
        0xffff,
    );
}

#[test]
fn native_u32_u64() {
    check_native(
        [0 as u32, 1, 2, 0xffff, 0x10000, 0x7fffffff, 0x80000000, 0xfffffffe, 0xffffffff],
        0xffffffff,
    );
    check_native(
        [
            0 as u64,
            1,
            2,
            0xffffffff,
            0x100000000,
            0x7fffffffffffffff,
            0x8000000000000000,
            0xfffffffffffffffe,
            0xffffffffffffffff,
        ],
        0xffffffffffffffff,
    );
}

#[test]
fn native_u128() {
    check_native(
        [
            0 as u128,
            1,
            2,
            3,
            0xffffffffffffffff,
            0x10000000000000000,
            0x10000000000000001,
            0x7fffffffffffffffffffffffffffffff,
            0x80000000000000000000000000000000,
            0xfffffffffffffffffffffffffffffffe,
            0xffffffffffffffffffffffffffffffff,
        ],
        0xffffffffffffffffffffffffffffffff,
    );
    // limb carries: (2^64 + 1)^2 = 2^128 + 2^65 + 1 overflows; (2^64 - 1)*(2^64 + 1) fits
    let a: u128 = 0x10000000000000001;
    assert_eq(wit(a).mul_or(wit(a)), (0, false));
    assert_eq(a.wrapping_mul(a), 0x20000000000000001);
    let b: u128 = 0xffffffffffffffff;
    assert_eq(wit(b).mul_or(wit(a)), (0xffffffffffffffffffffffffffffffff, true));
    let c: u128 = 0x123456789abcdef0fedcba9876543210;
    let d: u128 = 0xfedcba987;
    assert_eq(wit(c).div_or(wit(d)), (c / d, true));
    assert_eq(wit(c).mod_or(wit(d)), (c % d, true));
}

#[test]
fn limb_boundary_inputs() {
    // 2^128 - 1, 2^128, 2^128 + 1 are out of range for every N <= 126
    let t = two_pow::<128>();
    let xs: [Field; 3] = [t - 1, t, t + 1];
    for i in 0..3 {
        let x = xs[i];
        assert_eq(add_or::<126>(wit(x), wit(1)), (0, false));
        assert_eq(wrapping_add_or::<126>(wit(x), wit(1)), (1, false));
        assert_eq(wrapping_sub_or::<64>(wit(1), wit(x)), (1, false));
        assert_eq(mul_or::<126>(wit(x), wit(x)), (0, false));
        assert_eq(div_rem_or::<64>(wit(x), wit(3)), (0, 0, false));
        assert_eq(div_rem_or::<64>(wit(7), wit(x)), (0, 0, false));
        assert_eq(wrapping_neg_or::<127>(wit(x)), (0, false));
        assert_eq(pow_or::<64, 7>(wit(x), wit(2)), (0, false));
    }
}

/// Positive controls for the wrong-hint tests below: the same
/// constraint halves accept the honest hints, so each should_fail
/// test fails because of the wrong hint and nothing else.
#[test]
fn honest_hints_accepted() {
    assert_eq(constrain_sub_split::<8>(wit(5), wit(3), wit(false)), 2);
    assert_eq(constrain_sub_split::<8>(wit(3), wit(5), wit(true)), 254);
    assert_eq(
        constrain_add_split::<128>(wit(0xffffffffffffffffffffffffffffffff), wit(1), wit(true)),
        0,
    );
    assert_eq(constrain_div_128(wit(17), wit(5), wit(3), wit(0), wit(2)), 3);
    constrain_low_bits::<4>(wit(5), wit([true, false, true, false]));
    constrain_inverse(wit(5), wit(1 / 5), wit(false));
    constrain_inverse(wit(0), wit(0), wit(true));
    constrain_sqrt(wit(4), wit(2), wit(true), wit(0));
    constrain_sqrt(wit(0), wit(0), wit(true), wit(7));
    constrain_sqrt(
        wit(SQRT_NON_RESIDUE),
        wit(SQRT_NON_RESIDUE),
        wit(false),
        wit(1 / SQRT_NON_RESIDUE),
    );
    // The wrapped quotient in div_128_quotient_wrapping_p_rejected does
    // satisfy the bare Field equation a == q*b1 + r; only the carry
    // range of constrain_div_128 rejects it.
    let q = 0x60c89ce5c263405370a08b6d0302b0bb;
    let b1 = 0x80000000000000000000000000000000;
    assert_eq(q * b1, 0x57cc17b786468f6ebc1e0a6c0fffffff);
    assert_eq(0x70a08b6d0302b0bb + 0x60c89ce5c2634053 * two_pow::<64>(), q);
    // u128::MAX / 3 with its limbs, and a product with a nonzero carry
    let m: Field = 0xffffffffffffffffffffffffffffffff;
    assert_eq(
        constrain_div_128(
            wit(m),
            wit(3),
            wit(0x5555555555555555),
            wit(0x5555555555555555),
            wit(0),
        ),
        m / 3,
    );
    let (a0, a1) = (0xffffffffffffffff, 0x8000000000000000);
    // a = 2^127 + 2^64 - 1: a*a = 2^254 + 2^192 - 2^65 + 1
    let hi = constrain_mul_128(
        wit(a0),
        wit(a1),
        wit(a0),
        wit(a1),
        wit(0xfffffffffffffffe0000000000000001),
    );
    assert_eq(hi, 0x4000000000000000ffffffffffffffff);
    assert_eq(constrain_mul_128(wit(3), wit(0), wit(5), wit(0), wit(15)), 0);
}

// Wrong-hint tests: the soundness constraints must reject a dishonest
// prover's hints.

#[test(should_fail)]
fn wrong_borrow_rejected() {
    let _ = constrain_sub_split::<8>(5, 3, true);
}

#[test(should_fail)]
fn missing_borrow_rejected() {
    let _ = constrain_sub_split::<8>(3, 5, false);
}

#[test(should_fail)]
fn wrong_carry_128_rejected() {
    let _ = constrain_add_split::<128>(0xffffffffffffffffffffffffffffffff, 1, false);
}

#[test(should_fail)]
fn div_128_remainder_too_big_rejected() {
    let _ = constrain_div_128(17, 5, 2, 0, 7);
}

#[test(should_fail)]
fn div_128_quotient_wrapping_p_rejected() {
    // q*b1 = p + a with q < 2^128 and r = 0 < b1: limbs, remainder and
    // the field reconstruction all pass; a - q0*b1 is not 2^64 times
    // a small integer, so the 70-bit carry range fails.
    let _ = constrain_div_128(
        0x57cc17b786468f6ebc1e0a6c0fffffff,
        0x80000000000000000000000000000000,
        0x70a08b6d0302b0bb,
        0x60c89ce5c2634053,
        0,
    );
}

#[test(should_fail)]
fn div_128_negative_remainder_rejected() {
    // a = 17, b1 = 5, r = -3 (the field element p - 3), q = 4: the
    // reconstruction 4*5 - 3 == 17 holds and r < b1 "holds" mod p, but
    // r is not below 2^128.
    let _ = constrain_div_128(17, 5, 4, 0, 0 - 3);
}

#[test(should_fail)]
fn div_128_field_quotient_rejected() {
    // q = 1/3 in the field, r = 0: q*b1 + r == a mod p, but q's limbs
    // cannot be below 2^64 (a q0 of 1/3 fails its range).
    let _ = constrain_div_128(1, 3, 1 / 3, 0, 0);
}

#[test(should_fail)]
fn mul_128_low_half_off_by_one_rejected() {
    // lo = 15 + 1 for 3*5: the carry (s - lo) / 2^128 is not an integer.
    let _ = constrain_mul_128(3, 0, 5, 0, 16);
}

#[test(should_fail)]
fn mul_128_low_half_past_2_128_rejected() {
    // lo + 2^128 with the carry one smaller (the honest carry here is
    // 2^64 - 1, so c - 1 passes the 70-bit range): the 128-bit range on
    // lo rejects it.
    let (a0, a1) = (0xffffffffffffffff, 0x8000000000000000);
    let _ = constrain_mul_128(
        a0,
        a1,
        a0,
        a1,
        0xfffffffffffffffe0000000000000001 + TWO_POW_128,
    );
}

#[test(should_fail)]
fn wrong_exponent_bits_rejected() {
    constrain_low_bits::<4>(5, [true, false, false, false]);
}

#[test(should_fail)]
fn inverse_flag_on_nonzero_rejected() {
    constrain_inverse(5, 0, true);
}

#[test(should_fail)]
fn inverse_missing_flag_on_zero_rejected() {
    constrain_inverse(0, 0, false);
}

#[test(should_fail)]
fn wrong_inverse_rejected() {
    constrain_inverse(5, 2, false);
}

#[test(should_fail)]
fn wrong_root_rejected() {
    constrain_sqrt(4, 3, true, 0);
}

#[test(should_fail)]
fn square_claimed_non_square_rejected() {
    // 4 is a square, so 4*g is not: no root r satisfies r*r == 4*g.
    constrain_sqrt(4, 2, false, 1 / 4);
}

#[test(should_fail)]
fn non_square_claimed_square_rejected() {
    constrain_sqrt(SQRT_NON_RESIDUE, 0, true, 0);
}

#[test(should_fail)]
fn zero_claimed_non_square_rejected() {
    // x = 0, q = 0: r = 0 satisfies r*r == g*x, but no inv gives
    // x*inv == 1.
    constrain_sqrt(0, 0, false, 1);
}

// 128-bit multiplication and division at their extremes, and wrong hints
// beyond the ones above.

global M128: Field = 0xffffffffffffffffffffffffffffffff;
global M64: Field = 0xffffffffffffffff;

#[test]
fn mul_128_honest_extremes() {
    // (2^128-1)^2 = 2^256 - 2^129 + 1: low half 1, high half 2^128 - 2
    let (lo, fits) = mul_128(wit(M128), wit(M128));
    assert_eq(lo, 1);
    assert(!fits);
    // Safety: the constraint half with the honest hint
    let lo_h = unsafe { hint_mul_lo_128(M64, M64, M64, M64) };
    assert_eq(lo_h, 1);
    let hi = constrain_mul_128(wit(M64), wit(M64), wit(M64), wit(M64), wit(lo_h));
    assert_eq(hi, TWO_POW_128 - 2);
    let (lo, fits) = mul_128(wit(M128), wit(1));
    assert_eq(lo, M128);
    assert(fits);
    let (lo, fits) = mul_128(wit(TWO_POW_64), wit(TWO_POW_64));
    assert_eq(lo, 0);
    assert(!fits);
    let (lo, fits) = mul_128(wit(TWO_POW_64 - 1), wit(TWO_POW_64 + 1));
    assert_eq(lo, M128);
    assert(fits);
    let (lo, fits) = mul_128(wit(0), wit(M128));
    assert_eq(lo, 0);
    assert(fits);
    // a0*b0 alone close to 2^128, no carry out of the low column
    let (lo, fits) = mul_128(wit(M64), wit(M64));
    assert_eq(lo, M64 * M64);
    assert(fits);
    // facades
    let m: u128 = 0xffffffffffffffffffffffffffffffff;
    assert_eq(wit(m).mul_or(wit(m)), (0, false));
    assert_eq(wit(m).mul_or(wit(1)), (m, true));
    assert_eq(wit(m).saturating_mul(wit(m)), m);
    assert_eq(wit(m).saturating_mul(wit(0)), 0);
    let h: u128 = 0x10000000000000000;
    assert_eq(wit(h).mul_or(wit(h)), (0, false));
    assert_eq(wit(h).mul_or(wit(h - 1)), (0xffffffffffffffff0000000000000000, true));
    assert_eq((h - 1).mul_or(wit(h + 1)), (m, true));
}

#[test(should_fail)]
fn mul_128_low_half_wrapped_below_zero_rejected() {
    // lo' = 1 - 2^128 wraps to p - 2^128 + 1: fails the 128-bit RANGE
    let _ = constrain_mul_128(M64, M64, M64, M64, 1 - TWO_POW_128);
}

#[test(should_fail)]
fn mul_128_low_half_absorbing_the_carry_rejected() {
    // lo' = lo + c*2^128 makes the carry 0, which passes its range, but
    // lo' fails its own RANGE
    // Safety: wrong-hint test
    let lo_h = unsafe { hint_mul_lo_128(M64, M64, M64, M64) };
    let c = (M64 * M64 + (M64 * M64 + M64 * M64) * TWO_POW_64 - lo_h) / TWO_POW_128;
    let _ = constrain_mul_128(M64, M64, M64, M64, lo_h + c * TWO_POW_128);
}

#[test(should_fail)]
fn mul_128_low_half_plus_2_pow_127_rejected() {
    // lo' = lo + 2^127: the carry becomes c - 1/2 mod p, far outside 70 bits
    // Safety: wrong-hint test
    let lo_h = unsafe { hint_mul_lo_128(3, 0, 5, 0) };
    let _ = constrain_mul_128(3, 0, 5, 0, lo_h + two_pow::<127>());
}

#[test]
fn div_128_honest_extremes() {
    assert_eq(div_128(wit(M128), wit(1)), (M128, 0)); // the carry is q1 = 2^64 - 1
    assert_eq(div_128(wit(M128), wit(M128)), (1, 0));
    assert_eq(div_128(wit(0), wit(M128)), (0, 0));
    assert_eq(div_128(wit(0), wit(1)), (0, 0));
    assert_eq(div_128(wit(M128), wit(TWO_POW_64 + 1)), (TWO_POW_64 - 1, 0));
    assert_eq(div_128(wit(M128), wit(two_pow::<127>())), (1, two_pow::<127>() - 1));
    assert_eq(div_128(wit(M128), wit(2)), (two_pow::<127>() - 1, 1));
    assert_eq(div_128(wit(M128), wit(3)), (M128 / 3, 0));
    assert_eq(div_128(wit(TWO_POW_64), wit(M64)), (1, 1));
    assert_eq(div_128(wit(TWO_POW_64 - 1), wit(TWO_POW_64)), (0, TWO_POW_64 - 1));
    assert_eq(div_128(wit(M128 - 1), wit(M128)), (0, M128 - 1));
    // q1 = 2^64 - 1 needs b1 = 1; with b1 = 2^63, q1 = 1 and the carry is
    // 2^63
    assert_eq(div_128(wit(M128), wit(two_pow::<63>())), (two_pow::<65>() - 1, two_pow::<63>() - 1));
    let m: u128 = 0xffffffffffffffffffffffffffffffff;
    assert_eq(wit(m).div_or(wit(0)), (0, false));
    assert_eq(wit(m).div_rem_or(wit(0)), (0, 0, false));
    assert_eq(wit(m).mod_or(wit(0)), (0, false));
    assert_eq((0 as u128).div_or(wit(0)), (0, false));
    assert_eq(wit(m).div_or(wit(m)), (1, true));
    assert_eq(wit(m).mod_or(wit(7)), (m % 7, true));
}

#[test(should_fail)]
fn div_128_quotient_down_remainder_up_rejected() {
    // (q - 1, r + b1): the RANGE on b1 - r - 1 fails
    // Safety: wrong-hint test
    let (q0, q1, r) = unsafe { hint_div_128(M128, 7) };
    assert_eq(r, 3);
    let _ = constrain_div_128(M128, 7, q0 - 1, q1, r + 7);
}

#[test(should_fail)]
fn div_128_high_quotient_limb_bumped_rejected() {
    // Safety: wrong-hint test
    let (q0, q1, r) = unsafe { hint_div_128(M128, 5) };
    let _ = constrain_div_128(M128, 5, q0, q1 + 1, r);
}

#[test(should_fail)]
fn div_128_low_quotient_limb_past_64_bits_rejected() {
    // move 1 from q1 into q0 as 2^64: q0 fails its 64-bit RANGE
    // Safety: wrong-hint test
    let (q0, q1, r) = unsafe { hint_div_128(M128, 5) };
    let _ = constrain_div_128(M128, 5, q0 + TWO_POW_64, q1 - 1, r);
}

#[test(should_fail)]
fn div_128_zero_divisor_unsatisfiable() {
    // the precondition b1 >= 1 broken: b1 - r - 1 is negative for every r,
    // so no witness exists (callers select the divisor to 1 first)
    let _ = constrain_div_128(17, 0, 0, 0, 17);
}

#[test]
fn sqrt_edge_cases() {
    // -1 is a square (p = 1 mod 4)
    let (r, ok) = sqrt_or(wit(0 - 1));
    assert(ok);
    assert_eq(r * r, 0 - 1);
    let (r, ok) = sqrt_or(wit(0));
    assert(ok);
    assert_eq(r, 0);
    let (r, ok) = sqrt_or(wit(SQRT_NON_RESIDUE));
    assert(!ok);
    assert_eq(r, 0);
    // Safety: the honest non-square hint is accepted by the constraint half
    let (r, q, inv) = unsafe { hint_sqrt(SQRT_NON_RESIDUE * 9) };
    assert(!q);
    constrain_sqrt(wit(SQRT_NON_RESIDUE * 9), wit(r), wit(q), wit(inv));
}

#[test(should_fail)]
fn non_square_with_wrong_inverse_rejected() {
    // q = false with x*inv != 1
    // Safety: wrong-hint test
    let (r, _, _) = unsafe { hint_sqrt(SQRT_NON_RESIDUE) };
    constrain_sqrt(SQRT_NON_RESIDUE, r, false, 0);
}

#[test(should_fail)]
fn zero_claimed_non_square_with_any_inverse_rejected() {
    constrain_sqrt(0, 0, false, 12345);
}

#[test(should_fail)]
fn square_claimed_non_square_with_no_root_rejected() {
    // x = 9 is a square; q = false needs r*r = 45 = 5*9, a non-residue
    // times a square, which has no root: r = 0 stands for every r
    constrain_sqrt(9, 0, false, 1 / 9);
}
