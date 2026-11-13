// The 128-bit division and exponent-bit hints on hostile and edge
// arguments: each returns without trapping and its outputs have the
// property the constraint half checks; the constraint halves accept
// them and reject them once perturbed.
use crate::core::{two_pow, TWO_POW_128, TWO_POW_64};
use crate::test_support::wit;
use super::{
    constrain_div_128, constrain_low_bits, hint_div_128, hint_inverse, hint_low_bits,
    hint_mul_lo_128, hint_sqrt, SQRT_NON_RESIDUE,
};

global P_MINUS_1: Field = 0 - 1;

#[test]
unconstrained fn low_bits_hint_on_every_edge() {
    let xs: [Field; 6] = [0, 1, 0xa5, two_pow::<126>() - 1, two_pow::<128>(), P_MINUS_1];
    for i in 0..6 {
        let bits = hint_low_bits::<126>(xs[i]);
        let mut sum: Field = 0;
        let mut pw: Field = 1;
        for k in 0..126 {
            sum += (bits[k] as Field) * pw;
            pw *= 2;
        }
        // sum is the low 128 bits of xs[i] reduced mod 2^126
        let top = ((xs[i] as u128) as Field - sum) / two_pow::<126>();
        assert(top.lt(4));
        let bits8 = hint_low_bits::<8>(xs[i]);
        for k in 0..8 {
            assert_eq(bits8[k], bits[k]);
        }
    }
}

#[test(should_fail)]
fn perturbed_low_bits_rejected() {
    // Safety: test of the constraint half against a perturbed hint.
    let mut bits = unsafe { hint_low_bits::<4>(5) };
    bits[1] = !bits[1];
    constrain_low_bits::<4>(5, bits);
}

#[test]
fn honest_low_bits_accepted() {
    // Safety: positive control for the test above.
    let bits = unsafe { hint_low_bits::<4>(5) };
    constrain_low_bits::<4>(wit(5), wit(bits));
}

#[test]
unconstrained fn div_128_hint_on_every_edge() {
    // including a zero divisor (the hint returns zeros) and arguments
    // past 2^128 (it divides their low 128 bits)
    let xs: [Field; 10] = [
        0,
        1,
        5,
        0xffffffffffffffff,
        0x10000000000000000,
        0xffffffffffffffffffffffffffffffff,
        0x100000000000000000000000000000000,
        0x100000000000000000000000000000007,
        0x123456789abcdef0fedcba9876543210,
        P_MINUS_1,
    ];
    for i in 0..10 {
        for j in 0..10 {
            let (ai, bi) = ((xs[i] as u128) as Field, (xs[j] as u128) as Field);
            let (q0, q1, r) = hint_div_128(xs[i], xs[j]);
            assert(q0.lt(two_pow::<64>()));
            assert(q1.lt(two_pow::<64>()));
            if bi == 0 {
                assert_eq((q0, q1, r), (0, 0, 0));
            } else {
                assert_eq((q0 + q1 * two_pow::<64>()) * bi + r, ai);
                assert(r.lt(bi));
            }
        }
    }
}

#[test(should_fail)]
fn perturbed_div_128_quotient_rejected() {
    // Safety: test of the constraint half against a perturbed hint.
    let (q0, q1, r) = unsafe { hint_div_128(17, 5) };
    let _ = constrain_div_128(17, 5, q0 + 1, q1, r);
}

#[test]
fn honest_div_128_hints_accepted() {
    // Safety: positive control for the test above.
    let (q0, q1, r) = unsafe { hint_div_128(17, 5) };
    assert_eq(constrain_div_128(wit(17), wit(5), wit(q0), wit(q1), wit(r)), 3);
    let m: Field = 0xffffffffffffffffffffffffffffffff;
    // Safety: as above.
    let (q0, q1, r) = unsafe { hint_div_128(m, 3) };
    assert_eq(constrain_div_128(wit(m), wit(3), wit(q0), wit(q1), wit(r)), m / 3);
}

#[test]
unconstrained fn inverse_sqrt_and_128_bit_hints_on_every_edge() {
    let m64: Field = 0xffffffffffffffff;
    let m128: Field = 0xffffffffffffffffffffffffffffffff;
    let xs: [Field; 8] = [0, 1, 2, m64, TWO_POW_64, m128, TWO_POW_128, P_MINUS_1];
    for i in 0..8 {
        let (inv, z) = hint_inverse(xs[i]);
        if xs[i] == 0 {
            assert(z);
            assert_eq(inv, 0);
        } else {
            assert(!z);
            assert_eq(inv * xs[i], 1);
        }
        let (r, q, iv) = hint_sqrt(xs[i]);
        if xs[i] == 0 {
            assert(q);
            assert_eq(r, 0);
        } else {
            assert_eq(iv * xs[i], 1);
            if q {
                assert_eq(r * r, xs[i]);
            } else {
                assert_eq(r * r, SQRT_NON_RESIDUE * xs[i]);
            }
        }
        for j in 0..8 {
            // the limbs are the low 64 bits here; the hint must equal the
            // integer product's low 128 bits
            let a0 = (xs[i] as u64) as Field;
            let b0 = (xs[j] as u64) as Field;
            let lo = hint_mul_lo_128(a0, m64, b0, m64);
            let s = a0 * b0 + (a0 * m64 + m64 * b0) * TWO_POW_64;
            assert_eq(lo, (s as u128) as Field);
            let _ = hint_div_128(xs[i], xs[j]);
        }
    }
}
