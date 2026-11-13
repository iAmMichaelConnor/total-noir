// The split, division and limb hints on hostile and edge arguments:
// each returns without trapping, and its outputs have the property
// the constraint half checks, so the honest witness exists on the
// whole precondition domain. (hint_mul_div and hint_mul_div_wide have
// their sweeps in the multiply-divide test modules.)
use super::{hint_carry, hint_div, hint_split_128_at, hint_wide_limbs, two_pow, TWO_POW_128};

global P_MINUS_1: Field = 0 - 1;

/// Zero, one, every power-of-two edge the gadgets use, 2^128 - 1 (the
/// cast's edge), values past it, and the field's -1.
global XS: [Field; 16] = [
    0,
    1,
    2,
    0xff,
    0x100,
    0xffffffffffffffff,
    0x10000000000000000,
    0x10000000000000001,
    0x7fffffffffffffffffffffffffffffff,
    0x80000000000000000000000000000000,
    0xffffffffffffffffffffffffffffffff,
    TWO_POW_128,
    0x100000000000000000000000000000001,
    0x123456789abcdef0fedcba9876543210,
    0 - TWO_POW_128,
    P_MINUS_1,
];

/// The low 128 bits of x as a Field.
unconstrained fn low_128(x: Field) -> Field {
    (x as u128) as Field
}

unconstrained fn split_sweep<let N: u32>() {
    for i in 0..16 {
        let (lo, rest) = hint_split_128_at::<N>(XS[i]);
        assert(lo.lt(two_pow::<N>()));
        assert(rest.lt(two_pow::<128 - N>()));
        assert_eq(lo + rest * two_pow::<N>(), low_128(XS[i]));
    }
}

#[test]
unconstrained fn split_hint_on_every_edge() {
    split_sweep::<1>();
    split_sweep::<8>();
    split_sweep::<63>();
    split_sweep::<64>();
    split_sweep::<65>();
    split_sweep::<126>();
    split_sweep::<127>();
}

#[test]
unconstrained fn div_hint_on_every_edge() {
    // Divisors whose truncation is nonzero (the precondition b1 >= 1
    // below 2^N); hint_div traps on the others, which callers rule out
    // by selecting the divisor to 1 first.
    for i in 0..16 {
        for j in 0..16 {
            let (ai, bi) = (low_128(XS[i]), low_128(XS[j]));
            if bi != 0 {
                let (q, r) = hint_div::<126>(XS[i], XS[j]);
                assert_eq(q * bi + r, ai);
                assert(r.lt(bi));
                assert(q.lt(TWO_POW_128));
            }
        }
    }
}

#[test]
unconstrained fn wide_limb_hint_on_every_edge() {
    for i in 0..16 {
        for j in 0..16 {
            let src = [XS[i], XS[j], XS[(i + j) % 16], XS[j], XS[i]];
            let l = hint_wide_limbs(src[0], src[1], src[2], src[3], src[4]);
            for k in 0..5 {
                assert(l[2 * k].lt(two_pow::<64>()));
                assert(l[2 * k + 1].lt(two_pow::<64>()));
                assert_eq(l[2 * k] + l[2 * k + 1] * two_pow::<64>(), low_128(src[k]));
            }
        }
    }
}

#[test]
unconstrained fn carry_hint_on_128_bit_edges() {
    let m128: Field = 0xffffffffffffffffffffffffffffffff;
    assert(hint_carry::<128>(m128, m128));
    assert(!hint_carry::<128>(m128, 0));
    assert(hint_carry::<128>(m128, 1));
    // outside the precondition it still returns
    let _ = hint_carry::<128>(P_MINUS_1, P_MINUS_1);
    let _ = hint_carry::<1>(P_MINUS_1, TWO_POW_128);
}
