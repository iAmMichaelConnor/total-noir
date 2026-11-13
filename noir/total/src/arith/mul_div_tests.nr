use crate::core::two_pow;
use crate::test_support::wit;
use super::{mul_div_or, mul_div_to_or, TotalMulDiv};

global P_MINUS_1: Field = 0 - 1;

/// 0, 1, 2^N - 1, then the out-of-range 2^N, 2^N + 1 and p - 1.
fn bounds<let N: u32>() -> [Field; 6] {
    let m = two_pow::<N>();
    [0, 1, m - 1, m, m + 1, P_MINUS_1]
}

/// floor(prod / d) and prod mod d for prod in {0, 1, m - 1, (m - 1)^2}
/// and d in {1, m - 1}: the products and divisors the boundary values
/// produce, worked out by hand so the check covers N = 84, where u128
/// cannot hold the product.
fn boundary_ref(prod: Field, d: Field, m: Field) -> (Field, Field) {
    if d == 1 {
        (prod, 0)
    } else if prod == 0 {
        (0, 0)
    } else if prod == 1 {
        (0, 1)
    } else if prod == m - 1 {
        (1, 0)
    } else {
        assert_eq(prod, (m - 1) * (m - 1));
        (m - 1, 0)
    }
}

fn check_boundaries<let N: u32>() {
    let m = two_pow::<N>();
    let vals = bounds::<N>();
    for i in 0..6 {
        for j in 0..6 {
            for k in 0..6 {
                let (a, b, d) = (vals[i], vals[j], vals[k]);
                let ok = a.lt(m) & b.lt(m) & d.lt(m) & (d != 0);
                let (q, r) = if ok {
                    boundary_ref(a * b, d, m)
                } else {
                    (0, 0)
                };
                assert_eq(mul_div_or::<N>(wit(a), wit(b), wit(d)), (q, r, ok));
                // M = N: the only quotient at or above 2^N is
                // (m - 1)^2 (for N >= 2), whose low N bits are 1
                let ok_n = ok & q.lt(m);
                let (q_n, r_n) = if ok_n { (q, r) } else { (0, 0) };
                assert_eq(mul_div_to_or::<N, N>(wit(a), wit(b), wit(d)), (q_n, r_n, ok_n));
            }
        }
    }
}

#[test]
fn mul_div_boundaries_all_widths() {
    check_boundaries::<1>();
    check_boundaries::<8>();
    check_boundaries::<64>();
    check_boundaries::<84>();
}

#[test]
fn mul_div_zero_divisor() {
    let m = two_pow::<64>();
    let vals = [0, 1, 17, m - 1];
    for i in 0..4 {
        for j in 0..4 {
            assert_eq(mul_div_or::<64>(wit(vals[i]), wit(vals[j]), wit(0)), (0, 0, false));
            assert_eq(mul_div_to_or::<64, 64>(wit(vals[i]), wit(vals[j]), wit(0)), (0, 0, false));
        }
    }
    assert_eq(
        mul_div_or::<84>(wit(two_pow::<84>() - 1), wit(two_pow::<84>() - 1), wit(0)),
        (0, 0, false),
    );
    assert_eq(
        (0xffffffffffffffff as u64).mul_div_or(wit(0xffffffffffffffff), wit(0)),
        (0, 0, false),
    );
    assert_eq((200 as u8).mul_div_or(wit(200), wit(0)), (0, 0, false));
    assert_eq((7 as u32).mul_div_or(wit(9), wit(0)), (0, 0, false));
}

#[test]
fn mul_div_quotient_width() {
    let m = two_pow::<64>();
    // the largest full-width quotient, (2^64 - 1)^2
    assert_eq(mul_div_or::<64>(wit(m - 1), wit(m - 1), wit(1)), ((m - 1) * (m - 1), 0, true));
    // at M = 64: exactly 2^64 - 1 fits, 2^64 does not
    assert_eq(mul_div_to_or::<64, 64>(wit(m - 1), wit(1), wit(1)), (m - 1, 0, true));
    assert_eq(
        mul_div_to_or::<64, 64>(wit(two_pow::<32>()), wit(two_pow::<32>()), wit(1)),
        (0, 0, false),
    );
    // at M = 65: 2^64 fits
    assert_eq(
        mul_div_to_or::<64, 65>(wit(two_pow::<32>()), wit(two_pow::<32>()), wit(1)),
        (m, 0, true),
    );
    // u64 facade: the same two cases
    let big: u64 = 0xffffffffffffffff;
    assert_eq(wit(big).mul_div_or(wit(1), wit(1)), (big, 0, true));
    let t32: u64 = 0x100000000;
    assert_eq(wit(t32).mul_div_or(wit(t32), wit(1)), (0, 0, false));
    // r_out * amount / (r_in + amount) with r_in = 0 equals r_out
    assert_eq(wit(big).mul_div_or(wit(5), wit(5)), (big, 0, true));
    // (2^64 - 1)^2 / (2^64 - 1) = 2^64 - 1
    assert_eq(wit(big).mul_div_or(wit(big), wit(big)), (big, 0, true));
    // a*b near 2^128 with a divisor that leaves a remainder:
    // (2^64 - 1)^2 = 2^64 * (2^64 - 2) + 1, so the quotient is 2^64,
    // one past the u64 range (low bits 0)
    assert_eq(wit(big).mul_div_or(wit(big), wit(big - 1)), (0, 0, false));
    assert_eq(mul_div_to_or::<64, 64>(wit(m - 1), wit(m - 1), wit(m - 2)), (0, 0, false));
    assert_eq(mul_div_or::<64>(wit(m - 1), wit(m - 1), wit(m - 2)), (m, 1, true));
}

/// xorshift64. Shifts on u64 discard the bits shifted out.
unconstrained fn next(s: u64) -> u64 {
    let mut x = s;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    x
}

/// N-bit pseudo-random operands from three draws; the divisor gets a
/// random bit length so small and large divisors both occur.
unconstrained fn draw<let N: u32>(s: u64) -> (u64, u64, u64, u64) {
    let s1 = next(s);
    let s2 = next(s1);
    let s3 = next(s2);
    let s4 = next(s3);
    let shift = 64 - (N as u64);
    let a = s1 >> shift;
    let b = s2 >> shift;
    let d = (s3 >> shift) >> (s4 % (N as u64));
    (a, b, d, s4)
}

fn check_random<let N: u32>(seed: u64, count: u32) {
    let mut s = seed;
    for _ in 0..count {
        // Safety: test input generation only.
        let (a, b, d, s_next) = unsafe { draw::<N>(s) };
        s = s_next;
        let (af, bf, df) = (a as Field, b as Field, d as Field);
        if d == 0 {
            assert_eq(mul_div_or::<N>(wit(af), wit(bf), wit(df)), (0, 0, false));
        } else {
            let p = (a as u128) * (b as u128);
            let q = p / (d as u128);
            let r = p % (d as u128);
            assert_eq(mul_div_or::<N>(wit(af), wit(bf), wit(df)), (q as Field, r as Field, true));
            let fits = q < ((1 as u128) << (N as u128));
            let (qn, rn, okn) = mul_div_to_or::<N, N>(wit(af), wit(bf), wit(df));
            assert_eq(okn, fits);
            if fits {
                assert_eq((qn, rn), (q as Field, r as Field));
            } else {
                assert_eq((qn, rn), (0, 0));
            }
        }
    }
}

#[test]
fn mul_div_random_against_u128() {
    check_random::<8>(0x9e3779b97f4a7c15, 48);
    check_random::<32>(0xd1b54a32d192ed03, 48);
    check_random::<64>(0x2545f4914f6cdd1d, 64);
}

#[test]
fn mul_div_facades_random_against_u128() {
    let mut s: u64 = 0x5851f42d4c957f2d;
    for _ in 0..64 {
        // Safety: test input generation only.
        let (a, b, d, s_next) = unsafe { draw::<64>(s) };
        s = s_next;
        let (q, r, ok) = wit(a).mul_div_or(wit(b), wit(d));
        if d == 0 {
            assert_eq((q, r, ok), (0, 0, false));
        } else {
            let p = (a as u128) * (b as u128);
            let qw = p / (d as u128);
            assert_eq(ok, qw < 0x10000000000000000);
            if ok {
                assert_eq((q as u128, r as u128), (qw, p % (d as u128)));
            } else {
                assert_eq((q, r), (0, 0));
            }
        }
        // the same draws narrowed to u32, u16 and u8 operands
        let (a32, b32, d32) = (a as u32, b as u32, (d as u32) | 1);
        let p32 = (a32 as u64) * (b32 as u64);
        let (q, r, ok) = wit(a32).mul_div_or(wit(b32), wit(d32));
        assert_eq(ok, p32 / (d32 as u64) < 0x100000000);
        if ok {
            assert_eq((q as u64, r as u64), (p32 / (d32 as u64), p32 % (d32 as u64)));
        } else {
            assert_eq((q, r), (0, 0));
        }
        let (a16, b16, d16) = (a as u16, b as u16, (d >> 8) as u16);
        if d16 != 0 {
            let p16 = (a16 as u64) * (b16 as u64);
            let (q, r, ok) = wit(a16).mul_div_or(wit(b16), wit(d16));
            assert_eq(ok, p16 / (d16 as u64) < 0x10000);
            if ok {
                assert_eq((q as u64, r as u64), (p16 / (d16 as u64), p16 % (d16 as u64)));
            } else {
                assert_eq((q, r), (0, 0));
            }
        }
        let (a8, b8, d8) = (a as u8, b as u8, (d >> 3) as u8);
        if d8 != 0 {
            let p8 = (a8 as u32) * (b8 as u32);
            let (q, r, ok) = wit(a8).mul_div_or(wit(b8), wit(d8));
            assert_eq(ok, p8 / (d8 as u32) < 0x100);
            if ok {
                assert_eq((q as u32, r as u32), (p8 / (d8 as u32), p8 % (d8 as u32)));
            } else {
                assert_eq((q, r), (0, 0));
            }
        }
    }
}
