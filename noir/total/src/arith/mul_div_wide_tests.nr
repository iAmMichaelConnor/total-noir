use crate::core::two_pow;
use crate::test_support::wit;
use super::{mul_div_wide_or, mul_div_wide_to_or, TotalArith, TotalMulDiv};

global P_MINUS_1: Field = 0 - 1;

/// 0, 1, 2^N - 1, then the out-of-range 2^N, 2^N + 1 and p - 1.
fn bounds<let N: u32>() -> [Field; 6] {
    let m = two_pow::<N>();
    [0, 1, m - 1, m, m + 1, P_MINUS_1]
}

/// (q_lo, q_hi, r) of prod / d for prod in {0, 1, m - 1, (m - 1)^2}
/// and d in {1, m - 1}; sq = the limbs of (m - 1)^2 (from a reference
/// implementation, since (m - 1)^2 can exceed p).
fn boundary_ref(i: u32, j: u32, d: Field, m: Field, sq: (Field, Field)) -> (Field, Field, Field) {
    // vals index: 0 -> 0, 1 -> 1, 2 -> m - 1
    let zero = (i == 0) | (j == 0);
    if zero {
        (0, 0, 0)
    } else if d == 1 {
        if (i == 1) & (j == 1) {
            (1, 0, 0)
        } else if (i == 2) & (j == 2) {
            (sq.0, sq.1, 0)
        } else {
            (m - 1, 0, 0)
        }
    } else if (i == 1) & (j == 1) {
        (0, 0, 1)
    } else if (i == 2) & (j == 2) {
        (m - 1, 0, 0)
    } else {
        (1, 0, 0)
    }
}

fn check_boundaries<let N: u32>(sq: (Field, Field)) {
    let m = two_pow::<N>();
    let vals = bounds::<N>();
    for i in 0..6 {
        for j in 0..6 {
            for k in 0..6 {
                let (a, b, d) = (vals[i], vals[j], vals[k]);
                let ok = (i < 3) & (j < 3) & (k < 3) & (k != 0);
                let (q_lo, q_hi, r) = if ok {
                    boundary_ref(i, j, d, m, sq)
                } else {
                    (0, 0, 0)
                };
                assert_eq(mul_div_wide_or::<N>(wit(a), wit(b), wit(d)), (q_lo, q_hi, r, ok));
                if N == 128 {
                    // the only quotient at or above 2^128 is
                    // (m - 1)^2 / 1 = 2^256 - 2^129 + 1, which needs
                    // 256 bits: low 128 bits 1, low 253 bits
                    // 2^253 - 2^129 + 1
                    // the only quotient at or above 2^128 needs 256 bits, so
                    // both narrowed forms flag it and return (0, 0)
                    let ok_n = ok & (q_hi == 0);
                    let (q_n, r_n) = if ok_n { (q_lo, r) } else { (0, 0) };
                    assert_eq(mul_div_wide_to_or::<128>(wit(a), wit(b), wit(d)), (q_n, r_n, ok_n));
                    assert_eq(mul_div_wide_to_or::<253>(wit(a), wit(b), wit(d)), (q_n, r_n, ok_n));
                }
            }
        }
    }
}

#[test]
fn wide_boundaries_85() {
    check_boundaries::<85>((0xffffffffffc000000000000000000001, 0x3ffffffffff));
}

#[test]
fn wide_boundaries_96() {
    check_boundaries::<96>((0xfffffffe000000000000000000000001, 0xffffffffffffffff));
}

#[test]
fn wide_boundaries_124() {
    check_boundaries::<124>(
        (0xe0000000000000000000000000000001, 0xffffffffffffffffffffffffffffff),
    );
}

#[test]
fn wide_boundaries_125() {
    check_boundaries::<125>((0xc0000000000000000000000000000001, 0x3ffffffffffffffffffffffffffffff));
}

#[test]
fn wide_boundaries_127() {
    check_boundaries::<127>((0x1, 0x3fffffffffffffffffffffffffffffff));
}

#[test]
fn wide_boundaries_128() {
    check_boundaries::<128>((0x1, 0xfffffffffffffffffffffffffffffffe));
}

/// [a, b, d, r, then (q mod 2^M, q < 2^M) for M = 1, 64, 127, 128,
/// 135, 200, 253] from a reference implementation (Python integers,
/// seed 135); row 2 is the lending shape, (2^128 - 1)*1050000/30000,
/// whose quotient passes 2^128 but fits 135 bits.
global TO_ROWS: [[Field; 18]; 10] = [
    [
        0xffffffffffffffffffffffffffffffff,
        0xffffffffffffffffffffffffffffffff,
        0x1,
        0x0,
        0x1,
        0x0,
        0x1,
        0x0,
        0x1,
        0x0,
        0x1,
        0x0,
        0x7e00000000000000000000000000000001,
        0x0,
        0xfffffffffffffffffe00000000000000000000000000000001,
        0x0,
        0x1ffffffffffffffffffffffffffffffe00000000000000000000000000000001,
        0x0,
    ],
    [
        0xffffffffffffffffffffffffffffffff,
        0xffffffffffffffffffffffffffffffff,
        0xfffffffffffffffffffffffffffffffe,
        0x1,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x0,
        0x100000000000000000000000000000000,
        0x1,
        0x100000000000000000000000000000000,
        0x1,
        0x100000000000000000000000000000000,
        0x1,
    ],
    [
        0xffffffffffffffffffffffffffffffff,
        0x100590,
        0x7530,
        0x0,
        0x1,
        0x0,
        0xffffffffffffffdd,
        0x0,
        0x7fffffffffffffffffffffffffffffdd,
        0x0,
        0xffffffffffffffffffffffffffffffdd,
        0x0,
        0x22ffffffffffffffffffffffffffffffdd,
        0x1,
        0x22ffffffffffffffffffffffffffffffdd,
        0x1,
        0x22ffffffffffffffffffffffffffffffdd,
        0x1,
    ],
    [
        0xffffffffffffffffffffffffffffffff,
        0xffffffffffffffffffffffffffffffff,
        0x10000000000000000000000007,
        0x31000000e0000001,
        0x0,
        0x0,
        0xf8ffffffe0000000,
        0x0,
        0x7ffffffffffffffff8ffffffe0000000,
        0x0,
        0xfffffffffffffffff8ffffffe0000000,
        0x0,
        0x7ffffffffffffffffff8ffffffe0000000,
        0x0,
        0xffffffffffffffffffffffff8ffffffe0000000,
        0x1,
        0xffffffffffffffffffffffff8ffffffe0000000,
        0x1,
    ],
    [
        0xa2e28ad65f9ae5262708865bd4fde034,
        0x4efff863d6dfb716587fe0355c7446a3,
        0x9738b,
        0x4a2c5,
        0x1,
        0x0,
        0x92965cf0bef451e5,
        0x0,
        0x3f00734965fa779892965cf0bef451e5,
        0x0,
        0x3f00734965fa779892965cf0bef451e5,
        0x0,
        0x783f00734965fa779892965cf0bef451e5,
        0x0,
        0xfdfb68a217f0c31bf83f00734965fa779892965cf0bef451e5,
        0x0,
        0x5517d105efdfb68a217f0c31bf83f00734965fa779892965cf0bef451e5,
        0x1,
    ],
    [
        0xdeea8166eee26ef5d860cf35d6651227,
        0x810754646d9ef7641fd4499d63f5f52,
        0x48767,
        0x206e4,
        0x0,
        0x0,
        0xac214f04a4664a56,
        0x0,
        0x7ccb4434675e3432ac214f04a4664a56,
        0x0,
        0xfccb4434675e3432ac214f04a4664a56,
        0x0,
        0x47fccb4434675e3432ac214f04a4664a56,
        0x0,
        0xc395bdb7d9e6645e47fccb4434675e3432ac214f04a4664a56,
        0x0,
        0x18cede9e6c395bdb7d9e6645e47fccb4434675e3432ac214f04a4664a56,
        0x1,
    ],
    [
        0x57b3a799abe6f91b5af64f03c2f1c388,
        0xb7ce26dbd0ed8c003921836015131c7a,
        0xd107754bb1dce6d5cb049940b7ccb0f2,
        0x276c1a7641968079ded4718629ab2154,
        0x0,
        0x0,
        0xa2f7fc719769d92e,
        0x0,
        0x4d1e61674e38ffc2a2f7fc719769d92e,
        0x1,
        0x4d1e61674e38ffc2a2f7fc719769d92e,
        0x1,
        0x4d1e61674e38ffc2a2f7fc719769d92e,
        0x1,
        0x4d1e61674e38ffc2a2f7fc719769d92e,
        0x1,
        0x4d1e61674e38ffc2a2f7fc719769d92e,
        0x1,
    ],
    [
        0x8ce3466294819c04e459e0dcb5d7947,
        0xfdc1b84023f9b5f84da97726bc8f915d,
        0x267368d3869a8ce0e48e95427b8727cd,
        0x14eac3d53c6d63a81758b8b5c87fb75a,
        0x1,
        0x0,
        0x3ff409f1b0529535,
        0x0,
        0x3a1ca7d66fb5b7203ff409f1b0529535,
        0x1,
        0x3a1ca7d66fb5b7203ff409f1b0529535,
        0x1,
        0x3a1ca7d66fb5b7203ff409f1b0529535,
        0x1,
        0x3a1ca7d66fb5b7203ff409f1b0529535,
        0x1,
        0x3a1ca7d66fb5b7203ff409f1b0529535,
        0x1,
    ],
    [
        0x47c09ef05470e26cf361081acc1c81b5,
        0x14931560d82eb697497e0ee62ea4fc94,
        0x2cd92c8fd0757252a0b793b3bc74479d,
        0x1cfd8cd71593019a9e142c5ef43e9f8b,
        0x1,
        0x0,
        0xe54efa92b80374ad,
        0x0,
        0x20eac1b414da950ee54efa92b80374ad,
        0x1,
        0x20eac1b414da950ee54efa92b80374ad,
        0x1,
        0x20eac1b414da950ee54efa92b80374ad,
        0x1,
        0x20eac1b414da950ee54efa92b80374ad,
        0x1,
        0x20eac1b414da950ee54efa92b80374ad,
        0x1,
    ],
    [
        0x7e496a4c08688629fabc9efd6722a9c8,
        0x2ef7704ca8385faa1f4c9b05e48e1b6b,
        0xde6276c4033926d63bb0d655842d86d6,
        0x8cd0b57f871c2174fb7df2566e9db4b8,
        0x0,
        0x0,
        0xea4373eb631632d0,
        0x0,
        0x1aabd0ef5808eef4ea4373eb631632d0,
        0x1,
        0x1aabd0ef5808eef4ea4373eb631632d0,
        0x1,
        0x1aabd0ef5808eef4ea4373eb631632d0,
        0x1,
        0x1aabd0ef5808eef4ea4373eb631632d0,
        0x1,
        0x1aabd0ef5808eef4ea4373eb631632d0,
        0x1,
    ],
];

/// The reference row's (q mod 2^M, r, ok) as the entry returns it: both
/// values are 0 when the flag is.
fn expect(q: Field, r: Field, ok: Field) -> (Field, Field, bool) {
    if ok == 1 {
        (q, r, true)
    } else {
        (0, 0, false)
    }
}

#[test]
fn wide_to_every_width() {
    for i in 0..10 {
        let w = TO_ROWS[i];
        let (a, b, d, r) = (w[0], w[1], w[2], w[3]);
        assert_eq(mul_div_wide_to_or::<1>(wit(a), wit(b), wit(d)), expect(w[4], r, w[5]));
        assert_eq(mul_div_wide_to_or::<64>(wit(a), wit(b), wit(d)), expect(w[6], r, w[7]));
        assert_eq(mul_div_wide_to_or::<127>(wit(a), wit(b), wit(d)), expect(w[8], r, w[9]));
        assert_eq(mul_div_wide_to_or::<128>(wit(a), wit(b), wit(d)), expect(w[10], r, w[11]));
        assert_eq(mul_div_wide_to_or::<135>(wit(a), wit(b), wit(d)), expect(w[12], r, w[13]));
        assert_eq(mul_div_wide_to_or::<200>(wit(a), wit(b), wit(d)), expect(w[14], r, w[15]));
        assert_eq(mul_div_wide_to_or::<253>(wit(a), wit(b), wit(d)), expect(w[16], r, w[17]));
    }
}

#[test]
fn wide_to_flags_bad_inputs() {
    let m = two_pow::<128>();
    assert_eq(mul_div_wide_to_or::<135>(wit(m), wit(1), wit(1)), (0, 0, false));
    assert_eq(mul_div_wide_to_or::<135>(wit(1), wit(0 - 1), wit(1)), (0, 0, false));
    assert_eq(mul_div_wide_to_or::<135>(wit(5), wit(7), wit(0)), (0, 0, false));
    assert_eq(mul_div_wide_to_or::<135>(wit(5), wit(7), wit(m)), (0, 0, false));
    assert_eq(mul_div_wide_to_or::<135>(wit(5), wit(7), wit(2)), (17, 1, true));
}

/// [a, b, d, q mod 2^128, a*b mod d, ok] for the u128 facade, from a
/// reference implementation (Python integers, seed 96).
global U128_ROWS: [[Field; 6]; 12] = [
    [
        0xffffffffffffffffffffffffffffffff,
        0xffffffffffffffffffffffffffffffff,
        0xffffffffffffffffffffffffffffffff,
        0xffffffffffffffffffffffffffffffff,
        0x0,
        0x1,
    ],
    [
        0xffffffffffffffffffffffffffffffff,
        0xffffffffffffffffffffffffffffffff,
        0xfffffffffffffffffffffffffffffffe,
        0x0,
        0x1,
        0x0,
    ],
    [0xffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffff, 0x1, 0x1, 0x0, 0x0],
    [0xffffffffffffffffffffffffffffffff, 0x7, 0x0, 0x0, 0x0, 0x0],
    [
        0x80000000000000000000000000000000,
        0x3,
        0x80000000000000000000000000000001,
        0x2,
        0x7ffffffffffffffffffffffffffffffe,
        0x1,
    ],
    [
        0xd07a1a258a6a884a6ef9adc83cdac364,
        0x5fc40e3c0c1dee464af6968225e9abdb,
        0x8156cb79c37e81718cb467c230360b94,
        0x9a5c8ce4fb899a5358a4d6ab0d06e372,
        0x3d1ded0e3f8d6a1efa7484234bdf8ea4,
        0x1,
    ],
    [
        0x60ce7a6d670005fb5971db88e9e7d082,
        0x82768615d55201f71fe5338d214275c7,
        0x97d70fb1fd649a00ed079a97e570958b,
        0x532d6dd9f9857d46eed07358b2845deb,
        0x6eee6b92f11001ce3bfca0fa02a9b975,
        0x1,
    ],
    [
        0x130a67f874420e1d8c82b2d1fb498700,
        0xcf1bd0f0e5bf76ce6a4feabc7c8bfc71,
        0x7d0baff6b306712b7dfe33cc2caca355,
        0x1f894e17d127d71ad5ba6ec32d45dc3a,
        0x513afc6292fe0fe6f694eb926f589be,
        0x1,
    ],
    [
        0x6228f72db69ed0aecaf1e68e5,
        0x128c44c14f2ef6f8f40f10e,
        0xd845ac9ca88954cc,
        0x86b1bf8944fcf17878efa1dbcb5dba0,
        0x9390b7b8c30dce06,
        0x1,
    ],
    [
        0x7279fa0c022da51d736bd59b3,
        0x3697881fe7d5f7740fcea38,
        0x4da84441f0737ccb,
        0x5079aa6e5f3818696ccbeb3fa3639be5,
        0x2569677d923eb291,
        0x1,
    ],
    [
        0xca2a928d824b9d2eda57d9b0b,
        0x308a1d11ac77bb9487edbea,
        0xc55029273f9c26b0,
        0x31bbbff520889c6ae3965dcbf577fa2f,
        0xac97b2ac889926be,
        0x1,
    ],
    [
        0x768a22909ebe96c5203c8f7ca,
        0x2c2b2c339c3a337cd160932,
        0xe62e73c622d6646,
        0x6bf011db63790537ebd81231886a655f,
        0xb423f92fa23ed7a,
        0x0,
    ],
];

#[test]
fn u128_facade_reference_rows() {
    for i in 0..12 {
        let w = U128_ROWS[i];
        let (a, b, d) = (w[0] as u128, w[1] as u128, w[2] as u128);
        let (q, r, ok) = expect(w[3], w[4], w[5]);
        assert_eq(wit(a).mul_div_or(wit(b), wit(d)), (q as u128, r as u128, ok));
    }
}

#[test]
fn u128_facade_edges() {
    let max: u128 = 0xffffffffffffffffffffffffffffffff;
    assert_eq(wit(max).mul_div_or(wit(max), wit(max)), (max, 0, true));
    // (2^128 - 1)^2 / 1: past the type, flagged
    assert_eq(wit(max).mul_div_or(wit(max), wit(1)), (0, 0, false));
    // (2^128 - 1)^2 / (2^128 - 2) = 2^128 rem 1: one past the type
    assert_eq(wit(max).mul_div_or(wit(max), wit(max - 1)), (0, 0, false));
    assert_eq(wit(max).mul_div_or(wit(max), wit(0)), (0, 0, false));
    assert_eq((0 as u128).mul_div_or(wit(max), wit(1)), (0, 0, true));
    assert_eq((7 as u128).mul_div_or(wit(3), wit(2)), (10, 1, true));
}

#[test]
fn u128_facade_agrees_with_mul_then_div_when_the_product_fits() {
    let xs: [u128; 6] = [
        1,
        3,
        0xffffffffffffffff,
        0x10000000000000000,
        0x123456789abcdef,
        0xffffffffffffffffffffffff,
    ];
    for i in 0..6 {
        for j in 0..6 {
            for k in 0..6 {
                let (prod, fits) = TotalArith::mul_or(wit(xs[i]), wit(xs[j]));
                if fits {
                    let (q, _) = TotalArith::div_or(wit(prod), wit(xs[k]));
                    let (r, _) = TotalArith::mod_or(wit(prod), wit(xs[k]));
                    assert_eq(xs[i].mul_div_or(wit(xs[j]), wit(xs[k])), (q, r, true));
                }
            }
        }
    }
}

#[test]
fn u128_facade_agrees_with_u64_facade() {
    let xs: [u64; 4] = [1, 97, 0xfffffffffffffffe, 0xffffffffffffffff];
    for i in 0..4 {
        for j in 0..4 {
            for k in 0..4 {
                let (q, r, ok) = xs[i].mul_div_or(wit(xs[j]), wit(xs[k]));
                let (q2, r2, ok2) =
                    (xs[i] as u128).mul_div_or(wit(xs[j] as u128), wit(xs[k] as u128));
                assert(ok2);
                if ok {
                    assert_eq((q as u128, r as u128), (q2, r2));
                } else {
                    assert_eq((q, r), (0, 0));
                }
            }
        }
    }
}
