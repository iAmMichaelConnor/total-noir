// TotalUnsigned (widening_mul, pow_or, isqrt, abs_diff, div_ceil_or),
// TotalMulDiv::mul_div_ceil_or and the Field-domain entries at 127 and
// 128 bits: values against u128 references, on literals and on
// witnesses, plus the hints on hostile arguments and wrong-hint tests
// for the two new constraint halves.
use crate::core::{two_pow, TWO_POW_128, TWO_POW_64};
use crate::test_support::witnesses;
use super::{
    add_or, constrain_abs_diff, constrain_isqrt, div_rem_or, hint_isqrt, hint_lt_128, mul_or,
    saturating_mul_or, sub_or, TotalArith, TotalMulDiv, TotalUnsigned, wrapping_mul_or,
};

/// The value as a u128, for references in a wider type.
trait Wide {
    fn w(self) -> u128;
}
impl Wide for u8 {
    fn w(self) -> u128 {
        self as u128
    }
}
impl Wide for u16 {
    fn w(self) -> u128 {
        self as u128
    }
}
impl Wide for u32 {
    fn w(self) -> u128 {
        self as u128
    }
}
impl Wide for u64 {
    fn w(self) -> u128 {
        self as u128
    }
}

/// b^e and whether it is below 2^n, for b < 2^n and n <= 64. Every
/// partial product is below 2^128 (r < 2^n before each step).
unconstrained fn pow_ref(b: u128, e: u32, n: u32) -> (u128, bool) {
    let m = (1 as u128) << (n as u128);
    if b <= 1 {
        (if e == 0 { 1 } else { b }, true)
    } else if e >= 128 {
        (0, false)
    } else {
        let mut r: u128 = 1;
        let mut ok = true;
        for i in 0..128 {
            if ok & (i < e) {
                r = r * b;
                if r >= m {
                    ok = false;
                }
            }
        }
        (if ok { r } else { 0 }, ok)
    }
}

global EXPS: [u32; 12] = [0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 64, 0xffffffff];

fn check_unsigned<T, let N: u32, let K: u32>(vals: [T; K])
where
    T: TotalUnsigned + TotalMulDiv + Wide + Eq,
{
    let m: u128 = (1 as u128) << (N as u128);
    for i in 0..K {
        let a = vals[i];
        let aw = a.w();
        let r = a.isqrt().w();
        assert(r * r <= aw);
        assert(aw < (r + 1) * (r + 1));
        for k in 0..12 {
            // Safety: reference computation
            let (p, ok) = unsafe { pow_ref(aw, EXPS[k], N) };
            let (gp, gok) = a.pow_or(EXPS[k]);
            assert_eq((gp.w(), gok), (p, ok));
        }
        for j in 0..K {
            let b = vals[j];
            let bw = b.w();
            let (lo, hi) = a.widening_mul(b);
            assert_eq(lo.w() + hi.w() * m, aw * bw);
            assert_eq(a.abs_diff(b).w(), if aw >= bw { aw - bw } else { bw - aw });
            let (c, cok) = a.div_ceil_or(b);
            let bd = if bw == 0 { 1 } else { bw };
            assert_eq((c.w(), cok), (if bw == 0 { 0 } else { (aw + bd - 1) / bd }, bw != 0));
            for k in 0..K {
                let d = vals[k];
                let dw = d.w();
                let dd = if dw == 0 { 1 } else { dw };
                let pr = aw * bw;
                let c = pr / dd + (if pr % dd == 0 { 0 } else { 1 });
                let ok = (dw != 0) & (c < m);
                let (g, gok) = a.mul_div_ceil_or(b, d);
                assert_eq((g.w(), gok), (if ok { c } else { 0 }, ok));
            }
        }
    }
}

global V8: [u8; 7] = [0, 1, 2, 3, 127, 254, 255];
global V16: [u16; 6] = [0, 1, 3, 0x7fff, 0xfffe, 0xffff];
global V32: [u32; 6] = [0, 1, 3, 0x7fffffff, 0xfffffffe, 0xffffffff];
global V64: [u64; 6] = [0, 1, 3, 0x7fffffffffffffff, 0xfffffffffffffffe, 0xffffffffffffffff];

#[test]
fn unsigned_extras_u8_u16() {
    check_unsigned::<u8, 8, 7>(V8);
    check_unsigned::<u16, 16, 6>(V16);
}

#[test]
fn unsigned_extras_u32_u64() {
    check_unsigned::<u32, 32, 6>(V32);
    check_unsigned::<u64, 64, 6>(V64);
}

#[test]
fn unsigned_extras_on_witnesses() {
    let v8: [u8; 4] = [0, 3, 200, 255];
    check_unsigned::<u8, 8, 4>(witnesses(v8));
    let v64: [u64; 4] = [1, 0xffffffff, 0x100000000, 0xffffffffffffffff];
    check_unsigned::<u64, 64, 4>(witnesses(v64));
}

#[test]
fn isqrt_every_u8() {
    for x in 0..256 {
        let v = x as u8;
        let r = v.isqrt() as u32;
        assert(r * r <= x);
        assert(x < (r + 1) * (r + 1));
    }
}

#[test]
fn pow_exponent_split_boundaries() {
    // u8 runs the loop on 4 exponent bits: 15 is the last exponent in the
    // loop, 16 the first past it
    assert_eq((2 as u8).pow_or(7), (128, true));
    assert_eq((2 as u8).pow_or(15), (0, false));
    assert_eq((1 as u8).pow_or(15), (1, true));
    assert_eq((1 as u8).pow_or(16), (1, true));
    assert_eq((0 as u8).pow_or(16), (0, true));
    assert_eq((2 as u8).pow_or(16), (0, false));
    assert_eq((0 as u8).pow_or(0), (1, true));
    assert_eq((255 as u8).pow_or(0), (1, true));
    assert_eq((3 as u8).pow_or(5), (243, true));
    // u16: 5 bits, so 31 and 32
    assert_eq((1 as u16).pow_or(31), (1, true));
    assert_eq((2 as u16).pow_or(31), (0, false));
    assert_eq((0 as u16).pow_or(32), (0, true));
    // u64 and u128
    assert_eq((255 as u64).pow_or(8), (17878103347812890625, true));
    assert_eq((256 as u64).pow_or(8), (0, false));
    assert_eq((2 as u128).pow_or(127), (0x80000000000000000000000000000000, true));
    assert_eq((2 as u128).pow_or(128), (0, false));
    assert_eq((3 as u128).pow_or(80), (0x6f32f1ef8b18a2bc3cea59789c79d441, true));
    assert_eq((3 as u128).pow_or(81), (0, false));
    assert_eq((1 as u128).pow_or(0xffffffff), (1, true));
    assert_eq((0xffffffffffffffff as u128).pow_or(2), (0xfffffffffffffffe0000000000000001, true));
    assert_eq((0x10000000000000000 as u128).pow_or(2), (0, false));
}

global M128: u128 = 0xffffffffffffffffffffffffffffffff;

#[test]
fn u128_extras() {
    let ops: [u128; 4] = witnesses([M128, 0, 1, 0x10000000000000000]);
    let (max, zero, one, t64) = (ops[0], ops[1], ops[2], ops[3]);
    // widening_mul: (2^128 - 1)^2 = 2^256 - 2^129 + 1
    assert_eq(max.widening_mul(max), (1, max - 1));
    assert_eq(max.widening_mul(one), (max, 0));
    assert_eq(max.widening_mul(zero), (0, 0));
    assert_eq(t64.widening_mul(t64), (0, 1));
    assert_eq((t64 - 1).widening_mul(t64 + 1), (max, 0));
    // isqrt
    assert_eq(max.isqrt(), 0xffffffffffffffff);
    assert_eq((max - 1).isqrt(), 0xffffffffffffffff);
    assert_eq(((t64 - 1) * (t64 - 1)).isqrt(), 0xffffffffffffffff);
    assert_eq(((t64 - 1) * (t64 - 1) - 1).isqrt(), 0xfffffffffffffffe);
    assert_eq(zero.isqrt(), 0);
    assert_eq(one.isqrt(), 1);
    // abs_diff
    assert_eq(max.abs_diff(zero), max);
    assert_eq(zero.abs_diff(max), max);
    assert_eq(max.abs_diff(max), 0);
    assert_eq(t64.abs_diff(one), t64 - 1);
    // div_ceil_or
    assert_eq(max.div_ceil_or(one), (max, true));
    assert_eq(max.div_ceil_or(2), (0x80000000000000000000000000000000, true));
    assert_eq(max.div_ceil_or(max), (1, true));
    assert_eq(zero.div_ceil_or(max), (0, true));
    assert_eq(max.div_ceil_or(zero), (0, false));
    // mul_div_ceil_or
    assert_eq(max.mul_div_ceil_or(max, max), (max, true));
    assert_eq(max.mul_div_ceil_or(max, zero), (0, false));
    assert_eq(max.mul_div_ceil_or(max, max - 1), (0, false));
    assert_eq((7 as u128).mul_div_ceil_or(3, 2), (11, true));
    assert_eq((8 as u128).mul_div_ceil_or(3, 2), (12, true));
    // (MAX - 1)(d + 1) = MAX*d + (MAX - d - 1) with d = 2^127 + 5: the
    // floor is MAX with a remainder, so the ceiling does not fit
    let d: u128 = 0x80000000000000000000000000000005;
    assert_eq((max - 1).mul_div_or(d + 1, d), (max, 0x7ffffffffffffffffffffffffffffff9, true));
    assert_eq((max - 1).mul_div_ceil_or(d + 1, d), (0, false));
}

#[test]
fn mul_div_ceil_u8_carry() {
    // 254 * 201 = 255 * 200 + 54: floor 255, ceiling 256
    assert_eq((254 as u8).mul_div_or(201, 200), (255, 54, true));
    assert_eq((254 as u8).mul_div_ceil_or(201, 200), (0, false));
    assert_eq((255 as u8).mul_div_ceil_or(255, 255), (255, true));
    assert_eq((200 as u8).mul_div_ceil_or(200, 255), (157, true));
    assert_eq((255 as u8).mul_div_ceil_or(255, 1), (0, false));
    assert_eq((3 as u8).mul_div_ceil_or(3, 0), (0, false));
}

#[test]
fn field_domain_at_127_and_128_bits() {
    let ops: [Field; 5] = witnesses([
        TWO_POW_128 - 1,
        TWO_POW_128,
        TWO_POW_64,
        two_pow::<127>(),
        0 - 1,
    ]);
    let (max, t128, t64, t127, pm1) = (ops[0], ops[1], ops[2], ops[3], ops[4]);
    assert_eq(add_or::<128>(max, 0), (max, true));
    assert_eq(add_or::<128>(max, 1), (0, false));
    assert_eq(add_or::<128>(t128, 0), (0, false));
    assert_eq(add_or::<127>(t127 - 1, 1), (0, false));
    assert_eq(add_or::<127>(t127 - 2, 1), (t127 - 1, true));
    assert_eq(sub_or::<128>(max, max), (0, true));
    assert_eq(sub_or::<128>(0, 1), (0, false));
    assert_eq(mul_or::<128>(t64, t64 - 1), (max - (t64 - 1), true));
    assert_eq(mul_or::<128>(t64, t64), (0, false));
    assert_eq(wrapping_mul_or::<128>(max, max), (1, true));
    assert_eq(saturating_mul_or::<128>(max, 2), (max, true));
    assert_eq(mul_or::<127>(t64, t64 / 2 - 1), (t127 - t64, true));
    assert_eq(mul_or::<127>(t64, t64 / 2), (0, false));
    // (2^127 - 1)^2 mod 2^127 = 1
    assert_eq(wrapping_mul_or::<127>(t127 - 1, t127 - 1), (1, true));
    assert_eq(wrapping_mul_or::<127>(t127, 1), (0, false));
    assert_eq(div_rem_or::<128>(max, 2), (t127 - 1, 1, true));
    assert_eq(div_rem_or::<128>(max, max), (1, 0, true));
    assert_eq(div_rem_or::<128>(max, 0), (0, 0, false));
    assert_eq(div_rem_or::<128>(pm1, 3), (0, 0, false));
    assert_eq(div_rem_or::<127>(t127 - 1, t64), (t64 / 2 - 1, t64 - 1, true));
    assert_eq(div_rem_or::<127>(t127, 1), (0, 0, false));
    // the u128 facade agrees with the Field domain at 128 bits
    let (a, b): (u128, u128) = (M128 / 3, 3);
    assert_eq(a.mul_or(b), (M128, true));
    assert_eq(mul_or::<128>(a as Field, b as Field), (max, true));
}

// Hints on hostile arguments: each returns without trapping.

#[test]
unconstrained fn isqrt_and_lt_hints_on_every_edge() {
    let xs: [Field; 8] = [0, 1, 2, 3, TWO_POW_64, TWO_POW_128 - 1, TWO_POW_128, 0 - 1];
    for i in 0..8 {
        // the low 128 bits are rooted
        let xl = (xs[i] as u128) as Field;
        let r = hint_isqrt::<64>(xs[i]);
        assert(!xl.lt(r * r));
        assert(xl.lt((r + 1) * (r + 1)));
        let r4 = hint_isqrt::<4>(xs[i]);
        assert(r4.lt(16));
        for j in 0..8 {
            let _ = hint_lt_128(xs[i], xs[j]);
        }
    }
}

/// Positive controls for the wrong-hint tests below.
#[test]
fn honest_isqrt_and_abs_diff_accepted() {
    constrain_isqrt::<8>(0, 0);
    constrain_isqrt::<8>(15, 3);
    constrain_isqrt::<8>(16, 4);
    constrain_isqrt::<8>(255, 15);
    constrain_isqrt::<128>(TWO_POW_128 - 1, TWO_POW_64 - 1);
    assert_eq(constrain_abs_diff::<8>(3, 10, true), 7);
    assert_eq(constrain_abs_diff::<8>(10, 3, false), 7);
    // at a = b both bits give 0: the output is determined, the bit is not
    assert_eq(constrain_abs_diff::<8>(5, 5, true), 0);
    assert_eq(constrain_abs_diff::<8>(5, 5, false), 0);
    assert_eq(constrain_abs_diff::<128>(TWO_POW_128 - 1, 0, false), TWO_POW_128 - 1);
}

#[test(should_fail)]
fn isqrt_root_too_big_rejected() {
    // 4^2 > 15: x - r*r wraps to p - 1
    constrain_isqrt::<8>(15, 4);
}

#[test(should_fail)]
fn isqrt_root_too_small_rejected() {
    // (2 + 1)^2 <= 15: (r + 1)^2 - x - 1 wraps
    constrain_isqrt::<8>(15, 2);
}

/// A field element r with 2r = s for an odd s < 2^129 and
/// s^2 = p + 4*(x - u): for x = 0 the expressions x - r*r and
/// (r + 1)^2 - x - 1 are u and v below 2^128 (found by search).
global FIELD_ROOT: Field = 0x183227397098d014dc2822db40c0ac2ecbc0b548b438e547056ea219dbdc0d8d;

#[test]
fn field_root_passes_the_two_bounds() {
    // control: only the root's own RANGE rejects FIELD_ROOT
    let r = FIELD_ROOT;
    assert_eq(0 - r * r, 0x29bd10db598521bee475d47f86cc6de4);
    assert_eq((r + 1) * (r + 1) - 1, 0x4590716d9533383de2857a2040ebad35);
}

#[test(should_fail)]
fn isqrt_field_root_rejected() {
    constrain_isqrt::<128>(0, FIELD_ROOT);
}

#[test(should_fail)]
fn abs_diff_wrong_bit_rejected() {
    // a > b with c = 1: d = b - a = p - 7
    let _ = constrain_abs_diff::<8>(10, 3, true);
}

#[test(should_fail)]
fn abs_diff_missing_bit_rejected() {
    let _ = constrain_abs_diff::<8>(3, 10, false);
}

#[test(should_fail)]
fn abs_diff_wrong_bit_at_128_rejected() {
    let _ = constrain_abs_diff::<128>(TWO_POW_128 - 1, 0, true);
}
