// bitwise: and/or/xor/not_bits_or, the Field-domain shifts and rotations
// on both amount fronts (N <= 16 and N >= 17), and TotalShift on u8..u128.
use crate::bitwise::{
    and_bits_or, not_bits_or, or_bits_or, rotate_left_or, rotate_right_or, shl_exact_or, shl_or,
    shr_or, TotalShift, xor_bits_or,
};
use super::{bit, fits, high_bits, low_bits, Num, or_zero, pick_u, pow2, shape};

/// and, or, xor of two n-bit values bit by bit, then not of a.
unconstrained fn bitwise_model(a: Field, b: Field, n: u32) -> [(Field, bool); 4] {
    let ok = fits(a, n) & fits(b, n);
    let mut r = [0; 4];
    let mut pw: Field = 1;
    for i in 0..n {
        let (x, y) = (bit(a, i), bit(b, i));
        r[0] += (x & y) as Field * pw;
        r[1] += (x | y) as Field * pw;
        r[2] += (x ^ y) as Field * pw;
        r[3] += (!x) as Field * pw;
        pw *= 2;
    }
    [or_zero(ok, r[0]), or_zero(ok, r[1]), or_zero(ok, r[2]), or_zero(fits(a, n), r[3])]
}

fn check_bitwise<let N: u32>(sa: u8, a: Field, sb: u8, b: Field) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b) = unsafe { (shape(sa, a, N), shape(sb, b, N)) };
    // Safety: reference model, compared below.
    let m = unsafe { bitwise_model(a, b, N) };
    assert_eq(and_bits_or::<N>(a, b), m[0]);
    assert_eq(or_bits_or::<N>(a, b), m[1]);
    assert_eq(xor_bits_or::<N>(a, b), m[2]);
    assert_eq(not_bits_or::<N>(a), m[3]);
}

#[test]
fn bit_ops_field(sa: u8, a: Field, sb: u8, b: Field) {
    check_bitwise::<1>(sa, a, sb, b);
    check_bitwise::<8>(sa, a, sb, b);
    check_bitwise::<13>(sa, a, sb, b);
    check_bitwise::<64>(sa, a, sb, b);
    check_bitwise::<127>(sa, a, sb, b);
    check_bitwise::<128>(sa, a, sb, b);
}

/// shl, shl_exact, shr, rotate_left, rotate_right of an n-bit a by s,
/// from the bits that stay and the bits that move: with s < n,
/// a << s mod 2^n = (a mod 2^(n - s)) * 2^s and the bits shifted out are
/// a >> (n - s).
unconstrained fn shift_model(a: Field, s: Field, n: u32) -> [(Field, bool); 5] {
    if fits(a, n) & s.lt(n as Field) {
        let s = s as u32;
        let shl = low_bits(a, n - s) * pow2(s);
        let out = high_bits(a, n - s);
        let shr = high_bits(a, s);
        [
            (shl, true),
            or_zero(out == 0, shl),
            (shr, true),
            (shl + out, true),
            (shr + low_bits(a, s) * pow2(n - s), true),
        ]
    } else {
        [(0, false); 5]
    }
}

/// A shift amount for width n chosen by sel: 0, 1, n - 1, n, n + 1, a
/// value below n, p - 1, or s itself.
unconstrained fn shape_amount(sel: u8, s: Field, n: u32) -> Field {
    let k = sel % 8;
    let n = n as Field;
    if k == 0 {
        0
    } else if k == 1 {
        1
    } else if k == 2 {
        n - 1
    } else if k == 3 {
        n
    } else if k == 4 {
        n + 1
    } else if k == 5 {
        ((s as u32) % (n as u32)) as Field
    } else if k == 6 {
        0 - 1
    } else {
        s
    }
}

fn check_shifts<let N: u32>(sa: u8, a: Field, ss: u8, s: Field) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, s) = unsafe { (shape(sa, a, N), shape_amount(ss, s, N)) };
    // Safety: reference model, compared below.
    let m = unsafe { shift_model(a, s, N) };
    assert_eq(shl_or::<N>(a, s), m[0]);
    assert_eq(shl_exact_or::<N>(a, s), m[1]);
    assert_eq(shr_or::<N>(a, s), m[2]);
    assert_eq(rotate_left_or::<N>(a, s), m[3]);
    assert_eq(rotate_right_or::<N>(a, s), m[4]);
}

#[test]
fn shifts_field_scan(sa: u8, a: Field, ss: u8, s: Field) {
    check_shifts::<1>(sa, a, ss, s);
    check_shifts::<2>(sa, a, ss, s);
    check_shifts::<7>(sa, a, ss, s);
    check_shifts::<16>(sa, a, ss, s);
}

#[test]
fn shifts_field_split(sa: u8, a: Field, ss: u8, s: Field) {
    check_shifts::<17>(sa, a, ss, s);
    check_shifts::<32>(sa, a, ss, s);
    check_shifts::<64>(sa, a, ss, s);
    check_shifts::<100>(sa, a, ss, s);
    check_shifts::<127>(sa, a, ss, s);
    check_shifts::<128>(sa, a, ss, s);
}

/// shape_amount for a typed amount.
unconstrained fn pick_amount<T: Num, let N: u32>(sel: u8, s: T) -> T {
    T::from_real(shape_amount(sel, s.real(), N))
}

fn check_total_shift<T, let N: u32>(sa: u8, a: T, ss: u8, s: T)
where
    T: Num + TotalShift,
{
    // Safety: input selection; the values reach the library as witnesses.
    let (a, s) = unsafe { (pick_u::<T, N>(sa, a), pick_amount::<T, N>(ss, s)) };
    // Safety: reference model, compared below.
    let m = unsafe { shift_model(a.real(), s.real(), N) };
    let (v, ok) = a.shl_or(s);
    assert_eq((v.real(), ok), m[0]);
    let (v, ok) = a.shl_exact_or(s);
    assert_eq((v.real(), ok), m[1]);
    let (v, ok) = a.shr_or(s);
    assert_eq((v.real(), ok), m[2]);
}

#[test]
fn total_shift(
    sa: [u8; 5],
    ss: [u8; 5],
    a: (u8, u16, u32, u64, u128),
    s: (u8, u16, u32, u64, u128),
) {
    check_total_shift::<u8, 8>(sa[0], a.0, ss[0], s.0);
    check_total_shift::<u16, 16>(sa[1], a.1, ss[1], s.1);
    check_total_shift::<u32, 32>(sa[2], a.2, ss[2], s.2);
    check_total_shift::<u64, 64>(sa[3], a.3, ss[3], s.3);
    check_total_shift::<u128, 128>(sa[4], a.4, ss[4], s.4);
}
