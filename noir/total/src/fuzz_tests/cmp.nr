// cmp: cmp_bits from 1 to 253 bits, and the TotalOrd free functions on
// Field, bool and the native integer types.
use crate::cmp::{clamp, cmp_bits, eq, gt, gte, lt, lte, max, min, neq, TotalOrd};
use super::{fits, Num, pick_s, pick_u, pow2, shape};

/// (lt, eq, gt, a_ok, b_ok) for two n-bit values; the comparison flags
/// are all false unless both are in range.
unconstrained fn cmp_model(a: Field, b: Field, n: u32) -> [bool; 5] {
    let (a_ok, b_ok) = (fits(a, n), fits(b, n));
    let ok = a_ok & b_ok;
    [ok & a.lt(b), ok & (a == b), ok & b.lt(a), a_ok, b_ok]
}

fn check_cmp_bits<let N: u32>(sa: u8, a: Field, sb: u8, b: Field, same: bool) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b) = unsafe { (shape(sa, a, N), shape(sb, b, N)) };
    let b = if same { a } else { b };
    // Safety: reference model, compared below.
    let m = unsafe { cmp_model(a, b, N) };
    let f = cmp_bits::<N>(a, b);
    assert_eq([f.lt, f.eq, f.gt, f.a_ok, f.b_ok], m);
    assert_eq(
        [f.ok(), f.lte(), f.gte(), f.neq()],
        [m[3] & m[4], m[0] | m[1], m[2] | m[1], m[0] | m[2]],
    );
}

#[test]
fn cmp_bits_field(sa: u8, a: Field, sb: u8, b: Field, same: bool) {
    check_cmp_bits::<1>(sa, a, sb, b, same);
    check_cmp_bits::<8>(sa, a, sb, b, same);
    check_cmp_bits::<64>(sa, a, sb, b, same);
    check_cmp_bits::<127>(sa, a, sb, b, same);
    check_cmp_bits::<128>(sa, a, sb, b, same);
    check_cmp_bits::<129>(sa, a, sb, b, same);
    check_cmp_bits::<253>(sa, a, sb, b, same);
}

/// a < b on real values. Integers: shifted by 2^200, every real value
/// here (magnitude below 2^129) lands in (0, p) with its order kept.
/// Fields: the order of canonical values.
unconstrained fn less(a: Field, b: Field, field_order: bool) -> bool {
    let shift = if field_order { 0 } else { pow2(200) };
    (a + shift).lt(b + shift)
}

/// [lt, lte, gt, gte] of x and y, then min(x, y), max(x, y) and
/// clamp(x, y, z) = min(max(x, y), z).
unconstrained fn ord_model(x: Field, y: Field, z: Field, f: bool) -> ([bool; 4], [Field; 3]) {
    let lt = less(x, y, f);
    let gt = less(y, x, f);
    let lo_max = if lt { y } else { x };
    let clamped = if less(z, lo_max, f) { z } else { lo_max };
    ([lt, !gt, gt, !lt], [if gt { y } else { x }, lo_max, clamped])
}

/// Every TotalOrd free function on x, y, z against the order of their
/// real values.
fn check_ord<T>(x: T, y: T, z: T, field_order: bool)
where
    T: TotalOrd + Num,
{
    let (rx, ry, rz) = (x.real(), y.real(), z.real());
    // Safety: reference model, compared below.
    let (flags, vals) = unsafe { ord_model(rx, ry, rz, field_order) };
    assert_eq([eq(x, y), neq(x, y)], [rx == ry, rx != ry]);
    assert_eq([lt(x, y), lte(x, y), gt(x, y), gte(x, y)], flags);
    assert_eq([min(x, y).real(), max(x, y).real(), clamp(x, y, z).real()], vals);
}

/// check_ord on N-bit inputs from the unsigned shaper; y repeats x when
/// the selectors agree, to reach equality.
fn check_ord_u<T, let N: u32>(s: [u8; 3], x: T, y: T, z: T)
where
    T: TotalOrd + Num,
{
    // Safety: input selection; the values reach the library as witnesses.
    let (x, y, z) =
        unsafe { (pick_u::<T, N>(s[0], x), pick_u::<T, N>(s[1], y), pick_u::<T, N>(s[2], z)) };
    check_ord(x, if s[0] == s[1] { x } else { y }, z, false);
}

/// check_ord_u for the signed shaper.
fn check_ord_s<T, let N: u32>(s: [u8; 3], x: T, y: T, z: T)
where
    T: TotalOrd + Num,
{
    // Safety: input selection; the values reach the library as witnesses.
    let (x, y, z) =
        unsafe { (pick_s::<T, N>(s[0], x), pick_s::<T, N>(s[1], y), pick_s::<T, N>(s[2], z)) };
    check_ord(x, if s[0] == s[1] { x } else { y }, z, false);
}

#[test]
fn ord_unsigned(s: [u8; 3], a: [u8; 3], b: [u16; 3], c: [u32; 3], d: [u64; 3], e: [u128; 3]) {
    check_ord_u::<u8, 8>(s, a[0], a[1], a[2]);
    check_ord_u::<u16, 16>(s, b[0], b[1], b[2]);
    check_ord_u::<u32, 32>(s, c[0], c[1], c[2]);
    check_ord_u::<u64, 64>(s, d[0], d[1], d[2]);
    check_ord_u::<u128, 128>(s, e[0], e[1], e[2]);
}

#[test]
fn ord_signed(s: [u8; 3], a: [i8; 3], b: [i16; 3], c: [i32; 3], d: [i64; 3]) {
    check_ord_s::<i8, 8>(s, a[0], a[1], a[2]);
    check_ord_s::<i16, 16>(s, b[0], b[1], b[2]);
    check_ord_s::<i32, 32>(s, c[0], c[1], c[2]);
    check_ord_s::<i64, 64>(s, d[0], d[1], d[2]);
}

#[test]
fn ord_field_bool(s: [u8; 3], f: [Field; 3], b: [bool; 3]) {
    // Safety: input selection; the values reach the library as witnesses.
    let (x, y, z) =
        unsafe { (shape(s[0], f[0], 253), shape(s[1], f[1], 253), shape(s[2], f[2], 253)) };
    check_ord(x, if s[0] == s[1] { x } else { y }, z, true);
    check_ord(b[0], b[1], b[2], false);
}
