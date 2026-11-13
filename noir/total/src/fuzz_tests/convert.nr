// convert: Field to native integers (both signed readings), truncate_or,
// sgn0, the bounded bit and byte decompositions, full-width decoding, and
// every TotalNarrow impl.
use crate::convert::{
    bool_or, from_be_bits_or, from_be_bytes_or, from_le_bits_or, from_le_bytes_or, sgn0,
    to_be_bits_or, to_be_bytes_or, to_i16_from_signed_or, to_i16_or, to_i32_from_signed_or,
    to_i32_or, to_i64_from_signed_or, to_i64_or, to_i8_from_signed_or, to_i8_or, to_le_bits_or,
    to_le_bytes_or, to_u128_or, to_u16_or, to_u32_or, to_u64_or, to_u8_or, TotalNarrow, truncate_or,
};
use super::{bit, fits, high_bits, limbs, low_bits, Num, pick_s, pick_u, pow2, shape};

// ---------------------------------------------------------------------
// Field to native
// ---------------------------------------------------------------------

/// The unsigned reading of x on n bits: (x, ok).
fn check_to_u<T, let N: u32>(s: u8, x: Field, f: fn(Field) -> (T, bool))
where
    T: Num,
{
    // Safety: input selection; the value reaches the library as a witness.
    let x = unsafe { shape(s, x, N) };
    // Safety: reference model, compared below.
    let ok = unsafe { fits(x, N) };
    let (v, vok) = f(x);
    assert_eq((v.real(), vok), (if ok { x } else { 0 }, ok));
}

/// The bit-pattern reading of x on n bits: a pattern at or above 2^(n-1)
/// is the negative value pattern - 2^n.
fn check_to_i<T, let N: u32>(s: u8, x: Field, f: fn(Field) -> (T, bool))
where
    T: Num,
{
    // Safety: input selection; the value reaches the library as a witness.
    let x = unsafe { shape(s, x, N) };
    // Safety: reference model, compared below.
    let (ok, negative, m) = unsafe { (fits(x, N), !fits(x, N - 1), pow2(N)) };
    let want = if !ok {
        0
    } else if negative {
        x - m
    } else {
        x
    };
    let (v, vok) = f(x);
    assert_eq((v.real(), vok), (want, ok));
}

/// Whether x is a signed n-bit value: in [0, 2^(n-1)) or [p - 2^(n-1), p).
unconstrained fn signed_value_ok(x: Field, n: u32) -> bool {
    let h = pow2(n - 1);
    x.lt(h) | !x.lt(0 - h)
}

/// The signed-value reading. Inputs come from the width n - 1 shaper,
/// negated when asked.
fn check_from_signed<T, let N: u32>(s: u8, x: Field, negate: bool, f: fn(Field) -> (T, bool))
where
    T: Num,
{
    // Safety: input selection; the value reaches the library as a witness.
    let x = unsafe { shape(s, x, N - 1) };
    let x = if negate { 0 - x } else { x };
    // Safety: reference model, compared below.
    let ok = unsafe { signed_value_ok(x, N) };
    let (v, vok) = f(x);
    assert_eq((v.real(), vok), (if ok { x } else { 0 }, ok));
}

#[test]
fn field_to_native(s: u8, x: Field, negate: bool) {
    check_to_u::<u8, 8>(s, x, to_u8_or);
    check_to_u::<u16, 16>(s, x, to_u16_or);
    check_to_u::<u32, 32>(s, x, to_u32_or);
    check_to_u::<u64, 64>(s, x, to_u64_or);
    check_to_u::<u128, 128>(s, x, to_u128_or);
    check_to_i::<i8, 8>(s, x, to_i8_or);
    check_to_i::<i16, 16>(s, x, to_i16_or);
    check_to_i::<i32, 32>(s, x, to_i32_or);
    check_to_i::<i64, 64>(s, x, to_i64_or);
    check_from_signed::<i8, 8>(s, x, negate, to_i8_from_signed_or);
    check_from_signed::<i16, 16>(s, x, negate, to_i16_from_signed_or);
    check_from_signed::<i32, 32>(s, x, negate, to_i32_from_signed_or);
    check_from_signed::<i64, 64>(s, x, negate, to_i64_from_signed_or);
    // Safety: input selection; the value reaches the library as a witness.
    let b = unsafe { shape(s, x, 1) };
    assert_eq(bool_or(b), (b == 1, (b == 0) | (b == 1)));
}

// ---------------------------------------------------------------------
// truncate_or, sgn0, bits and bytes
// ---------------------------------------------------------------------

fn check_truncate<let N: u32>(s: u8, x: Field) {
    // Safety: input selection; the value reaches the library as a witness.
    let x = unsafe { shape(s, x, N) };
    // Safety: reference model, compared below.
    let (lo, dropped) = unsafe { (low_bits(x, N), high_bits(x, N)) };
    assert_eq(truncate_or::<N>(x), (lo, dropped, dropped == 0));
}

/// The bits of x below 2^n, or all false.
unconstrained fn le_bits_model<let N: u32>(x: Field) -> ([bool; N], bool) {
    let ok = fits(x, N);
    let mut bits = [false; N];
    for i in 0..N {
        bits[i] = ok & bit(x, i);
    }
    (bits, ok)
}

fn check_bits<let N: u32>(s: u8, x: Field) {
    // Safety: input selection; the value reaches the library as a witness.
    let x = unsafe { shape(s, x, N) };
    // Safety: reference model, compared below.
    let (le, ok) = unsafe { le_bits_model::<N>(x) };
    let mut be = [false; N];
    for i in 0..N {
        be[i] = le[N - 1 - i];
    }
    assert_eq(to_le_bits_or::<N>(x), (le, ok));
    assert_eq(to_be_bits_or::<N>(x), (be, ok));
}

/// The bytes of x below 2^(8n), or all zero.
pub(crate) unconstrained fn le_bytes_model<let N: u32>(x: Field) -> ([u8; N], bool) {
    let ok = fits(x, 8 * N);
    let mut bytes = [0; N];
    for i in 0..N {
        let byte = low_bits(high_bits(x, 8 * i), 8) as u8;
        bytes[i] = if ok { byte } else { 0 };
    }
    (bytes, ok)
}

fn check_bytes<let N: u32>(s: u8, x: Field) {
    // Safety: input selection; the value reaches the library as a witness.
    let x = unsafe { shape(s, x, 8 * N) };
    // Safety: reference model, compared below.
    let (le, ok) = unsafe { le_bytes_model::<N>(x) };
    let mut be = [0; N];
    for i in 0..N {
        be[i] = le[N - 1 - i];
    }
    assert_eq(to_le_bytes_or::<N>(x), (le, ok));
    assert_eq(to_be_bytes_or::<N>(x), (be, ok));
}

#[test]
fn truncate_bits_bytes(s: u8, x: Field) {
    check_truncate::<1>(s, x);
    check_truncate::<8>(s, x);
    check_truncate::<127>(s, x);
    check_truncate::<128>(s, x);
    check_truncate::<129>(s, x);
    check_truncate::<253>(s, x);
    // Safety: reference model, compared below.
    let odd = unsafe { bit(x, 0) };
    assert_eq(sgn0(x), odd);
    check_bits::<1>(s, x);
    check_bits::<8>(s, x);
    check_bits::<128>(s, x);
    check_bits::<129>(s, x);
    check_bits::<253>(s, x);
    check_bytes::<1>(s, x);
    check_bytes::<16>(s, x);
    check_bytes::<31>(s, x);
}

/// Round trip through the 31-byte decomposition and the 32-byte decoder.
#[test]
fn bytes_round_trip(s: u8, x: Field) {
    // Safety: input selection; the value reaches the library as a witness.
    let x = unsafe { shape(s, x, 248) };
    // Safety: reference model, compared below.
    let ok = unsafe { fits(x, 248) };
    let (le, lok) = to_le_bytes_or::<31>(x);
    let (be, bok) = to_be_bytes_or::<31>(x);
    let mut le32 = [0; 32];
    let mut be32 = [0; 32];
    for i in 0..31 {
        le32[i] = le[i];
        be32[i + 1] = be[i];
    }
    let want = if ok { x } else { 0 };
    assert_eq((lok, bok), (ok, ok));
    assert_eq(from_le_bytes_or(le32), (want, true));
    assert_eq(from_be_bytes_or(be32), (want, true));
}

// ---------------------------------------------------------------------
// Full-width decoding
// ---------------------------------------------------------------------

/// A 32-byte little-endian encoding chosen by sel: the raw bytes, p, p - 1,
/// p + 1, or the raw bytes with the top byte cleared.
pub(crate) unconstrained fn shape_bytes(sel: u8, raw: [u8; 32]) -> [u8; 32] {
    let p = std::field::modulus_le_bytes();
    let mut out = raw;
    let k = sel % 5;
    if (k >= 1) & (k <= 3) {
        for i in 0..32 {
            out[i] = p[i];
        }
        // The low byte of p is 1, so p - 1 and p + 1 differ from p there only.
        if k == 2 {
            out[0] = p[0] - 1;
        } else if k == 3 {
            out[0] = p[0] + 1;
        }
    } else if k == 4 {
        out[31] = 0;
    }
    out
}

/// The integer a little-endian byte string encodes, as (hi, lo), and
/// whether it is below p (compared with the limbs of p - 1).
pub(crate) unconstrained fn decode_model(le: [u8; 32]) -> (Field, bool) {
    let mut lo: u128 = 0;
    let mut hi: u128 = 0;
    for i in 0..16 {
        lo = lo * 256 + le[15 - i] as u128;
        hi = hi * 256 + le[31 - i] as u128;
    }
    let (phi, plo) = limbs(0 - 1);
    let ok = (hi < phi) | ((hi == phi) & (lo <= plo));
    if ok {
        ((lo as Field) + (hi as Field) * pow2(128), true)
    } else {
        (0, false)
    }
}

#[test]
fn decode_bytes(s: u8, raw: [u8; 32]) {
    // Safety: input selection; the bytes reach the library as witnesses.
    let le = unsafe { shape_bytes(s, raw) };
    // Safety: reference model, compared below.
    let want = unsafe { decode_model(le) };
    let mut be = [0; 32];
    for i in 0..32 {
        be[i] = le[31 - i];
    }
    assert_eq(from_le_bytes_or(le), want);
    assert_eq(from_be_bytes_or(be), want);
}

/// A 254-bit little-endian encoding chosen by sel: the raw bits, p, p - 1,
/// or the raw bits with the top bit cleared.
pub(crate) unconstrained fn shape_bits(sel: u8, raw: [bool; 254]) -> [bool; 254] {
    let p = std::field::modulus_le_bits();
    let mut out = raw;
    let k = sel % 4;
    if (k == 1) | (k == 2) {
        for i in 0..254 {
            out[i] = (p[i] as u8) == 1;
        }
        // p is odd: p - 1 clears bit 0.
        if k == 2 {
            out[0] = false;
        }
    } else if k == 3 {
        out[253] = false;
    }
    out
}

/// decode_model on the bits packed into bytes.
pub(crate) unconstrained fn decode_bits_model(le: [bool; 254]) -> (Field, bool) {
    let mut bytes = [0; 32];
    for i in 0..254 {
        bytes[i / 8] += (le[i] as u8) << ((i % 8) as u8);
    }
    decode_model(bytes)
}

#[test]
fn decode_bits(s: u8, raw: [bool; 254]) {
    // Safety: input selection; the bits reach the library as witnesses.
    let le = unsafe { shape_bits(s, raw) };
    // Safety: reference model, compared below.
    let want = unsafe { decode_bits_model(le) };
    let mut be = [false; 254];
    for i in 0..254 {
        be[i] = le[253 - i];
    }
    assert_eq(from_le_bits_or(le), want);
    assert_eq(from_be_bits_or(be), want);
}

// ---------------------------------------------------------------------
// TotalNarrow
// ---------------------------------------------------------------------

/// lo <= r <= hi on real values, for hi - lo < 2^128.
unconstrained fn in_bounds(r: Field, lo: Field, hi: Field) -> bool {
    (r - lo).lt(hi - lo + 1)
}

/// x converted to T: (x, true) when T holds the value, else (0, false).
fn check_narrow<S, T>(x: S)
where
    S: Num + TotalNarrow<T>,
    T: Num,
{
    let r = x.real();
    let (lo, hi) = T::bounds();
    // Safety: reference model, compared below.
    let ok = unsafe { in_bounds(r, lo, hi) };
    let (v, vok): (T, bool) = x.narrow_or();
    assert_eq((v.real(), vok), (if ok { r } else { 0 }, ok));
}

#[test]
fn narrow_from_unsigned(s: [u8; 5], a: u8, b: u16, c: u32, d: u64, e: u128) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b, c, d, e) = unsafe {
        (
            pick_u::<u8, 8>(s[0], a), pick_u::<u16, 16>(s[1], b), pick_u::<u32, 32>(s[2], c),
            pick_u::<u64, 64>(s[3], d), pick_u::<u128, 128>(s[4], e),
        )
    };
    check_narrow::<u8, i8>(a);
    check_narrow::<u8, i16>(a);
    check_narrow::<u8, i32>(a);
    check_narrow::<u8, i64>(a);
    check_narrow::<u16, u8>(b);
    check_narrow::<u16, i8>(b);
    check_narrow::<u16, i16>(b);
    check_narrow::<u16, i32>(b);
    check_narrow::<u16, i64>(b);
    check_narrow::<u32, u8>(c);
    check_narrow::<u32, u16>(c);
    check_narrow::<u32, i8>(c);
    check_narrow::<u32, i16>(c);
    check_narrow::<u32, i32>(c);
    check_narrow::<u32, i64>(c);
    check_narrow::<u64, u8>(d);
    check_narrow::<u64, u16>(d);
    check_narrow::<u64, u32>(d);
    check_narrow::<u64, i8>(d);
    check_narrow::<u64, i16>(d);
    check_narrow::<u64, i32>(d);
    check_narrow::<u64, i64>(d);
    check_narrow::<u128, u8>(e);
    check_narrow::<u128, u16>(e);
    check_narrow::<u128, u32>(e);
    check_narrow::<u128, u64>(e);
    check_narrow::<u128, i8>(e);
    check_narrow::<u128, i16>(e);
    check_narrow::<u128, i32>(e);
    check_narrow::<u128, i64>(e);
}

#[test]
fn narrow_from_signed(s: [u8; 4], a: i8, b: i16, c: i32, d: i64) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b, c, d) = unsafe {
        (
            pick_s::<i8, 8>(s[0], a), pick_s::<i16, 16>(s[1], b), pick_s::<i32, 32>(s[2], c),
            pick_s::<i64, 64>(s[3], d),
        )
    };
    check_narrow::<i8, u8>(a);
    check_narrow::<i8, u16>(a);
    check_narrow::<i8, u32>(a);
    check_narrow::<i8, u64>(a);
    check_narrow::<i8, u128>(a);
    check_narrow::<i16, i8>(b);
    check_narrow::<i16, u8>(b);
    check_narrow::<i16, u16>(b);
    check_narrow::<i16, u32>(b);
    check_narrow::<i16, u64>(b);
    check_narrow::<i16, u128>(b);
    check_narrow::<i32, i8>(c);
    check_narrow::<i32, i16>(c);
    check_narrow::<i32, u8>(c);
    check_narrow::<i32, u16>(c);
    check_narrow::<i32, u32>(c);
    check_narrow::<i32, u64>(c);
    check_narrow::<i32, u128>(c);
    check_narrow::<i64, i8>(d);
    check_narrow::<i64, i16>(d);
    check_narrow::<i64, i32>(d);
    check_narrow::<i64, u8>(d);
    check_narrow::<i64, u16>(d);
    check_narrow::<i64, u32>(d);
    check_narrow::<i64, u64>(d);
    check_narrow::<i64, u128>(d);
}
