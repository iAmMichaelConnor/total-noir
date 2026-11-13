// encode: the canonicity flags, the 31-byte chunk and Field packing
// entries, and the fixed-width integer byte conversions.
use crate::encode::{
    bytes_to_fields_be, bytes_to_fields_le, canonical_be_bits_flag, canonical_be_bytes_flag,
    canonical_le_bits_flag, canonical_le_bytes_flag, chunk_to_be_bytes_or, chunk_to_le_bytes_or,
    fields_to_bytes_be_or, fields_to_bytes_le_or, reverse, u128_from_be_bytes, u128_from_le_bytes,
    u128_to_be_bytes, u128_to_le_bytes, u16_from_be_bytes, u16_from_le_bytes, u16_to_be_bytes,
    u16_to_le_bytes, u32_from_be_bytes, u32_from_le_bytes, u32_to_be_bytes, u32_to_le_bytes,
    u64_from_be_bytes, u64_from_le_bytes, u64_to_be_bytes, u64_to_le_bytes,
};
use super::convert::{decode_bits_model, decode_model, le_bytes_model, shape_bits, shape_bytes};
use super::{pick_u, shape};

#[test]
fn canonical_flags(s: [u8; 2], raw: [u8; 32], bits: [bool; 254]) {
    // Safety: input selection; the values reach the library as witnesses.
    let (le, le_bits) = unsafe { (shape_bytes(s[0], raw), shape_bits(s[1], bits)) };
    // Safety: reference model, compared below.
    let (ok, bits_ok) = unsafe { (decode_model(le).1, decode_bits_model(le_bits).1) };
    assert_eq((canonical_le_bytes_flag(le), canonical_be_bytes_flag(reverse(le))), (ok, ok));
    assert_eq(
        (canonical_le_bits_flag(le_bits), canonical_be_bits_flag(reverse(le_bits))),
        (bits_ok, bits_ok),
    );
}

/// The 31 bytes of each Field below 2^248, little-endian and big-endian,
/// and the packing back.
#[test]
fn chunks_and_packing(s: [u8; 2], x: [Field; 2]) {
    // Safety: input selection; the values reach the library as witnesses.
    let f = unsafe { [shape(s[0], x[0], 248), shape(s[1], x[1], 248)] };
    // Safety: reference model, compared below.
    let ((c0, ok0), (c1, ok1)) =
        unsafe { (le_bytes_model::<31>(f[0]), le_bytes_model::<31>(f[1])) };
    assert_eq(chunk_to_le_bytes_or(f[0]), (c0, ok0));
    assert_eq(chunk_to_be_bytes_or(f[0]), (reverse(c0), ok0));
    let ok = ok0 & ok1;
    let (be1, be0) = (reverse(c1), reverse(c0));
    let mut le = [0; 62];
    let mut be = [0; 62];
    for j in 0..31 {
        le[j] = if ok { c0[j] } else { 0 };
        le[31 + j] = if ok { c1[j] } else { 0 };
        be[j] = if ok { be0[j] } else { 0 };
        be[31 + j] = if ok { be1[j] } else { 0 };
    }
    assert_eq(fields_to_bytes_le_or(f), (le, ok));
    assert_eq(fields_to_bytes_be_or(f), (be, ok));
    let packed = if ok { f } else { [0; 2] };
    assert_eq(bytes_to_fields_le(le), packed);
    assert_eq(bytes_to_fields_be(be), packed);
}

/// The bytes of a native value, both byte orders, and back.
#[test]
fn integer_bytes(s: [u8; 4], a: u16, b: u32, c: u64, d: u128) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b, c, d) = unsafe {
        (
            pick_u::<u16, 16>(s[0], a), pick_u::<u32, 32>(s[1], b), pick_u::<u64, 64>(s[2], c),
            pick_u::<u128, 128>(s[3], d),
        )
    };
    // Safety: reference model, compared below.
    let (la, lb, lc, ld) = unsafe {
        (
            le_bytes_model::<2>(a as Field).0, le_bytes_model::<4>(b as Field).0,
            le_bytes_model::<8>(c as Field).0, le_bytes_model::<16>(d as Field).0,
        )
    };
    assert_eq((u16_to_le_bytes(a), u16_to_be_bytes(a)), (la, reverse(la)));
    assert_eq((u32_to_le_bytes(b), u32_to_be_bytes(b)), (lb, reverse(lb)));
    assert_eq((u64_to_le_bytes(c), u64_to_be_bytes(c)), (lc, reverse(lc)));
    assert_eq((u128_to_le_bytes(d), u128_to_be_bytes(d)), (ld, reverse(ld)));
    assert_eq((u16_from_le_bytes(la), u16_from_be_bytes(reverse(la))), (a, a));
    assert_eq((u32_from_le_bytes(lb), u32_from_be_bytes(reverse(lb))), (b, b));
    assert_eq((u64_from_le_bytes(lc), u64_from_be_bytes(reverse(lc))), (c, c));
    assert_eq((u128_from_le_bytes(ld), u128_from_be_bytes(reverse(ld))), (d, d));
}
