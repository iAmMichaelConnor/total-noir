use crate::core::{two_pow, TWO_POW_128};
use crate::range::fits_bits;
use crate::test_support::wit;
use super::{
    bool_or, from_be_bits_or, from_be_bytes_or, from_bool, from_i16, from_i16_signed, from_i32,
    from_i32_signed, from_i64, from_i64_signed, from_i8, from_i8_signed, from_le_bits_or,
    from_le_bytes_or, from_u128, from_u16, from_u32, from_u64, from_u8, limbs_below_modulus, PHI,
    PLO, sgn0, to_be_bits_or, to_be_bits_total, to_be_bytes_or, to_be_bytes_total,
    to_i16_from_signed_or, to_i16_or, to_i32_from_signed_or, to_i32_or, to_i64_from_signed_or,
    to_i64_or, to_i8_from_signed_or, to_i8_or, to_le_bits_or, to_le_bits_total, to_le_bytes_or,
    to_le_bytes_total, to_u128_or, to_u16_or, to_u32_or, to_u64_or, to_u8_or, TotalNarrow,
    truncate_or,
};

global PM1: Field = 0 - 1;

#[test]
fn modulus_limbs() {
    assert_eq(PLO + PHI * TWO_POW_128, 0);
    let p = std::field::modulus_le_bytes();
    let mut lo: Field = 0;
    let mut hi: Field = 0;
    let mut pw: Field = 1;
    for i in 0..16 {
        lo += (p[i] as Field) * pw;
        hi += (p[i + 16] as Field) * pw;
        pw *= 256;
    }
    assert_eq(lo, PLO);
    assert_eq(hi, PHI);
    // PHI fits 126 bits, which the bit decoder relies on
    assert(PHI.lt(two_pow::<126>()));
}

// ---- Field -> unsigned ----

#[test]
fn to_u8_or_boundaries() {
    assert_eq(to_u8_or(wit(0)), (0, true));
    assert_eq(to_u8_or(wit(1)), (1, true));
    assert_eq(to_u8_or(wit(255)), (255, true));
    assert_eq(to_u8_or(wit(256)), (0, false));
    assert_eq(to_u8_or(wit(257)), (0, false));
    assert_eq(to_u8_or(wit(PM1)), (0, false));
    assert_eq(to_u8_or(wit(TWO_POW_128)), (0, false));
    assert_eq(to_u8_or(wit(TWO_POW_128 + 1)), (0, false));
}

#[test]
fn to_u16_u32_or_boundaries() {
    assert_eq(to_u16_or(wit(0)), (0, true));
    assert_eq(to_u16_or(wit(1)), (1, true));
    assert_eq(to_u16_or(wit(0xffff)), (0xffff, true));
    assert_eq(to_u16_or(wit(0x10000)), (0, false));
    assert_eq(to_u16_or(wit(0x10001)), (0, false));
    assert_eq(to_u16_or(wit(PM1)), (0, false));
    assert_eq(to_u32_or(wit(0xffffffff)), (0xffffffff, true));
    assert_eq(to_u32_or(wit(0x100000000)), (0, false));
    assert_eq(to_u32_or(wit(0)), (0, true));
    assert_eq(to_u32_or(wit(1)), (1, true));
    assert_eq(to_u32_or(wit(0x100000001)), (0, false));
    assert_eq(to_u32_or(wit(PM1)), (0, false));
}

#[test]
fn to_u64_or_boundaries() {
    assert_eq(to_u64_or(wit(0)), (0, true));
    assert_eq(to_u64_or(wit(0xffffffffffffffff)), (0xffffffffffffffff, true));
    assert_eq(to_u64_or(wit(0x10000000000000000)), (0, false));
    assert_eq(to_u64_or(wit(0x10000000000000001)), (0, false));
    assert_eq(to_u64_or(wit(PM1)), (0, false));
}

#[test]
fn to_u128_or_boundaries() {
    let m: u128 = 0xffffffffffffffffffffffffffffffff;
    assert_eq(to_u128_or(wit(TWO_POW_128 - 1)), (m, true));
    assert_eq(to_u128_or(wit(TWO_POW_128)), (0, false));
    assert_eq(to_u128_or(wit(TWO_POW_128 + 1)), (0, false));
    assert_eq(to_u128_or(wit(PM1)), (0, false));
    assert_eq(to_u128_or(wit(0)), (0, true));
}

#[test]
fn to_u_or_runtime_witness() {
    let x = wit(0x1ff);
    assert_eq(to_u8_or(wit(x)), (0, false));
    assert_eq(to_u16_or(wit(x)), (0x1ff, true));
}

// ---- Field -> signed ----

#[test]
fn to_i8_or_pattern_reading() {
    assert_eq(to_i8_or(wit(0)), (0, true));
    assert_eq(to_i8_or(wit(1)), (1, true));
    assert_eq(to_i8_or(wit(127)), (127, true));
    assert_eq(to_i8_or(wit(128)), (-128, true));
    assert_eq(to_i8_or(wit(255)), (-1, true));
    assert_eq(to_i8_or(wit(256)), (0, false));
    assert_eq(to_i8_or(wit(257)), (0, false));
    // Field -1 is not the pattern of -1
    assert_eq(to_i8_or(wit(PM1)), (0, false));
    assert_eq(to_i8_or(wit(TWO_POW_128)), (0, false));
}

#[test]
fn to_i_or_wider_patterns() {
    assert_eq(to_i16_or(wit(0)), (0, true));
    assert_eq(to_i16_or(wit(1)), (1, true));
    assert_eq(to_i16_or(wit(0xffff)), (-1, true));
    assert_eq(to_i16_or(wit(0x10001)), (0, false));
    assert_eq(to_i16_or(wit(PM1)), (0, false));
    assert_eq(to_i32_or(wit(0)), (0, true));
    assert_eq(to_i16_or(wit(0x8000)), (-32768, true));
    assert_eq(to_i16_or(wit(0x10000)), (0, false));
    assert_eq(to_i32_or(wit(0xffffffff)), (-1, true));
    assert_eq(to_i32_or(wit(0x7fffffff)), (2147483647, true));
    assert_eq(to_i32_or(wit(0x100000000)), (0, false));
    assert_eq(to_i64_or(wit(0xffffffffffffffff)), (-1, true));
    assert_eq(to_i64_or(wit(0x8000000000000000)), (-9223372036854775808, true));
    assert_eq(to_i64_or(wit(0x10000000000000000)), (0, false));
    assert_eq(to_i64_or(wit(0x10000000000000001)), (0, false));
    assert_eq(to_i64_or(wit(1)), (1, true));
    assert_eq(to_i64_or(wit(PM1)), (0, false));
}

#[test]
fn to_i8_from_signed_or_value_reading() {
    assert_eq(to_i8_from_signed_or(wit(0)), (0, true));
    assert_eq(to_i8_from_signed_or(wit(1)), (1, true));
    assert_eq(to_i8_from_signed_or(wit(127)), (127, true));
    assert_eq(to_i8_from_signed_or(wit(128)), (0, false));
    assert_eq(to_i8_from_signed_or(wit(PM1)), (-1, true));
    assert_eq(to_i8_from_signed_or(wit(0 - 128)), (-128, true));
    assert_eq(to_i8_from_signed_or(wit(0 - 129)), (0, false));
    assert_eq(to_i8_from_signed_or(wit(255)), (0, false));
    assert_eq(to_i8_from_signed_or(wit(TWO_POW_128)), (0, false));
}

#[test]
fn to_i_from_signed_or_wider() {
    assert_eq(to_i16_from_signed_or(wit(0 - 32768)), (-32768, true));
    assert_eq(to_i16_from_signed_or(wit(32767)), (32767, true));
    assert_eq(to_i16_from_signed_or(wit(32768)), (0, false));
    assert_eq(to_i16_from_signed_or(wit(0 - 32769)), (0, false));
    assert_eq(to_i32_from_signed_or(wit(0 - 2147483648)), (-2147483648, true));
    assert_eq(to_i32_from_signed_or(wit(2147483648)), (0, false));
    assert_eq(to_i64_from_signed_or(wit(PM1)), (-1, true));
    assert_eq(to_i64_from_signed_or(wit(0x7fffffffffffffff)), (9223372036854775807, true));
    assert_eq(to_i64_from_signed_or(wit(0x8000000000000000)), (0, false));
    assert_eq(to_i64_from_signed_or(wit(0 - 0x8000000000000000)), (-9223372036854775808, true));
    assert_eq(to_i64_from_signed_or(wit(0 - 0x8000000000000001)), (0, false));
}

// ---- widenings ----

#[test]
fn widenings_unsigned_and_bool() {
    assert_eq(from_bool(wit(true)), 1);
    assert_eq(from_bool(wit(false)), 0);
    assert_eq(from_u8(wit(255)), 255);
    assert_eq(from_u16(wit(0xffff)), 0xffff);
    assert_eq(from_u32(wit(0xffffffff)), 0xffffffff);
    assert_eq(from_u64(wit(0xffffffffffffffff)), 0xffffffffffffffff);
    assert_eq(from_u128(wit(0xffffffffffffffffffffffffffffffff)), TWO_POW_128 - 1);
}

#[test]
fn widenings_signed_both_readings() {
    assert_eq(from_i8(wit(-1)), 255);
    assert_eq(from_i8(wit(-128)), 128);
    assert_eq(from_i8(wit(127)), 127);
    assert_eq(from_i8_signed(wit(-1)), PM1);
    assert_eq(from_i8_signed(wit(-128)), 0 - 128);
    assert_eq(from_i8_signed(wit(127)), 127);
    assert_eq(from_i8_signed(wit(0)), 0);
    assert_eq(from_i16(wit(-1)), 0xffff);
    assert_eq(from_i16_signed(wit(-32768)), 0 - 32768);
    assert_eq(from_i32(wit(-1)), 0xffffffff);
    assert_eq(from_i32_signed(wit(-2147483648)), 0 - 2147483648);
    assert_eq(from_i64(wit(-1)), 0xffffffffffffffff);
    assert_eq(from_i64_signed(wit(-9223372036854775808)), 0 - 0x8000000000000000);
    assert_eq(from_i64_signed(wit(9223372036854775807)), 0x7fffffffffffffff);
}

#[test]
fn signed_round_trips() {
    let a = wit((0x8000000000000000 as u64) as i64);
    assert_eq(to_i64_or(wit(from_i64(wit(a)))), (a, true));
    assert_eq(to_i64_from_signed_or(wit(from_i64_signed(wit(a)))), (a, true));
    let b: i8 = -77;
    assert_eq(to_i8_or(wit(from_i8(wit(b)))), (b, true));
    assert_eq(to_i8_from_signed_or(wit(from_i8_signed(wit(b)))), (b, true));
}

// ---- narrowing ----

#[test]
fn narrow_unsigned() {
    let (v, ok): (u8, bool) = (255 as u16).narrow_or();
    assert_eq((v, ok), (255, true));
    let (v, ok): (u8, bool) = (256 as u16).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (u16, bool) = (0x1ffff as u32).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (u32, bool) = (0xffffffff as u64).narrow_or();
    assert_eq((v, ok), (0xffffffff, true));
    let (v, ok): (u32, bool) = (0x100000000 as u64).narrow_or();
    assert_eq((v, ok), (0, false));
    let m: u128 = 0xffffffffffffffffffffffffffffffff;
    let (v, ok): (u64, bool) = wit(m).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (u64, bool) = (0xffffffffffffffff as u128).narrow_or();
    assert_eq((v, ok), (0xffffffffffffffff, true));
    let (v, ok): (u8, bool) = (0 as u128).narrow_or();
    assert_eq((v, ok), (0, true));
    let (v, ok): (u8, bool) = (0x100 as u64).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (u16, bool) = (0xffff as u128).narrow_or();
    assert_eq((v, ok), (0xffff, true));
    let (v, ok): (u32, bool) = (0x1_0000_0000 as u128).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (u8, bool) = (0xff as u32).narrow_or();
    assert_eq((v, ok), (0xff, true));
    let (v, ok): (u16, bool) = (0x10000 as u64).narrow_or();
    assert_eq((v, ok), (0, false));
}

#[test]
fn narrow_unsigned_runtime_witness() {
    let x = wit(0x1ff as u64);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x1ff, true));
}

#[test]
fn narrow_signed() {
    let (v, ok): (i8, bool) = (-128i16).narrow_or();
    assert_eq((v, ok), (-128, true));
    let (v, ok): (i8, bool) = (-129i16).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (i8, bool) = (127i16).narrow_or();
    assert_eq((v, ok), (127, true));
    let (v, ok): (i8, bool) = (128i16).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (i8, bool) = (-1i32).narrow_or();
    assert_eq((v, ok), (-1, true));
    let (v, ok): (i16, bool) = (-32769i32).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (i16, bool) = (32767i32).narrow_or();
    assert_eq((v, ok), (32767, true));
    let (v, ok): (i32, bool) = (-2147483648i64).narrow_or();
    assert_eq((v, ok), (-2147483648, true));
    let (v, ok): (i32, bool) = (2147483648i64).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (i8, bool) = (0x17fi64).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (i16, bool) = (-5i64).narrow_or();
    assert_eq((v, ok), (-5, true));
}

#[test]
fn narrow_signed_runtime_witness() {
    let x = wit((0xffffffffffffff7f as u64) as i64); // -129
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (i16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (-129, true));
}

#[test]
fn narrow_sign_changes() {
    let (v, ok): (u8, bool) = (-1i8).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (u8, bool) = (127i8).narrow_or();
    assert_eq((v, ok), (127, true));
    let (v, ok): (i8, bool) = (128 as u8).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (i8, bool) = (127 as u8).narrow_or();
    assert_eq((v, ok), (127, true));
    let (v, ok): (u16, bool) = (-32768i16).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (i16, bool) = (0xffff as u16).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (u32, bool) = (2147483647i32).narrow_or();
    assert_eq((v, ok), (2147483647, true));
    let (v, ok): (i32, bool) = (0x80000000 as u32).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (u64, bool) = (-1i64).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (i64, bool) = (0x7fffffffffffffff as u64).narrow_or();
    assert_eq((v, ok), (9223372036854775807, true));
    let (v, ok): (i64, bool) = (0x8000000000000000 as u64).narrow_or();
    assert_eq((v, ok), (0, false));
    let (v, ok): (u8, bool) = (0i8).narrow_or();
    assert_eq((v, ok), (0, true));
}

// ---- cross-width sign changes ----

#[test]
fn narrow_cross_sign_from_i8_runtime_witness() {
    let x = wit((0x7f as u8) as i8);
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7f, true));
    let x = wit((0x80 as u8) as i8);
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xff as u8) as i8);
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u8) as i8);
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit((0x7f as u8) as i8);
    let (v, ok): (u32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7f, true));
    let x = wit((0x80 as u8) as i8);
    let (v, ok): (u32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xff as u8) as i8);
    let (v, ok): (u32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u8) as i8);
    let (v, ok): (u32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit((0x7f as u8) as i8);
    let (v, ok): (u64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7f, true));
    let x = wit((0x80 as u8) as i8);
    let (v, ok): (u64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xff as u8) as i8);
    let (v, ok): (u64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u8) as i8);
    let (v, ok): (u64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit((0x7f as u8) as i8);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7f, true));
    let x = wit((0x80 as u8) as i8);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xff as u8) as i8);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u8) as i8);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
}

#[test]
fn narrow_cross_sign_from_i16_runtime_witness() {
    let x = wit((0xff as u16) as i16);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0xff, true));
    let x = wit((0x100 as u16) as i16);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xffff as u16) as i16);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u16) as i16);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit((0x7fff as u16) as i16);
    let (v, ok): (u32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7fff, true));
    let x = wit((0x8000 as u16) as i16);
    let (v, ok): (u32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xffff as u16) as i16);
    let (v, ok): (u32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u16) as i16);
    let (v, ok): (u32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit((0x7fff as u16) as i16);
    let (v, ok): (u64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7fff, true));
    let x = wit((0x8000 as u16) as i16);
    let (v, ok): (u64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xffff as u16) as i16);
    let (v, ok): (u64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u16) as i16);
    let (v, ok): (u64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit((0x7fff as u16) as i16);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7fff, true));
    let x = wit((0x8000 as u16) as i16);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xffff as u16) as i16);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u16) as i16);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
}

#[test]
fn narrow_cross_sign_from_i32_runtime_witness() {
    let x = wit((0xff as u32) as i32);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0xff, true));
    let x = wit((0x100 as u32) as i32);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xffffffff as u32) as i32);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u32) as i32);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit((0xffff as u32) as i32);
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0xffff, true));
    let x = wit((0x10000 as u32) as i32);
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xffffffff as u32) as i32);
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u32) as i32);
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit((0x7fffffff as u32) as i32);
    let (v, ok): (u64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7fffffff, true));
    let x = wit((0x80000000 as u32) as i32);
    let (v, ok): (u64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xffffffff as u32) as i32);
    let (v, ok): (u64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u32) as i32);
    let (v, ok): (u64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit((0x7fffffff as u32) as i32);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7fffffff, true));
    let x = wit((0x80000000 as u32) as i32);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xffffffff as u32) as i32);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u32) as i32);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
}

#[test]
fn narrow_cross_sign_from_i64_runtime_witness() {
    let x = wit((0xff as u64) as i64);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0xff, true));
    let x = wit((0x100 as u64) as i64);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xffffffffffffffff as u64) as i64);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u64) as i64);
    let (v, ok): (u8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit((0xffff as u64) as i64);
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0xffff, true));
    let x = wit((0x10000 as u64) as i64);
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xffffffffffffffff as u64) as i64);
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u64) as i64);
    let (v, ok): (u16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit((0xffffffff as u64) as i64);
    let (v, ok): (u32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0xffffffff, true));
    let x = wit((0x100000000 as u64) as i64);
    let (v, ok): (u32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xffffffffffffffff as u64) as i64);
    let (v, ok): (u32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u64) as i64);
    let (v, ok): (u32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit((0x7fffffffffffffff as u64) as i64);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7fffffffffffffff, true));
    let x = wit((0x8000000000000000 as u64) as i64);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0xffffffffffffffff as u64) as i64);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit((0 as u64) as i64);
    let (v, ok): (u128, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
}

#[test]
fn narrow_cross_sign_from_u8_runtime_witness() {
    let x = wit(0xff as u8);
    let (v, ok): (i16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0xff, true));
    let x = wit(0 as u8);
    let (v, ok): (i16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit(0xff as u8);
    let (v, ok): (i32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0xff, true));
    let x = wit(0 as u8);
    let (v, ok): (i32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit(0xff as u8);
    let (v, ok): (i64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0xff, true));
    let x = wit(0 as u8);
    let (v, ok): (i64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
}

#[test]
fn narrow_cross_sign_from_u16_runtime_witness() {
    let x = wit(0x7f as u16);
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7f, true));
    let x = wit(0x80 as u16);
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0xffff as u16);
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0xffff as u16);
    let (v, ok): (i32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0xffff, true));
    let x = wit(0 as u16);
    let (v, ok): (i32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
    let x = wit(0xffff as u16);
    let (v, ok): (i64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0xffff, true));
    let x = wit(0 as u16);
    let (v, ok): (i64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
}

#[test]
fn narrow_cross_sign_from_u32_runtime_witness() {
    let x = wit(0x7f as u32);
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7f, true));
    let x = wit(0x80 as u32);
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0xffffffff as u32);
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0x7fff as u32);
    let (v, ok): (i16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7fff, true));
    let x = wit(0x8000 as u32);
    let (v, ok): (i16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0xffffffff as u32);
    let (v, ok): (i16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0xffffffff as u32);
    let (v, ok): (i64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0xffffffff, true));
    let x = wit(0 as u32);
    let (v, ok): (i64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, true));
}

#[test]
fn narrow_cross_sign_from_u64_runtime_witness() {
    let x = wit(0x7f as u64);
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7f, true));
    let x = wit(0x80 as u64);
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0xffffffffffffffff as u64);
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0x7fff as u64);
    let (v, ok): (i16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7fff, true));
    let x = wit(0x8000 as u64);
    let (v, ok): (i16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0xffffffffffffffff as u64);
    let (v, ok): (i16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0x7fffffff as u64);
    let (v, ok): (i32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7fffffff, true));
    let x = wit(0x80000000 as u64);
    let (v, ok): (i32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0xffffffffffffffff as u64);
    let (v, ok): (i32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
}

#[test]
fn narrow_cross_sign_from_u128_runtime_witness() {
    let x = wit(0x7f as u128);
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7f, true));
    let x = wit(0x80 as u128);
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0xffffffffffffffffffffffffffffffff as u128);
    let (v, ok): (i8, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0x7fff as u128);
    let (v, ok): (i16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7fff, true));
    let x = wit(0x8000 as u128);
    let (v, ok): (i16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0xffffffffffffffffffffffffffffffff as u128);
    let (v, ok): (i16, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0x7fffffff as u128);
    let (v, ok): (i32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7fffffff, true));
    let x = wit(0x80000000 as u128);
    let (v, ok): (i32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0xffffffffffffffffffffffffffffffff as u128);
    let (v, ok): (i32, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0x7fffffffffffffff as u128);
    let (v, ok): (i64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0x7fffffffffffffff, true));
    let x = wit(0x8000000000000000 as u128);
    let (v, ok): (i64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
    let x = wit(0xffffffffffffffffffffffffffffffff as u128);
    let (v, ok): (i64, bool) = wit(x).narrow_or();
    assert_eq((v, ok), (0, false));
}

// ---- truncate_or ----

#[test]
fn truncate_small_values() {
    assert_eq(truncate_or::<8>(wit(0)), (0, 0, true));
    assert_eq(truncate_or::<8>(wit(1)), (1, 0, true));
    assert_eq(truncate_or::<8>(wit(255)), (255, 0, true));
    assert_eq(truncate_or::<8>(wit(256)), (0, 1, false));
    assert_eq(truncate_or::<8>(wit(257)), (1, 1, false));
    assert_eq(truncate_or::<1>(wit(3)), (1, 1, false));
    assert_eq(
        truncate_or::<64>(wit(0x123456789abcdef0fedcba9876543210)),
        (0xfedcba9876543210, 0x123456789abcdef0, false),
    );
}

#[test]
fn truncate_limb_boundary() {
    assert_eq(truncate_or::<128>(wit(TWO_POW_128 - 1)), (TWO_POW_128 - 1, 0, true));
    assert_eq(truncate_or::<128>(wit(TWO_POW_128)), (0, 1, false));
    assert_eq(truncate_or::<128>(wit(TWO_POW_128 + 1)), (1, 1, false));
    assert_eq(truncate_or::<127>(wit(TWO_POW_128)), (0, 2, false));
    assert_eq(truncate_or::<8>(wit(TWO_POW_128 + 0x1ff)), (0xff, 0x1 + TWO_POW_128 / 256, false));
}

#[test]
fn truncate_modulus_edge() {
    let (lo, dropped, ok) = truncate_or::<8>(wit(PM1));
    assert(!ok);
    assert_eq(lo + dropped * 256, PM1);
    // p - 1 = ...f0000000: low byte 0
    assert_eq(lo, 0);
    let (lo64, d64, ok64) = truncate_or::<64>(wit(PM1));
    assert(!ok64);
    assert_eq(lo64, 0x43e1f593f0000000);
    assert_eq(lo64 + d64 * 0x10000000000000000, PM1);
    let (lo128, d128, ok128) = truncate_or::<128>(wit(PM1));
    assert(!ok128);
    assert_eq(lo128, PLO - 1);
    assert_eq(d128, PHI);
}

#[test]
fn truncate_matches_native_cast() {
    let x = wit(PM1);
    assert_eq(truncate_or::<8>(wit(x)).0, (x as u8) as Field);
    assert_eq(truncate_or::<16>(wit(x)).0, (x as u16) as Field);
    assert_eq(truncate_or::<32>(wit(x)).0, (x as u32) as Field);
    assert_eq(truncate_or::<64>(wit(x)).0, (x as u64) as Field);
    assert_eq(truncate_or::<128>(wit(x)).0, (x as u128) as Field);
    let y = wit(TWO_POW_128 * 3 + 0xabcdef);
    assert_eq(truncate_or::<8>(wit(y)).0, (y as u8) as Field);
    assert_eq(truncate_or::<16>(wit(y)).0, (y as u16) as Field);
    assert_eq(truncate_or::<64>(wit(y)).0, (y as u64) as Field);
    assert_eq(truncate_or::<128>(wit(y)).0, (y as u128) as Field);
}

// ---- full-width bits and bytes ----

#[test]
fn bits_total_round_trip_edges() {
    let xs = [0, 1, TWO_POW_128 - 1, TWO_POW_128, TWO_POW_128 + 1, PM1, PHI * TWO_POW_128];
    for j in 0..7 {
        let x = xs[j];
        let le = to_le_bits_total(wit(x));
        let be = to_be_bits_total(wit(x));
        for i in 0..254 {
            assert_eq(le[i], be[253 - i]);
        }
        assert_eq(from_le_bits_or(wit(le)), (x, true));
        assert_eq(from_be_bits_or(wit(be)), (x, true));
        // agrees with std's full-width decomposition
        let std_le: [bool; 254] = x.to_le_bits();
        assert_eq(le, std_le);
    }
}

#[test]
fn bits_total_values() {
    let le = to_le_bits_total(wit(5));
    assert(le[0] & !le[1] & le[2]);
    for i in 3..254 {
        assert(!le[i]);
    }
    let top = to_le_bits_total(wit(TWO_POW_128));
    assert(top[128]);
    assert(!top[127]);
}

#[test]
fn bytes_total_round_trip_edges() {
    let xs = [0, 1, 255, 256, TWO_POW_128 - 1, TWO_POW_128, TWO_POW_128 + 1, PM1];
    for j in 0..8 {
        let x = xs[j];
        let le = to_le_bytes_total(wit(x));
        let be = to_be_bytes_total(wit(x));
        for i in 0..32 {
            assert_eq(le[i], be[31 - i]);
        }
        assert_eq(from_le_bytes_or(wit(le)), (x, true));
        assert_eq(from_be_bytes_or(wit(be)), (x, true));
        let std_le: [u8; 32] = x.to_le_bytes();
        assert_eq(le, std_le);
    }
}

#[test]
fn bytes_total_runtime_witness() {
    let x = wit(PM1);
    let le = to_le_bytes_total(wit(x));
    // p ends in byte 0x01, so p - 1 is p's bytes with the low byte 0
    let p = std::field::modulus_le_bytes();
    assert_eq(le[0], p[0] - 1);
    for i in 1..32 {
        assert_eq(le[i], p[i]);
    }
    let bits = to_le_bits_total(wit(x));
    let pb = std::field::modulus_le_bits();
    assert(!bits[0]);
    for i in 1..254 {
        assert_eq(bits[i], pb[i]);
    }
}

// ---- canonical decoding ----

#[test]
fn from_le_bytes_or_rejects_modulus_and_above() {
    let p = std::field::modulus_le_bytes();
    let mut pb = [0; 32];
    for i in 0..32 {
        pb[i] = p[i];
    }
    // p itself
    assert_eq(from_le_bytes_or(wit(pb)), (0, false));
    // p + 1
    let mut p1 = pb;
    p1[0] = p1[0] + 1;
    assert_eq(from_le_bytes_or(wit(p1)), (0, false));
    // all 0xff (2^256 - 1)
    assert_eq(from_le_bytes_or(wit([0xff; 32])), (0, false));
    // p - 1 is canonical
    let mut pm1 = pb;
    pm1[0] = pm1[0] - 1;
    assert_eq(from_le_bytes_or(wit(pm1)), (PM1, true));
    // hi limb equal to PHI with lo = 0 is canonical
    let mut hi_eq = [0; 32];
    for i in 16..32 {
        hi_eq[i] = p[i];
    }
    assert_eq(from_le_bytes_or(wit(hi_eq)), (PHI * TWO_POW_128, true));
    // hi limb PHI + 1 with lo = 0 is not
    let mut hi_gt = hi_eq;
    hi_gt[16] = hi_gt[16] + 1;
    assert_eq(from_le_bytes_or(wit(hi_gt)), (0, false));
    assert_eq(from_le_bytes_or(wit([0; 32])), (0, true));
}

#[test]
fn from_be_bytes_or_rejects_modulus() {
    let p = std::field::modulus_be_bytes();
    let mut pb = [0; 32];
    for i in 0..32 {
        pb[i] = p[i];
    }
    assert_eq(from_be_bytes_or(wit(pb)), (0, false));
    pb[31] = pb[31] - 1;
    assert_eq(from_be_bytes_or(wit(pb)), (PM1, true));
}

#[test]
fn from_le_bits_or_rejects_modulus_and_above() {
    let p = std::field::modulus_le_bits();
    let mut pb = [false; 254];
    for i in 0..254 {
        pb[i] = p[i];
    }
    assert_eq(from_le_bits_or(wit(pb)), (0, false));
    // all ones: 2^254 - 1 >= p
    assert_eq(from_le_bits_or(wit([true; 254])), (0, false));
    // p - 1: p is odd, so clear bit 0
    let mut pm1 = pb;
    pm1[0] = false;
    assert_eq(from_le_bits_or(wit(pm1)), (PM1, true));
    // p + 1 = p with bit 1 set (p's bit 1 is 0 since p = ...01)
    let mut pp1 = pb;
    pp1[1] = true;
    assert_eq(from_le_bits_or(wit(pp1)), (0, false));
    let mut be = [false; 254];
    for i in 0..254 {
        be[i] = pb[253 - i];
    }
    assert_eq(from_be_bits_or(wit(be)), (0, false));
}

#[test]
fn limbs_below_modulus_edges() {
    assert(limbs_below_modulus(wit(0), wit(0)));
    assert(limbs_below_modulus(wit(PLO - 1), wit(PHI)));
    assert(!limbs_below_modulus(wit(PLO), wit(PHI)));
    assert(!limbs_below_modulus(wit(PLO + 1), wit(PHI)));
    assert(limbs_below_modulus(wit(TWO_POW_128 - 1), wit(PHI - 1)));
    assert(!limbs_below_modulus(wit(0), wit(PHI + 1)));
    assert(!limbs_below_modulus(wit(TWO_POW_128 - 1), wit(TWO_POW_128 - 1)));
}

// ---- bounded bits and bytes ----

#[test]
fn to_le_bits_or_bounds() {
    let (b, ok) = to_le_bits_or::<8>(wit(0xa5));
    assert(ok);
    assert_eq(b, [true, false, true, false, false, true, false, true]);
    let (b, ok) = to_le_bits_or::<8>(wit(256));
    assert(!ok);
    assert_eq(b, [false; 8]);
    let (b, ok) = to_le_bits_or::<8>(wit(PM1));
    assert(!ok);
    assert_eq(b, [false; 8]);
    let (b, ok) = to_be_bits_or::<4>(wit(0x8));
    assert(ok);
    assert_eq(b, [true, false, false, false]);
    let (b, ok) = to_be_bits_or::<4>(wit(0x10));
    assert(!ok);
    assert_eq(b, [false; 4]);
    let (b, ok) = to_le_bits_or::<128>(wit(TWO_POW_128 - 1));
    assert(ok);
    assert_eq(b, [true; 128]);
    let (b, ok) = to_le_bits_or::<128>(wit(TWO_POW_128));
    assert(!ok);
    assert_eq(b, [false; 128]);
    let (b, ok) = to_le_bits_or::<1>(wit(1));
    assert(ok & b[0]);
}

#[test]
fn to_le_bytes_or_bounds() {
    let (b, ok) = to_le_bytes_or::<2>(wit(0x1234));
    assert(ok);
    assert_eq(b, [0x34, 0x12]);
    let (b, ok) = to_be_bytes_or::<2>(wit(0x1234));
    assert(ok);
    assert_eq(b, [0x12, 0x34]);
    let (b, ok) = to_le_bytes_or::<2>(wit(0x10000));
    assert(!ok);
    assert_eq(b, [0, 0]);
    let (b, ok) = to_be_bytes_or::<2>(wit(PM1));
    assert(!ok);
    assert_eq(b, [0, 0]);
    let (b, ok) = to_le_bytes_or::<16>(wit(TWO_POW_128 - 1));
    assert(ok);
    assert_eq(b, [0xff; 16]);
    let (b, ok) = to_le_bytes_or::<16>(wit(TWO_POW_128));
    assert(!ok);
    assert_eq(b, [0; 16]);
}

// ---- widths 129..=253 ----

// truncate_or::<N> on the witnesses 0, 2^N - 1, 2^N and p - 1. For p - 1
// the parts are pinned by their ranges and the reconstruction: lo < 2^N,
// dropped < 2^(254 - N), and lo + dropped * 2^N < 2^254 < 2p.
fn check_truncate_wide<let N: u32>() {
    let t = two_pow::<N>();
    let (lo, d, ok) = truncate_or::<N>(wit(0));
    assert_eq((lo, d, ok), (0, 0, true));
    let (lo, d, ok) = truncate_or::<N>(wit(t - 1));
    assert_eq((lo, d, ok), (t - 1, 0, true));
    let (lo, d, ok) = truncate_or::<N>(wit(t));
    assert_eq((lo, d, ok), (0, 1, false));
    let (lo, d, ok) = truncate_or::<N>(wit(PM1));
    assert(!ok);
    assert(fits_bits::<N>(wit(lo)));
    assert(fits_bits::<254 - N>(wit(d)));
    assert_eq(lo + d * t, PM1);
}

#[test]
fn truncate_wide_widths() {
    check_truncate_wide::<129>();
    check_truncate_wide::<160>();
    check_truncate_wide::<248>();
    check_truncate_wide::<253>();
    // p - 1 is between 2^253 and 2^254: one dropped bit at N = 253
    let (_, d, ok) = truncate_or::<253>(wit(PM1));
    assert_eq((d, ok), (1, false));
    assert_eq(truncate_or::<129>(wit(TWO_POW_128 * 3 + 5)), (TWO_POW_128 + 5, 1, false));
}

// to_le_bits_or / to_be_bits_or::<N> on the witnesses 0, 2^N - 1, 2^N,
// p - 1 and 2^(N - 1) + 5.
fn check_bits_wide<let N: u32>() {
    let t = two_pow::<N>();
    let (b, ok) = to_le_bits_or::<N>(wit(0));
    assert(ok);
    assert_eq(b, [false; N]);
    let (b, ok) = to_le_bits_or::<N>(wit(t - 1));
    assert(ok);
    assert_eq(b, [true; N]);
    let (b, ok) = to_be_bits_or::<N>(wit(t - 1));
    assert(ok);
    assert_eq(b, [true; N]);
    let (b, ok) = to_le_bits_or::<N>(wit(t));
    assert(!ok);
    assert_eq(b, [false; N]);
    let (b, ok) = to_be_bits_or::<N>(wit(PM1));
    assert(!ok);
    assert_eq(b, [false; N]);
    let x = wit(two_pow::<N - 1>() + 5);
    let (le, ok) = to_le_bits_or::<N>(wit(x));
    let (be, ok2) = to_be_bits_or::<N>(wit(x));
    assert(ok & ok2);
    for i in 0..N {
        let expect = (i == 0) | (i == 2) | (i == N - 1);
        assert_eq(le[i], expect);
        assert_eq(be[N - 1 - i], expect);
    }
}

#[test]
fn bits_or_wide_widths() {
    check_bits_wide::<129>();
    check_bits_wide::<160>();
    check_bits_wide::<248>();
    check_bits_wide::<253>();
}

// to_le_bytes_or / to_be_bytes_or::<N> on 0, 2^(8N) - 1, 2^(8N), p - 1
// and a two-byte pattern at the ends.
fn check_bytes_wide<let N: u32>() {
    let t = two_pow::<8 * N>();
    let (b, ok) = to_le_bytes_or::<N>(wit(0));
    assert(ok);
    assert_eq(b, [0; N]);
    let (b, ok) = to_be_bytes_or::<N>(wit(t - 1));
    assert(ok);
    assert_eq(b, [0xff; N]);
    let (b, ok) = to_le_bytes_or::<N>(wit(t));
    assert(!ok);
    assert_eq(b, [0; N]);
    let (b, ok) = to_le_bytes_or::<N>(wit(PM1));
    assert(!ok);
    assert_eq(b, [0; N]);
    let x = wit(0xab * two_pow::<8 * N - 8>() + 0xcd);
    let (le, ok) = to_le_bytes_or::<N>(wit(x));
    let (be, ok2) = to_be_bytes_or::<N>(wit(x));
    assert(ok & ok2);
    assert_eq((le[0], le[N - 1]), (0xcd, 0xab));
    assert_eq((be[0], be[N - 1]), (0xab, 0xcd));
}

#[test]
fn bytes_or_wide_widths() {
    check_bytes_wide::<17>();
    check_bytes_wide::<20>();
    check_bytes_wide::<31>();
}

// ---- sgn0 ----

#[test]
fn sgn0_cases() {
    assert(!sgn0(wit(0)));
    assert(sgn0(wit(1)));
    assert(!sgn0(wit(2)));
    // p is odd: p - 1 is even, p - 2 odd
    assert(!sgn0(wit(PM1)));
    assert(sgn0(wit(PM1 - 1)));
    assert(!sgn0(wit(TWO_POW_128)));
    assert(sgn0(wit(TWO_POW_128 + 1)));
    assert(sgn0(wit(TWO_POW_128 - 1)));
}

#[test]
fn sgn0_runtime_witness() {
    let x = wit(PM1);
    let y = wit(TWO_POW_128 * 7 + 3);
    assert(!sgn0(wit(x)));
    assert(sgn0(wit(x - 1)));
    assert(sgn0(wit(y)));
    // x and -x have opposite parities for x != 0
    assert(sgn0(wit(y)) != sgn0(wit(0 - y)));
    assert_eq(sgn0(wit(y)), to_le_bits_total(wit(y))[0]);
}

// ---- bool ----

#[test]
fn bool_or_cases() {
    assert_eq(bool_or(wit(0)), (false, true));
    assert_eq(bool_or(wit(1)), (true, true));
    assert_eq(bool_or(wit(2)), (false, false));
    assert_eq(bool_or(wit(PM1)), (false, false));
    assert_eq(bool_or(wit(TWO_POW_128)), (false, false));
    assert_eq(bool_or(wit(TWO_POW_128 + 1)), (false, false));
}
