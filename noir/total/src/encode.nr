//! Byte encodings: canonicity flags, byte order and 31-byte field
//! packing, total for every input.
//!
//! Already in convert.nr and not repeated here: the canonical decoders
//! from_le_bytes_or / from_be_bytes_or / from_le_bits_or / from_be_bits_or
//! (value and canonical-encoding flag), the full-width decompositions
//! to_le_bytes_total / to_be_bytes_total / to_le_bits_total /
//! to_be_bits_total, and the bounded to_le_bytes_or::<N> / to_be_bytes_or
//! for N <= 31. This module adds the canonicity flags as standalone
//! predicates, byte-order helpers for native integers, packing of bytes
//! into 31-byte Field chunks and back.
//!
//! std and Aztec status for the operations here:
//! - Field::from_le_bytes::<N> / from_be_bytes::<N>: total and exact for
//!   N <= 31 (arithmetic only, 256^31 < p). Used directly.
//! - Field::to_le_bytes::<N> / to_be_bytes::<N> for N < 32: input-
//!   falsifiable for x >= 2^(8N); total when the caller's value is below
//!   2^(8N) by a type invariant or an earlier constraint. This module
//!   calls them only on such values.
//! - aztec-nr utils/conversion/bytes_as_fields.nr: encode_bytes_as_fields
//!   is total (arithmetic); decode_bytes_from_fields calls
//!   to_be_bytes::<31> and is input-falsifiable for a Field >= 2^248.
//!   bytes_to_fields_be matches the former exactly; fields_to_bytes_be_or
//!   is the flagged form of the latter.
//!
//! Packing conventions, both with 31-byte chunks so every chunk is below
//! 2^248 < p and the packing is exact:
//! - bytes_to_fields_be: chunk i is the big-endian integer of bytes
//!   31i .. 31i + 30. This is aztec-nr's encode_bytes_as_fields; like it,
//!   it requires the length to be a multiple of 31.
//! - bytes_to_fields_le: chunk i is the little-endian integer of the same
//!   bytes, and a short final chunk is allowed (equal to zero-padding the
//!   input at the end). This is the packing schnorr v0.4.0 documents for
//!   its challenge domain separator (SCHNORR_CHALLENGE_DST, "little-endian
//!   into 31-byte chunks"); the test le_packing_matches_schnorr_dst
//!   reproduces that constant with hash::p2_hash.
//!
//! Gadgets used: core::eq / is_zero (the inversion gadget), convert's
//! canonical decoders and to_le_bytes_total, and convert's exact casts (a
//! range check at the width, then `as`, used only on values already
//! below the width). All are hint-satisfiable for every input under the
//! preconditions stated at the call sites, and every flag built from them
//! is determined. This module adds no hints of its own. A select between
//! two u8 values (ctl's Select for u8, `if c { t } else { f }`) lowers to
//! one arithmetic definition with no range check.
//!
//! On ok = false every entry here returns all zero bytes.
//!
//! Length-bounded byte strings are BoundedVec<u8, MAX> with the flagged
//! operations of collections::bounded_vec (from_prefix_or for an array and
//! an untrusted length, get_or, push_or, extend_from_array_or,
//! extend_from_bounded_vec_or, set_len_or); std's Eq on BoundedVec compares
//! the lengths and the bytes below the length, and is reflexive. A str<N>
//! converts with s.as_bytes().
//!
//! Not provided:
//! - Hashing a byte string: pack with bytes_to_fields_le and use
//!   hash::p2_hash_var_or with the chunk count; the convention for the
//!   length (bytes or chunks) is the caller's choice, so no wrapper fixes
//!   one.
//! - Hex, base64, RLP and ABI encodings.

use crate::convert::{
    cast_u128, cast_u16, cast_u32, cast_u64, from_be_bits_or, from_be_bytes_or, from_le_bits_or,
    from_le_bytes_or, to_le_bytes_total,
};
use crate::ctl::Select;
use std::static_assert;

// ---------------------------------------------------------------------
// Canonicity flags
// ---------------------------------------------------------------------

/// Flag: the 32 little-endian bytes encode an integer below p. The flag
/// half of convert::from_le_bytes_or, with the same constraints (two
/// limb sums, a limb compare against the modulus built from lt_bounded and an
/// eq gadget). Hint-satisfiable for every input; determined.
pub fn canonical_le_bytes_flag(bytes: [u8; 32]) -> bool {
    from_le_bytes_or(bytes).1
}

/// Flag: the 32 big-endian bytes encode an integer below p. Same
/// constraints as canonical_le_bytes_flag.
pub fn canonical_be_bytes_flag(bytes: [u8; 32]) -> bool {
    from_be_bytes_or(bytes).1
}

/// Flag: the 254 little-endian bits encode an integer below p. The flag
/// half of convert::from_le_bits_or; hint-satisfiable for every input;
/// determined.
pub fn canonical_le_bits_flag(bits: [bool; 254]) -> bool {
    from_le_bits_or(bits).1
}

/// Flag: the 254 big-endian bits encode an integer below p. Same
/// constraints as canonical_le_bits_flag.
pub fn canonical_be_bits_flag(bits: [bool; 254]) -> bool {
    from_be_bits_or(bits).1
}

// ---------------------------------------------------------------------
// Byte order
// ---------------------------------------------------------------------

/// The array in reverse order: converts between little- and big-endian
/// byte (or bit) orders. Constant indices only: no constraints.
pub fn reverse<T, let N: u32>(arr: [T; N]) -> [T; N] {
    let mut out = arr;
    for i in 0..N {
        out[i] = arr[N - 1 - i];
    }
    out
}

/// reverse for the common 32-byte case. No constraints.
pub fn reverse32(arr: [u8; 32]) -> [u8; 32] {
    reverse(arr)
}

// Native integers to and from bytes. The to_* forms call std
// to_be_bytes::<N> / to_le_bytes::<N> on x as Field: the builtin radix-256
// decomposition (hinted bytes, 8-bit RANGEs, the reconstruction), with
// std's canonicity loop compiled out for N < 32. x is below 2^(8N) by its
// type invariant, so the decomposition exists and is unique:
// hint-satisfiable, determined. The from_* forms sum the bytes (exact,
// below 2^(8N)) and convert the sum with convert's exact cast (a RANGE
// at the width, then `as`), which holds for every witness because the sum
// is below 2^(8N); determined.

/// x as 2 big-endian bytes. See the note above for constraints.
pub fn u16_to_be_bytes(x: u16) -> [u8; 2] {
    (x as Field).to_be_bytes()
}

/// x as 2 little-endian bytes.
pub fn u16_to_le_bytes(x: u16) -> [u8; 2] {
    (x as Field).to_le_bytes()
}

/// The u16 encoded by 2 big-endian bytes.
pub fn u16_from_be_bytes(b: [u8; 2]) -> u16 {
    cast_u16(Field::from_be_bytes(b))
}

/// The u16 encoded by 2 little-endian bytes.
pub fn u16_from_le_bytes(b: [u8; 2]) -> u16 {
    cast_u16(Field::from_le_bytes(b))
}

/// x as 4 big-endian bytes.
pub fn u32_to_be_bytes(x: u32) -> [u8; 4] {
    (x as Field).to_be_bytes()
}

/// x as 4 little-endian bytes.
pub fn u32_to_le_bytes(x: u32) -> [u8; 4] {
    (x as Field).to_le_bytes()
}

/// The u32 encoded by 4 big-endian bytes.
pub fn u32_from_be_bytes(b: [u8; 4]) -> u32 {
    cast_u32(Field::from_be_bytes(b))
}

/// The u32 encoded by 4 little-endian bytes.
pub fn u32_from_le_bytes(b: [u8; 4]) -> u32 {
    cast_u32(Field::from_le_bytes(b))
}

/// x as 8 big-endian bytes.
pub fn u64_to_be_bytes(x: u64) -> [u8; 8] {
    (x as Field).to_be_bytes()
}

/// x as 8 little-endian bytes.
pub fn u64_to_le_bytes(x: u64) -> [u8; 8] {
    (x as Field).to_le_bytes()
}

/// The u64 encoded by 8 big-endian bytes.
pub fn u64_from_be_bytes(b: [u8; 8]) -> u64 {
    cast_u64(Field::from_be_bytes(b))
}

/// The u64 encoded by 8 little-endian bytes.
pub fn u64_from_le_bytes(b: [u8; 8]) -> u64 {
    cast_u64(Field::from_le_bytes(b))
}

/// x as 16 big-endian bytes.
pub fn u128_to_be_bytes(x: u128) -> [u8; 16] {
    (x as Field).to_be_bytes()
}

/// x as 16 little-endian bytes.
pub fn u128_to_le_bytes(x: u128) -> [u8; 16] {
    (x as Field).to_le_bytes()
}

/// The u128 encoded by 16 big-endian bytes.
pub fn u128_from_be_bytes(b: [u8; 16]) -> u128 {
    cast_u128(Field::from_be_bytes(b))
}

/// The u128 encoded by 16 little-endian bytes.
pub fn u128_from_le_bytes(b: [u8; 16]) -> u128 {
    cast_u128(Field::from_le_bytes(b))
}

// ---------------------------------------------------------------------
// 31-byte Field packing
// ---------------------------------------------------------------------

/// Pack bytes into Fields, 31 bytes per Field, each chunk read as a
/// big-endian integer; N must be a multiple of 31 (compile-time check).
/// Equal to aztec-nr's encode_bytes_as_fields. Arithmetic definitions
/// only, no failure source; each chunk is below 2^248, so the packing is
/// exact and injective.
pub fn bytes_to_fields_be<let N: u32>(bytes: [u8; N]) -> [Field; N / 31] {
    static_assert(
        N % 31 == 0,
        "bytes_to_fields_be: N must be a multiple of 31",
    );
    let mut out = [0; N / 31];
    for i in 0..N / 31 {
        let mut acc: Field = 0;
        for j in 0..31 {
            acc = acc * 256 + bytes[31 * i + j] as Field;
        }
        out[i] = acc;
    }
    out
}

/// Pack bytes into Fields, 31 bytes per Field, each chunk read as a
/// little-endian integer; any N. The last chunk holds the remaining
/// N mod 31 bytes, which equals packing the input zero-padded at the end.
/// Arithmetic definitions only, no failure source; exact (each chunk is
/// below 2^248).
pub fn bytes_to_fields_le<let N: u32>(bytes: [u8; N]) -> [Field; (N + 30) / 31] {
    let mut out = [0; (N + 30) / 31];
    for i in 0..(N + 30) / 31 {
        let mut acc: Field = 0;
        let mut pw: Field = 1;
        for j in 0..31 {
            if 31 * i + j < N {
                acc = acc + (bytes[31 * i + j] as Field) * pw;
                pw = pw * 256;
            }
        }
        out[i] = acc;
    }
    out
}

/// The 31 little-endian bytes of x when x < 2^248, else 31 zero bytes;
/// ok = (x < 2^248).
///
/// Constraints: convert::to_le_bytes_total (canonical limbs and their
/// byte decompositions, hint-satisfiable for every Field), the eq gadget
/// on the top byte, and 31 u8 selects (arithmetic). The canonical bytes
/// are unique, so the top byte and ok are determined.
pub fn chunk_to_le_bytes_or(x: Field) -> ([u8; 31], bool) {
    let le = to_le_bytes_total(x);
    let ok = le[31] == 0;
    let mut out = [0; 31];
    for j in 0..31 {
        out[j] = if ok { le[j] } else { 0 };
    }
    (out, ok)
}

/// Big-endian form of chunk_to_le_bytes_or (out[0] is the most
/// significant byte). Same constraints.
pub fn chunk_to_be_bytes_or(x: Field) -> ([u8; 31], bool) {
    let (le, ok) = chunk_to_le_bytes_or(x);
    (reverse(le), ok)
}

/// Inverse of bytes_to_fields_be: each Field as 31 big-endian bytes.
/// ok = every Field is below 2^248; on ok = false every byte is 0. The
/// flagged form of aztec-nr's decode_bytes_from_fields, which fails the
/// proof instead. Constraints: chunk_to_be_bytes_or per Field, an AND of
/// the flags, and 31N u8 selects. Hint-satisfiable for every input;
/// determined.
pub fn fields_to_bytes_be_or<let N: u32>(fields: [Field; N]) -> ([u8; 31 * N], bool) {
    let mut out = [0; 31 * N];
    let mut ok = true;
    for i in 0..N {
        let (chunk, c_ok) = chunk_to_be_bytes_or(fields[i]);
        for j in 0..31 {
            out[31 * i + j] = chunk[j];
        }
        ok = ok & c_ok;
    }
    (Select::select(ok, out, [0; 31 * N]), ok)
}

/// Inverse of bytes_to_fields_le for lengths that are a multiple of 31:
/// each Field as 31 little-endian bytes, with the same flag and zeroing
/// rule as fields_to_bytes_be_or. Same constraints.
pub fn fields_to_bytes_le_or<let N: u32>(fields: [Field; N]) -> ([u8; 31 * N], bool) {
    let mut out = [0; 31 * N];
    let mut ok = true;
    for i in 0..N {
        let (chunk, c_ok) = chunk_to_le_bytes_or(fields[i]);
        for j in 0..31 {
            out[31 * i + j] = chunk[j];
        }
        ok = ok & c_ok;
    }
    (Select::select(ok, out, [0; 31 * N]), ok)
}

mod tests {
    use crate::convert::{to_be_bits_total, to_be_bytes_total, to_le_bits_total, to_le_bytes_total};
    use crate::core::{two_pow, TWO_POW_128};
    use crate::hash::p2_hash;
    use super::{
        bytes_to_fields_be, bytes_to_fields_le, canonical_be_bits_flag, canonical_be_bytes_flag,
        canonical_le_bits_flag, canonical_le_bytes_flag, chunk_to_be_bytes_or, chunk_to_le_bytes_or,
        fields_to_bytes_be_or, fields_to_bytes_le_or, reverse, reverse32, u128_from_be_bytes,
        u128_from_le_bytes, u128_to_be_bytes, u128_to_le_bytes, u16_from_be_bytes,
        u16_from_le_bytes, u16_to_be_bytes, u16_to_le_bytes, u32_from_be_bytes, u32_from_le_bytes,
        u32_to_be_bytes, u32_to_le_bytes, u64_from_be_bytes, u64_from_le_bytes, u64_to_be_bytes,
        u64_to_le_bytes,
    };

    global P_MINUS_1: Field = 0 - 1;

    fn modulus_le() -> [u8; 32] {
        let m = std::field::modulus_le_bytes();
        let mut out = [0; 32];
        for i in 0..32 {
            out[i] = m[i];
        }
        out
    }

    #[test]
    fn canonical_bytes_flags() {
        assert(canonical_le_bytes_flag([0; 32]));
        assert(canonical_le_bytes_flag(to_le_bytes_total(P_MINUS_1)));
        assert(canonical_be_bytes_flag(to_be_bytes_total(P_MINUS_1)));
        let p = modulus_le();
        assert(!canonical_le_bytes_flag(p));
        assert(!canonical_be_bytes_flag(reverse32(p)));
        assert(!canonical_le_bytes_flag([0xff; 32]));
        // p + 1 is not canonical either
        let mut p1 = p;
        p1[0] = p1[0] + 1;
        assert(!canonical_le_bytes_flag(p1));
    }

    #[test]
    fn canonical_bits_flags() {
        assert(canonical_le_bits_flag([false; 254]));
        assert(canonical_le_bits_flag(to_le_bits_total(P_MINUS_1)));
        assert(canonical_be_bits_flag(to_be_bits_total(P_MINUS_1)));
        assert(!canonical_le_bits_flag([true; 254]));
        // p itself: bits of p - 1 with bit 0 set (p - 1 is even)
        let mut pb = to_le_bits_total(P_MINUS_1);
        assert(!pb[0]);
        pb[0] = true;
        assert(!canonical_le_bits_flag(pb));
        assert(!canonical_be_bits_flag(reverse(pb)));
    }

    #[test]
    fn reverse_cases() {
        assert_eq(reverse([1, 2, 3]), [3, 2, 1]);
        let x = 0x123456789abcdef0123456789abcdef0123456789abcdef;
        assert_eq(reverse32(to_le_bytes_total(x)), to_be_bytes_total(x));
        assert_eq(reverse32(reverse32(to_le_bytes_total(x))), to_le_bytes_total(x));
        let e: [u8; 0] = [];
        assert_eq(reverse(e), e);
    }

    #[test]
    fn native_byte_order() {
        assert_eq(u16_to_be_bytes(0x0102), [1, 2]);
        assert_eq(u16_to_le_bytes(0x0102), [2, 1]);
        assert_eq(u16_from_be_bytes([0xff, 0xff]), 0xffff);
        assert_eq(u16_from_le_bytes([0, 0]), 0);
        assert_eq(u32_to_be_bytes(0x01020304), [1, 2, 3, 4]);
        assert_eq(u32_to_le_bytes(0x01020304), [4, 3, 2, 1]);
        assert_eq(u32_from_be_bytes([1, 2, 3, 4]), 0x01020304);
        assert_eq(u32_from_le_bytes([4, 3, 2, 1]), 0x01020304);
        assert_eq(u32_from_be_bytes([0xff; 4]), 0xffffffff);
        assert_eq(u64_to_be_bytes(0xffffffffffffffff), [0xff; 8]);
        assert_eq(u64_to_le_bytes(1), [1, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq(u64_from_be_bytes([0, 0, 0, 0, 0, 0, 1, 0]), 256);
        assert_eq(u64_from_le_bytes(u64_to_le_bytes(0x0123456789abcdef)), 0x0123456789abcdef);
        let m: u128 = 0xffffffffffffffffffffffffffffffff;
        assert_eq(u128_to_be_bytes(m), [0xff; 16]);
        assert_eq(u128_from_be_bytes([0xff; 16]), m);
        assert_eq(u128_from_le_bytes(u128_to_le_bytes(0x0102)), 0x0102);
        assert_eq(u128_to_be_bytes(0)[15], 0);
        assert_eq(u128_to_be_bytes(1)[15], 1);
        assert_eq(u128_to_le_bytes(1)[0], 1);
    }

    #[test]
    fn be_packing_matches_aztec_example() {
        // aztec-nr's documented example: [1, 10, 3, ..., 0] (31 bytes) is
        // 1 * 256^30 + 10 * 256^29 + 3 * 256^28.
        let mut b = [0; 62];
        b[0] = 1;
        b[1] = 10;
        b[2] = 3;
        b[61] = 7;
        let f = bytes_to_fields_be(b);
        assert_eq(f[0], two_pow::<240>() + 10 * two_pow::<232>() + 3 * two_pow::<224>());
        assert_eq(f[1], 7);
        let ff = bytes_to_fields_be([0xff; 31]);
        assert_eq(ff[0], two_pow::<248>() - 1);
    }

    #[test]
    fn le_packing_matches_schnorr_dst() {
        let src = "schnorr_grumpkin_poseidon2".as_bytes();
        let packed = bytes_to_fields_le(src);
        assert_eq(packed.len(), 1);
        assert_eq(
            p2_hash(packed),
            0x024c76938ed06b8ec1d9094b1013d190baa4011372f0604643bda812a63b832e,
        );
    }

    #[test]
    fn le_packing_partial_chunk() {
        let mut b = [0; 33];
        b[0] = 1;
        b[30] = 2;
        b[31] = 3;
        b[32] = 4;
        let f = bytes_to_fields_le(b);
        assert_eq(f.len(), 2);
        assert_eq(f[0], 1 + 2 * two_pow::<240>());
        assert_eq(f[1], 3 + 4 * 256);
        let e: [u8; 0] = [];
        assert_eq(bytes_to_fields_le(e).len(), 0);
    }

    #[test]
    fn chunk_bytes_boundaries() {
        let (b, ok) = chunk_to_le_bytes_or(two_pow::<248>() - 1);
        assert(ok);
        assert_eq(b, [0xff; 31]);
        let (b0, ok0) = chunk_to_be_bytes_or(0);
        assert(ok0);
        assert_eq(b0, [0; 31]);
        let (b1, ok1) = chunk_to_be_bytes_or(1);
        assert(ok1);
        assert_eq(b1[30], 1);
        assert_eq(b1[0], 0);
        let (bt, okt) = chunk_to_le_bytes_or(TWO_POW_128);
        assert(okt);
        assert_eq(bt[16], 1);
    }

    #[test]
    fn chunk_bytes_adversarial() {
        let (b, ok) = chunk_to_le_bytes_or(two_pow::<248>());
        assert(!ok);
        assert_eq(b, [0; 31]);
        let (b2, ok2) = chunk_to_be_bytes_or(two_pow::<248>() + 1);
        assert(!ok2);
        assert_eq(b2, [0; 31]);
        let (b3, ok3) = chunk_to_be_bytes_or(P_MINUS_1);
        assert(!ok3);
        assert_eq(b3, [0; 31]);
    }

    #[test]
    fn fields_bytes_round_trip() {
        let mut b = [0; 62];
        for i in 0..62 {
            b[i] = (i * 4 + 1) as u8;
        }
        let (back, ok) = fields_to_bytes_be_or(bytes_to_fields_be(b));
        assert(ok);
        assert_eq(back, b);
        let (back_le, ok_le) = fields_to_bytes_le_or(bytes_to_fields_le(b));
        assert(ok_le);
        assert_eq(back_le, b);
    }

    #[test]
    fn fields_bytes_adversarial() {
        // one chunk too wide: ok = false and every byte zeroed
        let (out, ok) = fields_to_bytes_be_or([two_pow::<248>(), 0x0102]);
        assert(!ok);
        assert_eq(out, [0; 62]);
        let (out1, ok1) = fields_to_bytes_le_or([0x0102, P_MINUS_1]);
        assert(!ok1);
        assert_eq(out1, [0; 62]);
        let (oute, oke) = fields_to_bytes_be_or([]);
        assert(oke);
        assert_eq(oute, []);
        let (out2, ok2) = fields_to_bytes_le_or([P_MINUS_1]);
        assert(!ok2);
        assert_eq(out2, [0; 31]);
    }
}
