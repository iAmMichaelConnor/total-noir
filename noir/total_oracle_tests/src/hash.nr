//! The hash entries against Node's crypto (SHA-256), @noble/hashes
//! (Keccak-256) and Barretenberg's native Poseidon2 through bb.js.
//!
//! The fuzzer supplies the message; the server picks the length from a seed:
//! 0, the capacity, capacity + 1, the block boundaries (55, 56, 63, 64, 119,
//! 120, 127, 128 for SHA-256; 135, 136, 137 for Keccak-256; 3, 4, 6, 7 for
//! the Poseidon2 rate), random lengths in range, 2^32 + a length in range
//! (in range after truncation to u32), 2^32 - 1, 2^64 + l, 2^128 + l, the
//! Field negatives -1 .. -(capacity + 1), random u32 values above the
//! capacity and random Fields. Expected: ok = (len <= capacity), and the
//! digest of the first len elements, or the zero value when not ok.

use total::hash::{
    keccak256_var_or, p2_hash, p2_hash_sep, p2_hash_sep_var_or, p2_hash_var_or, sha256_var_or,
};

/// Byte capacity: spans three SHA-256 blocks and two Keccak-256 blocks.
global N: u32 = 140;
/// Field capacity of the Poseidon2 tests: two full rate-3 blocks and one more.
global M: u32 = 7;

#[oracle(len_case)]
unconstrained fn len_case_oracle(seed: Field, capacity: u32) -> Field {}

unconstrained fn len_case(seed: Field, capacity: u32) -> Field {
    len_case_oracle(seed, capacity)
}

#[oracle(sha256_ref)]
unconstrained fn sha256_ref_oracle(input: [u8; N], len: Field) -> ([u8; 32], bool) {}

unconstrained fn sha256_ref(input: [u8; N], len: Field) -> ([u8; 32], bool) {
    sha256_ref_oracle(input, len)
}

#[oracle(keccak256_ref)]
unconstrained fn keccak256_ref_oracle(input: [u8; N], len: Field) -> ([u8; 32], bool) {}

unconstrained fn keccak256_ref(input: [u8; N], len: Field) -> ([u8; 32], bool) {
    keccak256_ref_oracle(input, len)
}

#[oracle(poseidon2_ref)]
unconstrained fn poseidon2_ref_oracle<let K: u32>(
    input: [Field; K],
    len: Field,
    sep: Field,
    has_sep: bool,
) -> (Field, bool) {}

/// Poseidon2 of [sep] (when has_sep) followed by input[0..len], and
/// ok = (len <= K); (0, false) when not ok.
unconstrained fn poseidon2_ref<let K: u32>(
    input: [Field; K],
    len: Field,
    sep: Field,
    has_sep: bool,
) -> (Field, bool) {
    poseidon2_ref_oracle(input, len, sep, has_sep)
}

fn prefix<let K: u32>(input: [Field; M]) -> [Field; K] {
    let mut out = [0; K];
    for i in 0..K {
        out[i] = input[i];
    }
    out
}

/// p2_hash and p2_hash_sep on the first K elements.
fn check_fixed<let K: u32>(input: [Field; M], sep: Field) {
    let xs: [Field; K] = prefix(input);
    // Safety: the oracle only supplies the expected digests.
    let (plain, _) = unsafe { poseidon2_ref(xs, K as Field, 0, false) };
    // Safety: as above.
    let (separated, _) = unsafe { poseidon2_ref(xs, K as Field, sep, true) };
    assert_eq(p2_hash(xs), plain);
    assert_eq(p2_hash_sep(xs, sep), separated);
}

#[test]
fn sha256_var_or_matches_reference(input: [u8; N], seed: Field) {
    // Safety: the oracle only supplies the length and the expected answer.
    let len = unsafe { len_case(seed, N) };
    // Safety: as above.
    let expected = unsafe { sha256_ref(input, len) };
    assert_eq(sha256_var_or(input, len), expected);
}

#[test]
fn keccak256_var_or_matches_reference(input: [u8; N], seed: Field) {
    // Safety: the oracle only supplies the length and the expected answer.
    let len = unsafe { len_case(seed, N) };
    // Safety: as above.
    let expected = unsafe { keccak256_ref(input, len) };
    assert_eq(keccak256_var_or(input, len), expected);
}

// Every fixed length from 0 to M, with and without a separator.
#[test]
fn p2_hash_matches_reference(input: [Field; M], sep: Field) {
    check_fixed::<0>(input, sep);
    check_fixed::<1>(input, sep);
    check_fixed::<2>(input, sep);
    check_fixed::<3>(input, sep);
    check_fixed::<4>(input, sep);
    check_fixed::<5>(input, sep);
    check_fixed::<6>(input, sep);
    check_fixed::<7>(input, sep);
}

#[test]
fn p2_hash_var_or_matches_reference(input: [Field; M], seed: Field) {
    // Safety: the oracle only supplies the length and the expected answer.
    let len = unsafe { len_case(seed, M) };
    // Safety: as above.
    let expected = unsafe { poseidon2_ref(input, len, 0, false) };
    assert_eq(p2_hash_var_or(input, len), expected);
}

#[test]
fn p2_hash_sep_var_or_matches_reference(input: [Field; M], sep: Field, seed: Field) {
    // Safety: the oracle only supplies the length and the expected answer.
    let len = unsafe { len_case(seed, M) };
    // Safety: as above.
    let expected = unsafe { poseidon2_ref(input, len, sep, true) };
    assert_eq(p2_hash_sep_var_or(input, len, sep), expected);
}
