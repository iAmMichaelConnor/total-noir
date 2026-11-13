//! The Merkle entries against a TypeScript tree hashed with Barretenberg's
//! Poseidon2 (node = Poseidon2([sep, left, right]), path[i] the sibling at
//! height i, index bits little-endian).
//!
//! Seeded cases: a random tree of 32 leaves (some leaves small values) with
//! Aztec's separator, a random u32 separator, a random Field or 0, and one
//! leaf's index and path, unchanged or with a wrong leaf, another index in
//! range, an index out of range (32, 32 + i, 2^32 + i, 2^128 + i, p - 1,
//! p - 32 + i, a random Field; some with root 0 claimed), a replaced path
//! element, the two lowest siblings swapped, or a wrong root. The raw test
//! takes every input from the fuzzer. Expected: ok = (index < 32); the root
//! the path implies, or 0 when not ok; membership = ok and root matches.

use total::merkle::{
    is_member, is_member_sep, MERKLE_HASH_SEPARATOR, merkle_root_or, merkle_root_sep_or,
};

global D: u32 = 5;

#[oracle(merkle_case)]
unconstrained fn merkle_case_oracle(seed: Field) -> (Field, Field, [Field; D], Field, Field) {}

/// (leaf, index, path, root, sep).
unconstrained fn merkle_case(seed: Field) -> (Field, Field, [Field; D], Field, Field) {
    merkle_case_oracle(seed)
}

#[oracle(merkle_ref)]
unconstrained fn merkle_ref_oracle(
    leaf: Field,
    index: Field,
    path: [Field; D],
    root: Field,
    sep: Field,
) -> (Field, bool, bool) {}

/// (implied root, ok, member).
unconstrained fn merkle_ref(
    leaf: Field,
    index: Field,
    path: [Field; D],
    root: Field,
    sep: Field,
) -> (Field, bool, bool) {
    merkle_ref_oracle(leaf, index, path, root, sep)
}

/// Checks the _sep_ entries with sep, and the plain entries (Aztec's
/// separator) on the same inputs.
fn check(leaf: Field, index: Field, path: [Field; D], root: Field, sep: Field) {
    // Safety: the oracle only supplies the expected answers.
    let (implied, ok, member) = unsafe { merkle_ref(leaf, index, path, root, sep) };
    assert_eq(merkle_root_sep_or(leaf, index, path, sep), (implied, ok));
    assert_eq(is_member_sep(leaf, index, path, root, sep), member);
    // Safety: as above.
    let (implied, ok, member) =
        unsafe { merkle_ref(leaf, index, path, root, MERKLE_HASH_SEPARATOR) };
    assert_eq(merkle_root_or(leaf, index, path), (implied, ok));
    assert_eq(is_member(leaf, index, path, root), member);
}

#[test]
fn merkle_matches_reference(seed: Field) {
    // Safety: the oracle only supplies the case.
    let (leaf, index, path, root, sep) = unsafe { merkle_case(seed) };
    check(leaf, index, path, root, sep);
}

#[test]
fn merkle_raw_inputs(leaf: Field, index: Field, path: [Field; D], root: Field, sep: Field) {
    check(leaf, index, path, root, sep);
}
