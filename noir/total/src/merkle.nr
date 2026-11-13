//! Poseidon2 Merkle membership as flags: the root a leaf and its sibling
//! path imply, with the leaf index flagged, and membership against an
//! expected root.
//!
//! Hashing convention, Aztec's, so roots and paths interoperate with
//! Aztec's trees and its TypeScript tree code:
//! - A node is merkle_hash(left, right) = Poseidon2 of
//!   [MERKLE_HASH_SEPARATOR, left, right], that is
//!   hash::p2_hash_sep([left, right], 2982624097). This is protocol_types'
//!   merkle_hash (DOM_SEP__MERKLE_HASH), the node hash of Aztec's
//!   append-only trees. The _sep_ forms take another separator for trees
//!   that use one (Aztec's nullifier and public-data trees use their own).
//! - path[i] is the sibling at height i: path[0] is the leaf's sibling,
//!   path[D - 1] the root's child.
//! - Index bits are little-endian: bit i of the index is the side of the
//!   running node at height i, 0 for a left child (node = hash(node,
//!   path[i])) and 1 for a right child (node = hash(path[i], node)).
//! These are the semantics of protocol_types root_from_sibling_path(leaf,
//! leaf_index, sibling_path) (aztec-packages v6.0.0,
//! noir-projects/fnd/noir-protocol-circuits/crates/types/src/merkle_tree/
//! root.nr, the crate aztec-nr v6.0.0 re-exports as crate::protocol). The
//! tests reproduce that crate's TypeScript-generated root of the 16-leaf
//! tree [1, ..., 16] from every leaf's path, and its empty-tree roots.
//!
//! What this adds: root_from_sibling_path decomposes leaf_index with
//! to_le_bits::<N>(), which is input-falsifiable for an index at or above
//! 2^N (no bit decomposition of that length exists). Here the index is
//! flagged: ok = (index < 2^D), and on ok = false the root is 0 and
//! is_member is false.
//!
//! Gadgets: range::clamp_bits_or::<D> (canonical limbs and one split,
//! hint-satisfiable for every Field, determined), std to_le_bits::<D> on
//! the clamped index (below 2^D, so the decomposition exists and is
//! unique: hint-satisfiable, determined), Poseidon2 permutation black
//! boxes (definitions, total for every input), Field selects, and one eq
//! gadget in is_member. No hints of their own.

use crate::core::{eq, is_zero, select_field};
use crate::hash::p2_hash_sep;
use crate::range::clamp_bits_or;
use std::static_assert;

/// Aztec's DOM_SEP__MERKLE_HASH (protocol_types constants.nr, v6.0.0).
pub global MERKLE_HASH_SEPARATOR: Field = 2982624097;

/// The node hash: Poseidon2 of [sep, left, right]. One permutation;
/// definitions only, no failure source.
fn node_hash(left: Field, right: Field, sep: Field) -> Field {
    p2_hash_sep([left, right], sep)
}

/// Aztec's merkle_hash(left, right): node_hash with MERKLE_HASH_SEPARATOR.
/// One Poseidon2 permutation; definitions only, total.
pub fn merkle_hash(left: Field, right: Field) -> Field {
    node_hash(left, right, MERKLE_HASH_SEPARATOR)
}

/// The D little-endian bits of index and ok = (index < 2^D); the bits are
/// those of 0 when ok is false. For D = 0, ok = (index == 0) (one eq
/// gadget). Otherwise clamp_bits_or::<D> and to_le_bits::<D> on the
/// clamped value, as in the module header. Determined.
fn index_bits_or<let D: u32>(index: Field) -> ([bool; D], bool) {
    if D == 0 {
        ([false; D], is_zero(index))
    } else {
        let (i1, ok) = clamp_bits_or::<D>(index);
        (i1.to_le_bits(), ok)
    }
}

/// The root implied by leaf, its index and its sibling path in a tree of
/// depth D whose nodes are Poseidon2 of [sep, left, right]: (root, ok)
/// with ok = (index < 2^D); on ok = false the root is 0. 0 <= D <= 128.
///
/// Constraints: index_bits_or::<D> (hint-satisfiable for every Field
/// index, determined); per level two Field selects ordering (node,
/// path[i]) by the index bit and one Poseidon2 permutation; one select to
/// 0. Total for every input; root and ok are determined. Cost: one
/// fits_bits gadget, D bits, D permutations and 2D + 1 selects.
pub fn merkle_root_sep_or<let D: u32>(
    leaf: Field,
    index: Field,
    path: [Field; D],
    sep: Field,
) -> (Field, bool) {
    static_assert(D <= 128, "merkle_root_sep_or: D must be in 0..=128");
    let (bits, ok) = index_bits_or::<D>(index);
    let mut node = leaf;
    for i in 0..D {
        let left = select_field(bits[i], path[i], node);
        let right = select_field(bits[i], node, path[i]);
        node = node_hash(left, right, sep);
    }
    (select_field(ok, node, 0), ok)
}

/// merkle_root_sep_or with Aztec's MERKLE_HASH_SEPARATOR: the value of
/// protocol_types root_from_sibling_path(leaf, index, path) whenever
/// index < 2^D, and (0, false) otherwise. 0 <= D <= 128. Same constraints
/// and cost as merkle_root_sep_or.
pub fn merkle_root_or<let D: u32>(leaf: Field, index: Field, path: [Field; D]) -> (Field, bool) {
    static_assert(D <= 128, "merkle_root_or: D must be in 0..=128");
    merkle_root_sep_or(leaf, index, path, MERKLE_HASH_SEPARATOR)
}

/// True when index < 2^D and leaf at index with this sibling path hashes
/// (Aztec's convention) to root. merkle_root_or, then one eq gadget and an
/// AND with ok, so a root of 0 never matches an out-of-range index.
/// Total; determined. 0 <= D <= 128.
pub fn is_member<let D: u32>(leaf: Field, index: Field, path: [Field; D], root: Field) -> bool {
    static_assert(D <= 128, "is_member: D must be in 0..=128");
    let (r, ok) = merkle_root_or(leaf, index, path);
    ok & eq(r, root)
}

/// is_member for a tree hashed with separator sep. Same constraints.
pub fn is_member_sep<let D: u32>(
    leaf: Field,
    index: Field,
    path: [Field; D],
    root: Field,
    sep: Field,
) -> bool {
    static_assert(D <= 128, "is_member_sep: D must be in 0..=128");
    let (r, ok) = merkle_root_sep_or(leaf, index, path, sep);
    ok & eq(r, root)
}

mod tests {
    use crate::core::two_pow;
    use crate::hash::p2_hash_sep;
    use crate::test_support::wit;
    use super::{is_member, is_member_sep, merkle_hash, merkle_root_or, merkle_root_sep_or};

    global P_MINUS_1: Field = 0 - 1;
    global TWO_POW_128: Field = 0x100000000000000000000000000000000;

    // protocol_types merkle_tree/root.nr test_merkle_roots_match_typescript:
    // compute_tree_root([1, ..., 16]), generated by yarn-project's
    // balanced_merkle_tree_root.test.ts.
    global TS_ROOT_1_TO_16: Field =
        0x2bc86dba04dfdd6352c3b1c66b2300445964e2888aa52fdb023d2e645a3d3399;

    /// The 16-leaf tree [1, ..., 16] built level by level with
    /// merkle_hash: (leaves, level 1 (8 nodes), level 2 (4), level 3 (2)).
    fn tree16() -> ([Field; 16], [Field; 8], [Field; 4], [Field; 2]) {
        let mut l0 = [0; 16];
        for i in 0..16 {
            l0[i] = (i + 1) as Field;
        }
        let mut l1 = [0; 8];
        for i in 0..8 {
            l1[i] = merkle_hash(wit(l0[2 * i]), wit(l0[2 * i + 1]));
        }
        let mut l2 = [0; 4];
        for i in 0..4 {
            l2[i] = merkle_hash(wit(l1[2 * i]), wit(l1[2 * i + 1]));
        }
        let mut l3 = [0; 2];
        for i in 0..2 {
            l3[i] = merkle_hash(wit(l2[2 * i]), wit(l2[2 * i + 1]));
        }
        (l0, l1, l2, l3)
    }

    /// The sibling path of leaf i in tree16: the node next to the running
    /// node at each height (index XOR 1 at that level).
    fn path16(i: u32) -> [Field; 4] {
        let (l0, l1, l2, l3) = tree16();
        [l0[i ^ 1], l1[(i / 2) ^ 1], l2[(i / 4) ^ 1], l3[(i / 8) ^ 1]]
    }

    #[test]
    fn node_hash_is_aztec_merkle_hash() {
        // protocol_types test_empty_tree_root: compute_empty_tree_root::<1>
        // is merkle_hash(0, 0)
        assert_eq(
            merkle_hash(wit(0), wit(0)),
            0x19f1a0c09db4cd026f686e9c8fb45501a9fefb4eb1b4c6c328a51343a0094eeb,
        );
        assert_eq(merkle_hash(wit(3), wit(4)), p2_hash_sep(wit([3, 4]), wit(2982624097)));
    }

    #[test]
    fn hand_built_tree_matches_the_typescript_root() {
        let (_, _, _, l3) = tree16();
        assert_eq(merkle_hash(wit(l3[0]), wit(l3[1])), TS_ROOT_1_TO_16);
        for i in 0..16 {
            let leaf = (i + 1) as Field;
            assert_eq(
                merkle_root_or(wit(leaf), wit(i as Field), wit(path16(i))),
                (TS_ROOT_1_TO_16, true),
            );
            assert(
                is_member(
                    wit(leaf),
                    wit(i as Field),
                    wit(path16(i)),
                    wit(TS_ROOT_1_TO_16),
                ),
            );
        }
    }

    #[test]
    fn empty_tree_roots_match_aztec() {
        // protocol_types test_empty_tree_root: depth 2 and depth 10
        let mut z = [0; 10];
        let mut h: Field = 0;
        for i in 0..10 {
            z[i] = h;
            h = merkle_hash(wit(h), wit(h));
        }
        assert_eq(
            merkle_root_or(wit(0), wit(3), wit([z[0], z[1]])),
            (0x14e4b977b2203b70e6ee1c2456eb7114d090fe4b907f631eecd0919fed432e7d, true),
        );
        assert_eq(
            merkle_root_or(wit(0), wit(1023), wit(z)),
            (0x0d04c63f36bd168215c9b09a227c7e8d3ad48e2f11b8202fd07c524bd30ee88f, true),
        );
    }

    #[test]
    fn wrong_leaf_index_or_root_is_not_a_member() {
        let p = path16(5);
        assert(is_member(wit(6), wit(5), wit(p), wit(TS_ROOT_1_TO_16)));
        assert(!is_member(wit(7), wit(5), wit(p), wit(TS_ROOT_1_TO_16)));
        assert(!is_member(wit(6), wit(4), wit(p), wit(TS_ROOT_1_TO_16)));
        assert(!is_member(wit(6), wit(5), wit(p), wit(TS_ROOT_1_TO_16 + 1)));
        assert(!is_member(wit(6), wit(5), wit(path16(4)), wit(TS_ROOT_1_TO_16)));
    }

    #[test]
    fn out_of_range_index_is_flagged() {
        let p = path16(5);
        // 5 + 16 has the same low four bits as 5; it must not pass
        for index in [16, 21, 31, TWO_POW_128, TWO_POW_128 + 5, P_MINUS_1] {
            assert_eq(merkle_root_or(wit(6), wit(index), wit(p)), (0, false));
            assert(!is_member(wit(6), wit(index), wit(p), wit(TS_ROOT_1_TO_16)));
            assert(!is_member(wit(6), wit(index), wit(p), wit(0)));
        }
        assert_eq(merkle_root_or(wit(16), wit(15), wit(path16(15))), (TS_ROOT_1_TO_16, true));
    }

    #[test]
    fn depth_zero_and_wide_depths() {
        assert_eq(merkle_root_or(wit(42), wit(0), wit([])), (42, true));
        assert_eq(merkle_root_or(wit(42), wit(1), wit([])), (0, false));
        assert_eq(merkle_root_or(wit(42), wit(P_MINUS_1), wit([])), (0, false));
        assert(is_member(wit(42), wit(0), wit([]), wit(42)));
        assert(!is_member(wit(42), wit(1), wit([]), wit(0)));
        let (r, ok) = merkle_root_or(wit(1), wit(two_pow::<128>() - 1), wit([0; 128]));
        assert(ok);
        assert(r != 0);
        assert_eq(merkle_root_or(wit(1), wit(TWO_POW_128), wit([0; 128])), (0, false));
        let (r1, ok1) = merkle_root_or(wit(1), wit(two_pow::<127>()), wit([0; 128]));
        assert(ok1);
        assert(r1 != r);
    }

    #[test]
    fn separator_forms() {
        let sep = 12345;
        let r = p2_hash_sep(wit([p2_hash_sep(wit([7, 8]), wit(sep)), 9]), wit(sep));
        assert_eq(merkle_root_sep_or(wit(7), wit(0), wit([8, 9]), wit(sep)), (r, true));
        assert(is_member_sep(wit(7), wit(0), wit([8, 9]), wit(r), wit(sep)));
        assert(!is_member_sep(wit(7), wit(0), wit([8, 9]), wit(r), wit(sep + 1)));
        assert_eq(merkle_root_sep_or(wit(8), wit(1), wit([7, 9]), wit(sep)), (r, true));
        assert_eq(merkle_root_sep_or(wit(8), wit(4), wit([7, 9]), wit(sep)), (0, false));
    }
}
