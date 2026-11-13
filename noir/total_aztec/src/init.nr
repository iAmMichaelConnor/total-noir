//! Initialisation checks as determined flags.
//!
//! # Where aztec-nr v6 fails
//!
//! Function names are aztec-nr v6.0.0's (`aztec/src/...`).
//!
//! - The contract-level check: in a contract that has an initializer, the
//!   #[aztec] macro puts
//!   macros/functions/initialization_utils.nr's
//!   assert_is_initialized_private at the top of every private function
//!   that is not #[noinitcheck]. Its nullifier read request fails the
//!   kernel when the contract was never initialised, which only the
//!   deployer (for an account, its owner) decides.
//! - PublicImmutable::read in private: the hint asserts "Trying to read
//!   from uninitialized PublicImmutable" (a Brillig trap), and the
//!   nullifier read request would fail the kernel.
//! - PrivateImmutable and SinglePrivateImmutable have no constrained
//!   is_initialized: their initialisation nullifier needs the owner's
//!   nullifier hiding key (PrivateContext::request_nhk_app), which no
//!   other PXE holds. Not made total here: use the found flag of a note
//!   read instead (initialize creates the note in the same call as the
//!   nullifier, so a found note is an initialised variable).
//!
//! # What this module does instead
//!
//! nullifier_exists_at_anchor proves membership or non-membership of the
//! siloed nullifier in the anchor block's nullifier tree with one
//! indexed-tree witness, so the flag is determined relative to the anchor
//! block, and no kernel request is emitted. The price is time: a
//! nullifier emitted after the anchor block, or earlier in the same
//! transaction, reads as absent.
//!
//! # Initializer arguments before initialisation
//!
//! The address commits to the initializer's arguments: address ->
//! partial address -> salted initialization hash -> initialization hash
//! = poseidon2(selector, args hash) (initialization_utils.nr,
//! compute_initialization_hash). initializer_args_or reads hinted
//! arguments and checks them against that commitment, so a value the
//! deployer passed to the initializer (an account's first signing key)
//! is usable before the initializer's effects are readable: in a later
//! call of the initializer's own transaction, which cannot read the notes
//! the initializer created there (note.nr, "Other notes at the slot") and
//! sees no initialisation nullifier at the anchor block. It reports the initialisation flag beside the arguments, and a caller
//! should trust the arguments only while that flag is false: afterwards
//! the contract's state may have replaced them. The flag is relative to
//! the anchor block, which the executor chooses (design.md, "Oracle data
//! and provable error codes"), so "not yet initialised" holds for any
//! anchor before the initialisation settled.
//!
//! The hint is a transient array (aztec-nr's TransientArray) that the
//! initializer records with record_initializer_args: the PXE keeps it for
//! the transaction's simulation and shows it only to this contract's own
//! frames (not even to its sync code, which runs with a store of its
//! own), so the honest hint exists in the initializer's transaction,
//! after the initializer, and needs nothing from the wallet. It holds one
//! Field per element and the read checks the length first, so no record
//! the library writes can make the read abort. The other PXE 6.0.0
//! sources can abort: the auth witness oracle throws on an absent
//! witness, and a capsule, which the requester attaches to the
//! transaction, of another length than the reader's makes the Brillig VM
//! refuse the answer (a vector-typed return does not help: the VM then
//! expects a length slot that the PXE's answer does not have).

use aztec::context::PrivateContext;
use aztec::ephemeral::EphemeralArray;
use aztec::hash::{compute_siloed_nullifier, hash_args};
use aztec::macros::functions::initialization_utils::{
    compute_initialization_hash, compute_private_initialization_nullifier,
};
use aztec::oracle::{
    get_contract_instance::get_contract_instance,
    get_nullifier_membership_witness::{
        get_low_nullifier_membership_witness, get_nullifier_membership_witness,
    },
    nullifiers::get_nullifier_statuses,
};
use aztec::protocol::{
    abis::{
        block_header::BlockHeader, function_selector::FunctionSelector,
        nullifier_leaf_preimage::NullifierLeafPreimage,
    },
    constants::NULLIFIER_TREE_HEIGHT,
    hash::sha256_to_field,
    merkle_tree::{
        membership::check_membership_with_hasher, MembershipWitness, nullifier_merkle_hash,
    },
    traits::Hash,
};
use aztec::state_vars::PublicImmutable;
use aztec::transient::TransientArray;

/// Hint for nullifier_exists_at_anchor: whether the nullifier is in the
/// anchor block's tree, and the witness for that answer (its own leaf, or
/// the low leaf). PXE 6.0.0's status oracle answers for the anchor block
/// and reports a nullifier pending in this transaction with no origin
/// block, which therefore takes the low-leaf path. Each witness oracle is
/// asked only in the case it can answer. Trap-free in the Brillig code.
unconstrained fn hint_nullifier_witness(
    header: BlockHeader,
    inner_nullifier: Field,
    siloed_nullifier: Field,
) -> (bool, NullifierLeafPreimage, MembershipWitness<NULLIFIER_TREE_HEIGHT>) {
    let status = get_nullifier_statuses(EphemeralArray::from_array([inner_nullifier])).get(0);
    let at_anchor = status.exists & status.origin_block.is_some();
    let (leaf, witness) = if at_anchor {
        get_nullifier_membership_witness(header, siloed_nullifier)
    } else {
        get_low_nullifier_membership_witness(header, siloed_nullifier)
    };
    (at_anchor, leaf, witness)
}

/// True when the nullifier this contract pushed as inner_nullifier is in
/// the nullifier tree of the anchor block.
///
/// Constraints: the siloing hash; the hint's typed return (booleanity of
/// exists, and the leaf index's 42-bit decomposition inside the Merkle
/// path): hint-satisfiable; then check_nullifier_witness. No kernel
/// request is emitted.
///
/// Hint rule: the honest PXE reports whether the siloed nullifier is a
/// leaf of the anchor tree and returns that leaf, or the low leaf, with
/// its sibling path.
///
/// Determined (relative to the anchor block; see check_nullifier_witness).
pub fn nullifier_exists_at_anchor(context: &mut PrivateContext, inner_nullifier: Field) -> bool {
    let siloed = compute_siloed_nullifier(context.this_address(), inner_nullifier);
    let header = context.get_anchor_block_header();
    // Safety: check_nullifier_witness proves the answer either way, so a
    // wrong hint fails its own call and cannot flip the flag.
    // total-lint: allow typed hint return (exists flag, leaf index bits); the honest oracle is in range
    let (exists, leaf, witness) =
        unsafe { hint_nullifier_witness(header, inner_nullifier, siloed) };
    check_nullifier_witness(
        header.state.partial.nullifier_tree.root,
        siloed,
        exists,
        leaf,
        witness,
    )
}

/// Constraint half of nullifier_exists_at_anchor, split out so tests can
/// feed wrong hints. Returns exists after asserting that the witness
/// proves it against root.
///
/// Emits: the leaf hash and Merkle path (Poseidon2 per level, the index
/// decomposed into NULLIFIER_TREE_HEIGHT bits), the root equality, the
/// empty-leaf test, and either key == leaf.nullifier (exists) or
/// leaf.nullifier < key < leaf.next_nullifier or the leaf ends the list
/// (not exists); one assert on the conjunction, which restricts the hint:
/// in a valid indexed tree every key has exactly one of a matching leaf
/// or a valid low leaf, so the honest PXE satisfies it for every key.
///
/// Determined: a key cannot have both, so a passing witness fixes exists.
/// The empty leaf is excluded on both paths (it hashes to 0, which every
/// unused position holds), as aztec-nr's assert_nullifier_did_not_exist_by
/// excludes it.
pub fn check_nullifier_witness(
    root: Field,
    key: Field,
    exists: bool,
    leaf: NullifierLeafPreimage,
    witness: MembershipWitness<NULLIFIER_TREE_HEIGHT>,
) -> bool {
    // total-lint: allow Merkle path over the hinted leaf and path (index bits, hashes, root eq): flags, no assert of their own
    let in_tree = check_membership_with_hasher(leaf.hash(), witness, root, nullifier_merkle_hash);
    // total-lint: allow eq gadget on the hinted leaf; hint-satisfiable for every value
    let matching = leaf.nullifier == key;
    let points_to_infinity = (leaf.next_nullifier == 0) & (leaf.next_index == 0);
    // total-lint: allow Field comparisons on the hinted leaf (hinted decompositions); hint-satisfiable for every value
    let low = leaf.nullifier.lt(key) & (key.lt(leaf.next_nullifier) | points_to_infinity);
    let expected = if exists { matching } else { low };
    // total-lint: allow restricts the witness hint; the honest PXE has a valid witness for every key
    assert(in_tree & !leaf.is_empty() & expected, "nullifier witness does not prove the claim");
    exists
}

/// Flag: this contract was initialised (its private initialisation
/// nullifier is in the anchor block's tree). The total replacement for
/// the macro's check: mark the function #[noinitcheck] and fold this flag
/// into ok.
///
/// Permanently false for a contract with no initializer: such a contract
/// never emits the nullifier (and the macro adds no check to it), so do
/// not add this flag there.
///
/// Constraints: get_contract_instance (an instance hint and one assert
/// that it hashes to this address: hint-satisfiable, the PXE executing
/// this contract knows its instance), the nullifier hash, and
/// nullifier_exists_at_anchor. Determined, relative to the anchor block:
/// a contract initialised in the same transaction reads as not
/// initialised.
///
/// DEV DECISION: fail (the macro's check) or flag (this). Keep the
/// macro's check on functions only the owner calls; use #[noinitcheck]
/// plus this flag, or just the found flag of the state read, on functions
/// other users' transactions run.
pub fn contract_is_initialized(context: &mut PrivateContext) -> bool {
    let address = context.this_address();
    // total-lint: allow aztec-nr's instance hint and address check; the honest PXE knows the instance it executes
    let instance = get_contract_instance(address);
    let inner = compute_private_initialization_nullifier(address, instance.initialization_hash);
    nullifier_exists_at_anchor(context, inner)
}

/// Flag: this PublicImmutable was initialised (its initialisation
/// nullifier is in the anchor block's tree). Constraints: one Poseidon2
/// hash and nullifier_exists_at_anchor. Determined, relative to the
/// anchor block.
///
/// public::public_immutable_read_or does not need this: its flag comes
/// from the stored value hash and costs one tree proof instead of two.
pub fn public_immutable_is_initialized<T>(
    context: &mut PrivateContext,
    var: PublicImmutable<T, &mut PrivateContext>,
) -> bool {
    nullifier_exists_at_anchor(context, var.compute_initialization_inner_nullifier())
}

/// Transient slot of initializer_args_or's hint (a TransientArray of
/// Fields, one per argument, of this contract). Derived like aztec-nr's
/// own slots, so it does not collide with them.
pub global INITIALIZER_ARGS_SLOT: Field =
    sha256_to_field("TOTAL_AZTEC::INITIALIZER_ARGS_SLOT".as_bytes());

/// The arguments this contract's initializer was called with, checked
/// against the address, and whether the contract is initialised at the
/// anchor block.
pub struct InitializerArgs<let N: u32> {
    /// The hinted arguments when bound, all zero otherwise.
    pub args: [Field; N],
    /// The arguments and the initializer's selector hash to the
    /// initialization hash in this contract's address. Not determined:
    /// the executor can always make it false (no hint), and it is true
    /// only for the arguments the address commits to.
    pub bound: bool,
    /// contract_is_initialized's flag, from the same instance hint.
    /// Determined, relative to the anchor block.
    pub initialized: bool,
}

unconstrained fn store_initializer_args<let N: u32>(args: [Field; N]) {
    // total-lint: allow the PXE's transient-array clear: keyed by the executing contract, answers for every slot and does not throw
    let record = TransientArray::<Field>::empty_at(INITIALIZER_ARGS_SLOT);
    for i in 0..N {
        // total-lint: allow the PXE's transient-array push: answers for every slot and does not throw
        record.push(args[i]);
    }
}

/// Record the initializer's arguments for initializer_args_or in this
/// contract's later calls of the same transaction. Call it in the
/// initializer, with the arguments in the order the call serialises them
/// (for Field parameters, as declared).
///
/// Emits no constraint: N + 1 oracle calls (clear, then one push per
/// Field, of a TransientArray at INITIALIZER_ARGS_SLOT), none of which
/// throws. The record lives for the transaction's simulation, is visible
/// only to this contract's own frames (the PXE keys it by the executing
/// contract; the contract's sync code runs with a store of its own), and
/// is a hint: initializer_args_or checks it against the address.
pub fn record_initializer_args<let N: u32>(args: [Field; N]) {
    // Safety: a hint for later calls, checked by initializer_args_or.
    unsafe { store_initializer_args(args) };
}

/// Hint for initializer_args_or: the N Fields record_initializer_args
/// stored in this transaction, zeros when the record is absent or holds
/// another number of Fields. Asks for element i only when i is below the
/// length, and every element record_initializer_args writes is one Field,
/// so no record it writes makes this abort. An element of another width
/// at the slot would (the PXE answers with the stored width, and the
/// Brillig VM refuses an answer of another length): only class code that
/// writes the slot with the raw transient oracles can create one.
unconstrained fn hint_initializer_args<let N: u32>() -> [Field; N] {
    let record = TransientArray::<Field>::at(INITIALIZER_ARGS_SLOT);
    let mut args = [0; N];
    // total-lint: allow the PXE's transient-array length: answers for every slot (0 when empty) and does not throw
    if record.len() == N {
        for i in 0..N {
            // total-lint: allow the PXE's transient-array read below the length; record_initializer_args writes one-Field elements
            args[i] = record.get(i);
        }
    }
    args
}

/// Constraint half of initializer_args_or, split out so tests can feed
/// wrong arguments: whether args, as the arguments of the initializer
/// with this selector, give initialization_hash. Emits hash_args (one
/// Poseidon2 hash; 0 for N = 0, as the context's args hash), one more
/// Poseidon2 hash and one eq gadget: no assert. Determined.
pub fn initializer_args_match<let N: u32>(
    initialization_hash: Field,
    initializer: FunctionSelector,
    args: [Field; N],
) -> bool {
    compute_initialization_hash(initializer, hash_args(args)) == initialization_hash
}

/// The initializer's arguments from a hint checked against this
/// contract's address, and the initialisation flag.
///
/// initializer is the selector of the initializer the deployer chose
/// (the instance's initialization hash commits to it), and N its number
/// of argument Fields as the call serialises them (for Field parameters,
/// one each). A contract with no initializer has initialization hash 0,
/// which no selector and arguments give (Poseidon2 preimage), so bound
/// is false there.
///
/// Constraints: get_contract_instance (an instance hint and one assert
/// that it hashes to this address: hint-satisfiable, the PXE executing
/// this contract knows its instance), initializer_args_match on the
/// hinted arguments (no assert), N selects, and the initialisation
/// nullifier's hash and nullifier_exists_at_anchor (one indexed-tree
/// witness, as contract_is_initialized).
///
/// Hint rule: the honest PXE returns what record_initializer_args stored
/// in this transaction, or nothing. So for an honest executor bound can
/// be true only in a call after the initializer in the same transaction;
/// a dishonest one can pass the committed arguments in any transaction
/// (they are no secret to whoever holds the instance), and they are then
/// bound. A missing or wrong hint is bound = false and nothing fails.
///
/// DEV DECISION: what the arguments may decide. Trust them only while
/// initialized is false (they are what the deployer chose, before the
/// contract's own state exists); afterwards read the state, which may
/// have changed since. The executor chooses the anchor block, so the
/// arguments stay usable in every transaction anchored before the
/// initialisation settled (the transaction's expiration bounds how old
/// an anchor can be).
pub fn initializer_args_or<let N: u32>(
    context: &mut PrivateContext,
    initializer: FunctionSelector,
) -> InitializerArgs<N> {
    let address = context.this_address();
    // total-lint: allow aztec-nr's instance hint and address check; the honest PXE knows the instance it executes
    let instance = get_contract_instance(address);
    // Safety: initializer_args_match checks the hint against the address,
    // and a mismatch is bound = false, so a wrong hint cannot fail the call.
    let hinted: [Field; N] = unsafe { hint_initializer_args() };
    let bound = initializer_args_match(instance.initialization_hash, initializer, hinted);
    let mut args = [0; N];
    for i in 0..N {
        args[i] = if bound { hinted[i] } else { 0 };
    }
    let inner = compute_private_initialization_nullifier(address, instance.initialization_hash);
    InitializerArgs { args, bound, initialized: nullifier_exists_at_anchor(context, inner) }
}

mod tests {
    use super::{check_nullifier_witness, initializer_args_match};
    use aztec::macros::functions::initialization_utils::compute_initialization_hash;
    use aztec::protocol::abis::function_selector::FunctionSelector;
    use aztec::protocol::{
        abis::nullifier_leaf_preimage::NullifierLeafPreimage,
        constants::NULLIFIER_TREE_HEIGHT,
        merkle_tree::{
            MembershipWitness, nullifier_merkle_hash, root::root_from_sibling_path_with_hasher,
        },
        traits::Hash,
    };

    // A tree with three leaves, the sorted list 10 -> 20 -> 30 -> end, at
    // indices 0, 1, 2; every other position empty (hash 0).
    global L10: NullifierLeafPreimage =
        NullifierLeafPreimage { nullifier: 10, next_nullifier: 20, next_index: 1 };
    global L20: NullifierLeafPreimage =
        NullifierLeafPreimage { nullifier: 20, next_nullifier: 30, next_index: 2 };
    global L30: NullifierLeafPreimage =
        NullifierLeafPreimage { nullifier: 30, next_nullifier: 0, next_index: 0 };

    fn zero_hashes() -> [Field; NULLIFIER_TREE_HEIGHT] {
        let mut z = [0; NULLIFIER_TREE_HEIGHT];
        for i in 1..NULLIFIER_TREE_HEIGHT {
            z[i] = nullifier_merkle_hash(z[i - 1], z[i - 1]);
        }
        z
    }

    /// Sibling path of index 0..3 in the tree above.
    fn path(index: u32) -> MembershipWitness<NULLIFIER_TREE_HEIGHT> {
        let z = zero_hashes();
        let h = [L10.hash(), L20.hash(), L30.hash(), 0];
        let mut p = z;
        p[0] = h[index ^ 1];
        p[1] = if index < 2 {
            nullifier_merkle_hash(h[2], h[3])
        } else {
            nullifier_merkle_hash(h[0], h[1])
        };
        MembershipWitness { leaf_index: index as Field, sibling_path: p }
    }

    fn root() -> Field {
        root_from_sibling_path_with_hasher(
            L10.hash(),
            0,
            path(0).sibling_path,
            nullifier_merkle_hash,
        )
    }

    #[test]
    fn honest_witnesses_give_both_answers() {
        let r = root();
        // the three leaves agree on the root
        assert_eq(
            root_from_sibling_path_with_hasher(
                L30.hash(),
                2,
                path(2).sibling_path,
                nullifier_merkle_hash,
            ),
            r,
        );
        assert(check_nullifier_witness(r, 20, true, L20, path(1)));
        assert(!check_nullifier_witness(r, 25, false, L20, path(1)));
        assert(!check_nullifier_witness(r, 99, false, L30, path(2)));
    }

    #[test(should_fail_with = "nullifier witness does not prove the claim")]
    fn claiming_absent_for_a_present_key_fails() {
        // 20 is present; L10 is not a valid low leaf for it (next is 20).
        let _ = check_nullifier_witness(root(), 20, false, L10, path(0));
    }

    #[test(should_fail_with = "nullifier witness does not prove the claim")]
    fn claiming_present_for_an_absent_key_fails() {
        let _ = check_nullifier_witness(root(), 25, true, L20, path(1));
    }

    #[test(should_fail_with = "nullifier witness does not prove the claim")]
    fn the_empty_leaf_does_not_prove_absence() {
        // Position 3 is empty and its hash 0 is in the tree.
        let empty = NullifierLeafPreimage { nullifier: 0, next_nullifier: 0, next_index: 0 };
        let _ = check_nullifier_witness(root(), 20, false, empty, path(3));
    }

    #[test(should_fail_with = "nullifier witness does not prove the claim")]
    fn a_leaf_not_in_the_tree_fails() {
        let fake = NullifierLeafPreimage { nullifier: 25, next_nullifier: 30, next_index: 2 };
        let _ = check_nullifier_witness(root(), 25, true, fake, path(1));
    }

    #[test(should_fail_with = "nullifier witness does not prove the claim")]
    fn a_wrong_path_fails() {
        let _ = check_nullifier_witness(root(), 30, true, L30, path(1));
    }

    global CTOR: FunctionSelector = FunctionSelector::from_signature("constructor(Field,Field)");

    #[test]
    fn initializer_args_match_only_the_committed_arguments() {
        let args = [5, 6];
        let h = compute_initialization_hash(CTOR, aztec::hash::hash_args(args));
        assert(initializer_args_match(h, CTOR, args));
        assert(!initializer_args_match(h, CTOR, [5, 7]));
        assert(!initializer_args_match(h, CTOR, [6, 5]));
        assert(!initializer_args_match(h, CTOR, [0, 0]));
        let other = FunctionSelector::from_signature("initialize(Field,Field)");
        assert(!initializer_args_match(h, other, args));
        // no initializer: initialization hash 0
        assert(!initializer_args_match(0, CTOR, [0, 0]));
        // an initializer with no arguments: the args hash is 0
        let h0 = compute_initialization_hash(CTOR, 0);
        assert(initializer_args_match::<0>(h0, CTOR, []));
    }
}
