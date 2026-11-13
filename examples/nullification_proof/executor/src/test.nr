//! TXE tests for the proof-of-nullification pattern: the executor E
//! passes one of the owner B's handoffs, with the leaf's index and
//! sibling path at its anchor block, and A consumes B's note in E's
//! transaction.
//!
//! The TXE does not check recursive proofs: the ACVM solver treats
//! RecursiveAggregation as a no-op, so witness generation passes for any
//! proof bytes (docs/recagg-probe). These tests therefore pass
//! zero proof bytes and show the flow, the flags, the leaf's membership
//! path against the real tree and the nullifier's canonical value. Whether
//! B's proofs verify under A's public inputs is shown with bb by run.sh:
//! make_fixture.py proves B's handoffs from the values `fixture_values`
//! prints and runs E's pre-check on each, and outer_check.py proves the
//! executor's check on the real proofs. The handoffs passed here are the
//! ones that pre-check passes on (honest, bound to E, live; unsettled,
//! with no path), plus a few it rejects, passed anyway to show what A
//! does with them. A handoff the pre-check rejects outright (a proof for
//! other public inputs, or bound to another executor) is otherwise
//! replaced by the withheld one, which A reads as
//! withheld_proof_is_a_flag.
//!
//! The vk is the real one (owner_vk.nr), since A checks its hash. Every
//! other value is computed here: the planted note's leaf and nullifier
//! with aztec-nr's formulas, the anchor block from the TXE.

use crate::NullificationExecutor;
use crate::NullificationExecutor::ValueNote;
use crate::owner_vk::OWNER_VK;
use aztec::context::PrivateStaticCall;
use aztec::keys::getters::{get_nhk_app, get_public_keys};
use aztec::note::note_interface::{NoteHash, NoteType};
use aztec::note::utils::compute_note_nullifier;
use aztec::oracle::get_membership_witness::get_note_hash_membership_witness;
use aztec::oracle::notes::notify_created_note;
use aztec::protocol::address::AztecAddress;
use aztec::protocol::constants::{NOTE_HASH_TREE_HEIGHT, NULL_MSG_SENDER_CONTRACT_ADDRESS};
use aztec::protocol::hash::{
    compute_note_hash_nonce, compute_siloed_note_hash, compute_siloed_nullifier,
    compute_unique_note_hash, poseidon2_hash,
};
use aztec::protocol::traits::Packable;
use aztec::test::helpers::test_environment::{CreateAccountOptions, TestEnvironment};
use aztec::test::helpers::txe_oracles;
use total_aztec::note::check_note_hash_witness;
use total_aztec::nullification_proof::NullificationProof;

global VALUE: Field = 1000;
global RANDOMNESS: Field = 0x5eed;
global OWNER_SECRET: Field = 0xb0b;
global EXECUTOR_SECRET: Field = 0xe0e;
global OTHER_SECRET: Field = 0x0e1;
/// The proof bytes the tests pass: the TXE does not read them.
global NO_PROOF: [Field; 458] = [0; 458];

/// A, the owner B, the executor E, and another executor `other`, all at
/// fixed addresses (make_fixture.py's proofs bind them).
unconstrained fn setup() -> (TestEnvironment, AztecAddress, AztecAddress, AztecAddress, AztecAddress) {
    let mut env = TestEnvironment::new();
    let a = env.deploy("NullificationExecutor").without_initializer();
    let owner =
        env.create_light_account_opts(CreateAccountOptions::new().with_secret(OWNER_SECRET));
    let executor =
        env.create_light_account_opts(CreateAccountOptions::new().with_secret(EXECUTOR_SECRET));
    let other =
        env.create_light_account_opts(CreateAccountOptions::new().with_secret(OTHER_SECRET));
    (env, a, owner, executor, other)
}

/// The note-hash-tree leaf of owner's ValueNote { VALUE } in A's balances
/// with the given randomness and nonce: aztec-nr's note hash, siloed by
/// A and made unique by the nonce.
unconstrained fn leaf_of(
    a: AztecAddress,
    owner: AztecAddress,
    randomness: Field,
    nonce: Field,
) -> Field {
    let slot = NullificationExecutor::storage_layout().balances.slot;
    let note_hash = ValueNote { value: VALUE }.compute_note_hash(owner, slot, randomness);
    compute_unique_note_hash(nonce, compute_siloed_note_hash(a, note_hash))
}

/// Plant one of owner's ValueNotes in A's balances with fixed randomness
/// (aztec-nr's create_note draws it from an oracle), so that the owner's
/// proof can be made before the test runs: create_note's two steps, the
/// PXE notification and the note hash push, with our randomness. Returns
/// (leaf, nonce).
///
/// The nonce is the TXE's: a private context's effects become one
/// transaction whose nonce generator is the protocol nullifier of the
/// request hash block_number + 9999 (@aztec-labs/txe 6.0.0,
/// dest/txe_session.js and utils/block_creation.js). consume's read
/// request checks the resulting leaf is in the tree.
unconstrained fn plant(
    env: TestEnvironment,
    a: AztecAddress,
    owner: AztecAddress,
) -> (Field, Field) {
    let slot = NullificationExecutor::storage_layout().balances.slot;
    let note = ValueNote { value: VALUE };
    let note_hash = note.compute_note_hash(owner, slot, RANDOMNESS);
    let block = env.next_block_number();
    env.private_context_at(a, |context| {
        let counter = context.get_side_effect_counter();
        notify_created_note(
            owner,
            slot,
            RANDOMNESS,
            ValueNote::get_id(),
            note.pack(),
            note_hash,
            counter,
        );
        context.push_note_hash(note_hash);
    });
    let protocol_nullifier =
        compute_siloed_nullifier(NULL_MSG_SENDER_CONTRACT_ADDRESS, (block + 9999) as Field);
    let nonce = compute_note_hash_nonce(protocol_nullifier, 0);
    (leaf_of(a, owner, RANDOMNESS, nonce), nonce)
}

unconstrained fn owner_nhk_app(
    env: TestEnvironment,
    a: AztecAddress,
    owner: AztecAddress,
) -> Field {
    env.private_context_at(a, |_context| get_nhk_app(get_public_keys(owner).npk_m_hash))
}

#[test]
unconstrained fn fixture_values() {
    let (env, a, owner, executor, other) = setup();
    let (leaf, nonce) = plant(env, a, owner);
    env.call_private(owner, NullificationExecutor::at(a).register());
    // E's anchor block for its consume: the last block after the same
    // steps a consume test takes (registered(); fetching the leaf's path
    // mines no block), read before anything else here can mine a block.
    // (The tests read their own anchor; make_fixture.py uses this one for
    // the expiry proofs.)
    let anchor = env.last_block_number() as Field;
    let pin = env.execute_utility(NullificationExecutor::at(a).pin_of(owner));
    let nhk_app = owner_nhk_app(env, a, owner);
    println(f"FIXTURE contract_address {a}");
    let slot = NullificationExecutor::storage_layout().balances.slot;
    println(f"FIXTURE storage_slot {slot}");
    println(f"FIXTURE owner {owner}");
    println(f"FIXTURE value {VALUE}");
    println(f"FIXTURE randomness {RANDOMNESS}");
    println(f"FIXTURE nonce {nonce}");
    println(f"FIXTURE nhk_app {nhk_app}");
    println(f"FIXTURE leaf {leaf}");
    let nullifier = compute_note_nullifier(leaf, [nhk_app]);
    println(f"FIXTURE nullifier {nullifier}");
    println(f"FIXTURE pin {pin}");
    println(f"FIXTURE executor {executor}");
    println(f"FIXTURE other {other}");
    println(f"FIXTURE anchor {anchor}");
}

/// The world every consume test starts from: A, B's planted note and
/// B's registration, and the values B's handoffs carry.
struct World {
    env: TestEnvironment,
    a: AztecAddress,
    owner: AztecAddress,
    executor: AztecAddress,
    other: AztecAddress,
    /// The planted note's leaf and its nullifier (aztec-nr's formulas with
    /// B's key): what B's honest and bound handoffs claim.
    leaf: Field,
    nullifier: Field,
    /// The forged handoff's nullifier: the planted leaf under another key.
    forged_nullifier: Field,
    /// The unsettled handoff's leaf and nullifier: B's key over a preimage
    /// that was never planted (other randomness).
    unsettled_leaf: Field,
    unsettled_nullifier: Field,
}

unconstrained fn registered() -> World {
    let (env, a, owner, executor, other) = setup();
    let (leaf, nonce) = plant(env, a, owner);
    env.call_private(owner, NullificationExecutor::at(a).register());
    let nhk_app = owner_nhk_app(env, a, owner);
    let unsettled_leaf = leaf_of(a, owner, RANDOMNESS + 1, nonce);
    World {
        env,
        a,
        owner,
        executor,
        other,
        leaf,
        nullifier: compute_note_nullifier(leaf, [nhk_app]),
        forged_nullifier: compute_note_nullifier(leaf, [nhk_app + 1]),
        unsettled_leaf,
        unsettled_nullifier: compute_note_nullifier(unsettled_leaf, [nhk_app]),
    }
}

/// The leaf's index and sibling path in A's note hash tree at the latest
/// block (the anchor of E's next call), as E fetches them from a node; a
/// utility context mines no block. For a leaf that is not in the tree E
/// has no path: index 0 and an all-zero path.
unconstrained fn path_of(
    w: World,
    leaf: Field,
    settled: bool,
) -> (Field, [Field; NOTE_HASH_TREE_HEIGHT]) {
    if settled {
        w.env.utility_context_at(w.a, |context| {
            let witness = get_note_hash_membership_witness(context.block_header(), leaf);
            (witness.leaf_index, witness.sibling_path)
        })
    } else {
        (0, [0; NOTE_HASH_TREE_HEIGHT])
    }
}

/// One of B's unbound handoffs (executor = 0, expiry = 0) as E passes
/// it, with the leaf's path when the leaf is in the tree.
unconstrained fn handoff(
    w: World,
    vk: [Field; 115],
    leaf: Field,
    nullifier: Field,
    settled: bool,
) -> NullificationProof<1> {
    bound_handoff(w, vk, 0, 0, leaf, nullifier, settled)
}

/// One of B's handoffs with its claimed binding.
unconstrained fn bound_handoff(
    w: World,
    vk: [Field; 115],
    executor: Field,
    expiry: Field,
    leaf: Field,
    nullifier: Field,
    settled: bool,
) -> NullificationProof<1> {
    let (leaf_index, sibling_path) = path_of(w, leaf, settled);
    NullificationProof::<1> {
        vk,
        proof: NO_PROOF,
        executor,
        expiry,
        fields: [VALUE],
        leaf,
        leaf_index,
        sibling_path,
        nullifier,
    }
}

/// B's honest handoff of the planted note, with the given vk.
unconstrained fn honest(w: World, vk: [Field; 115]) -> NullificationProof<1> {
    handoff(w, vk, w.leaf, w.nullifier, true)
}

/// B's bound handoff of the planted note.
unconstrained fn bound(w: World, executor: Field, expiry: Field) -> NullificationProof<1> {
    bound_handoff(w, OWNER_VK, executor, expiry, w.leaf, w.nullifier, true)
}

/// A call to A::consume(owner, data) from caller.
unconstrained fn consume(
    w: World,
    caller: AztecAddress,
    data: NullificationProof<1>,
) -> (Field, bool) {
    w.env.call_private(caller, NullificationExecutor::at(w.a).consume(w.owner, data))
}

unconstrained fn last_tx_has_nullifier(a: AztecAddress, nullifier: Field) -> bool {
    let siloed = compute_siloed_nullifier(a, nullifier);
    let nullifiers = txe_oracles::get_last_tx_effects().nullifiers;
    let mut found = false;
    for i in 0..nullifiers.len() {
        if nullifiers.get(i) == siloed {
            found = true;
        }
    }
    found
}

// The vk the tests pass is the one A pins: bb's vk hash is poseidon2
// over the vk fields, which A recomputes. make_fixture.py --vk checks
// owner_vk.nr against the owner circuit.
#[test]
unconstrained fn owner_vk_is_the_pinned_one() {
    assert_eq(poseidon2_hash(OWNER_VK), NullificationExecutor::OWNER_CIRCUIT_VK_HASH);
}

#[test]
unconstrained fn executor_consumes_owners_note() {
    let w = registered();
    assert_eq(consume(w, w.executor, honest(w, OWNER_VK)), (VALUE, true));
    assert(last_tx_has_nullifier(w.a, w.nullifier));
}

// A withheld proof: E passes the all-zero handoff, A completes with
// ok = false and nothing is nullified. This is also what A sees for every
// handoff E's pre-check rejects (make_fixture.py: forged, bound to
// another executor, expired, claimed unbound).
#[test]
unconstrained fn withheld_proof_is_a_flag() {
    let w = registered();
    assert_eq(consume(w, w.executor, NullificationProof::withheld()), (0, false));
    assert(!last_tx_has_nullifier(w.a, w.nullifier));
}

#[test]
unconstrained fn unregistered_owner_is_a_flag() {
    let (env, a, owner, executor, other) = setup();
    let (leaf, _nonce) = plant(env, a, owner);
    let nullifier = compute_note_nullifier(leaf, [owner_nhk_app(env, a, owner)]);
    let w = World {
        env,
        a,
        owner,
        executor,
        other,
        leaf,
        nullifier,
        forged_nullifier: 0,
        unsettled_leaf: 0,
        unsettled_nullifier: 0,
    };
    assert_eq(consume(w, executor, honest(w, OWNER_VK)), (0, false));
    assert(!last_tx_has_nullifier(a, nullifier));
}

#[test]
unconstrained fn unpinned_vk_is_a_flag() {
    let w = registered();
    let mut vk = OWNER_VK;
    vk[3] += 1;
    assert_eq(consume(w, w.executor, honest(w, vk)), (0, false));
}

// A consume reached through a static call, with B's honest handoff:
// pushing the nullifier there would make the kernel reject E's
// transaction, so A reads it as ok = false, pushes nothing and leaves the
// verification's predicate 0. (The TXE does not enforce the static-call
// rules itself; without the static term this call returns the value and
// ok = true.) The handoff is still consumed by E's ordinary call.
#[test]
unconstrained fn static_call_is_a_flag() {
    let w = registered();
    let call = NullificationExecutor::at(w.a).consume(w.owner, honest(w, OWNER_VK));
    let view: PrivateStaticCall<_, _, (Field, bool)> =
        PrivateStaticCall::new(call.target_contract, call.selector, call.name, call.args);
    assert_eq(w.env.view_private(w.executor, view), (0, false));
    assert_eq(consume(w, w.executor, honest(w, OWNER_VK)), (VALUE, true));
    assert(last_tx_has_nullifier(w.a, w.nullifier));
}

// The same handoff passed twice: the second consume finds the note spent
// at its anchor block and returns ok = false instead of pushing a
// duplicate nullifier.
#[test]
unconstrained fn spent_note_is_a_flag() {
    let w = registered();
    let (_, first) = consume(w, w.executor, honest(w, OWNER_VK));
    assert(first);
    assert_eq(consume(w, w.executor, honest(w, OWNER_VK)), (0, false));
}

// What E's pre-check catches: B's forged handoff (a proof made with
// another key, so its key commitment is not B's pin and its nullifier is
// not the note's) passed without it. The pre-check rejects it
// (make_fixture.py: native verify against E's array fails). Every flag A
// can compute holds (pinned vk, registered owner, leaf in the tree,
// nullifier fresh), so ok = true, and the TXE, which does not check
// recursive proofs, completes the call and pushes the forged nullifier.
// A real prover cannot prove this call: bb fails on the recursive
// verification (outer_check.py "forged key"; the Chonk run in
// docs/toolchain-semantics.md). Whoever passes the handoff chooses this,
// which is why consume's call site carries the lint marker for it.
#[test]
unconstrained fn unchecked_forged_proof_passes_simulation_only() {
    let w = registered();
    let forged = handoff(w, OWNER_VK, w.leaf, w.forged_nullifier, true);
    assert_eq(consume(w, w.executor, forged), (VALUE, true));
    assert(last_tx_has_nullifier(w.a, w.forged_nullifier));
}

// B proves, with its real key, a note that was never planted: the proof
// verifies for A's public inputs, but the leaf is not in the note hash
// tree. E's pre-check passes the proof and finds no path for the leaf;
// passed with no path, or with the planted leaf's path, A's membership
// flag reads false, A returns ok = false, nothing is pushed. No oracle
// is asked (the PXE's witness oracle throws on an absent leaf).
#[test]
unconstrained fn never_settled_leaf_is_a_flag() {
    let w = registered();
    let no_path = handoff(w, OWNER_VK, w.unsettled_leaf, w.unsettled_nullifier, false);
    assert_eq(consume(w, w.executor, no_path), (0, false));
    let mut wrong_path = honest(w, OWNER_VK);
    wrong_path.leaf = w.unsettled_leaf;
    wrong_path.nullifier = w.unsettled_nullifier;
    assert_eq(consume(w, w.executor, wrong_path), (0, false));
    assert(!last_tx_has_nullifier(w.a, w.unsettled_nullifier));
}

// The membership flag on the TXE's real note hash tree: the planted leaf
// on its own path reads true; the never-planted leaf on that path, the
// planted leaf on the all-zero path and on an index outside the tree read
// false. A wrong witness can neither make the flag true nor fail the call
// (no assert on it).
#[test]
unconstrained fn membership_flag_on_the_real_tree() {
    let w = registered();
    let (index, path) = path_of(w, w.leaf, true);
    let (planted, unsettled, empty_path, wide) = w.env.private_context_at(w.a, |context| {
        let root = context.get_anchor_block_header().state.partial.note_hash_tree.root;
        (
            check_note_hash_witness(root, w.leaf, index, path),
            check_note_hash_witness(root, w.unsettled_leaf, index, path),
            check_note_hash_witness(root, w.leaf, 0, [0; NOTE_HASH_TREE_HEIGHT]),
            check_note_hash_witness(root, w.leaf, index + 0x40000000000, path),
        )
    });
    assert(planted);
    assert(!unsettled);
    assert(!empty_path);
    assert(!wide);
}

// The optional binding. B's bound handoffs are of the planted note with
// B's real key; only executor and expiry differ from the unbound one.
// make_fixture.py checks that the binding changes neither leaf nor
// nullifier, and that a bound proof claimed as unbound fails E's native
// verify (the binding is bound by the proof; outer_check.py "claimed
// unbound": no proof).

// B binds the proof to E: E's pre-check verifies it against E's array
// (with B's claimed executor and expiry) and finds the binding admits E,
// and A consumes the note in E's call.
#[test]
unconstrained fn proof_bound_to_this_executor_is_consumed() {
    let w = registered();
    assert_eq(consume(w, w.executor, bound(w, w.executor.inner, 0)), (VALUE, true));
    assert(last_tx_has_nullifier(w.a, w.nullifier));
}

// B binds the proof to another executor. E's pre-check: the proof
// verifies, but the binding does not admit E, so E passes the withheld
// handoff instead. Passed anyway, executor_ok is false in the circuit, so
// ok = false and nothing is pushed. Unlike a proof for other public
// inputs this is a flag, not a proving failure: the predicate is off, so
// E's transaction proves (outer_check.py "wrong executor").
#[test]
unconstrained fn proof_bound_to_another_executor_is_a_flag() {
    let w = registered();
    assert_eq(consume(w, w.executor, bound(w, w.other.inner, 0)), (0, false));
    assert(!last_tx_has_nullifier(w.a, w.nullifier));
}

// The executor a proof names consumes with it: the binding admits its
// own address as A's msg_sender.
#[test]
unconstrained fn the_named_executor_consumes_its_bound_proof() {
    let w = registered();
    assert_eq(consume(w, w.other, bound(w, w.other.inner, 0)), (VALUE, true));
    assert(last_tx_has_nullifier(w.a, w.nullifier));
}

// B's proof expires at E's anchor block (anchor < expiry fails). E's
// pre-check rejects it; passed anyway, A reads it as ok = false and
// nothing is pushed (outer_check.py "expired" proves). The anchor is the
// last block before E's call.
#[test]
unconstrained fn expired_proof_is_a_flag() {
    let w = registered();
    let anchor = w.env.last_block_number() as Field;
    assert_eq(consume(w, w.executor, bound(w, 0, anchor)), (0, false));
    assert(!last_tx_has_nullifier(w.a, w.nullifier));
}

// B's proof expires one block above E's anchor block: still open, and A
// consumes the note.
#[test]
unconstrained fn proof_with_future_expiry_is_consumed() {
    let w = registered();
    let anchor = w.env.last_block_number() as Field;
    assert_eq(consume(w, w.executor, bound(w, 0, anchor + 1)), (VALUE, true));
    assert(last_tx_has_nullifier(w.a, w.nullifier));
}
