//! TXE tests of consume_with_nullification_proof_or's binding flags through
//! the driver's consume_with_proof: the owner's proof may name an
//! executor (A's msg_sender; 0 = anyone) and an expiry (A's anchor block
//! number must be below it; 0 = never), and a binding that does not admit
//! the call reads as ok = false with nothing pushed.
//!
//! The TXE does not check recursive proofs (the ACVM treats
//! RecursiveAggregation as a no-op), so the proof passed here is zeros
//! and the vk any array whose hash the call is given: these tests show
//! the flags in a real contract call (msg_sender, the anchor block, the
//! leaf's path in the TXE's note hash tree, the nullifier push). That bb
//! verifies a real bound proof only for the executor and expiry it was
//! made for is shown in examples/nullification_proof (make_fixture.py,
//! outer_check.py).

use crate::TotalAztecDriver;
use aztec::note::note_interface::{NoteHash, NoteType};
use aztec::oracle::capsules;
use aztec::oracle::get_membership_witness::get_note_hash_membership_witness;
use aztec::oracle::notes::notify_created_note;
use aztec::protocol::address::AztecAddress;
use aztec::protocol::constants::NULL_MSG_SENDER_CONTRACT_ADDRESS;
use aztec::protocol::hash::{
    compute_note_hash_nonce, compute_siloed_note_hash, compute_siloed_nullifier,
    compute_unique_note_hash, poseidon2_hash,
};
use aztec::protocol::traits::Packable;
use aztec::test::helpers::test_environment::TestEnvironment;
use aztec::test::helpers::txe_oracles;
use total_aztec::KeyNote;
use total_aztec::nullification_proof::NullificationProof;

global VALUE: Field = 7;
global NULLIFIER: Field = 0x5eed1;
global PIN: Field = 0x1;

unconstrained fn vk() -> [Field; 115] {
    let mut vk = [0; 115];
    for i in 0..115 {
        vk[i] = (i + 1) as Field;
    }
    vk
}

/// The driver, the owner, the executor E and another account, and one
/// leaf in the driver's note hash tree: one of owner's KeyNotes at
/// key_set's slot, created with fixed randomness (create_note's two
/// steps, the PXE notification and the note hash push), siloed and made
/// unique with the TXE's nonce (a private context's effects become one
/// transaction whose nonce generator is the protocol nullifier of
/// block_number + 9999, as in examples/nullification_proof's plant).
unconstrained fn setup() -> (TestEnvironment, AztecAddress, AztecAddress, AztecAddress, AztecAddress, Field) {
    let mut env = TestEnvironment::new();
    let d = env.deploy("TotalAztecDriver").without_initializer();
    let owner = env.create_light_account();
    let executor = env.create_light_account();
    let other = env.create_light_account();
    let slot = TotalAztecDriver::storage_layout().key_set.slot;
    let note = KeyNote { x: VALUE, y: 0 };
    let randomness = 0x5eed;
    let note_hash = note.compute_note_hash(owner, slot, randomness);
    let block = env.next_block_number();
    env.private_context_at(d, |context| {
        let counter = context.get_side_effect_counter();
        notify_created_note(
            owner,
            slot,
            randomness,
            KeyNote::get_id(),
            note.pack(),
            note_hash,
            counter,
        );
        context.push_note_hash(note_hash);
    });
    let protocol_nullifier =
        compute_siloed_nullifier(NULL_MSG_SENDER_CONTRACT_ADDRESS, (block + 9999) as Field);
    let nonce = compute_note_hash_nonce(protocol_nullifier, 0);
    let leaf = compute_unique_note_hash(nonce, compute_siloed_note_hash(d, note_hash));
    (env, d, owner, executor, other, leaf)
}

/// A handoff of leaf with the given binding, carrying the leaf's index
/// and sibling path at the latest block (the anchor of the next call),
/// fetched in a utility context, which mines no block. A leaf that is not
/// in the tree gets the witness of index 0, which does not prove it.
unconstrained fn handoff(
    env: TestEnvironment,
    d: AztecAddress,
    leaf: Field,
    executor: Field,
    expiry: Field,
) -> NullificationProof<1> {
    let (leaf_index, sibling_path) = env.utility_context_at(d, |context| {
        let w = get_note_hash_membership_witness(context.block_header(), leaf);
        (w.leaf_index, w.sibling_path)
    });
    NullificationProof::<1> {
        vk: vk(),
        proof: [0; 458],
        executor,
        expiry,
        fields: [VALUE],
        leaf,
        leaf_index,
        sibling_path,
        nullifier: NULLIFIER,
    }
}

unconstrained fn consume(
    env: TestEnvironment,
    d: AztecAddress,
    caller: AztecAddress,
    owner: AztecAddress,
    data: NullificationProof<1>,
) -> (Field, bool) {
    env.call_private(
        caller,
        TotalAztecDriver::at(d).consume_with_proof(owner, poseidon2_hash(vk()), PIN, data),
    )
}

unconstrained fn nullified(d: AztecAddress) -> bool {
    let siloed = compute_siloed_nullifier(d, NULLIFIER);
    let nullifiers = txe_oracles::get_last_tx_effects().nullifiers;
    let mut found = false;
    for i in 0..nullifiers.len() {
        if nullifiers.get(i) == siloed {
            found = true;
        }
    }
    found
}

// Unbound (executor = 0, expiry = 0): bearer consent, any caller.
#[test]
unconstrained fn unbound_proof_is_consumed_by_any_caller() {
    let (env, d, owner, _executor, other, leaf) = setup();
    assert_eq(consume(env, d, other, owner, handoff(env, d, leaf, 0, 0)), (VALUE, true));
    assert(nullified(d));
}

#[test]
unconstrained fn proof_bound_to_the_caller_is_consumed() {
    let (env, d, owner, executor, _other, leaf) = setup();
    assert_eq(
        consume(
            env,
            d,
            executor,
            owner,
            handoff(env, d, leaf, executor.inner, 0),
        ),
        (VALUE, true),
    );
    assert(nullified(d));
}

// The binding names E; another caller passing the same handoff gets a
// flag, and the note stays unspent; E's own call consumes it.
#[test]
unconstrained fn proof_bound_to_another_caller_is_a_flag() {
    let (env, d, owner, executor, other, leaf) = setup();
    assert_eq(
        consume(
            env,
            d,
            other,
            owner,
            handoff(env, d, leaf, executor.inner, 0),
        ),
        (0, false),
    );
    assert(!nullified(d));
    assert_eq(
        consume(
            env,
            d,
            executor,
            owner,
            handoff(env, d, leaf, executor.inner, 0),
        ),
        (VALUE, true),
    );
    assert(nullified(d));
}

// expiry = the anchor block number: the window closed (anchor < expiry
// fails), a flag with nothing pushed.
#[test]
unconstrained fn expiry_at_the_anchor_block_is_a_flag() {
    let (env, d, owner, executor, _other, leaf) = setup();
    let anchor = env.last_block_number();
    let data = handoff(env, d, leaf, 0, anchor as Field);
    assert_eq(consume(env, d, executor, owner, data), (0, false));
    assert(!nullified(d));
}

#[test]
unconstrained fn expiry_above_the_anchor_block_is_consumed() {
    let (env, d, owner, executor, _other, leaf) = setup();
    let anchor = env.last_block_number();
    let data = handoff(env, d, leaf, 0, (anchor + 1) as Field);
    assert_eq(consume(env, d, executor, owner, data), (VALUE, true));
    assert(nullified(d));
}

// expiry is a Field compared in canonical order: a value above every u32
// block number never closes, and both bindings together admit E.
#[test]
unconstrained fn expiry_beyond_u32_and_executor_together() {
    let (env, d, owner, executor, _other, leaf) = setup();
    let data = handoff(env, d, leaf, executor.inner, 0x100000000);
    assert_eq(consume(env, d, executor, owner, data), (VALUE, true));
    assert(nullified(d));
}

// Through an intermediate contract: the binding sees the intermediate
// contract (here the driver itself) as msg_sender. A proof bound to the
// account reads as a flag; one bound to the intermediate contract is
// consumed.
#[test]
unconstrained fn consume_through_another_contract() {
    let (env, d, owner, executor, _other, leaf) = setup();
    let relay =
        |data| TotalAztecDriver::at(d).relay_consume(owner, poseidon2_hash(vk()), PIN, data);
    assert_eq(
        env.call_private(executor, relay(handoff(env, d, leaf, executor.inner, 0))),
        (0, false),
    );
    assert(!nullified(d));
    assert_eq(env.call_private(executor, relay(handoff(env, d, leaf, d.inner, 0))), (VALUE, true));
    assert(nullified(d));
}

// A withheld handoff (all zeros) is a flag.
#[test]
unconstrained fn a_withheld_handoff_is_a_flag() {
    let (env, d, owner, executor, _other, _leaf) = setup();
    assert_eq(consume(env, d, executor, owner, NullificationProof::withheld()), (0, false));
    assert(!nullified(d));
}

// A leaf that is not in the tree, with the path of another position, and
// an index outside the tree: flags with nothing pushed. No oracle is
// asked (the PXE's witness oracle throws on an absent leaf).
#[test]
unconstrained fn an_absent_leaf_and_a_wrong_index_are_flags() {
    let (env, d, owner, executor, _other, leaf) = setup();
    let mut absent = handoff(env, d, leaf, 0, 0);
    absent.leaf = leaf + 1;
    assert_eq(consume(env, d, executor, owner, absent), (0, false));
    let mut wide = handoff(env, d, leaf, 0, 0);
    wide.leaf_index += 0x40000000000;
    assert_eq(consume(env, d, executor, owner, wide), (0, false));
    assert(!nullified(d));
    assert_eq(consume(env, d, executor, owner, handoff(env, d, leaf, 0, 0)), (VALUE, true));
}

/// A capsule slot of the driver (the bytes of "nullproof").
global CAPSULE_SLOT: Field = 0x6e756c6c70726f6f66;

// Capsules the class's own code stores (here the driver's address, as any
// of its functions could) in the global scope: one of another length
// (this test) and one of a handoff's shape with a leaf that is not in the
// tree (the next). A capsule read would stop on the first (next test but
// one) and take its data from the second; consume reads no capsule.
#[test]
unconstrained fn planted_capsules_are_not_read() {
    let (env, d, owner, executor, _other, leaf) = setup();
    env.private_context_at(d, |context| {
        capsules::store(
            context.this_address(),
            CAPSULE_SLOT,
            [1, 2, 3],
            AztecAddress::zero(),
        );
    });
    assert_eq(consume(env, d, executor, owner, handoff(env, d, leaf, 0, 0)), (VALUE, true));
}

#[test]
unconstrained fn a_planted_handoff_shaped_capsule_is_not_read() {
    let (env, d, owner, executor, _other, leaf) = setup();
    let mut planted = [0; 115 + 458 + 6];
    planted[115 + 458 + 3] = leaf + 1; // leaf
    planted[115 + 458 + 5] = 1;
    env.private_context_at(d, |context| {
        capsules::store(
            context.this_address(),
            CAPSULE_SLOT,
            planted,
            AztecAddress::zero(),
        );
    });
    assert_eq(consume(env, d, executor, owner, handoff(env, d, leaf, 0, 0)), (VALUE, true));
}

// Why a capsule cannot carry the handoff: the PXE returns a stored
// capsule at its stored length, so a read expecting another length stops
// witness generation, and class code can store one at any slot of its
// own contract.
#[test(should_fail_with = "Foreign call return value does not match expected size")]
unconstrained fn a_capsule_of_another_length_stops_its_reader() {
    let (env, d, _owner, _executor, _other, _leaf) = setup();
    env.private_context_at(d, |context| {
        capsules::store(
            context.this_address(),
            CAPSULE_SLOT,
            [1, 2, 3],
            AztecAddress::zero(),
        );
    });
    let _: Option<[Field; 5]> = env.private_context_at(d, |context| {
        capsules::load(context.this_address(), CAPSULE_SLOT, AztecAddress::zero())
    });
}

// A call that already holds 16 nullifiers: the consume's push would
// overflow the call's nullifiers, so ok = false and nothing is pushed.
#[test]
unconstrained fn a_call_without_room_for_the_nullifier_is_a_flag() {
    let (env, d, owner, executor, _other, leaf) = setup();
    let data = handoff(env, d, leaf, 0, 0);
    let call =
        TotalAztecDriver::at(d).consume_after_nullifiers(owner, poseidon2_hash(vk()), PIN, data);
    assert_eq(env.call_private(executor, call), (0, false));
    assert(!nullified(d));
}
