//! TXE tests for total_aztec, through the driver. Run with
//! `nargo test --oracle-resolver http://127.0.0.1:<port> test::` after
//! `bb aztec_process` on the compiled artifact (run.sh does both).

use crate::probe_notes::{NarrowNote, WideNote};
use crate::TotalAztecDriver;
use aztec::note::{
    HintedNote, lifecycle::create_note, note_getter_options::NoteStatus, note_interface::NoteHash,
};
use aztec::oracle::{get_membership_witness::get_note_hash_membership_witness, notes::get_notes};
use aztec::protocol::{
    address::AztecAddress,
    constants::NOTE_HASH_TREE_HEIGHT,
    hash::{compute_siloed_note_hash, compute_unique_note_hash},
    traits::Packable,
};
use aztec::test::helpers::test_environment::{CallPrivateOptions, TestEnvironment};
use std::embedded_curve_ops::{EmbeddedCurveScalar, fixed_base_scalar_mul};
use total_aztec::KeyNote;

unconstrained fn pk(sk: Field) -> (Field, Field) {
    let p = fixed_base_scalar_mul(EmbeddedCurveScalar::from_field(sk));
    (p.x, p.y)
}

/// Create a KeyNote at slot for owner as the driver itself, bypassing its
/// writers (the planted state stands for anything the state's owner could
/// have put there).
unconstrained fn plant(
    env: TestEnvironment,
    d: AztecAddress,
    owner: AztecAddress,
    slot: Field,
    x: Field,
    y: Field,
) {
    let message =
        env.private_context_at(d, |context| create_note(context, owner, slot, KeyNote { x, y }));
    env.discover_note_at(d, message);
}

unconstrained fn setup() -> (TestEnvironment, AztecAddress, AztecAddress) {
    let mut env = TestEnvironment::new();
    let d = env.deploy("TotalAztecDriver").without_initializer();
    let owner = env.create_light_account();
    (env, d, owner)
}

// Every reader on empty state: flags, zero values, no failure.
#[test]
unconstrained fn missing_notes_are_flags() {
    let (mut env, d, owner) = setup();
    assert_eq(
        env.call_private(owner, TotalAztecDriver::at(d).read_immutable(owner)),
        (0, 0, false),
    );
    assert_eq(env.call_private(owner, TotalAztecDriver::at(d).read_single()), (0, 0, false));
    assert_eq(env.call_private(owner, TotalAztecDriver::at(d).read_mutable(owner)), (0, 0, false));
    assert_eq(
        env.call_private(owner, TotalAztecDriver::at(d).read_set(owner)),
        ([0; 4], [false; 4]),
    );
    assert(!env.call_private(owner, TotalAztecDriver::at(d).key_usable(owner)));
}

// The same state through aztec-nr's getter fails the call.
#[test(should_fail_with = "Failed to get a note")]
unconstrained fn aztec_nr_getter_fails_on_the_same_state() {
    let (mut env, d, owner) = setup();
    let _ = env.call_private(owner, TotalAztecDriver::at(d).aztec_read_immutable(owner));
}

#[test]
unconstrained fn found_notes_are_read() {
    let (mut env, d, owner) = setup();
    let layout = TotalAztecDriver::storage_layout();
    let (x, y) = pk(0x1d7a);
    plant(env, d, owner, layout.immutable_key.slot, x, y);
    plant(env, d, d, layout.single_key.slot, x + 1, y);
    plant(env, d, owner, layout.mutable_key.slot, x, y);
    assert_eq(env.call_private(owner, TotalAztecDriver::at(d).read_immutable(owner)), (x, y, true));
    // The SinglePrivateImmutable note is owned by the driver itself, so
    // the reader needs the driver's keys in scope to hold it.
    assert_eq(
        env.call_private_opts(
            owner,
            CallPrivateOptions::new().with_additional_scopes([d]),
            TotalAztecDriver::at(d).read_single(),
        ),
        (x + 1, y, true),
    );
    assert_eq(env.call_private(owner, TotalAztecDriver::at(d).read_mutable(owner)), (x, y, true));
    assert(env.call_private(owner, TotalAztecDriver::at(d).key_usable(owner)));
}

// A reader without the owner's keys gets a flag. This is every
// third-party reader in production: a v6 PXE holds another owner's note
// only if it holds that owner's keys (note.nr, "Who can read at all").
#[test]
unconstrained fn a_third_party_without_the_note_gets_a_flag() {
    let (mut env, d, owner) = setup();
    let (x, y) = pk(0x1d7a);
    plant(
        env,
        d,
        owner,
        TotalAztecDriver::storage_layout().immutable_key.slot,
        x,
        y,
    );
    let reader = env.create_light_account();
    assert_eq(
        env.call_private(reader, TotalAztecDriver::at(d).read_immutable(owner)),
        (0, 0, false),
    );
    // With the owner's account in scope it reads the note. The TXE scope
    // grants the reader the owner's secrets (a shared-key setting such as
    // an escrow); it does not model delivery to a stranger.
    assert_eq(
        env.call_private_opts(
            reader,
            CallPrivateOptions::new().with_additional_scopes([owner]),
            TotalAztecDriver::at(d).read_immutable(owner),
        ),
        (x, y, true),
    );
}

// Another owner's note in the same slot is not returned, even to a
// reader granted that other owner's scope (keys).
#[test]
unconstrained fn the_owner_filter_holds() {
    let (mut env, d, owner) = setup();
    let other = env.create_light_account();
    let (x, y) = pk(0x1d7a);
    plant(
        env,
        d,
        other,
        TotalAztecDriver::storage_layout().immutable_key.slot,
        x,
        y,
    );
    assert_eq(
        env.call_private_opts(
            owner,
            CallPrivateOptions::new().with_additional_scopes([other]),
            TotalAztecDriver::at(d).read_immutable(owner),
        ),
        (0, 0, false),
    );
}

#[test]
unconstrained fn set_notes_are_flagged_one_by_one() {
    let (mut env, d, owner) = setup();
    let slot = TotalAztecDriver::storage_layout().key_set.slot;
    plant(env, d, owner, slot, 11, 0);
    plant(env, d, owner, slot, 12, 0);
    plant(env, d, owner, slot, 13, 0);
    let (xs, found) = env.call_private(owner, TotalAztecDriver::at(d).read_set(owner));
    assert_eq(found, [true, true, true, false]);
    assert_eq(xs[3], 0);
    assert_eq(xs[0] + xs[1] + xs[2], 36);
}

// A stored key that is off the curve or infinity reads as unusable.
#[test]
unconstrained fn bad_planted_keys_are_flagged() {
    let (mut env, d, owner) = setup();
    let slot = TotalAztecDriver::storage_layout().mutable_key.slot;
    let (x, y) = pk(0x1d7a);
    plant(env, d, owner, slot, x, y + 1);
    assert(!env.call_private(owner, TotalAztecDriver::at(d).key_usable(owner)));
    let other = env.create_light_account();
    plant(env, d, other, slot, 0, 0);
    assert(!env.call_private(other, TotalAztecDriver::at(d).key_usable(other)));
}

#[test]
unconstrained fn contract_initialisation_is_a_determined_flag() {
    let mut env = TestEnvironment::new();
    let caller = env.create_light_account();
    let fresh = env.deploy("TotalAztecDriver").without_initializer();
    assert(!env.call_private(caller, TotalAztecDriver::at(fresh).initialized()));
    let init = env.deploy("TotalAztecDriver").with_private_initializer(
        caller,
        TotalAztecDriver::interface().constructor(),
    );
    assert(env.call_private(caller, TotalAztecDriver::at(init).initialized()));
}

#[test]
unconstrained fn public_immutable_reads_from_private() {
    let (mut env, d, caller) = setup();
    assert(!env.call_private(caller, TotalAztecDriver::at(d).public_immutable_initialized()));
    assert_eq(
        env.call_private(caller, TotalAztecDriver::at(d).read_public_immutable()),
        (0, false),
    );
    env.call_public(caller, TotalAztecDriver::at(d).init_public_immutable(42));
    assert(env.call_private(caller, TotalAztecDriver::at(d).public_immutable_initialized()));
    assert_eq(
        env.call_private(caller, TotalAztecDriver::at(d).read_public_immutable()),
        (42, true),
    );
}

#[test(should_fail_with = "Trying to read from uninitialized PublicImmutable")]
unconstrained fn aztec_nr_public_immutable_read_fails_when_unset() {
    let (mut env, d, caller) = setup();
    let _ = env.call_private(caller, TotalAztecDriver::at(d).aztec_read_public_immutable());
}

#[test]
unconstrained fn set_key_or_writes_only_good_keys() {
    let (mut env, d, owner) = setup();
    let (x, y) = pk(0x1d7a);
    assert(!env.call_private(owner, TotalAztecDriver::at(d).try_set_key(x, y + 1)));
    assert_eq(env.call_private(owner, TotalAztecDriver::at(d).read_mutable(owner)), (0, 0, false));
    assert(!env.call_private(owner, TotalAztecDriver::at(d).try_set_key(0, 0)));
    assert(env.call_private(owner, TotalAztecDriver::at(d).try_set_key(x, y)));
    assert_eq(env.call_private(owner, TotalAztecDriver::at(d).read_mutable(owner)), (x, y, true));
    // a second good key replaces the first
    let (x2, y2) = pk(0x2b0b);
    assert(env.call_private(owner, TotalAztecDriver::at(d).try_set_key(x2, y2)));
    assert_eq(env.call_private(owner, TotalAztecDriver::at(d).read_mutable(owner)), (x2, y2, true));
}

#[test(should_fail_with = "key is not a finite curve point")]
unconstrained fn refuse_bad_key_fails_the_writer() {
    let (mut env, d, owner) = setup();
    let (x, y) = pk(0x1d7a);
    let _: () = env.call_private(owner, TotalAztecDriver::at(d).set_key(x, y + 1));
}

#[test]
unconstrained fn refuse_bad_key_passes_a_good_key() {
    let (mut env, d, owner) = setup();
    let (x, y) = pk(0x1d7a);
    let _: () = env.call_private(owner, TotalAztecDriver::at(d).set_key(x, y));
    assert(env.call_private(owner, TotalAztecDriver::at(d).key_usable(owner)));
}

// Other notes at a KeyNote slot (total_aztec note.nr, "Other notes at
// the slot"). The states are created by class code (the driver's own
// address planting notes, or a driver function creating one before its
// read); the hint drops every note it cannot read as a KeyNote, so the
// read is a flag, except where the tests say otherwise.

/// The PXE's first note at (contract d, slot), owner filter owner, as
/// aztec-nr's get_notes decodes it for a KeyNote read (no filter on the
/// layout).
unconstrained fn decoded_as_key_note(
    env: TestEnvironment,
    d: AztecAddress,
    owner: Option<AztecAddress>,
    slot: Field,
) -> HintedNote<KeyNote> {
    env.utility_context_at(d, |_| {
        let notes: [Option<HintedNote<KeyNote>>; 1] = get_notes(
            owner,
            slot,
            0,
            [],
            [],
            [],
            [],
            [],
            [],
            [],
            [],
            [],
            1,
            0,
            NoteStatus.ACTIVE,
        );
        notes[0].unwrap()
    })
}

// A settled note one Field wider at a KeyNote slot. aztec-nr's oracle
// call refuses it ("Array size exceeds target length"); the library asks
// for a wider return and drops it.
#[test]
unconstrained fn a_wide_note_at_a_key_note_slot_is_not_found() {
    let (mut env, d, owner) = setup();
    let slot = TotalAztecDriver::storage_layout().immutable_key.slot;
    let message = env.private_context_at(d, |context| {
        create_note(context, owner, slot, WideNote { a: 1, b: 2, c: 3 })
    });
    env.discover_note_at(d, message);
    assert_eq(
        env.call_private(owner, TotalAztecDriver::at(d).read_immutable(owner)),
        (0, 0, false),
    );
}

#[test(should_fail_with = "Array size exceeds target length")]
unconstrained fn aztec_nr_getter_refuses_a_wide_note() {
    let (mut env, d, owner) = setup();
    let slot = TotalAztecDriver::storage_layout().immutable_key.slot;
    let message = env.private_context_at(d, |context| {
        create_note(context, owner, slot, WideNote { a: 1, b: 2, c: 3 })
    });
    env.discover_note_at(d, message);
    let _ = env.call_private(owner, TotalAztecDriver::at(d).aztec_read_immutable(owner));
}

// The same, pending: created earlier in the reading transaction.
#[test]
unconstrained fn a_pending_wide_note_is_not_found() {
    let (mut env, d, owner) = setup();
    assert_eq(
        env.call_private(owner, TotalAztecDriver::at(d).create_wide_then_read(owner)),
        (0, 0, false),
    );
}

// The residual of the wider case: a pending note wider than
// MAX_NOTE_PACKED_LEN plus the reader's width, which only class code
// that bypasses the #[note] macro can create, makes the PXE refuse the
// return (HugeNote, 64 Fields).
#[test(should_fail_with = "Array size exceeds target length")]
unconstrained fn a_pending_note_wider_than_any_message_fails_the_reader() {
    let (mut env, d, owner) = setup();
    let _ = env.call_private(owner, TotalAztecDriver::at(d).create_huge_then_read(owner));
}

// Pending notes whose note hash the reader's type does not reproduce
// (total_aztec note.nr, "The note hash the read request names"), each
// created in the reading call by one route. The kernel accepts a pending
// read request only for a note hash the transaction pushed, so a read
// that offered these notes would name a note hash nobody pushed; the
// library reads each as not found.

// A hand-written NoteHash: a MisHashNote at a KeyNote slot.
#[test]
unconstrained fn a_pending_note_with_another_note_hash_is_not_found() {
    let (mut env, d, owner) = setup();
    assert_eq(
        env.call_private(owner, TotalAztecDriver::at(d).create_mishashed_then_read(owner)),
        (0, 0, false),
    );
}

// A raw notify_created_note of a KeyNote while another note hash is
// pushed.
#[test]
unconstrained fn a_raw_notified_pending_note_is_not_found() {
    let (mut env, d, owner) = setup();
    assert_eq(
        env.call_private(owner, TotalAztecDriver::at(d).notify_raw_then_read(owner)),
        (0, 0, false),
    );
}

// One slot, two types: a KeyNote read as a MisHashNote.
#[test]
unconstrained fn a_pending_note_read_as_another_type_is_not_found() {
    let (mut env, d, owner) = setup();
    assert_eq(
        env.call_private(owner, TotalAztecDriver::at(d).create_key_then_read_mishashed(owner)),
        (0, 0, false),
    );
}

// Why: aztec-nr's getter in the first state reads the MisHashNote's
// Fields as a KeyNote and pushes a read request for KeyNote's note hash
// of them, which this call never pushed. The private kernel's tail
// rejects such a transaction ("Non empty note hash read requests"); the
// TXE's simulated kernel leaves an unmatched pending read request
// unchecked, so the driver function reports whether the request names a
// pushed note hash.
#[test]
unconstrained fn aztec_nr_getter_names_an_unpushed_note_hash() {
    let (mut env, d, owner) = setup();
    assert_eq(
        env.call_private(owner, TotalAztecDriver::at(d).aztec_create_mishashed_then_read(owner)),
        (5, false),
    );
}

// A note the reading call created itself is found; one created by a
// nested call is not: no oracle exposes another call's note hashes, so
// the library cannot tell it from the states above.
#[test]
unconstrained fn a_pending_note_is_found_only_in_the_call_that_created_it() {
    let (mut env, d, owner) = setup();
    assert_eq(
        env.call_private(owner, TotalAztecDriver::at(d).create_key_then_read(owner, 5, 6)),
        (5, 6, true),
    );
    assert_eq(
        env.call_private(owner, TotalAztecDriver::at(d).create_key_in_callee_then_read(owner, 5, 6)),
        (0, 0, false),
    );
}

// A note hash that differs between the hint and the circuit (TwoFaceNote:
// KeyNote's in Brillig, another value in ACIR), on a settled KeyNote: the
// hint finds KeyNote's note hash among the PXE's settled notes, the
// circuit would request the other one. The library reads it as not
// found; aztec-nr's getter requests the other note hash and the read
// request fails.
#[test]
unconstrained fn a_note_hash_that_differs_in_the_circuit_is_not_found() {
    let (mut env, d, owner) = setup();
    plant(
        env,
        d,
        owner,
        TotalAztecDriver::storage_layout().immutable_key.slot,
        5,
        6,
    );
    assert_eq(env.call_private(owner, TotalAztecDriver::at(d).read_two_face(owner)), (0, 0, false));
}

#[test(should_fail_with = "is reading an unknown note hash")]
unconstrained fn aztec_nr_getter_fails_on_a_note_hash_that_differs_in_the_circuit() {
    let (mut env, d, owner) = setup();
    plant(
        env,
        d,
        owner,
        TotalAztecDriver::storage_layout().immutable_key.slot,
        5,
        6,
    );
    let _ = env.call_private(owner, TotalAztecDriver::at(d).aztec_read_two_face(owner));
}

// A narrower note misaligns the hint, so its contract address does not
// match.
#[test]
unconstrained fn a_narrow_note_at_a_key_note_slot_is_not_found() {
    let (mut env, d, owner) = setup();
    let slot = TotalAztecDriver::storage_layout().mutable_key.slot;
    let message =
        env.private_context_at(d, |context| create_note(context, owner, slot, NarrowNote { a: 1 }));
    env.discover_note_at(d, message);
    assert_eq(env.call_private(owner, TotalAztecDriver::at(d).read_mutable(owner)), (0, 0, false));
}

// The aligned case: a one-Field note owned by the driver itself, settled
// at storage slot 3, read at slot 3 without an owner filter. Decoded as
// aztec-nr decodes it, its contract and slot match (the owner lands in
// the contract position, the stage code 3 in the slot position), so a
// read that trusted the decoding would emit a read request for a note
// hash that does not exist. The library's hint drops it.
#[test]
unconstrained fn a_narrow_contract_owned_note_at_its_stage_code_is_not_found() {
    let (mut env, d, owner) = setup();
    let slot = 3;
    let message =
        env.private_context_at(d, |context| create_note(context, d, slot, NarrowNote { a: 1 }));
    env.discover_note_at(d, message);
    let shifted = decoded_as_key_note(env, d, Option::none(), slot);
    assert_eq(shifted.contract_address, d);
    assert_eq(shifted.storage_slot, slot);
    assert_eq(
        env.call_private_opts(
            owner,
            CallPrivateOptions::new().with_additional_scopes([d]),
            TotalAztecDriver::at(d).read_at(slot),
        ),
        (0, 0, false),
    );
}

// A KeyNote at a ByteNote slot (an integer member): with a first Field of
// 256 or more it is a non-canonical packing for ByteNote, which would
// unpack by truncation to a note hash nobody committed; the hint drops
// it. With a first Field below 256 it is ByteNote's canonical packing,
// and (the derived note hash carrying no type id) the same note hash, so
// it is found.
#[test]
unconstrained fn a_non_canonical_packing_is_not_found() {
    let (mut env, d, owner) = setup();
    let slot = TotalAztecDriver::storage_layout().byte_note.slot;
    plant(env, d, owner, slot, 0x105, 6);
    assert_eq(env.call_private(owner, TotalAztecDriver::at(d).read_byte(owner)), (0, 0, false));
    let other = env.create_light_account();
    plant(env, d, other, slot, 5, 6);
    assert_eq(env.call_private(other, TotalAztecDriver::at(d).read_byte(other)), (5, 6, true));
}

// The residual of the typed-member case: a bool member outside {0, 1}
// asserts in Note::unpack inside the hint, before any filter can look at
// the note. total-lint reports that assert as an abort site of every
// function that reads such a note (README, "The lint").
#[test(should_fail_with = "bool field must be 0 or 1")]
unconstrained fn a_non_boolean_bool_member_fails_the_reader() {
    let (mut env, d, owner) = setup();
    let slot = TotalAztecDriver::storage_layout().bool_note.slot;
    plant(env, d, owner, slot, 2, 6);
    let _ = env.call_private(owner, TotalAztecDriver::at(d).read_bool(owner));
}

/// The randomness, nonce and note hash tree witness of owner's first
/// KeyNote at slot, at the latest block: what a caller of
/// read_from_witness fetches off the circuit (here from its PXE, in a
/// utility context, which mines no block).
unconstrained fn witness_of(
    env: TestEnvironment,
    d: AztecAddress,
    owner: AztecAddress,
    slot: Field,
) -> (Field, Field, Field, [Field; NOTE_HASH_TREE_HEIGHT]) {
    let hinted = decoded_as_key_note(env, d, Option::some(owner), slot);
    let nonce = hinted.metadata.pack()[1];
    env.utility_context_at(d, |context| {
        let note_hash = hinted.note.compute_note_hash(owner, slot, hinted.randomness);
        let leaf = compute_unique_note_hash(nonce, compute_siloed_note_hash(d, note_hash));
        let witness = get_note_hash_membership_witness(context.block_header(), leaf);
        (hinted.randomness, nonce, witness.leaf_index, witness.sibling_path)
    })
}

// The settled read from arguments: found is fixed by the preimage, the
// nonce and the witness the caller passes, against the anchor block's
// note hash tree root; a wrong nonce, index or path is found = false.
#[test]
unconstrained fn a_settled_note_is_read_from_its_witness() {
    let (mut env, d, owner) = setup();
    let slot = TotalAztecDriver::storage_layout().mutable_key.slot;
    let (x, y) = pk(0x1d7a);
    plant(env, d, owner, slot, x, y);
    let (r, nonce, index, path) = witness_of(env, d, owner, slot);
    let read = |x2: Field, nonce2: Field, index2: Field, path2: [Field; NOTE_HASH_TREE_HEIGHT]| {
        env.call_private(
            owner,
            TotalAztecDriver::at(d).read_from_witness(owner, x2, y, r, nonce2, index2, path2),
        )
    };
    assert_eq(read(x, nonce, index, path), (x, y, true));
    // each call mines a block, so take a fresh witness before each read
    let (_, _, index, path) = witness_of(env, d, owner, slot);
    assert_eq(read(x, nonce + 1, index, path), (0, 0, false));
    let (_, _, index, path) = witness_of(env, d, owner, slot);
    assert_eq(read(x, nonce, index + 1, path), (0, 0, false));
    let (_, _, index, path) = witness_of(env, d, owner, slot);
    let mut bad = path;
    bad[0] = bad[0] + 1;
    assert_eq(read(x, nonce, index, bad), (0, 0, false));
    let (_, _, index, path) = witness_of(env, d, owner, slot);
    assert_eq(read(x + 1, nonce, index, path), (0, 0, false));
}

// With two active notes at one slot, get_note_or returns the PXE's first:
// here the bad key planted first, so key_usable is false although a good
// key is stored too. get_notes_or returns both and lets the reader choose.
#[test]
unconstrained fn with_two_notes_at_a_slot_the_first_one_is_read() {
    let (mut env, d, owner) = setup();
    let layout = TotalAztecDriver::storage_layout();
    let (x, y) = pk(0x1d7a);
    plant(env, d, owner, layout.mutable_key.slot, x, y + 1);
    plant(env, d, owner, layout.mutable_key.slot, x, y);
    assert_eq(
        env.call_private(owner, TotalAztecDriver::at(d).read_mutable(owner)),
        (x, y + 1, true),
    );
    assert(!env.call_private(owner, TotalAztecDriver::at(d).key_usable(owner)));
    plant(env, d, owner, layout.key_set.slot, x, y + 1);
    plant(env, d, owner, layout.key_set.slot, x, y);
    let (xs, found) = env.call_private(owner, TotalAztecDriver::at(d).read_set(owner));
    assert_eq(found, [true, true, false, false]);
    assert_eq(xs, [x, x, 0, 0]);
}

// note_hash_exists_at_anchor in a contract call: a planted note's leaf on
// its own witness is true; a leaf that is not in the tree, with that
// witness or an index outside the tree, is false. Nothing asks an oracle,
// so an absent leaf cannot stop the call (the PXE's witness oracle
// throws on an absent leaf).
#[test]
unconstrained fn note_existence_at_the_anchor_is_a_flag() {
    let (mut env, d, owner) = setup();
    let slot = TotalAztecDriver::storage_layout().mutable_key.slot;
    let (x, y) = pk(0x1d7a);
    plant(env, d, owner, slot, x, y);
    let leaf_of = |r: Field, nonce: Field| {
        let note_hash = KeyNote { x, y }.compute_note_hash(owner, slot, r);
        compute_unique_note_hash(nonce, compute_siloed_note_hash(d, note_hash))
    };
    let (r, nonce, index, path) = witness_of(env, d, owner, slot);
    let leaf = leaf_of(r, nonce);
    assert(env.call_private(owner, TotalAztecDriver::at(d).note_exists(leaf, index, path)));
    let (_, _, index, path) = witness_of(env, d, owner, slot);
    assert(!env.call_private(owner, TotalAztecDriver::at(d).note_exists(leaf + 1, index, path)));
    let (_, _, index, path) = witness_of(env, d, owner, slot);
    assert(
        !env.call_private(
            owner,
            TotalAztecDriver::at(d).note_exists(leaf, index + 0x40000000000, path),
        ),
    );
}

// set_key_or called by a contract for an owner other than its caller:
// ok = false, nothing written. (Run, the write would ask the key oracle
// for another account's key, which stops the call.)
#[test]
unconstrained fn set_key_or_for_another_owner_is_a_flag() {
    let (mut env, d, owner) = setup();
    let other = env.create_light_account();
    let (x, y) = pk(0x1d7a);
    assert(!env.call_private(owner, TotalAztecDriver::at(d).set_key_for(other, x, y)));
    assert_eq(env.call_private(other, TotalAztecDriver::at(d).read_mutable(other)), (0, 0, false));
    // For the caller's own account it writes (set_key_for does not
    // deliver the note, so it is not read back here).
    assert(env.call_private(owner, TotalAztecDriver::at(d).set_key_for(owner, x, y)));
}

// registered_npk_app_hash for an owner other than the executor: the key
// oracle throws, and no flag can replace it. This is why the function
// carries no lint marker and its call sites must justify it.
#[test(should_fail_with = "Key validation request denied")]
unconstrained fn the_pin_registration_fails_outside_the_owners_own_transaction() {
    let (mut env, d, owner) = setup();
    let other = env.create_light_account();
    let _ = env.call_private(owner, TotalAztecDriver::at(d).unmarked_pin(other));
}

/// Write values to the driver's public storage from slot on, directly, as
/// any public function of its class could.
unconstrained fn write_directly<let N: u32>(
    env: TestEnvironment,
    d: AztecAddress,
    slot: Field,
    values: [Field; N],
) {
    env.public_context_at(d, |context| context.storage_write(slot, values));
}

// A PublicImmutable whose value slot the class overwrote after
// initialize, so the stored hash does not match it, and a value written
// with no hash: both read as flags. aztec-nr's read asserts its hint
// against the hash and stops the call (next test).
#[test]
unconstrained fn a_directly_written_public_immutable_is_a_flag() {
    let (mut env, d, caller) = setup();
    let slot = TotalAztecDriver::storage_layout().public_immutable.slot;
    write_directly(env, d, slot, [41]);
    assert_eq(
        env.call_private(caller, TotalAztecDriver::at(d).read_public_immutable()),
        (0, false),
    );
    env.call_public(caller, TotalAztecDriver::at(d).init_public_immutable(42));
    write_directly(env, d, slot, [43]);
    assert_eq(
        env.call_private(caller, TotalAztecDriver::at(d).read_public_immutable()),
        (0, false),
    );
}

#[test(should_fail_with = "Hint values do not match hash")]
unconstrained fn aztec_nr_public_immutable_read_fails_on_a_direct_write() {
    let (mut env, d, caller) = setup();
    let slot = TotalAztecDriver::storage_layout().public_immutable.slot;
    env.call_public(caller, TotalAztecDriver::at(d).init_public_immutable(42));
    write_directly(env, d, slot, [43]);
    let _ = env.call_private(caller, TotalAztecDriver::at(d).aztec_read_public_immutable());
}

// The delayed read on states the variable's own functions produce: never
// written, a change scheduled, the change in effect.
#[test]
unconstrained fn delayed_reads_follow_the_schedule() {
    let (mut env, d, caller) = setup();
    assert_eq(env.call_private(caller, TotalAztecDriver::at(d).read_delayed()), (0, true));
    env.call_public(caller, TotalAztecDriver::at(d).schedule_delayed(5));
    assert_eq(env.call_private(caller, TotalAztecDriver::at(d).read_delayed()), (0, true));
    assert_eq(env.call_private(caller, TotalAztecDriver::at(d).aztec_read_delayed()), 0);
    env.advance_next_block_timestamp_by(TotalAztecDriver::DELAY + 1);
    env.mine_block();
    assert_eq(env.call_private(caller, TotalAztecDriver::at(d).read_delayed()), (5, true));
    assert_eq(env.call_private(caller, TotalAztecDriver::at(d).aztec_read_delayed()), 5);
}

use aztec::protocol::delayed_public_mutable::{
    DelayedPublicMutableValues, ScheduledDelayChange, ScheduledValueChange,
};
use aztec::protocol::hash::poseidon2_hash;

/// The driver's delayed value slots and hash, as aztec-nr writes them, for
/// a value change to post at timestamp and a delay change.
unconstrained fn delayed_slots(post: Field, delay_post: Option<u64>) -> [Field; 4] {
    let packed = DelayedPublicMutableValues::<Field, TotalAztecDriver::DELAY>::new(
        ScheduledValueChange::new(0, post, 1),
        ScheduledDelayChange::new(Option::some(3600), delay_post, 1),
    )
        .pack();
    [packed[0], packed[1], packed[2], poseidon2_hash(packed)]
}

// States only direct writes make: a value slot changed after the hash,
// and a consistent state holding a delay of 0. The total read is a flag
// in both; aztec-nr's read stops the call (the next two tests).
#[test]
unconstrained fn directly_written_delayed_states_are_flags() {
    let (mut env, d, caller) = setup();
    let slot = TotalAztecDriver::storage_layout().delayed.slot;
    let mut mismatched = delayed_slots(7, Option::some(3600));
    mismatched[2] = 8;
    write_directly(env, d, slot, mismatched);
    assert_eq(env.call_private(caller, TotalAztecDriver::at(d).read_delayed()), (0, false));
    write_directly(env, d, slot, delayed_slots(7, Option::some(0)));
    assert_eq(env.call_private(caller, TotalAztecDriver::at(d).read_delayed()), (0, false));
    write_directly(env, d, slot, delayed_slots(7, Option::some(3600)));
    assert_eq(env.call_private(caller, TotalAztecDriver::at(d).read_delayed()), (7, true));
}

#[test(should_fail_with = "Hint values do not match hash")]
unconstrained fn aztec_nr_delayed_read_fails_on_a_mismatched_hash() {
    let (mut env, d, caller) = setup();
    let slot = TotalAztecDriver::storage_layout().delayed.slot;
    let mut mismatched = delayed_slots(7, Option::some(3600));
    mismatched[2] = 8;
    write_directly(env, d, slot, mismatched);
    let _ = env.call_private(caller, TotalAztecDriver::at(d).aztec_read_delayed());
}

#[test(should_fail_with = "attempt to subtract with overflow")]
unconstrained fn aztec_nr_delayed_read_fails_on_a_zero_delay() {
    let (mut env, d, caller) = setup();
    let slot = TotalAztecDriver::storage_layout().delayed.slot;
    write_directly(env, d, slot, delayed_slots(7, Option::some(0)));
    let _ = env.call_private(caller, TotalAztecDriver::at(d).aztec_read_delayed());
}

use aztec::hash::hash_args;
use aztec::protocol::abis::{gas::Gas, gas_fees::GasFees, gas_settings::GasSettings};
use aztec::protocol::constants::{MAX_PROCESSABLE_DA_GAS_PER_CHECKPOINT, MAX_PROCESSABLE_L2_GAS};
use aztec::protocol::traits::Empty;
use aztec::test::helpers::txe_oracles;

/// Deploy a TotalAztecDriver instance whose initializer is its private
/// constructor, with no deployer (anyone may initialise it), and call the
/// constructor from from (none: the call is the transaction's first, with
/// no msg_sender, as when an account-less transaction initialises it).
unconstrained fn initialise_with_deployer_zero(from: Option<AztecAddress>) {
    let mut env = TestEnvironment::new();
    let deployment = env.deploy("TotalAztecDriver");
    let call = TotalAztecDriver::interface().constructor();
    let instance = txe_oracles::deploy(
        deployment.path,
        call.name,
        call.args,
        deployment.secret,
        deployment.salt,
        AztecAddress::zero(),
        deployment.immutables_hash,
    );
    let gas = GasSettings::new(
        Gas::new(
            MAX_PROCESSABLE_DA_GAS_PER_CHECKPOINT,
            MAX_PROCESSABLE_L2_GAS,
        ),
        Gas::new(
            MAX_PROCESSABLE_DA_GAS_PER_CHECKPOINT / 8,
            MAX_PROCESSABLE_L2_GAS / 8,
        ),
        GasFees::empty(),
        GasFees::empty(),
    );
    let from = if from.is_some() {
        Option::some(env.create_light_account())
    } else {
        Option::none()
    };
    let _: [Field; 0] = txe_oracles::private_call_new_flow(
        from,
        instance.to_address(),
        call.selector,
        call.args,
        hash_args(call.args),
        false,
        [],
        [],
        gas,
    );
}

// aztec-nr's private initializer check with no deployer, called from an
// account: passes.
#[test]
unconstrained fn a_private_constructor_with_no_deployer_runs_for_an_account() {
    initialise_with_deployer_zero(Option::some(AztecAddress::zero()));
}

// The same constructor as the transaction's first call (no msg_sender):
// initialization_utils.nr's deployer check evaluates
// maybe_msg_sender().unwrap() even when the deployer is zero (`|` does
// not short-circuit), and the unwrap's assert has no witness, so it
// fails whatever the deployer is.
#[test(should_fail_with = "Cannot satisfy constraint")]
unconstrained fn a_private_constructor_as_the_first_call_fails_even_with_no_deployer() {
    initialise_with_deployer_zero(Option::none());
}
