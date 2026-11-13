//! TotalAztecDriver: one small function per total_aztec helper, for the
//! TXE tests and for running total-lint on each helper in a real contract
//! function. Not an application; every function is #[noinitcheck] except
//! the constructor, so that the tests control initialisation.

mod probe_notes;
mod test;
mod nullification_test;

use aztec::macros::aztec;

#[aztec]
pub contract TotalAztecDriver {
    use crate::probe_notes::{BoolNote, ByteNote, HugeNote, MisHashNote, TwoFaceNote, WideNote};
    use aztec::{
        macros::{functions::{external, initializer, noinitcheck}, storage::storage},
        messages::delivery::MessageDelivery,
        note::{lifecycle::create_note, note_getter::get_note, note_interface::NoteType},
        oracle::notes::notify_created_note,
        protocol::{address::AztecAddress, constants::NOTE_HASH_TREE_HEIGHT},
        state_vars::{
            DelayedPublicMutable, Owned, PrivateImmutable, PrivateMutable, PrivateSet,
            PublicImmutable, SinglePrivateImmutable, StateVariable,
        },
    };
    use total_aztec::{
        consume_with_nullification_proof_or,
        contract_is_initialized,
        delayed_public_mutable_read_or,
        GetNoteOr,
        GetNotesOr,
        KeyNote,
        note::{get_note_or, get_settled_note_from_witness_or},
        note_hash_exists_at_anchor,
        NullificationProof,
        public_immutable_is_initialized,
        public_immutable_read_or,
        refuse_bad_key,
        registered_npk_app_hash,
        set_key_or,
        single_private_immutable_get_note_or,
    };

    /// The delay of the driver's DelayedPublicMutable (the one-hour
    /// minimum).
    pub global DELAY: u64 = 3600;

    #[storage]
    struct Storage<Context> {
        immutable_key: Owned<PrivateImmutable<KeyNote, Context>, Context>,
        single_key: SinglePrivateImmutable<KeyNote, Context>,
        mutable_key: Owned<PrivateMutable<KeyNote, Context>, Context>,
        key_set: Owned<PrivateSet<KeyNote, Context>, Context>,
        public_immutable: PublicImmutable<Field, Context>,
        byte_note: Owned<PrivateImmutable<ByteNote, Context>, Context>,
        bool_note: Owned<PrivateImmutable<BoolNote, Context>, Context>,
        delayed: DelayedPublicMutable<Field, DELAY, Context>,
        bool_immutable: PublicImmutable<bool, Context>,
    }

    #[external("private")]
    #[initializer]
    fn constructor() {}

    // Readers: the code other users' transactions would run.

    #[external("private")]
    #[noinitcheck]
    fn read_immutable(owner: AztecAddress) -> (Field, Field, bool) {
        let (note, found) = self.storage.immutable_key.get_note_or(owner);
        (note.x, note.y, found)
    }

    #[external("private")]
    #[noinitcheck]
    fn read_single() -> (Field, Field, bool) {
        let (note, found) =
            single_private_immutable_get_note_or(self.context, self.storage.single_key);
        (note.x, note.y, found)
    }

    #[external("private")]
    #[noinitcheck]
    fn read_mutable(owner: AztecAddress) -> (Field, Field, bool) {
        let (note, found) = self.storage.mutable_key.get_note_or(owner);
        (note.x, note.y, found)
    }

    #[external("private")]
    #[noinitcheck]
    fn read_set(owner: AztecAddress) -> ([Field; 4], [bool; 4]) {
        let (notes, found): ([KeyNote; 4], [bool; 4]) = self.storage.key_set.get_notes_or(owner);
        (notes.map(|n: KeyNote| n.x), found)
    }

    /// A KeyNote read at any slot without an owner filter (as
    /// SinglePrivateImmutable reads), for the tests of other notes at a
    /// slot.
    #[external("private")]
    #[noinitcheck]
    fn read_at(slot: Field) -> (Field, Field, bool) {
        let (note, found): (KeyNote, bool) = get_note_or(self.context, Option::none(), slot);
        (note.x, note.y, found)
    }

    /// A read of a note with an integer member.
    #[external("private")]
    #[noinitcheck]
    fn read_byte(owner: AztecAddress) -> (Field, Field, bool) {
        let (note, found) = self.storage.byte_note.get_note_or(owner);
        (note.b as Field, note.f, found)
    }

    /// The settled KeyNote at mutable_key's slot read from arguments: the
    /// caller supplies the note's preimage, nonce and note hash tree
    /// witness, and found is determined by them and the anchor block.
    #[external("private")]
    #[noinitcheck]
    fn read_from_witness(
        owner: AztecAddress,
        x: Field,
        y: Field,
        randomness: Field,
        nonce: Field,
        leaf_index: Field,
        sibling_path: [Field; NOTE_HASH_TREE_HEIGHT],
    ) -> (Field, Field, bool) {
        let (note, found) = get_settled_note_from_witness_or(
            self.context,
            KeyNote { x, y },
            owner,
            self.storage.mutable_key.get_storage_slot(),
            randomness,
            nonce,
            leaf_index,
            sibling_path,
        );
        (note.x, note.y, found)
    }

    /// Whether leaf is in the anchor block's note hash tree at leaf_index
    /// with sibling_path: determined by the arguments, no oracle.
    #[external("private")]
    #[noinitcheck]
    fn note_exists(
        leaf: Field,
        leaf_index: Field,
        sibling_path: [Field; NOTE_HASH_TREE_HEIGHT],
    ) -> bool {
        note_hash_exists_at_anchor(self.context, leaf, leaf_index, sibling_path)
    }

    /// The flagged custom-note pattern: read the key note, decode it with
    /// flags, report whether it is usable.
    #[external("private")]
    #[noinitcheck]
    fn key_usable(owner: AztecAddress) -> bool {
        let (note, found) = self.storage.mutable_key.get_note_or(owner);
        let (_point, ok) = note.decode_or();
        found & ok
    }

    #[external("private")]
    #[noinitcheck]
    fn initialized() -> bool {
        contract_is_initialized(self.context)
    }

    #[external("private")]
    #[noinitcheck]
    fn public_immutable_initialized() -> bool {
        public_immutable_is_initialized(self.context, self.storage.public_immutable)
    }

    #[external("private")]
    #[noinitcheck]
    fn read_public_immutable() -> (Field, bool) {
        public_immutable_read_or(self.context, self.storage.public_immutable)
    }

    #[external("private")]
    #[noinitcheck]
    fn read_delayed() -> (Field, bool) {
        delayed_public_mutable_read_or(self.context, self.storage.delayed)
    }

    /// A third party's consume of owner's one-field note at key_set's
    /// slot with the owner's proof of nullification, passed by the caller
    /// as handoff: (value, ok). Driver only: the vk hash and the pin are
    /// arguments so the tests control them; an application pins the vk
    /// hash in its code and reads the pin from the owner's registration
    /// (examples/nullification_proof). The TXE does not check recursive
    /// proofs, so the driver's tests exercise the flags.
    #[external("private")]
    #[noinitcheck]
    fn consume_with_proof(
        owner: AztecAddress,
        vk_hash: Field,
        pin: Field,
        handoff: NullificationProof<1>,
    ) -> (Field, bool) {
        // total-lint: allow the recursive verification, predicated on ok: the handoff is this function's argument, so only its caller can pass a proof that does not verify, failing its own transaction
        let (fields, ok): ([Field; 1], bool) = consume_with_nullification_proof_or(
            self.context,
            handoff,
            vk_hash,
            pin,
            self.storage.key_set.get_storage_slot(),
            owner,
        );
        (fields[0], ok)
    }

    /// consume_with_proof reached through another contract (here the driver
    /// itself, so the msg_sender consume_with_proof sees is the driver's
    /// address, not the caller's account).
    #[external("private")]
    #[noinitcheck]
    fn relay_consume(
        owner: AztecAddress,
        vk_hash: Field,
        pin: Field,
        handoff: NullificationProof<1>,
    ) -> (Field, bool) {
        self.call(TotalAztecDriver::at(self.address).consume_with_proof(
            owner,
            vk_hash,
            pin,
            handoff,
        ))
    }

    // Writers: the owner's own transaction.

    /// Write-time refusal, then store (initialize or replace).
    #[external("private")]
    #[noinitcheck]
    fn set_key(x: Field, y: Field) {
        // total-lint: allow write-time refusal: set_key runs only in the owner's own transaction, whose sender chose the key
        refuse_bad_key(x, y, "key is not a finite curve point");
        // total-lint: allow the owner's own transaction: msg_sender is the owner's account
        let owner = self.msg_sender();
        // total-lint: allow aztec-nr's owner-side write and note delivery, in the owner's own transaction
        self.storage.mutable_key.at(owner).initialize_or_replace(|_old| KeyNote { x, y }).deliver(
            MessageDelivery::onchain_unconstrained(),
        );
    }

    /// The flag form: store only a good key and say whether it was stored.
    #[external("private")]
    #[noinitcheck]
    fn try_set_key(x: Field, y: Field) -> bool {
        // total-lint: allow the owner's own transaction: msg_sender is the owner's account
        let owner = self.msg_sender();
        // total-lint: allow aztec-nr's owner-side initialize_or_replace under ok: try_set_key runs only in the owner's own transaction, called by the owner's account
        let (message, ok) = set_key_or(self.storage.mutable_key, owner, x, y);
        // total-lint: allow aztec-nr's note delivery, in the owner's own transaction
        message.deliver(MessageDelivery::onchain_unconstrained());
        ok
    }

    #[external("public")]
    #[noinitcheck]
    fn init_public_immutable(value: Field) {
        self.storage.public_immutable.initialize(value);
    }

    #[external("public")]
    #[noinitcheck]
    fn schedule_delayed(value: Field) {
        self.storage.delayed.schedule_value_change(value);
    }

    #[external("public")]
    #[noinitcheck]
    fn init_bool_immutable(value: bool) {
        self.storage.bool_immutable.initialize(value);
    }

    // Uses of the library outside what it can make total, for the TXE
    // tests and for run.sh's check that total-lint reports each one.

    /// set_key_or for any owner: a call whose msg_sender is not owner is
    /// ok = false and writes nothing (TXE). The lint reports the
    /// owner-side write, which carries no marker here.
    #[external("private")]
    #[noinitcheck]
    fn set_key_for(owner: AztecAddress, x: Field, y: Field) -> bool {
        let (_message, ok) = set_key_or(self.storage.mutable_key, owner, x, y);
        ok
    }

    /// refuse_bad_key without a call-site marker: the lint reports its
    /// assert.
    #[external("private")]
    #[noinitcheck]
    fn unmarked_refuse(x: Field, y: Field) {
        refuse_bad_key(x, y, "key is not a finite curve point");
    }

    /// registered_npk_app_hash without a call-site marker, for an owner
    /// argument: in any PXE but owner's the key oracle throws; the lint
    /// reports it.
    #[external("private")]
    #[noinitcheck]
    fn unmarked_pin(owner: AztecAddress) -> Field {
        registered_npk_app_hash(self.context, owner)
    }

    /// consume_with_proof without the call-site marker: the lint reports
    /// the recursive verification.
    #[external("private")]
    #[noinitcheck]
    fn unmarked_consume(owner: AztecAddress, handoff: NullificationProof<1>) -> (Field, bool) {
        let (fields, ok): ([Field; 1], bool) = consume_with_nullification_proof_or(
            self.context,
            handoff,
            1,
            1,
            self.storage.key_set.get_storage_slot(),
            owner,
        );
        (fields[0], ok)
    }

    /// consume_with_proof in a call that already pushed 16 nullifiers
    /// (TXE: ok = false, the push would overflow).
    #[external("private")]
    #[noinitcheck]
    fn consume_after_nullifiers(
        owner: AztecAddress,
        vk_hash: Field,
        pin: Field,
        handoff: NullificationProof<1>,
    ) -> (Field, bool) {
        for i in 0..16 {
            self.context.push_nullifier_unsafe(0x5ee0 + i as Field);
        }
        let (fields, ok): ([Field; 1], bool) = consume_with_nullification_proof_or(
            self.context,
            handoff,
            vk_hash,
            pin,
            self.storage.key_set.get_storage_slot(),
            owner,
        );
        (fields[0], ok)
    }

    /// A PublicImmutable<bool> read: a directly written 2 with a matching
    /// hash makes the bool unpack assert; the lint reports it.
    #[external("private")]
    #[noinitcheck]
    fn read_bool_immutable() -> (bool, bool) {
        public_immutable_read_or(self.context, self.storage.bool_immutable)
    }

    // Class code a total contract must not contain, for the tests of
    // other notes at a slot (not linted by run.sh).

    /// A read of a note with a bool member: a KeyNote packing at its slot
    /// with a first Field outside {0, 1} makes the hint's unpack assert.
    #[external("private")]
    #[noinitcheck]
    fn read_bool(owner: AztecAddress) -> (bool, Field, bool) {
        let (note, found) = self.storage.bool_note.get_note_or(owner);
        (note.b, note.f, found)
    }

    /// Creates a WideNote at immutable_key's slot, then reads that slot
    /// in the same transaction (a pending note one Field wider).
    #[external("private")]
    #[noinitcheck]
    fn create_wide_then_read(owner: AztecAddress) -> (Field, Field, bool) {
        let slot = self.storage.immutable_key.get_storage_slot();
        let _ = create_note(self.context, owner, slot, WideNote { a: 1, b: 2, c: 3 });
        let (note, found): (KeyNote, bool) = get_note_or(self.context, Option::some(owner), slot);
        (note.x, note.y, found)
    }

    /// Creates a HugeNote (64 Fields, wider than any message can carry)
    /// at immutable_key's slot, then reads that slot in the same
    /// transaction.
    #[external("private")]
    #[noinitcheck]
    fn create_huge_then_read(owner: AztecAddress) -> (Field, Field, bool) {
        let slot = self.storage.immutable_key.get_storage_slot();
        let _ = create_note(self.context, owner, slot, HugeNote { f: [7; 64] });
        let (note, found): (KeyNote, bool) = get_note_or(self.context, Option::some(owner), slot);
        (note.x, note.y, found)
    }

    // Pending notes whose note hash the reader's type does not reproduce
    // (total_aztec note.nr, "The note hash the read request names"): each
    // creates the state in the reading call, by one route, then reads.

    /// A MisHashNote (KeyNote's width, hand-written NoteHash) at
    /// immutable_key's slot, read in the same call as a KeyNote.
    #[external("private")]
    #[noinitcheck]
    fn create_mishashed_then_read(owner: AztecAddress) -> (Field, Field, bool) {
        let slot = self.storage.immutable_key.get_storage_slot();
        let _ = create_note(self.context, owner, slot, MisHashNote { a: 5, b: 6 });
        let (note, found): (KeyNote, bool) = get_note_or(self.context, Option::some(owner), slot);
        (note.x, note.y, found)
    }

    /// The PXE told of a KeyNote {5, 6} at immutable_key's slot (a direct
    /// notify_created_note) while the call pushes another note hash, then
    /// a KeyNote read of the slot.
    #[external("private")]
    #[noinitcheck]
    fn notify_raw_then_read(owner: AztecAddress) -> (Field, Field, bool) {
        let slot = self.storage.immutable_key.get_storage_slot();
        let counter = self.context.get_side_effect_counter();
        notify_created_note(owner, slot, 9, KeyNote::get_id(), [5, 6], 0xbad, counter);
        self.context.push_note_hash(0xbad);
        let (note, found): (KeyNote, bool) = get_note_or(self.context, Option::some(owner), slot);
        (note.x, note.y, found)
    }

    /// A KeyNote at immutable_key's slot, read in the same call as a
    /// MisHashNote: one slot, two types, the reader's NoteHash
    /// hand-written.
    #[external("private")]
    #[noinitcheck]
    fn create_key_then_read_mishashed(owner: AztecAddress) -> (Field, Field, bool) {
        let slot = self.storage.immutable_key.get_storage_slot();
        let _ = create_note(self.context, owner, slot, KeyNote { x: 5, y: 6 });
        let (note, found): (MisHashNote, bool) =
            get_note_or(self.context, Option::some(owner), slot);
        (note.a, note.b, found)
    }

    /// A KeyNote created and read in the same call: found.
    #[external("private")]
    #[noinitcheck]
    fn create_key_then_read(owner: AztecAddress, x: Field, y: Field) -> (Field, Field, bool) {
        let slot = self.storage.immutable_key.get_storage_slot();
        let _ = create_note(self.context, owner, slot, KeyNote { x, y });
        let (note, found): (KeyNote, bool) = get_note_or(self.context, Option::some(owner), slot);
        (note.x, note.y, found)
    }

    /// Creates a KeyNote at immutable_key's slot.
    #[external("private")]
    #[noinitcheck]
    fn create_key(owner: AztecAddress, x: Field, y: Field) {
        let slot = self.storage.immutable_key.get_storage_slot();
        let _ = create_note(self.context, owner, slot, KeyNote { x, y });
    }

    /// A KeyNote created by a nested call, then read by the caller: a
    /// pending note this call did not push, so not found.
    #[external("private")]
    #[noinitcheck]
    fn create_key_in_callee_then_read(
        owner: AztecAddress,
        x: Field,
        y: Field,
    ) -> (Field, Field, bool) {
        self.call(TotalAztecDriver::at(self.address).create_key(owner, x, y));
        let slot = self.storage.immutable_key.get_storage_slot();
        let (note, found): (KeyNote, bool) = get_note_or(self.context, Option::some(owner), slot);
        (note.x, note.y, found)
    }

    /// immutable_key's slot read as a TwoFaceNote (its note hash is
    /// KeyNote's in the hint and another value in the circuit).
    #[external("private")]
    #[noinitcheck]
    fn read_two_face(owner: AztecAddress) -> (Field, Field, bool) {
        let slot = self.storage.immutable_key.get_storage_slot();
        let (note, found): (TwoFaceNote, bool) =
            get_note_or(self.context, Option::some(owner), slot);
        (note.x, note.y, found)
    }

    // aztec-nr's own getters in the same states, for contrast in the tests.

    /// aztec-nr's getter on create_mishashed_then_read's state: the note
    /// it read, and whether its read request names a note hash this call
    /// pushed (the kernel accepts a pending read request only then).
    #[external("private")]
    #[noinitcheck]
    fn aztec_create_mishashed_then_read(owner: AztecAddress) -> (Field, bool) {
        let slot = self.storage.immutable_key.get_storage_slot();
        let _ = create_note(self.context, owner, slot, MisHashNote { a: 5, b: 6 });
        let read = get_note::<KeyNote>(self.context, Option::some(owner), slot);
        let effects = (*self.context).finish();
        let request = effects.note_hash_read_requests.array[0].inner.inner;
        let mut named = false;
        for i in 0..16 {
            named |=
                (i < effects.note_hashes.length) & (effects.note_hashes.array[i].inner == request);
        }
        (read.note.x, named)
    }

    /// aztec-nr's getter reading immutable_key's slot as a TwoFaceNote.
    #[external("private")]
    #[noinitcheck]
    fn aztec_read_two_face(owner: AztecAddress) -> Field {
        let slot = self.storage.immutable_key.get_storage_slot();
        get_note::<TwoFaceNote>(self.context, Option::some(owner), slot).note.x
    }

    #[external("private")]
    #[noinitcheck]
    fn aztec_read_immutable(owner: AztecAddress) -> Field {
        self.storage.immutable_key.at(owner).get_note().x
    }

    #[external("private")]
    #[noinitcheck]
    fn aztec_read_public_immutable() -> Field {
        self.storage.public_immutable.read()
    }

    #[external("private")]
    #[noinitcheck]
    fn aztec_read_delayed() -> Field {
        self.storage.delayed.get_current_value()
    }
}
