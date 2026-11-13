//! Notes other than KeyNote at a KeyNote slot, used only by the TXE
//! tests of total_aztec's note reads (note.nr, "Other notes at the
//! slot" and "The note hash the read request names"): the note hash
//! carries no type id, so a class that creates one of these at a KeyNote
//! slot serves it to that slot's reader, and a KeyNote at a ByteNote or
//! BoolNote slot is a non-canonical packing for those. MisHashNote and
//! TwoFaceNote have KeyNote's width and hand-written note hashes that
//! differ from KeyNote's.

use aztec::{
    context::PrivateContext,
    macros::notes::note,
    note::note_interface::{NoteHash, NoteType},
    protocol::{address::AztecAddress, hash::poseidon2_hash, traits::{Packable, ToField}},
};
use total_aztec::KeyNote;

#[derive(Eq, Packable)]
#[note]
pub struct WideNote {
    pub a: Field,
    pub b: Field,
    pub c: Field,
}

#[derive(Eq, Packable)]
#[note]
pub struct NarrowNote {
    pub a: Field,
}

/// A note with an integer member: a KeyNote packing whose first Field is
/// 256 or more is a non-canonical packing for it.
#[derive(Eq, Packable)]
#[note]
pub struct ByteNote {
    pub b: u8,
    pub f: Field,
}

/// A note with a bool member: a KeyNote packing whose first Field is
/// outside {0, 1} makes its unpack assert.
#[derive(Eq, Packable)]
#[note]
pub struct BoolNote {
    pub b: bool,
    pub f: Field,
}

/// A note wider than any note a message can carry (the #[note] macro
/// refuses a packing over MAX_NOTE_PACKED_LEN Fields, so its NoteType and
/// NoteHash are written by hand), which class code can still create as a
/// pending note in its own transaction.
#[derive(Eq, Packable)]
pub struct HugeNote {
    pub f: [Field; 64],
}

impl NoteType for HugeNote {
    fn get_id() -> Field {
        0x4e6f7465
    }
}

impl NoteHash for HugeNote {
    fn compute_note_hash(
        self,
        owner: AztecAddress,
        storage_slot: Field,
        randomness: Field,
    ) -> Field {
        poseidon2_hash([self.f[0], owner.to_field(), storage_slot, randomness])
    }

    fn compute_nullifier(
        self,
        _context: &mut PrivateContext,
        _owner: AztecAddress,
        _note_hash_for_nullification: Field,
    ) -> Field {
        0
    }

    unconstrained fn compute_nullifier_unconstrained(
        self,
        _owner: AztecAddress,
        _note_hash_for_nullification: Field,
    ) -> Option<Field> {
        Option::none()
    }
}

/// KeyNote's width with a hand-written NoteHash that hashes the same
/// packing to another note hash: created at a KeyNote slot it is a
/// pending note whose Fields KeyNote hashes to a note hash nobody pushed,
/// and a KeyNote at a MisHashNote slot is the reverse.
#[derive(Eq, Packable)]
pub struct MisHashNote {
    pub a: Field,
    pub b: Field,
}

impl NoteType for MisHashNote {
    fn get_id() -> Field {
        0x6d6973
    }
}

impl NoteHash for MisHashNote {
    fn compute_note_hash(
        self,
        owner: AztecAddress,
        storage_slot: Field,
        randomness: Field,
    ) -> Field {
        poseidon2_hash(
            [self.a, self.b, owner.to_field(), storage_slot, randomness, 0x6d6973],
        )
    }

    fn compute_nullifier(
        self,
        _context: &mut PrivateContext,
        _owner: AztecAddress,
        _note_hash_for_nullification: Field,
    ) -> Field {
        0
    }

    unconstrained fn compute_nullifier_unconstrained(
        self,
        _owner: AztecAddress,
        _note_hash_for_nullification: Field,
    ) -> Option<Field> {
        Option::none()
    }
}

/// KeyNote's width with a note hash that is KeyNote's in Brillig (the
/// read's hint) and another value in ACIR (the circuit): a hint that
/// checks its note hash against the PXE checks one value and the circuit
/// requests another. Only the ACIR branch of is_unconstrained is compiled
/// into the circuit, so no compiled reader shows the difference.
#[derive(Eq, Packable)]
pub struct TwoFaceNote {
    pub x: Field,
    pub y: Field,
}

impl NoteType for TwoFaceNote {
    fn get_id() -> Field {
        0x2f
    }
}

impl NoteHash for TwoFaceNote {
    fn compute_note_hash(
        self,
        owner: AztecAddress,
        storage_slot: Field,
        randomness: Field,
    ) -> Field {
        let h = KeyNote { x: self.x, y: self.y }.compute_note_hash(owner, storage_slot, randomness);
        if std::runtime::is_unconstrained() {
            h
        } else {
            h + 1
        }
    }

    fn compute_nullifier(
        self,
        _context: &mut PrivateContext,
        _owner: AztecAddress,
        _note_hash_for_nullification: Field,
    ) -> Field {
        0
    }

    unconstrained fn compute_nullifier_unconstrained(
        self,
        _owner: AztecAddress,
        _note_hash_for_nullification: Field,
    ) -> Option<Field> {
        Option::none()
    }
}
