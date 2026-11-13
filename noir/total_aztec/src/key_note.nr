//! The note pattern for notes a non-owner must process.
//!
//! A note that other users' transactions read is state its owner
//! controls, so its contents are untrusted input to the reader's code.
//! (Who can read a note at all: note.nr's header.) Four rules make such a
//! note safe to read:
//!
//! 0. One note type per slot. The note hash carries no type id, so the
//!    PXE serves whatever note the class committed at the slot. The
//!    reads drop a note of another width, a non-canonical packing, and a
//!    note whose read request would name a note hash the kernel rejects
//!    (a settled note whose note hash the reader's type does not
//!    reproduce, a pending note whose note hash this call did not push)
//!    (note.nr, "Other notes at the slot" and "The note hash the read
//!    request names"; TXE tests in noir/total_aztec_driver,
//!    a_wide_note_at_a_key_note_slot_is_not_found and the tests after
//!    it). One case still fails the reader: a pending note wider than any
//!    message can carry, which only class code outside the #[note] macro
//!    can create; total-lint reports the call that creates one. One type
//!    per slot keeps every note readable.
//! 1. Field-only members, so unpack is the identity and has no assert. A
//!    bool member asserts inside the read's hint on a Field outside
//!    {0, 1} (total-lint reports it as an abort site of every reader);
//!    an integer member's non-canonical packing is dropped by the read.
//! 2. Decode with flags where the contents are used, never assert on
//!    them: here decode_or gives (point, ok) for a Grumpkin key.
//! 3. The all-zero packing must unpack, because note reads mask a missing
//!    note to it. Field-only notes satisfy this.
//!
//! Other notes follow the same shape: Field members and a decode_or that
//! returns typed values and a flag (total::convert has the conversions).

use aztec::{macros::notes::note, protocol::traits::Packable};
use total::ec::Point;

/// A note type that holds a key as two Fields, so key helpers can build
/// and read it without knowing its other members.
pub trait KeyFields {
    fn from_xy(x: Field, y: Field) -> Self;
    fn xy(self) -> (Field, Field);
}

/// A Grumpkin public key (x, y) in std's two-coordinate form. Owner and
/// randomness live in the note's metadata, as for every aztec-nr v6 note.
#[derive(Eq, Packable)]
#[note]
pub struct KeyNote {
    pub x: Field,
    pub y: Field,
}

impl KeyNote {
    /// The key as (point, ok); see keys::decode_key_or.
    pub fn decode_or(self) -> (Point, bool) {
        crate::keys::decode_key_or(self.x, self.y)
    }
}

impl KeyFields for KeyNote {
    fn from_xy(x: Field, y: Field) -> Self {
        KeyNote { x, y }
    }

    fn xy(self) -> (Field, Field) {
        (self.x, self.y)
    }
}

mod tests {
    use super::KeyNote;
    use aztec::protocol::traits::Packable;
    use std::embedded_curve_ops::{EmbeddedCurveScalar, fixed_base_scalar_mul};

    #[test]
    fn packing_is_the_identity_and_zero_unpacks() {
        let n = KeyNote { x: 5, y: 6 };
        assert_eq(n.pack(), [5, 6]);
        assert_eq(KeyNote::unpack([0, 0]), KeyNote { x: 0, y: 0 });
    }

    #[test]
    fn decode_flags_bad_keys() {
        let p = fixed_base_scalar_mul(EmbeddedCurveScalar::from_field(7));
        let (q, ok) = KeyNote { x: p.x, y: p.y }.decode_or();
        assert(ok);
        assert_eq((q.x, q.y), (p.x, p.y));
        let (_, bad) = KeyNote { x: p.x, y: p.y + 1 }.decode_or();
        assert(!bad);
        let (_, zero) = KeyNote { x: 0, y: 0 }.decode_or();
        assert(!zero);
    }
}
