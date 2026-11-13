//! Grumpkin keys: flags at read time, refusal at write time.
//!
//! The hazard. A key that is not a finite curve point makes every later
//! use of it fail: std's MSM and point-addition black boxes stop witness
//! generation on an off-curve point ("is not on curve"), and the Aztec v6
//! Schnorr account contract stores its signing key unchecked, so an
//! off-curve key there bricks the account. Whoever stores the key (the
//! state's owner) chooses whether later readers fail. An on-curve key can
//! fail too where it reaches std's MSM black box directly: bb 6.0.0's
//! gadget has no proof for a base in a known relation to its public
//! offset generators (total::ec::msm_or lists the cases).
//! total::ec::msm_or and total::schnorr_verify blind the bases and have a
//! proof for every on-curve key.
//!
//! The pattern. Refuse a bad key where it is written (in the writer's own
//! transaction, where refusal is the point), and still flag it where it
//! is read (the store may hold notes written by other code, or planted).
//! Keys travel as two Fields in std's two-coordinate form, where (0, 0)
//! is the point at infinity; every helper below refuses infinity as a key.

use crate::key_note::KeyFields;
use aztec::context::PrivateContext;
use aztec::note::{MaybeNoteMessage, note_interface::{NoteHash, NoteType}};
use aztec::protocol::{address::AztecAddress, traits::Packable};
use aztec::state_vars::{Owned, PrivateMutable};
use total::ec::{decode_xy_or, on_curve_flag, Point};

/// Flag: (x, y) is a finite Grumpkin point, i.e. y^2 = x^3 - 17. The
/// point at infinity, (0, 0) in std's form, is not on the curve, so it is
/// refused too.
///
/// Constraints: total::ec::on_curve_flag (arithmetic definitions and one
/// eq gadget, hint-satisfiable for every input). Determined.
pub fn key_ok(x: Field, y: Field) -> bool {
    on_curve_flag(x, y)
}

/// Decode a key as (point, ok). ok is key_ok(x, y); on ok = false the
/// point is infinity, so it can be fed to total::ec code (and to msm_or)
/// without a failure source.
///
/// Constraints: total::ec::decode_xy_or (two is_zero gadgets,
/// on_curve_flag, one Point select) and one bool product. Hint-satisfiable
/// for every input; determined.
pub fn decode_key_or(x: Field, y: Field) -> (Point, bool) {
    let (p, ok) = decode_xy_or(x, y);
    (p, ok & !p.inf)
}

/// Write-time refusal: fail the current transaction unless (x, y) is a
/// finite curve point.
///
/// Constraints: key_ok and one assert on it. The assert is
/// input-falsifiable on purpose: it fails the writer's own transaction
/// (a deployer's constructor, an owner's key rotation), whose sender chose
/// the key, instead of storing a key that every later reader would have
/// to flag. Do not call it in code other users' transactions run.
///
/// It carries no lint marker, because whether the assert is acceptable
/// depends on who runs the calling function: total-lint reports it in
/// every function that calls it, and each call site justifies it with a
/// total-lint justification marker stating that the function runs only in the
/// writer's own transaction.
///
/// DEV DECISION: refusing (this) or skipping the write and returning a
/// flag (set_key_or). Refusal is right where the writer is the one who
/// supplied the key; the flag form is for writes inside a transaction
/// whose sender must not be failable by the key.
pub fn refuse_bad_key<let N: u32>(x: Field, y: Field, message: str<N>) {
    assert(key_ok(x, y), message);
}

/// Store the key (x, y) in owner's PrivateMutable only when it is a
/// finite curve point and owner is this call's msg_sender: (message, ok).
/// On ok = true the variable is initialised or replaced through
/// aztec-nr's initialize_or_replace and the message carries the new note;
/// on ok = false nothing is written and the message is empty. Deliver the
/// message as usual.
///
/// Constraints: key_ok; the msg_sender comparison (maybe_msg_sender, no
/// unwrap, and an eq gadget); under the predicate ok, everything
/// initialize_or_replace emits. That part is owner-side and not total: it
/// asks the PXE's key oracle for owner's nullifier hiding key (the oracle
/// throws unless the executing PXE holds owner's keys in scope), branches
/// on an unconstrained "initialised" hint, and when initialised reads the
/// old note with aztec-nr's get_note, which traps when the executing PXE
/// does not hold it. The msg_sender term turns the plainest misuse, a
/// call for an owner other than the caller, into ok = false; it cannot
/// show that the executing PXE is owner's (msg_sender is the immediate
/// caller, which may be a contract). So set_key_or carries no lint
/// marker: total-lint reports what initialize_or_replace emits in every
/// function that calls it, and each call site justifies it with a
/// total-lint justification marker stating that the function runs only in
/// owner's own transaction, called directly by owner's account. The flag
/// is determined.
pub fn set_key_or<Note>(
    var: Owned<PrivateMutable<Note, &mut PrivateContext>, &mut PrivateContext>,
    owner: AztecAddress,
    x: Field,
    y: Field,
) -> (MaybeNoteMessage<Note>, bool)
where
    Note: NoteType + NoteHash + Packable + KeyFields,
{
    let sender = var.context.maybe_msg_sender();
    let from_owner = sender.is_some() & (sender.unwrap_unchecked() == owner);
    let ok = key_ok(x, y) & from_owner;
    let mut maybe = Option::none();
    if ok {
        let message = var.at(owner).initialize_or_replace(|_old| Note::from_xy(x, y));
        maybe = Option::some(message.get_new_note());
    }
    (MaybeNoteMessage::new(maybe, var.context), ok)
}

mod tests {
    use super::{decode_key_or, key_ok, refuse_bad_key};
    use std::embedded_curve_ops::{EmbeddedCurveScalar, fixed_base_scalar_mul};

    fn pk(sk: Field) -> (Field, Field) {
        let p = fixed_base_scalar_mul(EmbeddedCurveScalar::from_field(sk));
        (p.x, p.y)
    }

    #[test]
    fn finite_points_pass() {
        let (x, y) = pk(0x1d7a);
        assert(key_ok(x, y));
        let (p, ok) = decode_key_or(x, y);
        assert(ok);
        assert(!p.inf);
        assert_eq((p.x, p.y), (x, y));
        // the generator
        let (gx, gy) = pk(1);
        assert(key_ok(gx, gy));
    }

    #[test]
    fn off_curve_and_infinity_are_flagged() {
        let (x, y) = pk(0x1d7a);
        assert(!key_ok(x, y + 1));
        assert(!key_ok(0, 0));
        assert(!key_ok(x, 0));
        let (p, ok) = decode_key_or(x, y + 1);
        assert(!ok);
        assert(p.inf);
        let (q, ok0) = decode_key_or(0, 0);
        assert(!ok0);
        assert(q.inf);
        // -p is finite and passes
        assert(key_ok(x, 0 - y));
    }

    #[test(should_fail_with = "bad key")]
    fn refusal_fails_on_an_off_curve_key() {
        let (x, y) = pk(0x1d7a);
        refuse_bad_key(x, y + 1, "bad key");
    }

    #[test(should_fail_with = "bad key")]
    fn refusal_fails_on_infinity() {
        refuse_bad_key(0, 0, "bad key");
    }

    #[test]
    fn refusal_passes_a_good_key() {
        let (x, y) = pk(0x1d7a);
        refuse_bad_key(x, y, "bad key");
    }
}
