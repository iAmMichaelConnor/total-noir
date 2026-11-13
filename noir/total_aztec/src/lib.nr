//! total_aztec: total forms of the aztec-nr v6 operations that a state
//! owner or a caller can otherwise make fail.
//!
//! EXTREMELY EXPERIMENTAL, more so than the rest of the repository. The
//! PXE's oracles and aztec-nr were not designed for total circuits; ways
//! remain to make a private function unprovable (listed below and in
//! docs/design.md), and this API will change.
//!
//! The setting: user A's transaction runs contract B's private code
//! against state B's owner controls, with witnesses A's PXE supplies.
//! Written with these entries, B's code turns the failures listed below
//! into flags, so A's transaction completes with ok = false instead of
//! failing; the same entries keep a caller from failing its own call by
//! accident (a missing note, an uninitialised variable).
//!
//! Threat model. A contract that uses these entries and passes total-lint
//! must stay provable for an honest executor in every state, including
//! states its own author's code creates on purpose: the author is an
//! adversary. Against a dishonest executor the entries guarantee that a
//! witness exists, so a failure to prove is the executor's, but an
//! oracle-backed flag (a note's found) is the executor's choice; each
//! entry says which of its flags are determined.
//!
//! Markers. Every total-lint justification marker in this package states a
//! fact that holds whatever the caller passes and whatever state exists
//! (an honest hint satisfies the check, a flag guards the push). An item
//! acceptable only for some callers carries no marker here, so the lint
//! reports it in the calling function until its call site justifies it:
//! refuse_bad_key (an assert for the writer's own transaction),
//! set_key_or and registered_npk_app_hash (owner-side key requests),
//! static_call_flagged_or (the callee can fail the call), and the
//! recursive verification in consume_with_nullification_proof_or (the
//! caller supplies the proof).
//! docs/design.md, "Oracle data and provable error codes", states the two
//! parties and the conditions for using an oracle.
//!
//! Covered: a missing or mismatched note at a slot, including notes of
//! another type the class put there, and a settled note read from a
//! caller-held witness with a determined flag (note), an
//! uninitialised contract (init), PublicImmutable and DelayedPublicMutable
//! reads in every stored state, including states class code writes
//! directly (public), a bad stored Grumpkin key (keys, key_note), a note
//! consumed by a third party with the owner's proof (nullification_proof),
//! a static call's returns (call), and an initializer's arguments in a
//! later call of its own transaction, checked against the address (init). docs/aztec-nr-coverage.md surveys the aztec-nr v6 failure modes
//! and which entry, if any, covers each.
//!
//! Not covered, because no code in B's functions can reach it:
//! - Sync. A's PXE runs B's sync_state for A's scope before every private
//!   call into B, outside every function body; a trap there (for example
//!   a planted handshake the coverage doc lists) aborts A's simulation
//!   before B's total code runs.
//! - B's class. Totality is a property of the class B was deployed with,
//!   and B's owner can schedule a class upgrade. Nothing here lets A's
//!   circuit pin or flag the callee's class; reacting to an upgrade means
//!   monitoring it off the chain.
//! - The transaction's expiration window (DelayedPublicMutable reads,
//!   class-update horizons, anchor age), and B's own code outside these
//!   entries. Note reads still fail on one state only class code outside
//!   the #[note] macro can create in the reading transaction (note.nr,
//!   "Other notes at the slot"), and initializer_args_or on one that only
//!   class code writing its transient slot with the raw oracles can
//!   create (an element wider than one Field; init.nr).
//! - Simulation and proving are separate executions. Hint-backed flags
//!   (a note's found) can differ between them, and PXE state written
//!   during a simulation persists.
//!
//! Conventions follow noir/total, with one naming difference: get_notes_or
//! (and GetNotesOr, confirm_notes_or) returns ([Note; N], [bool; N]), one
//! found flag per slot. Entries document the constraints they emit,
//! their classification (input-falsifiable, hint-satisfiable,
//! definition), their hint rule, and whether each flag is determined.
//! Hinted entries have a constraint half that takes the hint as an
//! argument, so tests feed it wrong hints. Unlike noir/total, several
//! flags here are not determined and cannot be: a circuit cannot prove
//! that a note does not exist (note.nr, "What found means").
//! Places where an app developer chooses a policy carry a short
//! `DEV DECISION:` comment.
//!
//! Dependency: a consumer must name aztec-nr with exactly this line, so
//! that both packages share one `aztec` crate (nargo identifies a git
//! dependency by its URL string, not by its tag), and depend on `total`
//! at the same tag as `total_aztec`, so that both resolve one `total`
//! crate:
//!
//! ```toml
//! aztec = { git = "https://github.com/aztec-labs-eng/aztec-node", tag = "v6.0.0", directory = "noir-projects/aztec-nr/aztec" }
//! ```
//!
//! Account entrypoints need no entry of their own: the pattern is a
//! signature check that returns a flag with no failure source of its own
//! (single_private_immutable_get_note_or, keys::decode_key_or,
//! total::schnorr_verify), passed to aztec-nr's AccountActions, which
//! asserts it once (examples/total_account). An entrypoint that must run
//! in its own deployment transaction, after the constructor, takes the
//! constructor's key from initializer_args_or until the account is
//! initialised at the anchor block (the example's signing_key.nr).

pub mod note;
pub mod init;
pub mod public;
pub mod keys;
pub mod key_note;
pub mod call;
pub mod nullification_proof;

pub use call::static_call_flagged_or;
pub use init::{
    contract_is_initialized, initializer_args_or, INITIALIZER_ARGS_SLOT, InitializerArgs,
    nullifier_exists_at_anchor, public_immutable_is_initialized, record_initializer_args,
};
pub use key_note::KeyNote;
pub use keys::{decode_key_or, key_ok, refuse_bad_key, set_key_or};
pub use note::{
    get_note_or, get_notes_or, get_settled_note_from_witness_or, GetNoteOr, GetNotesOr,
    note_hash_exists_at_anchor, single_private_immutable_get_note_or,
};
pub use nullification_proof::{
    consume_with_nullification_proof_or, npk_app_hash, NullificationProof, registered_npk_app_hash,
};
pub use public::{delayed_public_mutable_read_or, public_immutable_read_or};
