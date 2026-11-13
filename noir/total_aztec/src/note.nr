//! Note reads that report a missing note through a flag instead of
//! failing.
//!
//! # Where aztec-nr v6 fails
//!
//! Function names are aztec-nr v6.0.0's (`aztec/src/...`).
//!
//! - note/note_getter.nr, view_note: `expect("Failed to get a note")` on
//!   the oracle's answer, reached from get_note, which every single-note
//!   getter calls (PrivateImmutable, SinglePrivateImmutable and
//!   PrivateMutable get_note, PrivateMutable replace). When the reader's
//!   PXE holds no note for the slot the Brillig VM traps and no witness
//!   exists.
//! - note/note_getter.nr, confirm_hinted_note / confirm_hinted_notes:
//!   asserts on the hinted note's contract address, owner and slot, then
//!   compute_note_existence_request and one note-hash read request
//!   (PrivateContext::assert_note_exists, 16 per call); the set form adds
//!   "Got more notes than limit" and the select and sort checks.
//! - PrivateMutable get_note and replace nullify the note, which calls
//!   PrivateContext::request_nhk_app for the owner's key: in another
//!   user's PXE the key oracle errors, so they never run there.
//!
//! # What this module does instead
//!
//! The same oracle query without the expect, asked one note at a time
//! for its raw packing and filtered in the hint ("Other notes at the
//! slot"). The contract, owner and slot checks, and a check that the
//! stage and nonce have a shape the PXE produces, and a check that the
//! read request will name a note hash the kernel accepts ("The note hash
//! the read request names"), are terms of the flag: found = the hint
//! offered a note and it matches. The existence request and its read request are emitted only
//! under found. The note is masked to Note::unpack of all zeros when
//! nothing was found. Nothing is forked.
//!
//! What found means. found is not determined: a circuit cannot prove that
//! a note does not exist, so the prover can always answer "none".
//! found = false proves nothing and only makes the reader's call return
//! ok = false. Folding the checks into found therefore costs no
//! soundness (a mismatched hint gives the prover nothing it could not get
//! by answering "none"), and it turns a misaligned hint into a flag
//! instead of an unprovable call. found = true proves inclusion and
//! nothing more: the kernel accepts the read request only if the note's
//! hash is in the note hash tree at the anchor block (or pending in this
//! transaction), and the checks fix (contract, owner, slot). Note hashes
//! are never removed, so the note may have been nullified since, and when
//! the slot has held several notes the prover picks which one.
//!
//! Freshness. Proving a note current takes its nullifier, which needs the
//! owner's key: nullify it in the owner's own transaction (aztec-nr's
//! PrivateMutable::get_note), or have the owner hand over a proof
//! (nullification_proof.nr). For a value third parties must read fresh,
//! use public state (public.nr).
//!
//! Who can read at all. A v6 PXE stores a note only if it can compute the
//! note's nullifier, which needs the owner's nullifier hiding key
//! (messages/discovery/nonce_discovery.nr, attempt_note_nonce_discovery,
//! "skipping PXE insertion"). So these reads find a note
//! only for the owner, or for users who share the owner's keys (an
//! escrow-style contract). For everyone else they return found = false:
//! "does not fail", not "can read".
//!
//! Two kinds of read. get_note_or, get_notes_or and their methods ask the
//! PXE (an oracle) which notes exist, so found is the executor's choice:
//! a PXE may answer "none" for a note that exists, and picks which note
//! comes first. get_settled_note_from_witness_or takes the note, its
//! metadata and its note hash tree witness as arguments and checks them
//! against the anchor block with no oracle, so found is determined by
//! the arguments and the anchor block (docs/design.md, "Oracle data and
//! provable error codes").
//!
//! # Other notes at the slot
//!
//! The note hash carries no type id, so the PXE serves the reader every
//! note the class committed at (contract, owner, slot), whatever its
//! type. The contract's author is an adversary (lib.nr), so the oracle
//! reads must stay provable whatever notes the class's own code put
//! there. aztec-nr's get_notes unpacks every return as the reader's type:
//! a wider note makes the PXE refuse the return ("Array size exceeds
//! target length"), a narrower one shifts every metadata field (in one
//! aligned case, a one-Field-narrower note owned by the contract itself
//! at storage slot 3, its contract, owner and slot fields matched and
//! the read request named a note hash that does not exist), and a
//! non-canonical packing (an integer member holding a wider value)
//! unpacks by truncation to a note that hashes elsewhere. The hint here
//! (view_notes_or) closes these:
//!
//! - It asks the PXE one note at a time for its raw packing, in a buffer
//!   MAX_NOTE_PACKED_LEN Fields wider than the reader's, so the PXE never
//!   refuses a note it can hold from a message (packings of at most
//!   MAX_NOTE_PACKED_LEN Fields).
//! - It keeps a note only if the raw Fields have exactly the layout the
//!   PXE gives a note of the reader's width (genuine_note_or): contract
//!   field equal to this contract, stage the Field 1, 2 or 3 (before the
//!   u8 cast), nonce 0 for stage 1 and not 0, 1, 2 or 3 for stages 2 and
//!   3, zeros after the nonce, and the note's Fields its canonical
//!   packing. A note k Fields wider puts its stage code (nonzero) after
//!   the nonce position when k >= 2; when k = 1 its nonce lands there
//!   (nonzero unless it is pending in this phase, and then the stage code
//!   1 lands in the nonce position, which stages 2 and 3 refuse and stage
//!   1 requires to be 0). A note k Fields narrower leaves the stage
//!   position 0 when k >= 2; when k = 1 its nonce lands in the stage
//!   position and the padding 0 in the nonce position, which passes only
//!   for a nonce of exactly 1 (stage 1 with nonce 0). Kernel nonces are
//!   Poseidon2 outputs of the transaction's first nullifier and the
//!   note's index, so a note's nonce is 1 with probability 1/p, and
//!   grinding transactions does not help beyond that per attempt.
//! - For a settled note it also asks the PXE whether it holds a settled
//!   note of this contract with the note hash the reader's type computes
//!   and the same nonce (get_settled_note_origin). The PXE stores a
//!   settled note only after finding its unique note hash, from that
//!   note hash and nonce, in a transaction at or before the anchor block
//!   (pxe NoteService.validateAndStoreNotes), so a kept settled note's
//!   read request holds, whatever type or sync code stored it.
//! - For a pending note (created earlier in the same transaction) it
//!   keeps the note only if the note hash the reader's type computes is
//!   one this call has pushed (the context's note hash vector, passed in).
//!   No oracle exposes the note hashes of the transaction's other calls,
//!   so a pending note created in another call (an earlier call into this
//!   contract, a nested call, a caller) is dropped: found = false.
//!
//! These are hint-side filters: they protect the executor (an honest
//! hint never offers a note whose read request fails) and add nothing
//! against a dishonest executor, who can always answer "none".
//!
//! # The note hash the read request names
//!
//! The PXE records a pending note with whatever Fields and note hash the
//! creating code reported (notify_created_note), and the kernel accepts a
//! pending read request only for a note hash this transaction pushed. A
//! class can make the two disagree: a hand-written NoteHash that hashes a
//! packing differently from the reader's type, a direct
//! notify_created_note of other Fields than the note hash it pushes, or a
//! slot written with one type and read with another whose NoteHash
//! differs. A hand-written compute_note_hash can also give one value in
//! Brillig and another in ACIR (std::runtime::is_unconstrained, or an
//! oracle call inside it), so the hash the hint checked is not the hash
//! the circuit requests; that reaches settled notes too. None of this is
//! visible in a compiled reader (the ACIR branch of is_unconstrained is
//! the only one compiled), so the reads do not trust the hint here; the
//! circuit decides, as a flag term (hash_ok):
//!
//! - the reader's type's note hash is computed once in the circuit, and
//!   that one value is what the read request names (the request is built
//!   here, not by compute_note_existence_request, which hashes again);
//! - it must equal the note hash the hint reports it checked, so a
//!   settled note's request names the note hash the honest hint found in
//!   the PXE's settled notes (get_settled_note_origin);
//! - for a pending note, it must be a nonzero entry of the note hashes
//!   this call pushed before the read (pushed_note_hashes), which the
//!   kernel accepts: same contract, lower counter, same value. The PXE
//!   keeps a read note hash out of transient squashing while a read of it
//!   is outstanding, and push_nullifier_for_note_hash notifies the PXE,
//!   which then stops returning the note.
//!
//! found = true is backed by the contract, owner and slot checks,
//! metadata_ok (a stage and nonce of a shape the PXE produces), hash_ok,
//! and a kernel read request. Every term is a flag, so whatever NoteHash
//! or creation code the class has, a read whose request would fail is
//! found = false instead of an unprovable call.
//!
//! What remains, for a class whose code tries to fail its own readers:
//! - A bool member (or a hand-written unpack or compute_note_hash that
//!   asserts) traps inside the hint on a Field outside its domain, before
//!   any filter runs. total-lint reports such an assert as a reachable
//!   abort site of every function that reads the note (and the
//!   compute_note_hash assert also as a constraint); Field-only notes
//!   with the #[note] derive have none (key_note.nr).
//! - A pending note wider than the reader's packing plus
//!   MAX_NOTE_PACKED_LEN makes the PXE refuse the return; only a note
//!   type outside the #[note] macro (which refuses such widths) can be
//!   one, and it can never be delivered. total-lint reports every call of
//!   the notifyCreatedNote oracle that creates one (note-width), so a
//!   lint-passing class cannot.
//!
//! Limits that remain:
//! - First note wins. get_note_or returns the PXE's first active note
//!   that passes the filters, which the owner chooses by order of
//!   creation; a bad note created before a good one is the one read (a
//!   flag after decoding, not a failure). get_notes_or returns up to N
//!   and lets the reader choose. Which notes, and whether any, is the
//!   executor's choice.
//! - Read budget. Each found note pushes one read request and a call holds
//!   16 (MAX_NOTE_HASH_READ_REQUESTS_PER_CALL). found is false for a note
//!   that would need a seventeenth, so the push never fails; keep the sum
//!   of N over all reads in a function at or below 16 to read every note.
//!   The transaction's 64 read requests are shared with every other call
//!   and checked only by the kernel.

use aztec::context::{NoteExistenceRequest, PrivateContext};
use aztec::messages::logs::note::MAX_NOTE_PACKED_LEN;
use aztec::note::{
    HintedNote,
    note_getter_options::NoteStatus,
    note_interface::{NoteHash, NoteType},
    note_metadata::NoteMetadata,
};
use aztec::oracle::notes::get_settled_note_origin;
use aztec::protocol::{
    address::AztecAddress,
    constants::{
        MAX_NOTE_HASH_READ_REQUESTS_PER_CALL, MAX_NOTE_HASHES_PER_CALL, NOTE_HASH_TREE_HEIGHT,
    },
    hash::{compute_siloed_note_hash, compute_unique_note_hash},
    side_effect::Counted,
    traits::{Packable, ToField},
};
use aztec::state_vars::{
    Owned, PrivateImmutable, PrivateMutable, PrivateSet, SinglePrivateImmutable, StateVariable,
};
use std::static_assert;
use total::merkle::is_member;

/// The PXE's note oracle (aztec_utl_getNotes, the oracle aztec-nr's
/// oracle::notes::get_notes wraps) with every returned note left as its
/// raw packing in W Fields. The PXE serialises the returned notes as one
/// flat run of their packings (each note's fields, then contract, owner,
/// randomness, slot, stage, nonce) zero-padded to max_notes * W, and
/// throws "Array size exceeds target length" when the run is longer.
/// Called with limit = max_notes = 1, so each answer is one note at the
/// start of the array and the rest is zero.
#[oracle(aztec_utl_getNotes)]
unconstrained fn get_raw_notes_oracle<let W: u32>(
    _owner: Option<AztecAddress>,
    _storage_slot: Field,
    _num_selects: u8,
    _select_by_indexes: [u8; 0],
    _select_by_offsets: [u8; 0],
    _select_by_lengths: [u8; 0],
    _select_values: [Field; 0],
    _select_comparators: [u8; 0],
    _sort_by_indexes: [u8; 0],
    _sort_by_offsets: [u8; 0],
    _sort_by_lengths: [u8; 0],
    _sort_order: [u8; 0],
    _limit: u32,
    _offset: u32,
    _status: u8,
    _max_notes: u32,
    _packed_hinted_note_length: u32,
) -> BoundedVec<[Field; W], 1> {}

/// Whether a nonce could be a kernel-assigned one: not 0, 1, 2 or 3. The
/// kernel's nonces are Poseidon2 outputs (compute_note_hash_nonce of the
/// transaction's first nullifier and the note's index), so a real one is
/// in {0, 1, 2, 3} with probability 4 / p per note.
unconstrained fn nonce_is_plausible(nonce: Field) -> bool {
    (nonce != 0) & (nonce != 1) & (nonce != 2) & (nonce != 3)
}

/// The note in raw (one note's packing, zero-padded to W) when raw has
/// exactly the layout the PXE gives a note of Note's width, none
/// otherwise: at Note's metadata positions the contract is this_address,
/// the stage is the Field 1, 2 or 3 (compared before the u8 cast), the
/// nonce is 0 for stage 1 and plausible (nonce_is_plausible) for stages 2
/// and 3, every Field after the nonce is 0, and the note's fields are its
/// canonical packing (Note::unpack then pack gives them back).
///
/// What this rejects (module header, "Other notes at the slot"): every
/// note of another width, a non-canonical packing for Note, and nothing
/// the PXE gives for a genuine note of Note's width with canonical
/// packing (the PXE's fromRawData sets exactly these stages and nonces).
///
/// Trap-free for every raw except inside Note::unpack, which is the
/// class's code (a bool member asserts on a Field outside {0, 1}). Runs
/// Note::unpack only on a raw whose layout checks hold.
unconstrained fn genuine_note_or<Note, let W: u32>(
    raw: [Field; W],
    this_address: AztecAddress,
) -> Option<HintedNote<Note>>
where
    Note: Packable,
{
    let w = <Note as Packable>::N;
    static_assert(
        w + 6 <= W,
        "genuine_note_or: the raw width must hold the note and its metadata",
    );
    let stage = raw[w + 4];
    let nonce = raw[w + 5];
    let mut ok = raw[w] == this_address.to_field();
    ok &=
        ((stage == 1) & (nonce == 0)) | (((stage == 2) | (stage == 3)) & nonce_is_plausible(nonce));
    for i in (w + 6)..W {
        ok &= raw[i] == 0;
    }
    let mut out = Option::none();
    if ok {
        let mut packed = [0; <HintedNote<Note> as Packable>::N];
        for i in 0..packed.len() {
            packed[i] = raw[i];
        }
        let hinted: HintedNote<Note> = HintedNote::unpack(packed);
        let repacked = hinted.note.pack();
        let mut canonical = true;
        for i in 0..w {
            canonical &= repacked[i] == raw[i];
        }
        if canonical {
            out = Option::some(hinted);
        }
    }
    out
}

/// Hint: the first N active notes at (owner, storage_slot) the PXE knows
/// of for this contract, each kept only if it can be read as a Note and
/// proven, with the note hash Note::compute_note_hash gives for each
/// (0 where none is kept): view_note's query (no selects or sorts, status
/// ACTIVE) asked one note at a time (offsets 0 to N - 1) through
/// get_raw_notes_oracle, each answer filtered by genuine_note_or; a
/// settled note is kept only if the PXE holds a settled note of this
/// contract with that note hash and the same nonce
/// (get_settled_note_origin), a pending note only if that note hash is
/// nonzero and among the first pushed_len entries of pushed (the
/// context's note hash vector: what this call has pushed). The PXE
/// stores a settled note only after finding its unique note hash, from
/// that note hash and nonce, in a transaction at or before the anchor
/// block, so a kept settled note's read request holds; the kernel accepts
/// a pending read request for a note hash this call pushed earlier. A
/// dropped note leaves a none in its position. The circuit re-checks the
/// note hash (hash_ok), so a NoteHash whose Brillig and ACIR values
/// differ gives found = false, not a failed read request.
///
/// The raw width is Note's hinted width plus MAX_NOTE_PACKED_LEN, which
/// holds every note the PXE can store from a message (their packing is
/// at most MAX_NOTE_PACKED_LEN Fields), so for those the oracle never
/// refuses the answer.
///
/// Trap-free in the Brillig code for every note the PXE can return,
/// except: inside Note::unpack and Note::compute_note_hash (class code;
/// the #[note] derive's are trap-free on every input for Field members),
/// and the oracle's refusal of a note wider than the raw width, which
/// only a note created in the same transaction by class code that
/// bypasses the #[note] macro's MAX_NOTE_PACKED_LEN bound can be.
unconstrained fn view_notes_or<Note, let N: u32>(
    owner: Option<AztecAddress>,
    storage_slot: Field,
    this_address: AztecAddress,
    pushed: [Field; MAX_NOTE_HASHES_PER_CALL],
    pushed_len: u32,
) -> ([Option<HintedNote<Note>>; N], [Field; N])
where
    Note: NoteType + NoteHash + Packable,
{
    let mut notes = [Option::none(); N];
    let mut hashes = [0; N];
    for i in 0..N {
        // total-lint: allow the PXE's note oracle; the raw width holds every note it can store from a message (view_notes_or)
        let raw: BoundedVec<[Field; <HintedNote<Note> as Packable>::N + MAX_NOTE_PACKED_LEN], 1> = get_raw_notes_oracle(
            owner,
            storage_slot,
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
            i,
            NoteStatus.ACTIVE,
            1,
            <HintedNote<Note> as Packable>::N + MAX_NOTE_PACKED_LEN,
        );
        if raw.len() != 0 {
            let candidate: Option<HintedNote<Note>> =
                genuine_note_or(raw.get_unchecked(0), this_address);
            if candidate.is_some() {
                let hinted = candidate.unwrap_unchecked();
                let note_hash = hinted.note.compute_note_hash(
                    hinted.owner,
                    hinted.storage_slot,
                    hinted.randomness,
                );
                let mut keep = false;
                if hinted.metadata.is_settled() {
                    let nonce = hinted.metadata.pack()[1];
                    // total-lint: allow the PXE's settled-note lookup, asked for this contract's own address; answers some or none for every note hash and nonce
                    keep = get_settled_note_origin(note_hash, this_address, nonce).is_some();
                } else if note_hash != 0 {
                    for j in 0..MAX_NOTE_HASHES_PER_CALL {
                        keep |= (j < pushed_len) & (pushed[j] == note_hash);
                    }
                }
                if keep {
                    notes[i] = candidate;
                    hashes[i] = note_hash;
                }
            }
        }
    }
    (notes, hashes)
}

/// Read the note at storage_slot (and owner, when given) as (note,
/// found). On found = false the note is Note::unpack of all zeros and no
/// read request is emitted; on found = true one read request is emitted.
///
/// Constraints: those of confirm_note_or, plus the compiler's range
/// checks on the hint's typed return (the Option flag, the metadata
/// stage, integer members): hint-satisfiable, Brillig produces in-range
/// values.
///
/// Hint rule: the honest PXE returns its first active note for this
/// contract, owner and slot that it saw included (or created earlier in
/// this transaction); view_notes_or drops it if it cannot be read as a
/// Note and proven (module header, "Other notes at the slot"), which
/// drops every pending note this call did not create.
///
/// Determinedness: found is NOT determined; it is the executor's choice
/// (its PXE can answer "none" for a note that exists, and picks the
/// first note). A requester can rely on found = true (inclusion, backed
/// by the kernel read request) and on nothing from found = false (module
/// header, "What found means"). get_settled_note_from_witness_or is the
/// determined form for a settled note whose witness the caller holds.
pub fn get_note_or<Note>(
    context: &mut PrivateContext,
    owner: Option<AztecAddress>,
    storage_slot: Field,
) -> (Note, bool)
where
    Note: NoteType + NoteHash + Packable,
{
    let this_address = context.this_address();
    let pushed = (*context).finish().note_hashes;
    // Safety: found = true is backed by the matching checks, hash_ok and
    // the kernel read request in confirm_note_or; found = false emits
    // nothing.
    let (hint, hash): ([Option<HintedNote<Note>>; 1], [Field; 1]) = unsafe {
        // total-lint: allow typed hint return (Option flag, metadata stage); Brillig produces in-range values
        view_notes_or::<Note, 1>(
            owner,
            storage_slot,
            this_address,
            pushed.array.map(|h: Counted<Field>| h.inner),
            pushed.length,
        )
    };
    confirm_note_or(context, hint[0], hash[0], owner, storage_slot)
}

/// Constraint half of get_note_or, split out so tests can feed wrong
/// hints. hinted_note_hash is the note hash the hint reports it checked
/// (view_notes_or).
///
/// Emits: note_matches (the contract, owner and slot eq gadgets and
/// metadata_ok, hint-satisfiable for every value); under the predicate
/// is_some & matches, the note's own hash (Note::compute_note_hash, 0
/// otherwise, so a NoteHash that asserts never sees the zeroed note of an
/// empty hint or a mismatched one); hash_ok (module header, "The note
/// hash the read request names"); found = is_some & matches & hash_ok &
/// read_request_room (the call's read requests below 16, an integer
/// comparison on the context's count); under found, request_note for
/// that note hash and the read request push, which has room by the flag;
/// then one select per packed field and Note::unpack of the masked
/// packing (total for a derived Packable on the all-zero packing).
pub fn confirm_note_or<Note>(
    context: &mut PrivateContext,
    hint: Option<HintedNote<Note>>,
    hinted_note_hash: Field,
    owner: Option<AztecAddress>,
    storage_slot: Field,
) -> (Note, bool)
where
    Note: NoteType + NoteHash + Packable,
{
    let hinted = hint.unwrap_unchecked();
    let matches = hint.is_some() & note_matches(context, hinted, owner, storage_slot);
    let mut note_hash = 0;
    if matches {
        note_hash =
            hinted.note.compute_note_hash(hinted.owner, hinted.storage_slot, hinted.randomness);
    }
    let pushed = pushed_note_hashes(context);
    let found = matches
        & hash_ok(hinted.metadata, note_hash, hinted_note_hash, pushed)
        & read_request_room(context);
    if found {
        request_note(context, hinted, note_hash);
    }
    (mask_note(hinted.note, found), found)
}

/// The note hashes this call has pushed so far: the context's note hash
/// vector, read through a copy of finish() (pure wiring), with every
/// position at or past its length set to 0. One u32 comparison and one
/// product per position (MAX_NOTE_HASHES_PER_CALL = 16). Total;
/// determined by what the call pushed before.
fn pushed_note_hashes(context: &mut PrivateContext) -> [Field; MAX_NOTE_HASHES_PER_CALL] {
    let pushed = (*context).finish().note_hashes;
    let mut out = [0; MAX_NOTE_HASHES_PER_CALL];
    for i in 0..MAX_NOTE_HASHES_PER_CALL {
        let live = i < pushed.length;
        out[i] = (live as Field) * pushed.array[i].inner;
    }
    out
}

/// Flag: a read request for note_hash (the reader's type's note hash of
/// a matching hinted note, computed once in the circuit) names a note
/// hash the kernel accepts, whatever code of the class created the note
/// (module header, "The note hash the read request names"): note_hash
/// equals hinted_note_hash, the hash the hint checked (for a settled
/// note, against the PXE's settled notes); and the note is settled or
/// note_hash is a nonzero entry of pushed (pushed_note_hashes). Eq
/// gadgets only, hint-satisfiable for every value; a flag term, never
/// asserted.
fn hash_ok(
    metadata: NoteMetadata,
    note_hash: Field,
    hinted_note_hash: Field,
    pushed: [Field; MAX_NOTE_HASHES_PER_CALL],
) -> bool {
    let same = note_hash == hinted_note_hash;
    let mut in_call = false;
    for i in 0..MAX_NOTE_HASHES_PER_CALL {
        in_call |= pushed[i] == note_hash;
    }
    same & (metadata.is_settled() | (in_call & (note_hash != 0)))
}

/// Flag: the call has room for one more note hash read request (it holds
/// MAX_NOTE_HASH_READ_REQUESTS_PER_CALL = 16). The count is the length of
/// the context's request vector, read through a copy of finish() (pure
/// wiring); one u32 comparison. Folded into found, so a read past the
/// budget is found = false instead of a failing push. Total; determined
/// by what the call pushed before.
pub fn read_request_room(context: &mut PrivateContext) -> bool {
    // total-lint: allow u32 comparison on the context's request count: the compiler's hints satisfy it for every count
    (*context).finish().note_hash_read_requests.length < MAX_NOTE_HASH_READ_REQUESTS_PER_CALL
}

/// Whether the hinted note is one of this contract's, at storage_slot,
/// owned by owner (when given), with metadata of a shape the PXE gives:
/// confirm_hinted_note's three checks and metadata_ok as a flag.
fn note_matches<Note>(
    context: &mut PrivateContext,
    hinted: HintedNote<Note>,
    owner: Option<AztecAddress>,
    storage_slot: Field,
) -> bool {
    // total-lint: allow eq gadgets on the hinted note; hint-satisfiable for every value
    let contract_ok = hinted.contract_address.eq(context.this_address());
    // total-lint: allow eq gadget on the hinted note; hint-satisfiable for every value
    let owner_ok = owner.is_none() | hinted.owner.eq(owner.unwrap_unchecked());
    // total-lint: allow eq gadget on the hinted note; hint-satisfiable for every value
    let slot_ok = hinted.storage_slot == storage_slot;
    contract_ok & owner_ok & slot_ok & metadata_ok(hinted.metadata)
}

/// Whether metadata has a shape NoteMetadata::from_raw_data produces:
/// stage 1 (pending, same phase) with nonce 0, or stage 2 (pending,
/// previous phase) or 3 (settled) with a nonzero nonce. Four eq gadgets
/// on the hinted metadata, hint-satisfiable for every value (a flag
/// term, never asserted). It does not make a read request hold (the
/// kernel decides that); it keeps found from accepting a stage no real
/// note has, such as one a misaligned packing put there.
fn metadata_ok(metadata: NoteMetadata) -> bool {
    // total-lint: allow eq gadgets on the hinted metadata; hint-satisfiable for every value
    let zero_nonce = metadata.pack()[1] == 0;
    // total-lint: allow eq gadgets on the hinted stage; hint-satisfiable for every value
    let same_phase = metadata.is_pending_same_phase();
    // total-lint: allow eq gadgets on the hinted stage; hint-satisfiable for every value
    let nonced = metadata.is_pending_previous_phase() | metadata.is_settled();
    (same_phase & zero_nonce) | (nonced & !zero_nonce)
}

/// The existence request and read request for one found note whose
/// reader's-type note hash is note_hash; called only under found, after
/// note_matches, hash_ok and read_request_room. The request is
/// compute_note_existence_request's, built from note_hash instead of
/// hashing the note again: for a settled note the unique note hash of
/// note_hash siloed with the note's contract and its nonce, for a pending
/// note note_hash and the contract.
fn request_note<Note>(context: &mut PrivateContext, hinted: HintedNote<Note>, note_hash: Field) {
    let request = if hinted.metadata.is_settled() {
        let nonce = hinted.metadata.pack()[1];
        NoteExistenceRequest::for_settled(compute_unique_note_hash(
            nonce,
            compute_siloed_note_hash(hinted.contract_address, note_hash),
        ))
    } else {
        // total-lint: allow predicated on found; for_pending's nonzero-address assert, unreachable once the note matches (its contract is this_address)
        NoteExistenceRequest::for_pending(note_hash, hinted.contract_address)
    };
    // total-lint: allow predicated on found, which includes read_request_room; the push has room
    context.assert_note_exists(request);
}

/// Note::unpack of the note's packing with every field multiplied by
/// keep.
fn mask_note<Note>(note: Note, keep: bool) -> Note
where
    Note: Packable,
{
    let packed = note.pack();
    let mut masked = packed;
    for i in 0..packed.len() {
        masked[i] = (keep as Field) * packed[i];
    }
    Note::unpack(masked)
}

/// Read up to N notes at storage_slot (and owner, when given) as (notes,
/// found): found[i] says whether notes[i] is a real note; the others are
/// Note::unpack of all zeros. Read requests are emitted for found notes
/// only. A note the oracle returns twice is kept once (by its own note
/// hash; two real notes agreeing on contents, owner, slot and randomness
/// would also count once, which undercounts rather than fails).
///
/// N is at most 16 (static assert); keep the sum of N over all reads in a
/// function at or below 16.
///
/// Constraints: those of confirm_notes_or, plus the hint's typed-return
/// range checks (as get_note_or). Hint rule: the honest PXE returns its
/// first N active notes for this contract, owner and slot, each dropped
/// by view_notes_or if it cannot be read as a Note and proven.
///
/// Determinedness: found[i] is NOT determined; which notes, and whether
/// any, is the executor's choice. Each found note is
/// distinct and was committed at (contract, owner, slot) at some point,
/// so sums over found notes are not balances. No selects, sorts, filter
/// or offset: filter the returned notes in constrained code and fold the
/// filter into found.
pub fn get_notes_or<Note, let N: u32>(
    context: &mut PrivateContext,
    owner: Option<AztecAddress>,
    storage_slot: Field,
) -> ([Note; N], [bool; N])
where
    Note: NoteType + NoteHash + Packable,
{
    static_assert(
        N <= MAX_NOTE_HASH_READ_REQUESTS_PER_CALL,
        "get_notes_or: N above the read requests of one call",
    );
    let this_address = context.this_address();
    let pushed = (*context).finish().note_hashes;
    // Safety: each found note is backed by the matching checks, hash_ok
    // and a kernel read request in confirm_notes_or; a missing note emits
    // nothing.
    let (hints, hashes): ([Option<HintedNote<Note>>; N], [Field; N]) = unsafe {
        // total-lint: allow typed hint return (Option flags, metadata stages); Brillig produces in-range values
        view_notes_or::<Note, N>(
            owner,
            storage_slot,
            this_address,
            pushed.array.map(|h: Counted<Field>| h.inner),
            pushed.length,
        )
    };
    confirm_notes_or(context, hints, hashes, owner, storage_slot)
}

/// Constraint half of get_notes_or, split out so tests can feed wrong
/// hints. hinted_note_hashes[i] is the note hash the hint reports it
/// checked for hints[i] (view_notes_or).
///
/// Emits, for each i: note_matches, then, under the predicate is_some &
/// matches, the note's own hash (Note::compute_note_hash; for a derived
/// #[note] one Poseidon2 hash, definitions), 0 otherwise; hash_ok (as
/// confirm_note_or, against the note hashes the call pushed before the
/// read); N(N-1)/2 eq gadgets comparing hashes with earlier slots'
/// (hint-satisfiable); found[i] = is_some & matches & hash_ok & not a
/// repeat & read_request_room (taken after the pushes for the earlier
/// slots); under found[i], request_note for that hash (as
/// confirm_note_or); then the masking selects. The hash runs only under
/// the predicate so that a hand-written NoteHash that asserts on its
/// note is never constrained on the zeroed note of an empty slot or on a
/// mismatched hint, and it runs once, so the read request names the hash
/// hash_ok checked.
pub fn confirm_notes_or<Note, let N: u32>(
    context: &mut PrivateContext,
    hints: [Option<HintedNote<Note>>; N],
    hinted_note_hashes: [Field; N],
    owner: Option<AztecAddress>,
    storage_slot: Field,
) -> ([Note; N], [bool; N])
where
    Note: NoteType + NoteHash + Packable,
{
    let mut found = [false; N];
    let mut hashes = [0; N];
    let pushed = pushed_note_hashes(context);
    for i in 0..N {
        let hinted = hints[i].unwrap_unchecked();
        found[i] = hints[i].is_some() & note_matches(context, hinted, owner, storage_slot);
        // Predicated: an empty or mismatched slot keeps hash 0, which the
        // dedupe below never compares (it masks with found).
        if found[i] {
            hashes[i] =
                hinted.note.compute_note_hash(hinted.owner, hinted.storage_slot, hinted.randomness);
        }
        found[i] = found[i] & hash_ok(hinted.metadata, hashes[i], hinted_note_hashes[i], pushed);
    }
    for j in 1..N {
        let mut seen = false;
        for i in 0..j {
            // total-lint: allow eq gadget on hinted note hashes; hint-satisfiable for every value
            seen = seen | (found[i] & (hashes[i] == hashes[j]));
        }
        found[j] = found[j] & !seen;
    }
    let mut notes = [Note::unpack(std::mem::zeroed()); N];
    for i in 0..N {
        let hinted = hints[i].unwrap_unchecked();
        found[i] = found[i] & read_request_room(context);
        if found[i] {
            request_note(context, hinted, hashes[i]);
        }
        notes[i] = mask_note(hinted.note, found[i]);
    }
    (notes, found)
}

/// get_note_or as a method of an owned PrivateImmutable or PrivateMutable
/// state variable: `storage.x.get_note_or(owner)`, the flagged form of
/// `storage.x.at(owner).get_note()`. The method is on the Owned wrapper
/// because aztec-nr keeps the context and owner of `.at(owner)` private.
///
/// For a PrivateMutable it does not nullify, so it runs in any PXE that
/// holds the note, at the cost of freshness (module header).
///
/// DEV DECISION: in the owner's own transaction, aztec-nr's
/// PrivateMutable::get_note proves the note current (by nullifying it)
/// and fails when it is missing; this reads without nullifying and flags.
pub trait GetNoteOr<Note> {
    fn get_note_or(self, owner: AztecAddress) -> (Note, bool);
}

impl<Note> GetNoteOr<Note> for Owned<PrivateImmutable<Note, &mut PrivateContext>, &mut PrivateContext>
where
    Note: NoteType + NoteHash + Packable,
{
    fn get_note_or(self, owner: AztecAddress) -> (Note, bool) {
        get_note_or(self.context, Option::some(owner), self.get_storage_slot())
    }
}

impl<Note> GetNoteOr<Note> for Owned<PrivateMutable<Note, &mut PrivateContext>, &mut PrivateContext>
where
    Note: NoteType + NoteHash + Packable,
{
    fn get_note_or(self, owner: AztecAddress) -> (Note, bool) {
        get_note_or(self.context, Option::some(owner), self.get_storage_slot())
    }
}

/// get_notes_or as a method of an owned PrivateSet:
/// `storage.x.get_notes_or::<N>(owner)`, without nullifying.
pub trait GetNotesOr<Note> {
    fn get_notes_or<let N: u32>(self, owner: AztecAddress) -> ([Note; N], [bool; N]);
}

impl<Note> GetNotesOr<Note> for Owned<PrivateSet<Note, &mut PrivateContext>, &mut PrivateContext>
where
    Note: NoteType + NoteHash + Packable,
{
    fn get_notes_or<let N: u32>(self, owner: AztecAddress) -> ([Note; N], [bool; N]) {
        get_notes_or(self.context, Option::some(owner), self.get_storage_slot())
    }
}

/// get_note_or on a SinglePrivateImmutable (no owner filter, as aztec-nr's
/// get_note). aztec-nr keeps its context private, so the context is an
/// argument.
pub fn single_private_immutable_get_note_or<Note>(
    context: &mut PrivateContext,
    var: SinglePrivateImmutable<Note, &mut PrivateContext>,
) -> (Note, bool)
where
    Note: NoteType + NoteHash + Packable,
{
    get_note_or(context, Option::none(), var.get_storage_slot())
}

/// Flag: leaf (a unique, siloed note hash) is at leaf_index on
/// sibling_path below the note hash tree root of the anchor block. The
/// total form of aztec-nr's history::note::assert_note_existed_by, with
/// the witness as arguments: no oracle and no kernel request.
///
/// Constraints: check_note_hash_witness against the anchor block's root.
/// Determined by the arguments and the anchor block: every satisfying
/// witness gives the same flag. true proves the leaf was in the tree at
/// the anchor block; false says only that this witness does not show it
/// (an append-only tree has no non-membership witness, so a requester
/// learns nothing more from false).
///
/// aztec-nr v6 has no non-aborting oracle for a note hash witness
/// (getNoteHashMembershipWitness throws on an absent leaf), so the caller
/// obtains the witness (an Aztec node's findLeavesIndexes and
/// getNoteHashSiblingPath at the anchor block) and passes it in.
///
/// DEV DECISION: assert_note_existed_by fails on an absent leaf; this
/// flags. Keep the assert where the leaf is the prover's own; use this
/// where it comes from someone else (an owner's handoff).
pub fn note_hash_exists_at_anchor(
    context: &mut PrivateContext,
    leaf: Field,
    leaf_index: Field,
    sibling_path: [Field; NOTE_HASH_TREE_HEIGHT],
) -> bool {
    let root = context.get_anchor_block_header().state.partial.note_hash_tree.root;
    check_note_hash_witness(root, leaf, leaf_index, sibling_path)
}

/// Constraint half of note_hash_exists_at_anchor: true when leaf_index is
/// below 2^NOTE_HASH_TREE_HEIGHT, leaf at leaf_index with sibling_path
/// hashes to root, and leaf is not 0 (every unused position holds 0, so a
/// path to one would "prove" leaf 0).
///
/// Emits: total::merkle::is_member (the index flagged below
/// 2^NOTE_HASH_TREE_HEIGHT, one Poseidon2 permutation per level, the root
/// eq gadget) and an eq gadget for leaf != 0. No assert: total for every
/// argument, determined.
pub fn check_note_hash_witness(
    root: Field,
    leaf: Field,
    leaf_index: Field,
    sibling_path: [Field; NOTE_HASH_TREE_HEIGHT],
) -> bool {
    is_member(leaf, leaf_index, sibling_path, root) & (leaf != 0)
}

/// Read a settled note of this contract from arguments, with no oracle:
/// the caller supplies the note, its owner, storage slot, randomness and
/// nonce, and the note hash tree witness of its unique note hash (leaf
/// index and sibling path) at the anchor block. Returns (note, found);
/// on found = false the note is Note::unpack of all zeros and nothing is
/// emitted, on found = true one read request is emitted.
///
/// found = the unique note hash, computed as aztec-nr v6 does for a
/// settled read (Note::compute_note_hash(owner, storage_slot,
/// randomness), siloed with this contract's address, then with the
/// nonce), is a nonzero leaf at leaf_index on sibling_path below the
/// anchor block's note hash tree root. Determined: every satisfying
/// witness gives the same found for the same arguments and anchor block
/// (no hint anywhere on this path), and found = true is exactly the
/// statement that the note was committed at (this contract, owner, slot)
/// by the anchor block. It says nothing about a nullifier: the note may
/// have been spent since. A wrong index, path or nonce, or a note that
/// was never committed, gives found = false.
///
/// Constraints: Note::compute_note_hash (one Poseidon2 hash for a
/// derived #[note]; a hand-written impl that asserts makes this entry
/// input-falsifiable), two Poseidon2 hashes (silo, unique), total's
/// is_member (index flagged below 2^NOTE_HASH_TREE_HEIGHT, one Poseidon2
/// permutation per level, root eq gadget), an eq gadget for leaf != 0,
/// read_request_room (found is false when the call's 16 read requests
/// are used up), and under found the read request push (the kernel
/// checks the same leaf against the same anchor root, so it holds
/// whenever found does), then the masking selects. Typed members
/// of Note are range checks on the entry parameters (Field-only notes
/// have none).
pub fn get_settled_note_from_witness_or<Note>(
    context: &mut PrivateContext,
    note: Note,
    owner: AztecAddress,
    storage_slot: Field,
    randomness: Field,
    note_nonce: Field,
    leaf_index: Field,
    sibling_path: [Field; NOTE_HASH_TREE_HEIGHT],
) -> (Note, bool)
where
    Note: NoteHash + Packable,
{
    let note_hash = note.compute_note_hash(owner, storage_slot, randomness);
    let leaf = compute_unique_note_hash(
        note_nonce,
        compute_siloed_note_hash(context.this_address(), note_hash),
    );
    let found = note_hash_exists_at_anchor(context, leaf, leaf_index, sibling_path)
        & read_request_room(context);
    if found {
        // total-lint: allow predicated on found, which includes read_request_room; the push has room
        context.assert_note_exists(NoteExistenceRequest::for_settled(leaf));
    }
    (mask_note(note, found), found)
}

mod tests {
    use crate::key_note::KeyNote;
    use aztec::context::{inputs::PrivateContextInputs, PrivateContext};
    use aztec::note::{HintedNote, note_metadata::NoteMetadata};
    use aztec::protocol::{address::AztecAddress, traits::FromField};

    global SLOT: Field = 7;

    fn context() -> PrivateContext {
        // A zeroed call: this_address is 0.
        PrivateContext::new(std::mem::zeroed::<PrivateContextInputs>(), 0)
    }

    fn hinted(x: Field, owner: Field, slot: Field, randomness: Field) -> HintedNote<KeyNote> {
        HintedNote {
            note: KeyNote { x, y: x + 1 },
            contract_address: AztecAddress::zero(),
            owner: AztecAddress::from_field(owner),
            randomness,
            storage_slot: slot,
            metadata: NoteMetadata::from_raw_data(false, 0x55),
        }
    }

    fn read_requests(context: PrivateContext) -> u32 {
        context.finish().note_hash_read_requests.length
    }

    /// The note hash an honest hint reports for hint (view_notes_or): the
    /// hinted note's own, computed in Brillig as the hint computes it, 0
    /// for none.
    unconstrained fn hint_hash<Note>(hint: Option<HintedNote<Note>>) -> Field
    where
        Note: NoteHash,
    {
        let mut hash = 0;
        if hint.is_some() {
            let h = hint.unwrap_unchecked();
            hash = h.note.compute_note_hash(h.owner, h.storage_slot, h.randomness);
        }
        hash
    }

    /// super::confirm_note_or with the note hash an honest hint reports.
    fn confirm_note_or<Note>(
        context: &mut PrivateContext,
        hint: Option<HintedNote<Note>>,
        owner: Option<AztecAddress>,
        slot: Field,
    ) -> (Note, bool)
    where
        Note: NoteType + NoteHash + Packable,
    {
        // Safety: test helper; the hash an honest hint reports.
        let hash = unsafe { hint_hash(hint) };
        super::confirm_note_or(context, hint, hash, owner, slot)
    }

    /// super::confirm_notes_or with the note hashes an honest hint
    /// reports.
    fn confirm_notes_or<Note, let N: u32>(
        context: &mut PrivateContext,
        hints: [Option<HintedNote<Note>>; N],
        owner: Option<AztecAddress>,
        slot: Field,
    ) -> ([Note; N], [bool; N])
    where
        Note: NoteType + NoteHash + Packable,
    {
        // Safety: test helper; the hashes an honest hint reports.
        let hashes = hints.map(|h| unsafe { hint_hash(h) });
        super::confirm_notes_or(context, hints, hashes, owner, slot)
    }

    /// A hint that does not match reads as not found, with nothing emitted.
    fn assert_not_found(hint: HintedNote<KeyNote>, owner: Option<AztecAddress>) {
        let mut context = context();
        let (note, found) = confirm_note_or(&mut context, Option::some(hint), owner, SLOT);
        assert(!found);
        assert_eq(note, KeyNote { x: 0, y: 0 });
        assert_eq(read_requests(context), 0);
    }

    #[test]
    fn missing_note_is_a_flag_and_emits_nothing() {
        let mut context = context();
        let (note, found) = confirm_note_or::<KeyNote>(
            &mut context,
            Option::none(),
            Option::some(AztecAddress::from_field(3)),
            SLOT,
        );
        assert(!found);
        assert_eq(note, KeyNote { x: 0, y: 0 });
        assert_eq(read_requests(context), 0);
    }

    #[test]
    fn found_note_is_returned_with_one_read_request() {
        let mut context = context();
        let (note, found) = confirm_note_or(
            &mut context,
            Option::some(hinted(5, 3, SLOT, 9)),
            Option::some(AztecAddress::from_field(3)),
            SLOT,
        );
        assert(found);
        assert_eq(note, KeyNote { x: 5, y: 6 });
        assert_eq(read_requests(context), 1);
    }

    #[test]
    fn wrong_owner_slot_or_contract_is_not_found() {
        assert_not_found(
            hinted(5, 4, SLOT, 9),
            Option::some(AztecAddress::from_field(3)),
        );
        assert_not_found(hinted(5, 3, SLOT + 1, 9), Option::none());
        let mut h = hinted(5, 3, SLOT, 9);
        h.contract_address = AztecAddress::from_field(0x99);
        assert_not_found(h, Option::none());
    }

    #[test]
    fn notes_found_individually_and_only_found_ones_are_requested() {
        let mut context = context();
        let owner = Option::some(AztecAddress::from_field(3));
        let hints = [
            Option::some(hinted(5, 3, SLOT, 1)),
            Option::none(),
            Option::some(hinted(8, 3, SLOT, 2)),
        ];
        let (notes, found) = confirm_notes_or(&mut context, hints, owner, SLOT);
        assert_eq(found, [true, false, true]);
        assert_eq(notes[0], KeyNote { x: 5, y: 6 });
        assert_eq(notes[1], KeyNote { x: 0, y: 0 });
        assert_eq(notes[2], KeyNote { x: 8, y: 9 });
        assert_eq(read_requests(context), 2);
    }

    #[test]
    fn a_repeated_note_counts_once() {
        let mut context = context();
        let h = hinted(5, 3, SLOT, 1);
        let (notes, found) = confirm_notes_or(
            &mut context,
            [Option::some(h), Option::some(h)],
            Option::none(),
            SLOT,
        );
        assert_eq(found, [true, false]);
        assert_eq(notes[1], KeyNote { x: 0, y: 0 });
        assert_eq(read_requests(context), 1);
        // the same contents with other randomness is another note
        let mut context2 = super::tests::context();
        let (_, found2) = confirm_notes_or(
            &mut context2,
            [Option::some(h), Option::some(hinted(5, 3, SLOT, 2))],
            Option::none(),
            SLOT,
        );
        assert_eq(found2, [true, true]);
    }

    #[test]
    fn a_mismatched_note_in_a_set_is_not_found() {
        let mut context = context();
        let owner = Option::some(AztecAddress::from_field(3));
        let (notes, found) = confirm_notes_or(
            &mut context,
            [Option::some(hinted(5, 3, SLOT, 1)), Option::some(hinted(6, 4, SLOT, 2))],
            owner,
            SLOT,
        );
        assert_eq(found, [true, false]);
        assert_eq(notes[1], KeyNote { x: 0, y: 0 });
        assert_eq(read_requests(context), 1);
    }

    // A mismatched copy does not hide a matching later note of the same
    // hash: dedupe only counts found copies.
    #[test]
    fn a_mismatched_copy_does_not_shadow_a_match() {
        let mut context = context();
        let good = hinted(5, 3, SLOT, 1);
        let mut bad = good;
        bad.contract_address = AztecAddress::from_field(0x99);
        let (_, found) = confirm_notes_or(
            &mut context,
            [Option::some(bad), Option::some(good)],
            Option::none(),
            SLOT,
        );
        assert_eq(found, [false, true]);
    }

    /// x as a witness, so a test reaches the constraints instead of being
    /// folded at compile time (the print oracle keeps the call).
    unconstrained fn opaque<T>(x: T) -> T {
        std::print("");
        x
    }

    fn wit<T>(x: T) -> T {
        // Safety: test-only witness construction; no constraint needed.
        unsafe {
            opaque(x)
        }
    }

    use aztec::context::PrivateContext as Context;
    use aztec::note::note_interface::{NoteHash, NoteType};
    use aztec::protocol::{hash::poseidon2_hash, traits::{Packable, ToField}};

    /// A hand-written note whose hash asserts on its contents, as a
    /// NoteHash impl outside the #[note] derive may.
    #[derive(Eq, Packable)]
    struct StrictNote {
        value: Field,
    }

    impl NoteType for StrictNote {
        fn get_id() -> Field {
            0x57
        }
    }

    impl NoteHash for StrictNote {
        fn compute_note_hash(
            self,
            owner: AztecAddress,
            storage_slot: Field,
            randomness: Field,
        ) -> Field {
            assert(self.value != 0, "StrictNote: zero value");
            poseidon2_hash([self.value, owner.to_field(), storage_slot, randomness])
        }

        fn compute_nullifier(
            self,
            _context: &mut Context,
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

    fn strict(value: Field, slot: Field, randomness: Field) -> HintedNote<StrictNote> {
        HintedNote {
            note: StrictNote { value },
            contract_address: AztecAddress::zero(),
            owner: AztecAddress::from_field(3),
            randomness,
            storage_slot: slot,
            metadata: NoteMetadata::from_raw_data(false, 0x55),
        }
    }

    // The note hash runs only for matching notes: the zeroed note of an
    // empty slot and a mismatched hint (here with value 0) never reach a
    // NoteHash impl that asserts on them.
    #[test]
    fn empty_and_mismatched_slots_never_reach_the_note_hash() {
        let mut context = context();
        let hints = wit([
            Option::some(strict(5, SLOT, 1)),
            Option::none(),
            Option::some(strict(0, SLOT + 1, 2)),
        ]);
        // Safety: test helper; the hash an honest hint reports for the
        // first, and 0 for the others (an honest hint drops them).
        let hashes = [unsafe { hint_hash(hints[0]) }, 0, 0];
        let (notes, found) =
            super::confirm_notes_or(&mut context, hints, wit(hashes), Option::none(), SLOT);
        assert_eq(found, [true, false, false]);
        assert_eq(
            notes,
            [StrictNote { value: 5 }, StrictNote { value: 0 }, StrictNote { value: 0 }],
        );
        assert_eq(read_requests(context), 1);
    }

    fn context_at(address: Field) -> PrivateContext {
        let mut inputs = std::mem::zeroed::<PrivateContextInputs>();
        inputs.call_context.contract_address = AztecAddress::from_field(address);
        PrivateContext::new(inputs, 0)
    }

    use super::genuine_note_or;
    use aztec::messages::logs::note::MAX_NOTE_PACKED_LEN;

    // The raw width view_notes_or asks for when reading a KeyNote.
    global W: u32 = 8 + MAX_NOTE_PACKED_LEN;

    /// fields, zero-padded to W, as the PXE returns one note.
    fn raw<let K: u32>(fields: [Field; K]) -> [Field; W] {
        let mut r = [0; W];
        for i in 0..K {
            r[i] = fields[i];
        }
        r
    }

    unconstrained fn keeps<Note>(r: [Field; W], this: Field) -> bool
    where
        Note: Packable,
    {
        genuine_note_or::<Note, W>(r, AztecAddress::from_field(this)).is_some()
    }

    // Genuine KeyNote packings in each stage are kept; the metadata the
    // PXE never produces is not: a stage that only truncates to 3, a
    // settled or previous-phase note with nonce 0 or a small nonce, a
    // same-phase note with a nonce, a nonzero Field after the nonce,
    // another contract.
    #[test]
    unconstrained fn the_hint_filter_keeps_exactly_the_genuine_layout() {
        let this = 0xc0;
        let (o, r, s) = (0xa1, 0x5eed, 7);
        assert(keeps::<KeyNote>(raw([5, 6, this, o, r, s, 3, 0x55]), this));
        assert(keeps::<KeyNote>(raw([5, 6, this, o, r, s, 1, 0]), this));
        assert(keeps::<KeyNote>(raw([5, 6, this, o, r, s, 2, 0x66]), this));
        assert(!keeps::<KeyNote>(raw([5, 6, this, o, r, s, 0x103, 0x55]), this));
        assert(!keeps::<KeyNote>(raw([5, 6, this, o, r, s, 3, 0]), this));
        assert(!keeps::<KeyNote>(raw([5, 6, this, o, r, s, 3, 2]), this));
        assert(!keeps::<KeyNote>(raw([5, 6, this, o, r, s, 2, 0]), this));
        assert(!keeps::<KeyNote>(raw([5, 6, this, o, r, s, 1, 9]), this));
        assert(!keeps::<KeyNote>(raw([5, 6, this, o, r, s, 3, 0x55, 1]), this));
        assert(!keeps::<KeyNote>(raw([5, 6, 0xc1, o, r, s, 3, 0x55]), this));
        assert(!keeps::<KeyNote>(raw([5, 6, this, o, r, s, 0, 0]), this));
    }

    // A one-Field note owned by contract 0xc0 itself, settled with nonce
    // 0x777, as the PXE returns it to a two-Field KeyNote read: every field
    // after the note moves one place (the contract reads the owner, the
    // owner the randomness, the slot the stage code 3, the stage the
    // nonce). Read straight into a HintedNote, as aztec-nr's get_notes
    // does, the contract, owner and slot match at slot 3 with an owner
    // filter equal to the randomness. The hint filter drops it (the stage
    // position holds the nonce, not 1, 2 or 3), so the read is found =
    // false with no read request; fed past the filter, metadata_ok
    // rejects the stage the u8 cast makes of the nonce (0x77).
    #[test]
    fn a_narrower_contract_owned_note_is_not_found() {
        let this = 0xc0;
        let (v, randomness, nonce) = (0x1234, 0x5eed, 0x0777);
        let narrow = [v, this, this, randomness, 3, 3, nonce];
        // Safety: test of the hint's filter on one oracle answer.
        let kept = unsafe { keeps::<KeyNote>(raw(narrow), this) };
        assert(!kept);
        let owner = Option::some(AztecAddress::from_field(randomness));
        let mut context = context_at(this);
        let (_, found) = confirm_note_or::<KeyNote>(&mut context, Option::none(), owner, 3);
        assert_eq((found, read_requests(context)), (false, 0));
        let bypass: HintedNote<KeyNote> =
            HintedNote::unpack(wit([v, this, this, randomness, 3, 3, nonce, 0]));
        let mut context = context_at(this);
        let (_, found) = confirm_note_or(&mut context, Option::some(bypass), owner, 3);
        assert_eq((found, read_requests(context)), (false, 0));
    }

    // The residual of the layout filter, exactly: a note one Field
    // narrower passes it only when its nonce is 1, which lands as stage 1
    // with the padding 0 as its nonce; a kernel nonce (a Poseidon2 output)
    // is 1 with probability 1/p. It then reads as a pending note, which
    // hash_ok finds only if this call pushed the note hash the reader
    // computes for it, and then its read request holds; here nothing was
    // pushed, so it is found = false with nothing emitted.
    #[test]
    fn the_layout_residual_reads_as_an_unpushed_pending_note() {
        let this = 0xc0;
        let (v, randomness) = (0x1234, 0x5eed);
        // Safety: test of the hint's filter on one oracle answer.
        let kept = unsafe { keeps::<KeyNote>(raw([v, this, this, randomness, 3, 3, 1]), this) };
        assert(kept);
        let bypass: HintedNote<KeyNote> =
            HintedNote::unpack(wit([v, this, this, randomness, 3, 3, 1, 0]));
        let mut context = context_at(this);
        let owner = Option::some(AztecAddress::from_field(randomness));
        let (_, found) = confirm_note_or(&mut context, Option::some(bypass), owner, 3);
        assert_eq((found, read_requests(context)), (false, 0));
    }

    /// KeyNote {x, x + 1} of owner 3 at SLOT with randomness 9, pending in
    /// this phase in contract 0xc0.
    fn pending(x: Field) -> HintedNote<KeyNote> {
        let mut h = hinted(x, 3, SLOT, 9);
        h.contract_address = AztecAddress::from_field(0xc0);
        h.metadata = NoteMetadata::from_raw_data(true, 0);
        h
    }

    fn key_note_hash(x: Field) -> Field {
        KeyNote { x, y: x + 1 }.compute_note_hash(AztecAddress::from_field(3), SLOT, 9)
    }

    // A pending note is found only when this call pushed the note hash the
    // reader computes for it (by create_note or any other push), and its
    // read request then names exactly that hash and this contract, which
    // the kernel accepts. Not pushed, or another note hash pushed (what a
    // hand-written NoteHash or a raw notify_created_note leaves behind):
    // found = false, nothing emitted.
    #[test]
    fn a_pending_note_is_found_only_when_this_call_pushed_its_hash() {
        let owner = Option::some(AztecAddress::from_field(3));
        let none = (KeyNote { x: 0, y: 0 }, false, 0);
        let read = |pushes: [Field; 2]| {
            let mut context = context_at(0xc0);
            for i in 0..2 {
                if pushes[i] != 0 {
                    context.push_note_hash(pushes[i]);
                }
            }
            let (note, found) =
                confirm_note_or(&mut context, Option::some(wit(pending(5))), owner, SLOT);
            (note, found, context.finish().note_hash_read_requests)
        };
        let (note, found, requests) = read([0, 0]);
        assert_eq((note, found, requests.length), none);
        let (note, found, requests) = read(wit([key_note_hash(6), 0]));
        assert_eq((note, found, requests.length), none);
        let (note, found, requests) = read(wit([key_note_hash(6), key_note_hash(5)]));
        assert_eq((note, found, requests.length), (KeyNote { x: 5, y: 6 }, true, 1));
        assert_eq(requests.array[0].inner.inner, key_note_hash(5));
        assert_eq(requests.array[0].contract_address, AztecAddress::from_field(0xc0));
    }

    // The same in a set read: each pending note needs its own pushed hash.
    #[test]
    fn a_set_read_finds_only_the_pushed_pending_notes() {
        let mut context = context_at(0xc0);
        context.push_note_hash(wit(key_note_hash(7)));
        let (_, found) = confirm_notes_or(
            &mut context,
            wit([Option::some(pending(5)), Option::some(pending(7))]),
            Option::some(AztecAddress::from_field(3)),
            SLOT,
        );
        assert_eq(found, [false, true]);
        assert_eq(read_requests(context), 1);
    }

    // A hint that reports another note hash than the one the circuit
    // computes is not found: the read request would not name the note hash
    // the hint checked.
    #[test]
    fn a_hint_hash_other_than_the_circuits_is_not_found() {
        let mut context = context();
        let h = wit(hinted(5, 3, SLOT, 9));
        let (_, found) = super::confirm_note_or(
            &mut context,
            Option::some(h),
            wit(key_note_hash(5) + 1),
            Option::none(),
            SLOT,
        );
        assert_eq((found, read_requests(context)), (false, 0));
        let mut context = super::tests::context();
        let (_, found) = super::confirm_note_or(
            &mut context,
            Option::some(h),
            wit(key_note_hash(5)),
            Option::none(),
            SLOT,
        );
        assert_eq((found, read_requests(context)), (true, 1));
    }

    /// A hand-written note whose hash is KeyNote's in Brillig and another
    /// value in ACIR: the hint checks one note hash and the circuit
    /// requests another. No compiled reader shows it (only the ACIR branch
    /// of is_unconstrained is compiled into the circuit).
    #[derive(Eq, Packable)]
    struct TwoFaceNote {
        x: Field,
        y: Field,
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
            let h =
                KeyNote { x: self.x, y: self.y }.compute_note_hash(owner, storage_slot, randomness);
            if std::runtime::is_unconstrained() {
                h
            } else {
                h + 1
            }
        }

        fn compute_nullifier(
            self,
            _context: &mut Context,
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

    fn two_face(h: HintedNote<KeyNote>) -> HintedNote<TwoFaceNote> {
        HintedNote {
            note: TwoFaceNote { x: h.note.x, y: h.note.y },
            contract_address: h.contract_address,
            owner: h.owner,
            randomness: h.randomness,
            storage_slot: h.storage_slot,
            metadata: h.metadata,
        }
    }

    // A KeyNote read as a TwoFaceNote, settled (the hint found KeyNote's
    // note hash among the PXE's settled notes) or pending (KeyNote's note
    // hash pushed): the circuit's hash differs from the hint's and from
    // every pushed one, so it is found = false, never a read request for a
    // note hash nobody committed.
    #[test]
    fn a_hash_that_differs_between_hint_and_circuit_is_not_found() {
        let owner = Option::some(AztecAddress::from_field(3));
        let mut context = context();
        let settled = wit(two_face(hinted(5, 3, SLOT, 9)));
        let (_, found) = confirm_note_or(&mut context, Option::some(settled), owner, SLOT);
        assert_eq((found, read_requests(context)), (false, 0));
        let mut context = context_at(0xc0);
        context.push_note_hash(wit(key_note_hash(5)));
        let (_, found) = confirm_note_or(
            &mut context,
            Option::some(wit(two_face(pending(5)))),
            owner,
            SLOT,
        );
        assert_eq((found, read_requests(context)), (false, 0));
    }

    /// A hand-written note whose note hash is its value.
    #[derive(Eq, Packable)]
    struct HashNote {
        value: Field,
    }

    impl NoteType for HashNote {
        fn get_id() -> Field {
            0x3f
        }
    }

    impl NoteHash for HashNote {
        fn compute_note_hash(
            self,
            _owner: AztecAddress,
            _slot: Field,
            _randomness: Field,
        ) -> Field {
            self.value
        }

        fn compute_nullifier(
            self,
            _context: &mut Context,
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

    // A pending note whose note hash is 0 is not found, even when 0 was
    // pushed (the positions past the pushed length read as 0 as well).
    #[test]
    fn a_pending_note_hash_of_zero_is_not_found() {
        let owner = Option::some(AztecAddress::from_field(3));
        let note = HintedNote {
            note: HashNote { value: 0 },
            contract_address: AztecAddress::from_field(0xc0),
            owner: AztecAddress::from_field(3),
            randomness: 9,
            storage_slot: SLOT,
            metadata: NoteMetadata::from_raw_data(true, 0),
        };
        let mut context = context_at(0xc0);
        let (_, found) = confirm_note_or(&mut context, Option::some(wit(note)), owner, SLOT);
        assert_eq((found, read_requests(context)), (false, 0));
        let mut context = context_at(0xc0);
        context.push_note_hash(wit(0));
        let (_, found) = confirm_note_or(&mut context, Option::some(wit(note)), owner, SLOT);
        assert_eq((found, read_requests(context)), (false, 0));
        let mut context = context_at(0xc0);
        context.push_note_hash(wit(0x77));
        let mut seven = note;
        seven.note = HashNote { value: 0x77 };
        let (_, found) = confirm_note_or(&mut context, Option::some(wit(seven)), owner, SLOT);
        assert_eq((found, read_requests(context)), (true, 1));
    }

    // A note one Field wider, pending in this phase (stage 1, nonce 0) at
    // slot 2, with its last field and randomness chosen to make the
    // shifted contract and slot match: the shifted stage is the slot 2 and
    // the shifted nonce the stage code 1, which no kernel nonce is. Two or
    // more Fields wider, its stage code lands after the nonce position,
    // where the filter wants 0.
    #[test]
    unconstrained fn a_wider_note_is_dropped_by_the_hint() {
        let this = 0xc0;
        assert(!keeps::<KeyNote>(raw([1, 2, this, this, 0xa1, 2, 2, 1, 0]), this));
        assert(!keeps::<KeyNote>(raw([1, 2, this, 9, this, 0xa1, 2, 2, 1, 0]), this));
        // settled one Field wider: its nonce lands after the nonce position
        assert(!keeps::<KeyNote>(raw([1, 2, this, this, 0xa1, 2, 2, 3, 0x55]), this));
    }

    /// A note with an integer member, for the canonical-packing check.
    #[derive(Eq, Packable)]
    struct ByteNote {
        b: u8,
        f: Field,
    }

    // A non-canonical packing (a u8 member holding 0x105) unpacks by
    // truncation to another note, so it would hash to a note hash that
    // was never committed; the filter drops it because the note re-packs
    // to other Fields. The canonical packing is kept.
    #[test]
    unconstrained fn a_non_canonical_packing_is_dropped_by_the_hint() {
        let this = 0xc0;
        assert(keeps::<ByteNote>(raw([5, 6, this, 0xa1, 0x5eed, 7, 3, 0x55]), this));
        assert(!keeps::<ByteNote>(raw([0x105, 6, this, 0xa1, 0x5eed, 7, 3, 0x55]), this));
    }

    use super::{check_note_hash_witness, note_hash_exists_at_anchor};
    use aztec::protocol::{
        constants::NOTE_HASH_TREE_HEIGHT,
        merkle_tree::{merkle_hash, root::root_from_sibling_path},
    };

    // A note hash tree with leaves 0x11, 0x22, 0x33 at indices 0..2, every
    // other position empty (0): the sibling path of index.
    fn note_path(index: u32) -> [Field; NOTE_HASH_TREE_HEIGHT] {
        path_in([0x11, 0x22, 0x33, 0], index)
    }

    fn note_root() -> Field {
        root_from_sibling_path(0x11, 0, note_path(0))
    }

    #[test]
    fn leaf_on_its_path_exists() {
        let r = note_root();
        assert(check_note_hash_witness(r, 0x11, 0, note_path(0)));
        assert(check_note_hash_witness(r, 0x33, 2, note_path(2)));
    }

    // Every wrong witness is a flag, as witnesses of the constraint (so the
    // checks run in the circuit, not at compile time): an absent leaf, a
    // real leaf on another path or index, the all-zero path, the empty
    // position 3 (its path proves the leaf 0, which is refused), and an
    // index at or above 2^NOTE_HASH_TREE_HEIGHT (aztec-nr's
    // check_membership asserts the index fits 42 bits; is_member flags
    // it).
    #[test]
    fn absent_leaf_wrong_path_and_wide_index_are_flags() {
        let r = note_root();
        let check = |leaf: Field, index: Field, path| {
            check_note_hash_witness(r, wit(leaf), wit(index), wit(path))
        };
        assert(!check(0x44, 0, note_path(0)));
        assert(!check(0x22, 0, note_path(0)));
        assert(!check(0x22, 2, note_path(1)));
        assert(!check(0x11, 0, [0; NOTE_HASH_TREE_HEIGHT]));
        assert(!check(0, 3, note_path(3)));
        assert(!check(0x11, 0x40000000000, note_path(0)));
        assert(!check(0x11, -1, note_path(0)));
        assert(check(0x11, 0, note_path(0)));
    }

    // The anchor-block form reads the context's root and needs no oracle:
    // a leaf that is not in the tree, with any witness the caller passes,
    // is false. (The PXE's witness oracle throws on an absent leaf.)
    #[test]
    fn an_absent_leaf_at_the_anchor_is_false_without_an_oracle() {
        let h = [0x11, 0x22, 0x33, 0];
        let mut context = context_with_tree(0xc0, h);
        assert(note_hash_exists_at_anchor(&mut context, wit(0x22), wit(1), wit(path_in(h, 1))));
        assert(!note_hash_exists_at_anchor(&mut context, wit(0x44), wit(1), wit(path_in(h, 1))));
        assert(!note_hash_exists_at_anchor(&mut context, wit(0x44), wit(3), wit(path_in(h, 3))));
        assert_eq(read_requests(context), 0);
    }

    // The read budget: a call holds 16 note hash read requests. The
    // seventeenth matching note reads as found = false with nothing pushed
    // (a push past 16 fails BoundedVec's bound), in both read forms.
    #[test]
    fn a_read_past_the_budget_is_not_found() {
        let mut context = context();
        let owner = Option::some(AztecAddress::from_field(3));
        for i in 0..16 {
            let (_, found) = confirm_note_or(
                &mut context,
                Option::some(wit(hinted(5, 3, SLOT, i as Field))),
                owner,
                SLOT,
            );
            assert(found);
        }
        let (note, found) = confirm_note_or(
            &mut context,
            Option::some(wit(hinted(5, 3, SLOT, 99))),
            owner,
            SLOT,
        );
        assert_eq((note, found), (KeyNote { x: 0, y: 0 }, false));
        let (_, found_set) = confirm_notes_or(
            &mut context,
            wit([Option::some(hinted(6, 3, SLOT, 1))]),
            owner,
            SLOT,
        );
        assert_eq(found_set, [false]);
        assert_eq(read_requests(context), 16);
    }

    #[test]
    fn a_set_read_stops_at_the_budget() {
        let mut context = context();
        let owner = Option::some(AztecAddress::from_field(3));
        let mut hints = [Option::none(); 16];
        for i in 0..16 {
            hints[i] = Option::some(hinted(5, 3, SLOT, i as Field));
        }
        let (_, first) = confirm_notes_or(&mut context, wit(hints), owner, SLOT);
        assert_eq(first, [true; 16]);
        let (_, second) = confirm_notes_or(
            &mut context,
            wit(
                [Option::some(hinted(7, 3, SLOT, 1)), Option::some(hinted(8, 3, SLOT, 2))],
            ),
            owner,
            SLOT,
        );
        assert_eq(second, [false, false]);
        assert_eq(read_requests(context), 16);
    }

    use super::get_settled_note_from_witness_or;
    use aztec::protocol::hash::{compute_siloed_note_hash, compute_unique_note_hash};

    /// A note hash tree with leaves h at indices 0..3, every other
    /// position empty: the sibling path of index.
    fn path_in(h: [Field; 4], index: u32) -> [Field; NOTE_HASH_TREE_HEIGHT] {
        let mut z = [0; NOTE_HASH_TREE_HEIGHT];
        for i in 1..NOTE_HASH_TREE_HEIGHT {
            z[i] = merkle_hash(z[i - 1], z[i - 1]);
        }
        let mut p = z;
        p[0] = h[index ^ 1];
        p[1] = if index < 2 {
            merkle_hash(h[2], h[3])
        } else {
            merkle_hash(h[0], h[1])
        };
        p
    }

    /// The unique note hash of KeyNote {x, x + 1} of contract this at
    /// (owner 3, SLOT, randomness 9) with nonce.
    fn unique_key_note_hash(this: Field, x: Field, nonce: Field) -> Field {
        let note = KeyNote { x, y: x + 1 };
        let h = note.compute_note_hash(AztecAddress::from_field(3), SLOT, 9);
        compute_unique_note_hash(
            nonce,
            compute_siloed_note_hash(AztecAddress::from_field(this), h),
        )
    }

    /// A call of contract this whose anchor note hash tree holds the
    /// leaves h.
    fn context_with_tree(this: Field, h: [Field; 4]) -> PrivateContext {
        let mut inputs = std::mem::zeroed::<PrivateContextInputs>();
        inputs.call_context.contract_address = AztecAddress::from_field(this);
        inputs.anchor_block_header.state.partial.note_hash_tree.root =
            root_from_sibling_path(h[0], 0, path_in(h, 0));
        PrivateContext::new(inputs, 0)
    }

    fn read_from_witness(
        this: Field,
        h: [Field; 4],
        x: Field,
        randomness: Field,
        nonce: Field,
        index: Field,
        path: [Field; NOTE_HASH_TREE_HEIGHT],
    ) -> (KeyNote, bool, u32) {
        let mut context = context_with_tree(this, h);
        let (note, found) = get_settled_note_from_witness_or(
            &mut context,
            wit(KeyNote { x, y: x + 1 }),
            AztecAddress::from_field(3),
            SLOT,
            wit(randomness),
            wit(nonce),
            wit(index),
            wit(path),
        );
        (note, found, read_requests(context))
    }

    // A committed note with its witness is found with one read request;
    // a wrong path, index, nonce, randomness, note or contract, and an
    // index at or above 2^NOTE_HASH_TREE_HEIGHT, read as found = false
    // with nothing emitted, never as a failure.
    #[test]
    fn a_settled_note_read_from_its_witness_is_determined_by_the_arguments() {
        let this = 0xc0;
        let leaf = unique_key_note_hash(this, 5, 0x55);
        let h = [0x11, leaf, 0x33, 0];
        let path = path_in(h, 1);
        let none = (KeyNote { x: 0, y: 0 }, false, 0);
        assert_eq(
            read_from_witness(this, h, 5, 9, 0x55, 1, path),
            (KeyNote { x: 5, y: 6 }, true, 1),
        );
        assert_eq(read_from_witness(this, h, 5, 9, 0x55, 1, path_in(h, 0)), none);
        assert_eq(read_from_witness(this, h, 5, 9, 0x55, 3, path), none);
        assert_eq(read_from_witness(this, h, 5, 9, 0x56, 1, path), none);
        assert_eq(read_from_witness(this, h, 5, 8, 0x55, 1, path), none);
        assert_eq(read_from_witness(this, h, 6, 9, 0x55, 1, path), none);
        assert_eq(read_from_witness(0xc1, h, 5, 9, 0x55, 1, path), none);
        assert_eq(read_from_witness(this, h, 5, 9, 0x55, 1 + 0x40000000000, path), none);
    }
}
