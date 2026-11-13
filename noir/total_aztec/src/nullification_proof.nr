//! Consuming another account's note with the owner's proof of
//! nullification: the executor side.
//!
//! # The setting
//!
//! Account B owns a note in contract A's storage. A third party E (the
//! executor) wants A to consume that note in E's transaction: read its
//! value and push its nullifier, exactly as if B had spent it. E's PXE
//! lacks B's nullifier hiding key, so aztec-nr's own path (the #[note]
//! derive's compute_nullifier, which calls
//! PrivateContext::request_nhk_app) cannot run there.
//!
//! B consents off-line instead: B's PXE proves the standalone circuit
//! `prove_nullification` (examples/nullification_proof) over the note's
//! preimage and B's app-siloed nullifier hiding key, and hands E the
//! (vk, proof) with the note's fields, leaf and nullifier. E adds the
//! leaf's index and sibling path in the note hash tree at its anchor
//! block and passes the whole handoff to A as a function argument; A
//! calls consume_with_nullification_proof_or, which verifies the proof
//! recursively under a pinned vk hash and a pinned key commitment, checks
//! the leaf's path to the anchor block's note hash tree root, and pushes
//! the nullifier.
//!
//! # What the proof binds
//!
//! Public inputs, in the owner circuit's order (nullification_public_inputs):
//!
//! ```text
//! [contract_address, storage_slot, owner, executor, expiry, fields[0..N],
//!  leaf, nullifier, npk_app_hash]
//! ```
//!
//! - leaf = unique_note_hash(contract_address, note_hash, nonce) and
//!   nullifier = P2(DOM_SEP__NOTE_NULLIFIER, leaf, nhk_app), the values
//!   aztec-nr's #[note] derive computes for a settled note
//!   (note/utils.nr, compute_note_nullifier).
//! - npk_app_hash = P2(DOM_SEP__NPK_APP_HASH, nhk_app), the commitment A
//!   pins.
//! - executor (compared with A's msg_sender; 0 = anyone) and expiry (the
//!   anchor block number must be below it; 0 = never) are B's optional
//!   binding, checked as flags.
//!
//! A builds the address, slot, owner and pin itself, so a proof for
//! another contract, slot, owner or key does not verify. The proof does
//! not show the leaf was ever inserted (B can prove over any preimage),
//! so A checks the leaf's membership itself, from the index and path in
//! the handoff, as a flag. No chain id or
//! protocol version is bound: a proof is usable on another network only
//! where the same contract address holds the same leaf under the same
//! pin, i.e. a fork or re-genesis with identical state; bind them as
//! further public inputs if that matters.
//!
//! # Why the pin must come from a kernel-validated registration
//!
//! The owner circuit cannot check that nhk_app is B's canonical key, so
//! anyone who knows a note's preimage can prove with any key k, producing
//! a non-canonical nullifier that leaves the note spendable by B. The pin
//! rules this out: registered_npk_app_hash computes it in B's own
//! transaction, where the kernel validates the key against B's npk_m_hash
//! and get_public_keys proves that against B's address. A stores it (the
//! example uses a PublicImmutable per owner) and passes the stored value.
//! Never take the pin from the executor's arguments.
//! registered_npk_app_hash works only in the owner's own transaction (the
//! key oracle throws in any other PXE), and nothing in it can flag that:
//! its call site carries the total-lint justification marker that says so.
//!
//! # Totality
//!
//! ok = vk_ok & pin_ok & in_tree & !spent & executor_ok & expiry_ok &
//! !is_static_call & room, and the recursive verification and the
//! nullifier push run only under ok (a nullifier pushed under a static
//! call would make the kernel reject the transaction; room says the call
//! holds fewer than 16 nullifiers, so the push cannot overflow). Every
//! term is computed from the handoff, the pin and the anchor block, with
//! no oracle, so ok is determined by the arguments and the anchor block.
//! The verification is the RecursiveAggregation black box, which carries
//! its branch condition as a predicate: the ACVM never checks the proof,
//! bb proves the circuit with the predicate 0 whatever the proof bytes,
//! and cannot prove it with the predicate 1 and an invalid proof
//! (docs/toolchain-semantics.md, section 3, including a run on an Aztec
//! 6.0.0 network with client-side proving).
//!
//! So no state B or anyone else can create makes E's transaction
//! unprovable: a withheld proof (E passes NullificationProof::withheld(),
//! all zeros), a never-settled or spent note, a wrong index or path, a
//! proof bound to another executor or an expired one all read as
//! ok = false with nothing nullified, as does a consume reached through a
//! static call. The one case A cannot flag is a handoff whose flags all
//! hold and whose proof does not verify for A's public inputs: it
//! simulates with ok = true and then proving fails. Recursive
//! verification has no flag form, so whoever supplies the handoff
//! chooses this: E when E's own call passes it, or the code of the
//! contract that passes it to A. The library therefore does not justify
//! the verification; each call site carries a total-lint justification marker
//! saying where its handoff comes from (otherwise the lint reports the
//! RecursiveAggregation item). E's pre-check
//! (examples/nullification_proof/README.md) catches a non-verifying
//! proof before E sends it.
//!
//! # Why arguments, not a capsule
//!
//! The handoff is a function argument. A capsule fails two of the
//! conditions for oracle data (docs/design.md, "Oracle data and provable
//! error codes"): nothing commits to its contents, and the read can
//! abort. PXE 6.0.0's getCapsule returns the stored array at its stored
//! length (it pads only a missing capsule), so a capsule of another
//! length stops witness generation, and the contract's own code can
//! store one at any slot of its own in the global scope, where only a
//! transient capsule on the transaction request overshadows it. As an
//! argument the handoff is hashed into the call's args_hash, every member
//! is a Field (no decoding can fail), and the leaf's membership is checked
//! from the index and sibling path it carries instead of through an
//! oracle that throws on an absent leaf.
//!
//! # Gate cost
//!
//! examples/nullification_proof/README.md, "Gate counts". The handoff is
//! 621 Fields, hashed into args_hash by the function's prologue.

use crate::init::nullifier_exists_at_anchor;
use crate::note::check_note_hash_witness;
use aztec::context::PrivateContext;
use aztec::keys::getters::get_public_keys;
use aztec::protocol::address::AztecAddress;
use aztec::protocol::constants::{
    MAX_NULLIFIERS_PER_CALL, NOTE_HASH_TREE_HEIGHT, RECURSIVE_PROOF_LENGTH,
    ULTRA_VK_LENGTH_IN_FIELDS,
};
use aztec::protocol::hash::{poseidon2_hash, poseidon2_hash_with_separator};
use aztec::protocol::traits::{Deserialize, Serialize, ToField};
use total::{eq, is_zero, lt};

/// ZK UltraHonk, the proof type bb writes for `-t noir-recursive`. The
/// protocol constants do not export it (the enum slot between
/// ROOT_ROLLUP_HONK = 5 and HN_FINAL = 7).
pub global PROOF_TYPE_HONK_ZK: u32 = 6;
/// Fields in a ZK UltraHonk proof: the non-ZK recursive length plus 48.
pub global ZK_PROOF_LENGTH: u32 = RECURSIVE_PROOF_LENGTH + 48; // 458
/// Fields in an UltraHonk verification key.
pub global VK_LENGTH: u32 = ULTRA_VK_LENGTH_IN_FIELDS; // 115

/// Domain separator of npk_app_hash. The owner circuit
/// (examples/nullification_proof/prove_nullification) repeats it; the
/// executor example's TXE test fails if the two disagree.
pub global DOM_SEP__NPK_APP_HASH: u32 = 0x6e706b61; // "npka"

/// What the executor passes for one consume, as a function argument: the
/// owner's (vk, proof), the values the proof binds that A cannot compute
/// (executor, expiry, fields, leaf, nullifier), and the leaf's index and
/// sibling path in the note hash tree at E's anchor block (an Aztec
/// node's findLeavesIndexes and getNoteHashSiblingPath). Every member is
/// a Field, so the argument has no range checks and nothing to decode.
#[derive(Deserialize, Serialize)]
pub struct NullificationProof<let N: u32> {
    pub vk: [Field; VK_LENGTH],
    pub proof: [Field; ZK_PROOF_LENGTH],
    pub executor: Field,
    pub expiry: Field,
    pub fields: [Field; N],
    pub leaf: Field,
    pub leaf_index: Field,
    pub sibling_path: [Field; NOTE_HASH_TREE_HEIGHT],
    pub nullifier: Field,
}

impl<let N: u32> NullificationProof<N> {
    /// The handoff to pass when there is nothing to consume: all zeros,
    /// which reads as ok = false (its vk hashes to no pinned value).
    pub fn withheld() -> Self {
        std::mem::zeroed()
    }
}

/// The commitment to an app-siloed nullifier hiding key that the owner
/// circuit outputs and A pins. One Poseidon2 hash; total.
pub fn npk_app_hash(nhk_app: Field) -> Field {
    poseidon2_hash_with_separator([nhk_app], DOM_SEP__NPK_APP_HASH)
}

/// The owner's canonical npk_app_hash for this contract, for A to store
/// as the pin. Owner's own transaction only, and not total: it pushes a
/// key validation request for the owner's npk_m_hash (the PXE's key
/// oracle throws unless the executing PXE holds that account's keys in
/// scope, and only the kernel checks the request), and get_public_keys
/// expects the owner's keys registered and asserts them against the
/// owner's address. No flag can stand in for either, so this carries no
/// lint marker: its call site justifies it (examples/nullification_proof,
/// register: the owner is msg_sender, in the owner's own transaction),
/// and the lint counts that justification.
pub fn registered_npk_app_hash(context: &mut PrivateContext, owner: AztecAddress) -> Field {
    let npk_m_hash = get_public_keys(owner).npk_m_hash;
    npk_app_hash(context.request_nhk_app(npk_m_hash))
}

/// The owner circuit's public-input array, rebuilt from what A holds and
/// the handoff's claimed values. E's pre-check verifies B's proof against
/// the same array, never against a list B supplies.
pub fn nullification_public_inputs<let N: u32>(
    contract_address: AztecAddress,
    storage_slot: Field,
    owner: AztecAddress,
    executor: Field,
    expiry: Field,
    fields: [Field; N],
    leaf: Field,
    nullifier: Field,
    pinned_npk_app_hash: Field,
) -> [Field; 5 + N + 3] {
    [contract_address.to_field(), storage_slot, owner.to_field(), executor, expiry]
        .concat(fields)
        .concat([leaf, nullifier, pinned_npk_app_hash])
}

/// Flag: the executor binding admits this caller: executor = 0, or
/// msg_sender exists and equals executor (a call with no msg_sender is
/// admitted only by executor = 0).
///
/// Constraints: total::is_zero and total::eq (hint-satisfiable inversion
/// gadgets) and boolean arithmetic. Determined.
pub fn executor_ok(executor: Field, msg_sender: Option<AztecAddress>) -> bool {
    let named = msg_sender.is_some() & eq(executor, msg_sender.unwrap_unchecked().to_field());
    is_zero(executor) | named
}

/// Flag: the validity window admits this anchor block: expiry = 0, or
/// anchor_block_number < expiry in the canonical order of Field values
/// (so every expiry is defined).
///
/// Constraints: total::is_zero and total::lt on Field (canonical limbs
/// and a bounded compare), hint-satisfiable for every pair. Determined.
pub fn expiry_ok(expiry: Field, anchor_block_number: u32) -> bool {
    is_zero(expiry) | lt(anchor_block_number as Field, expiry)
}

/// Flag: the call holds fewer than MAX_NULLIFIERS_PER_CALL (16)
/// nullifiers, so one more push has room. The count is the length of the
/// context's nullifier vector, read through a copy of finish() (pure
/// wiring); one u32 comparison. Total; determined by what the call pushed
/// before.
pub fn nullifier_room(context: &mut PrivateContext) -> bool {
    // total-lint: allow u32 comparison on the context's nullifier count: the compiler's hints satisfy it for every count
    (*context).finish().nullifiers.length < MAX_NULLIFIERS_PER_CALL
}

/// Consume owner's note at storage_slot of this contract with the owner's
/// proof of nullification, passed by the caller as handoff: (fields, ok).
/// On ok = true the proof verified under expected_vk_hash and the pin,
/// its binding admits this call, the leaf is at handoff.leaf_index on
/// handoff.sibling_path below the anchor block's note hash tree root, its
/// nullifier is not in the anchor block's nullifier tree, the call is not
/// static and has room for a nullifier, one nullifier was pushed, and
/// fields are the note's packed fields. On ok = false nothing was pushed
/// and fields are zeros. Pass NullificationProof::withheld() when there
/// is nothing to consume.
///
/// pinned_npk_app_hash is the owner's registered commitment, never an
/// executor argument.
///
/// Constraints: vk_ok (a Poseidon2 hash over the 115 vk fields and an eq
/// gadget); pin_ok = pin != 0 (eq gadget; an unregistered owner reads as
/// 0); executor_ok on context.maybe_msg_sender() (no unwrap); expiry_ok
/// on the anchor block number; in_tree = check_note_hash_witness
/// (total::merkle::is_member over the handoff's index and path, no
/// assert); spent = nullifier_exists_at_anchor (determined); the call
/// context's is_static_call bit (a kernel-checked input); nullifier_room;
/// then, under ok, the RecursiveAggregation black box over (vk, proof,
/// public inputs, expected_vk_hash, HONK_ZK) and one nullifier push;
/// finally the masking products.
///
/// Classification: the push cannot overflow (room). The recursive
/// verification is backend-defined and predicated on ok (module header,
/// "Totality"); the lint reports it, and the caller's marker says where
/// the handoff comes from. Under ok the kernel accepts the nullifier
/// unless the owner spent the note between E's anchor block and E's
/// inclusion, a race at inclusion (the sequencer drops E's transaction),
/// not a circuit failure.
///
/// Determinedness: ok is determined by the handoff, the pin and the
/// anchor block (no hint on this path). ok = true is sound: it implies a
/// verifying proof for these public inputs (or the transaction cannot be
/// proved), an admitting binding, a leaf in the anchor tree and a
/// nullifier absent from it.
///
/// DEV DECISION: the owner's binding. Options: none (bearer consent),
/// executor, expiry, or both. This code: both, each optional per proof
/// (0 = unbound) in one owner circuit and one vk, checked as flags so a
/// proof that does not admit the call reads as ok = false. Consequences
/// (bearer consent, executor = immediate caller, the expiry window):
/// examples/nullification_proof/README.md.
///
/// DEV DECISION: how settledness is checked. Options: a kernel note-hash
/// read request (cheaper; a leaf that was never inserted fails E's
/// transaction), or an in-circuit flag. This code: the flag in_tree over
/// the path in the handoff, so B's proof of a never-inserted leaf, or a
/// wrong path, reads as ok = false.
pub fn consume_with_nullification_proof_or<let N: u32>(
    context: &mut PrivateContext,
    handoff: NullificationProof<N>,
    expected_vk_hash: Field,
    pinned_npk_app_hash: Field,
    storage_slot: Field,
    owner: AztecAddress,
) -> ([Field; N], bool) {
    let vk_ok = poseidon2_hash(handoff.vk) == expected_vk_hash;
    let pin_ok = pinned_npk_app_hash != 0;
    let header = context.get_anchor_block_header();
    let in_tree = check_note_hash_witness(
        header.state.partial.note_hash_tree.root,
        handoff.leaf,
        handoff.leaf_index,
        handoff.sibling_path,
    );
    let spent = nullifier_exists_at_anchor(context, handoff.nullifier);
    let bound_ok = executor_ok(handoff.executor, context.maybe_msg_sender())
        & expiry_ok(handoff.expiry, header.block_number());
    // A static call may not emit the nullifier, so it reads as ok = false.
    let ok = vk_ok
        & pin_ok
        & in_tree
        & !spent
        & bound_ok
        & !context.is_static_call()
        & nullifier_room(context);
    if ok {
        let public_inputs = nullification_public_inputs(
            context.this_address(),
            storage_slot,
            owner,
            handoff.executor,
            handoff.expiry,
            handoff.fields,
            handoff.leaf,
            handoff.nullifier,
            pinned_npk_app_hash,
        );
        std::verify_proof_with_type(
            handoff.vk,
            handoff.proof,
            public_inputs,
            expected_vk_hash,
            PROOF_TYPE_HONK_ZK,
        );
        // `(nullifier, 0)` is the push for a settled note's nullifier.
        // total-lint: allow predicated on ok, which includes nullifier_room; the push has room
        context.push_nullifier_for_note_hash(handoff.nullifier, 0);
    }
    (handoff.fields.map(|f| (ok as Field) * f), ok)
}

mod tests {
    use super::{executor_ok, expiry_ok, npk_app_hash, nullification_public_inputs};
    use aztec::protocol::address::AztecAddress;
    use aztec::protocol::traits::FromField;

    #[test]
    fn public_inputs_follow_the_owner_circuit_layout() {
        let inputs = nullification_public_inputs(
            AztecAddress::from_field(0xc0),
            0x51,
            AztecAddress::from_field(0x0e),
            0xe0,
            0x77,
            [0xf1, 0xf2],
            0x1a,
            0x2a,
            0x3a,
        );
        assert_eq(inputs, [0xc0, 0x51, 0x0e, 0xe0, 0x77, 0xf1, 0xf2, 0x1a, 0x2a, 0x3a]);
    }

    #[test]
    fn executor_binding_admits_anyone_or_the_named_caller() {
        let e = AztecAddress::from_field(0xe0);
        let other = AztecAddress::from_field(0xe1);
        // unbound: any caller, and a call with no msg_sender
        assert(executor_ok(0, Option::some(e)));
        assert(executor_ok(0, Option::none()));
        // bound: only the named caller
        assert(executor_ok(0xe0, Option::some(e)));
        assert(!executor_ok(0xe0, Option::some(other)));
        assert(!executor_ok(0xe0, Option::none()));
        assert(!executor_ok(-1, Option::none()));
    }

    #[test]
    fn expiry_admits_anchors_strictly_below_it() {
        assert(expiry_ok(0, 0));
        assert(expiry_ok(0, 0xffffffff));
        assert(expiry_ok(11, 10));
        assert(!expiry_ok(10, 10));
        assert(!expiry_ok(9, 10));
        assert(!expiry_ok(1, 0xffffffff));
        // every Field value is defined, in canonical order
        assert(expiry_ok(0x100000000, 0xffffffff));
        assert(expiry_ok(-1, 0xffffffff));
    }

    #[test]
    fn npk_app_hash_separates_keys() {
        assert(npk_app_hash(1) != npk_app_hash(2));
        assert(npk_app_hash(0) != 0);
    }
}
