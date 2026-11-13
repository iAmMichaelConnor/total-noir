//! prove_nullification: the owner side of a proof of nullification.
//!
//! The owner B of a settled note in contract A proves, off-line in its
//! own PXE, that (leaf, nullifier, npk_app_hash) are consistent with the
//! note's preimage and B's app-siloed nullifier hiding key. A third
//! party E checks it off the chain against the public inputs E rebuilds,
//! and A verifies it recursively
//! (total_aztec::consume_with_nullification_proof_or), proves the leaf is in
//! the note hash tree and pushes the nullifier: B's note is spent in E's
//! transaction without B's key ever reaching E. Nothing here shows that
//! the leaf was ever inserted (B can prove over any preimage); A checks
//! that itself.
//!
//! Inputs. Public: contract_address, storage_slot, owner (A rebuilds
//! these), executor and expiry (B's optional binding, which A reads from
//! the handoff and checks as flags), and the note's packed fields (A
//! reads them). Private:
//! randomness and nonce (the note's, as B's PXE stores them for a
//! settled note) and nhk_app (B's app-siloed nullifier hiding key for A,
//! the secret key aztec-nr hashes into B's nullifiers in A; B's PXE
//! derives it from B's master nullifier hiding key and A's address).
//!
//! Outputs (public, after the inputs, in this order):
//! - leaf: the note-hash-tree leaf,
//!   unique_note_hash(contract_address, note_hash, nonce), with
//!   note_hash = P2(DOM_SEP__NOTE_HASH, slot, fields, owner, randomness);
//! - nullifier: P2(DOM_SEP__NOTE_NULLIFIER, leaf, nhk_app), the nullifier
//!   aztec-nr pushes when B spends the note itself;
//! - npk_app_hash: P2(DOM_SEP__NPK_APP_HASH, nhk_app), what A pins.
//!
//! Formulas: note_hash, unique_note_hash and note_nullifier below, over
//! the protocol_types hashes and domain separators.
//!
//! The circuit has no assert: every input has a witness, and it proves
//! nothing about nhk_app beyond the commitment. That nhk_app is B's
//! canonical key comes from A's pin, which B registered in its own
//! transaction under a kernel key validation (see the executor module
//! header in noir/total_aztec/src/nullification_proof.nr).
//!
//! executor and expiry enter no constraint: as public inputs they are
//! bound by the proof itself (UltraHonk's verifier takes the public-input
//! values into its transcript and permutation argument), so a proof made
//! for one executor or expiry does not verify for another; make_fixture.py
//! and outer_check.py check that with bb.
//!
//! N, the number of packed note fields, is fixed per note type; this
//! example uses a one-field note (a value).
//!
//! DEV DECISION: the owner's binding (executor, expiry; 0 = unbound),
//! chosen by B's PXE per proof. One circuit and one vk serve bearer and
//! bound consent; the consequences are in the example's README.
//!
//! DEV DECISION: which inputs are public. Default: the note's fields
//! are public, because the executor reads them (a third-party read is
//! the point). For a consume that must not reveal the value to the
//! executor, make fields private and output a commitment or the app
//! result instead; A's public-input layout changes with it.

use protocol_types::address::AztecAddress;
use protocol_types::constants::{DOM_SEP__NOTE_HASH, DOM_SEP__NOTE_NULLIFIER};
use protocol_types::hash::{
    compute_siloed_note_hash, compute_unique_note_hash, poseidon2_hash_with_separator,
};
use protocol_types::traits::FromField;

/// Must equal total_aztec::nullification_proof::DOM_SEP__NPK_APP_HASH;
/// make_fixture.py fails if the honest proof's npk_app_hash is not the
/// pin the executor contract registered.
global DOM_SEP__NPK_APP_HASH: u32 = 0x6e706b61; // "npka"

global N: u32 = 1;

// The Aztec v6 note formulas, as aztec-nr computes them for a #[note]
// note: compute_note_hash (note/utils.nr) over the #[note] derive's
// preimage [packed note..., owner, randomness], the settled leaf of
// compute_note_existence_request, and compute_note_nullifier with the
// owner's nhk_app. make_fixture.py checks the honest proof's outputs
// against the values aztec-nr computes in the TXE, and the test
// matches_aztec_nr pins one such run.

/// The note hash: P2(DOM_SEP__NOTE_HASH, slot, fields..., owner, randomness).
fn note_hash<let M: u32>(
    storage_slot: Field,
    owner: Field,
    fields: [Field; M],
    randomness: Field,
) -> Field {
    poseidon2_hash_with_separator(
        [storage_slot].concat(fields).concat([owner, randomness]),
        DOM_SEP__NOTE_HASH,
    )
}

/// A settled note's leaf: the note hash siloed by the contract address,
/// then made unique with the note's nonce.
fn unique_note_hash(contract_address: Field, note_hash: Field, nonce: Field) -> Field {
    compute_unique_note_hash(
        nonce,
        compute_siloed_note_hash(AztecAddress::from_field(contract_address), note_hash),
    )
}

/// A settled note's nullifier: P2(DOM_SEP__NOTE_NULLIFIER, leaf, nhk_app).
fn note_nullifier(leaf: Field, nhk_app: Field) -> Field {
    poseidon2_hash_with_separator([leaf, nhk_app], DOM_SEP__NOTE_NULLIFIER)
}

fn main(
    contract_address: pub Field,
    storage_slot: pub Field,
    owner: pub Field,
    executor: pub Field,
    expiry: pub Field,
    fields: pub [Field; N],
    randomness: Field,
    nonce: Field,
    nhk_app: Field,
) -> pub (Field, Field, Field) {
    // Bound as public inputs only; see the module header.
    let _ = (executor, expiry);
    let inner = note_hash(storage_slot, owner, fields, randomness);
    let leaf = unique_note_hash(contract_address, inner, nonce);
    let nullifier = note_nullifier(leaf, nhk_app);
    let npk_app_hash = poseidon2_hash_with_separator([nhk_app], DOM_SEP__NPK_APP_HASH);
    (leaf, nullifier, npk_app_hash)
}

#[test]
fn outputs_bind_every_input() {
    let base = main(0xc0, 0x51, 0x0e, 0, 0, [7], 0x99, 0x77, 0x55);
    assert(base.0 != main(0xc1, 0x51, 0x0e, 0, 0, [7], 0x99, 0x77, 0x55).0);
    assert(base.0 != main(0xc0, 0x52, 0x0e, 0, 0, [7], 0x99, 0x77, 0x55).0);
    assert(base.0 != main(0xc0, 0x51, 0x0f, 0, 0, [7], 0x99, 0x77, 0x55).0);
    assert(base.0 != main(0xc0, 0x51, 0x0e, 0, 0, [8], 0x99, 0x77, 0x55).0);
    assert(base.0 != main(0xc0, 0x51, 0x0e, 0, 0, [7], 0x98, 0x77, 0x55).0);
    assert(base.0 != main(0xc0, 0x51, 0x0e, 0, 0, [7], 0x99, 0x78, 0x55).0);
    let other_key = main(0xc0, 0x51, 0x0e, 0, 0, [7], 0x99, 0x77, 0x56);
    assert_eq(base.0, other_key.0);
    assert(base.1 != other_key.1);
    assert(base.2 != other_key.2);
}

// The binding changes no output: the same note has the same leaf and
// nullifier whoever may consume it and until when. It is bound as public
// inputs, which bb checks (make_fixture.py, outer_check.py).
#[test]
fn binding_leaves_the_outputs_unchanged() {
    let base = main(0xc0, 0x51, 0x0e, 0, 0, [7], 0x99, 0x77, 0x55);
    assert_eq(base, main(0xc0, 0x51, 0x0e, 0xe0, 0, [7], 0x99, 0x77, 0x55));
    assert_eq(base, main(0xc0, 0x51, 0x0e, 0, 42, [7], 0x99, 0x77, 0x55));
}

// Inputs and outputs of one run of make_fixture.py: the leaf and
// nullifier aztec-nr computes in the TXE for the executor test's planted
// note (ValueNote 1000, randomness 0x5eed, the TXE's nonce) and the pin
// total_aztec::registered_npk_app_hash registers for the owner's key.
#[test]
fn matches_aztec_nr() {
    let (leaf, nullifier, npk_app_hash) = main(
        0x0d71cf4c20298a19a16e5e5f3faee1b5d3dc0c58efc9b682660f3c15f67adfdb,
        0x01,
        0x26fa553bb60e307ea85e01b5ac24f31b6f07acd29b5e93e1d447f0c42a9680f0,
        0,
        0,
        [1000],
        0x5eed,
        0x18db22373c37fea7ed51d55576cdf1e7720697a75d97982647a7165f4a2838a4,
        0x1605952d096fe373506674295a7aad4a40e8207ad8defb2fac8e4a9dcfb5cfe4,
    );
    assert_eq(leaf, 0x30444f6ebecc9ddfb55974a45c6b9af8faa83e967fee531904bc5069d6c56556);
    assert_eq(nullifier, 0x2363ee41c6c810fb0da2989719283d8162fb2d2ea66c525f63d2b53af22808d2);
    assert_eq(npk_app_hash, 0x0fdf5fe30b3c265d877fcb93c24990770bc934a8652adbb650f542229690da29);
}
