//! The executor's recursive check outside Aztec, so bb can prove it: the
//! binding flags and the verification step of total_aztec's
//! check_nullification_proof_or with the library's own public-input
//! layout (nullification_public_inputs) and the same predicate shape.
//! TXE does not check recursive proofs; run.sh proves and verifies this
//! circuit with bb on the owner's real proofs (outer_check.py): the
//! consume cases prove, a binding that does not admit the call proves
//! with ok = false, and a proof checked against other public inputs
//! fails to prove.
//!
//! msg_sender and anchor_block_number stand for what A reads from its
//! context (the caller and the anchor block header); present stands for
//! A's remaining terms of ok (the leaf's membership, the nullifier's
//! freshness, the static-call and room flags), which the TXE tests
//! exercise on the real trees.

use aztec::protocol::address::AztecAddress;
use aztec::protocol::hash::poseidon2_hash;
use aztec::protocol::traits::FromField;
use total_aztec::nullification_proof::{
    executor_ok, expiry_ok, nullification_public_inputs, PROOF_TYPE_HONK_ZK,
};

fn main(
    present: bool,
    vk: [Field; 115],
    proof: [Field; 458],
    executor: Field,
    expiry: Field,
    fields: [Field; 1],
    leaf: Field,
    nullifier: Field,
    contract_address: pub Field,
    storage_slot: pub Field,
    owner: pub Field,
    pinned_npk_app_hash: pub Field,
    expected_vk_hash: pub Field,
    msg_sender: pub Field,
    anchor_block_number: pub u32,
) -> pub bool {
    let vk_ok = poseidon2_hash(vk) == expected_vk_hash;
    let bound_ok = executor_ok(executor, Option::some(AztecAddress::from_field(msg_sender)))
        & expiry_ok(expiry, anchor_block_number);
    let ok = present & vk_ok & (pinned_npk_app_hash != 0) & bound_ok;
    if ok {
        let public_inputs = nullification_public_inputs(
            AztecAddress::from_field(contract_address),
            storage_slot,
            AztecAddress::from_field(owner),
            executor,
            expiry,
            fields,
            leaf,
            nullifier,
            pinned_npk_app_hash,
        );
        std::verify_proof_with_type(
            vk,
            proof,
            public_inputs,
            expected_vk_hash,
            PROOF_TYPE_HONK_ZK,
        );
    }
    ok
}
