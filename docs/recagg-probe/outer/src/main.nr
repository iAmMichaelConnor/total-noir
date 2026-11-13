// The predication probe: a ZK UltraHonk proof (PROOF_TYPE_HONK_ZK = 6, the
// type aztec-nr contracts verify) checked only under a runtime boolean.
global PROOF_TYPE_HONK_ZK: u32 = 6;

fn main(present: bool, vk: [Field; 115], proof: [Field; 458], key_hash: Field, y: pub Field) {
    if present {
        std::verify_proof_with_type(vk, proof, [y], key_hash, PROOF_TYPE_HONK_ZK);
    }
}
