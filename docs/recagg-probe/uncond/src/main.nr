// The unpredicated control: the same verification outside any branch.
global PROOF_TYPE_HONK_ZK: u32 = 6;
fn main(vk: [Field; 115], proof: [Field; 458], key_hash: Field, y: pub Field) {
    std::verify_proof_with_type(vk, proof, [y], key_hash, PROOF_TYPE_HONK_ZK);
}
