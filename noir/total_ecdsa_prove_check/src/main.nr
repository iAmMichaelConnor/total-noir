// Backend-level check of the ECDSA entries: run.sh executes this program
// on each Prover*.toml and then proves and verifies the witness with bb,
// so a witness the solver accepts but the backend's constraints reject
// fails the run. Each file holds one secp256k1 and one secp256r1 input
// and the expected verdicts; besides a valid signature per curve they are
// inputs that bb 6.0.0's ECDSA gadgets cannot prove when they reach the
// black box directly: secp256k1 keys solved so that a ladder step of the
// multiplication meets equal x-coordinates, the off-curve key (0, 1), and
// R = O inputs whose last ladder step collides, keys and final points
// that make bb's non-equality check alias (x-coordinates differing by a
// multiple of the native modulus) in a ladder step and in a closing skew
// addition, and r = n; secp256r1 keys -(1/4) H and H for bb's offset
// generator H, a key in a later round's relation with it, and aliasing
// in the final addition. Each file's first line names its
// inputs. A failure here after a bb upgrade means the gadgets changed:
// see docs/ecdsa-totality.md and CONTRIBUTING.md ("Bumping bb").
use total::ecdsa::{ecdsa_k1_verify, ecdsa_r1_verify};

fn main(
    k1_pk_x: [u8; 32],
    k1_pk_y: [u8; 32],
    k1_sig: [u8; 64],
    k1_hash: [u8; 32],
    k1_valid: bool,
    r1_pk_x: [u8; 32],
    r1_pk_y: [u8; 32],
    r1_sig: [u8; 64],
    r1_hash: [u8; 32],
    r1_valid: bool,
) -> pub (bool, bool) {
    let a = ecdsa_k1_verify(k1_pk_x, k1_pk_y, k1_sig, k1_hash);
    assert_eq(a, k1_valid);
    let b = ecdsa_r1_verify(r1_pk_x, r1_pk_y, r1_sig, r1_hash);
    assert_eq(b, r1_valid);
    (a, b)
}
