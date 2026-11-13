// The blinded ECDSA wrappers: the constraint half of blind.nr on wrong
// hints, the verdict under every accepted blind, the inputs whose
// unblinded black-box call has no proof, the hint on hostile inputs and
// with its retries exhausted, k1_emul.nr against inputs known to collide,
// and the generated tables against a reference computation. The
// backend-level check (bb prove and verify) is
// noir/total_ecdsa_prove_check.
use crate::core::TWO_POW_64;
use crate::test_support::wit as w;
use super::bignum::{
    addmod, eq4, from_be, from_fields, from_mont, inv_mont, is_zero4, mmul, Mont, reduce_once,
    submod, to_mont, wmul5,
};
use super::blind::{blind_core, BlindHint, Secp256k1, Secp256r1, SecpCurve, select_point};
use super::blind_hint::{blind_hint, blind_hint_from, raw_bad, TRIES};
use super::{
    ecdsa_k1_verify, ecdsa_r1_verify, K1_DUMMY_HASH, K1_DUMMY_PK_X, K1_DUMMY_PK_Y, K1_DUMMY_SIG,
    R1_DUMMY_HASH, R1_DUMMY_PK_X, R1_DUMMY_PK_Y, R1_DUMMY_SIG,
};
use super::k1_emul::{k1_bad, k1_u2_wnafs};
use super::table_k1::{K1_G_ODD, K1_N_MONT, K1_P_MONT};
use super::table_r1::{R1_N_MONT, R1_P_MONT};
use super::vectors::{
    K1_COLLIDE_CTL_HASH, K1_COLLIDE_CTL_PK_X, K1_COLLIDE_CTL_PK_Y, K1_COLLIDE_CTL_SIG,
    K1_COLLIDE_DBL_HASH, K1_COLLIDE_DBL_PK_X, K1_COLLIDE_DBL_PK_Y, K1_COLLIDE_DBL_SIG,
    K1_COLLIDE_EQ_HASH, K1_COLLIDE_EQ_PK_X, K1_COLLIDE_EQ_PK_Y, K1_COLLIDE_EQ_SIG,
    K1_COLLIDE_NEG_HASH, K1_COLLIDE_NEG_PK_X, K1_COLLIDE_NEG_PK_Y, K1_COLLIDE_NEG_SIG,
    K1_RG_VALID_HASH, K1_RG_VALID_PK_X, K1_RG_VALID_PK_Y, K1_RG_VALID_SIG, K1_RINF_A_HASH,
    K1_RINF_A_PK_X, K1_RINF_A_PK_Y, K1_RINF_A_SIG, K1_RINF_B_HASH, K1_RINF_B_PK_X, K1_RINF_B_PK_Y,
    K1_RINF_B_SIG, K1_RINF_CTL_HASH, K1_RINF_CTL_PK_X, K1_RINF_CTL_PK_Y, K1_RINF_CTL_SIG,
    R1_KEY_H_HASH, R1_KEY_H_PK_X, R1_KEY_H_PK_Y, R1_KEY_H_SIG, R1_M4INV_H_HASH, R1_M4INV_H_PK_X,
    R1_M4INV_H_PK_Y, R1_M4INV_H_SIG,
};

// --- the constraint half on wrong hints ---

/// The honest hint for (x, y, s, h) altered in one place (m = 0: not
/// altered).
fn altered(h: BlindHint, m: u32) -> BlindHint {
    let mut h = h;
    if m == 1 {
        h.bits[5] = 1 - h.bits[5];
    }
    if m == 2 {
        h.bits[252] = 1 - h.bits[252];
    }
    if m == 3 {
        // 2 or 3: not a bit
        h.bits[7] = h.bits[7] + 2;
    }
    if m == 4 {
        h.lam[20][0] += 1;
    }
    if m == 5 {
        h.x[40][1] += 1;
    }
    if m == 6 {
        h.q_lam[7][0] += 1;
    }
    if m == 7 {
        h.q_x[62][3] += 1;
    }
    if m == 8 {
        h.yb[0] += 1;
    }
    if m == 9 {
        h.q_yb[2] += 1;
    }
    if m == 10 {
        h.inv[2] += 1;
    }
    if m == 11 {
        h.q_inv[1] += 1;
    }
    if m == 12 {
        h.lam_a[0] += 1;
    }
    if m == 13 {
        h.q_lam_a[0] += 1;
    }
    if m == 14 {
        h.key_x[0] += 1;
    }
    if m == 15 {
        h.q_x_a[1] += 1;
    }
    if m == 16 {
        h.key_y[3] += 1;
    }
    if m == 17 {
        h.q_y_a[0] += 1;
    }
    if m == 18 {
        h.slack_x[0] += 1;
    }
    if m == 19 {
        h.slack_y[2] += 1;
    }
    if m == 20 {
        h.hash[0] += 1;
    }
    if m == 21 {
        h.q_hash[0] += 1;
    }
    if m == 22 {
        h.slack_hash[1] += 1;
    }
    if m == 23 {
        // the same integer with limb 0 out of range
        h.x[10][0] += TWO_POW_64;
        h.x[10][1] -= 1;
    }
    if m == 24 {
        h.sign = 1 - h.sign;
    }
    if m == 25 {
        // 2 or 3: not a bit
        h.sign = h.sign + 2;
    }
    if m == 26 {
        // top digit 15
        for i in 252..256 {
            h.bits[i] = 1;
        }
    }
    h
}

/// blind_core on the secp256k1 dummy under the altered honest hint, then
/// the black box on its output.
fn k1_altered(m: u32) -> bool {
    let (x, y, s, z) = (w(K1_DUMMY_PK_X), w(K1_DUMMY_PK_Y), w(K1_DUMMY_SIG), w(K1_DUMMY_HASH));
    // Safety: test; blind_core checks the (altered) hint.
    let h = unsafe { blind_hint::<Secp256k1>(x, y, s, z) };
    let (bx, by, bz) = blind_core::<Secp256k1>(x, y, s, z, altered(h, m));
    std::ecdsa_secp256k1::verify_signature(bx, by, s, bz)
}

/// The same on the secp256r1 dummy.
fn r1_altered(m: u32) -> bool {
    let (x, y, s, z) = (w(R1_DUMMY_PK_X), w(R1_DUMMY_PK_Y), w(R1_DUMMY_SIG), w(R1_DUMMY_HASH));
    // Safety: test; blind_core checks the (altered) hint.
    let h = unsafe { blind_hint::<Secp256r1>(x, y, s, z) };
    let (bx, by, bz) = blind_core::<Secp256r1>(x, y, s, z, altered(h, m));
    std::ecdsa_secp256r1::verify_signature(bx, by, s, bz)
}

#[test]
fn honest_hint_accepted() {
    assert(k1_altered(0));
    assert(r1_altered(0));
}

#[test(should_fail)]
fn flipped_blind_bit_rejected() {
    let _ = k1_altered(1);
}

#[test(should_fail)]
fn flipped_top_window_bit_rejected() {
    let _ = k1_altered(2);
}

#[test(should_fail_with = "ecdsa blind: bit not boolean")]
fn non_boolean_bit_rejected() {
    let _ = k1_altered(3);
}

#[test(should_fail)]
fn wrong_chain_slope_rejected() {
    let _ = k1_altered(4);
}

#[test(should_fail)]
fn wrong_chain_x_rejected() {
    let _ = k1_altered(5);
}

#[test(should_fail)]
fn wrong_slope_quotient_rejected() {
    let _ = k1_altered(6);
}

#[test(should_fail)]
fn wrong_x_quotient_rejected() {
    let _ = k1_altered(7);
}

#[test(should_fail)]
fn wrong_blind_y_rejected() {
    let _ = k1_altered(8);
}

#[test(should_fail)]
fn wrong_blind_y_quotient_rejected() {
    let _ = k1_altered(9);
}

#[test(should_fail)]
fn wrong_inverse_rejected() {
    let _ = k1_altered(10);
}

#[test(should_fail)]
fn wrong_inverse_quotient_rejected() {
    let _ = k1_altered(11);
}

#[test(should_fail)]
fn wrong_key_slope_rejected() {
    let _ = k1_altered(12);
}

#[test(should_fail)]
fn wrong_key_slope_quotient_rejected() {
    let _ = k1_altered(13);
}

#[test(should_fail)]
fn wrong_blinded_x_rejected() {
    let _ = k1_altered(14);
}

#[test(should_fail)]
fn wrong_blinded_x_quotient_rejected() {
    let _ = k1_altered(15);
}

#[test(should_fail)]
fn wrong_blinded_y_rejected() {
    let _ = r1_altered(16);
}

#[test(should_fail)]
fn wrong_blinded_y_quotient_rejected() {
    let _ = k1_altered(17);
}

#[test(should_fail)]
fn wrong_x_slack_rejected() {
    let _ = k1_altered(18);
}

#[test(should_fail)]
fn wrong_y_slack_rejected() {
    let _ = r1_altered(19);
}

#[test(should_fail)]
fn wrong_blinded_hash_rejected() {
    let _ = k1_altered(20);
}

#[test(should_fail)]
fn wrong_hash_quotient_rejected() {
    let _ = k1_altered(21);
}

#[test(should_fail)]
fn wrong_hash_slack_rejected() {
    let _ = k1_altered(22);
}

#[test(should_fail)]
fn noncanonical_chain_limb_rejected() {
    let _ = k1_altered(23);
}

// A hint made for another hash fails the hash identity.
#[test(should_fail)]
fn flipped_sign_rejected() {
    let _ = k1_altered(24);
}

#[test(should_fail)]
fn flipped_sign_rejected_r1() {
    let _ = r1_altered(24);
}

#[test(should_fail_with = "ecdsa blind: sign not boolean")]
fn non_boolean_sign_rejected() {
    let _ = k1_altered(25);
}

#[test(should_fail_with = "ecdsa blind: top digit out of range")]
fn top_digit_fifteen_rejected() {
    let _ = k1_altered(26);
}

#[test(should_fail)]
fn hint_for_other_hash_rejected() {
    let mut other = R1_DUMMY_HASH;
    other[31] ^= 1;
    let (x, y, s, z) = (w(R1_DUMMY_PK_X), w(R1_DUMMY_PK_Y), w(R1_DUMMY_SIG), w(R1_DUMMY_HASH));
    // Safety: test; blind_core checks the hint.
    let h = unsafe { blind_hint::<Secp256r1>(x, y, s, w(other)) };
    let _ = blind_core::<Secp256r1>(x, y, s, z, h);
}

// --- the verdict does not depend on the blind ---

// Other accepted blinds (candidates 100.. and 7..) give the black box's
// verdict on the original inputs: true for the valid vector, false for a
// wrong hash, on both curves.
#[test]
fn verdict_independent_of_blind() {
    let mut bad = K1_DUMMY_HASH;
    bad[3] ^= 1;
    let (x, y, s) = (w(K1_DUMMY_PK_X), w(K1_DUMMY_PK_Y), w(K1_DUMMY_SIG));
    for t in 0..3 {
        // Safety: test; blind_core checks the hint.
        let (h, _) =
            unsafe { blind_hint_from::<Secp256k1>(x, y, s, w(K1_DUMMY_HASH), 100 + t, false) };
        let (bx, by, bz) = blind_core::<Secp256k1>(x, y, s, w(K1_DUMMY_HASH), h);
        assert(std::ecdsa_secp256k1::verify_signature(bx, by, s, bz));
        // Safety: as above.
        let (h2, _) = unsafe { blind_hint_from::<Secp256k1>(x, y, s, w(bad), 100 + t, false) };
        let (bx, by, bz) = blind_core::<Secp256k1>(x, y, s, w(bad), h2);
        assert(!std::ecdsa_secp256k1::verify_signature(bx, by, s, bz));
    }
    let mut bad = R1_DUMMY_HASH;
    bad[3] ^= 1;
    let (x, y, s) = (w(R1_DUMMY_PK_X), w(R1_DUMMY_PK_Y), w(R1_DUMMY_SIG));
    for t in 0..2 {
        // Safety: as above.
        let (h, _) =
            unsafe { blind_hint_from::<Secp256r1>(x, y, s, w(R1_DUMMY_HASH), 7 + t, false) };
        let (bx, by, bz) = blind_core::<Secp256r1>(x, y, s, w(R1_DUMMY_HASH), h);
        assert(std::ecdsa_secp256r1::verify_signature(bx, by, s, bz));
        // Safety: as above.
        let (h2, _) = unsafe { blind_hint_from::<Secp256r1>(x, y, s, w(bad), 7 + t, false) };
        let (bx, by, bz) = blind_core::<Secp256r1>(x, y, s, w(bad), h2);
        assert(!std::ecdsa_secp256r1::verify_signature(bx, by, s, bz));
    }
}

// --- inputs whose unblinded black-box call has no proof ---

fn k1(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> bool {
    ecdsa_k1_verify(w(pk_x), w(pk_y), w(sig), w(hash))
}

fn r1(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> bool {
    ecdsa_r1_verify(w(pk_x), w(pk_y), w(sig), w(hash))
}

// Keys solved for a collision in an early ladder step (secp256k1), and
// keys -(1/4) H and H for the offset generator H (secp256r1): each verdict
// is false, as the reference says.
#[test]
fn solved_keys_verdicts() {
    assert(
        !k1(
            K1_COLLIDE_EQ_PK_X,
            K1_COLLIDE_EQ_PK_Y,
            K1_COLLIDE_EQ_SIG,
            K1_COLLIDE_EQ_HASH,
        ),
    );
    assert(
        !k1(
            K1_COLLIDE_DBL_PK_X,
            K1_COLLIDE_DBL_PK_Y,
            K1_COLLIDE_DBL_SIG,
            K1_COLLIDE_DBL_HASH,
        ),
    );
    assert(
        !r1(
            R1_M4INV_H_PK_X,
            R1_M4INV_H_PK_Y,
            R1_M4INV_H_SIG,
            R1_M4INV_H_HASH,
        ),
    );
    assert(!r1(R1_KEY_H_PK_X, R1_KEY_H_PK_Y, R1_KEY_H_SIG, R1_KEY_H_HASH));
}

// The secp256k1 family with R a short multiple of G: R = O (false) and a
// valid signature with R = G (true), each colliding unblinded in the last
// round.
#[test]
fn short_r_family_verdicts() {
    assert(
        !k1(
            K1_RINF_A_PK_X,
            K1_RINF_A_PK_Y,
            K1_RINF_A_SIG,
            K1_RINF_A_HASH,
        ),
    );
    assert(
        !k1(
            K1_RINF_B_PK_X,
            K1_RINF_B_PK_Y,
            K1_RINF_B_SIG,
            K1_RINF_B_HASH,
        ),
    );
    assert(
        k1(
            K1_RG_VALID_PK_X,
            K1_RG_VALID_PK_Y,
            K1_RG_VALID_SIG,
            K1_RG_VALID_HASH,
        ),
    );
}

// --- k1_emul.nr against inputs known to collide ---

/// u1 = z/s and u2 = r/s mod n as bb derives them (s = 0 read as 1).
unconstrained fn scalars(sig: [u8; 64], hash: [u8; 32]) -> ([u64; 4], [u64; 4]) {
    let kn = K1_N_MONT;
    let mut rb = [0; 32];
    let mut sb = [0; 32];
    for i in 0..32 {
        rb[i] = sig[i];
        sb[i] = sig[32 + i];
    }
    let mut s = reduce_once(from_be(sb), kn.m);
    if is_zero4(s) {
        s = [1, 0, 0, 0];
    }
    let s_inv = inv_mont(to_mont(s, kn), kn);
    (
        mmul(s_inv, reduce_once(from_be(hash), kn.m), kn),
        mmul(s_inv, reduce_once(from_be(rb), kn.m), kn),
    )
}

/// k1_bad on the unblinded inputs: whether the raw black-box call meets
/// an assertion.
unconstrained fn raw_collides(x: [u8; 32], y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> bool {
    let kp = K1_P_MONT;
    let (u1, u2) = scalars(sig, hash);
    let (lo, hi) = k1_u2_wnafs(u2);
    k1_bad(to_mont(from_be(x), kp), to_mont(from_be(y), kp), u1, lo, hi)
}

// The emulation reproduces bb's outcome on the unblinded inputs (each
// collision vector fails bb prove when it reaches the black box directly,
// each control proves). One call site in a loop keeps the test's compile
// time down.
#[test]
unconstrained fn emulation_matches_known_outcomes() {
    let xs = [
        K1_COLLIDE_EQ_PK_X,
        K1_COLLIDE_DBL_PK_X,
        K1_COLLIDE_NEG_PK_X,
        K1_COLLIDE_CTL_PK_X,
        K1_RINF_A_PK_X,
        K1_RINF_B_PK_X,
        K1_RINF_CTL_PK_X,
        K1_RG_VALID_PK_X,
        K1_DUMMY_PK_X,
    ];
    let ys = [
        K1_COLLIDE_EQ_PK_Y,
        K1_COLLIDE_DBL_PK_Y,
        K1_COLLIDE_NEG_PK_Y,
        K1_COLLIDE_CTL_PK_Y,
        K1_RINF_A_PK_Y,
        K1_RINF_B_PK_Y,
        K1_RINF_CTL_PK_Y,
        K1_RG_VALID_PK_Y,
        K1_DUMMY_PK_Y,
    ];
    let sigs = [
        K1_COLLIDE_EQ_SIG,
        K1_COLLIDE_DBL_SIG,
        K1_COLLIDE_NEG_SIG,
        K1_COLLIDE_CTL_SIG,
        K1_RINF_A_SIG,
        K1_RINF_B_SIG,
        K1_RINF_CTL_SIG,
        K1_RG_VALID_SIG,
        K1_DUMMY_SIG,
    ];
    let hashes = [
        K1_COLLIDE_EQ_HASH,
        K1_COLLIDE_DBL_HASH,
        K1_COLLIDE_NEG_HASH,
        K1_COLLIDE_CTL_HASH,
        K1_RINF_A_HASH,
        K1_RINF_B_HASH,
        K1_RINF_CTL_HASH,
        K1_RG_VALID_HASH,
        K1_DUMMY_HASH,
    ];
    let expected = [true, true, true, false, true, true, false, true, false];
    for i in 0..9 {
        assert_eq(raw_collides(xs[i], ys[i], sigs[i], hashes[i]), expected[i]);
    }
}

// On an R = O input, whose unblinded call fails, the hint settles on a
// blind that passes the emulation and the black box.
#[test]
fn short_r_input_blinded() {
    let (x, y, s, z) = (w(K1_RINF_A_PK_X), w(K1_RINF_A_PK_Y), w(K1_RINF_A_SIG), w(K1_RINF_A_HASH));
    // Safety: test; blind_core checks the hint.
    let (h, rejected) = unsafe { blind_hint_from::<Secp256k1>(x, y, s, z, 0, false) };
    assert(rejected < TRIES);
    let (bx, by, bz) = blind_core::<Secp256k1>(x, y, s, z, h);
    assert(!std::ecdsa_secp256k1::verify_signature(bx, by, s, bz));
}

// The emulations flag aliasing (inputs of noir/total_ecdsa_prove_check:
// each fails bb prove when it reaches the black box directly): a
// secp256k1 key solved so that a ladder step's x-coordinates differ by a
// multiple of the native modulus, a final point R with x(R) = x(-lambda
// G) + j N whose closing skew addition divides by 0 mod N, and a
// secp256r1 key that does the same to the final addition T1 + T2. The
// wrappers prove all three (the hint moves to a blind that passes).
#[test]
unconstrained fn emulation_flags_aliasing() {
    let lad_x: [u8; 32] = [
        89, 62, 205, 61, 205, 188, 254, 122, 244, 6, 45, 155, 86, 34, 241, 178, 136, 150, 115, 29,
        51, 40, 200, 79, 76, 0, 47, 200, 104, 70, 212, 155,
    ];
    let lad_y: [u8; 32] = [
        4, 167, 212, 211, 116, 12, 161, 53, 114, 47, 117, 58, 251, 187, 67, 109, 143, 48, 63, 80,
        55, 11, 152, 106, 15, 63, 102, 8, 253, 196, 2, 253,
    ];
    let lad_sig: [u8; 64] = [
        193, 60, 49, 156, 49, 235, 115, 143, 62, 143, 28, 116, 133, 175, 153, 223, 137, 133, 117,
        62, 255, 213, 146, 122, 225, 52, 1, 74, 102, 94, 251, 142, 112, 149, 178, 60, 46, 100, 202,
        110, 23, 184, 217, 40, 136, 204, 85, 147, 94, 248, 82, 229, 208, 77, 229, 170, 106, 0, 45,
        101, 98, 204, 246, 113,
    ];
    let lad_hash: [u8; 32] = [
        224, 52, 140, 202, 121, 209, 177, 208, 42, 19, 27, 118, 73, 255, 1, 242, 137, 86, 192, 159,
        130, 159, 48, 240, 98, 123, 177, 145, 221, 146, 124, 75,
    ];
    let skew_x: [u8; 32] = [
        44, 29, 58, 178, 4, 195, 122, 112, 109, 122, 1, 70, 15, 221, 183, 254, 18, 15, 213, 134,
        190, 95, 222, 166, 209, 23, 55, 55, 225, 201, 214, 137,
    ];
    let skew_y: [u8; 32] = [
        228, 97, 40, 29, 120, 14, 253, 27, 2, 49, 156, 225, 254, 181, 217, 78, 126, 198, 18, 194,
        233, 29, 177, 128, 17, 155, 242, 2, 113, 82, 194, 80,
    ];
    let skew_sig: [u8; 64] = [
        86, 254, 9, 247, 222, 38, 196, 91, 250, 217, 211, 169, 10, 221, 18, 227, 176, 146, 88, 206,
        39, 252, 168, 50, 67, 108, 109, 42, 156, 71, 146, 219, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    ];
    let skew_hash: [u8; 32] = [
        74, 167, 28, 56, 104, 110, 128, 169, 248, 175, 140, 121, 50, 135, 208, 80, 242, 234, 208,
        168, 8, 8, 95, 104, 137, 27, 166, 173, 153, 138, 14, 50,
    ];
    let fin_x: [u8; 32] = [
        125, 151, 218, 89, 74, 109, 61, 96, 97, 242, 18, 169, 132, 64, 244, 195, 201, 59, 32, 200,
        28, 111, 221, 88, 244, 38, 133, 10, 227, 251, 204, 155,
    ];
    let fin_y: [u8; 32] = [
        203, 141, 96, 56, 143, 96, 49, 243, 88, 161, 168, 132, 105, 18, 102, 212, 135, 171, 187,
        103, 225, 141, 19, 242, 59, 249, 213, 100, 141, 216, 24, 72,
    ];
    let fin_sig: [u8; 64] = [
        243, 129, 151, 23, 251, 149, 37, 32, 181, 212, 88, 14, 10, 222, 212, 250, 176, 20, 93, 184,
        252, 66, 188, 158, 128, 102, 139, 124, 179, 161, 251, 27, 23, 130, 82, 85, 97, 245, 161, 62,
        179, 34, 235, 80, 227, 199, 142, 94, 216, 39, 14, 147, 146, 154, 21, 234, 118, 145, 202,
        159, 70, 9, 52, 161,
    ];
    let fin_hash: [u8; 32] = [
        13, 201, 60, 224, 87, 18, 89, 225, 50, 169, 40, 248, 63, 175, 82, 59, 133, 171, 17, 196,
        137, 63, 79, 150, 30, 118, 11, 35, 49, 149, 188, 238,
    ];
    assert(raw_bad::<Secp256k1>(lad_x, lad_y, lad_sig, lad_hash));
    assert(raw_bad::<Secp256k1>(skew_x, skew_y, skew_sig, skew_hash));
    assert(raw_bad::<Secp256r1>(fin_x, fin_y, fin_sig, fin_hash));
    assert(!raw_bad::<Secp256k1>(K1_DUMMY_PK_X, K1_DUMMY_PK_Y, K1_DUMMY_SIG, K1_DUMMY_HASH));
    assert(!raw_bad::<Secp256r1>(R1_DUMMY_PK_X, R1_DUMMY_PK_Y, R1_DUMMY_SIG, R1_DUMMY_HASH));
}

// --- the hint on hostile inputs ---

// The hints return for inputs the wrappers never pass them (off-curve
// keys, zero and all-0xff bytes, a key of order 3 on its own curve): no
// trap. One call site per function in a loop.
#[test]
unconstrained fn hints_do_not_trap() {
    let mut small = [0; 32];
    small[31] = 1;
    let xs = [[0; 32], [0xff; 32], K1_DUMMY_PK_X, [0; 32]];
    let ys = [[0; 32], [0xff; 32], [0; 32], small];
    let sigs = [[0; 64], [0xff; 64], K1_DUMMY_SIG, K1_DUMMY_SIG];
    let hashes = [[0; 32], [0xff; 32], [0xff; 32], K1_DUMMY_HASH];
    for i in 0..4 {
        let _ = blind_hint::<Secp256k1>(xs[i], ys[i], sigs[i], hashes[i]);
        let _ = blind_hint::<Secp256r1>(xs[i], ys[i], sigs[i], hashes[i]);
        let _ = raw_collides(xs[i], ys[i], sigs[i], hashes[i]);
    }
}

// With every candidate rejected the hint still returns after TRIES
// candidates, and what it returns (the last candidate) passes the
// constraints.
#[test]
fn exhausted_retries_return_a_well_formed_hint() {
    let (x, y, s, z) = (w(K1_DUMMY_PK_X), w(K1_DUMMY_PK_Y), w(K1_DUMMY_SIG), w(K1_DUMMY_HASH));
    // Safety: test; blind_core checks the hint.
    let (h, rejected) = unsafe { blind_hint_from::<Secp256k1>(x, y, s, z, 0, true) };
    assert(rejected == TRIES);
    let (bx, by, bz) = blind_core::<Secp256k1>(x, y, s, z, h);
    assert(std::ecdsa_secp256k1::verify_signature(bx, by, s, bz));
}

// --- the generated tables ---

/// Affine (x, y) in Montgomery form, (0, 0) standing for infinity.
unconstrained fn ref_add(
    a: ([u64; 4], [u64; 4]),
    b: ([u64; 4], [u64; 4]),
    am: [u64; 4],
    k: Mont,
) -> ([u64; 4], [u64; 4]) {
    let m = k.m;
    let a_inf = is_zero4(a.0) & is_zero4(a.1);
    let b_inf = is_zero4(b.0) & is_zero4(b.1);
    if a_inf {
        b
    } else if b_inf {
        a
    } else if eq4(a.0, b.0) & !eq4(a.1, b.1) {
        ([0; 4], [0; 4])
    } else {
        let lam = if eq4(a.0, b.0) {
            let xx = mmul(a.0, a.0, k);
            let num = addmod(addmod(addmod(xx, xx, m), xx, m), am, m);
            mmul(num, inv_mont(addmod(a.1, a.1, m), k), k)
        } else {
            mmul(submod(b.1, a.1, m), inv_mont(submod(b.0, a.0, m), k), k)
        };
        let x = submod(submod(mmul(lam, lam, k), a.0, m), b.0, m);
        (x, submod(mmul(lam, submod(a.0, x, m), k), a.1, m))
    }
}

/// e * P by double-and-add over the bits of the small scalar parts
/// (e = c * 16^w with c < 2^8, w < 64).
unconstrained fn ref_mul(
    p: ([u64; 4], [u64; 4]),
    c: u32,
    w: u32,
    am: [u64; 4],
    k: Mont,
) -> ([u64; 4], [u64; 4]) {
    let mut base = p;
    for _ in 0..4 * w {
        base = ref_add(base, base, am, k);
    }
    let mut acc = ([0; 4], [0; 4]);
    for i in 0..8 {
        if ((c >> i) & 1) == 1 {
            acc = ref_add(acc, base, am, k);
        }
        base = ref_add(base, base, am, k);
    }
    acc
}

/// Table entry (w, d) of curve C from the multilinear polynomial, against
/// the reference (d + 2) 16^w G.
unconstrained fn check_entry<C>(g: ([u64; 4], [u64; 4]), w: u32, d: u32)
where
    C: SecpCurve,
{
    let k = C::p_mont();
    let bits = [
        (d & 1) as Field,
        ((d >> 1) & 1) as Field,
        ((d >> 2) & 1) as Field,
        ((d >> 3) & 1) as Field,
    ];
    let (x, y) = select_point(C::fb()[w], bits);
    let (rx, ry) = ref_mul(g, d + 2, w, C::a_mont(), k);
    assert(eq4(from_fields(x), from_mont(rx, k)));
    assert(eq4(from_fields(y), from_mont(ry, k)));
}

/// The generators as plain limbs (SEC 2 / FIPS 186 values).
global K1_G: [[u64; 4]; 2] = [
    [0x59f2815b16f81798, 0x029bfcdb2dce28d9, 0x55a06295ce870b07, 0x79be667ef9dcbbac],
    [0x9c47d08ffb10d4b8, 0xfd17b448a6855419, 0x5da4fbfc0e1108a8, 0x483ada7726a3c465],
];
global R1_G: [[u64; 4]; 2] = [
    [0xf4a13945d898c296, 0x77037d812deb33a0, 0xf8bce6e563a440f2, 0x6b17d1f2e12c4247],
    [0xcbb6406837bf51f5, 0x2bce33576b315ece, 0x8ee7eb4a7c0f9e16, 0x4fe342e2fe1a7f9b],
];

#[test]
unconstrained fn fixed_base_tables_match_reference() {
    let gk = (to_mont(K1_G[0], K1_P_MONT), to_mont(K1_G[1], K1_P_MONT));
    let gr = (to_mont(R1_G[0], R1_P_MONT), to_mont(R1_G[1], R1_P_MONT));
    let entries = [(0, 0), (0, 15), (17, 9), (62, 15), (63, 7)];
    for i in 0..5 {
        let (wi, d) = entries[i];
        check_entry::<Secp256k1>(gk, wi, d);
        check_entry::<Secp256r1>(gr, wi, d);
    }
}

#[test]
unconstrained fn odd_multiples_of_g_match_reference() {
    let k = K1_P_MONT;
    let am = Secp256k1::a_mont();
    let g = (to_mont(K1_G[0], k), to_mont(K1_G[1], k));
    let idx = [0, 1, 64, 127];
    for j in 0..4 {
        let i = idx[j];
        let r = ref_mul(g, 2 * i + 1, 0, am, k);
        assert(eq4(K1_G_ODD[i][0], r.0));
        assert(eq4(K1_G_ODD[i][1], r.1));
    }
}

/// m * m_inv == -1 mod 2^64, R^2 R^2 / R == R^3, R mod m == R^2 / R, and
/// m * (m^-1 mod 2^320) == 1 mod 2^320.
unconstrained fn check_mont(k: Mont) {
    let p: u128 = (k.m[0] as u128) * (k.m_inv as u128);
    assert((p as u64) == 0xffffffffffffffff);
    assert(eq4(mmul(k.r2, k.r2, k), k.r3));
    assert(eq4(mmul(k.r2, [1, 0, 0, 0], k), k.one));
    let prod = wmul5([k.m[0], k.m[1], k.m[2], k.m[3], 0], k.inv320);
    assert(prod == [1, 0, 0, 0, 0]);
}

#[test]
unconstrained fn montgomery_constants_consistent() {
    check_mont(K1_P_MONT);
    check_mont(K1_N_MONT);
    check_mont(R1_P_MONT);
    check_mont(R1_N_MONT);
}
