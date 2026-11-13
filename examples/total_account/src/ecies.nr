//! Encryption to the account owner's key, total for every input.
//!
//! seal_or is the code other users' transactions run: key decode with
//! flags, an ephemeral key pair and an ECDH shared secret through
//! total::ec::msm_or, and Poseidon2 authenticated encryption of a
//! fixed-length plaintext. Every failure an input can cause, including
//! one the account owner causes by storing a bad key or no key, becomes
//! ok = false with masked (all-zero) outputs. open is the owner-side
//! inverse, unconstrained, for the owner's PXE.
//!
//! # Example code, not a vetted scheme
//!
//! - Fresh randomness per message. The AE key (S.x) and the AE nonce (E.x)
//!   both derive from the caller's randomness r, so two encryptions to the
//!   same key with the same r share a keystream (c1 - c2 = m1 - m2). Only
//!   r = 0 is refused; nothing here can check freshness, so every caller
//!   (seal_or, TotalAccount.encrypt_for_owner, total_caller's seal_to)
//!   must pass a fresh random r.
//! - No KDF and no context binding: the AE key is the raw x-coordinate of
//!   S, and neither the recipient key, the contract address nor the chain
//!   enters the key or the tag. Acceptable for a dedicated key in a demo;
//!   a real scheme would derive the key with a domain-separated hash over
//!   that context (as aztec-nr's messages/encryption does).
//! - It shows totality over owner-controlled keys. It has had no review as
//!   cryptography; do not copy it as an encryption scheme.
//!
//! # Scheme
//!
//! Recipient key pair: secret sk (a Field, read as the Grumpkin scalar
//! of its canonical integer), public PK = [sk]G. Sender randomness r (a
//! Field, nonzero). Ephemeral public key E = [r]G; shared secret
//! S = [r]PK = [sk]E. The AE key is S.x and the AE nonce is E.x, so the
//! tag binds the ciphertext to E. Output: (E.x, E.y, c[0..N], tag).
//!
//! The AE construction is adapted from the SAFE-API duplex in
//! noir_logic/pss_utils/src/ae.nr of
//! https://github.com/TaceoLabs/monty-hall-aztec (notice below), extended
//! past one rate block. Poseidon2 permutation of width 4, rate 3 (positions 0..2),
//! capacity position 3. The initial state is [key, nonce, 0, T] with T
//! the SAFE IO-pattern word for ABSORB(2) SQUEEZE(N) ABSORB(N) SQUEEZE(1)
//! and domain separator 0x4142, and it is permuted once. Element i of the
//! plaintext is added into rate position i mod 3 and the sum is both the
//! ciphertext element and the new state value at that position; between
//! rate blocks the state is permuted again. The tag is element 0 of one
//! final permutation. For N <= 3 this is byte-for-byte ae.nr's
//! encrypt1/2/3 (test ae_matches_taceo_kat).
//!
//! This is not aztec-nr's messages/encryption/poseidon2.nr convention.
//! That one puts (S.x, S.y) in the rate and nonce + L*2^128 in the
//! capacity, permutes before absorbing, uses rate positions 1..3, pads
//! the message to a multiple of 3 and takes the tag from position 1, so
//! a 4-element message gives 7 output elements. This module keeps
//! Taceo's SAFE layout because its length is N + 1 with no padding to
//! check on decrypt, and it matches the reference byte for byte.
//!
//! # Why seal_or is total
//!
//! - Key decode: total::ec::decode_xy_or (std's two-coordinate form,
//!   (0, 0) is infinity) gives the on-curve flag; the point's inf field
//!   gives the infinity flag. Both determined. A key the caller reports
//!   missing is masked to (0, 0) before decode, so contents it did not
//!   vouch for never reach the curve code.
//! - Scalar: total::core::limbs(r) gives the canonical 128-bit limbs of r,
//!   whose integer is below p < q, so msm_or's scalar check always
//!   passes. This replaces dh.nr's from_field_unsafe, which constrains
//!   only lo + 2^128*hi == r: without the limb range checks a prover can
//!   pick a non-canonical split (lo + 2^128, hi - 1), which the MSM
//!   solver rejects, or one that wraps mod p to a different scalar.
//! - Curve ops: total::ec::msm_or, which validates every point and
//!   scalar and swaps invalid ones for (infinity, 0) before the MSM black
//!   box (the select-to-dummy pattern). Here its inputs are always valid
//!   (G is constant; the decoded key is a well-formed Point, infinity on
//!   failure; the scalar is canonical), so its own ok flag is always true;
//!   it is folded in anyway. The ACVM solver accepts every validated
//!   input (checked in total::ec), and msm_or blinds the black box's
//!   bases, so bb's MSM gadget, which has no proof for some valid keys
//!   (its own offset generators, for one), has a proof for every key the
//!   owner can store (total::ec::msm_or has the argument). The in-circuit
//!   ladder (mul_or) does not use the black box at all but costs several
//!   times the gates.
//! - AE: Poseidon2 permutation black boxes (defined for every input, no
//!   predicate needed) and field additions. Definitions only.
//! - Masking: Outcome::mask_field / mask_array, selects on ok.
//!
//! No hints of its own. Every constraint it emits comes from the total
//! gadgets named above, so it adds no input-falsifiable constraint.
//!
//! # Licence of the adapted AE code
//!
//! ae_encrypt, ae_decrypt, io_pattern and the test helper taceo_encrypt
//! are adapted from ae.nr, under this licence:
//!
//! MIT License
//!
//! Copyright (c) 2025 TaceoLabs
//!
//! Permission is hereby granted, free of charge, to any person obtaining a copy
//! of this software and associated documentation files (the "Software"), to deal
//! in the Software without restriction, including without limitation the rights
//! to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//! copies of the Software, and to permit persons to whom the Software is
//! furnished to do so, subject to the following conditions:
//!
//! The above copyright notice and this permission notice shall be included in all
//! copies or substantial portions of the Software.
//!
//! THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//! IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//! FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//! AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//! LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//! OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
//! SOFTWARE.

use std::embedded_curve_ops::{EmbeddedCurvePoint, EmbeddedCurveScalar, multi_scalar_mul};
use std::hash::poseidon2_permutation;
use total::core::{is_zero, limbs, select_field};
use total::ctl::Outcome;
use total::ec::{decode_xy_or, msm_or, on_curve_flag, Point};

/// Plaintext length, fixed so every length in the circuit is static.
pub global PT_LEN: u32 = 4;

/// Ciphertext length: PT_LEN elements plus the tag.
pub global CT_LEN: u32 = 5;

/// Failure codes carried by Outcome (the first failing check wins).
pub global ERR_NO_KEY: Field = 1;
/// The stored key is not on the curve.
pub global ERR_KEY_OFF_CURVE: Field = 2;
/// The stored key is (0, 0), std's encoding of the point at infinity.
pub global ERR_KEY_INFINITY: Field = 3;
/// The sender's randomness is 0, which would give E = S = infinity and a
/// public AE key.
pub global ERR_ZERO_RANDOMNESS: Field = 4;
/// The ephemeral key or shared secret came out at infinity, or msm_or
/// reported an invalid input. Unreachable once the checks above pass
/// (prime-order group, nonzero scalar below q, finite key); kept so ok
/// does not rest on that argument.
pub global ERR_DH: Field = 5;

/// SAFE domain separator used by the reference ae.nr ("AB").
global SAFE_DOMAIN: Field = 0x4142;

/// The SAFE IO-pattern word for ABSORB(2) SQUEEZE(n) ABSORB(n)
/// SQUEEZE(1) with domain separator 0x4142, laid out as ae.nr's T1..T3:
/// 32-bit words [0x80000002, n, 0x80000000 + n, 1] followed by the 16-bit
/// separator. For n = 1, 2, 3 it equals ae.nr's T1, T2, T3 (test
/// io_pattern_matches_taceo). Compile-time arithmetic on constants.
pub fn io_pattern<let N: u32>() -> Field {
    let n = N as Field;
    let w32: Field = 0x100000000;
    let w16: Field = 0x10000;
    let absorb2: Field = 0x80000002;
    let absorb_n = 0x80000000 + n;
    (((absorb2 * w32 + n) * w32 + absorb_n) * w32 + 1) * w16 + SAFE_DOMAIN
}

/// SAFE-style Poseidon2 authenticated encryption of N fields under (key,
/// nonce). Returns N ciphertext elements followed by the tag. See the
/// module header for the construction.
///
/// Constraints: ceil(N / 3) + 1 Poseidon2 permutation black boxes (each
/// defined for every input) and field additions. Definitions only, no
/// failure source, for every input. The loop structure depends only on
/// the compile-time N.
pub fn ae_encrypt<let N: u32>(m: [Field; N], key: Field, nonce: Field) -> [Field; N + 1] {
    let mut s = poseidon2_permutation([key, nonce, 0, io_pattern::<N>()]);
    let mut c = [0; N + 1];
    for i in 0..N {
        if (i != 0) & (i % 3 == 0) {
            s = poseidon2_permutation(s);
        }
        s[i % 3] += m[i];
        c[i] = s[i % 3];
    }
    c[N] = poseidon2_permutation(s)[0];
    c
}

/// Inverse of ae_encrypt: Some(plaintext) when the tag matches, None
/// otherwise. Unconstrained, for the owner's PXE. Trap-free: field
/// arithmetic, permutations and compile-time indices only.
pub unconstrained fn ae_decrypt<let N: u32>(
    c: [Field; N + 1],
    key: Field,
    nonce: Field,
) -> Option<[Field; N]> {
    let mut s = poseidon2_permutation([key, nonce, 0, io_pattern::<N>()]);
    let mut m = [0; N];
    for i in 0..N {
        if (i != 0) & (i % 3 == 0) {
            s = poseidon2_permutation(s);
        }
        m[i] = c[i] - s[i % 3];
        s[i % 3] = c[i];
    }
    let tag = poseidon2_permutation(s)[0];
    if tag == c[N] {
        Option::some(m)
    } else {
        Option::none()
    }
}

/// The result of seal_or. On ok = false, eph_pk_x, eph_pk_y and every
/// ciphertext element are 0, and code names the first failed check.
pub struct Sealed {
    pub eph_pk_x: Field,
    pub eph_pk_y: Field,
    pub ciphertext: [Field; CT_LEN],
    pub ok: bool,
    pub code: Field,
}

/// Decode a stored encryption key: returns (point, outcome) where the
/// outcome fails with ERR_NO_KEY when found is false, ERR_KEY_OFF_CURVE
/// when (x, y) is neither on the curve nor (0, 0), and ERR_KEY_INFINITY
/// for (0, 0). On failure the point is infinity.
///
/// The coordinates are masked to (0, 0) under !found before decoding, so
/// whatever a reader left in an absent key's fields has no effect. Constraints: two selects, decode_xy_or (two is_zero gadgets,
/// on_curve_flag, a Point select: hint-satisfiable for every input),
/// Outcome arithmetic. Determined: found is the caller's, every other
/// flag is determined.
pub fn decode_key_or(x: Field, y: Field, found: bool) -> (Point, Outcome) {
    let kx = select_field(found, x, 0);
    let ky = select_field(found, y, 0);
    let (pk, dec_ok) = decode_xy_or(kx, ky);
    let o = Outcome::good().require(found, ERR_NO_KEY).require(dec_ok, ERR_KEY_OFF_CURVE).require(
        !pk.inf,
        ERR_KEY_INFINITY,
    );
    (pk, o)
}

/// Write-time key check for the constructor and set_encryption_key (both
/// refuse with total_aztec::refuse_bad_key, which asserts this flag):
/// total_aztec::keys::key_ok (on_curve_flag; (0, 0) is not on the curve,
/// so infinity is excluded). Re-exported so the tests below pin it.
pub use total_aztec::keys::key_ok;

/// Encrypt plaintext to the key (key_x, key_y) with sender randomness.
/// found says whether the key was read at all; when it is false the key
/// fields are ignored. TotalAccount.encrypt_for_owner passes the flag of
/// its public-state read (false only for a stored state the variable's
/// own functions cannot produce); an unset key reads as (0, 0), which
/// this refuses as infinity. A reader of a key note passes the note's
/// found flag.
///
/// Returns Sealed. ok is true exactly when found holds, the key is a
/// finite curve point, randomness is nonzero, and the curve operations
/// produced finite points (always, given the previous three). On ok =
/// false every output Field is 0.
///
/// Constraints, all from total gadgets (module header for the
/// arguments): decode_key_or; is_zero(randomness); core::limbs on
/// randomness (two 128-bit RANGEs on hinted limbs, reconstruction, limb
/// comparison against p: hint-satisfiable for every Field); two msm_or
/// calls of one term each (point and scalar validation, the MSM black
/// box on validated and blinded inputs, is_zero on the result); ae_encrypt
/// (definitions); Outcome and masking selects. No assert, no hint of its
/// own. Determinedness: every flag is a determined total flag except
/// found, which the caller supplies; the outputs are functions of the
/// inputs and those flags (msm_or returns the MSM of its inputs).
pub fn seal_or(
    key_x: Field,
    key_y: Field,
    found: bool,
    plaintext: [Field; PT_LEN],
    randomness: Field,
) -> Sealed {
    let (pk, key_outcome) = decode_key_or(key_x, key_y, found);
    let (lo, hi) = limbs(randomness);
    let (eph, eph_ok) = msm_or([Point::generator()], [lo], [hi]);
    let (shared, shared_ok) = msm_or([pk], [lo], [hi]);
    let o = key_outcome.require(!is_zero(randomness), ERR_ZERO_RANDOMNESS).require(
        eph_ok & shared_ok & !eph.inf & !shared.inf,
        ERR_DH,
    );
    let c = ae_encrypt(plaintext, shared.x, eph.x);
    Sealed {
        eph_pk_x: o.mask_field(eph.x),
        eph_pk_y: o.mask_field(eph.y),
        ciphertext: o.mask_array(c),
        ok: o.ok,
        code: o.code,
    }
}

/// Owner-side decryption: (plaintext, ok) with ok = true when (eph_x,
/// eph_y) is on the curve, the shared secret [sk]E is finite, and the
/// tag verifies. On ok = false the plaintext is all zeros. sk is the
/// owner's encryption secret, read as the Grumpkin scalar of its
/// canonical integer.
///
/// Unconstrained, for the owner's PXE. Trap-free for every argument: the
/// on-curve check comes before the MSM black box, so the black box only
/// sees a curve point and a canonical scalar (from_field's limbs are
/// below 2^128 and their integer is below p < q).
pub unconstrained fn open(
    sk: Field,
    eph_x: Field,
    eph_y: Field,
    ciphertext: [Field; CT_LEN],
) -> ([Field; PT_LEN], bool) {
    let mut out = ([0; PT_LEN], false);
    if on_curve_flag(eph_x, eph_y) {
        let e = EmbeddedCurvePoint { x: eph_x, y: eph_y };
        let s = multi_scalar_mul([e], [EmbeddedCurveScalar::from_field(sk)]);
        if !s.is_infinite() {
            let m = ae_decrypt::<PT_LEN>(ciphertext, s.x, eph_x);
            if m.is_some() {
                out = (m.unwrap_unchecked(), true);
            }
        }
    }
    out
}

mod tests {
    use super::{
        ae_decrypt, ae_encrypt, CT_LEN, decode_key_or, ERR_KEY_INFINITY, ERR_KEY_OFF_CURVE,
        ERR_NO_KEY, ERR_ZERO_RANDOMNESS, io_pattern, key_ok, open, PT_LEN, seal_or,
    };
    use std::embedded_curve_ops::{EmbeddedCurveScalar, fixed_base_scalar_mul};
    use std::hash::poseidon2_permutation;
    use total::ec::Point;

    global SK: Field = 0x1d7a0b3c5e9f21a4c6b8d0e2f4a6c8e0b2d4f6a8c0e2b4d6f8a0c2e4b6d8f0a;
    global R: Field = 0x2f1e3d5c7b9a8f6e4d2c1b0a99887766554433221100ffeeddccbbaa998877;
    global MSG: [Field; 4] = [0x11, 0x22, 0x33, 0x44];
    global P_MINUS_1: Field = 0 - 1;

    fn pk_of(sk: Field) -> (Field, Field) {
        let p = fixed_base_scalar_mul(EmbeddedCurveScalar::from_field(sk));
        (p.x, p.y)
    }

    fn assert_masked(s: super::Sealed) {
        assert(!s.ok);
        assert_eq(s.eph_pk_x, 0);
        assert_eq(s.eph_pk_y, 0);
        assert_eq(s.ciphertext, [0; CT_LEN]);
    }

    #[test]
    fn io_pattern_matches_taceo() {
        assert_eq(io_pattern::<1>(), 0x800000020000000180000001000000014142);
        assert_eq(io_pattern::<2>(), 0x800000020000000280000002000000014142);
        assert_eq(io_pattern::<3>(), 0x800000020000000380000003000000014142);
        assert_eq(io_pattern::<4>(), 0x800000020000000480000004000000014142);
    }

    // ae.nr's encrypt1 on the inputs of its encrypt_decrypt1 test: the
    // generic duplex reproduces it.
    #[test]
    fn ae_matches_taceo_kat() {
        let c = ae_encrypt([0x123], 0x456, 0x789);
        assert_eq(c[0], 0x286c1a243c558666b5831713c826988e93d25672dccc21d787e88c81c78209b9);
        assert_eq(c[1], 0x143e77b81535095f93e3a50e6fbc2debc978878f97c60407a07c839736d98df4);
    }

    // ae.nr's encrypt2 / encrypt3 bodies (one rate block), as the
    // reference for the generic duplex at N = 2 and N = 3.
    fn taceo_encrypt<let N: u32>(
        mut data: [Field; N],
        key: Field,
        nonce: Field,
    ) -> ([Field; N], Field) {
        let mut state = poseidon2_permutation([key, nonce, 0, io_pattern::<N>()]);
        for i in 0..N {
            state[i] += data[i];
            data[i] = state[i];
        }
        let tag = poseidon2_permutation(state)[0];
        (data, tag)
    }

    #[test]
    fn ae_matches_taceo_one_block() {
        let (d2, t2) = taceo_encrypt([0x123, 0x456], 0x789, 0xabc);
        let c2 = ae_encrypt([0x123, 0x456], 0x789, 0xabc);
        assert_eq([c2[0], c2[1]], d2);
        assert_eq(c2[2], t2);
        let (d3, t3) = taceo_encrypt([0x123, 0x456, 0x789], 0xabc, 0xdef);
        let c3 = ae_encrypt([0x123, 0x456, 0x789], 0xabc, 0xdef);
        assert_eq([c3[0], c3[1], c3[2]], d3);
        assert_eq(c3[3], t3);
    }

    // Pins the two-block layout used at N = 4: a change to the block
    // boundary handling must turn this red.
    #[test]
    fn ae_two_block_layout() {
        let key = 0xabc;
        let nonce = 0xdef;
        let mut s = poseidon2_permutation([key, nonce, 0, io_pattern::<4>()]);
        s[0] += MSG[0];
        s[1] += MSG[1];
        s[2] += MSG[2];
        let first = [s[0], s[1], s[2]];
        s = poseidon2_permutation(s);
        s[0] += MSG[3];
        let fourth = s[0];
        let tag = poseidon2_permutation(s)[0];
        assert_eq(ae_encrypt(MSG, key, nonce), [first[0], first[1], first[2], fourth, tag]);
    }

    #[test]
    unconstrained fn ae_round_trip_lengths() {
        let key = 0xabc;
        let nonce = 0xdef;
        let m1 = ae_decrypt::<1>(ae_encrypt([7], key, nonce), key, nonce);
        assert_eq(m1.unwrap(), [7]);
        let m3 = ae_decrypt::<3>(ae_encrypt([7, 8, 9], key, nonce), key, nonce);
        assert_eq(m3.unwrap(), [7, 8, 9]);
        let m4 = ae_decrypt::<4>(ae_encrypt(MSG, key, nonce), key, nonce);
        assert_eq(m4.unwrap(), MSG);
        let m7 = ae_decrypt::<7>(ae_encrypt([1, 2, 3, 4, 5, 6, 7], key, nonce), key, nonce);
        assert_eq(m7.unwrap(), [1, 2, 3, 4, 5, 6, 7]);
    }

    #[test]
    unconstrained fn ae_rejects_tampering() {
        let key = 0xabc;
        let nonce = 0xdef;
        let c = ae_encrypt(MSG, key, nonce);
        // every single-element change, including the second rate block
        // and the tag, breaks the tag check
        for i in 0..CT_LEN {
            let mut bad = c;
            bad[i] += 1;
            assert(ae_decrypt::<PT_LEN>(bad, key, nonce).is_none());
        }
        assert(ae_decrypt::<PT_LEN>(c, key + 1, nonce).is_none());
        assert(ae_decrypt::<PT_LEN>(c, key, nonce + 1).is_none());
    }

    #[test]
    fn seal_then_open_round_trip() {
        let (x, y) = pk_of(SK);
        let s = seal_or(x, y, true, MSG, R);
        assert(s.ok);
        assert_eq(s.code, 0);
        // E = [r]G
        let e = fixed_base_scalar_mul(EmbeddedCurveScalar::from_field(R));
        assert_eq(s.eph_pk_x, e.x);
        assert_eq(s.eph_pk_y, e.y);
        // Safety: test only.
        let (m, ok) = unsafe { open(SK, s.eph_pk_x, s.eph_pk_y, s.ciphertext) };
        assert(ok);
        assert_eq(m, MSG);
    }

    #[test]
    fn seal_edge_scalars() {
        // r = 1 and r = p - 1 (largest Field scalar) both work
        let (x, y) = pk_of(SK);
        let s1 = seal_or(x, y, true, MSG, 1);
        assert(s1.ok);
        // Safety: test only.
        let (m1, ok1) = unsafe { open(SK, s1.eph_pk_x, s1.eph_pk_y, s1.ciphertext) };
        assert(ok1);
        assert_eq(m1, MSG);
        let s2 = seal_or(x, y, true, MSG, P_MINUS_1);
        assert(s2.ok);
        // Safety: test only.
        let (m2, ok2) = unsafe { open(SK, s2.eph_pk_x, s2.eph_pk_y, s2.ciphertext) };
        assert(ok2);
        assert_eq(m2, MSG);
        // the owner secret at p - 1 too
        let (xs, ys) = pk_of(P_MINUS_1);
        let s3 = seal_or(xs, ys, true, MSG, R);
        assert(s3.ok);
        // Safety: test only.
        let (m3, ok3) = unsafe { open(P_MINUS_1, s3.eph_pk_x, s3.eph_pk_y, s3.ciphertext) };
        assert(ok3);
        assert_eq(m3, MSG);
    }

    #[test]
    unconstrained fn open_rejects_bad_inputs() {
        let (x, y) = pk_of(SK);
        let s = seal_or(x, y, true, MSG, R);
        // corrupted ciphertext element, corrupted tag
        let mut bad = s.ciphertext;
        bad[3] += 1;
        let (m, ok) = open(SK, s.eph_pk_x, s.eph_pk_y, bad);
        assert(!ok);
        assert_eq(m, [0; PT_LEN]);
        let mut bad_tag = s.ciphertext;
        bad_tag[4] += 1;
        assert(!open(SK, s.eph_pk_x, s.eph_pk_y, bad_tag).1);
        // wrong secret
        assert(!open(SK + 1, s.eph_pk_x, s.eph_pk_y, s.ciphertext).1);
        // off-curve ephemeral key: flagged before the MSM, no trap
        assert(!open(SK, s.eph_pk_x, s.eph_pk_y + 1, s.ciphertext).1);
        // the masked output of a failed seal does not open
        assert(!open(SK, 0, 0, [0; CT_LEN]).1);
        // -E has the same x (the AE nonce) but gives the shared secret -S,
        // which has the same x too: the scheme accepts it. Pinned so a
        // change in that behaviour is noticed.
        assert(open(SK, s.eph_pk_x, 0 - s.eph_pk_y, s.ciphertext).1);
    }

    #[test]
    fn key_decode_flags() {
        let (x, y) = pk_of(SK);
        let (p, o) = decode_key_or(x, y, true);
        assert(o.ok);
        assert(!p.inf);
        // off curve
        let (p1, o1) = decode_key_or(x, y + 1, true);
        assert(!o1.ok);
        assert_eq(o1.code, ERR_KEY_OFF_CURVE);
        assert(p1.inf);
        // infinity encoding
        let (_, o2) = decode_key_or(0, 0, true);
        assert(!o2.ok);
        assert_eq(o2.code, ERR_KEY_INFINITY);
        // (0, y) and (x, 0) are off curve
        let (_, o3) = decode_key_or(0, y, true);
        assert_eq(o3.code, ERR_KEY_OFF_CURVE);
        let (_, o4) = decode_key_or(x, 0, true);
        assert_eq(o4.code, ERR_KEY_OFF_CURVE);
        // p - 1 coordinates
        let (_, o5) = decode_key_or(P_MINUS_1, P_MINUS_1, true);
        assert_eq(o5.code, ERR_KEY_OFF_CURVE);
        // not found: the coordinates are ignored, even valid ones
        let (p6, o6) = decode_key_or(x, y, false);
        assert_eq(o6.code, ERR_NO_KEY);
        assert(p6.inf);
        let (_, o7) = decode_key_or(x, y + 1, false);
        assert_eq(o7.code, ERR_NO_KEY);
        // write-time check
        assert(key_ok(x, y));
        assert(!key_ok(x, y + 1));
        assert(!key_ok(0, 0));
        // field-max coordinates (p - 1, p - 1): y^2 = 1, x^3 - 17 = -18
        assert(!key_ok(-1, -1));
        let (p8, o8) = decode_key_or(-1, -1, true);
        assert_eq(o8.code, ERR_KEY_OFF_CURVE);
        assert(p8.inf);
        let g = Point::generator();
        assert(key_ok(g.x, g.y));
    }

    #[test]
    fn seal_masks_on_every_failure() {
        let (x, y) = pk_of(SK);
        let s1 = seal_or(x, y, false, MSG, R);
        assert_masked(s1);
        assert_eq(s1.code, ERR_NO_KEY);
        let s2 = seal_or(x, y + 1, true, MSG, R);
        assert_masked(s2);
        assert_eq(s2.code, ERR_KEY_OFF_CURVE);
        let s3 = seal_or(0, 0, true, MSG, R);
        assert_masked(s3);
        assert_eq(s3.code, ERR_KEY_INFINITY);
        let s4 = seal_or(x, y, true, MSG, 0);
        assert_masked(s4);
        assert_eq(s4.code, ERR_ZERO_RANDOMNESS);
        let s5 = seal_or(P_MINUS_1, 5, true, [P_MINUS_1; PT_LEN], P_MINUS_1);
        assert_masked(s5);
        assert_eq(s5.code, ERR_KEY_OFF_CURVE);
        // first failure wins: no key and zero randomness reports no key
        let s6 = seal_or(x, y, false, MSG, 0);
        assert_eq(s6.code, ERR_NO_KEY);
    }

    #[test]
    fn seal_is_deterministic_and_fresh() {
        let (x, y) = pk_of(SK);
        let a = seal_or(x, y, true, MSG, R);
        let b = seal_or(x, y, true, MSG, R);
        assert_eq(a.ciphertext, b.ciphertext);
        let c = seal_or(x, y, true, MSG, R + 1);
        assert(c.eph_pk_x != a.eph_pk_x);
        assert(c.ciphertext[0] != a.ciphertext[0]);
    }
}
