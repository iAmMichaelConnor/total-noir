//! secp256k1_on_curve and secp256r1_on_curve against integer arithmetic
//! (x < p, y < p and y^2 == x^3 + ax + b mod p, in TypeScript BigInt).
//!
//! Seeded cases: random curve points and their negations, points with small
//! x (x = 0 is on P-256), the largest x on the curve, points with x + p or
//! y + p in place of a coordinate, random off-curve pairs, a valid point with
//! one bit flipped, and pairs of edge values (0, 1, p - 1, p, p + 1,
//! 2^256 - 1, random values below and above p). The raw tests take the bytes
//! straight from the fuzzer.

use total::secp::{secp256k1_on_curve, secp256r1_on_curve};

global K1: Field = 1;
global R1: Field = 2;

#[oracle(secp_case)]
unconstrained fn secp_case_oracle(seed: Field, curve: Field) -> ([u8; 32], [u8; 32], bool) {}

unconstrained fn secp_case(seed: Field, curve: Field) -> ([u8; 32], [u8; 32], bool) {
    secp_case_oracle(seed, curve)
}

#[oracle(secp_on_curve_ref)]
unconstrained fn secp_on_curve_ref_oracle(x: [u8; 32], y: [u8; 32], curve: Field) -> bool {}

unconstrained fn secp_on_curve_ref(x: [u8; 32], y: [u8; 32], curve: Field) -> bool {
    secp_on_curve_ref_oracle(x, y, curve)
}

#[test]
fn secp256k1_on_curve_matches_reference(seed: Field) {
    // Safety: the oracle only supplies the case and the expected answer.
    let (x, y, expected) = unsafe { secp_case(seed, K1) };
    assert_eq(secp256k1_on_curve(x, y), expected);
}

#[test]
fn secp256r1_on_curve_matches_reference(seed: Field) {
    // Safety: the oracle only supplies the case and the expected answer.
    let (x, y, expected) = unsafe { secp_case(seed, R1) };
    assert_eq(secp256r1_on_curve(x, y), expected);
}

#[test]
fn secp256k1_on_curve_raw_bytes(x: [u8; 32], y: [u8; 32]) {
    // Safety: the oracle only supplies the expected answer.
    let expected = unsafe { secp_on_curve_ref(x, y, K1) };
    assert_eq(secp256k1_on_curve(x, y), expected);
}

#[test]
fn secp256r1_on_curve_raw_bytes(x: [u8; 32], y: [u8; 32]) {
    // Safety: the oracle only supplies the expected answer.
    let expected = unsafe { secp_on_curve_ref(x, y, R1) };
    assert_eq(secp256r1_on_curve(x, y), expected);
}
