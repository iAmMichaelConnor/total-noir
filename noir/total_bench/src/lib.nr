//! Benchmarks: one exported function per family of primitives. Changes to the
//! gate count or Brillig size of these functions show up on pull requests.

use total::arith::{TotalArith, TotalMulDiv, TotalUnsigned};
use total::bitwise::TotalShift;
use total::collections::bounded_vec::TotalBoundedVec;
use total::convert::{to_i64_or, to_u64_or};

#[export]
fn fits_bits_64(x: Field) -> bool {
    total::fits_bits::<64>(x)
}

#[export]
fn field_lt(a: Field, b: Field) -> bool {
    total::lt(a, b)
}

#[export]
fn to_u64(x: Field) -> (u64, bool) {
    to_u64_or(x)
}

#[export]
fn to_i64(x: Field) -> (i64, bool) {
    to_i64_or(x)
}

#[export]
fn u64_add(a: u64, b: u64) -> (u64, bool) {
    a.add_or(b)
}

#[export]
fn u64_mul(a: u64, b: u64) -> (u64, bool) {
    a.mul_or(b)
}

#[export]
fn u64_div(a: u64, b: u64) -> (u64, bool) {
    a.div_or(b)
}

#[export]
fn u64_mul_div(a: u64, b: u64, d: u64) -> (u64, u64, bool) {
    a.mul_div_or(b, d)
}

#[export]
fn u128_add(a: u128, b: u128) -> (u128, bool) {
    a.add_or(b)
}

#[export]
fn u128_mul(a: u128, b: u128) -> (u128, bool) {
    a.mul_or(b)
}

#[export]
fn u128_div(a: u128, b: u128) -> (u128, bool) {
    a.div_or(b)
}

#[export]
fn u128_mul_div(a: u128, b: u128, d: u128) -> (u128, u128, bool) {
    a.mul_div_or(b, d)
}

#[export]
fn i64_add(a: i64, b: i64) -> (i64, bool) {
    a.add_or(b)
}

#[export]
fn i64_mul(a: i64, b: i64) -> (i64, bool) {
    a.mul_or(b)
}

#[export]
fn i64_mul_div(a: i64, b: i64, d: i64) -> (i64, i64, bool) {
    a.mul_div_or(b, d)
}

#[export]
fn u64_isqrt(x: u64) -> u64 {
    x.isqrt()
}

#[export]
fn u128_widening_mul(a: u128, b: u128) -> (u128, u128) {
    a.widening_mul(b)
}

#[export]
fn field_add_128(a: Field, b: Field) -> (Field, bool) {
    total::arith::add_or::<128>(a, b)
}

#[export]
fn field_pow(base: Field, exp: Field) -> (Field, bool) {
    total::arith::pow_or::<64, 8>(base, exp)
}

#[export]
fn field_sqrt(x: Field) -> (Field, bool) {
    total::arith::sqrt_or(x)
}

#[export]
fn field_inverse(x: Field) -> (Field, bool) {
    total::inverse_or(x)
}

#[export]
fn shl_64(a: Field, s: Field) -> (Field, bool) {
    total::bitwise::shl_exact_or::<64>(a, s)
}

#[export]
fn u128_shl(a: u128, s: u128) -> (u128, bool) {
    a.shl_or(s)
}

#[export]
fn index_16(arr: [Field; 16], i: Field) -> (Field, bool) {
    total::index_or(arr, i)
}

#[export]
fn bounded_vec_push_get_16(v: BoundedVec<Field, 16>, x: Field, i: u32) -> (Field, bool) {
    let (w, pushed) = v.push_or(x);
    let (y, found) = w.get_or(i);
    (y, pushed & found)
}

#[export]
fn poseidon2_var_8(input: [Field; 8], len: Field) -> (Field, bool) {
    total::hash::p2_hash_var_or(input, len)
}

#[export]
fn grumpkin_decode(x: Field, y: Field, inf: Field) -> (total::ec::Point, bool) {
    total::ec::decode_or(x, y, inf)
}

#[export]
fn msm_or_1(x: Field, y: Field, lo: Field, hi: Field) -> (total::ec::Point, bool) {
    total::ec::msm_or([total::ec::Point { x, y, inf: false }], [lo], [hi])
}

#[export]
fn msm_or_2(
    x: [Field; 2],
    y: [Field; 2],
    lo: [Field; 2],
    hi: [Field; 2],
) -> (total::ec::Point, bool) {
    let p = total::ec::Point { x: x[0], y: y[0], inf: false };
    let q = total::ec::Point { x: x[1], y: y[1], inf: false };
    total::ec::msm_or([p, q], lo, hi)
}

#[export]
fn sha256_var_64(input: [u8; 64], len: Field) -> ([u8; 32], bool) {
    total::hash::sha256_var_or(input, len)
}

#[export]
fn keccak256_var_136(input: [u8; 136], len: Field) -> ([u8; 32], bool) {
    total::hash::keccak256_var_or(input, len)
}

#[export]
fn schnorr_verify(pk_x: Field, pk_y: Field, sig: [Field; 4], msg: Field) -> bool {
    total::schnorr_verify(pk_x, pk_y, sig, msg)
}

#[export]
fn ecdsa_k1_verify(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> bool {
    total::ecdsa_k1_verify(pk_x, pk_y, sig, hash)
}

#[export]
fn fits_bits_160(x: Field) -> bool {
    total::fits_bits::<160>(x)
}

#[export]
fn sort_8(arr: [Field; 8]) -> ([Field; 8], bool) {
    total::collections::sort_or::<8, 64>(arr)
}

#[export]
fn merkle_root_20(leaf: Field, index: Field, path: [Field; 20]) -> (Field, bool) {
    total::merkle::merkle_root_or(leaf, index, path)
}

#[export]
fn secp256k1_on_curve(x: [u8; 32], y: [u8; 32]) -> bool {
    total::secp::secp256k1_on_curve(x, y)
}
