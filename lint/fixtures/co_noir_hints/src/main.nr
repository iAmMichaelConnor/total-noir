// Every family of total's public entries that runs a hint (the library's own
// and the compiler's and std's), called on private inputs, for
// scripts/mpc-check.sh: its Brillig must hold no opcode co-noir's MPC VM
// cannot execute, and (with a co-noir binary) its three-party witness
// extension must succeed. The results fold into public accumulators, so a
// wrong hint value changes a public output; nargo execute gives the
// reference values.
//
// Covered: range and convert (fits, clamp, to_*_or, bits, bytes, truncate_or,
// narrow_or, sgn0); Field-domain and typed arithmetic (checked, wrapping,
// saturating add/sub/mul, neg, div, mod, mul_div and mul_div_ceil on
// unsigned and signed types, the wide mul_div, pow, inverse, TotalUnsigned's
// widening_mul, isqrt and abs_diff); bitwise (*_bits, shifts and rotates to 128 bits, TotalShift);
// signed (TotalArith and
// TotalSigned on i8..i64, abs); comparison (TotalOrd on every type,
// cmp_bits); collections and the BoundedVec forms; ec (decode, add, double, sub, the ladders, msm);
// schnorr_verify;
// secp (secp256k1_on_curve, secp256r1_on_curve); encode (canonical flags,
// chunks, fixed-width bytes, byte strings as BoundedVec<u8>); hash (p2_hash,
// the variable-length forms, Sponge); merkle.
//
// Excluded: sqrt_or and sqrt_canonical_or, whose Tonelli-Shanks hint does
// not run in co-noir, and hash::sha256_var_or and hash::keccak256_var_or, whose
// libraries' shift hints and keccakf1600 black box co-noir cannot run
// (docs/co-noir.md). The Prover.toml values
// exercise the ok and the not-ok path of each family: zero divisors, values
// above their declared width, p - 1, MIN / -1, off-curve points, lengths
// past the array.
use total::arith::{
    add_or, field_div_or, inverse_or, mul_or, neg_or, Saturating, saturating_add_or,
    saturating_mul_or, saturating_sub_or, sub_or, wrapping_add_or, wrapping_mul_or, wrapping_neg_or,
    wrapping_sub_or,
};
use total::arith::{div_rem_or, mod_or, mul_div_or, mul_div_to_or, pow_or, TotalArith, TotalMulDiv};
use total::arith::{mul_div_wide_or, mul_div_wide_to_or};
use total::arith::TotalUnsigned;
use total::bitwise::{and_bits_or, not_bits_or, or_bits_or, xor_bits_or};
use total::bitwise::{rotate_left_or, rotate_right_or, shl_exact_or, shl_or, shr_or, TotalShift};
use total::cmp::{cmp_bits, TotalOrd};
use total::collections::bounded_vec::{from_parts_or, from_prefix_or, TotalBoundedVec};
use total::collections::{
    first_index_of_or, first_true_or, index_flags_or, index_or, is_sorted_or, max_of_or, min_of_or,
    prefix_mask_or, set_or, sort_or, subarray_or, sum_or, sum_wide_or,
};
use total::convert::{
    bool_or, from_be_bits_or, from_be_bytes_or, from_i16_signed, from_i32_signed, from_i64_signed,
    from_i8_signed, from_le_bits_or, from_le_bytes_or, to_be_bits_or, to_be_bits_total,
    to_be_bytes_or, to_be_bytes_total, to_i16_from_signed_or, to_i32_from_signed_or,
    to_i64_from_signed_or, to_i8_from_signed_or, to_le_bits_or, to_le_bits_total, to_le_bytes_or,
    to_le_bytes_total, TotalNarrow, truncate_or,
};
use total::convert::{
    to_i16_or, to_i32_or, to_i64_or, to_i8_or, to_u128_or, to_u16_or, to_u32_or, to_u64_or,
    to_u8_or,
};
use total::ec::{self, Point};
use total::encode;
use total::hash::{p2_hash, p2_hash_sep, p2_hash_sep_var_or, p2_hash_var_or, Sponge};
use total::merkle;
use total::range::{clamp_bits_or, fits_bits};
use total::schnorr::schnorr_verify;
use total::secp::{secp256k1_on_curve, secp256r1_on_curve};
use total::signed::{
    TotalSigned, unsigned_abs_i16, unsigned_abs_i32, unsigned_abs_i64, unsigned_abs_i8,
};

fn f(b: bool) -> Field {
    b as Field
}

fn mix(acc: Field, v: Field) -> Field {
    acc * 3 + v
}

fn mixk(acc: Field, v: Field, k: bool) -> Field {
    mix(mix(acc, v), f(k))
}

// A typed value's bit pattern as a Field, for the accumulators.
trait ToF {
    fn to_f(self) -> Field;
}
impl ToF for Field {
    fn to_f(self) -> Field {
        self
    }
}
impl ToF for bool {
    fn to_f(self) -> Field {
        self as Field
    }
}
impl ToF for u8 {
    fn to_f(self) -> Field {
        self as Field
    }
}
impl ToF for u16 {
    fn to_f(self) -> Field {
        self as Field
    }
}
impl ToF for u32 {
    fn to_f(self) -> Field {
        self as Field
    }
}
impl ToF for u64 {
    fn to_f(self) -> Field {
        self as Field
    }
}
impl ToF for u128 {
    fn to_f(self) -> Field {
        self as Field
    }
}
impl ToF for i8 {
    fn to_f(self) -> Field {
        (self as u8) as Field
    }
}
impl ToF for i16 {
    fn to_f(self) -> Field {
        (self as u16) as Field
    }
}
impl ToF for i32 {
    fn to_f(self) -> Field {
        (self as u32) as Field
    }
}
impl ToF for i64 {
    fn to_f(self) -> Field {
        (self as u64) as Field
    }
}

fn fold_arr<T, let N: u32>(arr: [T; N]) -> Field
where
    T: ToF,
{
    let mut acc: Field = 0;
    for i in 0..N {
        acc = acc * 257 + arr[i].to_f();
    }
    acc
}

fn fold_point(acc: Field, p: Point) -> Field {
    mixk(mix(acc, p.x), p.y, p.inf)
}

// TotalArith on a type (unsigned and signed).
fn arith_ops<T>(a: T, b: T) -> Field
where
    T: TotalArith + ToF,
{
    let mut acc: Field = 0;
    let (v, k) = a.add_or(b);
    acc = mixk(acc, v.to_f(), k);
    let (v, k) = a.sub_or(b);
    acc = mixk(acc, v.to_f(), k);
    let (v, k) = a.mul_or(b);
    acc = mixk(acc, v.to_f(), k);
    let (v, k) = a.div_or(b);
    acc = mixk(acc, v.to_f(), k);
    let (v, k) = a.mod_or(b);
    mixk(acc, v.to_f(), k)
}

fn sat_ops<T>(a: T, b: T) -> Field
where
    T: Saturating + ToF,
{
    let v1 = a.saturating_add(b).to_f();
    let v2 = a.saturating_sub(b).to_f();
    let v3 = a.saturating_mul(b).to_f();
    v1 * 9 + v2 * 3 + v3
}

fn mul_div_ops<T>(a: T, b: T, d: T) -> Field
where
    T: TotalMulDiv + ToF,
{
    let (v, w, k) = a.mul_div_or(b, d);
    let (c, l) = a.mul_div_ceil_or(b, d);
    mixk(mixk(v.to_f() * 3 + w.to_f(), 0, k), c.to_f(), l)
}

fn unsigned_ops<T>(a: T, b: T) -> Field
where
    T: TotalUnsigned + ToF,
{
    let (lo, hi) = a.widening_mul(b);
    let (p, k) = a.pow_or(3);
    let (c, l) = a.div_ceil_or(b);
    let acc = mix(
        mix(mix(lo.to_f(), hi.to_f()), a.isqrt().to_f()),
        a.abs_diff(b).to_f(),
    );
    mixk(mixk(acc, p.to_f(), k), c.to_f(), l)
}

fn signed_ops<T>(a: T) -> Field
where
    T: TotalSigned + ToF,
{
    let (v, k) = a.neg_or();
    let (w, l) = a.abs_or();
    mixk(mixk(0, v.to_f(), k), w.to_f(), l)
}

fn ord_ops<T>(a: T, b: T, c: T) -> Field
where
    T: TotalOrd + ToF,
{
    let flags = [
        total::cmp::eq(a, b),
        total::cmp::neq(a, b),
        total::cmp::lt(a, b),
        total::cmp::lte(a, b),
        total::cmp::gt(a, b),
        total::cmp::gte(a, b),
    ];
    let lo = total::cmp::min(b, c);
    let hi = total::cmp::max(b, c);
    let v = total::cmp::min(a, b).to_f()
        + total::cmp::max(a, b).to_f() * 5
        + total::cmp::clamp(a, lo, hi).to_f() * 7;
    fold_arr(flags) * 3 + v
}

fn narrow<S, T>(s: S) -> Field
where
    S: TotalNarrow<T>,
    T: ToF,
{
    let (v, k): (T, bool) = s.narrow_or();
    v.to_f() * 2 + f(k)
}

// Field-domain add, sub, mul and neg at width N on one pair.
fn width_ops<let N: u32>(a: Field, b: Field) -> Field {
    let mut acc: Field = 0;
    let (v, k) = add_or::<N>(a, b);
    acc = mixk(acc, v, k);
    let (v, k) = wrapping_add_or::<N>(a, b);
    acc = mixk(acc, v, k);
    let (v, k) = saturating_add_or::<N>(a, b);
    acc = mixk(acc, v, k);
    let (v, k) = sub_or::<N>(a, b);
    acc = mixk(acc, v, k);
    let (v, k) = wrapping_sub_or::<N>(a, b);
    acc = mixk(acc, v, k);
    let (v, k) = saturating_sub_or::<N>(a, b);
    acc = mixk(acc, v, k);
    let (v, k) = mul_or::<N>(a, b);
    acc = mixk(acc, v, k);
    let (v, k) = wrapping_mul_or::<N>(a, b);
    acc = mixk(acc, v, k);
    let (v, k) = saturating_mul_or::<N>(a, b);
    acc = mixk(acc, v, k);
    let (v, k) = wrapping_neg_or::<N>(a);
    acc = mixk(acc, v, k);
    let (v, k) = neg_or::<N>(a);
    mixk(acc, v, k)
}

// Shifts and rotates at width N.
fn shift_ops<let N: u32>(a: Field, s: Field) -> Field {
    let mut acc: Field = 0;
    let (v, k) = shl_exact_or::<N>(a, s);
    acc = mixk(acc, v, k);
    let (v, k) = shl_or::<N>(a, s);
    acc = mixk(acc, v, k);
    let (v, k) = shr_or::<N>(a, s);
    acc = mixk(acc, v, k);
    let (v, k) = rotate_left_or::<N>(a, s);
    acc = mixk(acc, v, k);
    let (v, k) = rotate_right_or::<N>(a, s);
    mixk(acc, v, k)
}

// TotalShift on a typed value and shift amount.
fn typed_shift_ops<T>(a: T, s: T) -> Field
where
    T: TotalShift + ToF,
{
    let (v, k) = a.shl_or(s);
    let acc = mixk(0, v.to_f(), k);
    let (v, k) = a.shl_exact_or(s);
    let acc = mixk(acc, v.to_f(), k);
    let (v, k) = a.shr_or(s);
    mixk(acc, v.to_f(), k)
}

// A BoundedVec's storage, length and flag, for the accumulators.
fn fold_bv<let M: u32>(acc: Field, v: BoundedVec<Field, M>, k: bool) -> Field {
    mixk(mix(acc, fold_arr(v.storage())), v.len() as Field, k)
}

// Every BoundedVec form on a vector of capacity 4 built from the first
// len entries of base, with runtime indices and lengths.
fn bounded_vec_ops(base: [Field; 4], len: u32, i: u32, j: u32, x: Field) -> Field {
    let mut acc: Field = 0;
    let (v, k) = from_prefix_or(base, len);
    acc = fold_bv(acc, v, k);
    let (w, k) = from_parts_or(base, len);
    acc = fold_bv(acc, w, k);
    acc = mix(acc, f(v.is_valid()));
    let (y, k) = v.get_or(i);
    acc = mixk(acc, y, k);
    let (w, k) = v.set_or(i, x);
    acc = fold_bv(acc, w, k);
    let (w, k) = v.push_or(x);
    acc = fold_bv(acc, w, k);
    let (w, y, k) = v.pop_or();
    acc = mixk(fold_bv(acc, w, k), y, k);
    let (w, k) = v.set_len_or(j);
    acc = fold_bv(acc, w, k);
    let (w, k) = v.extend_from_array_or([x, base[0]]);
    acc = fold_bv(acc, w, k);
    let (small, _): (BoundedVec<Field, 2>, bool) = from_prefix_or([x, base[1]], i);
    let (w, k) = v.extend_from_bounded_vec_or(small);
    acc = fold_bv(acc, w, k);
    let g = total::ctl::Select::select(k, w, v);
    fold_bv(acc, g, k)
}

// Comparison of raw Fields at width N.
fn cmp_ops<let N: u32>(a: Field, b: Field) -> Field {
    let c = cmp_bits::<N>(a, b);
    fold_arr(
        [c.lt, c.eq, c.gt, c.a_ok, c.b_ok, c.ok(), c.lte(), c.gte(), c.neq()],
    )
}

fn trunc_ops<let N: u32>(x: Field) -> Field {
    let (lo, rest, k) = truncate_or::<N>(x);
    mixk(mix(0, lo), rest, k)
}

fn bit_ops<let N: u32, let B: u32>(x: Field) -> Field {
    let (le, k1) = to_le_bits_or::<N>(x);
    let (be, k2) = to_be_bits_or::<N>(x);
    let (ble, k3) = to_le_bytes_or::<B>(x);
    let (bbe, k4) = to_be_bytes_or::<B>(x);
    fold_arr(le) * 3
        + fold_arr(be)
        + fold_arr(ble) * 5
        + fold_arr(bbe)
        + f(k1)
        + f(k2) * 2
        + f(k3) * 4
        + f(k4) * 8
}

fn main(
    xs: [Field; 6],
    a8: u8,
    b8: u8,
    a16: u16,
    b16: u16,
    a32: u32,
    b32: u32,
    a64: u64,
    b64: u64,
    d64: u64,
    ws: [Field; 5],
    a128: u128,
    b128: u128,
    d128: u128,
    sh: [Field; 4],
    shw: [u128; 4],
    lens: [u32; 4],
    u8s: [u8; 4],
    u16s: [u16; 4],
    u32s: [u32; 4],
    u64s: [u64; 4],
    u128s: [u128; 4],
    i8s: [i8; 4],
    i16s: [i16; 4],
    i32s: [i32; 4],
    i64s: [i64; 4],
    nc: [u8; 32],
    ex: [Field; 5],
    ey: [Field; 5],
    einf: [Field; 5],
    gx: [u8; 32],
    gy: [u8; 32],
) -> pub [Field; 17] {
    let mut range: Field = 0;
    let mut conv: Field = 0;
    let mut arith: Field = 0;
    let mut bits: Field = 0;
    for i in 0..6 {
        let x = xs[i];
        range = range * 7
            + f(fits_bits::<1>(x))
            + f(fits_bits::<8>(x)) * 2
            + f(fits_bits::<64>(x)) * 4
            + f(fits_bits::<127>(x)) * 8
            + f(fits_bits::<128>(x)) * 16
            + f(total::range::fits_bits::<100>(x)) * 32
            + f(fits_bits::<160>(x)) * 64;
        let (c, ok) = clamp_bits_or::<64>(x);
        let (c2, ok2) = total::range::clamp_bits_or::<32>(x);
        range = range * 3 + c + f(ok) + c2 + f(ok2);
        let (u1, k1) = to_u8_or(x);
        let (u2, k2) = to_u16_or(x);
        let (u3, k3) = to_u32_or(x);
        let (u4, k4) = to_u64_or(x);
        let (s1, j1) = to_i8_or(x);
        let (s2, j2) = to_i16_or(x);
        let (s3, j3) = to_i32_or(x);
        let (s4, j4) = to_i64_or(x);
        conv = conv * 5
            + (u1 as Field)
            + (u2 as Field)
            + (u3 as Field)
            + (u4 as Field)
            + ((s1 as u8) as Field)
            + ((s2 as u16) as Field)
            + ((s3 as u32) as Field)
            + ((s4 as u64) as Field)
            + f(k1)
            + f(k2)
            + f(k3)
            + f(k4)
            + f(j1)
            + f(j2)
            + f(j3)
            + f(j4);
        let y = xs[(i + 1) % 6];
        let (q, r, ok) = div_rem_or::<64>(x, y);
        let (r2, ok2) = mod_or::<8>(x, y);
        let (mq, mr, mok) = mul_div_or::<64>(x, y, xs[(i + 2) % 6]);
        let (tq, tr, tok) = mul_div_to_or::<84, 84>(x, y, xs[(i + 3) % 6]);
        let (p, pok) = pow_or::<64, 8>(x, y);
        arith = arith * 11
            + q
            + r
            + f(ok)
            + r2
            + f(ok2)
            + mq
            + mr
            + f(mok)
            + tq
            + tr
            + f(tok)
            + p
            + f(pok);
        let (w1, o1) = and_bits_or::<64>(x, y);
        let (w2, o2) = or_bits_or::<8>(x, y);
        let (w3, o3) = xor_bits_or::<128>(x, y);
        let (w4, o4) = not_bits_or::<32>(x);
        bits = bits * 13 + w1 + w2 + w3 + w4 + f(o1) + f(o2) + f(o3) + f(o4);
    }
    // TotalArith and TotalMulDiv on every type
    let mut typed: Field = 0;
    let (v, k) = a8.add_or(b8);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a8.sub_or(b8);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a8.mul_or(b8);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a8.div_or(b8);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a8.mod_or(b8);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, w, k) = a8.mul_div_or(b8, 3);
    typed = typed * 3 + (v as Field) + (w as Field) + f(k);
    let (v, k) = a16.add_or(b16);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a16.sub_or(b16);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a16.mul_or(b16);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a16.div_or(b16);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a16.mod_or(b16);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, w, k) = a16.mul_div_or(b16, 7);
    typed = typed * 3 + (v as Field) + (w as Field) + f(k);
    let (v, k) = a32.add_or(b32);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a32.sub_or(b32);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a32.mul_or(b32);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a32.div_or(b32);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a32.mod_or(b32);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, w, k) = a32.mul_div_or(b32, 11);
    typed = typed * 3 + (v as Field) + (w as Field) + f(k);
    let (v, k) = a64.add_or(b64);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a64.sub_or(b64);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a64.mul_or(b64);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a64.div_or(d64);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, k) = a64.mod_or(d64);
    typed = typed * 3 + (v as Field) + f(k);
    let (v, w, k) = a64.mul_div_or(b64, d64);
    typed = typed * 3 + (v as Field) + (w as Field) + f(k);
    let (v, w, k) = a64.mul_div_or(b64, 0);
    typed = typed * 3 + (v as Field) + (w as Field) + f(k);
    // The wide multiply-divide (Field operands past 84 bits, the u128
    // facade), TotalArith on u128 and to_u128_or
    let mut wide: Field = 0;
    for i in 0..5 {
        let (x, y, z) = (ws[i], ws[(i + 1) % 5], ws[(i + 2) % 5]);
        let (l, h, r, ok) = mul_div_wide_or::<96>(x, y, z);
        let (l2, h2, r2, ok2) = mul_div_wide_or::<128>(x, y, z);
        let (t1, s1, k1) = mul_div_wide_to_or::<100>(x, y, z);
        let (t2, s2, k2) = mul_div_wide_to_or::<128>(x, y, z);
        let (t3, s3, k3) = mul_div_wide_to_or::<135>(x, y, z);
        let (u, k4) = to_u128_or(x);
        wide = wide * 17
            + l
            + h
            + r
            + f(ok)
            + l2
            + h2
            + r2
            + f(ok2)
            + t1
            + s1
            + f(k1)
            + t2
            + s2
            + f(k2)
            + t3
            + s3
            + f(k3)
            + (u as Field)
            + f(k4);
    }
    let (v, k) = a128.add_or(b128);
    wide = wide * 3 + (v as Field) + f(k);
    let (v, k) = a128.sub_or(b128);
    wide = wide * 3 + (v as Field) + f(k);
    let (v, k) = a128.mul_or(b128);
    wide = wide * 3 + (v as Field) + f(k);
    let (v, k) = a128.div_or(d128);
    wide = wide * 3 + (v as Field) + f(k);
    let (v, k) = a128.mod_or(d128);
    wide = wide * 3 + (v as Field) + f(k);
    let (v, k) = a128.div_or(0);
    wide = wide * 3 + (v as Field) + f(k);
    let (v, w, k) = a128.mul_div_or(b128, d128);
    wide = wide * 3 + (v as Field) + (w as Field) + f(k);
    let (v, w, k) = a128.mul_div_or(b128, 0);
    wide = wide * 3 + (v as Field) + (w as Field) + f(k);
    let (v, w, k) = a128.mul_div_or(1050000, 30000);
    wide = wide * 3 + (v as Field) + (w as Field) + f(k);
    // Field-domain width families and the field itself
    let mut width: Field = 0;
    for i in 0..6 {
        let (a, b) = (xs[i], xs[(i + 1) % 6]);
        width = mix(width, width_ops::<8>(a, b));
        width = mix(width, width_ops::<64>(a, b));
        width = mix(width, width_ops::<126>(a, b));
        let (v, k) = inverse_or(a);
        width = mixk(width, v, k);
        let (v, k) = field_div_or(a, b);
        width = mixk(width, v, k);
    }
    // TotalArith, Saturating and TotalMulDiv on array pairs (zero divisors,
    // overflow, MIN / -1), TotalSigned and abs
    let mut uints: Field = 0;
    let mut signed: Field = 0;
    for i in 0..4 {
        let j = (i + 1) % 4;
        let l = (i + 2) % 4;
        uints = mix(uints, arith_ops(u8s[i], u8s[j]));
        uints = mix(uints, sat_ops(u8s[i], u8s[j]));
        uints = mix(uints, mul_div_ops(u8s[i], u8s[j], u8s[l]));
        uints = mix(uints, unsigned_ops(u8s[i], u8s[j]));
        uints = mix(uints, arith_ops(u16s[i], u16s[j]));
        uints = mix(uints, sat_ops(u16s[i], u16s[j]));
        uints = mix(uints, mul_div_ops(u16s[i], u16s[j], u16s[l]));
        uints = mix(uints, unsigned_ops(u16s[i], u16s[j]));
        uints = mix(uints, arith_ops(u32s[i], u32s[j]));
        uints = mix(uints, sat_ops(u32s[i], u32s[j]));
        uints = mix(uints, mul_div_ops(u32s[i], u32s[j], u32s[l]));
        uints = mix(uints, unsigned_ops(u32s[i], u32s[j]));
        uints = mix(uints, arith_ops(u64s[i], u64s[j]));
        uints = mix(uints, sat_ops(u64s[i], u64s[j]));
        uints = mix(uints, mul_div_ops(u64s[i], u64s[j], u64s[l]));
        uints = mix(uints, unsigned_ops(u64s[i], u64s[j]));
        uints = mix(uints, arith_ops(u128s[i], u128s[j]));
        uints = mix(uints, sat_ops(u128s[i], u128s[j]));
        uints = mix(uints, mul_div_ops(u128s[i], u128s[j], u128s[l]));
        uints = mix(uints, unsigned_ops(u128s[i], u128s[j]));
        signed = mix(signed, arith_ops(i8s[i], i8s[j]));
        signed = mix(signed, signed_ops(i8s[i]));
        signed = mix(signed, unsigned_abs_i8(i8s[i]).to_f());
        signed = mix(signed, mul_div_ops(i8s[i], i8s[j], i8s[l]));
        signed = mix(signed, arith_ops(i16s[i], i16s[j]));
        signed = mix(signed, signed_ops(i16s[i]));
        signed = mix(signed, unsigned_abs_i16(i16s[i]).to_f());
        signed = mix(signed, mul_div_ops(i16s[i], i16s[j], i16s[l]));
        signed = mix(signed, arith_ops(i32s[i], i32s[j]));
        signed = mix(signed, signed_ops(i32s[i]));
        signed = mix(signed, unsigned_abs_i32(i32s[i]).to_f());
        signed = mix(signed, mul_div_ops(i32s[i], i32s[j], i32s[l]));
        signed = mix(signed, arith_ops(i64s[i], i64s[j]));
        signed = mix(signed, signed_ops(i64s[i]));
        signed = mix(signed, unsigned_abs_i64(i64s[i]).to_f());
        signed = mix(signed, mul_div_ops(i64s[i], i64s[j], i64s[l]));
    }
    // Shifts and rotates: in-range, zero and oversized shift counts
    let mut shifts: Field = 0;
    for i in 0..6 {
        let s = sh[i % 4];
        shifts = mix(shifts, shift_ops::<8>(xs[i], s));
        shifts = mix(shifts, shift_ops::<64>(xs[i], s));
        shifts = mix(shifts, shift_ops::<126>(xs[i], s));
        shifts = mix(shifts, shift_ops::<127>(xs[i], s));
        shifts = mix(shifts, shift_ops::<128>(xs[i], s));
        shifts = mix(shifts, shift_ops::<128>(xs[i], shw[i % 4] as Field));
    }
    // TotalShift: amounts 0, 1, 3, 7, 127, 128 and past every width
    for i in 0..4 {
        for j in 0..4 {
            shifts = mix(shifts, typed_shift_ops(u8s[i], u8s[j]));
            shifts = mix(shifts, typed_shift_ops(u8s[i], shw[j] as u8));
            shifts = mix(shifts, typed_shift_ops(u16s[i], u16s[j]));
            shifts = mix(shifts, typed_shift_ops(u32s[i], shw[j] as u32));
            shifts = mix(shifts, typed_shift_ops(u64s[i], u64s[j]));
            shifts = mix(shifts, typed_shift_ops(u64s[i], shw[j] as u64));
            shifts = mix(shifts, typed_shift_ops(u128s[i], u128s[j]));
            shifts = mix(shifts, typed_shift_ops(u128s[i], shw[j]));
        }
    }
    // Bits and bytes, truncate_or, the signed Field forms, narrow_or
    let mut enc: Field = 0;
    for i in 0..6 {
        let x = xs[i];
        enc = mix(enc, trunc_ops::<8>(x));
        enc = mix(enc, trunc_ops::<64>(x));
        enc = mix(enc, trunc_ops::<127>(x));
        enc = mix(enc, trunc_ops::<128>(x));
        enc = mix(enc, bit_ops::<8, 1>(x));
        enc = mix(enc, bit_ops::<64, 8>(x));
        enc = mix(enc, bit_ops::<128, 16>(x));
        let (b, k) = bool_or(x);
        enc = mixk(mix(enc, f(b)), 0, k);
        enc = mix(enc, f(total::convert::sgn0(x)));
        let le = to_le_bits_total(x);
        let be = to_be_bits_total(x);
        let lb = to_le_bytes_total(x);
        let bb = to_be_bytes_total(x);
        enc = mix(
            enc,
            fold_arr(le) + fold_arr(be) + fold_arr(lb) + fold_arr(bb),
        );
        let (r1, k1) = from_le_bits_or(le);
        let (r2, k2) = from_be_bits_or(be);
        let (r3, k3) = from_le_bytes_or(lb);
        let (r4, k4) = from_be_bytes_or(bb);
        enc = mixk(mixk(mixk(mixk(enc, r1, k1), r2, k2), r3, k3), r4, k4);
        let (v1, k1) = to_i8_from_signed_or(x);
        let (v2, k2) = to_i16_from_signed_or(x);
        let (v3, k3) = to_i32_from_signed_or(x);
        let (v4, k4) = to_i64_from_signed_or(x);
        enc = mixk(
            mixk(mixk(mixk(enc, v1.to_f(), k1), v2.to_f(), k2), v3.to_f(), k3),
            v4.to_f(),
            k4,
        );
        enc = mix(enc, from_i8_signed(v1));
        enc = mix(enc, from_i16_signed(v2));
        enc = mix(enc, from_i32_signed(v3));
        enc = mix(enc, from_i64_signed(v4));
    }
    let nc_bits = [nc[0] == 255; 254];
    let (r1, k1) = from_le_bytes_or(nc);
    let (r2, k2) = from_be_bytes_or(nc);
    let (r3, k3) = from_le_bits_or(nc_bits);
    let (r4, k4) = from_be_bits_or(nc_bits);
    enc = mixk(mixk(mixk(mixk(enc, r1, k1), r2, k2), r3, k3), r4, k4);
    enc = mix(enc, narrow::<u16, u8>(u16s[3]));
    enc = mix(enc, narrow::<u32, u8>(u32s[3]));
    enc = mix(enc, narrow::<u32, u16>(u32s[3]));
    enc = mix(enc, narrow::<u64, u8>(u64s[3]));
    enc = mix(enc, narrow::<u64, u16>(u64s[3]));
    enc = mix(enc, narrow::<u64, u32>(u64s[3]));
    enc = mix(enc, narrow::<u128, u8>(u128s[3]));
    enc = mix(enc, narrow::<u128, u16>(u128s[3]));
    enc = mix(enc, narrow::<u128, u32>(u128s[3]));
    enc = mix(enc, narrow::<u128, u64>(u128s[3]));
    enc = mix(enc, narrow::<i16, i8>(i16s[0]));
    enc = mix(enc, narrow::<i32, i8>(i32s[0]));
    enc = mix(enc, narrow::<i32, i16>(i32s[0]));
    enc = mix(enc, narrow::<i64, i8>(i64s[0]));
    enc = mix(enc, narrow::<i64, i16>(i64s[0]));
    enc = mix(enc, narrow::<i64, i32>(i64s[0]));
    enc = mix(enc, narrow::<i8, u8>(i8s[1]));
    enc = mix(enc, narrow::<u8, i8>(u8s[3]));
    enc = mix(enc, narrow::<i16, u16>(i16s[1]));
    enc = mix(enc, narrow::<u16, i16>(u16s[3]));
    enc = mix(enc, narrow::<i32, u32>(i32s[1]));
    enc = mix(enc, narrow::<u32, i32>(u32s[3]));
    enc = mix(enc, narrow::<i64, u64>(i64s[1]));
    enc = mix(enc, narrow::<u64, i64>(u64s[3]));
    // Comparisons
    let mut cmps: Field = 0;
    for i in 0..6 {
        let (a, b, c) = (xs[i], xs[(i + 1) % 6], xs[(i + 2) % 6]);
        cmps = mix(cmps, cmp_ops::<8>(a, b));
        cmps = mix(cmps, cmp_ops::<64>(a, b));
        cmps = mix(cmps, cmp_ops::<128>(a, b));
        cmps = mix(cmps, ord_ops(a, b, c));
        cmps = mix(cmps, f(total::is_zero(a)));
        cmps = mix(cmps, f(total::cmp::eq(a, b)));
        let (lo, hi) = total::core::limbs(a);
        cmps = mix(mix(cmps, lo), hi);
        cmps = mix(
            cmps,
            f(total::range::fits_u1(a)) + f(total::range::fits_u8(a)),
        );
        cmps = mix(
            cmps,
            f(total::range::fits_u16(a)) + f(total::range::fits_u32(a)),
        );
        cmps = mix(
            cmps,
            f(total::range::fits_u64(a)) + f(total::range::fits_u128(a)),
        );
    }
    for i in 0..4 {
        let (j, l) = ((i + 1) % 4, (i + 2) % 4);
        cmps = mix(cmps, ord_ops(u8s[i] == 0, u8s[j] == 0, u8s[l] == 0));
        cmps = mix(cmps, ord_ops(u8s[i], u8s[j], u8s[l]));
        cmps = mix(cmps, ord_ops(u16s[i], u16s[j], u16s[l]));
        cmps = mix(cmps, ord_ops(u32s[i], u32s[j], u32s[l]));
        cmps = mix(cmps, ord_ops(u64s[i], u64s[j], u64s[l]));
        cmps = mix(cmps, ord_ops(u128s[i], u128s[j], u128s[l]));
        cmps = mix(cmps, ord_ops(i8s[i], i8s[j], i8s[l]));
        cmps = mix(cmps, ord_ops(i16s[i], i16s[j], i16s[l]));
        cmps = mix(cmps, ord_ops(i32s[i], i32s[j], i32s[l]));
        cmps = mix(cmps, ord_ops(i64s[i], i64s[j], i64s[l]));
    }
    // Collections: runtime indices and lengths from xs (in and out of range)
    let mut colls: Field = 0;
    let arr4 = [xs[1], xs[4], xs[5], xs[0]];
    for i in 0..6 {
        let x = xs[i];
        let (v, k) = sum_or::<4, 8>([xs[1], xs[4], xs[5], x]);
        colls = mixk(colls, v, k);
        let (v, k) = sum_or::<4, 64>(arr4);
        colls = mixk(colls, v, k);
        let (v, k) = sum_wide_or::<4, 127>([xs[0], xs[2], x, xs[5]]);
        colls = mixk(colls, v, k);
        let (s1, k1) = is_sorted_or::<4, 16>(sh);
        let (s2, k2) = is_sorted_or::<4, 64>([xs[4], xs[5], x, xs[0]]);
        colls = mix(colls, f(s1) * 8 + f(k1) * 4 + f(s2) * 2 + f(k2));
        let (v, k) = index_or(arr4, x);
        colls = mixk(colls, v, k);
        let (a, k) = set_or(arr4, x, 9);
        colls = mixk(colls, fold_arr(a), k);
        let (a, k): ([Field; 2], bool) = subarray_or(arr4, x);
        colls = mixk(colls, fold_arr(a), k);
        let (a, k) = index_flags_or::<4>(x);
        colls = mixk(colls, fold_arr(a), k);
        let (a, k) = prefix_mask_or::<4>(x);
        colls = mixk(colls, fold_arr(a), k);
        let (v, k) = first_true_or([x == 0, x == 250, x == 1, false]);
        colls = mixk(colls, v, k);
        let (v, k) = first_index_of_or(arr4, x);
        colls = mixk(colls, v, k);
        let (v, k) = min_of_or::<4, 16>([xs[4], x, xs[5], xs[0]]);
        colls = mixk(colls, v, k);
        let (v, k) = max_of_or::<4, 64>([xs[4], x, xs[5], xs[0]]);
        colls = mixk(colls, v, k);
        let (a, k) = sort_or::<4, 64>([xs[4], x, xs[5], xs[0]]);
        colls = mixk(colls, fold_arr(a), k);
    }
    // BoundedVec forms: lengths 0, 2, 4 (full) and 9 (past the capacity)
    for i in 0..4 {
        let base = [xs[i], xs[(i + 1) % 6], xs[(i + 2) % 6], xs[(i + 3) % 6]];
        colls = mix(
            colls,
            bounded_vec_ops(base, lens[i], lens[(i + 1) % 4], lens[(i + 2) % 4], xs[5]),
        );
    }
    // ec: decode every point shape, then the group operations
    let mut pts = [Point::infinity(); 5];
    let mut ecs: Field = 0;
    for i in 0..5 {
        let (p, k) = ec::decode_or(ex[i], ey[i], einf[i]);
        pts[i] = p;
        ecs = mixk(fold_point(ecs, p), 0, k);
        let (q, k) = ec::decode_xy_or(ex[i], ey[i]);
        ecs = mixk(fold_point(ecs, q), 0, k);
        ecs = mix(
            ecs,
            f(ec::on_curve_flag(ex[i], ey[i])) * 2 + f(ec::is_well_formed(p)),
        );
    }
    for i in 0..5 {
        let (p, q) = (pts[i], pts[(i + 1) % 5]);
        ecs = fold_point(ecs, ec::add(p, q));
        ecs = fold_point(ecs, ec::sub(p, q));
        ecs = fold_point(ecs, ec::double(p));
        let (m, k) = ec::mul_or::<16>(p, xs[(i + 1) % 6]);
        ecs = mixk(fold_point(ecs, m), 0, k);
        let (l, h, k) = ec::scalar_limbs_or(xs[(i + 1) % 6], xs[(i + 2) % 6]);
        ecs = mixk(mix(mix(ecs, l), h), 0, k);
    }
    let (m, k) = ec::mul_or::<254>(pts[0], xs[0]);
    ecs = mixk(fold_point(ecs, m), 0, k);
    let (m, k) = ec::mul_limbs_or(pts[0], xs[1], xs[4]);
    ecs = mixk(fold_point(ecs, m), 0, k);
    let (m, k) = ec::msm_or::<2>([pts[0], pts[1]], [xs[1], xs[2]], [xs[4], xs[5]]);
    ecs = mixk(fold_point(ecs, m), 0, k);
    let (m, k) = ec::msm_or::<2>([pts[2], pts[3]], [xs[3], xs[0]], [xs[4], xs[3]]);
    ecs = mixk(fold_point(ecs, m), 0, k);
    // schnorr_verify: msm_or on [G, key], then Poseidon2
    let v0 = schnorr_verify(pts[0].x, pts[0].y, [xs[1], xs[4], xs[5], xs[4]], xs[0]);
    let v1 = schnorr_verify(pts[1].x, pts[1].y, [xs[2], xs[5], xs[1], xs[4]], xs[3]);
    ecs = mix(ecs, f(v0) * 2 + f(v1));
    // secp: the generator of secp256k1 (on secp256k1, off secp256r1) and
    // non-canonical coordinates
    ecs = mix(
        ecs,
        f(secp256k1_on_curve(gx, gy)) * 8
            + f(secp256r1_on_curve(gx, gy)) * 4
            + f(secp256k1_on_curve(nc, gy)) * 2
            + f(secp256r1_on_curve(gx, nc)),
    );
    // encode: canonical flags, chunks, fixed-width bytes, byte strings
    let mut encs: Field = 0;
    for i in 0..6 {
        let x = xs[i];
        let lb = to_le_bytes_total(x);
        let lbits = to_le_bits_total(x);
        encs = mix(
            encs,
            f(encode::canonical_le_bytes_flag(lb))
                + f(encode::canonical_be_bytes_flag(encode::reverse32(lb))) * 2
                + f(encode::canonical_le_bits_flag(lbits)) * 4
                + f(encode::canonical_be_bits_flag(encode::reverse(lbits))) * 8,
        );
        let (a, k) = encode::chunk_to_le_bytes_or(x);
        let (b, l) = encode::chunk_to_be_bytes_or(x);
        encs = mixk(mixk(encs, fold_arr(a), k), fold_arr(b), l);
        let (fa, k) = encode::fields_to_bytes_be_or([xs[1], xs[4], x]);
        let (fb, l) = encode::fields_to_bytes_le_or([xs[0], x]);
        encs = mixk(mixk(encs, fold_arr(fa), k), fold_arr(fb), l);
    }
    let flags = encode::canonical_le_bytes_flag(nc) as Field
        + (encode::canonical_be_bytes_flag(nc) as Field)
        + (encode::canonical_le_bits_flag(nc_bits) as Field)
        + (encode::canonical_be_bits_flag(nc_bits) as Field);
    encs = mix(encs, flags);
    let mut nc31 = [0; 31];
    for i in 0..31 {
        nc31[i] = nc[i];
    }
    encs = mix(encs, fold_arr(encode::bytes_to_fields_be(nc31)));
    encs = mix(encs, fold_arr(encode::bytes_to_fields_le(nc)));
    encs = mix(
        encs,
        encode::u16_from_be_bytes(encode::u16_to_be_bytes(a16)) as Field,
    );
    encs = mix(
        encs,
        encode::u16_from_le_bytes(encode::u16_to_le_bytes(a16)) as Field,
    );
    encs = mix(
        encs,
        encode::u32_from_be_bytes(encode::u32_to_be_bytes(a32)) as Field,
    );
    encs = mix(
        encs,
        encode::u32_from_le_bytes(encode::u32_to_le_bytes(a32)) as Field,
    );
    encs = mix(
        encs,
        encode::u64_from_be_bytes(encode::u64_to_be_bytes(a64)) as Field,
    );
    encs = mix(
        encs,
        encode::u64_from_le_bytes(encode::u64_to_le_bytes(a64)) as Field,
    );
    encs = mix(
        encs,
        encode::u128_from_be_bytes(encode::u128_to_be_bytes(a128)) as Field,
    );
    encs = mix(
        encs,
        encode::u128_from_le_bytes(encode::u128_to_le_bytes(a128)) as Field,
    );
    let storage = encode::u64_to_be_bytes(a64);
    for i in 0..6 {
        let (n, kn) = to_u32_or(xs[i]);
        let (bv, k) = from_prefix_or(storage, n);
        encs = mixk(mix(encs, fold_arr(bv.storage())), bv.len() as Field, k & kn);
        encs = mix(encs, f(bv.is_valid()));
        let (j, kj) = to_u32_or(xs[(i + 1) % 6]);
        let (v, l) = bv.get_or(j);
        encs = mixk(encs, v as Field, l & kj);
    }
    // hash wrappers: fixed, separated, runtime-length, Sponge
    let mut hashes: Field = 0;
    let h3 = [xs[0], xs[1], xs[2]];
    hashes = mix(hashes, p2_hash(h3));
    hashes = mix(hashes, p2_hash_sep(h3, xs[3]));
    for i in 0..6 {
        let (h, k) = p2_hash_var_or([xs[0], xs[1], xs[2], xs[3]], xs[i]);
        hashes = mixk(hashes, h, k);
        let (h, k) = p2_hash_sep_var_or([xs[0], xs[1], xs[2], xs[3]], xs[i], xs[(i + 1) % 6]);
        hashes = mixk(hashes, h, k);
    }
    let s = Sponge::new(xs[5]).absorb(xs[1]).absorb(xs[2]);
    hashes = mix(hashes, s.squeeze());
    for i in 0..6 {
        let (r, k) = merkle::merkle_root_or(xs[0], xs[i], [xs[1], xs[2], xs[3]]);
        hashes = mixk(hashes, r, k);
        hashes = mix(
            hashes,
            f(merkle::is_member(xs[0], xs[i], [xs[1], xs[2], xs[3]], r)),
        );
    }
    let s2 = s.absorb(xs[3]).absorb_array([xs[4], xs[0]]);
    hashes = mix(hashes, s2.squeeze());
    [
        range, conv, arith, bits, typed, wide, xs[0], width, uints, signed, shifts, enc, cmps,
        colls, ecs, encs, hashes,
    ]
}
