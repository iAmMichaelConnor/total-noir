// arith: the Field-domain entries at several widths, boundary widths
// included, and the unsigned trait methods on u8..u128.
use crate::arith::{
    add_or, div_or, div_rem_or, field_div_or, inverse_or, mod_or, mul_div_or, mul_div_to_or,
    mul_div_wide_or, mul_div_wide_to_or, mul_or, neg_or, pow_or, Saturating, saturating_add_or,
    saturating_mul_or, saturating_sub_or, sqrt_canonical_or, sqrt_or, sub_or, TotalArith,
    TotalMulDiv, TotalUnsigned, wrapping_add_or, wrapping_mul_or, wrapping_neg_or, wrapping_sub_or,
};
use crate::core::is_zero;
use super::{bit, div_wide, fits, in_or_zero, low_bits, mul_wide, Num, or_zero, pick_u, pow2, shape};

// ---------------------------------------------------------------------
// Models
// ---------------------------------------------------------------------

/// add_or, wrapping_add_or, saturating_add_or, sub_or, wrapping_sub_or,
/// saturating_sub_or on n bits (n <= 128, so every sum is exact).
unconstrained fn add_sub_model(a: Field, b: Field, n: u32) -> [(Field, bool); 6] {
    let ok_in = fits(a, n) & fits(b, n);
    let (a1, b1) = (in_or_zero(a, n), in_or_zero(b, n));
    let m = pow2(n);
    let s = a1 + b1;
    let s_fits = s.lt(m);
    let no_borrow = !a1.lt(b1);
    [
        or_zero(ok_in & s_fits, s),
        (if s_fits { s } else { s - m }, ok_in),
        (if s_fits { s } else { m - 1 }, ok_in),
        or_zero(ok_in & no_borrow, a1 - b1),
        (if no_borrow { a1 - b1 } else { a1 + m - b1 }, ok_in),
        (if no_borrow { a1 - b1 } else { 0 }, ok_in),
    ]
}

/// The low n bits of hi*2^128 + lo, and whether nothing lies above them
/// (n <= 128).
unconstrained fn wide_low(hi: u128, lo: u128, n: u32) -> (Field, bool) {
    let low = low_bits(lo as Field, n);
    (low, (hi == 0) & (low == lo as Field))
}

/// mul_or, wrapping_mul_or, saturating_mul_or on n bits.
unconstrained fn mul_model(a: Field, b: Field, n: u32) -> [(Field, bool); 3] {
    let ok_in = fits(a, n) & fits(b, n);
    let (hi, lo) = mul_wide(in_or_zero(a, n) as u128, in_or_zero(b, n) as u128);
    let (low, small) = wide_low(hi, lo, n);
    [or_zero(ok_in & small, low), (low, ok_in), (if small { low } else { pow2(n) - 1 }, ok_in)]
}

/// div_rem_or on n bits: (q, r, ok).
unconstrained fn div_model(a: Field, b: Field, n: u32) -> (Field, Field, bool) {
    if fits(a, n) & fits(b, n) & (b != 0) {
        let (x, y) = (a as u128, b as u128);
        ((x / y) as Field, (x % y) as Field, true)
    } else {
        (0, 0, false)
    }
}

/// b^e with b < 2^n, and whether it is below 2^n. For b >= 2 the power
/// reaches 2^n by e = n, so at most n products are formed.
unconstrained fn pow_below(b: u128, e: Field, n: u32) -> (Field, bool) {
    if b <= 1 {
        (if (b == 0) & (e != 0) { 0 } else { 1 }, true)
    } else if !e.lt(n as Field) {
        (0, false)
    } else {
        let mut r: u128 = 1;
        let mut ok = true;
        for _ in 0..(e as u32) {
            let (hi, lo) = mul_wide(r, b);
            let (low, small) = wide_low(hi, lo, n);
            ok = ok & small;
            r = low as u128;
        }
        or_zero(ok, r as Field)
    }
}

/// pow_or::<n, ebits>.
unconstrained fn pow_model(b: Field, e: Field, n: u32, ebits: u32) -> (Field, bool) {
    if fits(b, n) & fits(e, ebits) {
        pow_below(b as u128, e, n)
    } else {
        (0, false)
    }
}

/// floor(a*b / d) for a, b, d below 2^128 and d != 0: (q_hi, q_lo, r).
unconstrained fn mul_div_wide_ref(a: Field, b: Field, d: Field) -> (u128, u128, u128) {
    let (hi, lo) = mul_wide(a as u128, b as u128);
    div_wide(hi, lo, d as u128)
}

/// mul_div_to_or::<n, m> (q below 2^253 here: n <= 84).
unconstrained fn mul_div_model(
    a: Field,
    b: Field,
    d: Field,
    n: u32,
    m: u32,
) -> (Field, Field, bool) {
    if fits(a, n) & fits(b, n) & fits(d, n) & (d != 0) {
        let (qh, ql, r) = mul_div_wide_ref(a, b, d);
        let q = (qh as Field) * pow2(128) + ql as Field;
        if fits(q, m) {
            (q, r as Field, true)
        } else {
            (0, 0, false)
        }
    } else {
        (0, 0, false)
    }
}

/// mul_div_wide_or::<n>: (q_lo, q_hi, r, ok).
unconstrained fn mul_div_wide_model(
    a: Field,
    b: Field,
    d: Field,
    n: u32,
) -> (Field, Field, Field, bool) {
    if fits(a, n) & fits(b, n) & fits(d, n) & (d != 0) {
        let (qh, ql, r) = mul_div_wide_ref(a, b, d);
        (ql as Field, qh as Field, r as Field, true)
    } else {
        (0, 0, 0, false)
    }
}

/// mul_div_wide_to_or::<m>: the 128-bit operation with q below 2^m.
unconstrained fn mul_div_wide_to_model(
    a: Field,
    b: Field,
    d: Field,
    m: u32,
) -> (Field, Field, bool) {
    let (ql, qh, r, ok) = mul_div_wide_model(a, b, d, 128);
    // qh < 2^128, so qh < 2^(m - 128) is the test for m > 128.
    let q_fits = if m < 128 {
        (qh == 0) & fits(ql, m)
    } else {
        fits(qh, m - 128)
    };
    if ok & q_fits {
        (ql + qh * pow2(128), r, true)
    } else {
        (0, 0, false)
    }
}

/// A divisor that puts floor(a*b / d) at the m-bit bound K = 2^m - 1,
/// where a quotient or its ceiling crosses it: floor(a*b / K) gives a
/// quotient of K or more, one more gives a quotient below K. Kept in
/// [1, 2^n - 1] (a, b below 2^n <= 2^128, 1 <= m <= 128).
unconstrained fn edge_divisor(a: Field, b: Field, m: u32, n: u32, below: bool) -> Field {
    let (hi, lo) = mul_wide(a as u128, b as u128);
    let (qh, ql, _) = div_wide(hi, lo, (pow2(m) - 1) as u128);
    let d = (qh as Field) * pow2(128) + ql as Field + below as Field;
    if d == 0 {
        1
    } else if fits(d, n) {
        d
    } else {
        pow2(n) - 1
    }
}

/// The divisor input: one time in four (with a, b in range and m <= 128)
/// an edge divisor of a and b, else d from the shaper.
unconstrained fn shape_divisor(
    edge: u8,
    sd: u8,
    d: Field,
    a: Field,
    b: Field,
    m: u32,
    n: u32,
) -> Field {
    if (edge % 8 < 2) & fits(a, n) & fits(b, n) & (m <= 128) {
        edge_divisor(a, b, m, n, edge % 8 == 1)
    } else {
        shape(sd, d, n)
    }
}

// ---------------------------------------------------------------------
// Field domain
// ---------------------------------------------------------------------

fn check_add_sub<let N: u32>(sa: u8, a: Field, sb: u8, b: Field) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b) = unsafe { (shape(sa, a, N), shape(sb, b, N)) };
    // Safety: reference model, compared below.
    let m = unsafe { add_sub_model(a, b, N) };
    assert_eq(add_or::<N>(a, b), m[0]);
    assert_eq(wrapping_add_or::<N>(a, b), m[1]);
    assert_eq(saturating_add_or::<N>(a, b), m[2]);
    assert_eq(sub_or::<N>(a, b), m[3]);
    assert_eq(wrapping_sub_or::<N>(a, b), m[4]);
    assert_eq(saturating_sub_or::<N>(a, b), m[5]);
}

#[test]
fn add_sub_field(sa: u8, a: Field, sb: u8, b: Field) {
    check_add_sub::<1>(sa, a, sb, b);
    check_add_sub::<8>(sa, a, sb, b);
    check_add_sub::<64>(sa, a, sb, b);
    check_add_sub::<127>(sa, a, sb, b);
    check_add_sub::<128>(sa, a, sb, b);
}

fn check_mul<let N: u32>(sa: u8, a: Field, sb: u8, b: Field) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b) = unsafe { (shape(sa, a, N), shape(sb, b, N)) };
    // Safety: reference model, compared below.
    let m = unsafe { mul_model(a, b, N) };
    assert_eq(mul_or::<N>(a, b), m[0]);
    assert_eq(wrapping_mul_or::<N>(a, b), m[1]);
    assert_eq(saturating_mul_or::<N>(a, b), m[2]);
}

#[test]
fn mul_field(sa: u8, a: Field, sb: u8, b: Field) {
    check_mul::<1>(sa, a, sb, b);
    check_mul::<8>(sa, a, sb, b);
    check_mul::<64>(sa, a, sb, b);
    check_mul::<126>(sa, a, sb, b);
    check_mul::<127>(sa, a, sb, b);
    check_mul::<128>(sa, a, sb, b);
}

fn check_div<let N: u32>(sa: u8, a: Field, sb: u8, b: Field) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b) = unsafe { (shape(sa, a, N), shape(sb, b, N)) };
    // Safety: reference model, compared below.
    let (q, r, ok) = unsafe { div_model(a, b, N) };
    assert_eq(div_rem_or::<N>(a, b), (q, r, ok));
    assert_eq(div_or::<N>(a, b), (q, ok));
    assert_eq(mod_or::<N>(a, b), (r, ok));
}

#[test]
fn div_field(sa: u8, a: Field, sb: u8, b: Field) {
    check_div::<1>(sa, a, sb, b);
    check_div::<8>(sa, a, sb, b);
    check_div::<64>(sa, a, sb, b);
    check_div::<126>(sa, a, sb, b);
    check_div::<127>(sa, a, sb, b);
    check_div::<128>(sa, a, sb, b);
}

fn check_neg<let N: u32>(sa: u8, a: Field) {
    // Safety: input selection; the value reaches the library as a witness.
    let a = unsafe { shape(sa, a, N) };
    // Safety: reference model, compared below.
    let (ok, a1, m) = unsafe { (fits(a, N), in_or_zero(a, N), pow2(N)) };
    assert_eq(neg_or::<N>(a), (0, ok & (a1 == 0)));
    assert_eq(wrapping_neg_or::<N>(a), (if a1 == 0 { 0 } else { m - a1 }, ok));
}

fn check_pow<let N: u32, let E: u32>(sa: u8, a: Field, se: u8, e: Field) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, e) = unsafe { (shape(sa, a, N), shape(se, e, E)) };
    // Safety: reference model, compared below.
    let want = unsafe { pow_model(a, e, N, E) };
    assert_eq(pow_or::<N, E>(a, e), want);
}

#[test]
fn neg_pow_field(sa: u8, a: Field, se: u8, e: Field) {
    check_neg::<1>(sa, a);
    check_neg::<64>(sa, a);
    check_neg::<127>(sa, a);
    check_pow::<1, 1>(sa, a, se, e);
    check_pow::<8, 1>(sa, a, se, e);
    check_pow::<8, 4>(sa, a, se, e);
    check_pow::<16, 126>(sa, a, se, e);
    check_pow::<64, 7>(sa, a, se, e);
    check_pow::<127, 8>(sa, a, se, e);
    check_pow::<128, 8>(sa, a, se, e);
}

fn check_mul_div<let N: u32, let M: u32>(
    sa: u8,
    a: Field,
    sb: u8,
    b: Field,
    sd: u8,
    d: Field,
    edge: u8,
) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b) = unsafe { (shape(sa, a, N), shape(sb, b, N)) };
    // Safety: input selection; the value reaches the library as a witness.
    let d = unsafe { shape_divisor(edge, sd, d, a, b, M, N) };
    // Safety: reference model, compared below.
    let (want, want_to) =
        unsafe { (mul_div_model(a, b, d, N, 2 * N), mul_div_model(a, b, d, N, M)) };
    assert_eq(mul_div_or::<N>(a, b, d), want);
    assert_eq(mul_div_to_or::<N, M>(a, b, d), want_to);
}

#[test]
fn mul_div_field(sa: u8, a: Field, sb: u8, b: Field, sd: u8, d: Field, edge: u8) {
    check_mul_div::<1, 1>(sa, a, sb, b, sd, d, edge);
    check_mul_div::<8, 8>(sa, a, sb, b, sd, d, edge);
    check_mul_div::<64, 1>(sa, a, sb, b, sd, d, edge);
    check_mul_div::<64, 64>(sa, a, sb, b, sd, d, edge);
    check_mul_div::<84, 100>(sa, a, sb, b, sd, d, edge);
    check_mul_div::<84, 168>(sa, a, sb, b, sd, d, edge);
}

fn check_mul_div_wide<let N: u32>(sa: u8, a: Field, sb: u8, b: Field, sd: u8, d: Field) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b, d) = unsafe { (shape(sa, a, N), shape(sb, b, N), shape(sd, d, N)) };
    // Safety: reference model, compared below.
    let want = unsafe { mul_div_wide_model(a, b, d, N) };
    assert_eq(mul_div_wide_or::<N>(a, b, d), want);
}

fn check_mul_div_wide_to<let M: u32>(
    sa: u8,
    a: Field,
    sb: u8,
    b: Field,
    sd: u8,
    d: Field,
    edge: u8,
) {
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b) = unsafe { (shape(sa, a, 128), shape(sb, b, 128)) };
    // Safety: input selection; the value reaches the library as a witness.
    let d = unsafe { shape_divisor(edge, sd, d, a, b, M, 128) };
    // Safety: reference model, compared below.
    let want = unsafe { mul_div_wide_to_model(a, b, d, M) };
    assert_eq(mul_div_wide_to_or::<M>(a, b, d), want);
}

#[test]
fn mul_div_wide_field(sa: u8, a: Field, sb: u8, b: Field, sd: u8, d: Field, edge: u8) {
    check_mul_div_wide::<85>(sa, a, sb, b, sd, d);
    check_mul_div_wide::<124>(sa, a, sb, b, sd, d);
    check_mul_div_wide::<125>(sa, a, sb, b, sd, d);
    check_mul_div_wide::<128>(sa, a, sb, b, sd, d);
    check_mul_div_wide_to::<1>(sa, a, sb, b, sd, d, edge);
    check_mul_div_wide_to::<127>(sa, a, sb, b, sd, d, edge);
    check_mul_div_wide_to::<128>(sa, a, sb, b, sd, d, edge);
    check_mul_div_wide_to::<129>(sa, a, sb, b, sd, d, edge);
    check_mul_div_wide_to::<253>(sa, a, sb, b, sd, d, edge);
}

// ---------------------------------------------------------------------
// The field itself
// ---------------------------------------------------------------------

/// Whether x is a square in the field (0 included), by Euler's criterion:
/// x^((p - 1)/2) is 1 for a nonzero square and p - 1 for a non-square.
unconstrained fn is_square(x: Field) -> bool {
    let e = (0 - 1) / 2;
    let mut r: Field = 1;
    for i in 0..254 {
        r = r * r;
        if bit(e, 253 - i) {
            r = r * x;
        }
    }
    r != 0 - 1
}

/// Field inverse, division and square roots. The roots are checked by
/// their defining property: r*r = x, and the canonical root is the even
/// one.
#[test]
fn field_ops(sx: u8, x: Field, y: Field) {
    // 0, 1, p - 1, a square, or x itself.
    let k = sx % 5;
    let x = if k == 0 {
        0
    } else if k == 1 {
        1
    } else if k == 2 {
        0 - 1
    } else if k == 3 {
        y * y
    } else {
        x
    };
    // Safety: reference model, compared below.
    let (inv, square) = unsafe { (if x == 0 { 0 } else { 1 / x }, is_square(x)) };
    assert_eq(is_zero(x), x == 0);
    assert_eq(inverse_or(x), (inv, x != 0));
    assert_eq(field_div_or(y, x), (y * inv, x != 0));
    let (r, ok) = sqrt_or(x);
    assert_eq(ok, square);
    assert_eq(r * r, if ok { x } else { 0 });
    let (c, cok) = sqrt_canonical_or(x);
    // Safety: reference model, compared below.
    let odd = unsafe { bit(c, 0) };
    assert_eq((c * c, cok, odd), (if square { x } else { 0 }, square, false));
}

// ---------------------------------------------------------------------
// Native unsigned types
// ---------------------------------------------------------------------

/// TotalArith and Saturating on n-bit unsigned a, b: add, sub, mul,
/// saturating add, sub, mul as (value, ok) (ok = true for the saturating
/// forms), then div_rem as (q, r, ok).
unconstrained fn unsigned_model(
    a: Field,
    b: Field,
    n: u32,
) -> ([(Field, bool); 6], (Field, Field, bool)) {
    let m = pow2(n);
    let s = a + b;
    let (hi, lo) = mul_wide(a as u128, b as u128);
    let (low, small) = wide_low(hi, lo, n);
    let no_borrow = !a.lt(b);
    (
        [
            or_zero(s.lt(m), s),
            or_zero(no_borrow, a - b),
            or_zero(small, low),
            (if s.lt(m) { s } else { m - 1 }, true),
            (if no_borrow { a - b } else { 0 }, true),
            (if small { low } else { m - 1 }, true),
        ], div_model(a, b, n),
    )
}

/// TotalUnsigned on n-bit a, b: widening_mul (lo, hi), isqrt(a),
/// abs_diff, div_ceil_or.
unconstrained fn unsigned_more_model(
    a: Field,
    b: Field,
    n: u32,
) -> ((Field, Field), Field, Field, (Field, bool)) {
    let (hi, lo) = mul_wide(a as u128, b as u128);
    let lo_n = low_bits(lo as Field, n);
    // The product hi*2^128 + lo is below 2^(2n), so its high n bits are
    // (lo >> n) + hi * 2^(128 - n).
    let hi_n = (lo as Field - lo_n) / pow2(n) + (hi as Field) * pow2(128 - n);
    // isqrt: set the bits of the root from the top while the square stays
    // at most a; every candidate is below 2^64, so c*c fits a u128.
    let x = a as u128;
    let mut r: u128 = 0;
    for i in 0..(n / 2) {
        let c = r + ((1 as u128) << ((n / 2 - 1 - i) as u128));
        if c * c <= x {
            r = c;
        }
    }
    let diff = if a.lt(b) { b - a } else { a - b };
    let ceil = if b == 0 {
        (0, false)
    } else {
        let (q, rem) = (x / (b as u128), x % (b as u128));
        ((q as Field) + (rem != 0) as Field, true)
    };
    ((lo_n, hi_n), r as Field, diff, ceil)
}

/// TotalMulDiv on n-bit a, b, d: mul_div_or (q, r, ok) and
/// mul_div_ceil_or (c, ok).
unconstrained fn unsigned_mul_div_model(
    a: Field,
    b: Field,
    d: Field,
    n: u32,
) -> ((Field, Field, bool), (Field, bool)) {
    if d == 0 {
        ((0, 0, false), (0, false))
    } else {
        let (qh, ql, r) = mul_div_wide_ref(a, b, d);
        let q = (qh as Field) * pow2(128) + ql as Field;
        let c = q + (r != 0) as Field;
        let fl = if fits(q, n) {
            (q, r as Field, true)
        } else {
            (0, 0, false)
        };
        (fl, or_zero(fits(c, n), c))
    }
}

/// shape_divisor for the native types.
unconstrained fn pick_divisor<T: Num, let N: u32>(edge: u8, sd: u8, d: T, a: T, b: T) -> T {
    if edge % 8 < 2 {
        T::from_real(edge_divisor(a.real(), b.real(), N, N, edge % 8 == 1))
    } else {
        pick_u::<T, N>(sd, d)
    }
}

fn check_unsigned<T, let N: u32>(sa: u8, a: T, sb: u8, b: T, sd: u8, d: T, edge: u8, se: u8, e: u32)
where
    T: Num + TotalArith + Saturating + TotalUnsigned + TotalMulDiv,
{
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b, e) =
        unsafe { (pick_u::<T, N>(sa, a), pick_u::<T, N>(sb, b), pick_u::<u32, 32>(se, e)) };
    // Safety: input selection; the value reaches the library as a witness.
    let d = unsafe { pick_divisor::<T, N>(edge, sd, d, a, b) };
    let (ra, rb, rd) = (a.real(), b.real(), d.real());
    // Safety: reference model, compared below.
    let (m, (q, r, ok)) = unsafe { unsigned_model(ra, rb, N) };
    let (x, xok) = a.add_or(b);
    assert_eq((x.real(), xok), m[0]);
    let (x, xok) = a.sub_or(b);
    assert_eq((x.real(), xok), m[1]);
    let (x, xok) = a.mul_or(b);
    assert_eq((x.real(), xok), m[2]);
    assert_eq(a.saturating_add(b).real(), m[3].0);
    assert_eq(a.saturating_sub(b).real(), m[4].0);
    assert_eq(a.saturating_mul(b).real(), m[5].0);
    let (gq, gr, gok) = a.div_rem_or(b);
    assert_eq((gq.real(), gr.real(), gok), (q, r, ok));
    let (gq, gok) = a.div_or(b);
    assert_eq((gq.real(), gok), (q, ok));
    let (gr, gok) = a.mod_or(b);
    assert_eq((gr.real(), gok), (r, ok));

    // Safety: reference model, compared below.
    let ((lo, hi), root, diff, ceil) = unsafe { unsigned_more_model(ra, rb, N) };
    let (glo, ghi) = a.widening_mul(b);
    assert_eq((glo.real(), ghi.real()), (lo, hi));
    assert_eq(a.isqrt().real(), root);
    assert_eq(a.abs_diff(b).real(), diff);
    let (c, cok) = a.div_ceil_or(b);
    assert_eq((c.real(), cok), ceil);

    // Safety: reference model, compared below.
    let pow = unsafe { pow_below(ra as u128, e as Field, N) };
    let (p, pok) = a.pow_or(e);
    assert_eq((p.real(), pok), pow);

    // Safety: reference model, compared below.
    let (fl, cl) = unsafe { unsigned_mul_div_model(ra, rb, rd, N) };
    let (gq, gr, gok) = a.mul_div_or(b, d);
    assert_eq((gq.real(), gr.real(), gok), fl);
    let (c, cok) = a.mul_div_ceil_or(b, d);
    assert_eq((c.real(), cok), cl);
}

#[test]
fn unsigned_u8(sa: u8, a: u8, sb: u8, b: u8, sd: u8, d: u8, edge: u8, se: u8, e: u32) {
    check_unsigned::<u8, 8>(sa, a, sb, b, sd, d, edge, se, e);
}

#[test]
fn unsigned_u16(sa: u8, a: u16, sb: u8, b: u16, sd: u8, d: u16, edge: u8, se: u8, e: u32) {
    check_unsigned::<u16, 16>(sa, a, sb, b, sd, d, edge, se, e);
}

#[test]
fn unsigned_u32(sa: u8, a: u32, sb: u8, b: u32, sd: u8, d: u32, edge: u8, se: u8, e: u32) {
    check_unsigned::<u32, 32>(sa, a, sb, b, sd, d, edge, se, e);
}

#[test]
fn unsigned_u64(sa: u8, a: u64, sb: u8, b: u64, sd: u8, d: u64, edge: u8, se: u8, e: u32) {
    check_unsigned::<u64, 64>(sa, a, sb, b, sd, d, edge, se, e);
}

#[test]
fn unsigned_u128(sa: u8, a: u128, sb: u8, b: u128, sd: u8, d: u128, edge: u8, se: u8, e: u32) {
    check_unsigned::<u128, 128>(sa, a, sb, b, sd, d, edge, se, e);
}
