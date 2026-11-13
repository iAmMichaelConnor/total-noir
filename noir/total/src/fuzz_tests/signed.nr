// signed: TotalArith, Saturating, TotalSigned, TotalMulDiv and
// unsigned_abs on i8..i64, against models on real values: Field for
// + - * (every product is below 2^127 in magnitude) and u128 magnitudes
// for the divisions.
use crate::arith::{Saturating, TotalArith, TotalMulDiv};
use crate::signed::{
    TotalSigned, unsigned_abs_i16, unsigned_abs_i32, unsigned_abs_i64, unsigned_abs_i8,
};
use super::{Num, or_zero, pick_s, pow2};

/// Whether a real value is negative (every real value here has magnitude
/// below 2^127).
unconstrained fn neg(r: Field) -> bool {
    !r.lt(pow2(127))
}

unconstrained fn mag(r: Field) -> u128 {
    if neg(r) {
        (0 - r) as u128
    } else {
        r as u128
    }
}

unconstrained fn with_sign(negative: bool, m: u128) -> Field {
    if negative {
        0 - (m as Field)
    } else {
        m as Field
    }
}

/// Whether the real value r is representable on n signed bits.
unconstrained fn fits_s(r: Field, n: u32) -> bool {
    (r + pow2(n - 1)).lt(pow2(n))
}

/// r clamped to the n-bit signed range.
unconstrained fn saturate(r: Field, n: u32) -> Field {
    if fits_s(r, n) {
        r
    } else if neg(r) {
        0 - pow2(n - 1)
    } else {
        pow2(n - 1) - 1
    }
}

/// a / d truncated toward zero and the remainder with the sign of a,
/// for d != 0.
unconstrained fn div_trunc(a: Field, d: Field) -> (Field, Field) {
    let (ma, md) = (mag(a), mag(d));
    (with_sign(neg(a) != neg(d), ma / md), with_sign(neg(a), ma % md))
}

/// add, sub, mul as (value, ok); saturating add, sub, mul; then
/// div_rem (q, r, ok).
unconstrained fn ops_model(
    a: Field,
    b: Field,
    n: u32,
) -> ([(Field, bool); 3], [Field; 3], (Field, Field, bool)) {
    let (s, t, p) = (a + b, a - b, a * b);
    let div = if b == 0 {
        (0, 0, false)
    } else {
        let (q, r) = div_trunc(a, b);
        if fits_s(q, n) {
            (q, r, true)
        } else {
            (0, 0, false)
        }
    };
    (
        [or_zero(fits_s(s, n), s), or_zero(fits_s(t, n), t), or_zero(fits_s(p, n), p)],
        [saturate(s, n), saturate(t, n), saturate(p, n)], div,
    )
}

/// neg_or, abs_or, signum, unsigned_abs, then div_floor_or, div_euclid_or,
/// rem_euclid_or.
unconstrained fn signed_model(
    a: Field,
    d: Field,
    n: u32,
) -> ([(Field, bool); 2], Field, Field, [(Field, bool); 3]) {
    let abs = with_sign(false, mag(a));
    let signum = if a == 0 {
        0
    } else if neg(a) {
        0 - 1
    } else {
        1
    };
    let divs = if d == 0 {
        [(0, false); 3]
    } else {
        let (q, r) = div_trunc(a, d);
        let floor = if (r != 0) & (neg(a) != neg(d)) {
            q - 1
        } else {
            q
        };
        // Euclid: a negative remainder moves up by |d|, the quotient by -sign(d).
        let (qe, re) = if neg(r) {
            (if neg(d) { q + 1 } else { q - 1 }, r + (mag(d) as Field))
        } else {
            (q, r)
        };
        let ok = fits_s(q, n);
        [or_zero(ok, floor), or_zero(ok, qe), or_zero(ok, re)]
    };
    ([or_zero(fits_s(0 - a, n), 0 - a), or_zero(fits_s(abs, n), abs)], signum, abs, divs)
}

/// mul_div_or (q, r, ok) and mul_div_ceil_or (c, ok): a*b / d truncated
/// toward zero, the remainder with the sign of a*b, and the ceiling.
unconstrained fn mul_div_model(
    a: Field,
    b: Field,
    d: Field,
    n: u32,
) -> ((Field, Field, bool), (Field, bool)) {
    if d == 0 {
        ((0, 0, false), (0, false))
    } else {
        let p = a * b;
        let (q, r) = div_trunc(p, d);
        let c = if (r != 0) & (neg(p) == neg(d)) {
            q + 1
        } else {
            q
        };
        let fl = if fits_s(q, n) {
            (q, r, true)
        } else {
            (0, 0, false)
        };
        (fl, or_zero(fits_s(c, n), c))
    }
}

/// A divisor with the sign of a*b that puts a*b / d at MAX, where the
/// quotient or its ceiling crosses it: |a*b| / MAX in magnitude gives a
/// quotient of MAX or more, one more gives one below. Its magnitude is
/// kept in [1, MAX].
unconstrained fn edge_divisor(a: Field, b: Field, n: u32, below: bool) -> Field {
    let p = a * b;
    let max = pow2(n - 1) - 1;
    let e = (mag(p) / (max as u128)) as Field + below as Field;
    let e = if e == 0 {
        1
    } else if e.lt(max) {
        e
    } else {
        max
    };
    with_sign(neg(p), e as u128)
}

/// The divisor input: one time in four an edge divisor of a and b, else d
/// from the shaper.
unconstrained fn pick_divisor<T: Num, let N: u32>(edge: u8, sd: u8, d: T, a: T, b: T) -> T {
    if edge % 8 < 2 {
        T::from_real(edge_divisor(a.real(), b.real(), N, edge % 8 == 1))
    } else {
        pick_s::<T, N>(sd, d)
    }
}

fn check_signed<T, let N: u32>(sa: u8, a: T, sb: u8, b: T, sd: u8, d: T, edge: u8)
where
    T: Num + TotalArith + Saturating + TotalSigned + TotalMulDiv,
{
    // Safety: input selection; the values reach the library as witnesses.
    let (a, b) = unsafe { (pick_s::<T, N>(sa, a), pick_s::<T, N>(sb, b)) };
    // Safety: input selection; the value reaches the library as a witness.
    let d = unsafe { pick_divisor::<T, N>(edge, sd, d, a, b) };
    let (ra, rb, rd) = (a.real(), b.real(), d.real());
    // Safety: reference model, compared below.
    let (m, sat, (q, r, ok)) = unsafe { ops_model(ra, rb, N) };
    let (x, xok) = a.add_or(b);
    assert_eq((x.real(), xok), m[0]);
    let (x, xok) = a.sub_or(b);
    assert_eq((x.real(), xok), m[1]);
    let (x, xok) = a.mul_or(b);
    assert_eq((x.real(), xok), m[2]);
    assert_eq(a.saturating_add(b).real(), sat[0]);
    assert_eq(a.saturating_sub(b).real(), sat[1]);
    assert_eq(a.saturating_mul(b).real(), sat[2]);
    let (gq, gr, gok) = a.div_rem_or(b);
    assert_eq((gq.real(), gr.real(), gok), (q, r, ok));
    let (gq, gok) = a.div_or(b);
    assert_eq((gq.real(), gok), (q, ok));
    let (gr, gok) = a.mod_or(b);
    assert_eq((gr.real(), gok), (r, ok));

    // Safety: reference model, compared below.
    let (negabs, signum, _, divs) = unsafe { signed_model(ra, rb, N) };
    let (x, xok) = a.neg_or();
    assert_eq((x.real(), xok), negabs[0]);
    let (x, xok) = a.abs_or();
    assert_eq((x.real(), xok), negabs[1]);
    assert_eq(a.signum().real(), signum);
    let (x, xok) = a.div_floor_or(b);
    assert_eq((x.real(), xok), divs[0]);
    let (x, xok) = a.div_euclid_or(b);
    assert_eq((x.real(), xok), divs[1]);
    let (x, xok) = a.rem_euclid_or(b);
    assert_eq((x.real(), xok), divs[2]);

    // Safety: reference model, compared below.
    let (fl, cl) = unsafe { mul_div_model(ra, rb, rd, N) };
    let (gq, gr, gok) = a.mul_div_or(b, d);
    assert_eq((gq.real(), gr.real(), gok), fl);
    let (c, cok) = a.mul_div_ceil_or(b, d);
    assert_eq((c.real(), cok), cl);
}

/// unsigned_abs as the model's |a|.
fn check_unsigned_abs<T, U, let N: u32>(sa: u8, a: T, f: fn(T) -> U)
where
    T: Num,
    U: Num,
{
    // Safety: input selection; the value reaches the library as a witness.
    let a = unsafe { pick_s::<T, N>(sa, a) };
    // Safety: reference model, compared below.
    let (_, _, abs, _) = unsafe { signed_model(a.real(), 1, N) };
    assert_eq(f(a).real(), abs);
}

#[test]
fn signed_i8(sa: u8, a: i8, sb: u8, b: i8, sd: u8, d: i8, edge: u8) {
    check_signed::<i8, 8>(sa, a, sb, b, sd, d, edge);
    check_unsigned_abs::<i8, u8, 8>(sa, a, unsigned_abs_i8);
}

#[test]
fn signed_i16(sa: u8, a: i16, sb: u8, b: i16, sd: u8, d: i16, edge: u8) {
    check_signed::<i16, 16>(sa, a, sb, b, sd, d, edge);
    check_unsigned_abs::<i16, u16, 16>(sa, a, unsigned_abs_i16);
}

#[test]
fn signed_i32(sa: u8, a: i32, sb: u8, b: i32, sd: u8, d: i32, edge: u8) {
    check_signed::<i32, 32>(sa, a, sb, b, sd, d, edge);
    check_unsigned_abs::<i32, u32, 32>(sa, a, unsigned_abs_i32);
}

#[test]
fn signed_i64(sa: u8, a: i64, sb: u8, b: i64, sd: u8, d: i64, edge: u8) {
    check_signed::<i64, 64>(sa, a, sb, b, sd, d, edge);
    check_unsigned_abs::<i64, u64, 64>(sa, a, unsigned_abs_i64);
}
