// Witness-level differential check: total's entries on inputs read from
// Prover.toml, so the ACIR lowering and the solver run on real witnesses
// (unit tests on literals fold at compile time). Each result is asserted
// against an unconstrained reference on the same inputs, and the
// BoundedVec forms run on vectors whose length breaks the invariant
// (len > MaxLen, which an entry-point BoundedVec parameter admits).
// run.sh executes it on every Prover*.toml here; any mismatch fails.
use total::arith::{add_or, div_rem_or, mul_div_or, mul_or, sub_or, TotalArith};
use total::bitwise::{shl_or, shr_or};
use total::collections::bounded_vec::{from_parts_or, TotalBoundedVec};
use total::collections::{index_or, sort_or};
use total::convert::{to_u64_or, to_u8_or};
use total::range::{clamp_bits_or, fits_bits};

global TWO_64: Field = 0x10000000000000000;

unconstrained fn fits_ref(x: Field, bound: Field) -> bool {
    x.lt(bound)
}

unconstrained fn u64_ref(x: Field) -> (u128, bool) {
    let ok = x.lt(TWO_64);
    (if ok { x as u128 } else { 0 }, ok)
}

// (sum, difference, product, quotient, remainder, a*b / d, a*b % d,
// a << s mod 2^64, a >> s) with the flags total's entries report, and
// the zero value on a false flag.
unconstrained fn arith_ref(a: Field, b: Field, d: Field, s: Field) -> [(Field, bool); 9] {
    let (ai, oka) = u64_ref(a);
    let (bi, okb) = u64_ref(b);
    let (di, okd) = u64_ref(d);
    let ok = oka & okb;
    let m: u128 = 0xffffffffffffffff;
    let add_ok = ok & ((ai + bi) <= m);
    let sub_ok = ok & (ai >= bi);
    let mul_ok = ok & ((ai * bi) <= m);
    let div_ok = ok & (bi != 0);
    let md_ok = ok & okd & (di != 0);
    let s_ok = oka & s.lt(64);
    let sh = if s_ok { s as u128 } else { 0 };
    let z = |c: bool, v: u128| -> (Field, bool) { (if c { v as Field } else { 0 }, c) };
    [
        z(add_ok, if add_ok { ai + bi } else { 0 }),
        z(sub_ok, if sub_ok { ai - bi } else { 0 }),
        z(mul_ok, if mul_ok { ai * bi } else { 0 }),
        z(div_ok, if div_ok { ai / bi } else { 0 }),
        z(div_ok, if div_ok { ai % bi } else { 0 }),
        z(md_ok, if md_ok { (ai * bi) / di } else { 0 }),
        z(md_ok, if md_ok { (ai * bi) % di } else { 0 }),
        z(s_ok, if s_ok { (ai << sh) & m } else { 0 }),
        z(s_ok, if s_ok { ai >> sh } else { 0 }),
    ]
}

unconstrained fn sort_ref(arr: [Field; 4]) -> ([Field; 4], bool) {
    let mut ok = true;
    for i in 0..4 {
        ok = ok & arr[i].lt(TWO_64);
    }
    let mut out = [0; 4];
    if ok {
        out = arr;
        for i in 0..4 {
            for j in 0..3 - i {
                if out[j + 1].lt(out[j]) {
                    let t = out[j];
                    out[j] = out[j + 1];
                    out[j + 1] = t;
                }
            }
        }
    }
    (out, ok)
}

fn check_vec(v: BoundedVec<Field, 4>, x: Field) {
    // Safety: the reference only decides what is asserted
    let valid = unsafe { fits_ref(v.len() as Field, 5) };
    assert_eq(v.is_valid(), valid);
    let empty: BoundedVec<Field, 4> = BoundedVec::new();
    let (p, ok) = v.push_or(x);
    let (q, y, ok2) = v.pop_or();
    let (g, ok3) = v.get_or(0);
    let (s, ok4) = v.set_or(0, x);
    let (l, ok5) = v.set_len_or(2);
    let (e, ok6) = v.extend_from_array_or([x]);
    if !valid {
        // A broken length: every flag false, every vector empty and zeroed.
        assert(!(ok | ok2 | ok3 | ok4 | ok5 | ok6));
        assert_eq((y, g), (0, 0));
        for r in [p, q, s, l, e] {
            assert_eq(r.len(), 0);
            assert_eq(r.storage(), empty.storage());
        }
    } else {
        let n = v.len();
        assert_eq(ok, n < 4);
        assert_eq(ok2, n > 0);
        assert_eq(ok3, n > 0);
        assert_eq(ok4, n > 0);
        assert(ok5);
        assert_eq(l.len(), 2);
        assert_eq(ok6, n < 4);
        if ok {
            assert_eq(p.len(), n + 1);
            assert_eq(p.get(n), x);
        } else {
            assert_eq(p, v);
        }
        if ok3 {
            assert_eq(g, v.get(0));
            assert_eq(s.get(0), x);
            assert_eq(y, v.get(n - 1));
            assert_eq(q.len(), n - 1);
        }
    }
}

fn main(
    xs: [Field; 6],
    ys: [Field; 6],
    ds: [Field; 6],
    ss: [Field; 6],
    v_short: BoundedVec<Field, 4>,
    v_full: BoundedVec<Field, 4>,
    v_broken: BoundedVec<Field, 4>,
    v_huge: BoundedVec<Field, 4>,
) {
    for i in 0..6 {
        let (a, b, d, s) = (xs[i], ys[i], ds[i], ss[i]);
        // Safety: the reference only decides what is asserted
        let (f8, f64, f128, f160) = unsafe {
            (
                fits_ref(a, 256), fits_ref(a, TWO_64), fits_ref(a, TWO_64 * TWO_64),
                fits_ref(a, TWO_64 * TWO_64 * 0x100000000),
            )
        };
        assert_eq(fits_bits::<8>(a), f8);
        assert_eq(fits_bits::<64>(a), f64);
        assert_eq(fits_bits::<128>(a), f128);
        assert_eq(fits_bits::<160>(a), f160);
        assert_eq(clamp_bits_or::<64>(a), (if f64 { a } else { 0 }, f64));
        let (u, ok) = to_u8_or(a);
        assert_eq((u as Field, ok), (if f8 { a } else { 0 }, f8));
        let (w, ok) = to_u64_or(a);
        assert_eq((w as Field, ok), (if f64 { a } else { 0 }, f64));
        // Safety: the reference only decides what is asserted
        let r = unsafe { arith_ref(a, b, d, s) };
        assert_eq(add_or::<64>(a, b), r[0]);
        assert_eq(sub_or::<64>(a, b), r[1]);
        assert_eq(mul_or::<64>(a, b), r[2]);
        assert_eq(div_rem_or::<64>(a, b), (r[3].0, r[4].0, r[3].1));
        assert_eq(mul_div_or::<64>(a, b, d), (r[5].0, r[6].0, r[5].1));
        assert_eq(shl_or::<64>(a, s), r[7]);
        assert_eq(shr_or::<64>(a, s), r[8]);
        if f64 & fits_bits::<64>(b) {
            let (v, ok) = (a as u64).add_or(b as u64);
            assert_eq((v as Field, ok), r[0]);
        }
        // Safety: the reference only decides what is asserted
        let a_lt_b = unsafe { fits_ref(a, b) };
        assert_eq(total::lt(a, b), a_lt_b);
        let (e, ok) = index_or([xs[0], xs[1], xs[2], xs[3]], s);
        // Safety: the reference only decides what is asserted
        let in_range = unsafe { fits_ref(s, 4) };
        assert_eq(ok, in_range);
        if !in_range {
            assert_eq(e, 0);
        }
    }
    let arr = [ys[0], ys[1], ys[2], ys[3]];
    // Safety: the reference only decides what is asserted
    assert_eq(sort_or::<4, 64>(arr), unsafe { sort_ref(arr) });
    let (fv, ok) = from_parts_or(v_broken.storage(), v_broken.len());
    assert(!ok);
    assert_eq(fv.len(), 0);
    check_vec(v_short, xs[1]);
    check_vec(v_full, xs[1]);
    check_vec(v_broken, xs[1]);
    check_vec(v_huge, xs[1]);
}
