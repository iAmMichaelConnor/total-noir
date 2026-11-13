// msm_or: equivalence with the solver's MSM and with the in-circuit
// ladder, the inputs bb 6.0.0's MSM gadget cannot prove unblinded, the
// hints on edge inputs, and the constraint half on wrong hints. The
// backend-level check (bb prove and verify on the offset-generator
// inputs) is noir/total_prove_check.
use crate::core::TWO_POW_128;
use crate::ctl::Select;
use crate::test_support::wit as w;
use super::{
    add, constrain_msm_correction, double, is_well_formed, msm_or, msm_with_hints, mul_limbs_or,
    mul_or, ORDER_HI, ORDER_LO, Point,
};
use super::msm_hint::{
    blind_point, blind_scalar, hint_neg_sum, msm_hints, p2_permutation, p2_squeeze2,
};
use std::embedded_curve_ops::{EmbeddedCurvePoint, EmbeddedCurveScalar, multi_scalar_mul};

// bb 6.0.0's MSM offset generators o_1, o_2, o_3 (derive_generators of
// "cycle_group_offset_generator"); base j of a black-box call uses
// o_{j+1}.
pub(crate) global O1: Point = Point {
    x: 0x07ecf4931ea0257c089816cfc3ed44c9172b22622539fdad7535401a7a99fb4b,
    y: 0x0f8bf0d676c12c8e10ea1f8fe9e5100db24b89ef3006b321f2178adc6281ec74,
    inf: false,
};
pub(crate) global O2: Point = Point {
    x: 0x0fb76e5904e203fe96cf620f86739e685c85c56774b23c1e7c86fba3290ae42b,
    y: 0x2a32122a08e2dcc594f4b657eb5e2e4f84cb67f06ab4b2d432c5f61c22330a3f,
    inf: false,
};
pub(crate) global O3: Point = Point {
    x: 0x2e09e700d6472d6d69189b06ddde8a0c0a559603086c619abc217c43534866f6,
    y: 0x0ff3c9ddfc6aaa740822422a0cf194a98d6a06ec2c433435b5bae6a172d56b5f,
    inf: false,
};
/// -(1/15) o_1: the last table step of base 0 meets it.
pub(crate) global M15_O1: Point = Point {
    x: 0x25ad41cc795fc510b656aea4992667a6fa28cc5f4c7b3d17796444e9f12acc0b,
    y: 0x02c8a9e441b52c24ff6cea7dbb03605cc605190935b11e7a880a261794c86441,
    inf: false,
};
/// -(1/15) o_2.
pub(crate) global M15_O2: Point = Point {
    x: 0x23d26cbbc30f73d118577822621b815c5237a7e239312ff1d197ba4948a2ee9a,
    y: 0x3029dcebcc17d09a134832fe0eafa83f5b8d09b522ac9c352475441c24ed6c02,
    inf: false,
};
/// A = [12345678]G, and P2 with [5]A + [7]P2 = minus the total offset the
/// gadget's accumulator carries for two bases.
global A: Point = Point {
    x: 0x0c86ad3ab8b01adab12c7cc6e60683894b926177050d912fdccdc4a0018c975a,
    y: 0x1e8d4c68fb1746c192422257da8fdf1e81215f37e5d7bb6a5c84a143f3f7a4fe,
    inf: false,
};
global MINUS_W_P2: Point = Point {
    x: 0x2d1d5232623bbde43e880f51fb18dafee26290bc6c8a6fc72939b5d1486d494d,
    y: 0x05d966f8a7c2c831e57460c4fa7c480c13ea0ee2292337cc5f366f30519be6a7,
    inf: false,
};
/// A base whose run with scalar 5 collides in the accumulator (scalar 6
/// does not).
global ACC_S5: Point = Point {
    x: 0x0d64daeec4d6d8c41b957cf310b5abaf2be97a10c253179d0efaa1f19bd4b828,
    y: 0x0c6745f6006365d2257c551e71f5d498c19f235ea02bd04bbe92cca4e25c8666,
    inf: false,
};
/// o_0 - o_1: with scalar 2^252 its first entry meets the accumulator's
/// seed o_0.
global ACC_TOP: Point = Point {
    x: 0x1d4a936dd25907e632bc879a0f4291e92d7dc34906e09af53a715cdd0c947474,
    y: 0x047b25919d882bf0415c584949b1847b81d57051d43e7470cd956b50baff5668,
    inf: false,
};

global TWO_POW_124: Field = 0x10000000000000000000000000000000;

fn wp(p: Point) -> Point {
    Point { x: w(p.x), y: w(p.y), inf: w(p.inf) }
}

fn wpts<let N: u32>(p: [Point; N]) -> [Point; N] {
    let mut r = p;
    for i in 0..N {
        r[i] = wp(p[i]);
    }
    r
}

fn wf<let N: u32>(a: [Field; N]) -> [Field; N] {
    let mut r = a;
    for i in 0..N {
        r[i] = w(a[i]);
    }
    r
}

/// Reference without the library: the flags from the definitions, then
/// the solver's own MSM (std multi_scalar_mul in unconstrained code) on
/// valid inputs, infinity otherwise.
unconstrained fn solver_msm<let N: u32>(
    pts: [Point; N],
    lo: [Field; N],
    hi: [Field; N],
) -> (Point, bool) {
    let mut ok = true;
    let mut e = [EmbeddedCurvePoint::point_at_infinity(); N];
    let mut s = [EmbeddedCurveScalar::new(0, 0); N];
    for i in 0..N {
        let p = pts[i];
        let pv = if p.inf {
            (p.x == 0) & (p.y == 0)
        } else {
            p.y * p.y == p.x * p.x * p.x - 17
        };
        let sv = lo[i].lt(TWO_POW_128)
            & hi[i].lt(TWO_POW_128)
            & (hi[i].lt(ORDER_HI) | ((hi[i] == ORDER_HI) & lo[i].lt(ORDER_LO)));
        ok = ok & pv & sv;
        if pv & sv & !p.inf {
            e[i] = EmbeddedCurvePoint { x: p.x, y: p.y };
            s[i] = EmbeddedCurveScalar::new(lo[i], hi[i]);
        }
    }
    if ok {
        let r = multi_scalar_mul(e, s);
        let inf = (r.x == 0) & (r.y == 0);
        (Point { x: r.x, y: r.y, inf }, true)
    } else {
        (Point::infinity(), false)
    }
}

/// The in-circuit reference: one ladder per term and complete adds.
pub(crate) fn ladder_msm<let N: u32>(
    pts: [Point; N],
    lo: [Field; N],
    hi: [Field; N],
) -> (Point, bool) {
    let mut acc = Point::infinity();
    let mut ok = true;
    for i in 0..N {
        let pv = is_well_formed(pts[i]);
        let (m, sv) = mul_limbs_or(Point::select(pv, pts[i], Point::infinity()), lo[i], hi[i]);
        acc = add(acc, m);
        ok = ok & pv & sv;
    }
    (Point::select(ok, acc, Point::infinity()), ok)
}

/// msm_or on witnesses against the solver's MSM, coordinates included.
fn check<let N: u32>(pts: [Point; N], lo: [Field; N], hi: [Field; N]) {
    let (r, ok) = msm_or(wpts(pts), wf(lo), wf(hi));
    // Safety: a reference value, compared below.
    let (e, eok) = unsafe { solver_msm(pts, lo, hi) };
    assert_eq(ok, eok);
    assert_eq(r.inf, e.inf);
    assert_eq(r.x, e.x);
    assert_eq(r.y, e.y);
}

/// msm_or on witnesses against the ladder.
fn check_ladder<let N: u32>(pts: [Point; N], lo: [Field; N], hi: [Field; N]) {
    let (pw, lw, hw) = (wpts(pts), wf(lo), wf(hi));
    let (r, ok) = msm_or(pw, lw, hw);
    let (e, eok) = ladder_msm(pw, lw, hw);
    assert_eq(ok, eok);
    assert_eq(r.inf, e.inf);
    assert_eq(r.x, e.x);
    assert_eq(r.y, e.y);
}

#[test]
fn honest_inputs_match_the_solver() {
    let g = Point::generator();
    let g2 = double(g);
    let (g7, _) = mul_or::<8>(g, 7);
    check([g], [5], [0]);
    check([g, g2, g7], [3, 5, 11], [0, 0, 0]);
    // full-width scalars: q - 1, q - 2, q - 3 (the sum wraps q twice)
    check(
        [g, g2, g7],
        [ORDER_LO - 1, ORDER_LO - 2, ORDER_LO - 3],
        [ORDER_HI, ORDER_HI, ORDER_HI],
    );
    check([A, g7], [TWO_POW_128 - 1, 0], [ORDER_HI - 1, TWO_POW_124]);
    // a low-limb carry and limbs at the top of the high range
    check([g, g2, g7], [ORDER_LO + 5, ORDER_LO + 9, 1], [1, 2, 0]);
    check([g, g2, g7], [1, 2, 0], [ORDER_HI, ORDER_HI, 0]);
    // zero scalars, infinity bases, repeated and negated bases
    check([g, Point::infinity(), g], [0, 5, 0], [0, 0, 0]);
    check([g, g, g.neg()], [5, 7, 12], [1, 2, 3]);
    check([Point::infinity(), Point::infinity()], [1, 2], [0, 0]);
    check([g, g], [ORDER_LO - 1, 1], [ORDER_HI, 0]);
    // cancelling terms: the result is infinity with ok
    check([g, g.neg()], [9, 9], [4, 4]);
    check([A, A], [0, 0], [0, 0]);
    // no terms at all
    let (z, okz) = msm_or([], [], []);
    assert(okz);
    assert(z.inf);
}

#[test]
fn invalid_inputs_give_false_and_infinity() {
    let g = Point::generator();
    let g2 = double(g);
    check([Point { x: 1, y: 1, inf: false }, g2], [3, 5], [0, 0]);
    check([Point { x: 0, y: 0, inf: false }, g2], [3, 5], [0, 0]);
    check([Point { x: 3, y: 0, inf: true }, g2], [3, 5], [0, 0]);
    check([g, g2], [ORDER_LO, 5], [ORDER_HI, 0]);
    check([g, g2], [TWO_POW_128, 5], [0, 0]);
    check([g, g2], [1, 5], [TWO_POW_128, 0]);
    check([g, g2], [0 - 1, 5], [0, 0]);
    check([O1, M15_O1], [5, 5], [ORDER_HI + 1, 0]);
}

// The inputs that bb 6.0.0's gadget cannot prove when they reach it
// directly (noir/total_prove_check proves them through msm_or): correct
// output here, against the solver and against the ladder.
#[test]
fn offset_generator_inputs_match_the_solver() {
    check([O1], [5], [0]);
    check([O1], [0], [0]);
    check([M15_O1], [5], [0]);
    check([O1, O2], [5, 7], [0, 0]);
    check([Point::infinity(), O2], [5, 7], [0, 0]);
    check([O1, O2, O3], [ORDER_LO - 1, 1, 2], [ORDER_HI, 0, 0]);
    check([M15_O1, M15_O2], [1, 1], [0, 0]);
    check([A, MINUS_W_P2], [5, 7], [0, 0]);
    check([ACC_S5], [5], [0]);
    check([ACC_S5], [6], [0]);
    check([ACC_TOP], [0], [TWO_POW_124]);
}

// The same against the ladder (no black box at all) on two of them; the
// fuzz test fuzz_tests::ec runs the ladder comparison on fuzzed inputs.
#[test]
fn offset_generator_inputs_match_the_ladder() {
    check_ladder([O1, MINUS_W_P2], [5, 7], [0, 0]);
}

// --- the hints ---

global P_MINUS_1: Field = 0 - 1;

#[test]
unconstrained fn p2_permutation_matches_black_box() {
    let states: [[Field; 4]; 5] = [
        [0, 0, 0, 0],
        [0, 1, 2, 3],
        [P_MINUS_1, P_MINUS_1, P_MINUS_1, P_MINUS_1],
        [0x1234, 0x10000000000000000, TWO_POW_128, P_MINUS_1 - 5],
        [O1.x, O1.y, O2.x, O2.y],
    ];
    for i in 0..5 {
        assert_eq(p2_permutation(states[i]), std::hash::poseidon2_permutation(states[i]));
    }
}

#[test]
unconstrained fn p2_squeeze2_extends_p2_hash() {
    assert_eq(p2_squeeze2([7]).0, crate::hash::p2_hash([7]));
    assert_eq(p2_squeeze2([7, 8, 9]).0, crate::hash::p2_hash([7, 8, 9]));
    assert_eq(p2_squeeze2([1, 2, 3, 4, 5, 6]).0, crate::hash::p2_hash([1, 2, 3, 4, 5, 6]));
    let input = [1, 2, 3, 4, 5, P_MINUS_1, 0, 0, 9, 10, 11];
    let (h0, h1) = p2_squeeze2(input);
    assert_eq(h0, crate::hash::p2_hash(input));
    assert(h0 != h1);
}

// blind_point(h) is [s]G for s = 2^252 + (h mod 2^252), never infinity,
// on every edge of h.
#[test]
unconstrained fn blind_point_matches_the_solver() {
    let hs = [0, 1, 2, P_MINUS_1, TWO_POW_128, TWO_POW_128 - 1, 0x1234567890abcdef, O1.x];
    for i in 0..8 {
        let (x, y) = blind_point(hs[i]);
        let s = blind_scalar(hs[i]);
        let e = multi_scalar_mul(
            [EmbeddedCurvePoint::generator()],
            [EmbeddedCurveScalar::from_field(s)],
        );
        assert_eq(x, e.x);
        assert_eq(y, e.y);
        assert(y * y == x * x * x - 17);
        // 2^252 <= s < 2^253
        let top: [bool; 254] = s.to_le_bits();
        assert(top[252]);
        assert(!top[253]);
    }
}

/// The correction hint on limb pairs below q: t is canonical and
/// t + sum = k*q (checked by the constraint half), on edge sums.
#[test]
fn neg_sum_hint_satisfies_constraint() {
    let cases: [([Field; 3], [Field; 3]); 8] = [
        ([0, 0, 0], [0, 0, 0]),
        ([1, 0, 0], [0, 0, 0]),
        ([ORDER_LO - 1, 1, 0], [ORDER_HI, 0, 0]),
        ([ORDER_LO - 1, ORDER_LO - 1, ORDER_LO - 1], [ORDER_HI, ORDER_HI, ORDER_HI]),
        ([ORDER_LO + 7, 3, TWO_POW_128 - 1], [5, ORDER_HI - 5, 0]),
        ([0, 0, 0], [ORDER_HI, ORDER_HI, ORDER_HI]),
        ([ORDER_LO, ORDER_LO, 0], [ORDER_HI - 1, 0, 1]),
        ([TWO_POW_128 - 1, TWO_POW_128 - 1, TWO_POW_128 - 1], [ORDER_HI - 1, ORDER_HI - 1, 0]),
    ];
    for i in 0..8 {
        let (lo, hi) = cases[i];
        let (lw, hw) = (wf(lo), wf(hi));
        // Safety: test of the hint against its constraint half.
        let (t_lo, t_hi, k) = unsafe { hint_neg_sum(lw, hw) };
        constrain_msm_correction(lw, hw, t_lo, t_hi, k);
        // canonical: t < q
        assert(t_hi.lt(ORDER_HI) | ((t_hi == ORDER_HI) & t_lo.lt(ORDER_LO)));
    }
}

/// The hints never trap, including on inputs off their precondition
/// (malformed points, out-of-range limbs), which msm_or never passes.
#[test]
unconstrained fn hints_trap_free_on_hostile_inputs() {
    let bad = Point { x: P_MINUS_1, y: 5, inf: true };
    let _ = msm_hints(
        [bad, O1, Point::infinity()],
        [P_MINUS_1, 0, TWO_POW_128],
        [P_MINUS_1, P_MINUS_1, 0],
    );
    let _ = msm_hints([Point::infinity()], [0], [0]);
    let _ = msm_hints([], [], []);
}

// --- wrong hints: rejected, or the same output ---

fn honest_t<let N: u32>(lo: [Field; N], hi: [Field; N]) -> (Field, Field, Field) {
    // Safety: test helper; the constraint half checks it.
    unsafe {
        hint_neg_sum(lo, hi)
    }
}

fn xy(p: Point) -> (Field, Field) {
    (w(p.x), w(p.y))
}

// Any curve points as blinds give the same output: arbitrary, equal,
// equal to a base, the negation of a base (so P + B1 is infinity), each
// other's negation, and bb's own offset generators.
#[test]
fn any_curve_blinds_give_the_same_point() {
    let g = Point::generator();
    let g2 = double(g);
    let (g7, _) = mul_or::<8>(g, 7);
    let pts = wpts([g, g2]);
    let lo = wf([3, 5]);
    let hi = wf([0, 1]);
    // Safety: a reference value, compared below.
    let (want, _) = unsafe { solver_msm([g, g2], [3, 5], [0, 1]) };
    let t = honest_t(lo, hi);
    let blinds = [(g7, g2), (g7, g7), (g, g2), (g7, g.neg()), (g2, g2.neg()), (O1, O2), (O2, O3)];
    for i in 0..7 {
        let (b0, b1) = blinds[i];
        assert_eq(msm_with_hints(pts, lo, hi, xy(b0), xy(b1), t), want);
    }
}

#[test(should_fail_with = "msm_or: blind 0 not on the curve")]
fn off_curve_blind_0_rejected() {
    let g = Point::generator();
    let lo = wf([3, 5]);
    let hi = wf([0, 0]);
    let _ = msm_with_hints(wpts([g, g]), lo, hi, (w(1), w(1)), xy(g), honest_t(lo, hi));
}

#[test(should_fail_with = "msm_or: blind 1 not on the curve")]
fn infinity_encoding_blind_1_rejected() {
    let g = Point::generator();
    let lo = wf([3, 5]);
    let hi = wf([0, 0]);
    let _ = msm_with_hints(wpts([g, g]), lo, hi, xy(g), (w(0), w(0)), honest_t(lo, hi));
}

#[test(should_fail_with = "msm_or: correction scalar")]
fn wrong_correction_high_limb_rejected() {
    let lo = wf([3, 5]);
    let hi = wf([0, 0]);
    let (t_lo, t_hi, k) = honest_t(lo, hi);
    constrain_msm_correction(lo, hi, t_lo, t_hi + 1, k);
}

#[test(should_fail)]
fn wrong_correction_low_limb_rejected() {
    let lo = wf([3, 5]);
    let hi = wf([0, 0]);
    let (t_lo, t_hi, k) = honest_t(lo, hi);
    constrain_msm_correction(lo, hi, t_lo + 1, t_hi, k);
}

#[test(should_fail)]
fn wrong_multiple_rejected() {
    let lo = wf([3, 5]);
    let hi = wf([0, 0]);
    let (t_lo, t_hi, k) = honest_t(lo, hi);
    constrain_msm_correction(lo, hi, t_lo, t_hi, k + 1);
}

#[test(should_fail)]
fn zero_correction_rejected() {
    let lo = wf([3, 5]);
    let hi = wf([0, 0]);
    constrain_msm_correction(lo, hi, 0, 0, 0);
}

/// t + q, the same residue as t with k one larger, as limbs below 2^128.
fn t_plus_q(t: (Field, Field, Field)) -> (Field, Field, Field) {
    let l = t.0 + ORDER_LO;
    // Safety: test helper; the sum is checked by the constraint half.
    let carry = unsafe { lt_hint(l, TWO_POW_128) };
    let c = 1 - carry as Field;
    (l - c * TWO_POW_128, t.1 + ORDER_HI + c, t.2 + 1)
}

unconstrained fn lt_hint(a: Field, b: Field) -> bool {
    a.lt(b)
}

// t + q passes the identity (the same residue mod q). The solver
// refuses it as a scalar; were a backend to accept it, (t + q) B1 = t B1
// and the output would be the same.
#[test]
fn non_canonical_correction_passes_the_identity() {
    let lo = wf([3, 5]);
    let hi = wf([0, 0]);
    let t = t_plus_q(honest_t(lo, hi));
    constrain_msm_correction(lo, hi, t.0, t.1, t.2);
}

#[test(should_fail)]
fn non_canonical_correction_fails_in_the_solver() {
    let g = Point::generator();
    let lo = wf([3, 5]);
    let hi = wf([0, 0]);
    let t = t_plus_q(honest_t(lo, hi));
    let _ = msm_with_hints(wpts([g, g]), lo, hi, xy(g), xy(g), t);
}
