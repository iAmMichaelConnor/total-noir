// ec: msm_or against the in-circuit ladder (mul_limbs_or per term and
// complete adds, no black box), on points [a]G for fuzzed a mixed with
// special points: infinity, G and -G, bb 6.0.0's MSM offset generators
// o_1, o_2, o_3 and -(1/15) o_1, -(1/15) o_2 (inputs its gadget cannot
// prove unblinded), an off-curve point and a malformed infinity; and on
// edge scalars, valid and invalid.
use crate::ec::{msm_or, ORDER_HI, ORDER_LO, Point};
use crate::ec::msm_tests::{ladder_msm, M15_O1, M15_O2, O1, O2, O3};
use super::{low_bits, pow2};
use std::embedded_curve_ops::{EmbeddedCurvePoint, EmbeddedCurveScalar, multi_scalar_mul};

/// A point chosen by sel: one of the special points above, or [a]G (from
/// the solver's own MSM) for most selectors.
unconstrained fn pick_point(sel: u8, a: Field) -> Point {
    let k = sel % 16;
    if k == 0 {
        Point::infinity()
    } else if k == 1 {
        O1
    } else if k == 2 {
        O2
    } else if k == 3 {
        O3
    } else if k == 4 {
        M15_O1
    } else if k == 5 {
        M15_O2
    } else if k == 6 {
        Point::generator()
    } else if k == 7 {
        Point::generator().neg()
    } else if k == 8 {
        Point { x: a, y: a + 1, inf: false }
    } else if k == 9 {
        Point { x: a, y: 0, inf: true }
    } else {
        let e = multi_scalar_mul(
            [EmbeddedCurvePoint::generator()],
            [EmbeddedCurveScalar::from_field(a)],
        );
        Point { x: e.x, y: e.y, inf: (e.x == 0) & (e.y == 0) }
    }
}

/// A scalar (lo, hi) chosen by sel: 0, 1, q - 1, q, 2^252 (top window 1),
/// lo = 2^128, a short value, raw limbs cut into range (below q), the
/// high limb at q's (below or above q by the low limb), or the raw limbs.
unconstrained fn pick_scalar(sel: u8, lo: Field, hi: Field) -> (Field, Field) {
    let k = sel % 10;
    if k == 0 {
        (0, 0)
    } else if k == 1 {
        (1, 0)
    } else if k == 2 {
        (ORDER_LO - 1, ORDER_HI)
    } else if k == 3 {
        (ORDER_LO, ORDER_HI)
    } else if k == 4 {
        (0, pow2(124))
    } else if k == 5 {
        (pow2(128), 0)
    } else if k == 6 {
        (low_bits(lo, 64), 0)
    } else if k == 7 {
        (low_bits(lo, 128), low_bits(hi, 125))
    } else if k == 8 {
        (low_bits(lo, 128), ORDER_HI)
    } else {
        (lo, hi)
    }
}

#[test]
fn msm_matches_ladder(ps: [u8; 2], a: [Field; 2], ss: [u8; 2], lo: [Field; 2], hi: [Field; 2]) {
    // Safety: input selection; the values reach the library as witnesses.
    let pts = unsafe { [pick_point(ps[0], a[0]), pick_point(ps[1], a[1])] };
    // Safety: as above.
    let (l0, h0) = unsafe { pick_scalar(ss[0], lo[0], hi[0]) };
    // Safety: as above.
    let (l1, h1) = unsafe { pick_scalar(ss[1], lo[1], hi[1]) };
    let (r, ok) = msm_or(pts, [l0, l1], [h0, h1]);
    let (e, eok) = ladder_msm(pts, [l0, l1], [h0, h1]);
    assert_eq(ok, eok);
    assert_eq(r.inf, e.inf);
    assert_eq(r.x, e.x);
    assert_eq(r.y, e.y);
}
