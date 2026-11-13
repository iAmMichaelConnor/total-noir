// Backend-level check of the entries built on the MSM black box: run.sh
// executes this program on each Prover*.toml and then proves and verifies
// the witness with bb, so a witness the solver accepts but the backend's
// constraints reject fails the run. The inputs include points and scalars
// that bb 6.0.0's MSM gadget cannot prove when they reach it directly:
// its offset generators o_1 and o_2 as bases, -(1/15) o_1, a two-term
// MSM whose sum cancels the gadget's total offset, an engineered
// accumulator collision, and o_2 as a Schnorr key.
//
// Each msm_or result is compared with the solver's own MSM (std
// multi_scalar_mul in unconstrained code); schnorr_verify is compared with
// the expected verdict in the Prover file.
use std::embedded_curve_ops::{EmbeddedCurvePoint, EmbeddedCurveScalar, multi_scalar_mul};
use total::ec::{msm_or, Point};
use total::schnorr::schnorr_verify;

/// A point in std's form: (0, 0) is infinity.
fn point(x: Field, y: Field) -> Point {
    Point { x, y, inf: (x == 0) & (y == 0) }
}

/// The solver's MSM on the same inputs. The Prover files hold valid
/// points and canonical scalars only.
unconstrained fn reference<let N: u32>(
    x: [Field; N],
    y: [Field; N],
    lo: [Field; N],
    hi: [Field; N],
) -> (Field, Field) {
    let mut pts = [EmbeddedCurvePoint::point_at_infinity(); N];
    let mut scs = [EmbeddedCurveScalar::new(0, 0); N];
    for i in 0..N {
        pts[i] = EmbeddedCurvePoint { x: x[i], y: y[i] };
        scs[i] = EmbeddedCurveScalar::new(lo[i], hi[i]);
    }
    let r = multi_scalar_mul(pts, scs);
    (r.x, r.y)
}

fn check_msm<let N: u32>(
    x: [Field; N],
    y: [Field; N],
    lo: [Field; N],
    hi: [Field; N],
) -> (Field, Field) {
    let mut pts = [Point::infinity(); N];
    for i in 0..N {
        pts[i] = point(x[i], y[i]);
    }
    let (r, ok) = msm_or(pts, lo, hi);
    assert(ok);
    // Safety: a reference value, compared below.
    let (rx, ry) = unsafe { reference(x, y, lo, hi) };
    assert_eq(r.x, rx);
    assert_eq(r.y, ry);
    (r.x, r.y)
}

fn main(
    x1: [Field; 1],
    y1: [Field; 1],
    lo1: [Field; 1],
    hi1: [Field; 1],
    x2: [Field; 2],
    y2: [Field; 2],
    lo2: [Field; 2],
    hi2: [Field; 2],
    pk_x: Field,
    pk_y: Field,
    sig: [Field; 4],
    msg: Field,
    valid: bool,
) -> pub (Field, Field, Field, Field, bool) {
    let (ax, ay) = check_msm(x1, y1, lo1, hi1);
    let (bx, by) = check_msm(x2, y2, lo2, hi2);
    let v = schnorr_verify(pk_x, pk_y, sig, msg);
    assert_eq(v, valid);
    (ax, ay, bx, by, v)
}
