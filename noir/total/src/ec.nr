//! Grumpkin, the curve embedded in bn254: y^2 = x^3 - 17 over the
//! circuit's Field. Points are decoded with flags, added with complete
//! affine formulas, and multiplied by a double-and-add ladder. Nothing in
//! this module calls an elliptic-curve blackbox except msm_or, which
//! validates its inputs and blinds the bases it passes to the MSM black box
//! (see msm_or).
//!
//! Facts the code relies on, each pinned by a test:
//! - x^3 = 17 has no root in this Field (17^((p-1)/3) != 1, test
//!   seventeen_is_not_a_cube). So no finite point has y = 0, there is no
//!   point of order 2, and the doubling denominator 2y is nonzero for every
//!   finite point on the curve. The code still routes that denominator
//!   through arith::inverse_or and maps a zero denominator to infinity, so
//!   correctness does not rest on the fact.
//! - The group order is the prime q = ORDER_LO + 2^128 * ORDER_HI, the
//!   bn254 base-field modulus. Sources: the ACVM solver checks scalars
//!   against ark_grumpkin::FrConfig::MODULUS (noir 1.0.0-rc.3, commit 5a7ee9b,
//!   acvm-repo/bn254_blackbox_solver/src/embedded_curve_ops.rs), and
//!   @aztec-labs/foundation 6.0.0 defines GrumpkinScalar = Fq with
//!   Fq.MODULUS = 0x30644e72...d87cfd47 (dest/curves/grumpkin/index.js and
//!   dest/curves/bn254/field.js). The test order_kills_generator runs the
//!   ladder on the bits of q and gets infinity.
//! - q > p (the Field modulus). A Field scalar s is an integer below p, so
//!   it never wraps mod q, but scalars in [p, q) cannot be written as one
//!   Field: mul_limbs_or takes the two-limb form that std's
//!   EmbeddedCurveScalar uses. q and p share their high 128-bit limb.
//!
//! Point representation: Point { x, y, inf }. A Point is well-formed when
//! inf is true and x = y = 0, or inf is false and (x, y) is on the curve.
//! decode_or and decode_xy_or produce only well-formed Points, and add,
//! double, sub, mul_or, mul_limbs_or and msm_or map well-formed Points to
//! well-formed Points. Every entry is total for every input, including
//! malformed Points built directly through the public fields; on those the
//! result is defined but meaningless. Well-formedness is the decoders' job.
//!
//! On ok = false every Point-valued entry returns infinity, which serves
//! as Point's zero value: its coordinates are 0 and it is the group
//! identity, where a zeroed Point (0, 0, inf = false) would be malformed.
//! scalar_limbs_or returns zero limbs.
//!
//! Where std::embedded_curve_ops can fail (read from the std source at that
//! commit and from the ACVM solver source named above):
//! - The Noir code in embedded_curve_ops.nr has no assert. Every failure
//!   source is inside the two foreign blackboxes it calls.
//! - embedded_curve_add, used by EmbeddedCurvePoint `+`, `-`, double() and
//!   embedded_curve_add(): witness generation fails when either input is
//!   neither (0, 0) nor on the curve ("Point (..) is not on curve"), and
//!   would fail for a point outside the prime-order subgroup (vacuous here:
//!   the cofactor is 1).
//! - multi_scalar_mul, used by multi_scalar_mul() and
//!   fixed_base_scalar_mul(): the same point check, plus each scalar limb
//!   must be below 2^128 ("Limb .. is not less than 2^128") and
//!   lo + 2^128*hi must be below q ("is not a valid grumpkin scalar").
//! - Both blackboxes carry a predicate, so under a false branch condition
//!   they are skipped. The proving
//!   backend's constraints for these opcodes are backend-defined; treat the
//!   solver's conditions as the minimum it rejects.
//! - The backend rejects more. bb 6.0.0's MSM gadget asserts, for witness
//!   bases, that the x-coordinates of the points its incomplete additions
//!   combine differ, against public points of its own (msm_or's doc
//!   comment has the two families of assertions). Valid points and
//!   scalars in a known relation to those public points pass the solver
//!   and have no proof: for example a base equal to one of them. msm_or
//!   never hands the MSM black box an input's point directly; the blinding
//!   it uses instead is described at msm_or. bb's embedded_curve_add
//!   gadget uses complete formulas and asserts nothing of the kind; this
//!   module does not call it.
//! - Total parts of std: EmbeddedCurveScalar::from_field (bn254::decompose,
//!   and every Field is below q, so the scalar is always valid),
//!   is_infinite, point_at_infinity, neg, generator, Eq.
//! - std uses (0, 0) for infinity. (0, 0) is not on the curve (0 != -17),
//!   so that encoding is unambiguous; decode_xy_or accepts it.
//!
//! What replaces what: decode_or / decode_xy_or replace an on-curve
//! assert; add, double and sub replace `+`, double() and `-` with pure
//! arithmetic; mul_or and mul_limbs_or replace scalar multiplication with
//! an in-circuit ladder; msm_or wraps the MSM blackbox behind validation
//! and blinding.
//!
//! Gadgets used: core::eq / is_zero (the inversion gadget), arith::
//! inverse_or, core::limbs, core::fits_128, core::lt_bounded::<128> on
//! values already below 2^128, convert::to_le_bits_total, convert::bool_or, std
//! to_le_bits on limbs already below 2^128. Every one is hint-satisfiable
//! for every input under the preconditions stated at its call site, and
//! every flag built from them is determined. msm_or adds hints of its own
//! (ec/msm_hint.nr: two blinding points and a correction scalar); its
//! constraint half, msm_with_hints, is tested with wrong hints.
//!
//! Cost: the ladder is one double, one add and one select per scalar
//! bit. For a full-width scalar msm_or costs several times fewer gates,
//! at the price of trusting the backend's MSM gadget to be sound on the
//! blinded inputs; most of its cost is that gadget's own fixed cost (bb
//! 6.0.0 circuit size of a program taking the inputs as entry-point
//! Fields: 4704 gates for one term, 5348 for two, 5992 for three). A
//! windowed or GLV ladder is not provided.

mod msm_hint;
pub(crate) mod msm_tests;

use crate::arith::inverse_or;
use crate::convert::{bool_or, to_le_bits_total};
use crate::core::{eq, fits_128, INV_TWO_POW_128, is_zero, limbs, lt_bounded, select_field};
use crate::ctl::Select;
use msm_hint::msm_hints;
use std::cmp::Eq;
use std::embedded_curve_ops::{EmbeddedCurvePoint, EmbeddedCurveScalar, multi_scalar_mul};

/// The curve constant b in y^2 = x^3 + b: b = -17.
pub global CURVE_B: Field = 0 - 17;

/// Low 128-bit limb of the Grumpkin group order q.
pub global ORDER_LO: Field = 201385395114098847380338600778089168199;

/// High 128-bit limb of the Grumpkin group order q (below 2^126; equal to
/// the high limb of the Field modulus).
pub global ORDER_HI: Field = 64323764613183177041862057485226039389;

/// A Grumpkin point in affine coordinates with an explicit infinity flag.
/// See the module header for well-formedness. At a trust boundary take
/// three Fields and call decode_or rather than a Point parameter: an
/// entry-point bool gets an unconditional booleanity range check, which is
/// input-falsifiable.
pub struct Point {
    pub x: Field,
    pub y: Field,
    pub inf: bool,
}

impl Point {
    /// The point at infinity, Point { 0, 0, true }. Constants only.
    pub fn infinity() -> Point {
        Point { x: 0, y: 0, inf: true }
    }

    /// The Grumpkin generator (1, sqrt(-16)) from
    /// std::embedded_curve_ops. Constants only.
    pub fn generator() -> Point {
        let g = EmbeddedCurvePoint::generator();
        Point { x: g.x, y: g.y, inf: false }
    }

    /// -P = (x, -y). Infinity stays infinity (its y is 0). Total: one
    /// arithmetic definition.
    pub fn neg(self) -> Point {
        Point { x: self.x, y: 0 - self.y, inf: self.inf }
    }

    /// The std representation: (0, 0) for infinity, else (x, y). The
    /// coordinates are masked by !inf so the result is (0, 0) for any
    /// infinity Point. Total: two Field selects.
    pub fn to_embedded(self) -> EmbeddedCurvePoint {
        EmbeddedCurvePoint {
            x: select_field(self.inf, 0, self.x),
            y: select_field(self.inf, 0, self.y),
        }
    }
}

/// Field-wise selection. Total: two Field selects and one bool select.
impl Select for Point {
    fn select(c: bool, t: Point, f: Point) -> Point {
        Point {
            x: select_field(c, t.x, f.x),
            y: select_field(c, t.y, f.y),
            inf: bool::select(c, t.inf, f.inf),
        }
    }
}

/// Group equality: both infinity, or both finite with equal coordinates.
/// The coordinates of infinity Points are ignored. Total: two eq gadgets
/// (hint-satisfiable for every input) and bool arithmetic; determined.
impl Eq for Point {
    fn eq(self, other: Point) -> bool {
        let same_xy = eq(self.x, other.x) & eq(self.y, other.y);
        (self.inf & other.inf) | (!self.inf & !other.inf & same_xy)
    }
}

/// Flag: (x, y) satisfies y^2 = x^3 - 17.
///
/// Constraints: arithmetic definitions for y^2 and x^3 and one eq gadget
/// (hint-satisfiable for every input). Determined.
pub fn on_curve_flag(x: Field, y: Field) -> bool {
    eq(y * y, x * x * x + CURVE_B)
}

/// Flag: p is well-formed (inf with zero coordinates, or finite and on the
/// curve). Use it to re-check a Point that did not come from a decoder.
///
/// Constraints: on_curve_flag, two is_zero gadgets, bool select. All
/// hint-satisfiable for every input; determined.
pub fn is_well_formed(p: Point) -> bool {
    let zero_xy = is_zero(p.x) & is_zero(p.y);
    bool::select(p.inf, zero_xy, on_curve_flag(p.x, p.y))
}

/// Decode a point given as three Fields (x, y, inf). Returns (point, ok).
/// ok is true exactly when inf is 0 or 1, and either inf = 1 and
/// x = y = 0, or inf = 0 and (x, y) is on the curve. On ok = false the
/// point is infinity. Never asserts: an off-curve point, a nonzero
/// coordinate under inf = 1, and an inf value outside {0, 1} are all
/// reported through ok.
///
/// Constraints: convert::bool_or on inf (two eq gadgets), on_curve_flag,
/// two is_zero gadgets, bool arithmetic and one Point select. All
/// hint-satisfiable for every input. Determined: every flag is.
pub fn decode_or(x: Field, y: Field, inf: Field) -> (Point, bool) {
    let (claim_inf, inf_ok) = bool_or(inf);
    let zero_xy = is_zero(x) & is_zero(y);
    let on = on_curve_flag(x, y);
    let ok = inf_ok & bool::select(claim_inf, zero_xy, on);
    let finite = ok & !claim_inf;
    (Point::select(finite, Point { x, y, inf: false }, Point::infinity()), ok)
}

/// Decode a point in std's two-coordinate form, where (0, 0) means
/// infinity. Returns (point, ok): ok is true for (0, 0) and for points on
/// the curve; on ok = false the point is infinity.
///
/// Constraints: two is_zero gadgets, on_curve_flag, bool arithmetic and
/// one Point select. Hint-satisfiable for every input; determined.
pub fn decode_xy_or(x: Field, y: Field) -> (Point, bool) {
    let zero_xy = is_zero(x) & is_zero(y);
    let on = on_curve_flag(x, y);
    (Point::select(on, Point { x, y, inf: false }, Point::infinity()), zero_xy | on)
}

/// P + Q, complete for well-formed points: handles infinity on either
/// side, doubling, P = -Q and the generic chord in one formula with
/// selects instead of branches.
///
/// lambda = num / den with (num, den) = (3x1^2, 2y1) when x1 = x2, else
/// (y2 - y1, x2 - x1); den goes through inverse_or. x3 = lambda^2 - x1 - x2
/// and y3 = lambda*(x1 - x3) - y1 serve both the doubling and the chord.
/// The finite result is replaced by infinity when x1 = x2 and not
/// (y1 = y2 and den != 0): that is P = -Q, or a doubling with y = 0. For
/// x1 != x2 the denominator is nonzero, so inverse_or's flag is true there.
/// Then infinity on either input selects the other input.
///
/// Constraints: two eq gadgets (x1 = x2, y1 = y2), inverse_or (two
/// equations on a hinted inverse and a hinted bool, hint-satisfiable for
/// every input), arithmetic definitions, three Point selects. No
/// precondition: total for every pair of Points. The output is determined
/// (the flags and the masked inverse are). Correct when both inputs are
/// well-formed; the output is then well-formed.
pub fn add(p: Point, q: Point) -> Point {
    let x_eq = eq(p.x, q.x);
    let y_eq = eq(p.y, q.y);
    let num = select_field(x_eq, 3 * p.x * p.x, q.y - p.y);
    let den = select_field(x_eq, 2 * p.y, q.x - p.x);
    let (inv, den_ok) = inverse_or(den);
    let lambda = num * inv;
    let x3 = lambda * lambda - p.x - q.x;
    let y3 = lambda * (p.x - x3) - p.y;
    let fin_inf = x_eq & !(y_eq & den_ok);
    let r = Point::select(
        fin_inf,
        Point::infinity(),
        Point { x: x3, y: y3, inf: false },
    );
    let r = Point::select(q.inf, p, r);
    Point::select(p.inf, q, r)
}

/// 2P. lambda = 3x^2 / 2y with 2y through inverse_or; the result is
/// infinity when p is infinity or 2y = 0 (which no finite curve point
/// has, see the module header). Equal to add(p, p) on well-formed points,
/// at lower cost.
///
/// Constraints: inverse_or (hint-satisfiable for every input), arithmetic
/// definitions, one Point select. Total for every Point; determined.
pub fn double(p: Point) -> Point {
    let (inv, ok) = inverse_or(2 * p.y);
    let lambda = 3 * p.x * p.x * inv;
    let x3 = lambda * lambda - 2 * p.x;
    let y3 = lambda * (p.x - x3) - p.y;
    Point::select(
        p.inf | !ok,
        Point::infinity(),
        Point { x: x3, y: y3, inf: false },
    )
}

/// P - Q = add(P, -Q). Same constraints and guarantees as add.
pub fn sub(p: Point, q: Point) -> Point {
    add(p, q.neg())
}

/// Double-and-add over little-endian bits, most significant first:
/// r = 2r, then r = r + p where the bit is set (select, no branch).
/// Returns [sum of bits[i] * 2^i] p. Total for every input; constraints are
/// those of N doubles, N adds and N Point selects. The bits are the
/// caller's; every caller passes determined bits.
pub(crate) fn ladder<let N: u32>(p: Point, bits: [bool; N]) -> Point {
    let mut r = Point::infinity();
    for k in 0..N {
        let i = N - 1 - k;
        r = double(r);
        let t = add(r, p);
        r = Point::select(bits[i], t, r);
    }
    r
}

/// [s]P for a scalar given as one Field and bounded to MAX_BITS bits
/// (1 <= MAX_BITS <= 254). Returns (point, ok): ok = s < 2^MAX_BITS as an
/// integer; on ok = false the point is infinity, the product by the
/// clamped scalar 0. With MAX_BITS = 254 every Field is accepted (ok is
/// always true) and s is its canonical integer, which is below p < q, so
/// it never wraps mod q. Scalars in [p, q) need mul_limbs_or.
///
/// Constraints: for MAX_BITS > 128, convert::to_le_bits_total (canonical
/// limbs and their bit decompositions, hint-satisfiable for every Field);
/// for MAX_BITS <= 128, core::limbs and std to_le_bits::<128> on the low
/// limb (below 2^128 by the limbs range checks, so the decomposition
/// exists and is unique) plus is_zero on the high limb. ok is the AND of
/// the negated bits at positions >= MAX_BITS (and of hi == 0): bool
/// arithmetic on determined bits. Then ladder over the low MAX_BITS bits
/// and one Point select. Total for every Point and Field; determined.
/// Cost: one double, one add and one select per bit.
pub fn mul_or<let MAX_BITS: u32>(p: Point, s: Field) -> (Point, bool) {
    std::static_assert(
        (MAX_BITS >= 1) & (MAX_BITS <= 254),
        "mul_or: MAX_BITS must be in 1..=254",
    );
    let (all, hi_ok) = if MAX_BITS > 128 {
        (to_le_bits_total(s), true)
    } else {
        let (lo, hi) = limbs(s);
        let lo_bits: [bool; 128] = lo.to_le_bits();
        let mut a = [false; 254];
        for i in 0..128 {
            a[i] = lo_bits[i];
        }
        (a, is_zero(hi))
    };
    let mut bits = [false; MAX_BITS];
    for i in 0..MAX_BITS {
        bits[i] = all[i];
    }
    let mut ok = hi_ok;
    for i in MAX_BITS..254 {
        ok = ok & !all[i];
    }
    (Point::select(ok, ladder(p, bits), Point::infinity()), ok)
}

/// Flag and clamp for a Grumpkin scalar in two 128-bit limbs: returns
/// (lo', hi', ok) with ok = lo < 2^128, hi < 2^128 and lo + 2^128*hi < q,
/// exactly the conditions under which the std MSM blackbox accepts the
/// scalar (see the module header). On ok = false, lo' = hi' = 0.
///
/// Constraints: core::fits_128 on each limb (canonical limbs and an
/// is_zero gadget, hint-satisfiable for every Field); core::lt_bounded::<128> twice and
/// one eq gadget on the limbs clamped below 2^128, which meets lt_bounded's
/// precondition (ORDER_LO and ORDER_HI are below 2^128 too); bool
/// arithmetic; two Field selects. Determined.
pub fn scalar_limbs_or(lo: Field, hi: Field) -> (Field, Field, bool) {
    let lo_ok = fits_128(lo);
    let hi_ok = fits_128(hi);
    let lo_c = select_field(lo_ok, lo, 0);
    let hi_c = select_field(hi_ok, hi, 0);
    let below = lt_bounded::<128>(hi_c, ORDER_HI)
        | (eq(hi_c, ORDER_HI) & lt_bounded::<128>(lo_c, ORDER_LO));
    let ok = lo_ok & hi_ok & below;
    (select_field(ok, lo, 0), select_field(ok, hi, 0), ok)
}

/// [s]P for a full Grumpkin scalar s = lo + 2^128*hi, the layout of std's
/// EmbeddedCurveScalar. Returns (point, ok) with ok from scalar_limbs_or
/// (each limb below 2^128 and s < q); on ok = false the point is infinity.
///
/// Constraints: scalar_limbs_or; std to_le_bits::<128> on the clamped low
/// limb and to_le_bits::<126> on the clamped high limb. When ok holds the
/// limbs are below 2^128 and ORDER_HI < 2^126, and when it fails they are
/// 0, so both decompositions exist and are unique (hint-satisfiable for
/// every input). Then ladder over the 254 bits. Total for every Point and
/// limb pair; determined.
pub fn mul_limbs_or(p: Point, lo: Field, hi: Field) -> (Point, bool) {
    let (lo_c, hi_c, ok) = scalar_limbs_or(lo, hi);
    let lo_bits: [bool; 128] = lo_c.to_le_bits();
    let hi_bits: [bool; 126] = hi_c.to_le_bits();
    let mut bits = [false; 254];
    for i in 0..128 {
        bits[i] = lo_bits[i];
    }
    for i in 0..126 {
        bits[128 + i] = hi_bits[i];
    }
    (Point::select(ok, ladder(p, bits), Point::infinity()), ok)
}

/// Largest number of terms msm_or takes (constrain_msm_correction's carry
/// and multiple bounds).
pub global MSM_MAX_TERMS: u32 = 32767;

/// Bias that makes constrain_msm_correction's signed carry nonnegative.
global CARRY_BIAS: Field = 0x8000;

/// Constraint half of msm_or's correction scalar, split out so tests can
/// feed wrong hints. Forces t_lo + 2^128 t_hi + sum of (lo[i] + 2^128
/// hi[i]) = k*q as an integer identity. PRECONDITION: every lo[i], hi[i]
/// is below 2^128 (msm_or passes scalar_limbs_or's outputs) and N <=
/// MSM_MAX_TERMS. Emits RANGE t_lo and t_hi to 128 bits, RANGE k to 16
/// bits, the carry c = (L - k*q_lo) / 2^128 with L = t_lo + sum lo[i],
/// RANGE c + 2^15 to 16 bits, and H + c == k*q_hi with H = t_hi + sum
/// hi[i]. With N + 1 <= 2^15 summands below 2^128, L and H are below
/// 2^143; k*q_lo and k*q_hi are below 2^144 and |c*2^128| below 2^143.
/// So the Field equations L - k*q_lo = c*2^128 and H + c = k*q_hi hold
/// as integer equations, and together give L + 2^128 H = k*q.
/// Hint-satisfiable: for t the canonical representative of -sum mod q,
/// k = (t + sum)/q <= N and c lies in (-N, N + 1).
pub(crate) fn constrain_msm_correction<let N: u32>(
    lo: [Field; N],
    hi: [Field; N],
    t_lo: Field,
    t_hi: Field,
    k: Field,
) {
    t_lo.assert_max_bit_size::<128>();
    t_hi.assert_max_bit_size::<128>();
    k.assert_max_bit_size::<16>();
    let mut l = t_lo;
    let mut h = t_hi;
    for i in 0..N {
        l += lo[i];
        h += hi[i];
    }
    let c = (l - k * ORDER_LO) * INV_TWO_POW_128;
    (c + CARRY_BIAS).assert_max_bit_size::<16>();
    assert(h + c == k * ORDER_HI, "msm_or: correction scalar");
}

/// Constraint half of msm_or, split out so tests can feed wrong hints:
/// everything but the choice of the blinds b0, b1 and the correction
/// t = (t_lo, t_hi, k). PRECONDITION: every pts[i] is well-formed and
/// every (lo[i], hi[i]) has limbs below 2^128 (msm_or passes validated or
/// substituted values). Returns the sum of [lo[i] + 2^128 hi[i]] pts[i]
/// for EVERY b0, b1, t its assertions accept (msm_or has the argument).
///
/// Emits: two curve equations (b0 and b1 on the curve, so both finite:
/// (0, 0) is not on it), constrain_msm_correction, one complete add per
/// term, the MSM black box on N + 2 terms, two is_zero gadgets reading
/// its result and one complete add.
pub(crate) fn msm_with_hints<let N: u32>(
    pts: [Point; N],
    lo: [Field; N],
    hi: [Field; N],
    b0: (Field, Field),
    b1: (Field, Field),
    t: (Field, Field, Field),
) -> Point {
    assert(b0.1 * b0.1 == b0.0 * b0.0 * b0.0 + CURVE_B, "msm_or: blind 0 not on the curve");
    assert(b1.1 * b1.1 == b1.0 * b1.0 * b1.0 + CURVE_B, "msm_or: blind 1 not on the curve");
    constrain_msm_correction(lo, hi, t.0, t.1, t.2);
    let blind1 = Point { x: b1.0, y: b1.1, inf: false };
    let mut bases = [EmbeddedCurvePoint::point_at_infinity(); N + 2];
    let mut scs = [EmbeddedCurveScalar::new(0, 0); N + 2];
    // B0 first, with the scalar q - 1 (msm_or's totality argument).
    bases[0] = EmbeddedCurvePoint { x: b0.0, y: b0.1 };
    scs[0] = EmbeddedCurveScalar::new(ORDER_LO - 1, ORDER_HI);
    bases[1] = EmbeddedCurvePoint { x: b1.0, y: b1.1 };
    scs[1] = EmbeddedCurveScalar::new(t.0, t.1);
    for i in 0..N {
        bases[i + 2] = add(pts[i], blind1).to_embedded();
        scs[i + 2] = EmbeddedCurveScalar::new(lo[i], hi[i]);
    }
    let r = multi_scalar_mul(bases, scs);
    let rp = Point { x: r.x, y: r.y, inf: is_zero(r.x) & is_zero(r.y) };
    add(rp, Point { x: b0.0, y: b0.1, inf: false })
}

/// Sum of [s_i]P_i through std's multi_scalar_mul black box, with every
/// input validated and every base blinded. Returns (point, ok): ok =
/// every point is well-formed and every scalar passes scalar_limbs_or; on
/// ok = false the point is infinity. N <= MSM_MAX_TERMS (a static
/// assertion).
///
/// Validation: the black box's solver fails witness generation on an
/// invalid point or scalar, so each invalid point is replaced by infinity
/// and each invalid scalar by 0 first (the select-to-dummy pattern).
///
/// What the backend asserts. bb 6.0.0 lowers the black box to
/// cycle_group::batch_mul; with witness bases that is a Straus MSM with
/// 4-bit windows (64 rounds), built from incomplete additions guarded by
/// assertions that the two x-coordinates differ. o_0, o_1, ... are public
/// points of bb's (its offset generators, hashed to the curve); base j of
/// the call uses o_{j+1} and the accumulator starts at o_0. The assertions:
/// - table: base j's entries o_{j+1} + i Q_j (i = 0..15) are built by
///   repeated addition, asserting x(o_{j+1} + (i-1) Q_j) != x(Q_j) for
///   i = 1..15. Scalar-independent: Q_j = o_{j+1} or -(1/15) o_{j+1}
///   fails for every scalar;
/// - accumulator: in each round, after four doublings, each base's entry
///   for the current 4-bit digit of its scalar is added, asserting that
///   its x differs from the accumulator's. Points and scalars together:
///   for example a sum equal to minus the total offset the accumulator
///   carries fails in the last round.
/// The final removal of the offsets uses a complete subtraction. Valid
/// inputs in such a relation to the o_k pass the solver and have no
/// proof; anyone who knows bb's constants can build them.
///
/// Blinding. msm_or takes two hinted points B0, B1 and a hinted
/// correction scalar t (ec/msm_hint.nr) and calls the black box on
///   bases   [B0,     B1,  P_1 + B1, ..., P_N + B1]
///   scalars [q - 1,  t,   s_1,      ..., s_N     ]
/// with P_i + B1 from the complete add, then returns add(result, B0).
///
/// Soundness: for every hint the constraints accept, the output is
/// sum s_i P_i. They force B0 and B1 onto the curve and t + sum s_i = k*q
/// as integers (constrain_msm_correction), so the black box returns
/// (q - 1) B0 + t B1 + sum s_i (P_i + B1)
///   = -B0 + (t + sum s_i) B1 + sum s_i P_i = sum s_i P_i - B0,
/// and the complete add of B0 gives sum s_i P_i. The hints decide only
/// whether the black box's constraints can be met, never the output or
/// ok; this rests on bb's gadget being sound (it computes
/// the MSM or is unsatisfiable).
///
/// Totality: for every input an accepted hint exists, and the honest hint
/// is one except with negligible probability. Write each assertion as a
/// group relation over B0, B1, the P_i and the o_k.
/// - A table relation reads o_{j+1} = m Q_j with m in {i - 2, -i}. For
///   m = 0 it says o_{j+1} is the identity, which is false. Otherwise Q_j
///   is B0, B1 or P_i + B1, so the relation fixes B0 or B1 to at most one
///   value given the inputs (P_i + B1 = infinity takes bb's infinity path,
///   whose table checks compare fixed points only).
/// - In an accumulator relation the coefficient of B0 is the value of a
///   prefix of q - 1's base-16 digits (times 16, plus or minus the
///   current digit when base 0 is the one added): an integer strictly
///   between 0 and q, because B0 comes first and q - 1's top digit is 3.
///   So given B1 and the inputs it fixes B0 to at most one value.
/// There are 158 (N + 2) relations, so for every input fewer than
/// 158 (N + 2) blind values are excluded out of q > 2^253. t and k exist
/// for every input (constrain_msm_correction). The honest hint takes
/// B0 = [s0]G and B1 = [s1]G with s0, s1 from a Poseidon2 hash of every
/// input the black box sees, 2^252 possible values each: for inputs the
/// adversary picks, the honest blinds are excluded with probability below
/// 158 (N + 2) / 2^252 when Poseidon2 is modelled as a random function,
/// so making them excluded means a search of that order. The hints
/// themselves are trap-free for every input, including infinity points,
/// zero scalars and substituted invalid inputs (ec/msm_hint.nr).
///
/// Constraints: is_well_formed per point and scalar_limbs_or per scalar
/// (hint-satisfiable for every input), Point selects, msm_with_hints
/// (accepted for every input, above), one Point select. Determined: the
/// flags are, and the output is the same for every accepted hint.
pub fn msm_or<let N: u32>(points: [Point; N], lo: [Field; N], hi: [Field; N]) -> (Point, bool) {
    std::static_assert(N <= MSM_MAX_TERMS, "msm_or: at most MSM_MAX_TERMS terms");
    let mut pts = [Point::infinity(); N];
    let mut lo_c = [0; N];
    let mut hi_c = [0; N];
    let mut ok = true;
    for i in 0..N {
        let pv = is_well_formed(points[i]);
        let (l, h, sv) = scalar_limbs_or(lo[i], hi[i]);
        pts[i] = Point::select(pv, points[i], Point::infinity());
        lo_c[i] = l;
        hi_c[i] = h;
        ok = ok & pv & sv;
    }
    // Safety: msm_with_hints returns the same point for every blind pair
    // and correction its assertions accept (see above), and these hints
    // are accepted.
    let (b0, b1, t) = unsafe { msm_hints(pts, lo_c, hi_c) };
    let r = msm_with_hints(pts, lo_c, hi_c, b0, b1, t);
    (Point::select(ok, r, Point::infinity()), ok)
}

mod tests {
    use crate::core::{two_pow, TWO_POW_128};
    use super::{
        add, CURVE_B, decode_or, decode_xy_or, double, is_well_formed, ladder, msm_or, mul_limbs_or,
        mul_or, on_curve_flag, ORDER_HI, ORDER_LO, Point, scalar_limbs_or, sub,
    };
    use std::embedded_curve_ops::{
        embedded_curve_add, EmbeddedCurvePoint, EmbeddedCurveScalar, multi_scalar_mul,
    };

    global P_MINUS_1: Field = 0 - 1;

    fn g() -> Point {
        Point::generator()
    }

    fn from_std(e: EmbeddedCurvePoint) -> Point {
        let (p, ok) = decode_xy_or(e.x, e.y);
        assert(ok);
        p
    }

    /// The std MSM of one point, as the oracle for the ladder.
    fn std_mul(p: Point, lo: Field, hi: Field) -> Point {
        from_std(
            multi_scalar_mul([p.to_embedded()], [EmbeddedCurveScalar::new(lo, hi)]),
        )
    }

    unconstrained fn pow_field(b: Field, e: Field) -> Field {
        let bits: [bool; 254] = e.to_le_bits();
        let mut r: Field = 1;
        for i in 0..254 {
            r = r * r;
            if bits[253 - i] {
                r = r * b;
            }
        }
        r
    }

    // x^3 = 17 has a root iff 17^((p-1)/3) == 1 (p = 1 mod 3). It does
    // not, so no finite Grumpkin point has y = 0.
    #[test]
    unconstrained fn seventeen_is_not_a_cube() {
        let e = (0 - 1) / 3;
        assert_eq(e * 3, P_MINUS_1);
        assert(pow_field(17, e) != 1);
        // control: a cube passes the same test
        assert_eq(pow_field(8, e), 1);
    }

    #[test]
    fn generator_and_constants() {
        let gen = g();
        assert(on_curve_flag(gen.x, gen.y));
        assert(is_well_formed(gen));
        assert(is_well_formed(Point::infinity()));
        assert_eq(CURVE_B + 17, 0);
        // q and p share the high limb; q's low limb is larger
        assert_eq(ORDER_HI, 64323764613183177041862057485226039389);
        assert(!on_curve_flag(0, 0));
        assert(!on_curve_flag(1, 1));
        assert(!on_curve_flag(gen.x, gen.y + 1));
    }

    // The ladder over the bits of q returns infinity: q is a multiple of
    // the generator's order, consistent with the cited group order.
    #[test]
    fn order_kills_generator() {
        let lo_bits: [bool; 128] = ORDER_LO.to_le_bits();
        let hi_bits: [bool; 126] = ORDER_HI.to_le_bits();
        let mut bits = [false; 254];
        for i in 0..128 {
            bits[i] = lo_bits[i];
        }
        for i in 0..126 {
            bits[128 + i] = hi_bits[i];
        }
        assert(ladder(g(), bits).inf);
    }

    #[test]
    fn decode_or_valid_and_infinity() {
        let gen = g();
        let (p, ok) = decode_or(gen.x, gen.y, 0);
        assert(ok);
        assert_eq(p, gen);
        assert(!p.inf);
        let (i, ok_i) = decode_or(0, 0, 1);
        assert(ok_i);
        assert(i.inf);
        assert_eq(i.x, 0);
        assert_eq(i.y, 0);
    }

    #[test]
    fn decode_or_adversarial() {
        let gen = g();
        // off-curve
        let (p, ok) = decode_or(1, 1, 0);
        assert(!ok);
        assert(p.inf);
        assert_eq(p.x, 0);
        // (0, 0) without the infinity claim is off-curve
        let (p0, ok0) = decode_or(0, 0, 0);
        assert(!ok0);
        assert(p0.inf);
        // bad infinity encodings: nonzero coordinates under inf = 1
        let (p1, ok1) = decode_or(gen.x, gen.y, 1);
        assert(!ok1);
        assert(p1.inf);
        assert_eq(p1.y, 0);
        let (p2, ok2) = decode_or(0, 1, 1);
        assert(!ok2);
        assert(p2.inf);
        // inf outside {0, 1}
        let (p3, ok3) = decode_or(gen.x, gen.y, 2);
        assert(!ok3);
        assert(p3.inf);
        let (p4, ok4) = decode_or(0, 0, P_MINUS_1);
        assert(!ok4);
        assert(p4.inf);
        // p - 1 coordinates
        let (p5, ok5) = decode_or(P_MINUS_1, P_MINUS_1, 0);
        assert(!ok5);
        assert(p5.inf);
    }

    #[test]
    fn decode_xy_or_cases() {
        let gen = g();
        let (p, ok) = decode_xy_or(gen.x, gen.y);
        assert(ok);
        assert_eq(p, gen);
        let (i, oki) = decode_xy_or(0, 0);
        assert(oki);
        assert(i.inf);
        let (b, okb) = decode_xy_or(1, 1);
        assert(!okb);
        assert(b.inf);
        let (b2, okb2) = decode_xy_or(0, gen.y);
        assert(!okb2);
        assert(b2.inf);
    }

    #[test]
    fn to_embedded_masks_infinity() {
        let e = Point { x: 5, y: 7, inf: true }.to_embedded();
        assert(e.is_infinite());
        let ge = g().to_embedded();
        assert_eq(ge, EmbeddedCurvePoint::generator());
    }

    #[test]
    fn add_matches_std() {
        let gen = g();
        let eg = EmbeddedCurvePoint::generator();
        let g2 = add(gen, gen);
        assert_eq(g2, from_std(eg.double()));
        assert_eq(double(gen), g2);
        let g3 = add(g2, gen);
        assert_eq(g3, from_std(embedded_curve_add(eg.double(), eg)));
        assert_eq(add(gen, g2), g3);
        // associativity on a mixed triple
        let g5 = add(g2, g3);
        assert_eq(add(add(gen, g2), g3), add(gen, add(g2, g3)));
        assert_eq(sub(g5, g2), g3);
        assert(is_well_formed(g5));
    }

    #[test]
    fn add_infinity_cases() {
        let gen = g();
        let inf = Point::infinity();
        assert_eq(add(gen, inf), gen);
        assert_eq(add(inf, gen), gen);
        let ii = add(inf, inf);
        assert(ii.inf);
        assert_eq(ii.x, 0);
        let z = add(gen, gen.neg());
        assert(z.inf);
        assert_eq(z.x, 0);
        assert_eq(z.y, 0);
        assert(sub(gen, gen).inf);
        assert(double(inf).inf);
    }

    // Malformed Points: every entry still returns a defined value.
    #[test]
    fn add_total_on_malformed() {
        // same x, y = 0, off-curve: doubling denominator is zero
        let bad = Point { x: 5, y: 0, inf: false };
        let d = double(bad);
        assert(d.inf);
        let a = add(bad, bad);
        assert(a.inf);
        // same x, unrelated y: treated as P = -Q
        let r = add(
            Point { x: 1, y: 2, inf: false },
            Point { x: 1, y: 3, inf: false },
        );
        assert(r.inf);
        // arbitrary off-curve chord: defined, finite
        let c = add(
            Point { x: 1, y: 1, inf: false },
            Point { x: 2, y: 2, inf: false },
        );
        assert(!c.inf);
        // infinity flag with junk coordinates selects the other side
        let j = add(Point { x: 9, y: 9, inf: true }, g());
        assert_eq(j, g());
    }

    #[test]
    fn mul_or_small_scalars() {
        let gen = g();
        let (z, okz) = mul_or::<8>(gen, 0);
        assert(okz);
        assert(z.inf);
        let (one, ok1) = mul_or::<8>(gen, 1);
        assert(ok1);
        assert_eq(one, gen);
        let (two, ok2) = mul_or::<8>(gen, 2);
        assert(ok2);
        assert_eq(two, double(gen));
        let (m, okm) = mul_or::<8>(gen, 255);
        assert(okm);
        assert_eq(m, std_mul(gen, 255, 0));
        // infinity times anything is infinity
        let (ii, okii) = mul_or::<8>(Point::infinity(), 77);
        assert(okii);
        assert(ii.inf);
    }

    #[test]
    fn mul_or_bound_adversarial() {
        let gen = g();
        let (a, oka) = mul_or::<8>(gen, 256);
        assert(!oka);
        assert(a.inf);
        let (b, okb) = mul_or::<8>(gen, 257);
        assert(!okb);
        assert(b.inf);
        let (c, okc) = mul_or::<8>(gen, P_MINUS_1);
        assert(!okc);
        assert(c.inf);
        let (d, okd) = mul_or::<8>(gen, TWO_POW_128);
        assert(!okd);
        assert(d.inf);
    }

    #[test]
    fn mul_or_limb_boundary() {
        let gen = g();
        let (a, oka) = mul_or::<128>(gen, TWO_POW_128 - 1);
        assert(oka);
        assert_eq(a, std_mul(gen, TWO_POW_128 - 1, 0));
        let (b, okb) = mul_or::<128>(gen, TWO_POW_128);
        assert(!okb);
        assert(b.inf);
        let (c, okc) = mul_or::<129>(gen, TWO_POW_128);
        assert(okc);
        assert_eq(c, std_mul(gen, 0, 1));
        let (d, okd) = mul_or::<129>(gen, two_pow::<129>());
        assert(!okd);
        assert(d.inf);
    }

    #[test]
    fn mul_or_full_width() {
        let gen = g();
        // p - 1, the largest Field scalar, against the std MSM
        let (a, oka) = mul_or::<254>(gen, P_MINUS_1);
        assert(oka);
        let s = EmbeddedCurveScalar::from_field(P_MINUS_1);
        assert_eq(a, std_mul(gen, s.lo, s.hi));
        let x = 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcd;
        let (b, okb) = mul_or::<254>(gen, x);
        assert(okb);
        let sx = EmbeddedCurveScalar::from_field(x);
        assert_eq(b, std_mul(gen, sx.lo, sx.hi));
        let (z, okz) = mul_or::<254>(gen, 0);
        assert(okz);
        assert(z.inf);
    }

    #[test]
    fn scalar_limbs_flags() {
        let (lo, hi, ok) = scalar_limbs_or(ORDER_LO - 1, ORDER_HI);
        assert(ok);
        assert_eq(lo, ORDER_LO - 1);
        assert_eq(hi, ORDER_HI);
        let (lo2, hi2, ok2) = scalar_limbs_or(ORDER_LO, ORDER_HI);
        assert(!ok2);
        assert_eq(lo2, 0);
        assert_eq(hi2, 0);
        assert(!scalar_limbs_or(ORDER_LO + 1, ORDER_HI).2);
        assert(!scalar_limbs_or(0, ORDER_HI + 1).2);
        assert(scalar_limbs_or(TWO_POW_128 - 1, ORDER_HI - 1).2);
        assert(!scalar_limbs_or(TWO_POW_128, 0).2);
        assert(!scalar_limbs_or(0, TWO_POW_128).2);
        assert(!scalar_limbs_or(P_MINUS_1, 0).2);
        assert(scalar_limbs_or(0, 0).2);
    }

    #[test]
    fn mul_limbs_or_order_boundary() {
        let gen = g();
        // q - 1 gives -G
        let (a, oka) = mul_limbs_or(gen, ORDER_LO - 1, ORDER_HI);
        assert(oka);
        assert_eq(a, gen.neg());
        assert_eq(a, std_mul(gen, ORDER_LO - 1, ORDER_HI));
        // q and above are rejected with infinity
        let (b, okb) = mul_limbs_or(gen, ORDER_LO, ORDER_HI);
        assert(!okb);
        assert(b.inf);
        let (c, okc) = mul_limbs_or(gen, ORDER_LO + 1, ORDER_HI);
        assert(!okc);
        assert(c.inf);
        // s = 1 and s = 0
        let (d, okd) = mul_limbs_or(gen, 1, 0);
        assert(okd);
        assert_eq(d, gen);
        let (e, oke) = mul_limbs_or(gen, 0, 0);
        assert(oke);
        assert(e.inf);
        // limbs out of range
        let (f, okf) = mul_limbs_or(gen, TWO_POW_128, 0);
        assert(!okf);
        assert(f.inf);
    }

    #[test]
    fn msm_or_matches_and_validates() {
        let gen = g();
        let g2 = double(gen);
        let (a, oka) = msm_or([gen, g2], [3, 5], [0, 0]);
        assert(oka);
        // 3G + 10G = 13G
        let (b, _) = mul_or::<8>(gen, 13);
        assert_eq(a, b);
        // cancelling terms give infinity with ok
        let (c, okc) = msm_or([gen, gen.neg()], [1, 1], [0, 0]);
        assert(okc);
        assert(c.inf);
        // q - 1 through the blackbox
        let (d, okd) = msm_or([gen], [ORDER_LO - 1], [ORDER_HI]);
        assert(okd);
        assert_eq(d, gen.neg());
    }

    // Inputs that make std's multi_scalar_mul fail witness generation give
    // ok = false and infinity here.
    #[test]
    fn msm_or_adversarial() {
        let gen = g();
        let off = Point { x: 1, y: 1, inf: false };
        let (a, oka) = msm_or([off], [1], [0]);
        assert(!oka);
        assert(a.inf);
        let (b, okb) = msm_or([gen], [ORDER_LO], [ORDER_HI]);
        assert(!okb);
        assert(b.inf);
        let (c, okc) = msm_or([gen], [TWO_POW_128], [0]);
        assert(!okc);
        assert(c.inf);
        let bad_inf = Point { x: 3, y: 0, inf: true };
        let (d, okd) = msm_or([bad_inf, gen], [1, 1], [0, 0]);
        assert(!okd);
        assert(d.inf);
    }
}
