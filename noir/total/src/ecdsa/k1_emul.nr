//! The secp256k1 part of the blind hint: an emulation of bb 6.0.0's
//! secp256k1 ECDSA multiplication that says, for a blinded key Q' and
//! scalars u1, u2, whether bb's own witness violates one of the
//! multiplication's assertions. Unconstrained; nothing here is a soundness
//! argument (blind.nr's constraints accept every blind).
//!
//! What bb does (stdlib/primitives/biggroup at aztec-packages v6.0.0,
//! commit 0219f11d; the full list of source facts, the proof and its
//! assumptions are in docs/ecdsa-totality.md). secp256k1_ecdsa_mul(Q', u1,
//! u2) splits u1 and u2 with the endomorphism (k = k_lo - lambda k_hi),
//! writes the four halves as signed odd-digit wNAFs with a stagger
//! fragment and a skew each (u1: 8-bit digits, staggers 2 and 3; u2:
//! 4-bit digits, staggers 0 and 1), builds the table Q', 3Q', ..., 15Q'
//! with one doubling and seven complete additions, starts the accumulator
//! at the first u2_lo digit's multiple of Q', runs 16 rounds of two
//! doublings and six Montgomery-ladder steps A <- 2A + P, and finishes
//! with three complete additions of the fragments and four of the skew
//! bases (each skew addition is computed whether or not the skew is set).
//!
//! Which assertions depend on the witness:
//! - Each ladder step asserts x(A) != x(P) and x(A) != x(A + P)
//!   (multiple_montgomery_ladder). Equal x-coordinates mean A = P, A = -P
//!   or 2A + P = O.
//! - bigfield::assert_is_not_equal compares the two integers only modulo
//!   the circuit's native modulus N (BN254's scalar field), times factors
//!   for a few multiples of p: it also fails when the integers differ by
//!   k p + j N with j != 0 although the values differ mod p ("aliasing").
//!   Both ladder checks have this form, and so has the zero check of
//!   every division: the divisor 2y of each doubling and the divisor
//!   x2 - x1 (or 2y, in its doubling branch) of each complete addition.
//!   The values of k differ by kind of site (table_k1.nr's K1_ALIAS_*
//!   tables; scripts/gen_ecdsa_tables.py says which and why).
//! Everything else on the path holds for every input the wrappers pass
//! (docs/ecdsa-totality.md).
//!
//! k1_bad follows bb's computation on the actual points and reports any
//! of these. The ladder runs in Jacobian coordinates; the affine
//! coordinates the aliasing checks need come from one batch inversion at
//! its end. The seven closing additions run in affine coordinates with
//! bb's case split (infinity operand, doubling, inverse points).
//!
//! The honest hint (blind_hint.nr) calls k1_bad for every candidate
//! blind on secp256k1 and moves to the next candidate when it returns
//! true. scripts/ecdsa_differential.py compares this predicate (through a
//! Python model of the same computation) with bb prove in both
//! directions. If bb's multiplication changes, soundness is unaffected
//! (blind.nr's constraints do not depend on bb's internals) but this
//! emulation and the proof must be redone (CONTRIBUTING.md).

use super::bignum::{
    add4, addmod, batch_inv, eq4, from_mont, inv_mont, is_zero4, mmul, Mont, mul512, mulmod, negmod,
    reduce_once, sub4, submod,
};
use super::table_k1::{
    K1_ALIAS_ADD_A, K1_ALIAS_ADD_B, K1_ALIAS_ADD_C, K1_ALIAS_DBL_2, K1_ALIAS_DBL_3, K1_ALIAS_DBL_4,
    K1_ALIAS_INC, K1_BETA_MONT, K1_ENDO_B2, K1_ENDO_G1, K1_ENDO_G2, K1_ENDO_MINUS_B1, K1_G_ODD,
    K1_LAMBDA, K1_N_MONT, K1_P_MONT,
};

/// A signed wNAF digit: (magnitude, negative), magnitude odd.
pub(crate) type Digit = (u64, bool);

/// One half-scalar as bb decomposes it (compute_secp256k1_single_wnaf):
/// the ladder digits most significant first (entries beyond the round
/// count stay (1, false)), the stagger fragment as a signed odd digit
/// ((0, false) when the stagger is 0: bb adds no fragment then), and the
/// skew: whether it is set and whether bb then adds minus the base
/// (negative_skew, for a non-negative half) or the base (positive_skew,
/// for a half taken as minus n - k).
pub(crate) struct Wnaf {
    pub(crate) d: [Digit; 33],
    pub(crate) frag: Digit,
    pub(crate) skew: bool,
    pub(crate) skew_minus: bool,
}

/// bb's field::split_into_endomorphism_scalars (the large-modulus path)
/// for k < n: (k_lo, k_hi) with k = k_lo - lambda k_hi mod n.
pub(crate) unconstrained fn k1_split(k: [u64; 4]) -> ([u64; 4], [u64; 4]) {
    let kn = K1_N_MONT;
    let n = kn.m;
    let c1 = mul512(K1_ENDO_G2, k);
    let c2 = mul512(K1_ENDO_G1, k);
    let q1 = mul512([c1[4], c1[5], c1[6], c1[7]], K1_ENDO_MINUS_B1);
    let q2 = mul512([c2[4], c2[5], c2[6], c2[7]], K1_ENDO_B2);
    let a = reduce_once([q2[0], q2[1], q2[2], q2[3]], n);
    let b = reduce_once([q1[0], q1[1], q1[2], q1[3]], n);
    let k_hi = submod(a, b, n);
    let k_lo = addmod(mulmod(k_hi, K1_LAMBDA, kn), reduce_once(k, n), n);
    (k_lo, k_hi)
}

/// (lo + hi 2^128) >> s as (low 128 bits, the rest), for s < 128. Below
/// 2^128 each: lo / 2^s < 2^(128 - s) and (hi mod 2^s) 2^(128 - s) <=
/// (2^s - 1) 2^(128 - s).
unconstrained fn shr_wide(lo: u128, hi: u128, s: u32) -> (u128, u128) {
    if s == 0 {
        (lo, hi)
    } else {
        let d: u128 = (1 as u128) << (s as u128);
        let up: u128 = (1 as u128) << ((128 - s) as u128);
        (lo / d + (hi % d) * up, hi / d)
    }
}

/// One half-scalar as bb computes it (compute_secp256k1_single_wnaf over
/// fixed_wnaf, get_staggered_wnaf_fragment_value); W is the digit width
/// and ST the stagger, the round count is (129 + W - 1 - ST) / W. A half
/// of 130 bits or more is taken as minus n - k (bb's split never leaves
/// either magnitude at 2^129 or above: docs/ecdsa-totality.md).
/// Trap-free: a_lo is incremented only when even, so never past
/// 2^128 - 1; wp - d >= 1; the index is below the round count <= 33;
/// fv + 1 <= 2^ST <= 8.
unconstrained fn k1_wnaf<let W: u32, let ST: u32>(k_in: [u64; 4]) -> Wnaf {
    let n = K1_N_MONT.m;
    let neg = (k_in[3] != 0) | (k_in[2] >= 2);
    let k = if neg { sub4(n, k_in).0 } else { k_in };
    let rounds = (129 + W - 1 - ST) / W;
    let lo: u128 = (k[0] as u128) + (k[1] as u128) * 0x10000000000000000;
    let hi: u128 = (k[2] as u128) + (k[3] as u128) * 0x10000000000000000;
    let st_pow: u64 = (1 as u64) << (ST as u64);
    let frag_u = k[0] % st_pow;
    let (lo_s, hi_s) = shr_wide(lo, hi, ST);
    let mut a_lo = lo_s;
    let mut a_hi = hi_s;
    let wskew = a_lo % 2 == 0;
    if wskew {
        a_lo += 1;
    }
    let wp: u128 = (1 as u128) << (W as u128);
    let mut out = [(1, false); 33];
    for i in 0..rounds {
        let mut d = a_lo % wp;
        let mut dneg = false;
        let (nl, nh) = shr_wide(a_lo, a_hi, W);
        a_lo = nl;
        a_hi = nh;
        if (i + 1 < rounds) & (a_lo % 2 == 0) {
            d = wp - d;
            dneg = true;
            a_lo += 1;
        }
        out[rounds - 1 - i] = (d as u64, dneg != neg);
    }
    if ST == 0 {
        Wnaf { d: out, frag: (0, false), skew: wskew, skew_minus: !neg }
    } else {
        // the fragment of the magnitude: frag_u - 2^ST [wskew] + 1 [frag_u
        // even], odd; its sign flips with the half's
        let oskew = frag_u % 2 == 0;
        let fv = frag_u + (oskew as u64);
        let sub = if wskew { st_pow } else { 0 };
        let frag = if fv >= sub {
            (fv - sub, neg)
        } else {
            (sub - fv, !neg)
        };
        Wnaf { d: out, frag, skew: oskew, skew_minus: !neg }
    }
}

/// u2's halves, (u2_lo, u2_hi).
pub(crate) unconstrained fn k1_u2_wnafs(u2: [u64; 4]) -> (Wnaf, Wnaf) {
    let (lo, hi) = k1_split(u2);
    (k1_wnaf::<4, 0>(lo), k1_wnaf::<4, 1>(hi))
}

/// y^2 == x^3 + 7 for Montgomery-form coordinates.
pub(crate) unconstrained fn k1_on_curve(x: [u64; 4], y: [u64; 4]) -> bool {
    let kp = K1_P_MONT;
    let seven = mmul([7, 0, 0, 0], kp.r2, kp);
    eq4(
        mmul(y, y, kp),
        addmod(mmul(mmul(x, x, kp), x, kp), seven, kp.m),
    )
}

/// A Jacobian point (X, Y, Z), Montgomery form; Z = 0 is not used.
pub(crate) type Jac = [[u64; 4]; 3];

/// Mixed addition A + (x2, y2) (add-2007-bl with Z2 = 1): (A + P, H, r)
/// with H = x2 Z1^2 - X1 (zero exactly when x(A) == x2, for Z1 != 0) and
/// r = y2 Z1^3 - Y1. The affine chord slope is r / Z3. When H = 0 the
/// returned point is meaningless; callers check H first.
pub(crate) unconstrained fn madd(
    a: Jac,
    x2: [u64; 4],
    y2: [u64; 4],
    k: Mont,
) -> (Jac, [u64; 4], [u64; 4]) {
    let m = k.m;
    let z1z1 = mmul(a[2], a[2], k);
    let u2 = mmul(x2, z1z1, k);
    let s2 = mmul(y2, mmul(a[2], z1z1, k), k);
    let h = submod(u2, a[0], m);
    let r = submod(s2, a[1], m);
    let hh = mmul(h, h, k);
    let hhh = mmul(h, hh, k);
    let v = mmul(a[0], hh, k);
    let x3 = submod(submod(mmul(r, r, k), hhh, m), addmod(v, v, m), m);
    let y3 = submod(mmul(r, submod(v, x3, m), k), mmul(a[1], hhh, k), m);
    ([x3, y3, mmul(a[2], h, k)], h, r)
}

/// The ladder's two additions for an accumulator A and an affine table
/// point P: (2A + P, H1, H2, X(A + P), Z(A + P)) with H1 = 0 exactly when
/// x(A) == x(P) and H2 = 0 exactly when x(A) == x(A + P) (Z(A) != 0).
/// A + P is madd's; A rescaled to A + P's Z is (X1 H1^2, Y1 H1^3, Z1 H1),
/// both products already formed by madd, and the second sum is a co-Z
/// addition (H2 = X(A + P) - X1 H1^2, R = Y(A + P) - Y1 H1^3, then the
/// chord formulas with Z3 = Z H2). When H1 = 0 the other outputs are
/// meaningless; callers check H1 first.
unconstrained fn ladder_step(
    a: Jac,
    x2: [u64; 4],
    y2: [u64; 4],
    k: Mont,
) -> (Jac, [u64; 4], [u64; 4], [u64; 4], [u64; 4]) {
    let m = k.m;
    let z1z1 = mmul(a[2], a[2], k);
    let u2 = mmul(x2, z1z1, k);
    let s2 = mmul(y2, mmul(a[2], z1z1, k), k);
    let h = submod(u2, a[0], m);
    let r = submod(s2, a[1], m);
    let hh = mmul(h, h, k);
    let hhh = mmul(h, hh, k);
    let v = mmul(a[0], hh, k);
    let yh = mmul(a[1], hhh, k);
    let tx = submod(submod(mmul(r, r, k), hhh, m), addmod(v, v, m), m);
    let ty = submod(mmul(r, submod(v, tx, m), k), yh, m);
    let tz = mmul(a[2], h, k);
    // co-Z: P1 = (v, yh, tz) is A, P2 = (tx, ty, tz) is A + P
    let h2 = submod(tx, v, m);
    let r2 = submod(ty, yh, m);
    let hh2 = mmul(h2, h2, k);
    let hhh2 = mmul(h2, hh2, k);
    let v2 = mmul(v, hh2, k);
    let x3 = submod(submod(mmul(r2, r2, k), hhh2, m), addmod(v2, v2, m), m);
    let y3 = submod(mmul(r2, submod(v2, x3, m), k), mmul(yh, hhh2, k), m);
    ([x3, y3, mmul(tz, h2, k)], h, h2, tx, tz)
}

/// Doubling for a = 0 (dbl-2009-l).
unconstrained fn jdbl(a: Jac, k: Mont) -> Jac {
    let m = k.m;
    let xx = mmul(a[0], a[0], k);
    let yy = mmul(a[1], a[1], k);
    let yyyy = mmul(yy, yy, k);
    let t = addmod(a[0], yy, m);
    let t2 = submod(submod(mmul(t, t, k), xx, m), yyyy, m);
    let d = addmod(t2, t2, m);
    let e = addmod(addmod(xx, xx, m), xx, m);
    let x3 = submod(mmul(e, e, k), addmod(d, d, m), m);
    let y8 = addmod(yyyy, yyyy, m);
    let y8 = addmod(y8, y8, m);
    let y8 = addmod(y8, y8, m);
    let y3 = submod(mmul(e, submod(d, x3, m), k), y8, m);
    let yz = mmul(a[1], a[2], k);
    [x3, y3, addmod(yz, yz, m)]
}

/// The table point of a digit: the odd multiple (x, y) of the base given
/// by the digit's magnitude, as (beta x, -y) for the endomorphism table,
/// negated for a negative digit (so (beta x, y) for a negative endo
/// digit).
unconstrained fn table_point(base: [[u64; 4]; 2], d: Digit, endo: bool) -> ([u64; 4], [u64; 4]) {
    let kp = K1_P_MONT;
    let x = if endo {
        mmul(base[0], K1_BETA_MONT, kp)
    } else {
        base[0]
    };
    let y = if d.1 != endo {
        negmod(base[1], kp.m)
    } else {
        base[1]
    };
    (x, y)
}

/// Whether (v, flag) is in an aliasing table (table_k1.nr).
pub(crate) unconstrained fn in_table<let M: u32>(
    v: [u64; 4],
    flag: bool,
    t: [([u64; 4], bool); M],
) -> bool {
    let mut hit = false;
    for i in 0..M {
        hit = hit | ((t[i].1 == flag) & eq4(t[i].0, v));
    }
    hit
}

/// Whether the integer difference a - b of two plain values below p is in
/// the table.
pub(crate) unconstrained fn alias_diff<let M: u32>(
    a: [u64; 4],
    b: [u64; 4],
    t: [([u64; 4], bool); M],
) -> bool {
    let (d, borrow) = sub4(a, b);
    in_table(d, borrow != 0, t)
}

/// Whether the integer 2y, y a plain value below p, is in the table.
pub(crate) unconstrained fn alias_two_y<let M: u32>(y: [u64; 4], t: [([u64; 4], bool); M]) -> bool {
    let (v, carry) = add4(y, y);
    in_table(v, carry != 0, t)
}

/// An affine point in Montgomery form, or infinity.
pub(crate) struct Aff {
    pub(crate) x: [u64; 4],
    pub(crate) y: [u64; 4],
    pub(crate) inf: bool,
}

/// bb's complete addition A + P (add_internal) for a finite P, on the
/// curve with coefficient a (am, Montgomery form) and modulus k: the sum
/// and whether the divisor's zero check aliases (ta: the table for
/// x(P) - x(A), td: for 2 y(A)). The divisor is 1 for an infinite A or
/// for P = -A, 2 y(A) for P = A, and x(P) - x(A) otherwise. Trap-free; a
/// divisor that is 0 mod p (y = 0, off the curve only) gives a
/// meaningless sum, never a trap.
pub(crate) unconstrained fn complete_add<let MA: u32, let MD: u32>(
    a: Aff,
    px: [u64; 4],
    py: [u64; 4],
    k: Mont,
    am: [u64; 4],
    ta: [([u64; 4], bool); MA],
    td: [([u64; 4], bool); MD],
) -> (Aff, bool) {
    let m = k.m;
    if a.inf {
        (Aff { x: px, y: py, inf: false }, false)
    } else if eq4(a.x, px) {
        if eq4(a.y, py) {
            let alias = alias_two_y(from_mont(a.y, k), td);
            let xx = mmul(a.x, a.x, k);
            let lam = mmul(
                addmod(addmod(addmod(xx, xx, m), xx, m), am, m),
                inv_mont(addmod(a.y, a.y, m), k),
                k,
            );
            let x3 = submod(submod(mmul(lam, lam, k), a.x, m), a.x, m);
            let y3 = submod(mmul(lam, submod(a.x, x3, m), k), a.y, m);
            (Aff { x: x3, y: y3, inf: false }, alias)
        } else {
            (Aff { x: [0; 4], y: [0; 4], inf: true }, false)
        }
    } else {
        let alias = alias_diff(from_mont(px, k), from_mont(a.x, k), ta);
        let lam = mmul(submod(py, a.y, m), inv_mont(submod(px, a.x, m), k), k);
        let x3 = submod(submod(mmul(lam, lam, k), a.x, m), px, m);
        let y3 = submod(mmul(lam, submod(a.x, x3, m), k), a.y, m);
        (Aff { x: x3, y: y3, inf: false }, alias)
    }
}

/// Whether bb 6.0.0's secp256k1_ecdsa_mul(Q', u1, u2) fails one of its
/// witness-dependent assertions (module header), for the key Q' = (qx,
/// qy) in affine Montgomery form and u1 < n, with u2's halves from
/// k1_u2_wnafs. Returns true also when the key's odd multiples cannot be
/// formed (a key of small order: only off-curve arguments, which the
/// wrappers never pass). Trap-free (bignum.nr; table indices reduced mod
/// the table size).
pub(crate) unconstrained fn k1_bad(
    qx: [u64; 4],
    qy: [u64; 4],
    u1: [u64; 4],
    w2lo: Wnaf,
    w2hi: Wnaf,
) -> bool {
    let kp = K1_P_MONT;
    let (lo, hi) = k1_split(u1);
    let w1lo = k1_wnaf::<8, 2>(lo);
    let w1hi = k1_wnaf::<8, 3>(hi);
    // Q', 3Q', ..., 15Q' in affine form: 2Q' affine, a mixed-addition
    // chain, one batch inversion. bb divides by 2 y(Q') and then by
    // x(2Q') - x((2i - 1) Q') for i = 1..7.
    let mut bad = alias_two_y(from_mont(qy, kp), K1_ALIAS_DBL_2);
    let q1: Jac = [qx, qy, kp.one];
    let q2 = jdbl(q1, kp);
    let z2i = inv_mont(q2[2], kp);
    let z2i2 = mmul(z2i, z2i, kp);
    let q2x = mmul(q2[0], z2i2, kp);
    let q2y = mmul(q2[1], mmul(z2i, z2i2, kp), kp);
    bad = bad | is_zero4(q2[2]);
    let mut jt = [q1; 8];
    for i in 1..8 {
        let (t, h, _) = madd(jt[i - 1], q2x, q2y, kp);
        bad = bad | is_zero4(h);
        jt[i] = t;
    }
    let mut zs = [[0; 4]; 7];
    for i in 0..7 {
        zs[i] = jt[i + 1][2];
    }
    let zi = batch_inv(zs, kp);
    let mut qt = [[qx, qy]; 8];
    let q2x_plain = from_mont(q2x, kp);
    for i in 1..8 {
        bad = bad | alias_diff(q2x_plain, from_mont(qt[i - 1][0], kp), K1_ALIAS_ADD_A);
        let z = zi[i - 1];
        let z2 = mmul(z, z, kp);
        qt[i] = [mmul(jt[i][0], z2, kp), mmul(jt[i][1], mmul(z, z2, kp), kp)];
    }
    let d2lo = w2lo.d;
    let d2hi = w2hi.d;
    let d1lo = w1lo.d;
    let d1hi = w1hi.d;
    let (ax, ay) = table_point(qt[((d2lo[0].0 / 2) as u32) % 8], d2lo[0], false);
    let mut acc: Jac = [ax, ay, kp.one];
    // what the aliasing checks need, converted to affine after the loop:
    // per doubling (Y, Z) of its operand; per ladder step X(A), X(A + P),
    // their Z's and x(P). zall holds the Z's (doublings, then A's, then
    // A + P's, then the final accumulator) for one batch inversion.
    let mut dy = [[0; 4]; 32];
    let mut sx_a = [[0; 4]; 96];
    let mut sx_s = [[0; 4]; 96];
    let mut sx_p = [[0; 4]; 96];
    let mut zall = [kp.one; 225];
    for i in 0..16 {
        if !bad {
            dy[2 * i] = acc[1];
            zall[2 * i] = acc[2];
            acc = jdbl(acc, kp);
            dy[2 * i + 1] = acc[1];
            zall[2 * i + 1] = acc[2];
            acc = jdbl(acc, kp);
            let pts = [
                table_point(qt[((d2hi[2 * i].0 / 2) as u32) % 8], d2hi[2 * i], true),
                table_point(
                    qt[((d2lo[2 * i + 1].0 / 2) as u32) % 8],
                    d2lo[2 * i + 1],
                    false,
                ),
                table_point(K1_G_ODD[((d1hi[i].0 / 2) as u32) % 128], d1hi[i], true),
                table_point(K1_G_ODD[((d1lo[i].0 / 2) as u32) % 128], d1lo[i], false),
                table_point(
                    qt[((d2hi[2 * i + 1].0 / 2) as u32) % 8],
                    d2hi[2 * i + 1],
                    true,
                ),
                table_point(
                    qt[((d2lo[2 * i + 2].0 / 2) as u32) % 8],
                    d2lo[2 * i + 2],
                    false,
                ),
            ];
            for j in 0..6 {
                if !bad {
                    // x(A) == x(P) iff H1 == 0; then x(A) == x(A + P) iff
                    // H2 == 0 (A + P is finite once H1 != 0)
                    let s = 6 * i + j;
                    let (a2, h1, h2, tx, tz) = ladder_step(acc, pts[j].0, pts[j].1, kp);
                    bad = is_zero4(h1) | is_zero4(h2);
                    sx_a[s] = acc[0];
                    zall[32 + s] = acc[2];
                    sx_p[s] = pts[j].0;
                    if !bad {
                        sx_s[s] = tx;
                        zall[128 + s] = tz;
                    }
                    acc = a2;
                }
            }
        }
    }
    if !bad {
        // every Z is nonzero here: the points are finite (no H was zero)
        zall[224] = acc[2];
        let zinv = batch_inv(zall, kp);
        for t in 0..32 {
            let z = zinv[t];
            let y = mmul(dy[t], mmul(z, mmul(z, z, kp), kp), kp);
            // the first doubling of round 0 reads its operand from the ROM
            // table, whose y maximum is larger
            bad = bad
                | if t == 0 {
                    alias_two_y(from_mont(y, kp), K1_ALIAS_DBL_4)
                } else {
                    alias_two_y(from_mont(y, kp), K1_ALIAS_DBL_2)
                };
        }
        for s in 0..96 {
            let za = zinv[32 + s];
            let zs = zinv[128 + s];
            let xa = from_mont(mmul(sx_a[s], mmul(za, za, kp), kp), kp);
            let xs = from_mont(mmul(sx_s[s], mmul(zs, zs, kp), kp), kp);
            bad = bad
                | alias_diff(xa, from_mont(sx_p[s], kp), K1_ALIAS_INC)
                | alias_diff(xa, xs, K1_ALIAS_INC);
        }
        // the closing additions, in bb's order: the fragments of u1_hi,
        // u2_hi and u1_lo, then the skews of u1_lo, u1_hi, u2_lo, u2_hi
        let z = zinv[224];
        let z2 = mmul(z, z, kp);
        let mut a =
            Aff { x: mmul(acc[0], z2, kp), y: mmul(acc[1], mmul(z, z2, kp), kp), inf: false };
        let frags = [
            table_point(K1_G_ODD[((w1hi.frag.0 / 2) as u32) % 128], w1hi.frag, true),
            table_point(qt[((w2hi.frag.0 / 2) as u32) % 8], w2hi.frag, true),
            table_point(K1_G_ODD[((w1lo.frag.0 / 2) as u32) % 128], w1lo.frag, false),
        ];
        // the divisor's range of k differs by site (table_k1.nr)
        for t in 0..3 {
            let (sum, alias) = if t == 2 {
                complete_add(
                    a,
                    frags[t].0,
                    frags[t].1,
                    kp,
                    [0; 4],
                    K1_ALIAS_ADD_B,
                    K1_ALIAS_DBL_4,
                )
            } else {
                complete_add(
                    a,
                    frags[t].0,
                    frags[t].1,
                    kp,
                    [0; 4],
                    K1_ALIAS_ADD_A,
                    K1_ALIAS_DBL_3,
                )
            };
            bad = bad | alias;
            a = sum;
        }
        // conditional_add: accumulator + base with the base negated for a
        // negative skew, evaluated always, selected when the skew is set
        let skews = [
            (K1_G_ODD[0], false, w1lo),
            (K1_G_ODD[0], true, w1hi),
            (qt[0], false, w2lo),
            (qt[0], true, w2hi),
        ];
        for t in 0..4 {
            let (base, endo, w) = skews[t];
            let (bx, by) = table_point(base, (1, w.skew & w.skew_minus), endo);
            let (sum, alias) = if t < 2 {
                complete_add(a, bx, by, kp, [0; 4], K1_ALIAS_ADD_C, K1_ALIAS_DBL_2)
            } else if t == 2 {
                complete_add(a, bx, by, kp, [0; 4], K1_ALIAS_ADD_A, K1_ALIAS_DBL_3)
            } else {
                complete_add(a, bx, by, kp, [0; 4], K1_ALIAS_ADD_B, K1_ALIAS_DBL_4)
            };
            bad = bad | alias;
            if w.skew {
                a = sum;
            }
        }
    }
    bad
}
