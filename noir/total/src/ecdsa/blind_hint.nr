//! The honest hint of blind.nr: a blind (e, b') and every witness of the
//! constraints C1-C5 for it.
//!
//! Candidates come from Poseidon2 over a domain tag, the 160 input bytes
//! (packed into eight Fields) and a counter t = 0, 1, ...: candidate t is
//! the scalar v_t = (low 128 bits of p2_hash([tag, seed, t, 0])) +
//! 2^128 (low 128 bits of p2_hash([tag, seed, t, 1])), reduced mod n
//! (every residue has probability 2^-256 or 2^-255).
//! - When r != 0 mod n, v_t is the scalar u1 = z'/s the black box will
//!   multiply G by, and the blind is the residue beta = (z - s v_t) / r
//!   that produces it (s read as 1 when it is 0 mod n, as bb does).
//! - When r == 0 mod n the blind cannot move u1 (it is z/s for every
//!   blind) and beta = v_t.
//! beta is written as e b' with b' = o + D in blind.nr's range (blind.nr,
//! C1: always possible for beta != 0). The hint takes the first candidate
//! that
//! 1. has beta != 0 and x(B) != x(Q), which C3 and C4 need (false for at
//!    most three values of beta), and
//! 2. passes the emulation of the black box's multiplication on
//!    (Q', u1, u2): k1_emul.nr on secp256k1, r1_emul.nr on secp256r1.
//! It tries at most TRIES candidates and otherwise returns the last one,
//! a well-formed hint whose proof may fail (docs/ecdsa-totality.md bounds
//! how often).
//!
//! Every other witness follows from the blind: the chain A_j of C3 is
//! computed with mixed Jacobian additions (the affine slope of each step
//! is r / Z3 in madd's terms) and one batch inversion; the key addition
//! by affine formulas; the quotients of close() by bignum.nr's
//! close_quotient; the slacks as m - 1 - v. With the blind fixed, these
//! satisfy C1-C5 for every input (blind.nr's header, and the honest
//! witness argument of close()).
//!
//! Trap-free for every argument, including off-curve keys, zero or
//! out-of-range scalars and all-0xff bytes: bignum.nr's operations, the
//! Poseidon2 black box, constant-bound loops with constant or
//! loop-counter indices (table indices reduced mod the table size), and
//! no assertion. The emulations run only for a key on the curve (an
//! off-curve key never reaches this hint from the wrappers, which pass
//! the dummy instead).
//!
//! Cost (Brillig opcodes): ecdsa.nr's header.

use crate::hash::p2_hash;
use super::bignum::{
    batch_inv, bits_le, close_quotient, ext5, from_be, from_fields, from_mont, geq, inv_mont,
    is_zero4, mmul, negmod, reduce_once, sub4, submod, to_fields, to_mont, wadd5, wmul5, wprod,
    wsub5,
};
use super::blind::{BlindHint, SecpCurve, select_point, window_bits};
use super::k1_emul::{Jac, k1_bad, k1_on_curve, k1_u2_wnafs, madd, Wnaf};
use super::r1_emul::{r1_bad, r1_on_curve};

/// Candidate blinds tried before giving up (docs/ecdsa-totality.md, T2).
pub(crate) global TRIES: u32 = 256;
/// Domain tag: "total-ecdsa-blind" as a big-endian integer.
global BLIND_DST: Field = 0x746f74616c2d65636473612d626c696e64;

/// The seed: Poseidon2 of the 160 input bytes packed 20 per Field.
unconstrained fn seed_of(qx: [u8; 32], qy: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> Field {
    let mut all = [0; 160];
    for i in 0..32 {
        all[i] = qx[i];
        all[32 + i] = qy[i];
        all[128 + i] = hash[i];
    }
    for i in 0..64 {
        all[64 + i] = sig[i];
    }
    let mut packed = [0; 8];
    for i in 0..8 {
        let mut v: Field = 0;
        for j in 0..20 {
            v = v * 256 + (all[20 * i + j] as Field);
        }
        packed[i] = v;
    }
    p2_hash(packed)
}

/// Candidate ctr's scalar v (module header), below n.
unconstrained fn derive_scalar(seed: Field, ctr: u32, n: [u64; 4]) -> [u64; 4] {
    let h0: [u8; 32] = p2_hash([BLIND_DST, seed, ctr as Field, 0]).to_be_bytes();
    let h1: [u8; 32] = p2_hash([BLIND_DST, seed, ctr as Field, 1]).to_be_bytes();
    let a = from_be(h0);
    let b = from_be(h1);
    reduce_once([a[0], a[1], b[0], b[1]], n)
}

/// The blind (bits of D, sign) with e (o + D) == beta mod n, for
/// 0 < beta < n (blind.nr, C1): D = beta - o mod n when that is below
/// 15 * 16^63, else D = -beta - o mod n with the sign set.
unconstrained fn blind_repr<C>(beta: [u64; 4]) -> ([Field; 256], bool, [u64; 4])
where
    C: SecpCurve,
{
    let n = C::n_mont().m;
    let o = C::blind_o();
    let mut dd = submod(beta, o, n);
    let mut sign = false;
    if geq(dd, C::blind_lim()) {
        dd = submod(negmod(beta, n), o, n);
        sign = true;
    }
    let b = bits_le(dd);
    let mut bits = [0; 256];
    for i in 0..256 {
        bits[i] = b[i] as Field;
    }
    (bits, sign, dd)
}

/// One candidate: the chain of C3 and the key addition of C4, in
/// Montgomery form, and the table points in plain form.
struct Candidate {
    bits: [Field; 256],
    /// Table points T_w, plain limbs.
    xs: [[u64; 4]; 64],
    ys: [[u64; 4]; 64],
    /// Affine x of A_j (j = 0..63) and slopes of steps 1..63, Montgomery.
    xa: [[u64; 4]; 64],
    lam: [[u64; 4]; 63],
    yb: [u64; 4],
    /// x(B) != x(Q): the key addition below is meaningful.
    ok: bool,
    inv: [u64; 4],
    lam_a: [u64; 4],
    x2: [u64; 4],
    y2: [u64; 4],
}

/// The chain and key addition for the bits, against the key (xq, yq) in
/// Montgomery form.
unconstrained fn candidate<C>(
    bits: [Field; 256],
    sign: bool,
    xq: [u64; 4],
    yq: [u64; 4],
) -> Candidate
where
    C: SecpCurve,
{
    let kp = C::p_mont();
    let p = kp.m;
    let fb = C::fb();
    let mut xs = [[0; 4]; 64];
    let mut ys = [[0; 4]; 64];
    let mut xm = [[0; 4]; 64];
    let mut ym = [[0; 4]; 64];
    for w in 0..64 {
        let (x, y) = select_point(fb[w], window_bits(bits, w));
        xs[w] = from_fields(x);
        ys[w] = from_fields(y);
        xm[w] = to_mont(xs[w], kp);
        ym[w] = to_mont(ys[w], kp);
    }
    let mut acc: Jac = [xm[0], ym[0], kp.one];
    let mut big_x = [[0; 4]; 63];
    let mut zs = [[0; 4]; 64];
    let mut rs = [[0; 4]; 63];
    for j in 1..64 {
        let (t, _, r) = madd(acc, xm[j], ym[j], kp);
        big_x[j - 1] = t[0];
        zs[j - 1] = t[2];
        rs[j - 1] = r;
        acc = t;
    }
    // x(B) - x(Q) = -h / Z_B^2 with h = x_Q Z_B^2 - X_B; Z_B h joins the
    // batch inversion, and 1 / (x(B) - x(Q)) = -Z_B^3 / (Z_B h)
    let zb = acc[2];
    let zb2 = mmul(zb, zb, kp);
    let h = submod(mmul(xq, zb2, kp), acc[0], p);
    let ok = !is_zero4(h);
    zs[63] = mmul(zb, h, kp);
    let zi = batch_inv(zs, kp);
    let mut xa = [[0; 4]; 64];
    let mut lam = [[0; 4]; 63];
    xa[0] = xm[0];
    for j in 1..64 {
        let z2 = mmul(zi[j - 1], zi[j - 1], kp);
        xa[j] = mmul(big_x[j - 1], z2, kp);
        lam[j - 1] = mmul(rs[j - 1], zi[j - 1], kp);
    }
    let z63 = zi[62];
    let yb = mmul(acc[1], mmul(z63, mmul(z63, z63, kp), kp), kp);
    let inv = negmod(mmul(mmul(zb2, zb, kp), zi[63], kp), p);
    // Q' = Q + e B: the slope uses e y_B
    let yb_e = if sign { negmod(yb, p) } else { yb };
    let lam_a = mmul(submod(yb_e, yq, p), inv, kp);
    let x2 = submod(submod(mmul(lam_a, lam_a, kp), xq, p), xa[63], p);
    let y2 = submod(mmul(lam_a, submod(xq, x2, p), kp), yq, p);
    Candidate { bits, xs, ys, xa, lam, yb, ok, inv, lam_a, x2, y2 }
}

/// a (b - c) mod 2^320, the difference taken mod 2^320 (a ring, so this
/// is a b - a c).
unconstrained fn mul_diff(a: [u64; 4], b: [u64; 4], c: [u64; 4]) -> [u64; 5] {
    wmul5(ext5(a), wsub5(ext5(b), ext5(c)))
}

/// m - 1 - v for v < m.
unconstrained fn slack(v: [u64; 4], m: [u64; 4]) -> [Field; 4] {
    to_fields(sub4(sub4(m, [1, 0, 0, 0]).0, v).0)
}

/// The honest hint (module header).
pub(crate) unconstrained fn blind_hint<C>(
    qx: [u8; 32],
    qy: [u8; 32],
    sig: [u8; 64],
    hash: [u8; 32],
) -> BlindHint
where
    C: SecpCurve,
{
    blind_hint_from::<C>(qx, qy, sig, hash, 0, false).0
}

/// The hint starting at candidate `first`, and the number of candidates
/// it rejected. reject_all (tests only) rejects every candidate, which
/// exercises the exhausted-retries path.
pub(crate) unconstrained fn blind_hint_from<C>(
    qx: [u8; 32],
    qy: [u8; 32],
    sig: [u8; 64],
    hash: [u8; 32],
    first: u32,
    reject_all: bool,
) -> (BlindHint, u32)
where
    C: SecpCurve,
{
    let kp = C::p_mont();
    let kn = C::n_mont();
    let p = kp.m;
    let n = kn.m;
    let seed = seed_of(qx, qy, sig, hash);
    let xq = from_be(qx);
    let yq = from_be(qy);
    let xq_m = to_mont(reduce_once(xq, p), kp);
    let yq_m = to_mont(reduce_once(yq, p), kp);
    let mut rb = [0; 32];
    let mut sb = [0; 32];
    for i in 0..32 {
        rb[i] = sig[i];
        sb[i] = sig[32 + i];
    }
    let r = from_be(rb);
    let z = from_be(hash);
    let r_n = reduce_once(r, n);
    let z_n = reduce_once(z, n);
    // s as bb reads it (0 mod n as 1), u2 = r/s, and 1/r when r != 0
    let mut s_n = reduce_once(from_be(sb), n);
    if is_zero4(s_n) {
        s_n = [1, 0, 0, 0];
    }
    let s_m = to_mont(s_n, kn);
    let s_inv = inv_mont(s_m, kn);
    let u2 = mmul(s_inv, r_n, kn);
    let r_zero = is_zero4(r_n);
    let r_inv = inv_mont(to_mont(r_n, kn), kn);
    let u1_fixed = mmul(s_inv, z_n, kn);
    let is_k1 = C::is_k1();
    let on_curve = if is_k1 {
        k1_on_curve(xq_m, yq_m)
    } else {
        r1_on_curve(xq_m, yq_m)
    };
    let mut w2lo = Wnaf { d: [(1, false); 33], frag: (0, false), skew: false, skew_minus: false };
    let mut w2hi = w2lo;
    if is_k1 {
        let (lo, hi) = k1_u2_wnafs(u2);
        w2lo = lo;
        w2hi = hi;
    }
    let mut c = Candidate {
        bits: [0; 256],
        xs: [[0; 4]; 64],
        ys: [[0; 4]; 64],
        xa: [[0; 4]; 64],
        lam: [[0; 4]; 63],
        yb: [0; 4],
        ok: false,
        inv: [0; 4],
        lam_a: [0; 4],
        x2: [0; 4],
        y2: [0; 4],
    };
    let mut sign = false;
    let mut dd = [0; 4];
    let mut zq = [0; 4];
    let mut rejected: u32 = 0;
    for t in 0..TRIES {
        let v = derive_scalar(seed, first + t, n);
        // beta and the u1 the black box will see
        let (beta, u1) = if r_zero {
            (v, u1_fixed)
        } else {
            (mmul(r_inv, submod(z_n, mmul(s_m, v, kn), n), kn), v)
        };
        let (bits, sg, d) = blind_repr::<C>(beta);
        sign = sg;
        dd = d;
        c = candidate::<C>(bits, sg, xq_m, yq_m);
        // z' = z - e r b' = z - r beta mod n
        zq = submod(z_n, mmul(to_mont(r_n, kn), beta, kn), n);
        let mut good = c.ok & !is_zero4(beta);
        if good & on_curve & !reject_all {
            good = if is_k1 {
                !k1_bad(c.x2, c.y2, u1, w2lo, w2hi)
            } else {
                !r1_bad(c.x2, c.y2, u1, u2)
            };
        }
        if good & !reject_all {
            break;
        }
        rejected += 1;
    }
    // plain values and the quotients of close()
    let mut lam = [[0; 4]; 63];
    let mut xa = [[0; 4]; 64];
    for j in 0..64 {
        xa[j] = from_mont(c.xa[j], kp);
    }
    for j in 0..63 {
        lam[j] = from_mont(c.lam[j], kp);
    }
    let xs = c.xs;
    let ys = c.ys;
    let yb = from_mont(c.yb, kp);
    let mut h_lam = [[0; 4]; 63];
    let mut h_x = [[0; 4]; 63];
    let mut q_lam = [[0; 4]; 63];
    let mut q_x = [[0; 4]; 63];
    for j in 1..64 {
        let l = lam[j - 1];
        let mut f = wsub5(mul_diff(l, xs[j], xa[j - 1]), ext5(ys[j]));
        if j == 1 {
            f = wadd5(f, ext5(ys[0]));
        } else {
            f = wsub5(
                wadd5(f, mul_diff(lam[j - 2], xs[j - 1], xa[j - 1])),
                ext5(ys[j - 1]),
            );
        }
        q_lam[j - 1] = close_quotient(f, kp);
        let g = wsub5(
            wsub5(wsub5(wprod(l, l), ext5(xa[j - 1])), ext5(xs[j])),
            ext5(xa[j]),
        );
        q_x[j - 1] = close_quotient(g, kp);
        h_lam[j - 1] = to_fields(l);
        h_x[j - 1] = to_fields(xa[j]);
    }
    let f_yb = wsub5(
        wsub5(mul_diff(lam[62], xs[63], xa[63]), ext5(ys[63])),
        ext5(yb),
    );
    let xb = xa[63];
    let inv = from_mont(c.inv, kp);
    let la = from_mont(c.lam_a, kp);
    let x2 = from_mont(c.x2, kp);
    let y2 = from_mont(c.y2, kp);
    let f_inv = wsub5(mul_diff(inv, xb, xq), [1, 0, 0, 0, 0]);
    // la (x_B - x_Q) - e y_B + y_Q
    let f_la0 = wadd5(mul_diff(la, xb, xq), ext5(yq));
    let f_la = if sign {
        wadd5(f_la0, ext5(yb))
    } else {
        wsub5(f_la0, ext5(yb))
    };
    let f_xa = wsub5(wsub5(wsub5(wprod(la, la), ext5(xq)), ext5(xb)), ext5(x2));
    let f_ya = wsub5(wsub5(mul_diff(la, xq, x2), ext5(yq)), ext5(y2));
    // e r b' + z' - z with b' = o + D as an integer (below 2^257)
    let rb5 = wmul5(ext5(r), wadd5(ext5(dd), ext5(C::blind_o())));
    let zdiff = wsub5(ext5(zq), ext5(z));
    let f_z = if sign {
        wsub5(zdiff, rb5)
    } else {
        wadd5(zdiff, rb5)
    };
    let hint = BlindHint {
        bits: c.bits,
        sign: sign as Field,
        lam: h_lam,
        x: h_x,
        q_lam,
        q_x,
        yb: to_fields(yb),
        q_yb: close_quotient(f_yb, kp),
        inv: to_fields(inv),
        q_inv: close_quotient(f_inv, kp),
        lam_a: to_fields(la),
        q_lam_a: close_quotient(f_la, kp),
        q_x_a: close_quotient(f_xa, kp),
        q_y_a: close_quotient(f_ya, kp),
        key_x: to_fields(x2),
        key_y: to_fields(y2),
        slack_x: slack(x2, p),
        slack_y: slack(y2, p),
        hash: to_fields(zq),
        q_hash: close_quotient(f_z, kn),
        slack_hash: slack(zq, n),
    };
    (hint, rejected)
}

/// The emulation on the unblinded inputs (ecdsa.nr's diagnostics): u1 =
/// z/s and u2 = r/s as bb derives them, on the key as given.
pub(crate) unconstrained fn raw_bad<C>(
    qx: [u8; 32],
    qy: [u8; 32],
    sig: [u8; 64],
    hash: [u8; 32],
) -> bool
where
    C: SecpCurve,
{
    let kp = C::p_mont();
    let kn = C::n_mont();
    let n = kn.m;
    let xq = to_mont(reduce_once(from_be(qx), kp.m), kp);
    let yq = to_mont(reduce_once(from_be(qy), kp.m), kp);
    let mut rb = [0; 32];
    let mut sb = [0; 32];
    for i in 0..32 {
        rb[i] = sig[i];
        sb[i] = sig[32 + i];
    }
    let mut s_n = reduce_once(from_be(sb), n);
    if is_zero4(s_n) {
        s_n = [1, 0, 0, 0];
    }
    let s_inv = inv_mont(to_mont(s_n, kn), kn);
    let u1 = mmul(s_inv, reduce_once(from_be(hash), n), kn);
    let u2 = mmul(s_inv, reduce_once(from_be(rb), n), kn);
    if C::is_k1() {
        let (lo, hi) = k1_u2_wnafs(u2);
        k1_bad(xq, yq, u1, lo, hi)
    } else {
        r1_bad(xq, yq, u1, u2)
    }
}
