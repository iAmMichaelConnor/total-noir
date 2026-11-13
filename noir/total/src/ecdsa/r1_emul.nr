//! The secp256r1 part of the blind hint: an emulation of the parts of bb
//! 6.0.0's secp256r1 ECDSA multiplication whose assertions do not all
//! depend on the blinded key, saying whether bb's own witness violates
//! one of them. Unconstrained; nothing here is a soundness argument.
//!
//! What bb does (stdlib/primitives/biggroup/biggroup_secp256r1.hpp at
//! aztec-packages v6.0.0, commit 0219f11d; the source facts, the proof
//! and its assumptions are in docs/ecdsa-totality.md).
//! secp256r1_ecdsa_mul(Q', u1, u2) computes
//! - T1 = u1 G with secp256r1_fixed_base_mul: 38 table points
//!   L_w = d_w 2^off(w) G + 2^w H (d_w the w-th window of u1, H bb's
//!   "biggroup table offset generator"), summed by a chain of 37
//!   incomplete additions, each asserting distinct x-coordinates, then a
//!   complete subtraction of the constant (2^38 - 1) H;
//! - T2 = u2 Q' as a hinted point (u2 read as 2 when it is 0, 1 or -1),
//!   checked by a 128-bit two-point multiplication on Q' and T2 that
//!   starts from a second generator (the "biggroup offset generator");
//! - T1 + T2 by a complete addition.
//! bigfield::assert_is_not_equal compares integers modulo the circuit's
//! native modulus only (k1_emul.nr's header: "aliasing"); the chain's
//! x-checks and the divisor checks of the complete subtraction and
//! addition have that form (table_r1.nr's R1_ALIAS_* tables).
//!
//! r1_bad follows the fixed-base chain, the offset subtraction and the
//! final addition on the actual points and reports an exact or aliasing
//! failure in any of them. The chain's conditions depend on u1 alone, a
//! fixed set of scalars whatever the key is, and the two complete
//! operations on u1, u2 and Q'. It does not follow the two-point
//! multiplication: every assertion there compares points that move with
//! the blinded key, an exact failure excludes at most 383 keys for given
//! (r, s), and an aliasing failure is covered by the assumption named in
//! docs/ecdsa-totality.md.

use super::bignum::{
    addmod, batch_inv, bits_le, eq4, from_mont, inv_mont, is_zero4, mmul, Mont, submod,
};
use super::k1_emul::{Aff, alias_diff, complete_add, Jac, madd};
use super::table_r1::{
    R1_A_MONT, R1_ALIAS_ADD_A, R1_ALIAS_ADD_C, R1_ALIAS_DBL_2, R1_ALIAS_DBL_3, R1_ALIAS_INC,
    R1_B_MONT, R1_FB_BITS, R1_FB_TOTAL_OFFSET, R1_FB_WINDOWS, R1_N_MONT, R1_P_MONT,
};

/// y^2 == x^3 + a x + b for Montgomery-form coordinates.
pub(crate) unconstrained fn r1_on_curve(x: [u64; 4], y: [u64; 4]) -> bool {
    let kp = R1_P_MONT;
    let m = kp.m;
    let rhs = addmod(
        addmod(mmul(mmul(x, x, kp), x, kp), mmul(R1_A_MONT, x, kp), m),
        R1_B_MONT,
        m,
    );
    eq4(mmul(y, y, kp), rhs)
}

/// Jacobian doubling for a general coefficient a (dbl-2007-bl).
unconstrained fn jdbl_a(a: Jac, k: Mont) -> Jac {
    let m = k.m;
    let xx = mmul(a[0], a[0], k);
    let yy = mmul(a[1], a[1], k);
    let yyyy = mmul(yy, yy, k);
    let zz = mmul(a[2], a[2], k);
    let t = addmod(a[0], yy, m);
    let s1 = submod(submod(mmul(t, t, k), xx, m), yyyy, m);
    let s = addmod(s1, s1, m);
    let mm = addmod(
        addmod(addmod(xx, xx, m), xx, m),
        mmul(R1_A_MONT, mmul(zz, zz, k), k),
        m,
    );
    let x3 = submod(mmul(mm, mm, k), addmod(s, s, m), m);
    let y8 = addmod(yyyy, yyyy, m);
    let y8 = addmod(y8, y8, m);
    let y8 = addmod(y8, y8, m);
    let y3 = submod(mmul(mm, submod(s, x3, m), k), y8, m);
    let yz = addmod(a[1], a[2], m);
    let z3 = submod(submod(mmul(yz, yz, k), yy, m), zz, m);
    [x3, y3, z3]
}

/// e * B for an affine B and the bits e[from .. from + bits] (least
/// significant first) of the scalar: (point, whether the scalar != 0).
/// Double-and-add from the top bit; for a scalar below the group order no
/// step adds equal or opposite points.
unconstrained fn mul_bits(b: [[u64; 4]; 2], e: [bool; 256], from: u32, bits: u32) -> (Jac, bool) {
    let kp = R1_P_MONT;
    let mut acc: Jac = [b[0], b[1], kp.one];
    let mut set = false;
    for i in 0..bits {
        let j = bits - 1 - i;
        if set {
            acc = jdbl_a(acc, kp);
        }
        if e[from + j] {
            if set {
                acc = madd(acc, b[0], b[1], kp).0;
            } else {
                set = true;
            }
        }
    }
    (acc, set)
}

/// Whether the fixed-base chain, the offset subtraction or the final
/// addition of bb 6.0.0's secp256r1_ecdsa_mul(Q', u1, u2) fails a
/// witness-dependent assertion (module header), for the key Q' = (qx, qy)
/// in affine Montgomery form and u1, u2 < n. Trap-free (bignum.nr;
/// constant-bound loops, loop-counter indices).
pub(crate) unconstrained fn r1_bad(qx: [u64; 4], qy: [u64; 4], u1: [u64; 4], u2: [u64; 4]) -> bool {
    let kp = R1_P_MONT;
    let n = R1_N_MONT.m;
    let mut bad = false;
    // the 38 table points L_w = d_w 2^off(w) G + 2^w H
    let mut lj: [Jac; 38] = [[[0; 4]; 3]; 38];
    let mut zs = [kp.one; 38];
    let mut off: u32 = 0;
    let u1_bits = bits_le(u1);
    for w in 0..38 {
        let bits = R1_FB_BITS[w];
        let hw = R1_FB_WINDOWS[w][1];
        let (kb, nonzero) = mul_bits(R1_FB_WINDOWS[w][0], u1_bits, off, bits);
        off += bits;
        if nonzero {
            let (t, h, _) = madd(kb, hw[0], hw[1], kp);
            // d 2^off G == +-2^w H would give the discrete log of H
            bad = bad | is_zero4(h);
            lj[w] = t;
        } else {
            lj[w] = [hw[0], hw[1], kp.one];
        }
        zs[w] = lj[w][2];
    }
    let mut out = bad;
    if !bad {
        let zi = batch_inv(zs, kp);
        let mut lx = [[0; 4]; 38];
        let mut ly = [[0; 4]; 38];
        for w in 0..38 {
            let z2 = mmul(zi[w], zi[w], kp);
            lx[w] = mmul(lj[w][0], z2, kp);
            ly[w] = mmul(lj[w][1], mmul(zi[w], z2, kp), kp);
        }
        // the chain S_i = S_(i-1) + L_i, S_0 = L_0; X and Z of each S for
        // the aliasing checks
        let mut s: Jac = [lx[0], ly[0], kp.one];
        let mut sx = [[0; 4]; 38];
        let mut sz = [kp.one; 38];
        for i in 1..38 {
            sx[i - 1] = s[0];
            sz[i - 1] = s[2];
            if !bad {
                let (t, h, _) = madd(s, lx[i], ly[i], kp);
                bad = is_zero4(h);
                s = t;
            }
        }
        out = bad;
        if !bad {
            sz[37] = s[2];
            let szi = batch_inv(sz, kp);
            for i in 1..38 {
                let z = szi[i - 1];
                let xs = from_mont(mmul(sx[i - 1], mmul(z, z, kp), kp), kp);
                let xl = from_mont(lx[i], kp);
                // chain_add_start compares x(L_0) with x(L_1); chain_add
                // x(L_i) with x(S_(i-1))
                out = out
                    | if i == 1 {
                        alias_diff(xs, xl, R1_ALIAS_INC)
                    } else {
                        alias_diff(xl, xs, R1_ALIAS_INC)
                    };
            }
            // raw - (2^38 - 1) H by bb's complete subtraction: complete
            // addition of the negated constant (same divisor x2 - x1; the
            // doubling branch is raw == -constant)
            let z = szi[37];
            let z2 = mmul(z, z, kp);
            let raw = Aff { x: mmul(s[0], z2, kp), y: mmul(s[1], mmul(z, z2, kp), kp), inf: false };
            let c = R1_FB_TOTAL_OFFSET;
            let (t1, alias1) = complete_add(
                raw,
                c[0],
                submod([0; 4], c[1], kp.m),
                kp,
                R1_A_MONT,
                R1_ALIAS_ADD_C,
                R1_ALIAS_DBL_2,
            );
            out = out | alias1;
            // T2 = u2 Q', u2 read as 2 when it is 0, 1 or -1
            let one = [1, 0, 0, 0];
            let u2s = if is_zero4(u2) | eq4(u2, one) | eq4(u2, submod([0; 4], one, n)) {
                [2, 0, 0, 0]
            } else {
                u2
            };
            let (t2j, _) = mul_bits([qx, qy], bits_le(u2s), 0, 256);
            let zi2 = inv_mont(t2j[2], kp);
            let zz = mmul(zi2, zi2, kp);
            let (_, alias2) = complete_add(
                t1,
                mmul(t2j[0], zz, kp),
                mmul(t2j[1], mmul(zi2, zz, kp), kp),
                kp,
                R1_A_MONT,
                R1_ALIAS_ADD_A,
                R1_ALIAS_DBL_3,
            );
            out = out | alias2;
        }
    }
    out
}
