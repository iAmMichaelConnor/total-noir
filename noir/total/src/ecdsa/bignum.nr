//! Unconstrained 256-bit modular arithmetic for the hints of the blinded
//! ECDSA wrappers (blind_hint.nr, k1_emul.nr): four u64 limbs, least
//! significant first, Montgomery multiplication modulo an odd modulus
//! 2^255 < m < 2^256 (the secp256k1 and secp256r1 base fields and group
//! orders), a binary extended-Euclid inversion on 128-bit halves, and
//! arithmetic modulo 2^320 for the quotients of blind.nr's integer
//! identities.
//!
//! Trap-free for every argument, by construction rather than by input
//! checks: every product is u64 * u64 + (u64 + u64) in u128, below 2^128;
//! every limb subtraction is (a + 2^64) - (b + borrow) with both sides
//! below 2^65 and the first larger; a 128-bit subtraction or addition is
//! formed only after the comparison that keeps it in range; every shift is
//! by a constant below the width and moves at most one set bit to the top;
//! every division is by the constant 2^64; every index is a constant or a
//! loop counter within its array; loops have constant bounds; there is no
//! assertion. A wrong argument (a value >= m, a zero to invert) gives a
//! wrong value, never a trap. Brillig still compiles overflow and bounds
//! checks for these operations (total-lint counts them as reachable abort
//! sites, whitelisted with the library); the argument above is why none
//! fires.
//!
//! These hints use integer bit operations and the Poseidon2 black box and
//! run only under the ECDSA entries, which co-noir cannot execute anyway
//! (co-acvm does not solve the ECDSA black box; docs/co-noir.md).

/// Montgomery parameters of a modulus m, R = 2^256.
pub(crate) struct Mont {
    pub(crate) m: [u64; 4],
    /// -m^-1 mod 2^64.
    pub(crate) m_inv: u64,
    /// R mod m (Montgomery form of 1).
    pub(crate) one: [u64; 4],
    /// R^2 mod m.
    pub(crate) r2: [u64; 4],
    /// R^3 mod m.
    pub(crate) r3: [u64; 4],
    /// m^-1 mod 2^320.
    pub(crate) inv320: [u64; 5],
}

global B64: u128 = 0x10000000000000000;

/// a*b + c + d as (low, high) 64-bit halves; below 2^128, so no overflow.
/// (c + d is formed first, below 2^65, so only one addition is checked;
/// the high half is a division by the constant 2^64.)
pub(crate) unconstrained fn mac(a: u64, b: u64, c: u64, d: u64) -> (u64, u64) {
    let t: u128 = (a as u128) * (b as u128) + ((c as u128) + (d as u128));
    (t as u64, (t / B64) as u64)
}

/// a >= b.
pub(crate) unconstrained fn geq(a: [u64; 4], b: [u64; 4]) -> bool {
    if a[3] != b[3] {
        a[3] > b[3]
    } else if a[2] != b[2] {
        a[2] > b[2]
    } else if a[1] != b[1] {
        a[1] > b[1]
    } else {
        a[0] >= b[0]
    }
}

pub(crate) unconstrained fn is_zero4(a: [u64; 4]) -> bool {
    (a[0] == 0) & (a[1] == 0) & (a[2] == 0) & (a[3] == 0)
}

pub(crate) unconstrained fn eq4(a: [u64; 4], b: [u64; 4]) -> bool {
    (a[0] == b[0]) & (a[1] == b[1]) & (a[2] == b[2]) & (a[3] == b[3])
}

/// One limb of a subtraction: (a - b - borrow) mod 2^64 and the borrow
/// out. a + 2^64 and b + borrow are below 2^65, and the first is at least
/// the second, so the one checked subtraction never underflows.
unconstrained fn sbb(a: u64, b: u64, borrow: u128) -> (u64, u128) {
    let d: u128 = ((a as u128) + B64) - ((b as u128) + borrow);
    (d as u64, (d < B64) as u128)
}

/// One limb of an addition: (a + b + carry) mod 2^64 and the carry out
/// (the sum is below 2^65).
unconstrained fn adc(a: u64, b: u64, carry: u128) -> (u64, u128) {
    let s: u128 = (a as u128) + (b as u128) + carry;
    (s as u64, (s >= B64) as u128)
}

/// a - b mod 2^256 and the borrow out (0 or 1).
pub(crate) unconstrained fn sub4(a: [u64; 4], b: [u64; 4]) -> ([u64; 4], u64) {
    let (d0, c) = sbb(a[0], b[0], 0);
    let (d1, c) = sbb(a[1], b[1], c);
    let (d2, c) = sbb(a[2], b[2], c);
    let (d3, c) = sbb(a[3], b[3], c);
    ([d0, d1, d2, d3], c as u64)
}

/// a + b mod 2^256 and the carry out (0 or 1).
pub(crate) unconstrained fn add4(a: [u64; 4], b: [u64; 4]) -> ([u64; 4], u64) {
    let (s0, c) = adc(a[0], b[0], 0);
    let (s1, c) = adc(a[1], b[1], c);
    let (s2, c) = adc(a[2], b[2], c);
    let (s3, c) = adc(a[3], b[3], c);
    ([s0, s1, s2, s3], c as u64)
}

/// (a + b) mod m for a, b < m.
pub(crate) unconstrained fn addmod(a: [u64; 4], b: [u64; 4], m: [u64; 4]) -> [u64; 4] {
    let (s, c) = add4(a, b);
    if (c != 0) | geq(s, m) {
        sub4(s, m).0
    } else {
        s
    }
}

/// (a - b) mod m for a, b < m.
pub(crate) unconstrained fn submod(a: [u64; 4], b: [u64; 4], m: [u64; 4]) -> [u64; 4] {
    let (d, borrow) = sub4(a, b);
    if borrow != 0 {
        add4(d, m).0
    } else {
        d
    }
}

/// -a mod m for a < m.
pub(crate) unconstrained fn negmod(a: [u64; 4], m: [u64; 4]) -> [u64; 4] {
    if is_zero4(a) {
        a
    } else {
        sub4(m, a).0
    }
}

/// Montgomery product a*b/R mod m (CIOS), below m when a*b < m*R (for
/// instance a, b < m).
pub(crate) unconstrained fn mmul(a: [u64; 4], b: [u64; 4], k: Mont) -> [u64; 4] {
    let m = k.m;
    let mut t0: u64 = 0;
    let mut t1: u64 = 0;
    let mut t2: u64 = 0;
    let mut t3: u64 = 0;
    let mut t4: u64 = 0;
    for i in 0..4 {
        let bi = b[i];
        let (l0, c) = mac(a[0], bi, t0, 0);
        let (l1, c) = mac(a[1], bi, t1, c);
        let (l2, c) = mac(a[2], bi, t2, c);
        let (l3, c) = mac(a[3], bi, t3, c);
        let s: u128 = (t4 as u128) + (c as u128);
        let l4 = s as u64;
        let l5 = (s / B64) as u64;
        let mm = ((l0 as u128) * (k.m_inv as u128)) as u64;
        let (_, c) = mac(mm, m[0], l0, 0);
        let (r0, c) = mac(mm, m[1], l1, c);
        let (r1, c) = mac(mm, m[2], l2, c);
        let (r2, c) = mac(mm, m[3], l3, c);
        let s: u128 = (l4 as u128) + (c as u128);
        t0 = r0;
        t1 = r1;
        t2 = r2;
        t3 = s as u64;
        t4 = l5 + ((s / B64) as u64);
    }
    let t = [t0, t1, t2, t3];
    if (t4 != 0) | geq(t, m) {
        sub4(t, m).0
    } else {
        t
    }
}

pub(crate) unconstrained fn to_mont(a: [u64; 4], k: Mont) -> [u64; 4] {
    mmul(a, k.r2, k)
}

pub(crate) unconstrained fn from_mont(a: [u64; 4], k: Mont) -> [u64; 4] {
    mmul(a, [1, 0, 0, 0], k)
}

/// a*b mod m for plain a, b < m.
pub(crate) unconstrained fn mulmod(a: [u64; 4], b: [u64; 4], k: Mont) -> [u64; 4] {
    mmul(to_mont(a, k), b, k)
}

/// a mod m for a < 2^256 < 2m.
pub(crate) unconstrained fn reduce_once(a: [u64; 4], m: [u64; 4]) -> [u64; 4] {
    if geq(a, m) {
        sub4(a, m).0
    } else {
        a
    }
}

global MAX128: u128 = 0xffffffffffffffffffffffffffffffff;

/// A 256-bit value as (low, high) 128-bit halves.
unconstrained fn halves(a: [u64; 4]) -> (u128, u128) {
    ((a[0] as u128) + (a[1] as u128) * B64, (a[2] as u128) + (a[3] as u128) * B64)
}

/// (a - b) mod 2^256 on halves, and the borrow out. Each subtraction is of
/// a smaller from a larger value, or (MAX - b) + a + 1 <= MAX for a < b.
unconstrained fn sub2(a: (u128, u128), b: (u128, u128)) -> ((u128, u128), bool) {
    let (lo, b0) = if a.0 >= b.0 {
        (a.0 - b.0, false)
    } else {
        ((MAX128 - b.0) + a.0 + 1, true)
    };
    let (h1, b1) = if a.1 >= b.1 {
        (a.1 - b.1, false)
    } else {
        ((MAX128 - b.1) + a.1 + 1, true)
    };
    if b0 {
        if h1 >= 1 {
            ((lo, h1 - 1), b1)
        } else {
            ((lo, MAX128), true)
        }
    } else {
        ((lo, h1), b1)
    }
}

/// (a + b) mod 2^256 on halves, and the carry out. a + b is formed only
/// when a <= MAX - b, otherwise a - (MAX - b) - 1 >= 0.
unconstrained fn add2(a: (u128, u128), b: (u128, u128)) -> ((u128, u128), bool) {
    let (lo, c0) = if a.0 <= MAX128 - b.0 {
        (a.0 + b.0, false)
    } else {
        (a.0 - (MAX128 - b.0) - 1, true)
    };
    let (h1, c1) = if a.1 <= MAX128 - b.1 {
        (a.1 + b.1, false)
    } else {
        (a.1 - (MAX128 - b.1) - 1, true)
    };
    if c0 {
        if h1 < MAX128 {
            ((lo, h1 + 1), c1)
        } else {
            ((lo, 0), true)
        }
    } else {
        ((lo, h1), c1)
    }
}

/// (a + top * 2^256) / 2, rounded down; the bits shifted left are single
/// bits moved to position 127.
unconstrained fn shr1(a: (u128, u128), top: bool) -> (u128, u128) {
    ((a.0 >> 1) | ((a.1 & 1) << 127), (a.1 >> 1) | ((top as u128) << 127))
}

/// x / 2 mod m for x < m, m odd.
unconstrained fn halve(x: (u128, u128), m: (u128, u128)) -> (u128, u128) {
    if (x.0 & 1) == 0 {
        shr1(x, false)
    } else {
        let (s, c) = add2(x, m);
        shr1(s, c)
    }
}

/// (a - b) mod m for a, b < m.
unconstrained fn submod2(a: (u128, u128), b: (u128, u128), m: (u128, u128)) -> (u128, u128) {
    let (d, borrow) = sub2(a, b);
    if borrow {
        add2(d, m).0
    } else {
        d
    }
}

unconstrained fn is_one2(a: (u128, u128)) -> bool {
    (a.0 == 1) & (a.1 == 0)
}

/// a^-1 mod m for 0 < a < m and m an odd prime below 2^256 (plain form),
/// by binary extended Euclid on 128-bit halves with the invariants
/// x1*a == u and x2*a == v (mod m). Each step halves an even u or v, or
/// subtracts the smaller of two odd values from the larger, which leaves
/// an even value for the next step; halvings are at most
/// bitlen(a) + bitlen(m) <= 512, so the 1100-step bound is never reached
/// for such arguments. For a = 0 or another argument outside the domain
/// the loop runs to the bound and returns some value: no trap.
pub(crate) unconstrained fn inv_plain(a: [u64; 4], m4: [u64; 4]) -> [u64; 4] {
    let m = halves(m4);
    let mut u = halves(a);
    let mut v = m;
    let mut x1: (u128, u128) = (1, 0);
    let mut x2: (u128, u128) = (0, 0);
    for _ in 0..1100 {
        if is_one2(u) | is_one2(v) {
            break;
        }
        if (u.0 & 1) == 0 {
            u = shr1(u, false);
            x1 = halve(x1, m);
        } else if (v.0 & 1) == 0 {
            v = shr1(v, false);
            x2 = halve(x2, m);
        } else if (u.1 > v.1) | ((u.1 == v.1) & (u.0 >= v.0)) {
            u = sub2(u, v).0;
            x1 = submod2(x1, x2, m);
        } else {
            v = sub2(v, u).0;
            x2 = submod2(x2, x1, m);
        }
    }
    let r = if is_one2(u) { x1 } else { x2 };
    [r.0 as u64, (r.0 / B64) as u64, r.1 as u64, (r.1 / B64) as u64]
}

/// The Montgomery-form inverse of a Montgomery-form a (a*R -> a^-1*R):
/// inv_plain gives (aR)^-1 = a^-1 R^-1, and multiplying by R^3 in
/// Montgomery form gives a^-1 R. Zero for a = 0 is not guaranteed; the
/// callers never use the value then.
pub(crate) unconstrained fn inv_mont(a: [u64; 4], k: Mont) -> [u64; 4] {
    mmul(inv_plain(a, k.m), k.r3, k)
}

/// Montgomery inverses of N Montgomery values with one inversion. A zero
/// entry makes every output wrong, never a trap.
pub(crate) unconstrained fn batch_inv<let N: u32>(a: [[u64; 4]; N], k: Mont) -> [[u64; 4]; N] {
    let mut pre = [[0; 4]; N];
    let mut acc = k.one;
    for i in 0..N {
        pre[i] = acc;
        acc = mmul(acc, a[i], k);
    }
    let mut inv = inv_mont(acc, k);
    let mut out = [[0; 4]; N];
    for j in 0..N {
        let i = N - 1 - j;
        out[i] = mmul(inv, pre[i], k);
        inv = mmul(inv, a[i], k);
    }
    out
}

/// a*b mod 2^320.
pub(crate) unconstrained fn wmul5(a: [u64; 5], b: [u64; 5]) -> [u64; 5] {
    let mut out = [0; 5];
    for i in 0..5 {
        let mut carry: u64 = 0;
        for j in 0..(5 - i) {
            let (lo, hi) = mac(a[i], b[j], out[i + j], carry);
            out[i + j] = lo;
            carry = hi;
        }
    }
    out
}

/// a + b mod 2^320.
pub(crate) unconstrained fn wadd5(a: [u64; 5], b: [u64; 5]) -> [u64; 5] {
    let mut out = [0; 5];
    let mut carry: u128 = 0;
    for i in 0..5 {
        let (s, c) = adc(a[i], b[i], carry);
        out[i] = s;
        carry = c;
    }
    out
}

/// a - b mod 2^320.
pub(crate) unconstrained fn wsub5(a: [u64; 5], b: [u64; 5]) -> [u64; 5] {
    let mut out = [0; 5];
    let mut borrow: u128 = 0;
    for i in 0..5 {
        let (d, c) = sbb(a[i], b[i], borrow);
        out[i] = d;
        borrow = c;
    }
    out
}

pub(crate) unconstrained fn ext5(a: [u64; 4]) -> [u64; 5] {
    [a[0], a[1], a[2], a[3], 0]
}

/// a*b mod 2^320 for four-limb a, b.
pub(crate) unconstrained fn wprod(a: [u64; 4], b: [u64; 4]) -> [u64; 5] {
    wmul5(ext5(a), ext5(b))
}

/// a*b as eight limbs.
pub(crate) unconstrained fn mul512(a: [u64; 4], b: [u64; 4]) -> [u64; 8] {
    let mut out = [0; 8];
    for i in 0..4 {
        let mut carry: u64 = 0;
        for j in 0..4 {
            let (lo, hi) = mac(a[i], b[j], out[i + j], carry);
            out[i + j] = lo;
            carry = hi;
        }
        out[i + 4] = carry;
    }
    out
}

/// The quotient q of blind.nr's close(f, m, q): (F + 2^258 m) / m, with
/// F given mod 2^320 as f. Exact whenever the true quotient is a
/// nonnegative integer below 2^260 (the honest witnesses of every caller;
/// close's doc comment): m is odd, so m^-1 mod 2^320 exists and the
/// product is the quotient. Returned in close's limb form, the top limb
/// holding q_3 + q_4 * 2^64.
pub(crate) unconstrained fn close_quotient(f: [u64; 5], k: Mont) -> [Field; 4] {
    // 2^258 * m mod 2^320 is (4 m_0 mod 2^64) * 2^256
    let off = [0, 0, 0, 0, ((k.m[0] as u128) * 4) as u64];
    let q = wmul5(wadd5(f, off), k.inv320);
    [
        q[0] as Field,
        q[1] as Field,
        q[2] as Field,
        (q[3] as Field) + (q[4] as Field) * 0x10000000000000000,
    ]
}

pub(crate) unconstrained fn to_fields(a: [u64; 4]) -> [Field; 4] {
    [a[0] as Field, a[1] as Field, a[2] as Field, a[3] as Field]
}

/// Field limbs to u64 limbs (truncating casts; exact for limbs below 2^64).
pub(crate) unconstrained fn from_fields(a: [Field; 4]) -> [u64; 4] {
    [a[0] as u64, a[1] as u64, a[2] as u64, a[3] as u64]
}

/// The 256 bits of a, least significant first. Division and remainder by
/// 2 only (no shift or mask opcode: scripts/mpc-check.sh).
pub(crate) unconstrained fn bits_le(a: [u64; 4]) -> [bool; 256] {
    let mut out = [false; 256];
    for l in 0..4 {
        let mut v = a[l];
        for i in 0..64 {
            out[64 * l + i] = v % 2 == 1;
            v = v / 2;
        }
    }
    out
}

/// 32 big-endian bytes to limbs.
pub(crate) unconstrained fn from_be(b: [u8; 32]) -> [u64; 4] {
    let mut out = [0; 4];
    for i in 0..4 {
        let mut v: u64 = 0;
        for j in 0..8 {
            v = (v << 8) | (b[8 * (3 - i) + j] as u64);
        }
        out[i] = v;
    }
    out
}
