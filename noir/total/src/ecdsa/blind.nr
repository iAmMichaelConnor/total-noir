//! Key blinding for the ECDSA black boxes: the constraint half.
//!
//! blind_core takes an on-curve key Q with canonical coordinates, a
//! signature (r, s) and a hash z, and returns (Q', z') with
//!     Q' = Q + e B,  B = b' G,  z' == z - e r b' (mod n),
//! for a scalar b' the prover chooses through 256 hinted bits and a sign
//! e in {1, -1} it chooses through one more. Then
//!     (z' / s) G + (r / s) Q' = (z / s) G + (r / s) Q = R,
//! so the black box decides (Q', r, s, z') exactly as it would decide
//! (Q, r, s, z), while every point its variable-base multiplication
//! touches depends on e b'. ecdsa.nr's header says why that matters and
//! blind_hint.nr how the honest prover picks the blind. The pairs (e, b')
//! reach every nonzero residue e b' mod n (C1), so when r != 0 mod n the
//! prover can give the black box any scalar u1 = z'/s it likes: that is
//! what docs/ecdsa-totality.md's existence argument uses.
//!
//! Constraints (all 256-bit values are four 64-bit limbs, least
//! significant first; "X == 0 mod m" means close(): the integer identity
//! X + 2^258 m = q m with a hinted quotient q):
//! C1 (blind scalar). bits are 256 hinted Fields and sign is one more,
//!    each asserted boolean (b * b == b). Window w is bits 4w .. 4w + 3,
//!    d_w its value, and the top digit is constrained d_63 != 15 (the
//!    product of the four top bits is 0). b' = sum (d_w + 2) 16^w
//!    = o + D with o = sum 2 * 16^w and 0 <= D < 15 * 16^63, and
//!    e = 1 - 2 sign. Coverage: for every beta != 0 mod n one of
//!    beta - o, -beta - o has its residue mod n below L = 15 * 16^63. If
//!    x = (beta - o) mod n is not, x lies in [L, n) and -beta - o
//!    == -2o - x, whose residue -2o - x + 2n lies in (n - 2o, 2n - 2o - L],
//!    inside [0, L) because n > 2o and n - o < L
//!    (scripts/gen_ecdsa_tables.py asserts both for each curve). So
//!    beta == e b' mod n for some accepted (e, b').
//! C2 (table select). T_w = (d_w + 2) 16^w G, read from the public table
//!    of table_k1.nr / table_r1.nr by the multilinear polynomial in the
//!    window's bits (select_point). Exact for boolean bits: every limb is
//!    the table's limb, below 2^64.
//! C3 (fixed-base sum). A_0 = T_0 and A_j = A_(j-1) + T_j for j = 1..63
//!    by the affine chord formulas, with hinted slope lam_j and x_j (each
//!    limb RANGEd to 64 bits) and y_(j-1) written as
//!    lam_(j-1) (x(T_(j-1)) - x_(j-1)) - y(T_(j-1)) (y(T_0) for j = 1):
//!    lam_j (x(T_j) - x_(j-1)) - y(T_j) + y_(j-1) == 0 mod p and
//!    lam_j^2 - x_(j-1) - x(T_j) - x_j == 0 mod p; finally the hinted y_B
//!    (RANGEd) with y_B - lam_63 (x(T_63) - x_63) + y(T_63) == 0 mod p.
//!    B = (x_63, y_B).
//! C4 (key addition, Q' = Q + e B; e B = (x_B, e y_B)). Hinted inv, lam,
//!    x' and y' (each limb RANGEd):
//!    inv (x_B - x_Q) - 1 == 0, lam (x_B - x_Q) - e y_B + y_Q == 0,
//!    lam^2 - x_Q - x_B - x' == 0 and lam (x_Q - x') - y_Q - y' == 0, all
//!    mod p; and x' + e_x == p - 1, y' + e_y == p - 1 exactly, with
//!    hinted slacks e_x, e_y RANGEd to 64 bits per limb (canonical).
//! C5 (hash). Hinted z' (limbs RANGEd): e r b' + z' - z == 0 mod n, and
//!    z' + e_z == n - 1 exactly (canonical), r the first 32 bytes of the
//!    signature.
//! The outputs are x', y' and z' as big-endian bytes, one to_be_bytes per
//! limb (exact for a RANGEd limb).
//!
//! Soundness: every hint that passes C1-C5 gives (Q', z') as above.
//! (a) close() is exact. Every operand has limbs below 2^65 in absolute
//!     value (RANGEd hints, table limbs, byte limbs, differences of two of
//!     them, b' with limbs below 17 * 16^16 / 15 < 2^65, and e times one
//!     of these), each identity
//!     has at most three products, so every column is below 2^134 and the
//!     carries argument of close() applies: X + 2^258 m = q m over the
//!     integers, hence X == 0 mod m.
//! (b) C3 never meets equal x-coordinates. Before window j the partial
//!     sum is a G with 2 (16^j - 1) / 15 <= a <= 17 (16^j - 1) / 15
//!     < 2 * 16^j, and T_j = t G with 2 * 16^j <= t <= 17 * 16^j
//!     (t <= 16 * 16^63 = 2^256 for j = 63, the top digit being at most
//!     14). So 0 < a < t. For j <= 62, a + t < 19 * 16^62 < n, hence
//!     a != t, a != -t mod n and neither is 0 mod n. For j = 63,
//!     0 < t - a < 2^256 and t - a = n would need a = t - n <= 2^256 - n
//!     < 2^225, below the least partial sum 2 (16^63 - 1) / 15, so
//!     a != t mod n; t != 0 mod n because 0 < t <= 2^256 < 2n and t != n
//!     (n is odd, t a multiple of 16^63); and a + t = n (one a for
//!     d_63 = 13, on each curve) makes A_62 = -T_63, where the slope
//!     identity reads -2 y(T_63) == 0 mod p and has no solution, so no
//!     hint is accepted for that b' (it is b' == 0 mod n: B would be
//!     infinity). In every accepted case x(A_(j-1)) != x(T_j) mod p: the
//!     slope identity then has exactly one solution mod p, the second
//!     identity fixes x_j mod p, and y_j as written is the chord
//!     formula's y; by induction (x_j, y_j) is A_j mod p. So B = b' G
//!     with b' != 0 mod n, and the prover's only freedom is the bits.
//! (c) C4: the inverse identity forces x_B != x_Q mod p, so e B != +-Q
//!     and Q + e B is a chord addition with a unique slope (without it,
//!     e B = Q would leave lam free and Q' forgeable); the other three
//!     fix x' and y' mod p, and the slacks make them the canonical values
//!     below p. Q + e B is not infinity because e B != -Q. e is 1 or -1
//!     because sign is boolean.
//! (d) C5 gives z' == z - e r b' mod n with z' < n; b' enters as the
//!     integer o + D, which may exceed n, and only its residue matters on
//!     both sides (B = b' G, and the identity is mod n).
//! Nothing here asserts a property of the inputs: the identities hold
//! for the honest hint for every input (blind_hint.nr).
//!
//! Cost: about 19,200 bb gates per call (ecdsa.nr's table): per chain
//! step two close() (four quotient RANGEs and five carry RANGEs each) and
//! eight 64-bit RANGEs, plus 11 bit products per window for the select.

use crate::core::{INV_TWO_POW_64, two_pow, TWO_POW_128, TWO_POW_64};
use crate::secp::{be_limbs64, constrain_columns, mul_columns};
use super::bignum::Mont;
use super::blind_hint::blind_hint;
use super::table_k1::{K1_A_MONT, K1_BLIND_LIM, K1_BLIND_O, K1_FB, K1_N, K1_N_MONT, K1_P, K1_P_MONT};
use super::table_r1::{R1_A_MONT, R1_BLIND_LIM, R1_BLIND_O, R1_FB, R1_N, R1_N_MONT, R1_P, R1_P_MONT};

/// The constants of one curve, for the constraint half and the hint.
pub(crate) trait SecpCurve {
    /// The fixed-base window table (table_k1.nr's header).
    fn fb() -> [[[Field; 16]; 8]; 64];
    /// Base-field modulus p, 64-bit limbs.
    fn p() -> [Field; 4];
    /// Group order n, 64-bit limbs.
    fn n() -> [Field; 4];
    fn p_mont() -> Mont;
    fn n_mont() -> Mont;
    /// The curve coefficient a, Montgomery form mod p.
    fn a_mont() -> [u64; 4];
    /// Whether the hint must emulate bb's secp256k1 multiplication.
    fn is_k1() -> bool;
    /// The blind's offset o and the bound 15 * 16^63 on its digit part.
    fn blind_o() -> [u64; 4];
    fn blind_lim() -> [u64; 4];
}

pub(crate) struct Secp256k1 {}

impl SecpCurve for Secp256k1 {
    fn fb() -> [[[Field; 16]; 8]; 64] {
        K1_FB
    }
    fn p() -> [Field; 4] {
        K1_P
    }
    fn n() -> [Field; 4] {
        K1_N
    }
    fn p_mont() -> Mont {
        K1_P_MONT
    }
    fn n_mont() -> Mont {
        K1_N_MONT
    }
    fn a_mont() -> [u64; 4] {
        K1_A_MONT
    }
    fn is_k1() -> bool {
        true
    }
    fn blind_o() -> [u64; 4] {
        K1_BLIND_O
    }
    fn blind_lim() -> [u64; 4] {
        K1_BLIND_LIM
    }
}

pub(crate) struct Secp256r1 {}

impl SecpCurve for Secp256r1 {
    fn fb() -> [[[Field; 16]; 8]; 64] {
        R1_FB
    }
    fn p() -> [Field; 4] {
        R1_P
    }
    fn n() -> [Field; 4] {
        R1_N
    }
    fn p_mont() -> Mont {
        R1_P_MONT
    }
    fn n_mont() -> Mont {
        R1_N_MONT
    }
    fn a_mont() -> [u64; 4] {
        R1_A_MONT
    }
    fn is_k1() -> bool {
        false
    }
    fn blind_o() -> [u64; 4] {
        R1_BLIND_O
    }
    fn blind_lim() -> [u64; 4] {
        R1_BLIND_LIM
    }
}

/// The hint of blind_core (field names follow the module header).
pub(crate) struct BlindHint {
    /// C1: the blind's 256 bits and its sign bit (1 for e = -1), each
    /// asserted boolean.
    pub(crate) bits: [Field; 256],
    pub(crate) sign: Field,
    /// C3, steps j = 1..63 at index j - 1: slope, x of A_j, and the two
    /// quotients.
    pub(crate) lam: [[Field; 4]; 63],
    pub(crate) x: [[Field; 4]; 63],
    pub(crate) q_lam: [[Field; 4]; 63],
    pub(crate) q_x: [[Field; 4]; 63],
    /// C3: y_B and its quotient.
    pub(crate) yb: [Field; 4],
    pub(crate) q_yb: [Field; 4],
    /// C4: inverse, slope, their quotients, and the blinded key.
    pub(crate) inv: [Field; 4],
    pub(crate) q_inv: [Field; 4],
    pub(crate) lam_a: [Field; 4],
    pub(crate) q_lam_a: [Field; 4],
    pub(crate) q_x_a: [Field; 4],
    pub(crate) q_y_a: [Field; 4],
    pub(crate) key_x: [Field; 4],
    pub(crate) key_y: [Field; 4],
    pub(crate) slack_x: [Field; 4],
    pub(crate) slack_y: [Field; 4],
    /// C5: the adjusted hash, its quotient and slack.
    pub(crate) hash: [Field; 4],
    pub(crate) q_hash: [Field; 4],
    pub(crate) slack_hash: [Field; 4],
}

/// f + a*b by 2^64-columns (a, b may hold signed limb differences).
fn add_prod(f: [Field; 8], a: [Field; 4], b: [Field; 4]) -> [Field; 8] {
    let c = mul_columns(a, b);
    let mut out = f;
    for k in 0..7 {
        out[k] += c[k];
    }
    out
}

/// f + sign * c, for sign in {1, -1}.
fn add_lin(f: [Field; 8], c: [Field; 4], sign: Field) -> [Field; 8] {
    let mut out = f;
    for k in 0..4 {
        out[k] += sign * c[k];
    }
    out
}

fn sub_limbs(a: [Field; 4], b: [Field; 4]) -> [Field; 4] {
    [a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]
}

/// RANGE each limb to 64 bits.
fn range64(a: [Field; 4]) {
    for i in 0..4 {
        a[i].assert_max_bit_size::<64>();
    }
}

/// Asserts X + 2^258 m == q m over the integers, X = sum f_k 2^(64k), so
/// X == 0 (mod m). PRECONDITION (met by every caller, module header (a)):
/// f is a sum of at most three products of operands whose limbs are below
/// 2^65 in absolute value plus linear terms with limbs below 2^66, so
/// |f_k| < 2^134; m < 2^256 with limbs below 2^64.
/// Emits: RANGE q's limbs (64, 64, 64, 68 bits); with g = f + 2^258 m -
/// q m by columns, carries c_k = (g_k + c_(k-1)) / 2^64 for k = 0..4 (a
/// Field multiple of the constant 1/2^64, no witness of its own), each
/// RANGEd as c_k + 2^72 to 73 bits; and c_4 + g_5 + g_6 2^64 + g_7 2^128
/// == 0 in the Field.
/// Sound: q m has columns below 2^133, so |g_k| < 2^135; by induction
/// each c_k is an integer in [-2^72, 2^72) and c_k 2^64 == g_k + c_(k-1)
/// holds between values below 2^137 < r/2 in absolute value, so over the
/// integers; then G = 2^320 * bracket with |bracket| < 2^72 + 2^135 +
/// 2^199 + 2^194 < r, and bracket == 0 mod r, so bracket = 0 and G = 0.
/// Honest witness: for X == 0 mod m with -2^258 m <= X < 2^516 the
/// quotient (X + 2^258 m) / m is a nonnegative integer below 2^260 (limb
/// form: three 64-bit limbs and a 68-bit top limb), and each honest carry
/// is the exact prefix quotient, below 2^135 / 2^64 * (1 + 2^-63) < 2^72.
/// Every caller's honest X lies in that interval: it is at most two
/// products of values below 2^256, plus linear terms, so |X| < 2^514 <=
/// 2^258 m for m > 2^255.
fn close(f: [Field; 8], m: [Field; 4], q: [Field; 4]) {
    for i in 0..3 {
        q[i].assert_max_bit_size::<64>();
    }
    q[3].assert_max_bit_size::<68>();
    let qm = mul_columns(q, m);
    let mut g = f;
    for k in 0..7 {
        g[k] -= qm[k];
    }
    for k in 0..4 {
        g[4 + k] += 4 * m[k];
    }
    let mut c: Field = 0;
    for k in 0..5 {
        c = (g[k] + c) * INV_TWO_POW_64;
        (c + two_pow::<72>()).assert_max_bit_size::<73>();
    }
    assert(
        c + g[5] + g[6] * TWO_POW_64 + g[7] * TWO_POW_128 == 0,
        "ecdsa blind: reduction identity",
    );
}

/// Asserts v + slack == m - 1 over the integers with every slack limb
/// RANGEd to 64 bits, so v <= m - 1. PRECONDITION: v's limbs below 2^64,
/// m's limbs below 2^64 and m_0 >= 1. Emits four RANGEs and
/// secp::constrain_columns on the columns v_k + slack_k - (m - 1)_k (each
/// below 2^66 in absolute value; the total below 2^258), which checks the
/// identity exactly. Honest witness: slack = m - 1 - v, canonical limbs,
/// for every v < m.
fn constrain_canonical(v: [Field; 4], slack: [Field; 4], m: [Field; 4]) {
    range64(slack);
    let mut f = [0; 8];
    for k in 0..4 {
        f[k] = v[k] + slack[k] - m[k];
    }
    f[0] += 1;
    constrain_columns(f);
}

/// The table entry of one window selected by its bits: the (x, y) limbs of
/// (d + 2) 16^w G. Eleven products of bits and eight linear combinations;
/// exact for boolean bits (the polynomial interpolates the table), so
/// every limb is the table's, below 2^64, with no RANGE.
pub(crate) fn select_point(tbl: [[Field; 16]; 8], b: [Field; 4]) -> ([Field; 4], [Field; 4]) {
    let mut m = [0; 16];
    m[0] = 1;
    for i in 0..4 {
        let bit = b[i];
        let half = 1 << i;
        for s in 0..half {
            m[half + s] = m[s] * bit;
        }
    }
    let mut v = [0; 8];
    for l in 0..8 {
        let mut acc: Field = 0;
        for s in 0..16 {
            acc += tbl[l][s] * m[s];
        }
        v[l] = acc;
    }
    ([v[0], v[1], v[2], v[3]], [v[4], v[5], v[6], v[7]])
}

/// The bits of window w (module header C1).
pub(crate) fn window_bits(bits: [Field; 256], w: u32) -> [Field; 4] {
    [bits[4 * w], bits[4 * w + 1], bits[4 * w + 2], bits[4 * w + 3]]
}

/// b' as four limbs below 2^65: limb l = sum over the windows
/// 16l .. 16l + 15 of (d_w + 2) 16^(w - 16l). Linear in the bits, no
/// constraint; the limbs are not canonical but their integer is b'.
pub(crate) fn blind_scalar_limbs(bits: [Field; 256]) -> [Field; 4] {
    let mut out = [0; 4];
    for l in 0..4 {
        let mut v: Field = 0;
        for k in 0..16 {
            let wb = window_bits(bits, 16 * l + 15 - k);
            let d = wb[0] + 2 * wb[1] + 4 * wb[2] + 8 * wb[3];
            v = v * 16 + d + 2;
        }
        out[l] = v;
    }
    out
}

/// C2 and C3 (module header): returns (x_B, y_B) with B = b' G, as limbs
/// below 2^64 congruent mod p to B's affine coordinates.
fn fixed_base<C>(h: BlindHint) -> ([Field; 4], [Field; 4])
where
    C: SecpCurve,
{
    let fb = C::fb();
    let p = C::p();
    for i in 0..256 {
        assert(h.bits[i] * h.bits[i] == h.bits[i], "ecdsa blind: bit not boolean");
    }
    // d_63 != 15
    assert(
        (h.bits[252] * h.bits[253]) * (h.bits[254] * h.bits[255]) == 0,
        "ecdsa blind: top digit out of range",
    );
    let (x0, y0) = select_point(fb[0], window_bits(h.bits, 0));
    let mut x_acc = x0;
    let mut xt_prev = x0;
    let mut yt_prev = y0;
    let mut lam_prev = [0; 4];
    for j in 1..64 {
        let (xt, yt) = select_point(fb[j], window_bits(h.bits, j));
        let lam = h.lam[j - 1];
        let x_new = h.x[j - 1];
        range64(lam);
        range64(x_new);
        // lam (xt - x_acc) - yt + y_acc == 0 mod p, y_acc written through
        // the previous step's slope (yt_prev itself for j = 1)
        let mut f = add_lin(add_prod([0; 8], lam, sub_limbs(xt, x_acc)), yt, -1);
        if j == 1 {
            f = add_lin(f, yt_prev, 1);
        } else {
            f = add_lin(
                add_prod(f, lam_prev, sub_limbs(xt_prev, x_acc)),
                yt_prev,
                -1,
            );
        }
        close(f, p, h.q_lam[j - 1]);
        // lam^2 - x_acc - xt - x_new == 0 mod p
        let g = add_lin(
            add_lin(add_lin(add_prod([0; 8], lam, lam), x_acc, -1), xt, -1),
            x_new,
            -1,
        );
        close(g, p, h.q_x[j - 1]);
        x_acc = x_new;
        xt_prev = xt;
        yt_prev = yt;
        lam_prev = lam;
    }
    // y_B - lam_63 (xt_63 - x_63) + yt_63 == 0 mod p
    range64(h.yb);
    let f = add_lin(
        add_lin(
            add_prod([0; 8], lam_prev, sub_limbs(xt_prev, x_acc)),
            yt_prev,
            -1,
        ),
        h.yb,
        -1,
    );
    close(f, p, h.q_yb);
    (x_acc, h.yb)
}

/// The blinded key and hash (module header) for a key (qx, qy) that is
/// on the curve with canonical coordinates, the signature sig (r is its
/// first 32 bytes) and the hash, under the hint h: returns (x', y', z')
/// as big-endian bytes. PRECONDITION: the key is on the curve with
/// coordinates below p (the wrappers pass the real key only when
/// secp*_on_curve holds, the dummy otherwise). Constraints C1-C5. For an
/// off-curve key the honest hint still satisfies them, but (c) does not
/// describe a group operation.
pub(crate) fn blind_core<C>(
    qx: [u8; 32],
    qy: [u8; 32],
    sig: [u8; 64],
    hash: [u8; 32],
    h: BlindHint,
) -> ([u8; 32], [u8; 32], [u8; 32])
where
    C: SecpCurve,
{
    let p = C::p();
    let n = C::n();
    let (xb, yb) = fixed_base::<C>(h);
    assert(h.sign * h.sign == h.sign, "ecdsa blind: sign not boolean");
    // e = 1 or -1; e y_B and e b' limb by limb (magnitudes unchanged)
    let sg = 1 - 2 * h.sign;
    let eyb = [sg * yb[0], sg * yb[1], sg * yb[2], sg * yb[3]];
    let xq = be_limbs64(qx);
    let yq = be_limbs64(qy);
    let x2 = h.key_x;
    let y2 = h.key_y;
    range64(x2);
    range64(y2);
    let dx = sub_limbs(xb, xq);
    range64(h.inv);
    range64(h.lam_a);
    // inv (x_B - x_Q) - 1 == 0 mod p
    let mut one = [0; 8];
    one[0] = -1;
    close(add_prod(one, h.inv, dx), p, h.q_inv);
    // lam (x_B - x_Q) - e y_B + y_Q == 0 mod p
    close(
        add_lin(add_lin(add_prod([0; 8], h.lam_a, dx), eyb, -1), yq, 1),
        p,
        h.q_lam_a,
    );
    // lam^2 - x_Q - x_B - x' == 0 mod p
    let g = add_lin(
        add_lin(add_lin(add_prod([0; 8], h.lam_a, h.lam_a), xq, -1), xb, -1),
        x2,
        -1,
    );
    close(g, p, h.q_x_a);
    // lam (x_Q - x') - y_Q - y' == 0 mod p
    let e = add_lin(
        add_lin(add_prod([0; 8], h.lam_a, sub_limbs(xq, x2)), yq, -1),
        y2,
        -1,
    );
    close(e, p, h.q_y_a);
    constrain_canonical(x2, h.slack_x, p);
    constrain_canonical(y2, h.slack_y, p);
    // e r b' + z' - z == 0 mod n
    let mut rb = [0; 32];
    for i in 0..32 {
        rb[i] = sig[i];
    }
    let z2 = h.hash;
    range64(z2);
    let bl = blind_scalar_limbs(h.bits);
    let eb = [sg * bl[0], sg * bl[1], sg * bl[2], sg * bl[3]];
    let z = add_lin(
        add_lin(add_prod([0; 8], be_limbs64(rb), eb), z2, 1),
        be_limbs64(hash),
        -1,
    );
    close(z, n, h.q_hash);
    constrain_canonical(z2, h.slack_hash, n);
    (be_bytes(x2), be_bytes(y2), be_bytes(z2))
}

/// Four 64-bit limbs (each RANGEd to 64 bits by the caller) as 32
/// big-endian bytes: one to_be_bytes per limb, a decomposition that is
/// exact and unique for a limb below 2^64.
fn be_bytes(v: [Field; 4]) -> [u8; 32] {
    let mut out = [0; 32];
    for i in 0..4 {
        let b: [u8; 8] = v[3 - i].to_be_bytes();
        for j in 0..8 {
            out[8 * i + j] = b[j];
        }
    }
    out
}

/// blind_core on the honest hint (blind_hint.nr), for the curve whose
/// marker value is passed first.
pub(crate) fn blind<C>(
    _curve: C,
    qx: [u8; 32],
    qy: [u8; 32],
    sig: [u8; 64],
    hash: [u8; 32],
) -> ([u8; 32], [u8; 32], [u8; 32])
where
    C: SecpCurve,
{
    // Safety: blind_core constrains every field of the hint, and the black
    // box's verdict on its output equals the verdict on the inputs for
    // every hint it accepts (module header).
    let h = unsafe { blind_hint::<C>(qx, qy, sig, hash) };
    blind_core::<C>(qx, qy, sig, hash, h)
}
