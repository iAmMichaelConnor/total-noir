#!/usr/bin/env python3
"""Generate the constant tables of total's blinded ECDSA wrappers.

Writes noir/total/src/ecdsa/table_k1.nr and table_r1.nr (or the files under
the directory given as the first argument). Each holds, for its curve:

- the fixed-base window table of the in-circuit blind B = b'G: entry (w, d)
  is the affine point (d + 2) * 16^w * G for w < 64 and d < 16 (d < 15 for
  w = 63: the top digit 15 is excluded by a constraint and its entry
  repeats d = 14), stored per 64-bit limb (x0..x3, y0..y3) as the 16 coefficients
  of the multilinear polynomial in the four bits of d that interpolates
  the limb (coefficient index S = the set of bits multiplied);
- the base-field and group-order moduli as limbs, and the Montgomery
  parameters the unconstrained hint arithmetic uses;
- for secp256k1, the constants of barretenberg 6.0.0's endomorphism split
  (ecc/curves/secp256k1/secp256k1.hpp: fr's cube root of unity and the
  split constants), beta with lambda * (x, y) = (beta * x, y), and the
  odd multiples G, 3G, ..., 255G (affine, Montgomery form) that the hint's
  emulation of bb's secp256k1 multiplication uses.

Every value is computed here with Python integers and checked before it is
written. The files in the tree are this output after `nargo fmt`; `--check`
regenerates in memory and exits 1 if a file differs from it in anything but
whitespace and trailing commas.

Usage: scripts/gen_ecdsa_tables.py [--check] [out_dir]
"""
import os
import re
import sys

BN254_R = 21888242871839275222246405745257275088548364400416034343698204186575808495617


class Curve:
    def __init__(self, p, a, b, n, gx, gy):
        self.p, self.a, self.b, self.n, self.G = p, a, b, n, (gx, gy)

    def on(self, P):
        return (P[1] * P[1] - (P[0] ** 3 + self.a * P[0] + self.b)) % self.p == 0

    def add(self, A, B):
        if A is None:
            return B
        if B is None:
            return A
        p = self.p
        if A[0] == B[0]:
            if (A[1] + B[1]) % p == 0:
                return None
            lam = (3 * A[0] * A[0] + self.a) * pow(2 * A[1], -1, p) % p
        else:
            lam = (B[1] - A[1]) * pow(B[0] - A[0], -1, p) % p
        x = (lam * lam - A[0] - B[0]) % p
        return (x, (lam * (A[0] - x) - A[1]) % p)

    def mul(self, k, P):
        k %= self.n
        R = None
        while k:
            if k & 1:
                R = self.add(R, P)
            P = self.add(P, P)
            k >>= 1
        return R


K1 = Curve(
    2**256 - 2**32 - 977,
    0,
    7,
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
    0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
    0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8,
)
_P256 = 2**256 - 2**224 + 2**192 + 2**96 - 1
R1 = Curve(
    _P256,
    _P256 - 3,
    0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B,
    0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551,
    0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
    0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5,
)


def limbs(v, k=4):
    return [(v >> (64 * i)) & (2**64 - 1) for i in range(k)]


def from_limbs(ls):
    return sum(v << (64 * i) for i, v in enumerate(ls))


# barretenberg 6.0.0, ecc/curves/secp256k1/secp256k1.hpp, FrParams:
# cube_root_of_unity in Montgomery form, and the endomorphism constants.
BB_K1_FR_CUBE_ROOT_MONT = from_limbs(
    [0xF07DEB3DC9926C9E, 0x2C93E7AD83C6944C, 0x73A9660652697D91, 0x532840178558D639]
)
BB_K1_ENDO_G1 = from_limbs([0x6F547FA90ABFE4C4, 0xE4437ED6010E8828])
BB_K1_ENDO_G2 = from_limbs([0xE86C90E49284EB15, 0x3086D221A7D46BCD])
BB_K1_ENDO_MINUS_B1 = from_limbs([0x6F547FA90ABFE4C3, 0xE4437ED6010E8828])
BB_K1_ENDO_B2 = from_limbs([0xE86C90E49284EB15, 0x3086D221A7D46BCD])

W = 64


def fixed_base_table(C):
    """coeff[w][limb][S] for the entries (d + 2) * 16^w * G."""
    out = []
    base = C.G
    for w in range(W):
        pts = []
        acc = C.add(base, base)
        for d in range(16):
            pts.append(acc)
            acc = C.add(acc, base)
        assert pts[3] == C.mul(5 * 16**w, C.G)
        vals = [[limbs(P[0])[l] for P in pts] for l in range(4)]
        vals += [[limbs(P[1])[l] for P in pts] for l in range(4)]
        co = []
        for v in vals:
            c = list(v)
            if w == W - 1:
                # the top digit 15 is never selected (blind.nr, C1)
                c[15] = c[14]
            for bit in range(4):  # Moebius transform over the subset lattice
                for S in range(16):
                    if S >> bit & 1:
                        c[S] -= c[S ^ (1 << bit)]
            for d in range(16 if w < W - 1 else 15):
                assert sum(c[S] for S in range(16) if S & d == S) == v[d]
            co.append(c)
        out.append(co)
        for _ in range(4):
            base = C.add(base, base)
    return out


def fld(c):
    c %= BN254_R
    return hex(c) if c <= BN254_R // 2 else "-" + hex(BN254_R - c)


def arr(v):
    return "[" + ", ".join(hex(x) for x in v) + "]"


def mont(name, m, doc):
    R = 2**256
    m_inv = (-pow(m, -1, 2**64)) % 2**64
    assert (m * m_inv + 1) % 2**64 == 0
    return (
        f"/// {doc}\n"
        f"pub(crate) global {name}: Mont = Mont {{\n"
        f"    m: {arr(limbs(m))},\n"
        f"    m_inv: {hex(m_inv)},\n"
        f"    one: {arr(limbs(R % m))},\n"
        f"    r2: {arr(limbs(R * R % m))},\n"
        f"    r3: {arr(limbs(R * R * R % m))},\n"
        f"    inv320: {arr(limbs(pow(m, -1, 2**320), 5))},\n"
        f"}};\n"
    )


# The ranges of k for which barretenberg 6.0.0's bigfield non-equality check
# treats an integer difference k*p + j*N (N = BN254_R, j != 0) as zero, per
# kind of site (docs/ecdsa-totality.md, S8). They follow from the static
# maximum values of the operands (floor(max / p) on each side) and were
# confirmed by probing bb at every kind of site that can be reached with a
# crafted input (1438 runs for secp256k1).
#   x(A) - x(P) and x(A) - x(A + P) in an incomplete addition: both
#   operands have the default maximum 2^256 - 1.
ALIAS_K_INCOMPLETE = range(-1, 2)
#   The divisor x2 - x1 of a complete addition (its witness is the
#   difference plus 2p): (A) both x-coordinates witnesses; (B) the same
#   when the accumulator's y carries a ROM table's maximum 2p (the select
#   between x2 - x1 and 2y takes the larger maximum); (C) x2 a constant.
ALIAS_K_ADD_A = range(-2, 2)
ALIAS_K_ADD_B = range(-2, 3)
ALIAS_K_ADD_C = range(-2, 1)
#   The divisor 2y: of a doubling (2), of the first doubling of round 0,
#   whose operand is read from the ROM table (4); and of the doubling
#   branch of a complete addition of kind A (3), B (4), C (2).
ALIAS_K_DBL_2 = range(0, 3)
ALIAS_K_DBL_3 = range(0, 4)
ALIAS_K_DBL_4 = range(0, 5)


def alias_values(p, ks, lo, hi):
    """The nonzero integers k*p + j*N, k in ks, j != 0, in [lo, hi)."""
    out = set()
    for k in ks:
        j0 = (lo - k * p) // BN254_R
        j = j0
        while k * p + j * BN254_R < hi:
            v = k * p + j * BN254_R
            if j != 0 and lo <= v:
                out.add(v)
            j += 1
    return sorted(out)


def alias_table(name, doc, vals):
    """(v mod 2^256 as limbs, flag): flag = v < 0 for differences, v >= 2^256 for 2y."""
    s = f"/// {doc}\n"
    s += f"pub(crate) global {name}: [([u64; 4], bool); {len(vals)}] = [\n"
    seen = set()
    for v in vals:
        key = (v % 2**256, v < 0 or v >= 2**256)
        assert key not in seen
        seen.add(key)
        s += f"    ({arr(limbs(v % 2**256))}, {'true' if key[1] else 'false'}),\n"
    s += "];\n"
    return s


def alias_tables(tag, p, add_kinds, dbl_kinds):
    s = alias_table(
        f"{tag}_ALIAS_INC",
        "Differences a - b of two x-coordinates in [0, p) that bb's incomplete additions treat as\n"
        "/// equal although they differ mod p: (a - b mod 2^256, a < b).",
        alias_values(p, ALIAS_K_INCOMPLETE, -p + 1, p),
    )
    for kind, ks in (("A", ALIAS_K_ADD_A), ("B", ALIAS_K_ADD_B), ("C", ALIAS_K_ADD_C)):
        if kind not in add_kinds:
            continue
        s += alias_table(
            f"{tag}_ALIAS_ADD_{kind}",
            f"The same for the divisor x2 - x1 of bb's complete addition, kind {kind} (gen_ecdsa_tables.py).",
            alias_values(p, ks, -p + 1, p),
        )
    for kind, ks in (("2", ALIAS_K_DBL_2), ("3", ALIAS_K_DBL_3), ("4", ALIAS_K_DBL_4)):
        if kind not in dbl_kinds:
            continue
        s += alias_table(
            f"{tag}_ALIAS_DBL_{kind}",
            f"Values 2y, y in [0, p), that a divisor check treats as zero, k up to {kind}: (2y mod 2^256,\n"
            "/// 2y >= 2^256).",
            alias_values(p, ks, 1, 2 * p),
        )
    return s


def k1_extra():
    C = K1
    p, n = C.p, C.n
    lam = BB_K1_FR_CUBE_ROOT_MONT * pow(2**256, -1, n) % n
    assert pow(lam, 3, n) == 1 and lam != 1
    lg = C.mul(lam, C.G)
    beta = lg[0] * pow(C.G[0], -1, p) % p
    assert pow(beta, 3, p) == 1 and lg[1] == C.G[1]
    for k in (2, 12345, n - 7):
        P = C.mul(k, C.G)
        assert C.mul(lam, P) == (beta * P[0] % p, P[1])
    s = "/// bb's fr::cube_root_of_unity lambda (plain), with lambda * P = (beta * x, y).\n"
    s += f"pub(crate) global K1_LAMBDA: [u64; 4] = {arr(limbs(lam))};\n"
    s += "/// beta, Montgomery form mod p.\n"
    s += f"pub(crate) global K1_BETA_MONT: [u64; 4] = {arr(limbs(beta * 2**256 % p))};\n"
    s += "/// bb's endomorphism split constants (FrParams endo_g1, endo_g2, endo_minus_b1, endo_b2).\n"
    s += f"pub(crate) global K1_ENDO_G1: [u64; 4] = {arr(limbs(BB_K1_ENDO_G1))};\n"
    s += f"pub(crate) global K1_ENDO_G2: [u64; 4] = {arr(limbs(BB_K1_ENDO_G2))};\n"
    s += f"pub(crate) global K1_ENDO_MINUS_B1: [u64; 4] = {arr(limbs(BB_K1_ENDO_MINUS_B1))};\n"
    s += f"pub(crate) global K1_ENDO_B2: [u64; 4] = {arr(limbs(BB_K1_ENDO_B2))};\n"
    s += "/// (2i + 1) * G for i < 128, affine (x, y), Montgomery form mod p.\n"
    s += "pub(crate) global K1_G_ODD: [[[u64; 4]; 2]; 128] = [\n"
    P = C.G
    G2 = C.add(C.G, C.G)
    for i in range(128):
        assert P == C.mul(2 * i + 1, C.G)
        s += f"    [{arr(limbs(P[0] * 2**256 % p))}, {arr(limbs(P[1] * 2**256 % p))}],\n"
        P = C.add(P, G2)
    s += "];\n"
    s += alias_tables("K1", p, "ABC", "234")
    return s


# barretenberg 6.0.0, ecc/groups/precomputed_generators_secp256r1_impl.hpp:
# the "biggroup table offset generator" H of secp256r1's fixed-base tables
# (stdlib_circuit_builders/plookup_tables/secp256r1_fixed_base*: entry k of
# window w is k * 2^off(w) * G + 2^w * H, windows of 7 bits x 19, 3 bits,
# 7 bits x 17, 1 bit).
BB_R1_TABLE_OFFSET_GEN = (
    0x12F1907BC0F7CAA93716082E67E3466F525281C6A2CD95990B6D3582B5C1375F,
    0x3111B47A8C982605786143F3D7B4F4C754A1B83AEAA81A7AF6B90176B7328D08,
)
BB_R1_FB_WINDOW_BITS = [7] * 19 + [3] + [7] * 17 + [1]


def r1_extra():
    C = R1
    p = C.p
    H = BB_R1_TABLE_OFFSET_GEN
    assert C.on(H) and sum(BB_R1_FB_WINDOW_BITS) == 256 and len(BB_R1_FB_WINDOW_BITS) == 38
    m = lambda v: arr(limbs(v * 2**256 % p))
    s = f"/// The curve coefficient b, Montgomery form mod p.\npub(crate) global R1_B_MONT: [u64; 4] = {m(C.b)};\n"
    s += "/// bb's secp256r1 fixed-base windows: bit widths, least significant window first.\n"
    s += f"pub(crate) global R1_FB_BITS: [u32; 38] = {BB_R1_FB_WINDOW_BITS};\n"
    s += "/// Per window w: (2^off(w) * G, 2^w * H), affine, Montgomery form (H: bb's table offset\n"
    s += "/// generator; off(w) the sum of the earlier widths). bb's table entry k is k times the\n"
    s += "/// first plus the second.\n"
    s += "pub(crate) global R1_FB_WINDOWS: [[[[u64; 4]; 2]; 2]; 38] = [\n"
    B, Hw, tot = C.G, H, None
    for w in range(38):
        s += f"    [[{m(B[0])}, {m(B[1])}], [{m(Hw[0])}, {m(Hw[1])}]],\n"
        tot = C.add(tot, Hw)
        for _ in range(BB_R1_FB_WINDOW_BITS[w]):
            B = C.add(B, B)
        Hw = C.add(Hw, Hw)
    assert tot == C.mul(2**38 - 1, H)
    s += "];\n"
    s += "/// (2^38 - 1) * H: the constant bb subtracts from the chain's sum.\n"
    s += f"pub(crate) global R1_FB_TOTAL_OFFSET: [[u64; 4]; 2] = [{m(tot[0])}, {m(tot[1])}];\n"
    # the offset subtraction has a constant operand (kind C); the final addition is kind A
    s += alias_tables("R1", p, "AC", "23")
    return s


def render(C, tag, name):
    co = fixed_base_table(C)
    s = (
        f"//! Generated by scripts/gen_ecdsa_tables.py (do not edit): the {name} constants of\n"
        "//! the blinded ECDSA wrapper (module header of blind.nr). The fixed-base table's entry\n"
        "//! (w, d) is the affine point (d + 2) * 16^w * G, stored per 64-bit limb (x0..x3,\n"
        "//! y0..y3) as the 16 coefficients of the multilinear polynomial in the four bits of d\n"
        "//! (coefficient S multiplies the bits in the set S); the top window's digit 15 is unused.\n"
        "\n"
        "use super::bignum::Mont;\n"
        "\n"
        f"pub(crate) global {tag}_FB: [[[Field; 16]; 8]; 64] = [\n"
    )
    for w in range(W):
        s += "    [\n"
        for l in co[w]:
            s += "        [" + ", ".join(fld(c) for c in l) + "],\n"
        s += "    ],\n"
    s += "];\n\n"
    s += f"/// Base-field modulus p, 64-bit limbs.\npub(crate) global {tag}_P: [Field; 4] = {arr(limbs(C.p))};\n"
    s += f"/// Group order n, 64-bit limbs.\npub(crate) global {tag}_N: [Field; 4] = {arr(limbs(C.n))};\n"
    s += mont(f"{tag}_P_MONT", C.p, "Montgomery parameters mod p.")
    s += mont(f"{tag}_N_MONT", C.n, "Montgomery parameters mod n.")
    o = 2 * (16**64 - 1) // 15
    lim = 15 * 16**63
    assert o < C.n and lim < C.n
    # every nonzero residue mod n is o + D or -(o + D) for some D < lim (blind.nr, C1)
    assert C.n > 2 * o and C.n - o < lim
    s += f"/// The blind's offset o = sum 2 * 16^w.\npub(crate) global {tag}_BLIND_O: [u64; 4] = {arr(limbs(o))};\n"
    s += f"/// The bound 15 * 16^63 on the blind's digit part.\npub(crate) global {tag}_BLIND_LIM: [u64; 4] = {arr(limbs(lim))};\n"
    s += f"/// The curve coefficient a, Montgomery form mod p.\npub(crate) global {tag}_A_MONT: [u64; 4] = {arr(limbs(C.a * 2**256 % C.p))};\n"
    if tag == "K1":
        s += k1_extra()
    else:
        s += r1_extra()
    return s


def normalized(text):
    """The text without whitespace and without commas before a closing bracket."""
    t = re.sub(r"\s+", "", text)
    return t.replace(",]", "]").replace(",}", "}")


def main():
    args = sys.argv[1:]
    check = "--check" in args
    args = [a for a in args if a != "--check"]
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out = args[0] if args else os.path.join(root, "noir", "total", "src", "ecdsa")
    assert K1.on(K1.G) and R1.on(R1.G)
    status = 0
    for C, tag, name, fname in ((K1, "K1", "secp256k1", "table_k1.nr"), (R1, "R1", "secp256r1", "table_r1.nr")):
        text = render(C, tag, name)
        path = os.path.join(out, fname)
        if check:
            with open(path) as f:
                if normalized(f.read()) != normalized(text):
                    print(f"{path} differs from the generator's output")
                    status = 1
        else:
            with open(path, "w") as f:
                f.write(text)
            print(path)
    sys.exit(status)


if __name__ == "__main__":
    main()
