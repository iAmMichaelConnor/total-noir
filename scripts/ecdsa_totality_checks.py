#!/usr/bin/env python3
"""The computed facts of docs/ecdsa-totality.md, recomputed with exact
integer and rational arithmetic. Each block prints the fact it checks and
asserts it; the script exits nonzero if any fails. Runs in a few seconds.

  C1  bb's secp256k1 endomorphism split: exact formula, range of both
      halves (below 2^129 in magnitude), and the region containing its
      image
  C2  the lattice {(x, y): x - lambda y == 0 mod n} has no nonzero vector
      with both coordinates below 2^127 in magnitude
  C3  the bound on the dense exact class: sum over the ladder relations of
      rounds 8..15 of area / 2^(pinned bits)
  C4  counting bounds for the other classes and the per-candidate
      rejection bounds used by T2
  C5  every nonzero residue is e (o + D) for an accepted blind (both
      curves)

The finite multiplicity fact (C6 in the document) is checked by
scripts/ecdsa_alias_multiplicity.py, which takes minutes on many cores.
"""
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ecdsa_bb_model as M  # noqa: E402
import gen_ecdsa_tables as T  # noqa: E402

n = M.K1.n
p = M.K1.p
lam = M.LAM
m = T.BB_K1_ENDO_MINUS_B1
b2 = T.BB_K1_ENDO_B2
g1, g2 = T.BB_K1_ENDO_G1, T.BB_K1_ENDO_G2
TWO = 2**256


def cen(x):
    return x if x <= n // 2 else x - n


# ---- C1 -------------------------------------------------------------------
a2 = -cen(lam * b2 % n)
assert cen(lam * m % n) == b2 and a2 > 0
assert g2 == b2 and g1 == m + 1
s1 = TWO - n - a2
assert 0 < s1 < 2**126
assert b2 * b2 + a2 * m == n, "the basis (b2, m), (a2, -b2) has determinant n"
# with c1 = floor(b2 k / 2^256), c2 = floor((m + 1) k / 2^256), e_i the fractional parts:
#   k2 = c2 b2 - c1 m      = t2 + e1 m - e2 b2,    t2 = b2 k / 2^256 in [0, b2)
#   k1 = k - c2 a2 - c1 b2 = t1 + e1 b2 + e2 a2,   t1 = s1 k / 2^256 in [0, s1), s1 = 2^256 - n - a2
rnd = random.Random(5)
for k in [0, 1, 2, n - 1, n - 2, n // 2, n // 3] + [rnd.randrange(n) for _ in range(20000)]:
    k1, k2 = M.k1_split(k)
    c1, c2 = (g2 * k) >> 256, (g1 * k) >> 256
    e1, e2 = F(g2 * k, TWO) - c1, F(g1 * k, TWO) - c2
    assert cen(k2) == c2 * b2 - c1 * m == F(b2 * k, TWO) + e1 * m - e2 * b2
    assert cen(k1) == k - c2 * a2 - c1 * b2 == F(s1 * k, TWO) + e1 * b2 + e2 * a2
    assert (cen(k1) - lam * cen(k2) - k) % n == 0
# hence for every k in [0, n): -b2 < k2 < b2 + m and 0 <= k1 < s1 + b2 + a2
assert b2 + m < 2**129 and s1 + b2 + a2 < 2**129 and b2 < 2**126
# c2 b2 and c1 m are below 2^256, so bb's 256-bit truncation of the products is exact
assert (m + 1) * b2 < TWO and b2 * m < TWO
# the image lies in the hexagon K = {c (s1, b2) + e1 (b2, m) + e2 (a2, -b2): c, e1, e2 in [0, 1]}, the
# parallelogram of area n swept along the segment (s1, b2)
AREA = n + abs(s1 * m - b2 * b2) + abs(s1 * b2 + b2 * a2)
WX, WY = s1 + b2 + a2, 2 * b2 + m
print(f"C1 split: 0 <= k_lo < {float(F(s1 + b2 + a2, 2**128)):.4f} * 2^128, "
      f"{-float(F(b2, 2**128)):.4f} * 2^128 < k_hi < {float(F(b2 + m, 2**128)):.4f} * 2^128; "
      f"image region area = {float(F(AREA, n)):.5f} n")


def class_bound(i, j):
    """Upper bound on #{u in Z_n: (k_lo, k_hi) in one residue class mod (2^i, 2^j)}: the cells
    [0, 2^i) x [0, 2^j) attached to the class's points in K are disjoint and lie in K + cell."""
    return F(AREA + WX * 2**j + WY * 2**i + 2**(i + j), 2**(i + j))


# ---- C2 -------------------------------------------------------------------
# (x, y) = al (b2, m) + be (a2, -b2); al = (b2 x + a2 y) / n, be = (m x - b2 y) / n
B = 2**127
assert (b2 + a2) * B < n and (m + b2) * B < n, "|al|, |be| < 1 for |x|, |y| <= 2^127: only the zero vector"
print("C2 lattice: no nonzero (x, y) with x == lambda y mod n and |x|, |y| <= 2^127")

# ---- C3 -------------------------------------------------------------------
dense = F(0)
count7 = 0
for i in range(8, 16):
    for j in range(6):
        for kind in ("eq", "neg", "ret"):
            n_lo = (15 - i) + (j < 3) + (j == 3 and kind != "ret")
            n_hi = (15 - i) + (j < 2) + (j == 2 and kind != "ret")
            bl, bh = 3 + 8 * n_lo, 4 + 8 * n_hi
            assert bl <= 67 and bh <= 68
            dense += class_bound(bl, bh)
            count7 += (bl + bh == 7)
DENSE = dense / n
assert count7 == 7
print(f"C3 dense exact class: at most {float(DENSE):.5f} n scalars u1 (7 relations pin 7 bits)")

# ---- C4 -------------------------------------------------------------------
INC = len(M.AL_K1.inc)
ADD = len(M.AL_K1.add['B'])
DBL = len(M.AL_K1.dbl[4])
# exact, non-dense: 288 relations, at most one u1 per prefix value (rounds 0..7: at most 2^128
# values) or per suffix value (rounds 8..15: at most 2^(67 + 68 + 8))
nondense = F(288 * 2**143, n)
# aliasing at key-independent sites, by counting (document, section 5.4):
#   ladder steps adding a multiple of G in rounds 8..14 and step (15, 2): per digit and alias value
#   at most 2 accumulators (check 1) and 6 (check 2); a suffix value pins both halves
g_sites = F(0)
for i in range(8, 16):
    for j in (2, 3):
        if (i, j) == (15, 3):
            continue
        n_lo = (15 - i) + 1
        n_hi = (15 - i) + (j == 2)
        g_sites += 256 * 8 * INC * class_bound(3 + 8 * n_lo, 4 + 8 * n_hi)
#   doublings of rounds 8..15: at most 3 |DBL| operands each
d_sites = sum(2 * 3 * DBL * class_bound(3 + 8 * (16 - i), 4 + 8 * (16 - i)) for i in range(8, 16))
#   the small sites, given C6 (a final point R fails at most one comparison there): the largest
#   set of scalars sharing one comparison is the one-bit class of k_hi at the skew addition of the
#   endo generator together with one (3, 4)-bit class at the fragment addition before it
small = class_bound(0, 1) + class_bound(3, 4)
#   key-dependent operand against a key-independent one: at most 6 |alias| keys per prefix or
#   suffix value
keydep = F((96 * 2 * 6 * INC + 40 * 3 * max(ADD, DBL)) * 2**143, n)
P_K1 = DENSE + nondense + g_sites / n + d_sites / n + small / n + keydep
print(f"C4 secp256k1 per-candidate rejection bound (without the named assumption's epsilon): "
      f"{float(P_K1):.4f} = dense {float(DENSE):.4f} + small aliasing sites {float(small / n):.4f} "
      f"+ other key-independent aliasing {float((g_sites + d_sites) / n):.4f} + negligible")
assert P_K1 < F(8, 10)
TRIES = 256
import math  # noqa: E402
print(f"   all {TRIES} candidates rejected: below 2^{TRIES * math.log2(float(P_K1)):.1f}")

# secp256r1: the fixed-base chain (document, section 6)
n2 = M.R1.n
off = M.FB_OFF
INC2, ADD2 = len(M.AL_R1.inc), len(M.AL_R1.add['A'])
# sites 1 and 2 exhaustively: no 21-bit prefix of u1 meets an exact or aliasing x-collision there
if not M._fb_base:
    M._fb_init()
C2_ = M.R1
tab = [[C2_.add(C2_.mul(k, M._fb_base[w][0]), M._fb_base[w][1]) for k in range(128)] for w in range(3)]
x2 = {P[0] for P in tab[2]}
for d0 in range(128):
    for d1 in range(128):
        A, Bp = tab[0][d0], tab[1][d1]
        assert A[0] != Bp[0] and (A[0] - Bp[0]) not in M.AL_R1.inc
        S = C2_.add(A, Bp)
        assert S[0] not in x2
        for v in M.AL_R1.inc:
            # x(L_2) - x(S_1) == v
            assert not (0 <= S[0] + v < C2_.p and S[0] + v in x2)
exact_fb = sum(F(2, 2**off[i + 1]) for i in range(3, 37)) + F(3, n2)
alias_fb = sum(F(2 * INC2 * 2**M.FB_BITS[i], 2**off[i + 1]) for i in range(3, 38))
# off(i + 1) bits of u1 fix the site's operands; residues mod 2^off below n: at most n / 2^off + 1 scalars each
slack = F(37 * 2 * (1 + INC2 * 128) * 1, n2)
P_R1 = exact_fb + alias_fb + slack + F(2 * ADD2 + 10 * ADD2 + 3, n2)
print(f"C4 secp256r1 per-candidate rejection bound: {float(P_R1):.2e} "
      f"(sites 1 and 2 of the chain checked exhaustively; from site 3 on: exact collisions "
      f"{float(exact_fb):.2e}, aliasing {float(alias_fb):.2e})")
assert P_R1 < F(1, 2**14)

# ---- C5 -------------------------------------------------------------------
for C in (M.K1, M.R1):
    o, lim = 2 * (16**64 - 1) // 15, 15 * 16**63
    assert o < C.n and C.n > 2 * o and C.n - o < lim < C.n
    for beta in [1, 2, C.n - 1, o, o - 1, o + 1, (o + lim) % C.n, (o + lim - 1) % C.n, (o + lim + 1) % C.n,
                 C.n - o, C.n - o - 1] + [rnd.randrange(1, C.n) for _ in range(20000)]:
        x = (beta - o) % C.n
        if x >= lim:
            x = (-beta - o) % C.n
            assert x < lim and (-(o + x) - beta) % C.n == 0
        # the chain of blind.nr never meets a + t == 0 mod n except for b' == 0 mod n
        assert (o + x) % C.n != 0
    # C3 of blind.nr at j = 63: a in [o63, o63 + 16^63), t = (d + 2) 16^63, d <= 14
    o63 = 2 * (16**63 - 1) // 15
    assert 2**256 - C.n < o63 and 19 * 16**62 < C.n
print("C5 blind coverage and the chain's range lemma hold on both curves")
print("all checks passed")
