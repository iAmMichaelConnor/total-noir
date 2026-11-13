#!/usr/bin/env python3
"""Reference model of barretenberg 6.0.0's ECDSA multiplications
(aztec-packages v6.0.0, commit 0219f11d): which witness-dependent assertion,
if any, bb's own witness violates for a key Q and scalars u1 = z/s, u2 = r/s.

  k1_sites(Q, u1, u2)   secp256k1_ecdsa_mul (biggroup_secp256k1.hpp)
  r1_sites(Q, u1, u2)   secp256r1_ecdsa_mul (biggroup_secp256r1.hpp)

Both run bb's computation on real affine points with Python integers and
return the list of violated sites; an empty list predicts that `bb prove`
succeeds on the raw black-box call. Sites are (name, kind): kind 'eq',
'neg', 'ret' for the exact collisions A = P, A = -P, 2A + P = O of an
incomplete addition, 'alias' for an integer difference that
bigfield::assert_is_not_equal treats as zero although it is nonzero mod p.
docs/ecdsa-totality.md lists the source facts this follows; the constants
come from scripts/gen_ecdsa_tables.py. scripts/ecdsa_differential.py
compares the model, the library's Noir emulation and bb.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_ecdsa_tables as T  # noqa: E402

NAT = T.BN254_R
K1, R1 = T.K1, T.R1


def neg(C, A):
    return None if A is None else (A[0], (-A[1]) % C.p)


def lift(C, x, odd=None):
    """A point with this x, or None."""
    if not 0 <= x < C.p:
        return None
    y = pow((x**3 + C.a * x + C.b) % C.p, (C.p + 1) // 4, C.p)
    if (y * y - x**3 - C.a * x - C.b) % C.p:
        return None
    if odd is not None and y % 2 != odd:
        y = C.p - y
    return (x, y)


def alias_set(C, ks, lo, hi):
    return set(T.alias_values(C.p, ks, lo, hi))


class Alias:
    """The aliasing sets of one curve, per kind of site (gen_ecdsa_tables.py)."""

    def __init__(self, C):
        self.inc = alias_set(C, T.ALIAS_K_INCOMPLETE, -C.p + 1, C.p)
        self.add = {k: alias_set(C, ks, -C.p + 1, C.p)
                    for k, ks in (('A', T.ALIAS_K_ADD_A), ('B', T.ALIAS_K_ADD_B), ('C', T.ALIAS_K_ADD_C))}
        self.dbl = {k: alias_set(C, ks, 1, 2 * C.p)
                    for k, ks in ((2, T.ALIAS_K_DBL_2), (3, T.ALIAS_K_DBL_3), (4, T.ALIAS_K_DBL_4))}


AL_K1 = Alias(K1)
AL_R1 = Alias(R1)
# complete-addition kind -> the k bound of its doubling branch
DBL_OF = {'A': 3, 'B': 4, 'C': 2}


def complete_add(C, al, A, B, site, viol, kind='A'):
    """bb's add_internal for a finite B: divisor 1 (A infinite, or B = -A),
    2 y(A) (B = A) or x(B) - x(A)."""
    if A is not None:
        if A[0] == B[0]:
            if A[1] == B[1] and 2 * A[1] in al.dbl[DBL_OF[kind]]:
                viol.append((site, 'alias'))
        elif B[0] - A[0] in al.add[kind]:
            viol.append((site, 'alias'))
    return C.add(A, B)


# ---- secp256k1 ----------------------------------------------------------
n1 = K1.n
LAM = T.BB_K1_FR_CUBE_ROOT_MONT * pow(2**256, -1, n1) % n1
ML = (-LAM) % n1
BETA = K1.mul(LAM, K1.G)[0] * pow(K1.G[0], -1, K1.p) % K1.p


def endo(A):
    """bb's endomorphism table entry for the plain entry A: (beta x, -y) = -lambda A."""
    return (A[0] * BETA % K1.p, (-A[1]) % K1.p)


def k1_split(k):
    """field::split_into_endomorphism_scalars (large-modulus path): residues
    (k1, k2) mod n with k = k1 - lambda k2."""
    c1 = (T.BB_K1_ENDO_G2 * k) >> 256
    c2 = (T.BB_K1_ENDO_G1 * k) >> 256
    q1 = (c1 * T.BB_K1_ENDO_MINUS_B1) & (2**256 - 1)
    q2 = (c2 * T.BB_K1_ENDO_B2) & (2**256 - 1)
    k2 = (q2 - q1) % n1
    return (k2 * LAM + k) % n1, k2


def fixed_wnaf(kv, num_bits, w):
    """ecc/groups/wnaf.hpp fixed_wnaf<num_bits, 1, w>: (signed odd digits,
    most significant first, skew)."""
    entries = (num_bits + w - 1) // w
    final_bits = w if num_bits % w == 0 else num_bits % w
    mask = (1 << w) - 1
    skew = (kv & 1) == 0
    out = [None] * entries
    previous = (kv & mask) + skew
    for r in range(1, entries - 1):
        sl = (kv >> (r * w)) & mask
        pred = (sl & 1) == 0
        out[entries - r] = previous - (pred << w)
        previous = sl + pred
    sl = (kv >> ((entries - 1) * w)) & ((1 << final_bits) - 1)
    pred = (sl & 1) == 0
    out[1] = previous - (pred << w)
    out[0] = sl + pred
    return out, skew


def k1_wnaf(k_res, w, stagger):
    """compute_secp256k1_endo_wnaf's sign handling and
    compute_secp256k1_single_wnaf for one half (a residue mod n):
    (digits, frag, skew) with the signed half equal to
    2^stagger sum(d_i 2^(w i)) + frag + skew; frag is None for stagger 0;
    skew in {-1, 0, 1} is positive_skew - negative_skew."""
    negative = k_res.bit_length() > 129
    k = n1 - k_res if negative else k_res
    assert k.bit_length() <= 129, "biggroup_nafs: half > 129 bits"
    frag_u = k & ((1 << stagger) - 1)
    digs, wskew = fixed_wnaf(k >> stagger, 129 - stagger, w)
    assert len(digs) == (129 + w - 1 - stagger) // w
    if stagger == 0:
        frag, oskew = None, wskew
    else:
        f = -frag_u if negative else frag_u
        if wskew:
            f += (1 << stagger) if negative else -(1 << stagger)
        oskew = (frag_u & 1) == 0
        if oskew:
            f += -1 if negative else 1
        assert f % 2 == 1 and abs(f) < (1 << w)
        frag = f
    if negative:
        digs = [-d for d in digs]
    skew = (1 if negative else -1) if oskew else 0
    val = (sum(d << (w * i) for i, d in enumerate(reversed(digs))) << stagger) + (frag or 0) + skew
    assert val == (-k if negative else k), "wnaf reconstruction"
    return digs, frag, skew


def k1_digits(u1, u2):
    a_lo, a_hi = k1_split(u1 % n1)
    b_lo, b_hi = k1_split(u2 % n1)
    return dict(u1lo=k1_wnaf(a_lo, 8, 2), u1hi=k1_wnaf(a_hi, 8, 3),
                u2lo=k1_wnaf(b_lo, 4, 0), u2hi=k1_wnaf(b_hi, 4, 1))


def k1_schedule(D):
    """The 96 ladder additions: (round, step, stream, digit); streams QL
    (base Q), QH (-lambda Q), GH (-lambda G), GL (G)."""
    out = []
    for i in range(16):
        out += [(i, 0, 'QH', D['u2hi'][0][2 * i]), (i, 1, 'QL', D['u2lo'][0][2 * i + 1]),
                (i, 2, 'GH', D['u1hi'][0][i]), (i, 3, 'GL', D['u1lo'][0][i]),
                (i, 4, 'QH', D['u2hi'][0][2 * i + 1]), (i, 5, 'QL', D['u2lo'][0][2 * i + 2])]
    return out


def k1_scalar_trace(q, u1, u2):
    """With Q = q G: per ladder step (round, step, a, b, pa, pb), the
    accumulator a q + b and the added point pa q + pb before the step, mod
    n. For solving keys that hit a chosen site."""
    D = k1_digits(u1, u2)
    co = dict(QL=(1, 0), QH=(ML, 0), GH=(0, ML), GL=(0, 1))
    a, b = D['u2lo'][0][0], 0
    out = []
    for (i, j, st, d) in k1_schedule(D):
        if j == 0:
            a, b = 4 * a, 4 * b
        pa, pb = d * co[st][0], d * co[st][1]
        out.append((i, j, a % n1, b % n1, pa % n1, pb % n1))
        a, b = 2 * a + pa, 2 * b + pb
    return out


def k1_sites(Q, u1, u2, al=AL_K1):
    C = K1
    D = k1_digits(u1, u2)
    viol = []

    def dbl(A, site):
        if 2 * A[1] in al.dbl[4 if site == 'r0.dbl0' else 2]:
            viol.append((site, 'alias'))
        return C.add(A, A)

    d2 = dbl(Q, 'table.dbl')
    odd = [Q]
    for i in range(1, 8):
        odd.append(complete_add(C, al, odd[-1], d2, f'table.add{i}', viol))

    def tpoint(st, d):
        b = odd[abs(d) // 2] if st[0] == 'Q' else C.mul(abs(d), C.G)
        if d < 0:
            b = neg(C, b)
        return endo(b) if st[1] == 'H' else b

    A = tpoint('QL', D['u2lo'][0][0])
    for (i, j, st, d) in k1_schedule(D):
        if j == 0:
            A = dbl(A, f'r{i}.dbl0')
            A = dbl(A, f'r{i}.dbl1')
        Pt = tpoint(st, d)
        site = f'r{i}.s{j}'
        if A == Pt:
            return viol + [(site, 'eq')]
        if A == neg(C, Pt):
            return viol + [(site, 'neg')]
        if A[0] - Pt[0] in al.inc:
            viol.append((site + '.c1', 'alias'))
        S = C.add(A, Pt)
        if S[0] == A[0]:
            return viol + [(site, 'ret')]
        if A[0] - S[0] in al.inc:
            viol.append((site + '.c2', 'alias'))
        A = C.add(S, A)
    for t, (st, key) in enumerate((('GH', 'u1hi'), ('QH', 'u2hi'), ('GL', 'u1lo'))):
        A = complete_add(C, al, A, tpoint(st, D[key][1]), f'frag{t}', viol, 'AAB'[t])
    for t, (st, key) in enumerate((('GL', 'u1lo'), ('GH', 'u1hi'), ('QL', 'u2lo'), ('QH', 'u2hi'))):
        # conditional_add: accumulator + base (negated for a negative skew), always evaluated
        sk = D[key][2]
        cand = complete_add(C, al, A, tpoint(st, -1 if sk < 0 else 1), f'skew{t}', viol, 'CCAB'[t])
        if sk:
            A = cand
    assert A == C.add(C.mul(u1, C.G), C.mul(u2, Q)), "model does not reconstruct u1 G + u2 Q"
    return viol


# ---- secp256r1 ----------------------------------------------------------
n2 = R1.n
H_TAB = T.BB_R1_TABLE_OFFSET_GEN
# precomputed_generators_secp256r1_impl.hpp, "biggroup offset generator"
H_OFF = (0xB61BD0F5671BC04EC041799E87E735AF4ED40920C6CA71E63C8010FF162BD90A,
         0x338540B43F94CBFE32A1E62D192EA7D5827F4A4A66BB781A02321033110E492B)
FB_BITS = T.BB_R1_FB_WINDOW_BITS
FB_OFF = [sum(FB_BITS[:w]) for w in range(39)]
assert R1.on(H_OFF)
_fb_base = []


def _fb_init():
    B, Hw = R1.G, H_TAB
    for w in range(38):
        _fb_base.append((B, Hw))
        for _ in range(FB_BITS[w]):
            B = R1.add(B, B)
        Hw = R1.add(Hw, Hw)


def r1_fake_glv(s):
    """compute_secp256r1_fake_glv_decomposition: (alpha, |beta|, beta < 0)."""
    u_prev, u_curr, v_prev, v_curr = n2, s, 0, 1
    while u_curr >= 1 << 128:
        q = u_prev // u_curr
        u_prev, u_curr = u_curr, u_prev - q * u_curr
        v_prev, v_curr = v_curr, (v_prev - q * v_curr) % n2
    return (u_curr, v_curr, False) if v_curr <= n2 >> 1 else (u_curr, n2 - v_curr, True)


def r1_naf(k, rounds=128):
    """compute_naf: entries[0..rounds) (True = -1), entries[rounds] = skew."""
    skew = (k & 1) == 0
    k += skew
    e = [False] * (rounds + 1)
    e[rounds] = skew
    for i in range(rounds - 1):
        e[rounds - i - 1] = not ((k >> (i + 1)) & 1)
    return e


def r1_sites(Q, u1, u2, al=AL_R1, parts=('fixed', 'msm', 'final')):
    """parts: 'fixed' the fixed-base chain and the offset subtraction,
    'msm' the two-point multiplication, 'final' T1 + T2. The library's
    hint follows 'fixed' and 'final' only."""
    C = R1
    if not _fb_base:
        _fb_init()
    viol = []
    u1 %= n2
    u2 %= n2
    u2s = 2 if u2 in (0, 1, n2 - 1) else u2
    # T1 = u1 G: chain over the 38 table points, then minus (2^38 - 1) H
    L = [C.add(C.mul((u1 >> FB_OFF[w]) & ((1 << FB_BITS[w]) - 1), _fb_base[w][0]), _fb_base[w][1]) for w in range(38)]
    S = L[0]
    fixed_ok = True
    for i in range(1, 38):
        if S[0] == L[i][0]:
            if 'fixed' in parts:
                viol.append((f'chain{i}', 'eq' if S == L[i] else 'neg'))
            fixed_ok = False
            break
        d = S[0] - L[i][0] if i == 1 else L[i][0] - S[0]
        if d in al.inc and 'fixed' in parts:
            viol.append((f'chain{i}', 'alias'))
        S = C.add(S, L[i])
    if not fixed_ok:
        return viol
    v = []
    T1 = complete_add(C, al, S, neg(C, C.mul(2**38 - 1, H_TAB)), 'offset', v, 'C')
    if 'fixed' in parts:
        viol += v
    assert T1 == C.mul(u1, C.G)
    T2 = C.mul(u2s, Q)
    if 'msm' in parts:
        viol += _r1_msm(Q, T2, u2s, al)
    v = []
    complete_add(C, al, T1, T2, 'final', v)
    if 'final' in parts:
        viol += v
    return viol


def _r1_msm(Q, T2, u2s, al):
    """batch_mul({Q, -+T2}, {alpha, |beta|}, 128 bits, no edge cases)."""
    C = R1
    viol = []
    alpha, beta_abs, beta_neg = r1_fake_glv(u2s)
    P0, P1 = Q, (T2 if beta_neg else neg(C, T2))
    if P0[0] == P1[0]:
        return [('msm.table', 'eq')]
    if P1[0] - P0[0] in al.inc:
        viol.append(('msm.table', 'alias'))
    tab = [C.add(P1, P0), C.add(P1, neg(C, P0))]
    tab += [neg(C, tab[1]), neg(C, tab[0])]
    na, nb = r1_naf(alpha), r1_naf(beta_abs)
    if H_OFF[0] == tab[0][0]:
        return viol + [('msm.init', 'eq')]
    if H_OFF[0] - tab[0][0] in al.inc:
        viol.append(('msm.init', 'alias'))
    A = C.add(H_OFF, tab[0])
    for r in range(1, 128):
        Dp = tab[na[r] + 2 * nb[r]]
        if A[0] == Dp[0]:
            return viol + [(f'msm.r{r}', 'eq' if A == Dp else 'neg')]
        if A[0] - Dp[0] in al.inc:
            viol.append((f'msm.r{r}.c1', 'alias'))
        S = C.add(A, Dp)
        if S[0] == A[0]:
            return viol + [(f'msm.r{r}', 'ret')]
        if A[0] - S[0] in al.inc:
            viol.append((f'msm.r{r}.c2', 'alias'))
        A = C.add(S, A)
    for t, (e, Pt) in enumerate(((na[128], P0), (nb[128], P1))):
        cand = complete_add(C, al, A, neg(C, Pt), f'msm.skew{t}', viol)
        if e:
            A = cand
    assert A == C.mul(1 << 127, H_OFF), "the two-point multiplication must end at 2^127 H"
    return viol


def verdict(C, Q, r, s, z):
    """The documented verdict of the library entries for an on-curve key:
    the gates (p - n <= r < n; on secp256r1 also r != s, r + s != n) and
    textbook ECDSA with low s."""
    if not (C.p - C.n <= r < C.n):
        return False
    if C is R1 and (r == s or r + s == C.n):
        return False
    if not 0 < s < (C.n + 1) // 2:
        return False
    w = pow(s, -1, C.n)
    R = C.add(C.mul(z * w, C.G), C.mul(r * w, Q))
    return R is not None and R[0] % C.n == r


if __name__ == '__main__':
    import random
    rnd = random.Random(7)
    for _ in range(40):
        q, u1, u2 = rnd.randrange(1, n1), rnd.randrange(n1), rnd.randrange(n1)
        assert not k1_sites(K1.mul(q, K1.G), u1, u2)
        q, u1, u2 = rnd.randrange(1, n2), rnd.randrange(n2), rnd.randrange(2, n2 - 1)
        assert not r1_sites(R1.mul(q, R1.G), u1, u2)
    print('model self-check ok')
