"""Shared helpers: F_p[x] arithmetic (Kronecker substitution on Python ints), root finding over F_p,
cube roots, curve lifts, and x-coordinate maps of small endomorphisms of secp256k1.
Pure standard library; used by scripts/ecdsa_alias_multiplicity.py."""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ecdsa_bb_model as _M  # noqa: E402

P, n, NAT, G, ML, BETA, endo = _M.K1.p, _M.K1.n, _M.NAT, _M.K1.G, _M.ML, _M.BETA, _M.endo
add = _M.K1.add


def neg(A):
    return _M.neg(_M.K1, A)


def mul(k, A):
    return _M.K1.mul(k, A)


def on_curve(A):
    return A is None or _M.K1.on(A)

SB = 67                      # bytes per Kronecker slot (536 bits > 512 + log2(len))


# ---------------------------------------------------------------- polynomials (lists, low degree first)
def ptrim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def _pack(a):
    return int.from_bytes(b''.join(c.to_bytes(SB, 'little') for c in a), 'little')


def _unpack(v, cnt):
    bs = v.to_bytes(cnt * SB, 'little')
    return [int.from_bytes(bs[i * SB:(i + 1) * SB], 'little') % P for i in range(cnt)]


def pmul(a, b):
    if not a or not b:
        return []
    if len(a) < 4 or len(b) < 4:
        out = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    out[i + j] += x * y
        return ptrim([c % P for c in out])
    return ptrim(_unpack(_pack(a) * _pack(b), len(a) + len(b) - 1))


def padd(a, b):
    if len(a) < len(b):
        a, b = b, a
    return ptrim([(x + (b[i] if i < len(b) else 0)) % P for i, x in enumerate(a)])


def psub(a, b):
    m = max(len(a), len(b))
    return ptrim([((a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)) % P for i in range(m)])


def pscale(a, c):
    return ptrim([x * c % P for x in a])


def pdivmod(a, f):
    """schoolbook; f nonzero"""
    a = a[:]
    df = len(f) - 1
    inv = pow(f[-1], -1, P)
    q = [0] * max(len(a) - df, 0)
    for i in range(len(a) - 1, df - 1, -1):
        c = a[i] * inv % P
        if c:
            q[i - df] = c
            for j in range(df + 1):
                a[i - df + j] = (a[i - df + j] - c * f[j]) % P
    return ptrim(q), ptrim(a[:df])


def pmonic(a):
    return pscale(a, pow(a[-1], -1, P)) if a else a


def pgcd(a, b):
    a, b = a[:], b[:]
    while b:
        a, b = b, pdivmod(a, b)[1]
    return pmonic(a)


def peval(a, x):
    r = 0
    for c in reversed(a):
        r = (r * x + c) % P
    return r


class ModPoly:
    """Reduction modulo a fixed monic f (degree d) of polynomials of degree <= 2d - 2, by Newton inverse."""

    def __init__(self, f):
        self.f = pmonic(f)
        self.d = len(self.f) - 1
        d = self.d
        if d > 24:
            rf = self.f[::-1]            # reversed f, constant term 1
            g = [1]
            k = 1
            while k < d:
                k = min(2 * k, d)
                e = pmul(pmul(g, g)[:k], rf[:k])[:k]
                g = psub(pscale(g, 2), e)[:k]
                g += [0] * (k - len(g))
            self.rinv = ptrim(g[:d])     # rf^-1 mod x^d
        else:
            self.rinv = None

    def red(self, a):
        d = self.d
        if len(a) <= d:
            return a
        if self.rinv is None:
            return pdivmod(a, self.f)[1]
        m = len(a) - 1
        k = m - d + 1                    # quotient has k coefficients
        ra = a[::-1][:k]
        q = pmul(ra, self.rinv[:k])[:k]
        q += [0] * (k - len(q))
        q = ptrim(q[::-1])
        r = psub(a[:d], pmul(q, self.f)[:d])
        return ptrim(r[:d])

    def mul(self, a, b):
        return self.red(pmul(a, b))

    def pow(self, a, e):
        r = [1]
        for bit in bin(e)[2:]:
            r = self.mul(r, r)
            if bit == '1':
                r = self.mul(r, a)
        return r


def roots(f, rnd=None):
    """All roots in F_p of f (distinct)."""
    rnd = rnd or random.Random(1)
    f = pmonic(ptrim(f[:]))
    if len(f) <= 1:
        return []
    out = []
    while f and f[0] == 0:              # root 0
        f = f[1:]
        if 0 not in out:
            out.append(0)
    if len(f) <= 1:
        return out
    M = ModPoly(f)
    xp = M.pow([0, 1] if M.d > 1 else M.red([0, 1]), P)
    g = pgcd(psub(xp, [0, 1]), f)

    def split(g):
        if len(g) <= 1:
            return
        if len(g) == 2:
            out.append((-g[0]) % P)
            return
        Mg = ModPoly(g)
        while True:
            a = rnd.randrange(P)
            h = Mg.pow(Mg.red([a, 1]), (P - 1) // 2)
            h = pgcd(psub(h, [1]), g)
            if 1 < len(h) < len(g):
                split(h)
                split(pdivmod(g, h)[0])
                return

    split(g)
    return out


# ---------------------------------------------------------------- curve helpers
def lift(x):
    """a point with this x (the square-root sign is whatever the exponentiation gives), or None"""
    if not 0 <= x < P:
        return None
    y = pow((x ** 3 + 7) % P, (P + 1) // 4, P)
    return (x, y) if (y * y - x ** 3 - 7) % P == 0 else None


assert P % 9 == 7
def cube_roots(c):
    """all cube roots of c mod p"""
    c %= P
    if c == 0:
        return [0]
    if pow(c, (P - 1) // 3, P) != 1:
        return []
    r = pow(c, (P + 2) // 9, P)
    if pow(r, 3, P) != c:               # exponent formula not valid for this residue: generic root finder
        return roots([(-c) % P, 0, 0, 1])
    return [r, r * BETA % P, r * BETA * BETA % P]


def points_with_y(y):
    return [(x, y % P) for x in cube_roots(y * y - 7)]


def emul(g, W):
    """(a + b*ML) * W for the Eisenstein pair g = (a, b)"""
    return mul((g[0] + g[1] * ML) % n, W)


def norm(g):
    a, b = g
    return a * a + a * b + b * b       # ML^2 - ML + 1 = 0


_xmap_cache = {}


def xmap(g, rnd=None):
    """(U, V): x((a + b ML) W) = U(x(W)) / V(x(W)), deg U = N(g), deg V <= N(g) - 1, by interpolation
    from random curve points (exact: verified on fresh points)."""
    g = tuple(g)
    if g in _xmap_cache:
        return _xmap_cache[g]
    rnd = rnd or random.Random(hash(g) & 0xffffffff)
    N = norm(g)
    assert N > 0
    if g == (1, 0):
        res = ([0, 1], [1])
    elif g == (-1, 0):
        res = ([0, 1], [1])
    else:
        unk = 2 * N + 1                # u_0..u_N, v_0..v_{N-1}
        rows = []
        while len(rows) < unk + 2:
            W = lift(rnd.randrange(P))
            if W is None:
                continue
            X = emul(g, W)
            if X is None:
                continue
            x = W[0]
            pw = [1]
            for _ in range(N):
                pw.append(pw[-1] * x % P)
            rows.append(pw + [(-X[0] * pw[i]) % P for i in range(N)])
        # nullspace by Gaussian elimination
        piv = []
        r = 0
        m = len(rows)
        for c in range(unk):
            pr = next((i for i in range(r, m) if rows[i][c]), None)
            if pr is None:
                continue
            rows[r], rows[pr] = rows[pr], rows[r]
            inv = pow(rows[r][c], -1, P)
            rows[r] = [v * inv % P for v in rows[r]]
            rr = rows[r]
            for i in range(m):
                if i != r and rows[i][c]:
                    f = rows[i][c]
                    rows[i] = [(v - f * w) % P for v, w in zip(rows[i], rr)]
            piv.append(c)
            r += 1
        free = [c for c in range(unk) if c not in piv]
        assert len(free) == 1, (g, len(free))
        fc = free[0]
        sol = [0] * unk
        sol[fc] = 1
        for i, c in enumerate(piv):
            sol[c] = (-rows[i][fc]) % P
        res = (ptrim(sol[:N + 1]), ptrim(sol[N + 1:]))
    U, V = res
    for _ in range(3):                 # exactness check on fresh points
        W = None
        while W is None:
            W = lift(rnd.randrange(P))
        X = emul(g, W)
        assert (peval(U, W[0]) - X[0] * peval(V, W[0])) % P == 0
    _xmap_cache[g] = res
    return res


def solve_xdiff(g1, g2, delta, rnd=None):
    """All curve points W (one per x; the sign of y is irrelevant) with x(g1 W) - x(g2 W) = delta (integers
    reduced mod p here; the caller checks the exact integer difference)."""
    U1, V1 = xmap(g1)
    U2, V2 = xmap(g2)
    f = psub(psub(pmul(U1, V2), pmul(U2, V1)), pscale(pmul(V1, V2), delta % P))
    out = []
    for x in roots(f, rnd):
        W = lift(x)
        if W is None:
            continue
        A, B = emul(g1, W), emul(g2, W)
        if A is None or B is None:
            continue
        if (A[0] - B[0] - delta) % P == 0:
            out.append(W)
    return out


def solve_x_minus_xsum(T, c, rnd=None):
    """All curve points S with x(S) - x(S + T) = c (mod p), T a fixed affine point, S != +-T, S != inf.
    Eliminate y_S:  x3 = lam^2 - x - xT with lam = (yS - yT)/(x - xT) and x3 = x - c gives
        2 yS yT = x^3 + 7 + yT^2 - (2x + xT - c)(x - xT)^2 ;  squaring: degree-6 polynomial in x."""
    xT, yT = T
    c %= P
    # h(x) = x^3 + 7 + yT^2 - (2x + xT - c)(x - xT)^2
    h = psub([(7 + yT * yT) % P, 0, 0, 1], pmul([(xT - c) % P, 2], pmul([(-xT) % P, 1], [(-xT) % P, 1])))
    f = psub(pmul(h, h), pscale([7, 0, 0, 1], 4 * yT * yT % P))
    out = []
    i2y = pow(2 * yT, -1, P)
    for x in roots(f, rnd):
        if x == xT:
            continue
        y = peval(h, x) * i2y % P
        S = (x, y)
        if not on_curve(S):
            continue
        R = add(S, T)
        if R is None:
            continue
        if (S[0] - R[0] - c) % P == 0:
            out.append(S)
    return out


if __name__ == '__main__':
    rnd = random.Random(5)
    # polynomial self-tests
    for d in (3, 7, 30, 90):
        f = [rnd.randrange(P) for _ in range(d)] + [1]
        M = ModPoly(f)
        a = [rnd.randrange(P) for _ in range(d)]
        b = [rnd.randrange(P) for _ in range(d)]
        assert M.mul(a, b) == pdivmod(pmul(a, b), f)[1]
    rs = [rnd.randrange(P) for _ in range(5)]
    f = [1]
    for r in rs:
        f = pmul(f, [(-r) % P, 1])
    f = pmul(f, [3, 0, 1])              # x^2 + 3 may or may not split
    got = roots(f)
    assert set(rs) <= set(got) and all(peval(f, r) == 0 for r in got)
    # cube roots
    cnt = 0
    for _ in range(30):
        c = rnd.randrange(P)
        cr = cube_roots(c)
        assert all(pow(r, 3, P) == c for r in cr) and len(cr) in (0, 3)
        cnt += bool(cr)
    assert cnt > 3
    # endomorphism x-maps
    W = lift(5) or lift(6) or lift(7)
    for g in ((2, 0), (0, 1), (3, 1), (4, -1), (-8, 3)):
        U, V = xmap(g)
        assert len(U) - 1 == norm(g), (g, len(U), norm(g))
    S = solve_xdiff((2, 0), (1, 0), 12345)
    for W in S:
        assert (mul(2, W)[0] - W[0] - 12345) % P == 0
    T = mul(77, G)
    A = lift(1234567) or lift(1234568)
    c = (A[0] - add(A, T)[0]) % P
    assert A in solve_x_minus_xsum(T, c)
    print('ecp self-test ok; solve_xdiff example roots:', len(S))
