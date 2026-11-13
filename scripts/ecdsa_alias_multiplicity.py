#!/usr/bin/env python3
"""Computed fact C6 of docs/ecdsa-totality.md: the finite multiplicity of the aliasing "small
sites" of bb 6.0.0's secp256k1_ecdsa_mul.

usage: scripts/ecdsa_alias_multiplicity.py [--kmax 6] [--workers N] [--out results.md]
       scripts/ecdsa_alias_multiplicity.py --selftest
(minutes on many cores; pure standard library; uses scripts/ecdsa_bb_model.py and
scripts/ecdsa_alias_ecp.py)

For every site and parameter tuple sigma, W(site, sigma) = { final points R for which the site is alias-bad }.
The script enumerates every (R, site, sigma), finds every R that occurs for two different (site, sigma),
and reports the maximum number of (site, sigma) that are bad for one R.

Sites (u2-side contributions assumed to vanish), EG = -lam G:
  skew1  sigma = (Kh)                 A = R - Kh EG                          bad: x(EG) - x(A) in Dset
  skew0  sigma = (Kl, Kh)             A = R - Kl G - Kh EG                   bad: x(G) - x(A) in Dset
  frag2  sigma = (Fl, Kl, Kh)         A = R - (Fl+Kl) G - Kh EG              bad: x(Fl G) - x(A) in Dset
  frag0  sigma = (Fl, Kl, Fh, Kh)     A = R - (Fl+Kl) G - (Fh+Kh) EG         bad: x(Fh EG) - x(A) in Dset
  lad    sigma = (d, Fl, Kl, Fh, Kh)  A = (R - (4d+Fl+Kl) G - (Fh+Kh) EG)/8  bad: x(A) - x(d G) in Dset   (check 1)
                                                                              or x(A) - x(A + d G) in Dset (check 2)
Ranges: Kh in {-1,0,1}, Kl in {-1,0}, Fl odd |Fl|<=3, Fh odd |Fh|<=7, d odd |d|<=255.

The ladder site depends on (Fh, Kh) only through Fh+Kh, so tuples with equal Fh+Kh have the identical set W;
they are stored once ("effective tuple") with a weight = number of (Fh, Kh) pairs with that sum, and the
report gives both raw (weighted) and effective counts.
"""
import os, sys, time, random, argparse, multiprocessing as mp

ap = argparse.ArgumentParser()
ap.add_argument('--kmax', type=int, default=6)
ap.add_argument('--workers', type=int, default=os.cpu_count() or 4)
ap.add_argument('--out', default=None)
ap.add_argument('--selftest', action='store_true')
args = ap.parse_args()
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from array import array
import ecdsa_bb_model as _M  # noqa: E402

P, n, NAT, G, ML, BETA, endo = _M.K1.p, _M.K1.n, _M.NAT, _M.K1.G, _M.ML, _M.BETA, _M.endo
add = _M.K1.add


def neg(A):
    return _M.neg(_M.K1, A)


def mul(k, A):
    return _M.K1.mul(k, A)


def on_curve(A):
    return A is None or _M.K1.on(A)
from ecdsa_alias_ecp import lift, solve_x_minus_xsum  # noqa: E402

EG = endo(G)
assert EG == mul(ML, G)
INV8 = pow(8, -1, n)
KH, KL = (-1, 0, 1), (-1, 0)
FL = (-3, -1, 1, 3)
FH = (-7, -5, -3, -1, 1, 3, 5, 7)
DS = [d for d in range(-255, 256) if d % 2]
SITES = ['skew1', 'skew0', 'frag2', 'frag0', 'lad']

# ---- sigma tables --------------------------------------------------------------------------------
# small sites: one record per sigma. ladder: one record per effective tuple (d, Fl, Kl, s = Fh+Kh).
SIG = []                                   # code -> (site, sigma or effective sigma, weight, raw sigmas)
for kh in KH:
    SIG.append(('skew1', (kh,), 1, [(kh,)]))
for kl in KL:
    for kh in KH:
        SIG.append(('skew0', (kl, kh), 1, [(kl, kh)]))
for fl in FL:
    for kl in KL:
        for kh in KH:
            SIG.append(('frag2', (fl, kl, kh), 1, [(fl, kl, kh)]))
for fl in FL:
    for kl in KL:
        for fh in FH:
            for kh in KH:
                SIG.append(('frag0', (fl, kl, fh, kh), 1, [(fl, kl, fh, kh)]))
N_SMALL = len(SIG)
HSUMS = sorted({fh + kh for fh in FH for kh in KH})
LAD_BASE = {}
for d in DS:
    LAD_BASE[d] = len(SIG)
    for fl in FL:
        for kl in KL:
            for s in HSUMS:
                raw = [(d, fl, kl, fh, kh) for fh in FH for kh in KH if fh + kh == s]
                SIG.append(('lad', (d, fl, kl, s), len(raw), raw))
CODE = {(s[0], s[1]): i for i, s in enumerate(SIG)}


def make_dset(kmax):
    out = set()
    for k in range(-kmax, kmax + 1):
        j0 = (-k * P) // NAT
        for j in range(j0 - 8, j0 + 9):
            d = k * P + j * NAT
            if d != 0 and -P < d < P:
                out.add(d)
    return sorted(out)


def pts_with_x(x):
    A = lift(x)
    return [] if A is None else [A, neg(A)]


def h64(R):
    return ((R[0] & ((1 << 63) - 1)) << 1) | (R[1] & 1)


_GM = {}


def gm(k):
    if k not in _GM:
        _GM[k] = mul(k, G)
    return _GM[k]


def egm(k):
    return endo(gm(k)) if k % n else None


def shiftR(A, a, b):
    """A + a G + b EG"""
    return add(add(A, gm(a % n) if a % n else None), egm(b))


def R_of(code, A):
    site, sg, _, _ = SIG[code]
    if site == 'skew1':
        return shiftR(A, 0, sg[0])
    if site == 'skew0':
        return shiftR(A, sg[0], sg[1])
    if site == 'frag2':
        return shiftR(A, sg[0] + sg[1], sg[2])
    if site == 'frag0':
        return shiftR(A, sg[0] + sg[1], sg[2] + sg[3])
    d, fl, kl, s = sg
    return shiftR(mul(8, A), 4 * d + fl + kl, s)


def _R_job(job):
    return R_of(job[0], job[1])


def unit_small(dset):
    """records for skew1, skew0, frag2, frag0: (list of A points, hashes, codes, src)"""
    pts, H, C, S = [], [], [], []

    def emit(code, A):
        R = R_of(code, A)
        if R is None:
            return
        pts.append(A)
        H.append(h64(R)); C.append(code); S.append(len(pts) - 1)

    for delta in dset:
        for A in pts_with_x(EG[0] - delta):
            for kh in KH:
                emit(CODE[('skew1', (kh,))], A)
        for A in pts_with_x(G[0] - delta):
            for kl in KL:
                for kh in KH:
                    emit(CODE[('skew0', (kl, kh))], A)
        for fl in FL:
            for A in pts_with_x(gm(abs(fl))[0] - delta):
                for kl in KL:
                    for kh in KH:
                        emit(CODE[('frag2', (fl, kl, kh))], A)
        for fh in FH:
            for A in pts_with_x(egm(abs(fh))[0] - delta):
                for fl in FL:
                    for kl in KL:
                        for kh in KH:
                            emit(CODE[('frag0', (fl, kl, fh, kh))], A)
    return pts, H, C, S


def unit_lad(job):
    d, dset = job
    dsetS = set(dset)
    T = gm(d % n)
    As = {}
    # check 1: x(A) - x(dG) = delta
    c1 = c2 = 0
    for delta in dset:
        for A in pts_with_x(T[0] + delta):
            As[A] = As.get(A, 0) | 1
            c1 += 1
    # check 2: x(S) - x(S + dG) = delta ; solve per residue mod p, keep exact integer matches
    rnd = random.Random(d)
    for c in sorted({delta % P for delta in dset}):
        for S in solve_x_minus_xsum(T, c, rnd):
            S2 = add(S, T)
            if (S[0] - S2[0]) in dsetS:
                As[S] = As.get(S, 0) | 2
                c2 += 1
    pts = list(As)
    H, C, S_ = [], [], []
    base = LAD_BASE[d]
    ninf = 0
    for idx, A in enumerate(pts):
        B = add(mul(8, A), gm(4 * d % n))
        code = base
        for fl in FL:
            for kl in KL:
                Bl = add(B, gm((fl + kl) % n) if (fl + kl) % n else None)
                for s in HSUMS:
                    R = add(Bl, egm(s))
                    if R is None:
                        ninf += 1
                    else:
                        H.append(h64(R)); C.append(code); S_.append(idx)
                    code += 1
    return (d, pts, [As[A] for A in pts], array('Q', H).tobytes(), array('I', C).tobytes(), array('I', S_).tobytes(),
            c1, c2, sum(1 for v in As.values() if v == 3), ninf)


def run(dset, workers, log=print):
    t0 = time.time()
    pts, H, C, S = unit_small(dset)
    allpts = list(pts)
    allflags = [0] * len(pts)
    H = array('Q', H); C = array('I', C); S = array('I', S)
    stats = dict(c1=0, c2=0, both=0, inf=0)
    with mp.Pool(workers) as pool:
        for (d, pts, flags, hb, cb, sb, c1, c2, both, ninf) in pool.imap_unordered(unit_lad, [(d, dset) for d in DS], chunksize=1):
            off = len(allpts)
            allpts.extend(pts)
            allflags.extend(flags)
            H.frombytes(hb)
            C.frombytes(cb)
            s_loc = array('I'); s_loc.frombytes(sb)
            S.extend(array('I', [v + off for v in s_loc]))
            stats['c1'] += c1; stats['c2'] += c2; stats['both'] += both; stats['inf'] += ninf
    log(f'enumerated {len(H)} records from {len(allpts)} accumulator points in {time.time() - t0:.0f}s')
    # ---- per-site totals
    totals = {nm: [0, 0] for nm in SITES}
    cnt_by_code = {}
    for c in C:
        cnt_by_code[c] = cnt_by_code.get(c, 0) + 1
    for c, cnt in cnt_by_code.items():
        totals[SIG[c][0]][0] += cnt
        totals[SIG[c][0]][1] += cnt * SIG[c][2]
    # ---- coincidences: equal 64-bit hash, then exact confirmation
    Hs = sorted(H)
    dup = set()
    prev = None
    for v in Hs:
        if v == prev:
            dup.add(v)
        prev = v
    del Hs
    byhash = {}
    if dup:
        for i, v in enumerate(H):
            if v in dup:
                byhash.setdefault(v, []).append(i)
    groups = []                       # (R, record indices with exactly that R)
    hash_only = 0
    recs = [r for idxs in byhash.values() for r in idxs]
    with mp.Pool(workers) as pool:
        Rs = pool.map(_R_job, [(C[r], allpts[S[r]]) for r in recs], chunksize=2000)
    Rof = dict(zip(recs, Rs))
    del Rs
    for v, idxs in byhash.items():
        exact = {}
        for r in idxs:
            exact.setdefault(Rof[r], []).append(r)
        if all(len(rs) == 1 for rs in exact.values()):
            hash_only += 1
        for R, rs in exact.items():
            if len(rs) > 1:
                groups.append((R, rs))
    log(f'{len(recs)} records share a 64-bit hash with another; {len(groups)} exact groups; {time.time() - t0:.0f}s')
    coinc = []
    for R, rs in groups:
        members = []
        for r in rs:
            code = int(C[r])
            site, sg, w, raw = SIG[code]
            A = allpts[S[r]]
            # the "events": which arithmetic facts fail (a set per record).
            #   small sites: (accumulator point, x of the added point)
            #   ladder check 1: (accumulator point A, x(d G))
            #   ladder check 2: the unordered pair {A, A + d G} (digit d at A and digit -d at A + d G are the same
            #                   two x-coordinates compared, and give the same R)
            if site == 'skew1':
                ev = {(A, EG[0])}
            elif site == 'skew0':
                ev = {(A, G[0])}
            elif site == 'frag2':
                ev = {(A, gm(abs(sg[0]))[0])}
            elif site == 'frag0':
                ev = {(A, egm(abs(sg[2]))[0])}
            else:
                ev = set()
                fl_ = allflags[S[r]]
                if fl_ & 1:
                    ev.add(('c1', A, gm(abs(sg[0]))[0]))
                if fl_ & 2:
                    ev.add(('c2', frozenset((A, add(A, gm(sg[0] % n))))))
            members.append(dict(site=site, eff=sg, weight=w, raw=raw, A=A, ev=ev))
        codes = {(m['site'], m['eff']) for m in members}
        if len(codes) < 2:
            continue                  # the same (site, sigma) reached twice (cannot happen: R -> A is injective)
        evs = set().union(*[m['ev'] for m in members])
        nev = len(evs)
        mirror = (nev == 1 and all(m['site'] == 'lad' for m in members) and len(members) == 2
                  and members[0]['eff'][0] == -members[1]['eff'][0] and members[0]['eff'][1:] == members[1]['eff'][1:])
        coinc.append(dict(R=R, members=members, structural=(nev == 1), mirror=mirror, nev=nev,
                          mult=sum(m['weight'] for m in members)))
    max_eff_lad_weight = max(s[2] for s in SIG)
    return dict(totals=totals, stats=stats, coinc=coinc, hash_only=hash_only, nrec=len(H), npts=len(allpts),
                max_weight=max_eff_lad_weight, secs=time.time() - t0)


def fmt_member(m):
    return f"{m['site']}{m['raw'] if len(m['raw']) > 1 else m['raw'][0]}"


def selftest(workers):
    rnd = random.Random(42)
    def rpt():
        while True:
            A = lift(rnd.randrange(P))
            if A:
                return A
    # plant 1: R1 bad for (skew1, Kh=0) and (skew0, Kl=0, Kh=0)
    R1 = rpt()
    da, db = EG[0] - R1[0], G[0] - R1[0]
    # plant 2: R2 bad for (lad check 2, d=77, Fl=1, Kl=0, Fh=3, Kh=0) and (frag0, Fl=-1, Kl=-1, Fh=5, Kh=1)
    A = rpt()
    R2 = shiftR(mul(8, A), 4 * 77 + 1, 3)
    dc = A[0] - add(A, gm(77))[0]
    A2 = shiftR(R2, 2, -6)
    dd = egm(5)[0] - A2[0]
    # plant 3: R3 bad for (lad check 1, d=-9, Fl=-3, Kl=-1, Fh=-7, Kh=-1) and (frag2, Fl=3, Kl=0, Kh=1)
    A3 = rpt()
    R3 = shiftR(mul(8, A3), 4 * -9 - 4, -8)
    de = A3[0] - gm(9)[0]
    A4 = shiftR(R3, -3, -1)
    df = gm(3)[0] - A4[0]
    toy = sorted({da, db, dc, dd, de, df})
    res = run(toy, workers, log=lambda *a: None)
    found = {c['R']: {(m['site'], m['eff']) for m in c['members']} for c in res['coinc']}
    exp = {R1: {('skew1', (0,)), ('skew0', (0, 0))},
           R2: {('lad', (77, 1, 0, 3)), ('frag0', (-1, -1, 5, 1))},
           R3: {('lad', (-9, -3, -1, -8)), ('frag2', (3, 0, 1))}}
    ok = all(R in found and exp[R] <= found[R] for R in exp)
    nonstruct = [c for c in res['coinc'] if not c['structural']]
    lines = [f'self-test (toy Dset of {len(toy)} planted differences): '
             f'{"PASS" if ok else "FAIL"} - all 3 planted coincidences found; {len(nonstruct)} two-event coincidences reported in '
             f'total (a planted coincidence drags a family with it: the same two accumulator points under the other '
             f'digit shifts, and the negated points); {res["nrec"]} records']
    for R in exp:
        lines.append(f'  planted R x={hex(R[0])[:18]}..: expected {sorted(exp[R])} found {sorted(found.get(R, []))}')
    assert ok, lines
    return lines


if __name__ == '__main__':
    t0 = time.time()
    st = selftest(args.workers)
    print('\n'.join(st), flush=True)
    if args.selftest:
        sys.exit(0)
    dset = make_dset(args.kmax)
    print(f'|Dset| = {len(dset)} integers (k in [-{args.kmax}, {args.kmax}]), {len({d % P for d in dset})} residues mod p', flush=True)
    res = run(dset, args.workers)
    struct = [c for c in res['coinc'] if c['structural']]
    nons = [c for c in res['coinc'] if not c['structural']]
    maxmult = max([res['max_weight']] + [c['mult'] for c in res['coinc']])
    maxmult_eff = max([1] + [c['nev'] for c in res['coinc']])
    out = []
    out.append('# Multiplicity of the aliasing small sites (C6)\n')
    out.append(f'Command: `scripts/ecdsa_alias_multiplicity.py --kmax {args.kmax}`; wall time {time.time() - t0:.0f} s '
               f'({args.workers} workers).\n')
    out.append(f'Dset = {{k p + j N : |k| <= {args.kmax}, nonzero, in (-p, p)}}: {len(dset)} integers, '
               f'{len({d % P for d in dset})} residues mod p.\n')
    out.append('## Self-test\n')
    out += ['    ' + l for l in st]
    out.append('\n## (i) Sizes\n')
    out.append('| site | #sigma (raw) | (R, sigma) triples, raw | stored records (effective sigma) |')
    out.append('|---|---|---|---|')
    nsig = dict(skew1=3, skew0=6, frag2=24, frag0=192, lad=256 * 192)
    for nm in SITES:
        out.append(f'| {nm} | {nsig[nm]} | {res["totals"][nm][1]} | {res["totals"][nm][0]} |')
    out.append(f'| total | {sum(nsig.values())} | {sum(v[1] for v in res["totals"].values())} | {res["nrec"]} |')
    out.append(f'\nLadder (15,3): {res["stats"]["c1"]} accumulator points from check 1, {res["stats"]["c2"]} from check 2, '
               f'{res["stats"]["both"]} in both (counted once); {res["stats"]["inf"]} tuples skipped because R would be the '
               f'point at infinity. Distinct accumulator points over all sites: {res["npts"]}.\n')
    out.append('## (ii) Coincidences (one R, two different (site, sigma))\n')
    out.append(f'- 64-bit hash collisions that were not exact point collisions: {res["hash_only"]}')
    out.append('- Built-in identities of the ladder site (not stored as separate records): tuples (d, Fl, Kl, Fh, Kh) and '
               '(d, Fl, Kl, Fh\', Kh\') with Fh + Kh = Fh\' + Kh\' have the same accumulator A and the same checks, so '
               'W is the identical set. For each even s = Fh + Kh in [-6, 6] there are exactly 2 such pairs '
               '((s-1, +1) and (s+1, -1)); odd s and s = +-8 have 1.')
    mir = [c for c in struct if c['mirror']]
    oth = [c for c in struct if not c['mirror']]
    out.append(f'- Ladder mirror identity, found by the search: {len(mir)} points R are bad for both (d, Fl, Kl, s) and '
               f'(-d, Fl, Kl, s). Every one is check 2: x(A) - x(A + d G) in Dset holds for accumulator A with digit d iff it '
               f'holds for accumulator A + d G with digit -d (same two x-coordinates, Dset is symmetric), and both give the '
               f'same R = 8A + 4d G + ... . This pairs up all {res["stats"]["c2"]} check-2 accumulator points '
               f'({res["stats"]["c2"]} / 2 x {len(FL) * len(KL) * len(HSUMS)} effective tuples = '
               f'{res["stats"]["c2"] // 2 * len(FL) * len(KL) * len(HSUMS)}).')
    out.append(f'- Small-site identities, found by the search (same accumulator point A and same x-coordinate of the added '
               f'point, reached under several digit tuples): {len(oth)} points R, by pattern:')
    kinds = {}
    for c in oth:
        key = tuple(sorted(f"{m['site']}{m['eff']}" for m in c['members']))
        kinds[key] = kinds.get(key, 0) + 1
    for key, cnt in sorted(kinds.items()):
        out.append(f'    - {" = ".join(key)}: {cnt} points R')
    out.append(f'- **Coincidences that are not one of these identities (two different events for one R): {len(nons)}**')
    for c in nons[:200]:
        out.append(f'    - R = ({hex(c["R"][0])}, {hex(c["R"][1])}): ' + ' ; '.join(fmt_member(m) for m in c['members']))
    if len(nons) > 200:
        out.append(f'    - ... {len(nons) - 200} more in the _coincidences.tsv file')
    out.append('\n## (iii) Maximum multiplicity\n')
    out.append(f'- max over R of the number of raw (site, sigma) pairs that are bad: **{maxmult}**')
    out.append(f'- max over R of the number of distinct events (one event = one failing comparison: same accumulator '
               f'point and same added x-coordinate for the small sites and check 1; the unordered pair {{A, A + d G}} '
               f'for check 2): **{max(maxmult_eff, 1)}**')
    byk = {}
    for c in res['coinc']:
        byk[c['mult']] = byk.get(c['mult'], 0) + 1
    out.append(f'- points R by raw multiplicity among those found by the hash search: {dict(sorted(byk.items()))} '
               f'(all other R have multiplicity 1, or 2 for a ladder tuple with even Fh+Kh in [-6, 6])')
    text = '\n'.join(out) + '\n'
    print(text)
    if args.out:
        open(args.out, 'w').write(text)
        with open(os.path.splitext(args.out)[0] + '_coincidences.tsv', 'w') as f:
            f.write('structural\tmult\tRx\tRy\tmembers   (only coincidences that are not built-in identities)\n')
            for c in nons:
                f.write(f"{int(c['structural'])}\t{c['mult']}\t{hex(c['R'][0])}\t{hex(c['R'][1])}\t"
                        + ' ; '.join(fmt_member(m) for m in c['members']) + '\n')
