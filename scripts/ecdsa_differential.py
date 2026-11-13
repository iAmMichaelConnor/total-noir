#!/usr/bin/env python3
"""Differential test of the ECDSA totality argument against bb.

For many inputs (random, and crafted to hit each failure class of bb's
ECDSA gadgets) this compares three things:

  model   scripts/ecdsa_bb_model.py: does bb's own witness violate an
          assertion of the raw black-box call?
  emu     the library's Noir emulation (the hint's predicate, through
          total::ecdsa::ecdsa_{k1,r1}_raw_unprovable), by nargo execute
  bb      nargo execute + bb prove + bb verify on the raw black-box call
          (std::ecdsa_secp256{k1,r1}::verify_signature)

and checks, in both directions, model == (bb fails) and emu == model (for
secp256r1, emu == model restricted to the parts the hint follows). It then
runs every input through the shipped entries (total::ecdsa::ecdsa_k1_verify
and ecdsa_r1_verify): each must prove and verify with the documented
verdict.

Needs nargo and bb on PATH (BB overrides the bb binary). Work files go
under --work (default: $TMPDIR, else target/ in the checkout), in a fresh
directory that is removed at the end unless --keep. Exit status 1 on any mismatch.

Usage: scripts/ecdsa_differential.py [--random N] [--crafted N] [--jobs J]
           [--seed S] [--work DIR] [--keep] [--extra DIR ...] [--out FILE]
  --extra DIR   also run every *.toml in DIR (raw-call inputs with pk_x,
                pk_y, sig, hash) as secp256k1 cases
"""
import argparse
import concurrent.futures as cf
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ecdsa_bb_model as M  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BB = os.environ.get("BB", "bb")
PROVED_FOR_BB = "6.0.0"
K1, R1 = M.K1, M.R1

PKGS = {
    "raw_k1": "fn main(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> pub bool {\n"
              "    std::ecdsa_secp256k1::verify_signature(pk_x, pk_y, sig, hash)\n}\n",
    "raw_r1": "fn main(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> pub bool {\n"
              "    std::ecdsa_secp256r1::verify_signature(pk_x, pk_y, sig, hash)\n}\n",
    "lib_k1": "fn main(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> pub bool {\n"
              "    total::ecdsa::ecdsa_k1_verify(pk_x, pk_y, sig, hash)\n}\n",
    "lib_r1": "fn main(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> pub bool {\n"
              "    total::ecdsa::ecdsa_r1_verify(pk_x, pk_y, sig, hash)\n}\n",
    "emu_k1": "fn main(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> pub bool {\n"
              "    // Safety: diagnostic output only\n"
              "    unsafe { total::ecdsa::ecdsa_k1_raw_unprovable(pk_x, pk_y, sig, hash) }\n}\n",
    "emu_r1": "fn main(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> pub bool {\n"
              "    // Safety: diagnostic output only\n"
              "    unsafe { total::ecdsa::ecdsa_r1_raw_unprovable(pk_x, pk_y, sig, hash) }\n}\n",
}


def bts(v):
    return "[" + ",".join(str(b) for b in v.to_bytes(32, "big")) + "]"


def toml(c):
    return (f"pk_x = {bts(c['Q'][0])}\npk_y = {bts(c['Q'][1])}\n"
            f"sig = {bts(c['r'])[:-1]},{bts(c['s'])[1:]}\nhash = {bts(c['z'])}\n")


def sh(cmd, cwd=None):
    return subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)


# ---- case generation ------------------------------------------------------
def scalars_to_sig(C, u1, u2, rnd):
    """(r, s, z) with z/s = u1 and r/s = u2 mod n, s low, r in the gate when possible."""
    for _ in range(200):
        s = rnd.randrange(1, (C.n + 1) // 2)
        r = u2 * s % C.n
        if r >= C.p - C.n and not (C is R1 and (r == s or r + s == C.n)):
            return r, s, u1 * s % C.n
    return None


def case(C, cat, Q, u1, u2, rnd):
    sig = scalars_to_sig(C, u1, u2, rnd)
    if sig is None or Q is None:
        return None
    return dict(curve="k1" if C is K1 else "r1", cat=cat, Q=Q, r=sig[0], s=sig[1], z=sig[2], raw=True)


def gen_k1(rnd, n_random, n_crafted):
    C, n = K1, K1.n
    out = []
    for i in range(n_random):
        d, k, z = rnd.randrange(1, n), rnd.randrange(1, n), rnd.randrange(2**256)
        Q = C.mul(d, C.G)
        r = C.mul(k, C.G)[0] % n
        s = pow(k, -1, n) * (z + r * d) % n
        s = min(s, n - s)
        if i % 3 == 1:
            z ^= 1
        if i % 3 == 2:
            s = rnd.randrange(1, n)
        if r >= C.p - n and s:
            out.append(dict(curve="k1", cat="random", Q=Q, r=r, s=s, z=z, raw=True))
    for i in range(n_crafted):
        u1, u2 = rnd.randrange(1, n), rnd.randrange(1, n)
        tr = M.k1_scalar_trace(1, u1, u2)
        # exact collision at a random ladder step
        (_, _, a, b, pa, pb) = rnd.choice(tr)
        kind = rnd.choice(("eq", "neg", "ret"))
        co, rhs = {"eq": (a - pa, pb - b), "neg": (a + pa, -(b + pb)), "ret": (2 * a + pa, -(2 * b + pb))}[kind]
        if co % n:
            q = rhs * pow(co, -1, n) % n
            if q:
                out.append(case(C, "exact-" + kind, C.mul(q, C.G), u1, u2, rnd))
        # aliasing in check 1 of a ladder step that adds a multiple of G
        (ri, sj, a, b, pa, pb) = rnd.choice([t for t in tr if t[1] in (2, 3)])
        Pt = C.mul(pb, C.G)
        A = M.lift(C, Pt[0] + rnd.choice(sorted(M.AL_K1.inc)), rnd.randrange(2))
        if A is not None and a:
            Q = C.mul(pow(a, -1, n), C.add(A, M.neg(C, C.mul(b, C.G))))
            out.append(case(C, "alias-ladder", Q, u1, u2, rnd))
            # control: one off the aliasing value
            A = M.lift(C, A[0] + 1) or M.lift(C, A[0] + 2)
            if A is not None:
                Q = C.mul(pow(a, -1, n), C.add(A, M.neg(C, C.mul(b, C.G))))
                out.append(case(C, "alias-ladder-control", Q, u1, u2, rnd))
        # final point R chosen so that a closing addition aliases for suitable low digits
        base = rnd.choice((C.G, M.endo(C.G), C.mul(3, C.G), M.endo(C.mul(3, C.G)), M.endo(C.mul(5, C.G))))
        R = M.lift(C, base[0] - rnd.choice(WIDE[C]), rnd.randrange(2))
        if R is not None:
            sh_ = rnd.choice((0, 0, 1, -1)) + ML_SHIFT[rnd.randrange(3)]
            R = C.add(R, C.mul(sh_, C.G))
            out.append(case(C, "alias-closing", C.mul(pow(u2, -1, n), C.add(R, M.neg(C, C.mul(u1, C.G)))), u1, u2, rnd))
        # R = rho G for a short rho: the dense exact class
        rho = rnd.choice((0, 0, 1, -1, 2, 3, -3, 5)) + ML_SHIFT[rnd.randrange(3)] * rnd.choice((1, 3))
        q = (rho - u1) * pow(u2, -1, n) % n
        if q:
            out.append(case(C, "short-R", C.mul(q, C.G), u1, u2, rnd))
    return [c for c in out if c]


ML_SHIFT = (0, M.ML, -M.ML)
# divisor differences k p + j N for k in -3..3: inside and outside every site's range of k, so that
# both outcomes occur (the model decides which)
WIDE = {C: M.T.alias_values(C.p, range(-3, 4), -C.p + 1, C.p) for C in (K1, R1)}


def gen_r1(rnd, n_random, n_crafted):
    C, n = R1, R1.n
    out = []
    for i in range(n_random):
        d, k, z = rnd.randrange(1, n), rnd.randrange(1, n), rnd.randrange(2**256)
        Q = C.mul(d, C.G)
        r = C.mul(k, C.G)[0] % n
        s = pow(k, -1, n) * (z + r * d) % n
        s = min(s, n - s)
        if i % 3 == 1:
            z ^= 1
        if i % 3 == 2:
            s = rnd.randrange(1, n)
        if r >= C.p - n and s and r != s and r + s != n:
            out.append(dict(curve="r1", cat="random", Q=Q, r=r, s=s, z=z, raw=True))
    for i in range(n_crafted):
        u1, u2 = rnd.randrange(1, n), rnd.randrange(2, n - 1)
        # exact collision in a round of the two-point multiplication: Q a multiple of its offset generator
        alpha, beta_abs, beta_neg = M.r1_fake_glv(u2)
        t = (u2 if beta_neg else -u2) % n
        na, nb = M.r1_naf(alpha), M.r1_naf(beta_abs)
        sg = lambda e: -1 if e else 1  # noqa: E731
        rr = rnd.randrange(1, 128)
        ca = cb = 1
        for r_ in range(1, rr):
            ca, cb = 2 * ca + sg(na[r_]), 2 * cb + sg(nb[r_])
        c_, d_ = ca + cb * t, sg(na[rr]) + sg(nb[rr]) * t
        kind = rnd.choice(("eq", "neg", "ret"))
        co, hh = {"eq": (c_ - d_, 1 << (rr - 1)), "neg": (c_ + d_, 1 << (rr - 1)), "ret": (2 * c_ + d_, 1 << rr)}[kind]
        if co % n:
            Q = C.mul(-hh * pow(co, -1, n), M.H_OFF)
            out.append(case(C, "exact-msm-" + kind, Q, u1, u2, rnd))
        # aliasing in the final addition T1 + T2
        T1 = C.mul(u1, C.G)
        T2 = M.lift(C, T1[0] + rnd.choice(WIDE[C]), rnd.randrange(2))
        if T2 is not None:
            out.append(case(C, "alias-final", C.mul(pow(u2, -1, n), T2), u1, u2, rnd))
            T2 = M.lift(C, T2[0] + 1) or M.lift(C, T2[0] + 2)
            if T2 is not None:
                out.append(case(C, "alias-final-control", C.mul(pow(u2, -1, n), T2), u1, u2, rnd))
    return [c for c in out if c]


def gen_edges(rnd):
    """Inputs for the shipped entries only (the raw call's solver and bb may disagree on them)."""
    out = []
    for C, name in ((K1, "k1"), (R1, "r1")):
        n = C.n
        d, k, z = rnd.randrange(1, n), rnd.randrange(1, n), rnd.randrange(n)
        Q = C.mul(d, C.G)
        r = C.mul(k, C.G)[0] % n
        s = pow(k, -1, n) * (z + r * d) % n
        s = min(s, n - s)
        for cat, (r_, s_, z_) in (("valid", (r, s, z)), ("r=n", (n, s, z)), ("r=n+1", (n + 1, s, z)),
                                  ("r=2^256-1", (2**256 - 1, s, z)), ("r=0", (0, s, z)), ("s=0", (r, 0, z)),
                                  ("s=n", (r, n, z)), ("high-s", (r, n - s, z)), ("z+n", (r, s, z + n)),
                                  ("r=n,z=0", (n, 1, 0)), ("r=n,s=1", (n, 1, z)), ("r=p-n-1", (C.p - n - 1, s, z))):
            if z_ < 2**256:
                out.append(dict(curve=name, cat="edge-" + cat, Q=Q, r=r_, s=s_, z=z_, raw=False))
    return out


def load_extra(d):
    out = []
    for f in sorted(os.listdir(d)):
        if not f.endswith(".toml"):
            continue
        v = {}
        for line in open(os.path.join(d, f)):
            m = re.match(r"(\w+)\s*=\s*\[(.*)\]", line)
            if m:
                v[m.group(1)] = bytes(int(x) for x in m.group(2).split(","))
        Q = (int.from_bytes(v["pk_x"], "big"), int.from_bytes(v["pk_y"], "big"))
        out.append(dict(curve="k1", cat="extra:" + os.path.basename(d.rstrip("/")), Q=Q,
                        r=int.from_bytes(v["sig"][:32], "big"), s=int.from_bytes(v["sig"][32:], "big"),
                        z=int.from_bytes(v["hash"], "big"), raw=True, name=f))
    return out


# ---- running ----------------------------------------------------------------
def execute(work, pkg, cid):
    d = os.path.join(work, pkg)
    r = sh(["nargo", "execute", "--silence-warnings", "-p", os.path.join(work, "cases", cid), f"{pkg}_{cid}"], cwd=d)
    m = re.search(r"Circuit output: (\w+)", r.stdout)
    wit = os.path.join(d, "target", f"{pkg}_{cid}.gz")
    return (m.group(1) == "true") if m else None, wit if os.path.exists(wit) else None


def prove(work, pkg, cid, wit):
    d = os.path.join(work, pkg)
    out = os.path.join(work, "proofs", f"{pkg}_{cid}")
    os.makedirs(out, exist_ok=True)
    r = sh([BB, "prove", "-b", os.path.join(d, "target", pkg + ".json"), "-w", wit, "-k", os.path.join(d, "vk", "vk"), "-o", out])
    ok = r.returncode == 0 and os.path.exists(os.path.join(out, "proof"))
    if ok:
        v = sh([BB, "verify", "-k", os.path.join(d, "vk", "vk"), "-p", os.path.join(out, "proof"),
                "-i", os.path.join(out, "public_inputs")])
        ok = v.returncode == 0
    shutil.rmtree(out, ignore_errors=True)
    os.remove(wit)
    return ok


def run_case(args):
    work, c = args
    cid, cv = c["id"], c["curve"]
    C = K1 if cv == "k1" else R1
    res = dict(id=cid, curve=cv, cat=c["cat"])
    u1 = u2 = None
    if c["raw"]:
        s_eff = c["s"] % C.n or 1
        w = pow(s_eff, -1, C.n)
        u1, u2 = c["z"] * w % C.n, c["r"] * w % C.n
        if cv == "k1":
            sites = M.k1_sites(c["Q"], u1, u2)
            hint_sites = sites
        else:
            sites = M.r1_sites(c["Q"], u1, u2)
            hint_sites = [x for x in sites if not x[0].startswith("msm")]
        res["model_bad"] = bool(sites)
        res["model_hint_bad"] = bool(hint_sites)
        res["sites"] = ";".join(f"{a}:{b}" for a, b in sites[:3])
        _, wit = execute(work, "raw_" + cv, cid)
        res["raw_proved"] = prove(work, "raw_" + cv, cid, wit) if wit else None
        emu, wit = execute(work, "emu_" + cv, cid)
        res["emu_bad"] = emu
        if wit:
            os.remove(wit)
    outv, wit = execute(work, "lib_" + cv, cid)
    res["lib_out"] = outv
    res["lib_proved"] = prove(work, "lib_" + cv, cid, wit) if wit else None
    res["expected"] = M.verdict(C, c["Q"], c["r"], c["s"], c["z"])
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--random", type=int, default=200)
    ap.add_argument("--crafted", type=int, default=100)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--work")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--extra", action="append", default=[])
    ap.add_argument("--out")
    a = ap.parse_args()
    have = sh([BB, "--version"]).stdout.strip().splitlines()[:1]
    if have != [PROVED_FOR_BB]:
        print(f"bb is {have}; the model and docs/ecdsa-totality.md are for bb {PROVED_FOR_BB}")
        return 2
    base = a.work or os.environ.get("TMPDIR") or os.path.join(ROOT, "target")
    os.makedirs(base, exist_ok=True)
    work = tempfile.mkdtemp(prefix="ecdsa-diff-", dir=base)
    os.environ["TMPDIR"] = work
    try:
        rnd = random.Random(a.seed)
        cases = gen_k1(rnd, a.random, a.crafted) + gen_r1(rnd, a.random, a.crafted) + gen_edges(rnd)
        for d in a.extra:
            cases += load_extra(d)
        os.makedirs(os.path.join(work, "cases"))
        for i, c in enumerate(cases):
            c["id"] = f"c{i:05d}"
            open(os.path.join(work, "cases", c["id"] + ".toml"), "w").write(toml(c))
        for pkg, src in PKGS.items():
            d = os.path.join(work, pkg)
            os.makedirs(os.path.join(d, "src"))
            dep = "" if pkg.startswith("raw") else f'total = {{ path = "{ROOT}/noir/total" }}\n'
            open(os.path.join(d, "Nargo.toml"), "w").write(
                f'[package]\nname = "{pkg}"\ntype = "bin"\ncompiler_version = ">=1.0.0"\n\n[dependencies]\n{dep}')
            open(os.path.join(d, "src", "main.nr"), "w").write(src)
        def build(pkg):
            d = os.path.join(work, pkg)
            r = sh(["nargo", "compile", "--silence-warnings"], cwd=d)
            if r.returncode:
                return pkg + ": " + r.stdout[-2000:]
            if not pkg.startswith("emu"):
                r = sh([BB, "write_vk", "-b", os.path.join(d, "target", pkg + ".json"), "-o", os.path.join(d, "vk")])
                if r.returncode:
                    return pkg + ": " + r.stdout[-2000:]
            return None
        with cf.ThreadPoolExecutor(len(PKGS)) as ex:
            errs = [e for e in ex.map(build, PKGS) if e]
        if errs:
            print("\n".join(errs))
            return 2
        print(f"{len(cases)} cases, {a.jobs} jobs", flush=True)
        with cf.ProcessPoolExecutor(a.jobs) as ex:
            results = list(ex.map(run_case, [(work, c) for c in cases], chunksize=1))
    finally:
        if not a.keep:
            shutil.rmtree(work, ignore_errors=True)
    # ---- summary
    bad = []
    tab = {}
    for r in results:
        key = (r["curve"], r["cat"])
        t = tab.setdefault(key, dict(n=0, model_bad=0, raw_fail=0, emu_bad=0, lib_ok=0))
        t["n"] += 1
        if "model_bad" in r:
            t["model_bad"] += r["model_bad"]
            t["raw_fail"] += r["raw_proved"] is False
            t["emu_bad"] += bool(r["emu_bad"])
            if r["raw_proved"] is None or r["model_bad"] != (not r["raw_proved"]):
                bad.append(("model-vs-bb", r))
            if r["emu_bad"] is None or r["emu_bad"] != r["model_hint_bad"]:
                bad.append(("emu-vs-model", r))
        if r["lib_proved"] and r["lib_out"] == r["expected"]:
            t["lib_ok"] += 1
        else:
            bad.append(("shipped-entry", r))
    lines = ["curve category                 cases model-bad raw-bb-fail emu-bad shipped-ok"]
    for (cv, cat), t in sorted(tab.items()):
        lines.append(f"{cv:5} {cat:24} {t['n']:5} {t['model_bad']:9} {t['raw_fail']:11} {t['emu_bad']:7} {t['lib_ok']:10}")
    raw = [r for r in results if "model_bad" in r]
    lines.append(f"raw calls: {len(raw)}; model bad and bb fails: {sum(r['model_bad'] and r['raw_proved'] is False for r in raw)}; "
                 f"model good and bb proves: {sum((not r['model_bad']) and r['raw_proved'] is True for r in raw)}; "
                 f"mismatches: {sum(1 for k, _ in bad if k == 'model-vs-bb')}")
    lines.append(f"emulation vs model mismatches: {sum(1 for k, _ in bad if k == 'emu-vs-model')}")
    lines.append(f"shipped entries: {len(results)} runs, {len(results) - sum(1 for k, _ in bad if k == 'shipped-entry')} proved with the expected verdict")
    for k, r in bad[:40]:
        lines.append(f"MISMATCH {k}: {r}")
    text = "\n".join(lines)
    print(text)
    if a.out:
        open(a.out, "w").write(text + "\n")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
