#!/usr/bin/env node

// Reference oracle for the differential tests in noir/total_oracle_tests.
//
// nargo calls it through `resolve_foreign_call` (JSON-RPC on port 8095, or
// $PORT). Each `*_case` oracle turns the fuzzer's seed into a test case with
// the expected answer; each `*_ref` oracle computes the expected answer for
// inputs the fuzzer chose. The references share no code with the Noir
// library: BigInt arithmetic for curve membership and Grumpkin, @noble/curves
// for ECDSA, Node's crypto and @noble/hashes for SHA-256 and Keccak-256, and
// Barretenberg's native Poseidon2 (bb.js) for Poseidon2, the Merkle trees and
// the Schnorr challenge. A case depends only on the seed, so the seed nargo
// prints for a failure rebuilds it.
//
//   yarn build && yarn start           (or scripts/run.sh, which also runs the tests)

import express from "express";
import { createHash } from "node:crypto";
import { secp256k1 } from "@noble/curves/secp256k1";
import { p256 } from "@noble/curves/nist";
import { weierstrassN } from "@noble/curves/abstract/weierstrass";
import { keccak_256 } from "@noble/hashes/sha3";
import { BarretenbergSync } from "@aztec-foundation/bb.js";

// --- JSON-RPC types: each parameter and result is a hex Field or an array of them ---

type Param = string | string[];

interface ForeignCallInfo {
  function: string;
  inputs: Param[];
}

interface ForeignCallResult {
  values: Param[];
}

type Value = bigint | number | boolean | Value[];

// --- encoding ---

const TWO_128 = 1n << 128n;
const TWO_256 = 1n << 256n;
/** The circuit Field modulus (BN254 scalar field, Grumpkin base field). */
const P_FIELD = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

const hexToBig = (s: string): bigint => BigInt("0x" + (s.replace(/^0x/, "") || "0"));
const single = (p: Param): bigint => {
  if (Array.isArray(p)) throw new Error("expected a single value, got an array");
  return hexToBig(p);
};
const array = (p: Param): bigint[] => {
  if (!Array.isArray(p)) throw new Error("expected an array, got a single value");
  return p.map(hexToBig);
};
const flatten = (v: Value): bigint[] =>
  Array.isArray(v) ? v.flatMap(flatten) : [typeof v === "bigint" ? v : BigInt(Number(v))];
/** One result value: a scalar, or a (nested) array flattened to one array. */
const encode = (v: Value): Param =>
  Array.isArray(v) ? flatten(v).map((x) => x.toString(16)) : flatten(v)[0].toString(16);

const mod = (a: bigint, m: bigint): bigint => ((a % m) + m) % m;
const pow = (b: bigint, e: bigint, m: bigint): bigint => {
  let r = 1n;
  b = mod(b, m);
  while (e > 0n) {
    if (e & 1n) r = (r * b) % m;
    b = (b * b) % m;
    e >>= 1n;
  }
  return r;
};
/** Inverse mod a prime m, by the extended Euclidean algorithm. */
const inv = (a: bigint, m: bigint): bigint => {
  let [r0, r1, t0, t1] = [mod(a, m), m, 1n, 0n];
  if (r0 === 0n) throw new Error("inverse of zero");
  while (r1 !== 0n) {
    const q = r0 / r1;
    [r0, r1, t0, t1] = [r1, r0 - q * r1, t1, t0 - q * t1];
  }
  return mod(t0, m);
};
const toBytes = (x: bigint, n = 32): number[] => {
  if (x < 0n || x >= 1n << BigInt(8 * n)) throw new Error(`${x} does not fit ${n} bytes`);
  return Array.from({ length: n }, (_, i) => Number((x >> BigInt(8 * (n - 1 - i))) & 255n));
};
const fromBytes = (b: ArrayLike<number | bigint>): bigint =>
  Array.from(b).reduce<bigint>((acc, x) => (acc << 8n) | BigInt(x), 0n);

// --- deterministic choices: SHA-256 of a label, the seed and a counter ---

class Draw {
  private block = new Uint8Array();
  private used = 0;
  private counter = 0;
  private readonly key: Buffer;
  constructor(seed: bigint, label: string) {
    this.key = createHash("sha256")
      .update(label)
      .update(Buffer.from(toBytes(seed)))
      .digest();
  }
  byte(): number {
    if (this.used === this.block.length) {
      const c = Buffer.alloc(4);
      c.writeUInt32BE(this.counter++);
      this.block = createHash("sha256").update(this.key).update(c).digest();
      this.used = 0;
    }
    return this.block[this.used++];
  }
  bytes(n: number): number[] {
    return Array.from({ length: n }, () => this.byte());
  }
  /** Uniform-enough integer in [0, n) for n below 2^24. */
  below(n: number): number {
    return ((this.byte() << 16) | (this.byte() << 8) | this.byte()) % n;
  }
  /** Integer in [0, n) for any n > 0 (512 random bits reduced). */
  bigBelow(n: bigint): bigint {
    return fromBytes(this.bytes(64)) % n;
  }
  /** Integer in [lo, hi). */
  range(lo: bigint, hi: bigint): bigint {
    return lo + this.bigBelow(hi - lo);
  }
  pick<T>(xs: readonly T[]): T {
    return xs[this.below(xs.length)];
  }
}

// --- secp256k1 and secp256r1: membership by integer arithmetic ---

type Noble = typeof secp256k1;
interface Secp {
  name: string;
  p: bigint;
  n: bigint;
  a: bigint;
  b: bigint;
  noble: Noble;
}

const K1: Secp = {
  name: "secp256k1",
  p: 2n ** 256n - 2n ** 32n - 977n,
  n: 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n,
  a: 0n,
  b: 7n,
  noble: secp256k1,
};
const R1: Secp = {
  name: "secp256r1",
  p: 2n ** 256n - 2n ** 224n + 2n ** 192n + 2n ** 96n - 1n,
  n: 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551n,
  a: -3n,
  b: 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604bn,
  noble: p256 as unknown as Noble,
};
// The constants above are typed in, not read from the library; check them
// against noble's so a typo cannot hide.
for (const c of [K1, R1]) {
  const C = c.noble.ProjectivePoint.CURVE();
  if (C.p !== c.p || C.n !== c.n || mod(C.a, c.p) !== mod(c.a, c.p) || C.b !== c.b)
    throw new Error(`${c.name} constants disagree with @noble/curves`);
}
const curveOf = (id: bigint): Secp => (id === 1n ? K1 : id === 2n ? R1 : fail(`curve ${id}`));
function fail(what: string): never {
  throw new Error(`unknown ${what}`);
}

const rhs = (c: Secp, x: bigint): bigint => mod(x * x * x + c.a * x + c.b, c.p);
/** The documented flag: x < p, y < p and y^2 == x^3 + ax + b (mod p). */
const onCurve = (c: Secp, x: bigint, y: bigint): boolean =>
  x >= 0n && y >= 0n && x < c.p && y < c.p && mod(y * y - rhs(c, x), c.p) === 0n;

/** A square root mod p (both moduli are 3 mod 4), or null. */
const sqrt = (c: Secp, v: bigint): bigint | null => {
  const r = pow(v, (c.p + 1n) / 4n, c.p);
  return (r * r) % c.p === mod(v, c.p) ? r : null;
};

// Roots of x^3 + a x + k over F_p: gcd with x^p - x, then random splitting.
// Polynomials are coefficient arrays, lowest degree first.
type Poly = bigint[];
const trim = (f: Poly): Poly => {
  const g = f.slice();
  while (g.length && g[g.length - 1] === 0n) g.pop();
  return g;
};
function polyMod(f: Poly, m: Poly, p: bigint): Poly {
  let r = trim(f.map((x) => mod(x, p)));
  const lead = inv(m[m.length - 1], p);
  while (r.length >= m.length) {
    const q = (r[r.length - 1] * lead) % p,
      shift = r.length - m.length;
    for (let i = 0; i < m.length; i++) r[shift + i] = mod(r[shift + i] - q * m[i], p);
    r = trim(r);
  }
  return r;
}
function polyMulMod(f: Poly, g: Poly, m: Poly, p: bigint): Poly {
  const out: Poly = Array(Math.max(f.length + g.length - 1, 0)).fill(0n);
  f.forEach((x, i) => g.forEach((y, j) => (out[i + j] = (out[i + j] + x * y) % p)));
  return polyMod(out, m, p);
}
function polyPowMod(f: Poly, e: bigint, m: Poly, p: bigint): Poly {
  let r: Poly = [1n],
    b = polyMod(f, m, p);
  while (e > 0n) {
    if (e & 1n) r = polyMulMod(r, b, m, p);
    b = polyMulMod(b, b, m, p);
    e >>= 1n;
  }
  return r;
}
function polyGcd(f: Poly, g: Poly, p: bigint): Poly {
  let a = trim(f),
    b = trim(g);
  while (b.length) [a, b] = [b, polyMod(a, b, p)];
  const lead = inv(a[a.length - 1], p);
  return a.map((x) => (x * lead) % p);
}
const polySub = (f: Poly, g: Poly, p: bigint): Poly =>
  trim(
    Array.from({ length: Math.max(f.length, g.length) }, (_, i) =>
      mod((f[i] ?? 0n) - (g[i] ?? 0n), p),
    ),
  );
function splitRoots(g: Poly, p: bigint, draw: Draw): bigint[] {
  if (g.length <= 1) return [];
  if (g.length === 2) return [mod(-g[0] * inv(g[1], p), p)];
  for (;;) {
    const h = polySub(polyPowMod([draw.bigBelow(p), 1n], (p - 1n) / 2n, g, p), [1n], p);
    const d = polyGcd(g, h.length ? h : [0n], p);
    if (d.length > 1 && d.length < g.length) {
      const rest = polyDiv(g, d, p);
      return [...splitRoots(d, p, draw), ...splitRoots(rest, p, draw)];
    }
  }
}
function polyDiv(f: Poly, m: Poly, p: bigint): Poly {
  const r = trim(f.slice()),
    q: Poly = Array(Math.max(r.length - m.length + 1, 0)).fill(0n),
    lead = inv(m[m.length - 1], p);
  while (r.length >= m.length) {
    const c = (r[r.length - 1] * lead) % p,
      shift = r.length - m.length;
    q[shift] = c;
    for (let i = 0; i < m.length; i++) r[shift + i] = mod(r[shift + i] - c * m[i], p);
    r.pop();
  }
  return q;
}
/** The x with (x, y) on the curve. */
function xsForY(c: Secp, y: bigint, draw: Draw): bigint[] {
  const f: Poly = [mod(c.b - y * y, c.p), mod(c.a, c.p), 0n, 1n];
  const xp = polyPowMod([0n, 1n], c.p, f, c.p);
  return splitRoots(polyGcd(f, polySub(xp, [0n, 1n], c.p), c.p), c.p, draw);
}

type Affine = { x: bigint; y: bigint };
const point = (c: Secp, k: bigint): Affine => c.noble.ProjectivePoint.BASE.multiply(k).toAffine();
/** A point with x drawn from [lo, hi), or null if none is found quickly. */
function pointWithX(c: Secp, draw: Draw, lo: bigint, hi: bigint): Affine | null {
  for (let i = 0; i < 64; i++) {
    const x = draw.range(lo, hi),
      y = sqrt(c, rhs(c, x));
    if (y !== null) return { x, y: draw.below(2) ? y : mod(-y, c.p) };
  }
  return null;
}

// Classes of secp_case. The verdict is always recomputed by onCurve, so a
// class only steers the distribution.
function secpCase(c: Secp, d: Draw): [bigint, bigint] {
  const { p } = c;
  const valid = () => point(c, d.range(1n, c.n));
  const edges = (v: bigint) => [0n, 1n, p - 1n, p, p + 1n, TWO_256 - 1n, d.bigBelow(p), d.range(p, TWO_256), v];
  switch (d.below(10)) {
    case 0:
    case 1: {
      const q = valid();
      return [q.x, q.y];
    }
    case 2: {
      // small x: on the curve when x^3 + ax + b is a square (x = 0 on P-256)
      const x = BigInt(d.below(16)),
        y = sqrt(c, rhs(c, x));
      return [x, y === null ? d.bigBelow(p) : d.below(2) ? y : mod(-y, p)];
    }
    case 3: {
      // x + p for an on-curve point with x < 2^256 - p
      const q = pointWithX(c, d, 0n, TWO_256 - p);
      return q ? [q.x + p, q.y] : [p, 0n];
    }
    case 4: {
      // y + p for an on-curve point with y < 2^256 - p
      for (let i = 0; i < 32; i++) {
        const y = d.bigBelow(TWO_256 - p),
          xs = xsForY(c, y, d);
        if (xs.length) {
          const x = d.pick(xs);
          if (!onCurve(c, x, y)) throw new Error("cubic root is not on the curve");
          return d.below(4) ? [x, y + p] : [x, y];
        }
      }
      return [0n, p];
    }
    case 5: {
      // the largest x on the curve region, p - k
      const q = pointWithX(c, d, p - 64n, p);
      return q ? [q.x, q.y] : [p - 1n, 0n];
    }
    case 6:
      return [d.bigBelow(p), d.bigBelow(p)];
    case 7: {
      // one bit off a valid point
      const q = valid(),
        bit = 1n << BigInt(d.below(256));
      return d.below(2) ? [q.x ^ bit, q.y] : [q.x, q.y ^ bit];
    }
    default: {
      const q = valid();
      return [d.pick(edges(q.x)), d.pick(edges(q.y))];
    }
  }
}

// --- ECDSA: @noble/curves verification with the library's documented gate ---

interface EcdsaInput {
  x: bigint;
  y: bigint;
  r: bigint;
  s: bigint;
  z: bigint;
}

/** p - n: the library rejects r below it (module header of ecdsa.nr, class 1) and r >= n (class 4). */
const gap = (c: Secp) => c.p - c.n;

/**
 * The documented verdict: secpXXX_on_curve(pk) and ecdsa_XX_sig_admissible(sig)
 * and the std black box accepts (low s), where the black box is @noble/curves'
 * verify with lowS on the 32-byte hash (reduced mod n, no prehash).
 */
function ecdsaExpected(c: Secp, v: EcdsaInput) {
  const keyOnCurve = onCurve(c, v.x, v.y);
  let admissible = v.r >= gap(c) && v.r < c.n;
  if (c === R1) admissible = admissible && v.r !== v.s && v.r + v.s !== c.n;
  let verifies = false;
  if (keyOnCurve && v.r > 0n && v.r < c.n && v.s > 0n && v.s < c.n) {
    const pk = Uint8Array.from([4, ...toBytes(v.x), ...toBytes(v.y)]);
    const sig = Uint8Array.from([...toBytes(v.r), ...toBytes(v.s)]);
    verifies = c.noble.verify(sig, Uint8Array.from(toBytes(v.z)), pk, {
      lowS: true,
      prehash: false,
      format: "compact",
    });
  }
  return { keyOnCurve, admissible, valid: keyOnCurve && admissible && verifies };
}

const half = (c: Secp) => (c.n - 1n) / 2n;

/**
 * A textbook-valid signature under key P made from chosen u1, u2:
 * R = u1 G + u2 P, r = R.x mod n, s = r / u2, z = u1 s. Null when R is
 * infinity or r = 0.
 */
function forge(c: Secp, P: Affine, u1: bigint, u2: bigint): EcdsaInput | null {
  const Pt = c.noble.ProjectivePoint;
  const R = Pt.BASE.multiplyUnsafe(u1).add(Pt.fromAffine(P).multiplyUnsafe(u2));
  if (R.equals(Pt.ZERO)) return null;
  const r = mod(R.toAffine().x, c.n);
  if (r === 0n) return null;
  const s = mod(r * inv(u2, c.n), c.n);
  return { x: P.x, y: P.y, r, s, z: mod(u1 * s, c.n) };
}

/** barretenberg 6.0.0's secp256r1 offset generator H (biggroup offset generator). */
const R1_OFFSET_GENERATOR: Affine = {
  x: 0xb61bd0f5671bc04ec041799e87e735af4ed40920c6ca71e63c8010ff162bd90an,
  y: 0x338540b43f94cbfe32a1e62d192ea7d5827f4a4a66bb781a02321033110e492bn,
};

/**
 * secp256k1 inputs whose unblinded black-box call has no proof on bb 6.0.0:
 * keys solved so that a ladder step of its multiplication meets A = P,
 * 2A + P = O or A = -P; two inputs with R = u1 G + u2 Q at infinity whose last
 * ladder step meets 2A + P = O; and a valid signature with R = G that does
 * the same (ecdsa/vectors.nr in the library, generated independently).
 */
const K1_UNBLINDED_UNPROVABLE: EcdsaInput[] = [
  { x: 0x7f9b1bf2ddad89084801ba554c61d8964faadda8f72e2fad6f4b07b9d5223e52n, y: 0xdb0f472650db1c6db1f4f8bfa695f8b1bd6aef4d5652c9d7e2e16cccabc93e84n, r: 0x54594bf418e379cf4e0e502ee90e8555bd80b8a10664fb429075cb17750c0b17n, s: 0x7c8f978e351fca738afce2e9796a69d3cb30daab2d07e2ce5aa772736f744c64n, z: 0x0266023070076c2610997266308ea53c5f21a9051a330b7eb0bf4aa4189df8cbn },
  { x: 0x95f70959a4f80dbc2009852a412d4b7b305d4d37c61935140c1622efdda0461an, y: 0xfca767b52aaf2c887b68c9909c46933dbcaf5ffd7e6349fe3fd59555c6b579e3n, r: 0xa5da49fca6bfe3f760349387629e8f94f41d6739bb8defe5a46bafe9166ba081n, s: 0x1040ef1cab9efcf13ff5eef9dc979a26dcec557eb0120afc8731f50f17745600n, z: 0xa9065ae2522eae1f920124473494cfb00392435e54c3fbdef6a0b113f200d582n },
  { x: 0x7f9b1bf2ddad89084801ba554c61d8964faadda8f72e2fad6f4b07b9d5223e52n, y: 0x24f0b8d9af24e3924e0b0740596a074e429510b2a9ad36281d1e93325436bdabn, r: 0xb9afe664036ccd3b2f962ba7e751e518f853f4b8ade6a6a567b3c52306559b97n, s: 0x7b8d20b14df4a9e18508de5f067cfdf86ffb2a5f6e524fd57e60f8f33b4140c6n, z: 0x2a4fd6c874754a8d43d447266c1da06d4892168e289d4f02c91e2efcf0e1231fn },
  { x: 0xd549f08f90353a122bbbe0eb4cd901fa2d9469ede1bdf3e9c7df8d6e8a7eef88n, y: 0xba996da86ea8518bb9fd478b12aa0d8fb36f2093ddfaa50d3852882b8add079en, r: 0x59aec2dd7d060190b77a538f51020480b0e867eb0fb04ed114d42ba954e50505n, s: 0x5747fbf5d96527b107f9dd99637d6cc79d47c6642e841f856a8120fb1e0e45a4n, z: 0xbc4fc9734aaf06f103b20ef02b3a93019c7ba93bbcd93e00e04234e0a423b07fn },
  { x: 0x26587d0c80c18f8fd89859a6cada72ee8ef756c33e7c68ff0ae272dd99da625dn, y: 0x1b03642c7bc7edb1ee8ffd2d61e0afee460098824071fd8cc774e38b6dd3de92n, r: 0x76056f03abe10bedd8dbe2fe8701162d9d8145c78641811f8362b2bea41a4ed1n, s: 0x1bac3626ec64a4e31b5c5fd8ea6ad9ff7f131d39f797461680d38c5c27f23955n, z: 0xe60e793edcb9d758f9d8ee5b1e49805359df06084a6d515b70db70de761510e8n },
  { x: 0x955df289b0cb90e0152c9ece4f2d0a4e549969f221b3dc383616c47b2104f062n, y: 0x74e588f90609bc80b62ff89a4469a71156153ddf7bb78769ed68f81291f54394n, r: 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798n, s: 0x0ba150435a10c40ae4f6499bb46f477c593a9dbb2a2ba0ccdbfaa48a602899e7n, z: 0x511b6e3bc7149bb57b76da15e168f768ecd18e84283bb18087cc00b09d7b0e8bn },
];

function honest(c: Secp, d: Draw): EcdsaInput {
  const sk = d.range(1n, c.n),
    z = fromBytes(d.bytes(32)),
    P = point(c, sk);
  const sig = c.noble.sign(Uint8Array.from(toBytes(z)), sk, { lowS: true, prehash: false });
  return { x: P.x, y: P.y, r: sig.r, s: sig.s, z };
}

// Classes of ecdsa_case. Again only a distribution: ecdsaExpected decides.
function ecdsaCase(c: Secp, d: Draw): EcdsaInput {
  const { n, p } = c;
  const Pt = c.noble.ProjectivePoint;
  const base = honest(c, d);
  const key = () => point(c, d.range(1n, n));
  const unit = () => d.pick([1n, n - 1n]);
  const flip = (v: bigint) => v ^ (1n << BigInt(d.below(256)));
  const scalarEdge = (v: bigint) =>
    d.pick([0n, 1n, n - 1n, n, n + 1n, v + n < TWO_256 ? v + n : n, d.range(n, TWO_256), TWO_256 - 1n, gap(c) - 1n, gap(c)]);
  for (;;) {
    switch (d.below(25)) {
      case 0:
      case 1:
      case 2:
        return base;
      case 3:
        return { ...base, z: d.below(2) ? flip(base.z) : mod(base.z + 1n, TWO_256) };
      case 4:
        return { ...base, r: flip(base.r) };
      case 5:
        return { ...base, s: flip(base.s) };
      case 6:
        // high s: (r, n - s) is textbook-valid and must be rejected
        return { ...base, s: n - base.s };
      case 7:
        return { ...base, r: scalarEdge(base.r) };
      case 8:
        return { ...base, s: scalarEdge(base.s) };
      case 9: {
        // s at the low-s boundary: (n - 1)/2 is low, (n + 1)/2 is high
        const sk = d.range(1n, n),
          k = d.range(1n, n),
          P = point(c, sk),
          r = mod(point(c, k).x, n),
          s = half(c) + BigInt(d.below(2));
        return { x: P.x, y: P.y, r, s, z: mod(s * k - r * sk, n) };
      }
      case 10: {
        // R.x = r + n with r < p - n: textbook-valid, excluded by the gate
        const R = pointWithX(c, d, n, p);
        if (!R) continue;
        const u1 = d.range(1n, n),
          u2 = d.range(1n, n),
          iu2 = inv(u2, n);
        const P = Pt.fromAffine(R).add(Pt.BASE.multiply(u1).negate()).multiply(iu2).toAffine();
        const r = R.x - n,
          s = mod(r * iu2, n);
        return { x: P.x, y: P.y, r, s, z: mod(u1 * s, n) };
      }
      case 11: {
        // u2 = r/s in {1, -1}: r == s or r + s == n
        const v = forge(c, key(), d.range(1n, n), unit());
        if (v) return v;
        continue;
      }
      case 12: {
        // u1 in {0, 1, -1}: hash 0 (or n), s or n - s
        const v = forge(c, key(), d.pick([0n, 1n, n - 1n]), d.range(1n, n));
        if (!v) continue;
        return v.z === 0n && d.below(2) ? { ...v, z: n } : v;
      }
      case 13: {
        // hash + n verifies like hash
        if (base.z + n < TWO_256) return { ...base, z: base.z + n };
        return { ...base, z: base.z % n };
      }
      case 14: {
        // u1 G + u2 P at infinity
        const sk = d.range(1n, n),
          u2 = d.range(1n, n),
          u1 = mod(-u2 * sk, n),
          P = point(c, sk),
          r = d.range(1n, n),
          s = mod(r * inv(u2, n), n);
        return { x: P.x, y: P.y, r, s, z: mod(u1 * s, n) };
      }
      case 15: {
        // special valid keys: G, -G, 2G, the curve point with smallest or
        // largest x found, x = 0 on P-256; signatures forged for them
        const keys: (Affine | null)[] = [
          point(c, 1n),
          point(c, n - 1n),
          point(c, 2n),
          pointWithX(c, d, 0n, 64n),
          pointWithX(c, d, p - 64n, p),
        ];
        const P = d.pick(keys);
        if (!P) continue;
        const v = forge(c, P, d.range(1n, n), d.range(1n, n));
        if (v) return v;
        continue;
      }
      case 16:
        // random off-curve key with canonical coordinates
        return { ...base, x: d.bigBelow(p), y: d.bigBelow(p) };
      case 17:
        return d.below(2) ? { ...base, x: flip(base.x) } : { ...base, y: flip(base.y) };
      case 18: {
        // small-order points of y^2 = x^3 + b' and infinity encodings
        const [x, y] = d.pick([
          [0n, 1n],
          [0n, 2n],
          [5n, 0n],
          [0n, 0n],
          [p, 0n],
          [0n, p],
          [TWO_256 - 1n, TWO_256 - 1n],
        ]);
        return { ...base, x, y };
      }
      case 19:
        // x = 0 or y = 0 next to a valid other coordinate
        return d.below(2) ? { ...base, x: 0n } : { ...base, y: 0n };
      case 20: {
        // coordinates >= p congruent to a valid key
        const P = pointWithX(c, d, 0n, TWO_256 - p);
        if (!P) continue;
        const v = forge(c, P, d.range(1n, n), d.range(1n, n));
        if (!v) continue;
        return { ...v, x: v.x + p };
      }
      case 21: {
        // the negated key, and the other curve's key
        if (d.below(2)) return { ...base, y: mod(-base.y, p) };
        const o = c === K1 ? R1 : K1,
          P = point(o, d.range(1n, o.n));
        return { ...base, x: P.x, y: P.y };
      }
      case 22:
        return { x: base.x, y: base.y, r: d.pick([0n, TWO_256 - 1n]), s: d.pick([0n, TWO_256 - 1n]), z: base.z };
      case 23: {
        // inputs whose unblinded black-box call has no proof on bb 6.0.0:
        // fixed secp256k1 vectors, and on secp256r1 the keys -(1/4) H,
        // (1/4) H and H for bb's offset generator H, with u2 = 5
        if (c === K1) return d.pick(K1_UNBLINDED_UNPROVABLE);
        const H = Pt.fromAffine(R1_OFFSET_GENERATOR);
        const P = d.pick([H.multiply(n - inv(4n, n)), H.multiply(inv(4n, n)), H]).toAffine();
        const v = forge(c, P, d.range(1n, n), 5n);
        if (v) return v;
        continue;
      }
      default: {
        // hash = 2^256 - 1, n, 0 under an honest signature (verdict by reference)
        return { ...base, z: d.pick([0n, n, TWO_256 - 1n]) };
      }
    }
  }
}

const ecdsaBytes = (v: EcdsaInput) => ({
  x: toBytes(v.x),
  y: toBytes(v.y),
  sig: [...toBytes(v.r), ...toBytes(v.s)],
  hash: toBytes(v.z),
});

// ecdsa_fields_case: the same vectors with every byte as a Field, and in a
// third of cases one entry replaced by a value of 256 or more.
function ecdsaFieldsCase(c: Secp, d: Draw): Value[] {
  const v = ecdsaCase(c, d),
    b = ecdsaBytes(v);
  const all: bigint[] = [...b.x, ...b.y, ...b.sig, ...b.hash].map(BigInt);
  if (d.below(3) === 0) {
    const i = d.below(all.length);
    all[i] = d.pick([
      all[i] + 256n,
      all[i] + 256n * BigInt(1 + d.below(1000)),
      256n,
      P_FIELD - 1n,
      P_FIELD - 256n + all[i],
      (1n << 32n) + all[i],
      d.bigBelow(P_FIELD),
    ]);
  }
  const bytesOk = all.every((x) => x < 256n);
  const valid = bytesOk && ecdsaExpected(c, v).valid;
  return [all.slice(0, 32), all.slice(32, 64), all.slice(64, 128), all.slice(128, 160), valid];
}

// --- hashes ---

const bb = { api: null as BarretenbergSync | null };
const poseidon2 = (xs: bigint[]): bigint => {
  for (const x of xs) if (x < 0n || x >= P_FIELD) throw new Error(`${x} is not a Field`);
  const out = bb.api!.poseidon2Hash({ inputs: xs.map((x) => Uint8Array.from(toBytes(x))) });
  return fromBytes(out.hash);
};

/** A length for a variable-length entry of capacity n, as a Field. */
function lenCase(d: Draw, n: bigint): bigint {
  const boundaries = [55n, 56n, 63n, 64n, 119n, 120n, 127n, 128n, 135n, 136n, 137n, 3n, 4n, 6n, 7n];
  switch (d.below(12)) {
    case 0:
      return 0n;
    case 1:
      return n;
    case 2:
      return n + 1n;
    case 3: {
      const b = d.pick(boundaries);
      return b <= n + 1n ? b : d.bigBelow(n + 1n);
    }
    case 4:
      // truncates into range as a u32 but is not a valid length
      return (1n << 32n) + d.bigBelow(n + 1n);
    case 5:
      return d.pick([(1n << 32n) - 1n, (1n << 64n) + d.bigBelow(n + 1n), TWO_128 + d.bigBelow(n + 1n)]);
    case 6:
      // the Field negatives -1 .. -(n + 1)
      return P_FIELD - 1n - d.bigBelow(n + 1n);
    case 7:
      return d.bigBelow(P_FIELD);
    case 8:
      return d.range(n + 2n, 1n << 32n);
    default:
      return d.bigBelow(n + 1n);
  }
}

/** (digest, ok) of a byte hash over input[0..len], 32 zero bytes when len > N. */
function byteHashRef(hash: (b: Uint8Array) => Uint8Array, input: bigint[], len: bigint): Value[] {
  const ok = len <= BigInt(input.length);
  if (!ok) return [Array(32).fill(0n), false];
  const msg = Uint8Array.from(input.slice(0, Number(len)).map(Number));
  return [Array.from(hash(msg), BigInt), true];
}
const sha256 = (b: Uint8Array) => new Uint8Array(createHash("sha256").update(b).digest());

function poseidon2Ref(input: bigint[], len: bigint, sep: bigint, hasSep: boolean): Value[] {
  const ok = len <= BigInt(input.length);
  if (!ok) return [0n, false];
  const prefix = input.slice(0, Number(len));
  return [poseidon2(hasSep ? [sep, ...prefix] : prefix), true];
}

// --- Merkle trees: Aztec's node hash Poseidon2([sep, left, right]) ---

const MERKLE_SEP = 2982624097n;
const DEPTH = 5;

/** (root, ok, member) for the documented semantics of merkle_root_sep_or and is_member_sep. */
function merkleRef(leaf: bigint, index: bigint, path: bigint[], root: bigint, sep: bigint): Value[] {
  const ok = index < 1n << BigInt(path.length);
  if (!ok) return [0n, false, false];
  let node = leaf;
  path.forEach((sibling, i) => {
    node = (index >> BigInt(i)) & 1n ? poseidon2([sep, sibling, node]) : poseidon2([sep, node, sibling]);
  });
  return [node, true, node === root];
}

/** A random tree of 2^DEPTH leaves, one leaf's path, and tampered variants. */
function merkleCase(d: Draw): Value[] {
  const size = 1 << DEPTH;
  const sep = d.below(4) ? MERKLE_SEP : d.pick([BigInt(d.below(2 ** 24) * 256 + d.below(256)), d.bigBelow(P_FIELD), 0n]);
  const leaves = Array.from({ length: size }, () => (d.below(8) ? d.bigBelow(P_FIELD) : BigInt(d.below(4))));
  const levels = [leaves];
  while (levels[levels.length - 1].length > 1) {
    const prev = levels[levels.length - 1];
    levels.push(Array.from({ length: prev.length / 2 }, (_, i) => poseidon2([sep, prev[2 * i], prev[2 * i + 1]])));
  }
  const root = levels[DEPTH][0];
  const i = d.below(size);
  const path = levels.slice(0, DEPTH).map((level, h) => level[(i >> h) ^ 1]);
  let leaf = leaves[i],
    index = BigInt(i),
    claimed = root;
  switch (d.below(10)) {
    case 0:
      leaf = d.below(2) ? d.bigBelow(P_FIELD) : mod(leaf + 1n, P_FIELD);
      break;
    case 1:
      index = BigInt(i ^ (1 << d.below(DEPTH)));
      break;
    case 2:
      // out of range, some congruent to the real index mod 2^DEPTH
      index = d.pick([BigInt(size), BigInt(size + i), (1n << 32n) + BigInt(i), TWO_128 + BigInt(i), P_FIELD - 1n, P_FIELD - BigInt(size - i), d.bigBelow(P_FIELD)]);
      claimed = d.below(2) ? root : 0n;
      break;
    case 3:
      path[d.below(DEPTH)] = d.bigBelow(P_FIELD);
      break;
    case 4:
      claimed = d.pick([0n, mod(root + 1n, P_FIELD), d.bigBelow(P_FIELD)]);
      break;
    case 5:
      // two adjacent siblings swapped
      [path[0], path[1]] = [path[1], path[0]];
      break;
    default:
      break;
  }
  return [leaf, index, path, claimed, sep];
}

// --- Schnorr over Grumpkin (noir-lang/schnorr v0.4.0's scheme) ---

const GQ = 21888242871839275222246405745257275088696311157297823662689037894645226208583n; // group order
const GG: Affine = { x: 1n, y: 17631683881184975370165255887551781615748388533673675138860n };
const DST = 0x024c76938ed06b8ec1d9094b1013d190baa4011372f0604643bda812a63b832en;
type GPoint = Affine | null; // null is infinity
const onGrumpkin = (x: bigint, y: bigint) => mod(y * y - (x * x * x - 17n), P_FIELD) === 0n;
function gAdd(a: GPoint, b: GPoint): GPoint {
  if (!a) return b;
  if (!b) return a;
  const p = P_FIELD;
  let l: bigint;
  if (a.x === b.x) {
    if (mod(a.y + b.y, p) === 0n) return null;
    l = mod(3n * a.x * a.x * inv(2n * a.y, p), p);
  } else l = mod((b.y - a.y) * inv(b.x - a.x, p), p);
  const x = mod(l * l - a.x - b.x, p);
  return { x, y: mod(l * (a.x - x) - a.y, p) };
}
/** Affine double-and-add: slow, used to check the fast multiplication below. */
function gMulAffine(k: bigint, a: GPoint): GPoint {
  let r: GPoint = null;
  for (let i = BigInt(k.toString(2).length - 1); i >= 0n; i--) {
    r = gAdd(r, r);
    if ((k >> i) & 1n) r = gAdd(r, a);
  }
  return r;
}
// Scalar multiplication in projective coordinates, for speed: @noble/curves'
// generic short-Weierstrass code instantiated with Grumpkin's parameters.
const Grumpkin = weierstrassN({ p: P_FIELD, n: GQ, h: 1n, a: 0n, b: P_FIELD - 17n, Gx: GG.x, Gy: GG.y });
function gMul(k: bigint, a: GPoint): GPoint {
  if (!a) return null;
  const R = Grumpkin.fromAffine(a).multiplyUnsafe(mod(k, GQ));
  return R.is0() ? null : R.toAffine();
}
{
  const k = 0x1234567890abcdef1234567890abcdef1234567890abcdefn,
    slow = gMulAffine(k, GG),
    fast = gMul(k, GG);
  if (!onGrumpkin(GG.x, GG.y) || gMulAffine(GQ, GG) !== null || !slow || !fast || slow.x !== fast.x || slow.y !== fast.y)
    throw new Error("Grumpkin constants or arithmetic are wrong");
}
const DST_CHECK = () => {
  const src = Buffer.from("schnorr_grumpkin_poseidon2");
  const packed = Array.from(src).reduceRight((acc, b) => acc * 256n + BigInt(b), 0n);
  if (poseidon2([packed]) !== DST) throw new Error("Schnorr DST does not match its derivation");
};

// bb 6.0.0's MSM offset generators o_1, o_2, o_3 (cycle_group's
// derive_generators("cycle_group_offset_generator")) and -(1/15) o_2.
const MSM_OFFSET_KEYS: bigint[][] = [
  [0x07ecf4931ea0257c089816cfc3ed44c9172b22622539fdad7535401a7a99fb4bn, 0x0f8bf0d676c12c8e10ea1f8fe9e5100db24b89ef3006b321f2178adc6281ec74n],
  [0x0fb76e5904e203fe96cf620f86739e685c85c56774b23c1e7c86fba3290ae42bn, 0x2a32122a08e2dcc594f4b657eb5e2e4f84cb67f06ab4b2d432c5f61c22330a3fn],
  [0x2e09e700d6472d6d69189b06ddde8a0c0a559603086c619abc217c43534866f6n, 0x0ff3c9ddfc6aaa740822422a0cf194a98d6a06ec2c433435b5bae6a172d56b5fn],
  [0x23d26cbbc30f73d118577822621b815c5237a7e239312ff1d197ba4948a2ee9an, 0x3029dcebcc17d09a134832fe0eafa83f5b8d09b522ac9c352475441c24ed6c02n],
];
for (const [x, y] of MSM_OFFSET_KEYS)
  if (!onGrumpkin(x, y)) throw new Error("MSM offset generator is not on Grumpkin");

const limbs = (v: bigint): bigint[] => [v % TWO_128, v / TWO_128];
const canonical = (lo: bigint, hi: bigint) => lo < TWO_128 && hi < TWO_128 && lo + hi * TWO_128 < GQ;

/** (inputs_ok, valid) as schnorr_inputs_ok and schnorr_verify document them. */
function schnorrExpected(px: bigint, py: bigint, sig: bigint[], msg: bigint) {
  const inputsOk = onGrumpkin(px, py) && canonical(sig[0], sig[1]) && canonical(sig[2], sig[3]);
  if (!inputsOk) return { inputsOk, valid: false };
  const s = sig[0] + sig[1] * TWO_128,
    e = sig[2] + sig[3] * TWO_128;
  if (s === 0n || e === 0n) return { inputsOk, valid: false };
  const R = gAdd(gMul(s, GG), gMul(e, { x: px, y: py }));
  const valid = R !== null && poseidon2([DST, R.x, px, py, msg]) === e % P_FIELD;
  // Cross-check with Barretenberg's native verifier where its scalar
  // encoding is unambiguous (e below the Field modulus).
  if (e < P_FIELD) {
    const bbValid = bb.api!.schnorrVerifySignature({
      messageField: Uint8Array.from(toBytes(msg)),
      publicKey: { x: Uint8Array.from(toBytes(px)), y: Uint8Array.from(toBytes(py)) },
      s: Uint8Array.from(toBytes(s)),
      e: Uint8Array.from(toBytes(e)),
    }).verified;
    if (bbValid !== valid) throw new Error(`Schnorr reference disagrees with bb.js on ${[px, py, s, e, msg]}`);
  }
  return { inputsOk, valid };
}

function schnorrSign(d: Draw, sk: bigint, msg: bigint): bigint[] {
  for (;;) {
    const k = d.range(1n, GQ),
      R = gMul(k, GG)!,
      P = gMul(sk, GG)!;
    const e = poseidon2([DST, R.x, P.x, P.y, msg]);
    const s = mod(k - e * sk, GQ);
    if (s !== 0n && e !== 0n) return [...limbs(s), ...limbs(e)];
  }
}

function schnorrCase(d: Draw): Value[] {
  const sk = d.pick([1n, GQ - 1n, d.range(1n, GQ), d.range(1n, GQ)]);
  const P = gMul(sk, GG)!;
  const msg = d.below(4) ? d.bigBelow(P_FIELD) : BigInt(d.below(1000));
  const sig = schnorrSign(d, sk, msg);
  let [px, py, m] = [P.x, P.y, msg];
  const s = sig[0] + sig[1] * TWO_128,
    e = sig[2] + sig[3] * TWO_128;
  const set = (sv: bigint, ev: bigint) => {
    sig.splice(0, 4, ...limbs(sv), ...limbs(ev));
  };
  switch (d.below(16)) {
    case 0:
    case 1:
    case 2:
      break;
    case 3:
      m = mod(m + 1n + d.bigBelow(3n), P_FIELD);
      break;
    case 4:
      set(s ^ (1n << BigInt(d.below(254))), e);
      break;
    case 5:
      set(s, e ^ (1n << BigInt(d.below(254))));
      break;
    case 6:
      set(d.pick([0n, s]), d.pick([0n, e === 0n ? 1n : 0n]));
      break;
    case 7:
      // scalars at or above the group order
      if (d.below(2)) set(s + GQ, e);
      else set(s, d.pick([e + GQ, GQ, GQ - 1n]));
      break;
    case 8: {
      // the same scalar split non-canonically
      const i = d.pick([0, 2]);
      if (sig[i + 1] > 0n) {
        sig[i] += TWO_128;
        sig[i + 1] -= 1n;
      } else sig[i + 1] = TWO_128;
      break;
    }
    case 9:
      // e + p: the same challenge as a Field, a different scalar
      set(s, e + P_FIELD);
      break;
    case 10:
      // the negated signature: R' = -R has the same x, the challenge differs
      set(mod(-s, GQ), mod(-e, GQ));
      break;
    case 11:
      // off-curve keys, (0, 0), the negated key, and bb's MSM offset
      // generators o_1, o_2, o_3 and -(1/15) o_2 (keys bb's MSM gadget
      // cannot prove unblinded)
      [px, py] = d.pick([
        [px, mod(py + 1n, P_FIELD)],
        [0n, 0n],
        [px, mod(-py, P_FIELD)],
        [d.bigBelow(P_FIELD), d.bigBelow(P_FIELD)],
        ...MSM_OFFSET_KEYS,
      ]);
      break;
    case 12: {
      // R = s G + e P at infinity
      const s2 = mod(-e * sk, GQ);
      set(s2 === 0n ? 1n : s2, e);
      break;
    }
    case 13:
      for (let i = 0; i < 4; i++) sig[i] = d.pick([d.bigBelow(TWO_128), d.bigBelow(P_FIELD), TWO_128 - 1n, TWO_128]);
      break;
    case 14:
      set(GQ - 1n, GQ - 1n);
      break;
    default:
      // a signature under another key
      [px, py] = (() => {
        const Q = gMul(d.range(1n, GQ), GG)!;
        return [Q.x, Q.y];
      })();
      break;
  }
  const { inputsOk, valid } = schnorrExpected(px, py, sig, m);
  return [px, py, sig, m, inputsOk, valid];
}

// --- the oracles ---

type Oracle = (inputs: Param[]) => Value[];

const oracles: Record<string, Oracle> = {
  // (seed, curve) -> (x, y, on_curve)
  secp_case: ([seed, curve]) => {
    const c = curveOf(single(curve)),
      [x, y] = secpCase(c, new Draw(single(seed), "secp" + c.name));
    return [toBytes(x).map(BigInt), toBytes(y).map(BigInt), onCurve(c, x, y)];
  },
  // (x, y, curve) -> on_curve
  secp_on_curve_ref: ([x, y, curve]) => [onCurve(curveOf(single(curve)), fromBytes(array(x)), fromBytes(array(y)))],
  // (seed, curve) -> (pk_x, pk_y, sig, hash, key_on_curve, sig_admissible, valid)
  ecdsa_case: ([seed, curve]) => {
    const c = curveOf(single(curve)),
      v = ecdsaCase(c, new Draw(single(seed), "ecdsa" + c.name)),
      b = ecdsaBytes(v),
      e = ecdsaExpected(c, v);
    return [b.x, b.y, b.sig, b.hash].map((a) => a.map(BigInt) as Value).concat([e.keyOnCurve, e.admissible, e.valid]);
  },
  // (seed, curve) -> (pk_x, pk_y, sig, hash, valid), every byte a Field
  ecdsa_fields_case: ([seed, curve]) => {
    const c = curveOf(single(curve));
    return ecdsaFieldsCase(c, new Draw(single(seed), "ecdsa_fields" + c.name));
  },
  // (seed, capacity) -> len
  len_case: ([seed, n]) => [lenCase(new Draw(single(seed), "len"), single(n))],
  // (input, len) -> (digest, ok)
  sha256_ref: ([input, len]) => byteHashRef(sha256, array(input), single(len)),
  keccak256_ref: ([input, len]) => byteHashRef(keccak_256, array(input), single(len)),
  // (input, len, sep, has_sep) -> (digest, ok)
  poseidon2_ref: ([input, len, sep, hasSep]) =>
    poseidon2Ref(Array.isArray(input) ? array(input) : [], single(len), single(sep), single(hasSep) === 1n),
  // seed -> (leaf, index, path, root, sep)
  merkle_case: ([seed]) => merkleCase(new Draw(single(seed), "merkle")),
  // (leaf, index, path, root, sep) -> (root, ok, member)
  merkle_ref: ([leaf, index, path, root, sep]) =>
    merkleRef(single(leaf), single(index), array(path), single(root), single(sep)),
  // seed -> (pk_x, pk_y, sig, msg, inputs_ok, valid)
  schnorr_case: ([seed]) => schnorrCase(new Draw(single(seed), "schnorr")),
};

async function handleForeignCall(params: unknown[]): Promise<ForeignCallResult> {
  const [callInfo] = params as [ForeignCallInfo];
  const { function: functionName, inputs } = callInfo;
  const oracle = oracles[functionName];
  if (!oracle) throw new Error(`Unknown function: ${functionName}`);
  return { values: oracle(inputs).map(encode) };
}

// --- server ---

const app = express();
app.use(express.json({ limit: "10mb" }));

app.post("/", async (req, res) => {
  const { method, params, id } = req.body;
  if (method !== "resolve_foreign_call") {
    res.json({ jsonrpc: "2.0", id, error: { code: -32601, message: "Method not found" } });
    return;
  }
  try {
    const result = await handleForeignCall(params || []);
    res.json({ jsonrpc: "2.0", id, result });
  } catch (error) {
    console.error(error);
    res.json({ jsonrpc: "2.0", id, error: { code: -32000, message: String((error as Error).message ?? error) } });
  }
});

app.get("/health", (_req, res) => {
  res.json({ status: "ok" });
});

const PORT = Number(process.env.PORT || 8095);
BarretenbergSync.initSingleton().then((api) => {
  bb.api = api;
  DST_CHECK();
  app.listen(PORT, "127.0.0.1", () => {
    console.log(`Oracle server running on 127.0.0.1:${PORT}`);
  });
});
