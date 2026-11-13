#!/usr/bin/env python3
"""Gate-cost benchmark driver for the total library.

For every (native op, total op) pair it generates tiny Noir packages that
apply the op N times over N distinct witness inputs, compiles them,
measures UltraHonk gates and ACIR opcodes with `bb gates`, fits
gates(N) = a + b*N and writes build/gate-costs.md (the raw points
go to build/gate-costs.json).

Disk discipline: packages are built one group at a time; each package
directory (source, target/, artifact) is deleted right after it has been
measured, and the group directory is removed before the next group starts.
Only numbers survive, in <build>/results.json (resumable cache).

A run limited by --groups or --only still rewrites the whole report: the
benchmarks it does not select keep their recorded points from the current
build/gate-costs.json.

Usage: scripts/gate-bench.sh [--groups g1,g2] [--smoke] [--workers K]
"""
import argparse, json, os, re, shutil, subprocess, sys, time, itertools
from concurrent.futures import ThreadPoolExecutor, as_completed

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NARGO = os.environ.get("NARGO", "nargo")
BB = os.environ.get("BB", "bb")
BUILD = os.environ.get("GATE_BENCH_BUILD", os.path.join(REPO, "build", "gate-bench"))
RAW_JSON = os.path.join(REPO, "build", "gate-costs.json")  # raw points, kept after the run
DOCS = os.path.join(REPO, "build")
NS_DEFAULT = [1, 8, 32, 64, 128, 256]

UTYPES = [("u8", 8), ("u16", 16), ("u32", 32), ("u64", 64), ("u128", 128)]
ITYPES = [("i8", 8, "u8"), ("i16", 16, "u16"), ("i32", 32, "u32"), ("i64", 64, "u64")]

PRELUDE = """use total::arith::{TotalMulDiv, Saturating, TotalArith};
use total::convert::TotalNarrow;
use total::ctl::{Outcome, Select};
use total::signed::TotalSigned;
use std::ops::{WrappingAdd, WrappingMul, WrappingSub};
use std::embedded_curve_ops::{EmbeddedCurvePoint, EmbeddedCurveScalar, embedded_curve_add, multi_scalar_mul};
"""


class Bench:
    """One comparison. `variants` maps a variant name to (pre, op, post)
    Noir snippets; the first variant named native* is the primary native,
    variants named total* are total forms. params: (name, elem type, size)
    where size is a Python expression in N (e.g. "N", "2*N") or an int for
    a fixed-size array, or None for a scalar."""

    def __init__(self, id, group, title, params, variants, ns=None, dep="total", note="", ns_native=None):
        self.id, self.group, self.title = id, group, title
        self.params, self.variants = params, variants
        self.ns = ns or NS_DEFAULT
        self.dep, self.note = dep, note
        self.ns_native = ns_native  # larger N for natives that sit on a table floor

    def ns_for(self, variant):
        if self.ns_native and variant.startswith("native"):
            return self.ns_native
        return self.ns


BENCHES = []


def add(*a, **k):
    BENCHES.append(Bench(*a, **k))


def v(op, pre="", post=""):
    return (pre, op, post)


def tof(t, e):
    """expression e of type t as Field (signed via the unsigned pattern)."""
    if t.startswith("i"):
        return f"(({e}) as u{t[1:]}) as Field"
    if t == "bool":
        return f"({e}) as Field"
    return f"({e}) as Field"


# ------------------------------------------------------------------ sinks
add("sink1", "baseline", "accumulator sink only: acc += x (one term)",
    [("x", "Field", "N")], {"native": v("acc += x[i];")})
add("sink2", "baseline", "accumulator sink only: acc += x + y (two terms)",
    [("x", "Field", "N"), ("y", "Field", "N")], {"native": v("acc += x[i] + y[i];")})

# ------------------------------------------------------------------ range
for w in (1, 8, 16, 32, 64, 128):
    add(f"fits_bits_{w}", "range", f"fits_bits::<{w}> vs assert_max_bit_size::<{w}>",
        [("x", "Field", "N")],
        {"native": v(f"x[i].assert_max_bit_size::<{w}>(); acc += x[i];"),
         "total": v(f"let ok = total::range::fits_bits::<{w}>(x[i]); acc += x[i] + ok as Field;")})
for w in (8, 64, 128):
    add(f"clamp_bits_or_{w}", "range", f"clamp_bits_or::<{w}> vs assert_max_bit_size::<{w}>",
        [("x", "Field", "N")],
        {"native": v(f"x[i].assert_max_bit_size::<{w}>(); acc += x[i];"),
         "total": v(f"let (c, ok) = total::range::clamp_bits_or::<{w}>(x[i]); acc += c + ok as Field;")})

# ------------------------------------------------------------------ cmp
for t, w in UTYPES:
    add(f"lt_{t}", "cmp", f"lt on {t} (typed inputs) vs native <",
        [("a", t, "N"), ("b", t, "N")],
        {"native": v("acc += (a[i] < b[i]) as Field;"),
         "total": v("acc += total::lt(a[i], b[i]) as Field;")})
for t, w, u in ITYPES:
    add(f"lt_{t}", "cmp", f"lt on {t} (typed inputs) vs native <",
        [("a", t, "N"), ("b", t, "N")],
        {"native": v("acc += (a[i] < b[i]) as Field;"),
         "total": v("acc += total::lt(a[i], b[i]) as Field;")})
for fn, sym in (("lte", "<="), ("gt", ">"), ("gte", ">=")):
    for t in ("u64", "i64"):
        add(f"{fn}_{t}", "cmp", f"{fn} on {t} vs native {sym}",
            [("a", t, "N"), ("b", t, "N")],
            {"native": v(f"acc += (a[i] {sym} b[i]) as Field;"),
             "total": v(f"acc += total::{fn}(a[i], b[i]) as Field;")})
add("lt_field", "cmp", "lt on Field vs std::field::bn254::lt",
    [("a", "Field", "N"), ("b", "Field", "N")],
    {"native": v("acc += std::field::bn254::lt(a[i], b[i]) as Field;"),
     "total": v("acc += total::lt(a[i], b[i]) as Field;")})
add("lte_field", "cmp", "lte on Field vs !bn254::lt(b, a)",
    [("a", "Field", "N"), ("b", "Field", "N")],
    {"native": v("acc += (!std::field::bn254::lt(b[i], a[i])) as Field;"),
     "total": v("acc += total::lte(a[i], b[i]) as Field;")})
add("eq_field", "cmp", "eq on Field vs ==",
    [("a", "Field", "N"), ("b", "Field", "N")],
    {"native": v("acc += (a[i] == b[i]) as Field;"),
     "total": v("acc += total::eq(a[i], b[i]) as Field;")})
add("is_zero_field", "cmp", "is_zero vs x == 0",
    [("a", "Field", "N")],
    {"native": v("acc += (a[i] == 0) as Field;"),
     "total": v("acc += total::is_zero(a[i]) as Field;")})
add("min_u64", "cmp", "min on u64 vs if a < b",
    [("a", "u64", "N"), ("b", "u64", "N")],
    {"native": v("acc += (if a[i] < b[i] { a[i] } else { b[i] }) as Field;"),
     "total": v("acc += total::cmp::min(a[i], b[i]) as Field;")})
add("min_field", "cmp", "min on Field vs if bn254::lt",
    [("a", "Field", "N"), ("b", "Field", "N")],
    {"native": v("acc += if std::field::bn254::lt(a[i], b[i]) { a[i] } else { b[i] };"),
     "total": v("acc += total::cmp::min(a[i], b[i]);")})
add("cmp_bits_64", "cmp", "cmp_bits::<64> (Field operands, flags) vs two assert_max_bit_size + native u64 <",
    [("a", "Field", "N"), ("b", "Field", "N")],
    {"native": v("a[i].assert_max_bit_size::<64>(); b[i].assert_max_bit_size::<64>(); acc += ((a[i] as u64) < (b[i] as u64)) as Field;"),
     "total": v("let f = total::cmp::cmp_bits::<64>(a[i], b[i]); acc += f.ok() as Field + f.lte() as Field;")})

# ---------------------------------------------------------------- convert
for t, w in UTYPES:
    add(f"to_{t}_or", "convert", f"to_{t}_or (Field in) vs silent `as {t}` and assert_max_bit_size + `as {t}`",
        [("x", "Field", "N")],
        {"native_silent": v(f"acc += (x[i] as {t}) as Field;"),
         "native_checked": v(f"x[i].assert_max_bit_size::<{w}>(); acc += (x[i] as {t}) as Field;"),
         "total": v(f"let (c, ok) = total::convert::to_{t}_or(x[i]); acc += (c as Field) + ok as Field;")})
for t, w, u in ITYPES:
    add(f"to_{t}_or", "convert", f"to_{t}_or (Field in, bit-pattern reading) vs silent `as {u} as {t}` and checked",
        [("x", "Field", "N")],
        {"native_silent": v(f"acc += ((x[i] as {u}) as {t} as {u}) as Field;"),
         "native_checked": v(f"x[i].assert_max_bit_size::<{w}>(); acc += ((x[i] as {u}) as {t} as {u}) as Field;"),
         "total": v(f"let (c, ok) = total::convert::to_{t}_or(x[i]); acc += ((c as {u}) as Field) + ok as Field;")})
for src, dst in (("u64", "u32"), ("u32", "u8"), ("u128", "u64"), ("i64", "i32"), ("u64", "i64")):
    add(f"narrow_{src}_{dst}", "convert", f"TotalNarrow {src} -> {dst} vs silent `as {dst}`",
        [("a", src, "N")],
        {"native": v(f"acc += ({tof(dst, f'a[i] as {dst}')});"),
         "total": v(f"let (c, ok) = TotalNarrow::<{dst}>::narrow_or(a[i]); acc += {tof(dst, 'c')} + ok as Field;")})
add("truncate_32", "convert", "truncate_or::<32> (Field, returns low and dropped part) vs `as u32`",
    [("x", "Field", "N")],
    {"native": v("acc += (x[i] as u32) as Field;"),
     "total": v("let (lo, hi, ok) = total::convert::truncate_or::<32>(x[i]); acc += lo + hi + ok as Field;")})
add("bool_or", "convert", "bool_or vs assert_max_bit_size::<1>",
    [("x", "Field", "N")],
    {"native": v("x[i].assert_max_bit_size::<1>(); acc += x[i];"),
     "total": v("let (b, ok) = total::convert::bool_or(x[i]); acc += (b as Field) + ok as Field;")})
add("to_le_bytes_total", "convert", "to_le_bytes_total (32 bytes, canonical, no flag) vs std to_le_bytes::<32>",
    [("x", "Field", "N")], ns=[1, 8, 16, 32, 64],
    variants={"native": v("let b: [u8; 32] = x[i].to_le_bytes(); acc += (b[0] as Field) + (b[31] as Field);"),
     "total": v("let b = total::convert::to_le_bytes_total(x[i]); acc += (b[0] as Field) + (b[31] as Field);")})
add("to_le_bits_total", "convert", "to_le_bits_total (254 bits, canonical) vs std to_le_bits::<254>",
    [("x", "Field", "N")], ns=[1, 8, 16, 32, 64],
    variants={"native": v("let b: [bool; 254] = x[i].to_le_bits(); acc += (b[0] as Field) + (b[253] as Field);"),
     "total": v("let b = total::convert::to_le_bits_total(x[i]); acc += (b[0] as Field) + (b[253] as Field);")})
add("to_le_bytes_or_8", "convert", "to_le_bytes_or::<8> vs std to_le_bytes::<8>",
    [("x", "Field", "N")],
    {"native": v("let b: [u8; 8] = x[i].to_le_bytes(); acc += (b[0] as Field) + (b[7] as Field);"),
     "total": v("let (b, ok) = total::convert::to_le_bytes_or::<8>(x[i]); acc += (b[0] as Field) + (b[7] as Field) + ok as Field;")})
add("to_le_bits_or_64", "convert", "to_le_bits_or::<64> vs std to_le_bits::<64>",
    [("x", "Field", "N")],
    {"native": v("let b: [bool; 64] = x[i].to_le_bits(); acc += (b[0] as Field) + (b[63] as Field);"),
     "total": v("let (b, ok) = total::convert::to_le_bits_or::<64>(x[i]); acc += (b[0] as Field) + (b[63] as Field) + ok as Field;")})
add("from_le_bytes_or", "convert", "from_le_bytes_or (canonical) vs a plain 32-byte accumulate (malleable)",
    [("b", "[u8; 32]", "N")], ns=[1, 4, 16, 32, 64],
    variants={"native": v("let mut r: Field = 0; for j in 0..32 { r = r * 256 + (b[i][31 - j] as Field); } acc += r;"),
     "total": v("let (r, ok) = total::convert::from_le_bytes_or(b[i]); acc += r + ok as Field;")})

# ------------------------------------------------------------------ arith
for t, w in UTYPES:
    for name, sym, wr in (("add", "+", "wrapping_add"), ("sub", "-", "wrapping_sub"), ("mul", "*", "wrapping_mul")):
        add(f"{name}_{t}", "arith", f"{name}_or on {t} vs native {sym} (asserting) and {wr}",
            [("a", t, "N"), ("b", t, "N")],
            {"native": v(f"acc += (a[i] {sym} b[i]) as Field;"),
             "native_wrapping": v(f"acc += a[i].{wr}(b[i]) as Field;"),
             "total": v(f"let (c, ok) = TotalArith::{name}_or(a[i], b[i]); acc += (c as Field) + ok as Field;")})
    for name, sym in (("div", "/"), ("mod", "%")):
        add(f"{name}_{t}", "arith", f"{name}_or on {t} vs native {sym}",
            [("a", t, "N"), ("b", t, "N")],
            {"native": v(f"acc += (a[i] {sym} b[i]) as Field;"),
             "total": v(f"let (c, ok) = TotalArith::{name}_or(a[i], b[i]); acc += (c as Field) + ok as Field;")})
    for name, sym in (("add", "wrapping_add"), ("sub", "wrapping_sub"), ("mul", "wrapping_mul")):
        add(f"sat{name}_{t}", "arith", f"saturating_{name} on {t} vs std {sym} (no native saturating exists)",
            [("a", t, "N"), ("b", t, "N")],
            {"native": v(f"acc += a[i].{sym}(b[i]) as Field;"),
             "total": v(f"acc += Saturating::saturating_{name}(a[i], b[i]) as Field;")})
for name, sym in (("add", "+"), ("sub", "-"), ("mul", "*")):
    add(f"{name}_or_64", "arith", f"{name}_or::<64> (Field-domain, u64-typed inputs cast up) vs native u64 {sym}",
        [("a", "u64", "N"), ("b", "u64", "N")],
        {"native": v(f"acc += (a[i] {sym} b[i]) as Field;"),
         "total": v(f"let (c, ok) = total::arith::{name}_or::<64>(a[i] as Field, b[i] as Field); acc += c + ok as Field;")})
add("inverse_or", "arith", "inverse_or (Field) vs std `1 / x`",
    [("x", "Field", "N")],
    {"native": v("acc += 1 / x[i];"),
     "total": v("let (r, ok) = total::arith::inverse_or(x[i]); acc += r + ok as Field;")})
add("field_div_or", "arith", "field_div_or vs std Field `a / b`",
    [("a", "Field", "N"), ("b", "Field", "N")],
    {"native": v("acc += a[i] / b[i];"),
     "total": v("let (r, ok) = total::arith::field_div_or(a[i], b[i]); acc += r + ok as Field;")})
add("sqrt_or", "arith", "sqrt_or (Field; no native sqrt exists)",
    [("x", "Field", "N")], ns=[1, 8, 16, 32, 64],
    variants={"total": v("let (r, ok) = total::arith::sqrt_or(x[i]); acc += r + ok as Field;")})
add("pow_or_64_8", "arith", "pow_or::<64, 8> (Field operands, flagged overflow) vs native u64 power by square-multiply (8 exponent bits)",
    [("a", "u64", "N"), ("e", "u64", "N")], ns=[1, 4, 16, 32, 64],
    variants={"native": v("let mut r: u64 = 1; let mut b = a[i]; for j in 0..8 { if (e[i] >> (j as u64)) & 1 == 1 { r = r * b; } b = b.wrapping_mul(b); } acc += r as Field;"),
     "total": v("let (r, ok) = total::arith::pow_or::<64, 8>(a[i] as Field, e[i] as Field); acc += r + ok as Field;")})

# ----------------------------------------------------------------- muldiv
for t, w in (("u32", 32), ("u64", 64)):
    add(f"mul_div_{t}", "muldiv",
        f"TotalMulDiv::mul_div_or on {t} (fused floor(a*b/d), quotient narrowed to {t}) vs native "
        f"(a as u128 * b as u128) / d (asserting) and the u128 facades mul_or then div_or",
        [("a", t, "N"), ("b", t, "N"), ("d", t, "N")],
        {"native": v("acc += (((a[i] as u128) * (b[i] as u128)) / (d[i] as u128)) as Field;"),
         "native_facades": v("let (p, ok1) = TotalArith::mul_or(a[i] as u128, b[i] as u128); "
                             "let (q, ok2) = TotalArith::div_or(p, d[i] as u128); acc += (q as Field) + (ok1 & ok2) as Field;"),
         "total": v("let (q, _, ok) = TotalMulDiv::mul_div_or(a[i], b[i], d[i]); acc += (q as Field) + ok as Field;")})
add("mul_div_or_64", "muldiv",
    "mul_div_or::<64> (Field-domain with input clamps, 128-bit quotient; u64-typed inputs cast up) vs native "
    "(a as u128 * b as u128) / d (asserting)",
    [("a", "u64", "N"), ("b", "u64", "N"), ("d", "u64", "N")],
    {"native": v("acc += (((a[i] as u128) * (b[i] as u128)) / (d[i] as u128)) as Field;"),
     "total": v("let (q, _, ok) = total::arith::mul_div_or::<64>(a[i] as Field, b[i] as Field, d[i] as Field); acc += q + ok as Field;")})
add("mul_div_or_84", "muldiv",
    "mul_div_or::<84> (Field operands, the widest N; no native: the product does not fit u128)",
    [("a", "Field", "N"), ("b", "Field", "N"), ("d", "Field", "N")],
    {"total": v("let (q, _, ok) = total::arith::mul_div_or::<84>(a[i], b[i], d[i]); acc += q + ok as Field;")})
add("mul_div_u128", "muldiv",
    "TotalMulDiv::mul_div_or on u128 (wide gadget at N = 128, quotient narrowed to u128) vs native "
    "a * b / d on u128 (asserting; it also fails whenever a*b >= 2^128) and the u128 facades mul_or then div_or",
    [("a", "u128", "N"), ("b", "u128", "N"), ("d", "u128", "N")],
    {"native": v("acc += ((a[i] * b[i]) / d[i]) as Field;"),
     "native_facades": v("let (p, ok1) = TotalArith::mul_or(a[i], b[i]); "
                         "let (q, ok2) = TotalArith::div_or(p, d[i]); acc += (q as Field) + (ok1 & ok2) as Field;"),
     "total": v("let (q, _, ok) = TotalMulDiv::mul_div_or(a[i], b[i], d[i]); acc += (q as Field) + ok as Field;")})
for w in (96, 112, 124, 125, 128):
    add(f"mul_div_wide_or_{w}", "muldiv",
        f"mul_div_wide_or::<{w}> (Field operands with input clamps, quotient as two 128-bit limbs; no native: "
        f"the product does not fit u128)",
        [("a", "Field", "N"), ("b", "Field", "N"), ("d", "Field", "N")],
        {"total": v(f"let (l, h, _, ok) = total::arith::mul_div_wide_or::<{w}>(a[i], b[i], d[i]); acc += l + h + ok as Field;")})
add("mul_div_wide_to_or_135", "muldiv",
    "mul_div_wide_to_or::<135> (Field operands clamped to 128 bits, quotient flagged below 2^135; no native)",
    [("a", "Field", "N"), ("b", "Field", "N"), ("d", "Field", "N")],
    {"total": v("let (q, _, ok) = total::arith::mul_div_wide_to_or::<135>(a[i], b[i], d[i]); acc += q + ok as Field;")})

# ----------------------------------------------------------------- signed
for t, w, u in ITYPES:
    for name, sym in (("add", "+"), ("sub", "-"), ("mul", "*"), ("div", "/"), ("mod", "%")):
        add(f"s{name}_{t}", "signed", f"{name}_or on {t} vs native {sym}",
            [("a", t, "N"), ("b", t, "N")],
            {"native": v(f"acc += {tof(t, f'a[i] {sym} b[i]')};"),
             "total": v(f"let (c, ok) = TotalArith::{name}_or(a[i], b[i]); acc += {tof(t, 'c')} + ok as Field;")})
    add(f"sneg_{t}", "signed", f"neg_or on {t} vs native unary -",
        [("a", t, "N")],
        {"native": v(f"acc += {tof(t, '-a[i]')};"),
         "total": v(f"let (c, ok) = TotalSigned::neg_or(a[i]); acc += {tof(t, 'c')} + ok as Field;")})
    add(f"sabs_{t}", "signed", f"abs_or on {t} vs `if a < 0 {{ -a }} else {{ a }}`",
        [("a", t, "N")],
        {"native": v(f"acc += {tof(t, 'if a[i] < 0 { -a[i] } else { a[i] }')};"),
         "total": v(f"let (c, ok) = TotalSigned::abs_or(a[i]); acc += {tof(t, 'c')} + ok as Field;")})

# ---------------------------------------------------------------- bitwise
for name, sym in (("and", "&"), ("or", "|"), ("xor", "^")):
    for t, w in (("u8", 8), ("u32", 32), ("u64", 64), ("u128", 128)):
        if name != "xor" and t in ("u32", "u128"):
            continue
        add(f"{name}_bits_{w}", "bitwise", f"{name}_bits_or::<{w}> (Field operands, flag) vs native {sym} on {t}",
            [("a", t, "N"), ("b", t, "N")], ns_native=[256, 1024, 2048, 4096],
            variants={"native": v(f"acc += (a[i] {sym} b[i]) as Field;"),
             "total": v(f"let (c, ok) = total::bitwise::{name}_bits_or::<{w}>(a[i] as Field, b[i] as Field); acc += c + ok as Field;")})
add("not_bits_32", "bitwise", "not_bits_or::<32> vs native ! on u32",
    [("a", "u32", "N")],
    {"native": v("acc += (!a[i]) as Field;"),
     "total": v("let (c, ok) = total::bitwise::not_bits_or::<32>(a[i] as Field); acc += c + ok as Field;")})
for t, w in (("u32", 32), ("u64", 64)):
    add(f"shl_{t}", "bitwise", f"shl_exact_or::<{w}> vs native << ({t} by {t})",
        [("a", t, "N"), ("s", t, "N")],
        {"native": v("acc += (a[i] << s[i]) as Field;"),
         "total": v(f"let (c, ok) = total::bitwise::shl_exact_or::<{w}>(a[i] as Field, s[i] as Field); acc += c + ok as Field;")})
    add(f"shr_{t}", "bitwise", f"shr_or::<{w}> vs native >> ({t} by {t})",
        [("a", t, "N"), ("s", t, "N")],
        {"native": v("acc += (a[i] >> s[i]) as Field;"),
         "total": v(f"let (c, ok) = total::bitwise::shr_or::<{w}>(a[i] as Field, s[i] as Field); acc += c + ok as Field;")})
add("wshl_u32", "bitwise", "shl_or::<32> vs native << with the amount reduced (s & 31)",
    [("a", "u32", "N"), ("s", "u32", "N")],
    {"native": v("acc += (a[i] << (s[i] & 31)) as Field;"),
     "total": v("let (c, ok) = total::bitwise::shl_or::<32>(a[i] as Field, s[i] as Field); acc += c + ok as Field;")})
add("rotl_u32", "bitwise", "rotate_left_or::<32> vs (a << s) | (a >> (32 - s)) (native asserts at s = 0 or s >= 32)",
    [("a", "u32", "N"), ("s", "u32", "N")],
    {"native": v("acc += ((a[i] << s[i]) | (a[i] >> (32 - s[i]))) as Field;"),
     "total": v("let (c, ok) = total::bitwise::rotate_left_or::<32>(a[i] as Field, s[i] as Field); acc += c + ok as Field;")})

# -------------------------------------------------------------------- ctl
add("select_field", "ctl", "Select::select on Field vs if/else",
    [("c", "bool", "N"), ("t", "Field", "N"), ("f", "Field", "N")],
    {"native": v("acc += if c[i] { t[i] } else { f[i] };"),
     "total": v("acc += Select::select(c[i], t[i], f[i]);")})
add("select_bool", "ctl", "Select::select on bool vs if/else",
    [("c", "bool", "N"), ("t", "bool", "N"), ("f", "bool", "N")],
    {"native": v("acc += (if c[i] { t[i] } else { f[i] }) as Field;"),
     "total": v("acc += Select::select(c[i], t[i], f[i]) as Field;")})
add("select_arr4", "ctl", "Select::select on [Field; 4] vs if/else",
    [("c", "bool", "N"), ("t", "[Field; 4]", "N"), ("f", "[Field; 4]", "N")],
    {"native": v("let r = if c[i] { t[i] } else { f[i] }; acc += r[0] + r[3];"),
     "total": v("let r = Select::select(c[i], t[i], f[i]); acc += r[0] + r[3];")})
add("select_tuple3", "ctl", "Select::select on (Field, Field, Field) vs if/else",
    [("c", "bool", "N"), ("t", "Field", "N"), ("f", "Field", "N")],
    {"native": v("let r = if c[i] { (t[i], f[i], t[i]) } else { (f[i], t[i], f[i]) }; acc += r.0 + r.1 + r.2;"),
     "total": v("let r = Select::select(c[i], (t[i], f[i], t[i]), (f[i], t[i], f[i])); acc += r.0 + r.1 + r.2;")})
add("outcome_require", "ctl", "Outcome::require chain vs assert(flag) (native bricks on a false flag; chains up to 64, longer ones grow slightly superlinearly because the carried code expression grows)",
    [("f", "bool", "N"), ("t", "Field", "N")], ns=[1, 8, 16, 32, 64],
    variants=
    {"native": v("assert(f[i], \"fail\"); acc += t[i];"),
     "total": v("o = o.require(f[i], 7); acc += t[i];", pre="let mut o = Outcome::good();",
                post="acc += (o.ok as Field) + o.code;")})

# ------------------------------------------------------------ collections
for m in (8, 32, 128):
    add(f"index_or_{m}", "collections", f"index_or on [Field; {m}] vs arr[i] (dynamic index, u32 typed)",
        [("arr", "Field", m), ("idx", "u32", "N")],
        {"native": v("acc += arr[idx[i]];"),
         "total": v("let (r, ok) = total::collections::index_or(arr, idx[i] as Field); acc += r + ok as Field;")})
for m in (8, 32):
    add(f"set_or_{m}", "collections", f"set_or on [Field; {m}] (chained writes) vs arr[i] = v",
        [("arr0", "Field", m), ("idx", "u32", "N"), ("val", "Field", "N")],
        {"native": v("arr[idx[i]] = val[i];", pre="let mut arr = arr0;", post="acc += arr[0] + arr[1];"),
         "total": v("let (a2, ok) = total::collections::set_or(arr, idx[i] as Field, val[i]); arr = a2; acc += ok as Field;",
                    pre="let mut arr = arr0;", post="acc += arr[0] + arr[1];")})
add("first_index_of_16", "collections", "first_index_of_or on [Field; 16] vs a native search loop (no flag, assumes presence)",
    [("arr", "Field", 16), ("x", "Field", "N")],
    {"native": v("let mut r: Field = 0; let mut found = false; for j in 0..16 { if (!found) & (arr[j] == x[i]) { r = j as Field; found = true; } } acc += r;"),
     "total": v("let (r, ok) = total::collections::first_index_of_or(arr, x[i]); acc += r + ok as Field;")})

# ------------------------------------------------------------------- hash
for l in (2, 4, 8):
    add(f"p2_fixed_{l}", "hash", f"p2_hash::<{l}> vs noir-lang/poseidon v0.3.0 Poseidon2::hash(x, {l})",
        [("x", f"[Field; {l}]", "N")], ns=[1, 4, 16, 32, 64], dep="poseidon",
        variants={"native": v(f"acc += poseidon::poseidon2::Poseidon2::hash(x[i], {l});"),
         "total": v("acc += total::hash::p2_hash(x[i]);")})
add("p2_sep_4", "hash", "p2_hash_sep::<4> vs noir-lang/poseidon v0.3.0 Poseidon2::hash([sep, x...], 5)",
    [("x", "[Field; 4]", "N"), ("sep", "Field", "N")], ns=[1, 4, 16, 32, 64], dep="poseidon",
    variants={"native": v("acc += poseidon::poseidon2::Poseidon2::hash([sep[i], x[i][0], x[i][1], x[i][2], x[i][3]], 5);"),
     "total": v("acc += total::hash::p2_hash_sep(x[i], sep[i]);")})
for l in (8, 16):
    add(f"p2_var_{l}", "hash", f"p2_hash_var_or::<{l}> (flagged) vs noir-lang/poseidon v0.3.0 Poseidon2::hash(x, len) with len typed u32",
        [("x", f"[Field; {l}]", "N"), ("len", "u32", "N")], ns=[1, 4, 16, 32, 64], dep="poseidon",
        variants={"native": v("acc += poseidon::poseidon2::Poseidon2::hash(x[i], len[i]);"),
         "total": v("let (h, ok) = total::hash::p2_hash_var_or(x[i], len[i] as Field); acc += h + ok as Field;")})
add("p2_sep_var_8", "hash", "p2_hash_sep_var_or::<8> vs noir-lang/poseidon v0.3.0 Poseidon2::hash([sep, x...], len + 1)",
    [("x", "[Field; 8]", "N"), ("len", "u32", "N"), ("sep", "Field", "N")], ns=[1, 4, 16, 32, 64], dep="poseidon",
    variants={"native": v("let mut full = [0; 9]; full[0] = sep[i]; for j in 0..8 { full[j + 1] = x[i][j]; } acc += poseidon::poseidon2::Poseidon2::hash(full, len[i] + 1);"),
     "total": v("let (h, ok) = total::hash::p2_hash_sep_var_or(x[i], len[i] as Field, sep[i]); acc += h + ok as Field;")})

# --------------------------------------------------------------------- ec
EC2 = [("px", "Field", "N"), ("py", "Field", "N"), ("qx", "Field", "N"), ("qy", "Field", "N")]
EP = "EmbeddedCurvePoint::new(px[i], py[i])"
EQ = "EmbeddedCurvePoint::new(qx[i], qy[i])"
TP = "total::ec::Point { x: px[i], y: py[i], inf: false }"
TQ = "total::ec::Point { x: qx[i], y: qy[i], inf: false }"
add("ec_decode", "ec", "decode_xy_or vs a native on-curve assert (y^2 = x^3 - 17)",
    [("px", "Field", "N"), ("py", "Field", "N")],
    {"native": v("assert(py[i] * py[i] == px[i] * px[i] * px[i] - 17); acc += px[i] + py[i];"),
     "total": v("let (p, ok) = total::ec::decode_xy_or(px[i], py[i]); acc += p.x + p.y + ok as Field;")})
add("ec_add", "ec", "ec::add (complete, flag-free) vs embedded_curve_add black box",
    EC2,
    {"native": v(f"let r = embedded_curve_add({EP}, {EQ}); acc += r.x + r.y;"),
     "total": v(f"let r = total::ec::add({TP}, {TQ}); acc += r.x + r.y + r.inf as Field;")})
add("ec_double", "ec", "ec::double vs embedded_curve_add(p, p) black box",
    [("px", "Field", "N"), ("py", "Field", "N")],
    {"native": v(f"let r = embedded_curve_add({EP}, {EP}); acc += r.x + r.y;"),
     "total": v(f"let r = total::ec::double({TP}); acc += r.x + r.y + r.inf as Field;")})
for bits in (64, 254):
    add(f"ec_mul_{bits}", "ec", f"mul_or::<{bits}> (one Field scalar) vs multi_scalar_mul([P],[from_field(s)])",
        [("px", "Field", "N"), ("py", "Field", "N"), ("s", "Field", "N")], ns=[1, 2, 3, 4, 8],
        variants={"native": v(f"let r = multi_scalar_mul([{EP}], [EmbeddedCurveScalar::from_field(s[i])]); acc += r.x + r.y;"),
         "total": v(f"let (r, ok) = total::ec::mul_or::<{bits}>({TP}, s[i]); acc += r.x + r.y + ok as Field;")})
add("ec_mul_limbs", "ec", "mul_limbs_or (two-limb scalar, full range) vs multi_scalar_mul([P],[scalar(lo,hi)])",
    [("px", "Field", "N"), ("py", "Field", "N"), ("lo", "Field", "N"), ("hi", "Field", "N")], ns=[1, 2, 3, 4, 8],
    variants={"native": v(f"let r = multi_scalar_mul([{EP}], [EmbeddedCurveScalar::new(lo[i], hi[i])]); acc += r.x + r.y;"),
     "total": v(f"let (r, ok) = total::ec::mul_limbs_or({TP}, lo[i], hi[i]); acc += r.x + r.y + ok as Field;")})
add("ec_msm_1", "ec", "msm_or::<1> (guarded) vs multi_scalar_mul with 1 term",
    [("px", "Field", "N"), ("py", "Field", "N"), ("lo", "[Field; 1]", "N"), ("hi", "[Field; 1]", "N")], ns=[1, 2, 3, 4, 8],
    variants={"native": v(f"let r = multi_scalar_mul([{EP}], [EmbeddedCurveScalar::new(lo[i][0], hi[i][0])]); acc += r.x + r.y;"),
     "total": v(f"let (r, ok) = total::ec::msm_or([{TP}], lo[i], hi[i]); acc += r.x + r.y + ok as Field;")})
add("ec_msm_2", "ec", "msm_or::<2> (guarded) vs multi_scalar_mul with 2 terms",
    [("px", "Field", "N"), ("py", "Field", "N"), ("qx", "Field", "N"), ("qy", "Field", "N"),
     ("lo", "[Field; 2]", "N"), ("hi", "[Field; 2]", "N")], ns=[1, 2, 3, 4, 8],
    variants={"native": v(f"let r = multi_scalar_mul([{EP}, {EQ}], [EmbeddedCurveScalar::new(lo[i][0], hi[i][0]), EmbeddedCurveScalar::new(lo[i][1], hi[i][1])]); acc += r.x + r.y;"),
     "total": v(f"let (r, ok) = total::ec::msm_or([{TP}, {TQ}], lo[i], hi[i]); acc += r.x + r.y + ok as Field;")})

# ----------------------------------------------------------------- encode
add("enc_chunk_le", "encode", "chunk_to_le_bytes_or (31 bytes) vs std to_le_bytes::<31>",
    [("x", "Field", "N")], ns=[1, 8, 16, 32, 64],
    variants={"native": v("let b: [u8; 31] = x[i].to_le_bytes(); acc += (b[0] as Field) + (b[30] as Field);"),
     "total": v("let (b, ok) = total::encode::chunk_to_le_bytes_or(x[i]); acc += (b[0] as Field) + (b[30] as Field) + ok as Field;")})
for t, w, nb in (("u32", 32, 4), ("u64", 64, 8), ("u128", 128, 16)):
    add(f"enc_{t}_to_be", "encode", f"{t}_to_be_bytes vs (x as Field).to_be_bytes::<{nb}>()",
        [("a", t, "N")],
        {"native": v(f"let b: [u8; {nb}] = (a[i] as Field).to_be_bytes(); acc += (b[0] as Field) + (b[{nb-1}] as Field);"),
         "total": v(f"let b = total::encode::{t}_to_be_bytes(a[i]); acc += (b[0] as Field) + (b[{nb-1}] as Field);")})
    shifts = " | ".join(f"((b[i][{j}] as {t}) << {8*(nb-1-j)})" for j in range(nb))
    add(f"enc_{t}_from_be", "encode", f"{t}_from_be_bytes vs a manual shift-or on bytes",
        [("b", f"[u8; {nb}]", "N")], ns=[1, 8, 16, 32, 64], ns_native=[64, 256, 1024, 2048],
        variants={"native": v(f"acc += ({shifts}) as Field;"),
         "total": v(f"acc += total::encode::{t}_from_be_bytes(b[i]) as Field;")})
add("enc_canon_le_bytes", "encode", "canonical_le_bytes_flag (32 bytes) vs a plain byte accumulate (no canonicity check)",
    [("b", "[u8; 32]", "N")], ns=[1, 4, 16, 32, 64],
    variants={"native": v("let mut r: Field = 0; for j in 0..32 { r = r * 256 + (b[i][31 - j] as Field); } acc += r;"),
     "total": v("let mut r: Field = 0; for j in 0..32 { r = r * 256 + (b[i][31 - j] as Field); } acc += r + total::encode::canonical_le_bytes_flag(b[i]) as Field;")})

# -------------------------------------------------------------------- sig
add("schnorr", "sig", "schnorr_verify vs raw noir-lang/schnorr verify_signature",
    [("px", "Field", "N"), ("py", "Field", "N"), ("sig", "[Field; 4]", "N"), ("msg", "Field", "N")],
    ns=[1, 2, 3, 4, 8], dep="schnorr",
    variants={"native": v("acc += schnorr::verify_signature(EmbeddedCurvePoint::new(px[i], py[i]), (EmbeddedCurveScalar::new(sig[i][0], sig[i][1]), EmbeddedCurveScalar::new(sig[i][2], sig[i][3])), msg[i]) as Field;"),
              "total": v("acc += total::schnorr::schnorr_verify(px[i], py[i], sig[i], msg[i]) as Field;")})
for curve, mod in (("k1", "ecdsa_secp256k1"), ("r1", "ecdsa_secp256r1")):
    add(f"ecdsa_{curve}", "sig", f"ecdsa_{curve}_verify vs std {mod}::verify_signature",
        [("px", "[u8; 32]", "N"), ("py", "[u8; 32]", "N"), ("sig", "[u8; 64]", "N"), ("h", "[u8; 32]", "N")],
        ns=[1, 2, 3, 4],
        variants={"native": v(f"acc += std::{mod}::verify_signature(px[i], py[i], sig[i], h[i]) as Field;"),
                  "total": v(f"acc += total::ecdsa::ecdsa_{curve}_verify(px[i], py[i], sig[i], h[i]) as Field;")})



NOTES = """## Reading the tables: where totality costs, and why

Rows with ratio above 2 (and the reason), then the cases where the total form is cheaper than the native one.

**Flag forms of range checks (`fits_bits`, `clamp_bits_or`, `to_*_or`, `bool_or`, `cmp_bits`).** The native `assert_max_bit_size` is one RANGE opcode (1 to 7 gates). A flag cannot be a failing constraint, so `fits_bits::<N>` decomposes the value into canonical 128-bit limbs (hinted, range-checked, plus a borrow compare against the modulus limbs, four 128-bit RANGEs), splits the low limb at bit N and runs two `is_zero` gadgets: about 42 gates for any N below 128 and about 33 at 128. The cost is flat in N, so the ratio is large for narrow widths (27x at 8 bits) and small for wide ones (4.8x at 128 bits). Against a silent `as uN` cast, which is itself about 28 gates (it must decompose to truncate), `to_uN_or` is only 1.6x.

**Field-domain arithmetic and bit ops (`add_or::<64>`, `and_bits_or`, `or_bits_or`, `xor_bits_or`, `not_bits_or`, `shl_exact_or`, `shr_or`, `cmp_bits`).** These take `Field` operands and so first clamp each operand with `clamp_bits_or`, two flag gadgets at about 42 gates each. That is the 9x of `add_or::<64>` against native u64 `+`. When the operands are already typed (`u64`, `u32`, ...) use the facades (`add_or`, `sub_or`, `mul_or`, `div_or`, `mod_or`, `Saturating`), which skip the clamps: 1.1 to 1.7x at 8..64 bits. The native `&`, `|`, `^` are total already, so use them on typed operands. The shifts at 32 and 64 bits also clamp the shift amount and split it into log2 N bits (widths up to 16 scan the candidate amounts with one `eq` gadget each instead), about 110 gates per shift.

**`mul_or` and `div_or` on u128** (2.1x and 1.8x) pay for a double-width product and a 128-bit Euclidean-division constraint set.

**Fused multiply-divide (`TotalMulDiv`, `mul_div_or`).** floor(a*b/d) where a*b needs double width. The typed facade on u64 is 34 gates per operation: 0.51x of the native asserting `(a as u128 * b as u128) / d` (66) and 0.22x of the u128 facades `mul_or` then `div_or` (155), which pay for 128-bit generality twice (a limb schoolbook for the product and a second one to check quotient times divisor). The fused gadget checks one identity a*b == q*d + r in the field, with four 64-bit RANGEs (quotient halves, remainder, divisor minus remainder) and two `is_zero` gadgets. The Field-domain `mul_div_or::<64>` adds three input clamps (about 42 gates each) on top, so prefer the facade whenever the operands are typed. Past 84 bits the wide gadget (`mul_div_wide_or`, `TotalMulDiv` on u128) adds a check that a*b - q*d - r vanishes mod 2^128 (one carry RANGE) to the field identity. The u128 facade is 103 gates per operation: 1.26x the native asserting u128 `a * b / d` (82), which fails whenever a*b >= 2^128 and so cannot express the operation, and 0.63x the u128 facades `mul_or` then `div_or` (165). In the Field domain the unsplit layout (N <= 124) costs about 13 gates over `mul_div_or::<84>` (168.8 at N = 96, 172.3 at 124 against 155.5); from N = 125 the operands and the quotient limbs are split at bit 64 and a second carry is checked (206.3 at 125; 177.3 at 128, whose input clamps are `clamp_128`, one split cheaper per operand). `mul_div_wide_to_or::<135>` adds a split of the high quotient limb and an `is_zero`: 187.8.

**Array helpers.** `index_or` and `set_or` are eq-scans with no memory ops: cost is linear in the array length, 6 to 8 gates per element for `index_or` (47 at length 8, 223 at 32, 1024 at 128) and 3.4 to 4.6 per element for `set_or`, against 1.3 gates for a native dynamic read, which is a ROM lookup plus a bounds assert. For long arrays prefer a bounded index obtained once and used with a native read behind a flag you verify yourself, or restructure to avoid witness indices.

**`Outcome::require`** (about 9 gates per check, 6.7x a bare `assert`) carries the first-failure code: a bool product and one Field select.

**EC scalar multiplication.** `mul_or` and `mul_limbs_or` are an in-circuit ladder (a double, an add and a select per bit, 90 to 97 gates per bit): 5.8k gates at 64 bits and 25k at 254 bits per multiplication, 7x and 31x the std MSM black box for one term (770 to 790 gates). `msm_or::<1>` and `msm_or::<2>` wrap that black box behind validation and blinding (two more black-box terms, a correction-scalar check and N + 1 complete adds, so that every input has a proof) and cost 2.47x and 2.01x, about 1.1k gates more per call. Use `msm_or` unless the ladder's independence from the MSM opcode is required. `decode_xy_or` is 3.5x a bare on-curve assert (13 against 3.7 gates, tiny in absolute terms).

**Encoding.** `canonical_le_bytes_flag` and `from_le_bytes_or` add a canonical (below p) compare to a plain byte accumulate: 2.1x, about 57 extra gates. `to_le_bytes_or::<8>` is 4.1x of the native decomposition and `chunk_to_le_bytes_or` 1.7x.

**Conversions between integer types (`TotalNarrow`).** 1.3 to 2.7x, a few gates in absolute terms.

**Cheaper than the native form.** Field `lt`, `lte`, `min`: 0.45x of `std::field::bn254::lt` (83 against 182 gates). `to_le_bytes_total` and `to_le_bits_total`: 0.2x and 0.3x of the std decompositions. Saturating arithmetic is 0.3 to 0.65x of std `wrapping_*` on the same types (the native wrapping forms are surprisingly expensive: they decompose). `ec::add` (27 gates) and `ec::double` (13) are 0.42x and 0.21x of the `embedded_curve_add` black box (65 and 62 gates). `pow_or`, `first_index_of_or`, the variable-length Poseidon2 forms (0.7 to 0.95x of the library's variable-length hash), signed `neg_or` and `abs_or`, and the `uN_from_be_bytes` helpers are also at or below native. Fixed-length Poseidon2 (`p2_hash`, `p2_hash_sep`) is identical to the library call (it is the same permutation black box), and `lt` and friends on typed operands are identical to native `<`.

**Fixed costs.** UltraHonk builds its range and lookup tables once per circuit: about 2.7k gates once any 16-bit-or-wider RANGE appears, about 3.4k once 32-bit ranges appear, about 4.1k for the byte-wide AND/XOR tables. Every circuit that range-checks a u64 already pays the same table the total forms use, so the `fixed` and `dA` columns mostly read as 0 once a typed operand is in the circuit; a circuit that avoids all wide ranges and uses a flag form pays the table once (dA about +2.7k). Rows with a dagger sit partly on such a floor at small N.
"""

# ---------------------------------------------------------------- engine
def disk_used():
    st = shutil.disk_usage(os.path.expanduser("~"))
    return st.used


PEAK = {"used": 0, "start": 0}


def sample_disk():
    u = disk_used()
    PEAK["used"] = max(PEAK["used"], u)


def gen_source(b, variant, n):
    pre, op, post = b.variants[variant]
    ps = []
    for name, ty, size in b.params:
        if size is None:
            ps.append(f"{name}: {ty}")
        else:
            sz = eval(str(size), {"N": n}) if isinstance(size, str) else size
            ps.append(f"{name}: [{ty}; {sz}]")
    return (PRELUDE + f"fn main({', '.join(ps)}) -> pub Field {{\n    let mut acc: Field = 0;\n    {pre}\n"
            f"    for i in 0..{n} {{\n        {op}\n    }}\n    {post}\n    acc\n}}\n")


def build_one(b, variant, n, gdir):
    name = f"{b.id}_{variant}_{n}"
    pkg = os.path.join(gdir, name)
    os.makedirs(os.path.join(pkg, "src"))
    deps = f'total = {{ path = "{BUILD}/lib/total" }}\n'
    if b.dep == "poseidon":
        deps += 'poseidon = { tag = "v0.3.0", git = "https://github.com/noir-lang/poseidon" }\n'
    if b.dep == "schnorr":
        deps += 'schnorr = { tag = "v0.4.0", git = "https://github.com/noir-lang/schnorr" }\n'
    with open(os.path.join(pkg, "Nargo.toml"), "w") as f:
        f.write(f'[package]\nname = "{b.id}_{variant}_{n}"\ntype = "bin"\ncompiler_version = ">=1.0.0"\n\n[dependencies]\n{deps}')
    with open(os.path.join(pkg, "src", "main.nr"), "w") as f:
        f.write(gen_source(b, variant, n))
    env = dict(os.environ, HARDWARE_CONCURRENCY="2")
    res = {"bench": b.id, "variant": variant, "n": n}
    try:
        for attempt in range(3):  # nargo can fail transiently on its git-cache lock
            t0 = time.time()
            p = subprocess.run(["nice", "-n", "19", NARGO, "compile", "--force", "--silence-warnings"], cwd=pkg,
                               capture_output=True, text=True, env=env, timeout=3600)
            if p.returncode == 0 or "error:" in (p.stderr + p.stdout):
                break
            time.sleep(5)
        res["compile_s"] = round(time.time() - t0, 2)
        if p.returncode != 0:
            res["error"] = ("nargo: " + (p.stderr + p.stdout))[-1500:]
            return res
        art = os.path.join(pkg, "target", f"{name}.json")
        p = subprocess.run(["nice", "-n", "19", BB, "gates", "-b", art], capture_output=True, text=True, env=env, timeout=3600)
        if p.returncode != 0:
            res["error"] = ("bb: " + (p.stderr + p.stdout))[-1500:]
            return res
        m = re.search(r'\{.*\}', p.stdout, re.S)
        fn = json.loads(m.group(0))["functions"][0]
        res["gates"] = fn["circuit_size"]
        res["acir"] = fn["acir_opcodes"]
        sample_disk()
    except Exception as e:  # noqa
        res["error"] = repr(e)
    finally:
        shutil.rmtree(pkg, ignore_errors=True)  # prune immediately
    return res


def fit(ns, ys, tol_abs=3.0, tol_rel=0.003):
    """Least squares gates = a + b*N on the longest tail of the points
    that is linear. A circuit's size jumps at small N when a fixed lookup
    or range table first appears (or sits as a floor under the gates), so
    the smallest N are dropped, one at a time, until the maximum residual is
    within max(tol_abs, tol_rel*gates) or two points remain. Returns
    (a, b, maxres, ns_used)."""
    pts = list(zip(ns, ys))
    while True:
        k = len(pts)
        xs, zs = [p[0] for p in pts], [p[1] for p in pts]
        mx, my = sum(xs) / k, sum(zs) / k
        sxx = sum((x - mx) ** 2 for x in xs)
        b = sum((x - mx) * (z - my) for x, z in zip(xs, zs)) / sxx
        a = my - b * mx
        resid = max(abs(z - (a + b * x)) for x, z in zip(xs, zs))
        if k <= 2 or resid <= max(tol_abs, tol_rel * max(zs)):
            return a, b, resid, xs
        pts = pts[1:]


def seed_unselected(cache, groups_sel, only_sel):
    path = RAW_JSON
    if not os.path.exists(path):
        return
    selected = {b.id for b in BENCHES
                if (not groups_sel or b.group in groups_sel)
                and (not only_sel or any(b.id.startswith(o) for o in only_sel))}
    seeded = 0
    for rec in json.load(open(path))["benchmarks"]:
        if rec["id"] in selected:
            continue
        for var, vv in rec["variants"].items():
            for pt in vv.get("points", []):
                key = f"{rec['id']}|{var}|{pt['n']}"
                if key not in cache:
                    cache[key] = {"bench": rec["id"], "variant": var, "n": pt["n"], "gates": pt["gates"],
                                  "acir": pt["acir"], "compile_s": pt["compile_s"]}
                    seeded += 1
    print(f"kept {seeded} recorded points of unselected benchmarks from {path}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", default="")
    ap.add_argument("--smoke", action="store_true", help="N=2 only, report compile errors, write nothing")
    ap.add_argument("--workers", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--only", default="", help="comma-separated bench ids (prefix match)")
    ap.add_argument("--fresh", action="store_true")
    ap.add_argument("--keep-build", action="store_true")
    args = ap.parse_args()

    os.makedirs(BUILD, exist_ok=True)
    cache_path = os.path.join(BUILD, "results.json")
    cache = {} if args.fresh or not os.path.exists(cache_path) else json.load(open(cache_path))
    groups_sel = [g for g in args.groups.split(",") if g]
    only_sel = [o for o in args.only.split(",") if o]
    if groups_sel or only_sel:
        # A partial run rewrites the whole report, so the benchmarks it does
        # not select keep their recorded points from the current JSON
        # instead of disappearing; the selected ones are measured afresh.
        seed_unselected(cache, groups_sel, only_sel)
    # snapshot the libraries so a concurrent edit cannot change a run
    libdir = os.path.join(BUILD, "lib")
    shutil.rmtree(libdir, ignore_errors=True)
    shutil.copytree(os.path.join(REPO, "noir", "total"), os.path.join(libdir, "total"),
                    ignore=shutil.ignore_patterns("target"))

    groups = []
    for b in BENCHES:
        if b.group not in groups:
            groups.append(b.group)
    if args.groups:
        groups = [g for g in groups if g in args.groups.split(",")]
    only = [s for s in args.only.split(",") if s]

    PEAK["start"] = disk_used()
    PEAK["used"] = PEAK["start"]
    disk_log = []
    ver = subprocess.run([NARGO, "--version"], capture_output=True, text=True).stdout.splitlines()[0]
    bbv = subprocess.run([BB, "--version"], capture_output=True, text=True).stdout.strip()

    for g in groups:
        sample_disk()
        disk_log.append((g, "before", disk_used()))
        gdir = os.path.join(BUILD, "g_" + g)
        shutil.rmtree(gdir, ignore_errors=True)
        os.makedirs(gdir)
        tasks = []
        for b in BENCHES:
            if b.group != g or (only and not any(b.id.startswith(o) for o in only)):
                continue
            for var in b.variants:
                for n in ([2] if args.smoke else b.ns_for(var)):
                    key = f"{b.id}|{var}|{n}"
                    if not args.smoke and key in cache and "gates" in cache[key]:
                        continue
                    tasks.append((key, b, var, n))
        print(f"[{g}] {len(tasks)} packages", flush=True)
        # biggest N first for better load balance
        tasks.sort(key=lambda t: -t[3])
        with ThreadPoolExecutor(args.workers) as ex:
            futs = {ex.submit(build_one, b, var, n, gdir): key for key, b, var, n in tasks}
            done = 0
            for f in as_completed(futs):
                r = f.result()
                done += 1
                if args.smoke:
                    if "error" in r:
                        print(f"  FAIL {futs[f]}: {r['error'][:700]}", flush=True)
                    else:
                        print(f"  ok   {futs[f]} gates={r['gates']} acir={r['acir']}", flush=True)
                else:
                    cache[futs[f]] = r
                    if "error" in r:
                        print(f"  FAIL {futs[f]}: {r['error'][:300]}", flush=True)
                    if done % 20 == 0:
                        json.dump(cache, open(cache_path, "w"))
                        print(f"  {done}/{len(tasks)}", flush=True)
        shutil.rmtree(gdir, ignore_errors=True)
        if not args.smoke:
            json.dump(cache, open(cache_path, "w"))
        sample_disk()
        disk_log.append((g, "after", disk_used()))
        print(f"[{g}] done; disk used {disk_used()/2**30:.2f} GiB (peak {PEAK['used']/2**30:.2f}, start {PEAK['start']/2**30:.2f})", flush=True)
    if args.smoke:
        return

    write_reports(cache, ver, bbv, disk_log)
    if not args.keep_build:
        shutil.rmtree(BUILD, ignore_errors=True)
        try:
            os.rmdir(os.path.dirname(BUILD))
        except OSError:
            pass
    print("peak extra disk over start: %.3f GiB" % ((PEAK["used"] - PEAK["start"]) / 2**30))


def write_reports(cache, ver, bbv, disk_log):
    rows = []
    for b in BENCHES:
        rec = {"id": b.id, "group": b.group, "title": b.title, "ns": b.ns, "variants": {}}
        for var in b.variants:
            pts = [cache.get(f"{b.id}|{var}|{n}") for n in b.ns_for(var)]
            pts = [p for p in pts if p and "gates" in p]
            if len(pts) < 2:
                rec["variants"][var] = {"error": "; ".join(sorted({p.get('error', '')[:200] for p in
                                         [cache.get(f"{b.id}|{var}|{n}", {}) for n in b.ns_for(var)] if p.get('error')})) or "no data"}
                continue
            ns = [p["n"] for p in pts]
            a, bb_, r, used = fit(ns, [p["gates"] for p in pts])
            ao, bo, ro, _ = fit(ns, [p["acir"] for p in pts], 0.5, 0.0)
            rec["variants"][var] = {
                "points": [{"n": p["n"], "gates": p["gates"], "acir": p["acir"], "compile_s": p["compile_s"]} for p in pts],
                "gates_fixed": round(a, 1), "gates_per_op": round(bb_, 2), "gates_max_residual": round(r, 1),
                "fit_ns": used, "tail_fit": len(used) < len(ns),
                "acir_fixed": round(ao, 1), "acir_per_op": round(bo, 2),
                "compile_s_max_n": pts[-1]["compile_s"]}
        rows.append(rec)
    sinks = {r["id"]: r["variants"]["native"] for r in rows if r["group"] == "baseline" and "per_op" in json.dumps(r["variants"]["native"])}
    out = {"toolchain": {"nargo": ver, "bb": bbv},
           "method": "gates(N) = a + b*N least-squares over the listed N; b = per-op gates, a = fixed. "
                     "Every package applies the op N times over N distinct input elements and sums the results "
                     "(and flags) into one public Field output.",
           "disk": {"start_bytes": PEAK["start"], "peak_bytes": PEAK["used"],
                    "peak_extra_gib": round((PEAK["used"] - PEAK["start"]) / 2**30, 3),
                    "per_group": [{"group": g, "when": w, "used_gib": round(u / 2**30, 2)} for g, w, u in disk_log]},
           "benchmarks": rows}
    os.makedirs(os.path.dirname(RAW_JSON), exist_ok=True)
    json.dump(out, open(RAW_JSON, "w"), indent=1)
    open(os.path.join(DOCS, "gate-costs.md"), "w").write(render_md(out))


GROUP_TITLES = {
    "baseline": "Baseline: the accumulator sink alone",
    "range": "Range flags",
    "cmp": "Comparison",
    "convert": "Casts and conversions",
    "arith": "Unsigned and Field arithmetic",
    "muldiv": "Fused multiply-divide",
    "signed": "Signed arithmetic",
    "bitwise": "Shifts and bitwise",
    "ctl": "Select and Outcome",
    "collections": "Array helpers",
    "hash": "Poseidon2",
    "ec": "Grumpkin EC",
    "encode": "Encoding helpers",
    "sig": "Signatures",
}


def fnum(x, d=1):
    if x is None:
        return "-"
    s = f"{x:.{d}f}"
    return s.rstrip("0").rstrip(".") if "." in s else s


def render_md(out):
    L = []
    L.append("# Gate costs of the total primitives against their native forms\n")
    L.append(f"Generated by `scripts/gate-bench.sh` (`scripts/gate_bench.py`). Toolchain: {out['toolchain']['nargo'].replace('nargo version = ', 'nargo ')}, bb {out['toolchain']['bb']}. "
             "Raw points: build/gate-costs.json after a run of scripts/gate-bench.sh.\n")
    L.append("## Method\n")
    L.append("Each row compares one total entry against the native Noir operation it replaces. For each side the "
             "script generates a package whose `main` applies the operation N times over N distinct input elements "
             "(array parameters, so nothing constant-folds or deduplicates) and sums every result, and every flag, "
             "into one public `Field` output. Packages are compiled with nargo and measured with `bb gates` "
             "(UltraHonk `circuit_size`, plus ACIR opcode count) at several N, and `gates(N) = a + b*N` is "
             "fitted by least squares. **b is the per-operation cost; a is the fixed cost** (lookup tables, "
             "constants, the output). A single-call count would mix the two: range checks and lookups build "
             "tables once per circuit, so a lone op reports mostly `a`.\n")
    L.append("- Typed operands (`u64`, `i32`, `bool`, ...) are `main` parameters on both sides, so their entry "
             "range checks are identical and cancel; the total side converts with `as Field` (free). "
             "Field-domain entries take `Field` parameters on both sides.\n"
             "- \"native\" is the closest honest native form; the title of each row says what it is. Where "
             "there are two natives (silent cast and checked cast, asserting `+` and `wrapping_add`) both are "
             "shown. Native `+ - * / %` and `assert_max_bit_size` are unsatisfiable on bad input: the gate cost "
             "is what an author pays for the unsafe form, the total form buys totality.\n"
             "- The sink (`acc += value`, `acc += flag`) is in every measurement and costs about "
             "`SINK1` gates per term, see the baseline table. Per-op values are gross of it; the total side "
             "carries one extra term for its flag.\n"
             "- Gates are bb 6.0.0 UltraHonk gates, not proving time. `ratio` is b_total / b_native "
             "(`-` where the native per-op cost is below 0.5 gate, so the ratio is meaningless). "
             "`dA` is a_total - a_native: fixed cost the total form adds (or saves) once per circuit. "
             "A dagger marks rows where the smallest N were dropped from the fit: UltraHonk's lookup and range "
             "tables appear as a one-off step (or as a floor under a small circuit) at some N, so the "
             "slope is taken on the linear tail and `fixed` is that tail's intercept, i.e. the cost at N = 0 "
             "once the tables the operation needs exist. The raw points are in the JSON (`points`, `fit_ns`). "
             "`maxres` is the largest deviation of any measured point from the fitted line; "
             "a value near 0 means the cost really is linear in N.\n")
    L.append("Lookup and range tables (UltraHonk): range checks of any width up to 14 bits and the "
             "byte-wide AND/XOR/decomposition tables are built once per circuit from shared tables, "
             "so every primitive that range checks or masks shares them with the native form; the "
             "difference between native and total in column `dA` is the extra tables or constants the "
             "total form needs. Primitives with no lookups (field arithmetic, select) show a fixed cost "
             "of only the constants.\n")
    sink1 = None
    for r in out["benchmarks"]:
        if r["id"] == "sink1" and "gates_per_op" in r["variants"]["native"]:
            sink1 = r["variants"]["native"]["gates_per_op"]
    for g in dict.fromkeys(r["group"] for r in out["benchmarks"]):
        L.append(f"## {GROUP_TITLES.get(g, g)}\n")
        if g == "baseline":
            L.append("| bench | gates/op | gates fixed | ACIR/op |\n|---|---|---|---|")
            for r in out["benchmarks"]:
                if r["group"] != g:
                    continue
                n = r["variants"]["native"]
                L.append(f"| {r['title']} | {fnum(n.get('gates_per_op'),2)} | {fnum(n.get('gates_fixed'))} | {fnum(n.get('acir_per_op'),2)} |")
            L.append("")
            continue
        L.append("| entry (and what it is compared with) | native gates/op | total gates/op | ratio | native fixed | total fixed | dA | native ACIR/op | total ACIR/op | maxres (n/t) |")
        L.append("|---|---|---|---|---|---|---|---|---|---|")
        for r in out["benchmarks"]:
            if r["group"] != g:
                continue
            vs = r["variants"]
            nat = [k for k in vs if k.startswith("native")]
            tot = vs.get("total", {})
            if not nat:
                nat = [None]
            for k in nat:
                nv = vs.get(k, {}) if k else {}
                label = r["title"] + (f" [{k.replace('native_','')}]" if k and k != "native" and len(nat) > 1 else "")
                if (nv.get("tail_fit") if nv else False) or tot.get("tail_fit"):
                    label += " \u2020"
                if "gates_per_op" not in tot:
                    L.append(f"| {label} | - | FAILED | | | | | | | |")
                    continue
                if k is None or "gates_per_op" not in nv:
                    L.append(f"| {label} | - | {fnum(tot['gates_per_op'])} | - | - | {fnum(tot['gates_fixed'])} | - | - | {fnum(tot['acir_per_op'])} | -/{fnum(tot['gates_max_residual'])} |")
                    continue
                nb, tb = nv["gates_per_op"], tot["gates_per_op"]
                ratio = f"{tb/nb:.2f}x" if nb >= 0.5 else "-"
                L.append(f"| {label} | {fnum(nb,2)} | {fnum(tb,2)} | {ratio} | {fnum(nv['gates_fixed'])} | {fnum(tot['gates_fixed'])} | {fnum(tot['gates_fixed']-nv['gates_fixed'])} | {fnum(nv['acir_per_op'],2)} | {fnum(tot['acir_per_op'],2)} | {fnum(nv['gates_max_residual'])}/{fnum(tot['gates_max_residual'])} |")
        L.append("")
    L.append(NOTES)
    L.append("## Compile time\n")
    slow = []
    for r in out["benchmarks"]:
        for k, vv in r["variants"].items():
            if vv.get("compile_s_max_n", 0) >= 10:
                slow.append((r["id"], k, vv["points"][-1]["n"], vv["compile_s_max_n"]))
    if slow:
        L.append("nargo compile wall time at the largest N (up to 32 packages compile concurrently at nice 19, so these are upper bounds); only those of 10 s or more:\n")
        L.append("| bench | variant | N | seconds |\n|---|---|---|---|")
        for s in sorted(slow, key=lambda s: -s[3]):
            L.append(f"| {s[0]} | {s[1]} | {s[2]} | {s[3]} |")
    else:
        L.append("Every benchmark compiled in under 10 s at its largest N (full per-point times are in the JSON).")
    L.append("")
    L.append("## Disk\n")
    d = out["disk"]
    ran = list(dict.fromkeys(x["group"] for x in d["per_group"]))
    scope = "" if set(ran) >= {r["group"] for r in out["benchmarks"]} else f" (the last run measured only: {', '.join(ran)}; the other rows keep their recorded points)"
    L.append(f"Packages were deleted as soon as they were measured and one group at a time; peak extra disk use over the start of the run: {d['peak_extra_gib']} GiB{scope}.\n")
    return "\n".join(L).replace("`SINK1`", fnum(sink1, 2) if sink1 is not None else "?")


if __name__ == "__main__":
    main()
