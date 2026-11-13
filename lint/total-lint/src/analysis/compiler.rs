//! The compiler's own hint directives, and the constraints on their outputs
//! that hold for every input when the hints are honest (`hint-compiler`).
//!
//! nargo 1.0.0-rc.3 lowers ordinary total operations through three Brillig
//! directives it generates itself, with no source location:
//!
//! - `directive_invert` (`==`, `!=` as a value, casts, comparisons):
//!   z = 1/E, or 0 when E = 0.
//! - `directive_integer_quotient` (casts, `&`, `/` and `%` by constants,
//!   integer comparisons): (q, r) = (a div b, a mod b) on the canonical
//!   integer value of a.
//! - `directive_to_radix` (`to_le_bytes`, `to_le_bits` and friends): the
//!   first n base-`radix` digits of x's canonical value.
//!
//! A directive is recognised only when its Brillig bytecode is exactly the
//! rc.3 compiler's (a user function of the same name is not), the call's
//! predicate is a nonzero constant (so the call always runs), its inputs are
//! linear expressions over assigned witnesses, and the parameters below that
//! the argument needs (the divisor, the radix, the limb count) are constants.
//!
//! Given the honest outputs, a constraint is `hint-compiler` when one of
//! these holds; each is a statement about integers below the field modulus
//! p, so it holds in the field too:
//!
//! - is-zero: `E*y = 0` (any nonzero multiple) where `y = 1 - E*z` was
//!   defined from z = invert(E). If E = 0 the product is 0; otherwise
//!   z = 1/E, y = 0. y is 0 or 1, and 1 exactly when E = 0.
//! - integer quotient: `r + b*q - a = 0` for (q, r) = quotient(a, b), b a
//!   nonzero constant: the definition of integer division. Also r < b, and
//!   q <= floor(amax / b) where amax bounds a's canonical value (p - 1 when
//!   nothing tighter is known).
//! - radix: `sum(radix^i * d_i) - x = 0` for digits d of x, when radix^n
//!   exceeds every value x can take: p - 1 at full width, or a bound on x
//!   from earlier range checks. Every digit is below the radix.
//! - range: a RANGE on a witness, or an assertion, whose value interval,
//!   computed from the facts above (and bounds that earlier opcodes
//!   establish), lies in [0, 2^bits) or is exactly {0}. Values are tracked
//!   as integer intervals through linear and bilinear definitions with
//!   small signed coefficients; a result outside [0, p) is not used.
//! - booleanity: `x*x - x = 0` when x's honest value lies in [0, 1] by the
//!   facts above and earlier opcodes (an is-zero flag, a binary digit, a
//!   definition over them whose interval is that tight), or when x is
//!   0 or 1 for every 0/1 value of the bits its definition is built from
//!   (exclusive or). The bound the assertion itself teaches later opcodes
//!   is never its evidence: a hint, or a hint selected through a compiler
//!   comparison, stays hint-class (aztec-nr's `Packable for bool` unpack
//!   asserts this on a field read from storage, which can hold 2).
//! - truncation check: an expression `y * X` with y an is-zero flag of
//!   `c - q` (q a quotient output): when y = 0 it is 0; when y = 1, q = c
//!   and the remainder of the same quotient is at most amax - c*b, which
//!   bounds X. This is the canonical-decomposition check the compiler
//!   emits after truncating a Field to an integer type.
//!
//! Anything else touching these outputs stays hint-class. In particular
//! the byte-by-byte comparison with the modulus after a full-width
//! `to_le_bytes` and the decomposition inside `Field::lt` are total only by
//! a global argument the lint does not make.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::OnceLock;

use acir::brillig::Opcode as BOp;
use acir::circuit::Program;
use acir::circuit::brillig::{BrilligInputs, BrilligOutputs};
use acir::native_types::Expression;
use acir::{AcirField, FieldElement};
use num_bigint::{BigInt, BigUint, Sign};

use super::{FnAnalyser, Norm, normalise, wname};

/// A Brillig function the compiler generates itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Directive {
    Invert,
    IntegerQuotient,
    ToRadix,
}

impl Directive {
    fn name(self) -> &'static str {
        match self {
            Directive::Invert => "directive_invert",
            Directive::IntegerQuotient => "directive_integer_quotient",
            Directive::ToRadix => "directive_to_radix",
        }
    }

    /// The bytecode nargo 1.0.0-rc.3 emits, one opcode per line as the
    /// Brillig opcode's Display prints it.
    fn bytecode(self) -> &'static [&'static str] {
        match self {
            Directive::Invert => &[
                "@21 = const u32 1",
                "@20 = const u32 0",
                "@0 = calldata copy [@20; @21]",
                "@2 = const field 0",
                "@3 = field eq @0, @2",
                "jump if @3 to 8",
                "@1 = const field 1",
                "@0 = field field_div @1, @0",
                "stop @[@20; @21]",
            ],
            Directive::IntegerQuotient => &[
                "@10 = const u32 2",
                "@11 = const u32 0",
                "@0 = calldata copy [@11; @10]",
                "@2 = field int_div @0, @1",
                "@1 = field mul @2, @1",
                "@1 = field sub @0, @1",
                "@0 = @2",
                "stop @[@11; @10]",
            ],
            Directive::ToRadix => &[
                "@5 = const u32 0",
                "@6 = const u32 1",
                "@7 = const u32 3",
                "@0 = calldata copy [@5; @7]",
                "@1 = cast @1 to u32",
                "@9 = const u32 10",
                "@7 = u32 add @9, @1",
                "@3 = field int_div @0, @2",
                "@4 = field mul @3, @2",
                "@4 = field sub @0, @4",
                "store @4 at @9",
                "@9 = u32 add @9, @6",
                "@0 = @3",
                "@8 = u32 lt @9, @7",
                "jump if @8 to 7",
                "@9 = const u32 10",
                "stop @[@9; @1]",
            ],
        }
    }

    const ALL: [Directive; 3] = [
        Directive::Invert,
        Directive::IntegerQuotient,
        Directive::ToRadix,
    ];

    /// The directive this Brillig function is, by name and exact bytecode.
    pub fn recognise(name: &str, code: &[BOp<FieldElement>]) -> Option<Directive> {
        Directive::ALL.into_iter().find(|d| {
            d.name() == name
                && d.bytecode().len() == code.len()
                && d.bytecode()
                    .iter()
                    .zip(code)
                    .all(|(want, op)| op.to_string() == *want)
        })
    }
}

/// The program's Brillig functions that are compiler directives.
pub fn directives(program: &Program<FieldElement>) -> BTreeMap<u32, Directive> {
    program
        .unconstrained_functions
        .iter()
        .enumerate()
        .filter_map(|(i, f)| {
            Directive::recognise(&f.function_name, &f.bytecode).map(|d| (i as u32, d))
        })
        .collect()
}

/// A recognised argument, named in explanations.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Pattern {
    IsZero,
    Quotient,
    Radix,
    Truncation,
}

impl Pattern {
    pub fn name(self) -> &'static str {
        match self {
            Pattern::IsZero => "is-zero",
            Pattern::Quotient => "integer-quotient",
            Pattern::Radix => "radix",
            Pattern::Truncation => "truncation-check",
        }
    }

    pub fn explain(self) -> &'static str {
        match self {
            Pattern::IsZero => {
                "field inversion (directive_invert): z = 1/E, or 0 when E = 0; for y = 1 - E*z, E*y = 0 for every E, and y is 0 or 1"
            }
            Pattern::Quotient => {
                "integer quotient (directive_integer_quotient) by a nonzero constant b: a = b*q + r with r < b and q <= floor(amax/b), amax a bound on a"
            }
            Pattern::Radix => {
                "radix decomposition (directive_to_radix) with constant radix and limb count: digits are below the radix and recompose x when radix^limbs exceeds every value of x"
            }
            Pattern::Truncation => {
                "canonical truncation check: y = is_zero(c - q) for a quotient q; when y = 1, q = c and the remainder is at most amax - c*b"
            }
        }
    }

    pub const ALL: [Pattern; 4] = [
        Pattern::IsZero,
        Pattern::Quotient,
        Pattern::Radix,
        Pattern::Truncation,
    ];
}

/// One recognised directive call, with the honest-value facts it gives.
#[derive(Clone, Debug)]
pub(super) enum HintCall {
    Invert {
        e: Norm,
    },
    Quotient {
        a: Norm,
        amax: BigInt,
        b: FieldElement,
        q: u32,
        r: u32,
    },
    ToRadix {
        x: Norm,
        xmax: BigInt,
        radix: FieldElement,
        limbs: Vec<u32>,
    },
}

/// What a witness is in a recognised call.
#[derive(Clone, Copy, Debug)]
enum Role {
    Inverse(usize),
    Quotient(usize),
    Remainder(usize),
    Limb(usize),
}

/// Honest-value facts for one ACIR function.
#[derive(Default)]
pub(super) struct Facts {
    calls: Vec<HintCall>,
    roles: HashMap<u32, Role>,
    /// y -> the invert call whose input E it is the is-zero flag of.
    is_zero: HashMap<u32, usize>,
    /// Definitions u = expr of hint-derived witnesses.
    defs: HashMap<u32, Norm>,
}

impl Facts {
    pub(super) fn record_call(&mut self, call: HintCall) {
        let i = self.calls.len();
        match &call {
            HintCall::Invert { .. } => {}
            HintCall::Quotient { q, r, .. } => {
                self.roles.insert(*q, Role::Quotient(i));
                self.roles.insert(*r, Role::Remainder(i));
            }
            HintCall::ToRadix { limbs, .. } => {
                for l in limbs {
                    self.roles.insert(*l, Role::Limb(i));
                }
            }
        }
        self.calls.push(call);
    }

    fn record_inverse(&mut self, z: u32) {
        self.roles.insert(z, Role::Inverse(self.calls.len() - 1));
    }
}

/// Depth of definitions followed when bounding a value.
const DEPTH: u32 = 4;

/// Most bits a booleanity argument by cases enumerates (2^8 cases).
const BIT_CASES: usize = 8;

fn modulus() -> &'static BigInt {
    static P: OnceLock<BigInt> = OnceLock::new();
    P.get_or_init(|| to_int(-FieldElement::one()) + 1)
}

/// Canonical integer value of a field element.
fn to_int(c: FieldElement) -> BigInt {
    BigInt::from_biguint(Sign::Plus, BigUint::from_bytes_be(&c.to_be_bytes()))
}

/// A coefficient read as a signed integer: c, or c - p when that is
/// smaller in magnitude.
fn signed(c: FieldElement) -> BigInt {
    let v = to_int(c);
    if v.clone() * 2 > *modulus() {
        v - modulus()
    } else {
        v
    }
}

fn pow2(bits: u32) -> BigInt {
    BigInt::from(1) << bits
}

/// An integer interval; empty when lo > hi.
#[derive(Clone, Debug, PartialEq)]
struct Iv {
    lo: BigInt,
    hi: BigInt,
}

impl Iv {
    fn point(v: BigInt) -> Iv {
        Iv {
            lo: v.clone(),
            hi: v,
        }
    }

    fn empty() -> Iv {
        Iv {
            lo: BigInt::from(1),
            hi: BigInt::from(0),
        }
    }

    fn field() -> Iv {
        Iv {
            lo: BigInt::from(0),
            hi: modulus() - 1,
        }
    }

    fn upto(hi: BigInt) -> Iv {
        Iv {
            lo: BigInt::from(0),
            hi,
        }
    }

    fn is_empty(&self) -> bool {
        self.lo > self.hi
    }

    fn meet(&self, o: &Iv) -> Iv {
        Iv {
            lo: self.lo.clone().max(o.lo.clone()),
            hi: self.hi.clone().min(o.hi.clone()),
        }
    }

    fn hull(&self, o: &Iv) -> Iv {
        if self.is_empty() {
            return o.clone();
        }
        if o.is_empty() {
            return self.clone();
        }
        Iv {
            lo: self.lo.clone().min(o.lo.clone()),
            hi: self.hi.clone().max(o.hi.clone()),
        }
    }

    fn add(&self, o: &Iv) -> Iv {
        Iv {
            lo: &self.lo + &o.lo,
            hi: &self.hi + &o.hi,
        }
    }

    fn scale(&self, k: &BigInt) -> Iv {
        if *k >= BigInt::from(0) {
            Iv {
                lo: &self.lo * k,
                hi: &self.hi * k,
            }
        } else {
            Iv {
                lo: &self.hi * k,
                hi: &self.lo * k,
            }
        }
    }

    /// Product of two intervals of nonnegative values.
    fn mul_nonneg(&self, o: &Iv) -> Iv {
        Iv {
            lo: &self.lo * &o.lo,
            hi: &self.hi * &o.hi,
        }
    }

    /// A canonical field value: inside [0, p).
    fn canonical(&self) -> bool {
        self.lo >= BigInt::from(0) && self.hi < *modulus()
    }
}

/// Facts that hold when an is-zero flag y is 1: its input E is 0.
struct Assume {
    y: u32,
    fixed: HashMap<u32, BigInt>,
    caps: HashMap<u32, BigInt>,
}

impl FnAnalyser<'_, '_> {
    /// A directive call the honest-value facts apply to, read before its
    /// outputs are assigned.
    pub(super) fn directive_call(
        &self,
        id: u32,
        inputs: &[BrilligInputs<FieldElement>],
        outputs: &[BrilligOutputs],
        predicate: &Expression<FieldElement>,
    ) -> Option<HintCall> {
        let directive = *self.ctx.directives.get(&id)?;
        let pred = normalise(predicate);
        if !pred.mul.is_empty() || !pred.lin.is_empty() || pred.c.is_zero() {
            return None;
        }
        let mut exprs = Vec::new();
        for input in inputs {
            let BrilligInputs::Single(e) = input else {
                return None;
            };
            let n = normalise(e);
            if !n.mul.is_empty() || n.lin.iter().any(|(_, w)| !self.known(*w)) {
                return None;
            }
            exprs.push(n);
        }
        let constant = |n: &Norm| n.lin.is_empty().then_some(n.c);
        let simple: Vec<u32> = outputs
            .iter()
            .filter_map(|o| match o {
                BrilligOutputs::Simple(w) => Some(w.0),
                BrilligOutputs::Array(_) => None,
            })
            .collect();
        match (directive, exprs.as_slice()) {
            (Directive::Invert, [e]) if simple.len() == 1 && outputs.len() == 1 => {
                Some(HintCall::Invert { e: e.clone() })
            }
            (Directive::IntegerQuotient, [a, b]) if simple.len() == 2 && outputs.len() == 2 => {
                let b = constant(b).filter(|b| !b.is_zero())?;
                Some(HintCall::Quotient {
                    amax: self.max_value(a),
                    a: a.clone(),
                    b,
                    q: simple[0],
                    r: simple[1],
                })
            }
            (Directive::ToRadix, [x, n, radix]) => {
                let (n, radix) = (constant(n)?, constant(radix)?);
                let [BrilligOutputs::Array(limbs)] = outputs else {
                    return None;
                };
                let ok = n.num_bits() <= 32
                    && n.to_u128() as usize == limbs.len()
                    && !limbs.is_empty()
                    && radix.num_bits() <= 32
                    && radix.to_u128() >= 2;
                ok.then(|| HintCall::ToRadix {
                    xmax: self.max_value(x),
                    x: x.clone(),
                    radix,
                    limbs: limbs.iter().map(|w| w.0).collect(),
                })
            }
            _ => None,
        }
    }

    /// Record an invert call's output once it is assigned.
    pub(super) fn record_directive(&mut self, call: HintCall, outputs: &[BrilligOutputs]) {
        let is_invert = matches!(call, HintCall::Invert { .. });
        self.honest.record_call(call);
        if is_invert && let [BrilligOutputs::Simple(z)] = outputs {
            self.honest.record_inverse(z.0);
        }
    }

    /// Largest canonical value a linear expression can take, from the
    /// facts known now; p - 1 when nothing tighter is known.
    fn max_value(&self, n: &Norm) -> BigInt {
        let iv = self.interval_expr(n, None, DEPTH);
        if iv.canonical() { iv.hi } else { modulus() - 1 }
    }

    /// Record the definition u = -(rest)/lin_u of a hint-derived witness,
    /// and recognise the is-zero flag y = 1 - E*z.
    pub(super) fn record_definition(&mut self, n: &Norm, u: u32, lin_u: FieldElement) {
        let def = n
            .add(&Norm::witness(u).scale(-lin_u))
            .scale(-(FieldElement::one() / lin_u));
        let zs: Vec<(u32, usize)> = def
            .witnesses()
            .into_iter()
            .filter_map(|w| match self.honest.roles.get(&w) {
                Some(Role::Inverse(i)) => Some((w, *i)),
                _ => None,
            })
            .collect();
        for (z, i) in zs {
            let HintCall::Invert { e } = &self.honest.calls[i] else {
                continue;
            };
            let Some(ez) = e.times_witness(z) else {
                continue;
            };
            let flag = Norm::constant(FieldElement::one()).add(&ez.scale(-FieldElement::one()));
            if flag == def {
                self.honest.is_zero.insert(u, i);
                break;
            }
        }
        self.honest.defs.insert(u, def);
    }

    /// Interval of a witness's canonical value under the honest hints.
    fn interval_w(&self, w: u32, assume: Option<&Assume>, depth: u32) -> Iv {
        if let Some(c) = self.w.get(&w).and_then(|i| i.constant) {
            return Iv::point(to_int(c));
        }
        let mut iv = Iv::field();
        if let Some(b) = self.w.get(&w).and_then(|i| i.bound) {
            iv = iv.meet(&Iv::upto(pow2(b) - 1));
        }
        if let Some(a) = assume {
            if let Some(v) = a.fixed.get(&w) {
                iv = iv.meet(&Iv::point(v.clone()));
            }
            if let Some(cap) = a.caps.get(&w) {
                iv = iv.meet(&Iv::upto(cap.clone()));
            }
        }
        match self.honest.roles.get(&w) {
            Some(Role::Quotient(i)) => {
                if let HintCall::Quotient { amax, b, .. } = &self.honest.calls[*i] {
                    iv = iv.meet(&Iv::upto(amax / to_int(*b)));
                }
            }
            Some(Role::Remainder(i)) => {
                if let HintCall::Quotient { b, .. } = &self.honest.calls[*i] {
                    iv = iv.meet(&Iv::upto(to_int(*b) - 1));
                }
            }
            Some(Role::Limb(i)) => {
                if let HintCall::ToRadix { radix, .. } = &self.honest.calls[*i] {
                    iv = iv.meet(&Iv::upto(to_int(*radix) - 1));
                }
            }
            Some(Role::Inverse(_)) | None => {}
        }
        if self.honest.is_zero.contains_key(&w) {
            iv = iv.meet(&Iv::upto(BigInt::from(1)));
        }
        if depth > 0
            && let Some(def) = self.honest.defs.get(&w)
        {
            let d = self.interval_expr(def, assume, depth - 1);
            if d.canonical() || d.is_empty() {
                iv = iv.meet(&d);
            }
        }
        iv
    }

    /// Interval of an expression's integer value (coefficients read as
    /// signed integers); its field value equals it when the interval lies
    /// in [0, p).
    fn interval_expr(&self, n: &Norm, assume: Option<&Assume>, depth: u32) -> Iv {
        let mut acc = Iv::point(signed(n.c));
        for (k, a, b) in &n.mul {
            let (ia, ib) = (
                self.interval_w(*a, assume, depth),
                self.interval_w(*b, assume, depth),
            );
            if ia.is_empty() || ib.is_empty() {
                return Iv::empty();
            }
            acc = acc.add(&ia.mul_nonneg(&ib).scale(&signed(*k)));
        }
        for (k, w) in &n.lin {
            let iw = self.interval_w(*w, assume, depth);
            if iw.is_empty() {
                return iw;
            }
            acc = acc.add(&iw.scale(&signed(*k)));
        }
        acc
    }

    /// The facts that hold when is-zero flag y is 1, or None when y = 1
    /// is impossible with honest hints.
    fn assume_flag(&self, y: u32) -> Option<Assume> {
        let mut a = Assume {
            y,
            fixed: HashMap::new(),
            caps: HashMap::new(),
        };
        a.fixed.insert(y, BigInt::from(1));
        let HintCall::Invert { e } = &self.honest.calls[self.honest.is_zero[&y]] else {
            return Some(a);
        };
        if let [(k, v)] = e.lin.as_slice() {
            // E = k*v + c = 0: v = -c/k.
            let val = to_int(-(e.c / *k));
            if !self
                .interval_w(*v, None, DEPTH)
                .meet(&Iv::point(val.clone()))
                .is_empty()
            {
                if let Some(Role::Quotient(i)) = self.honest.roles.get(v)
                    && let HintCall::Quotient { amax, b, r, .. } = &self.honest.calls[*i]
                {
                    let cap = amax - &val * to_int(*b);
                    if cap < BigInt::from(0) {
                        return None;
                    }
                    a.caps.insert(*r, cap);
                }
                a.fixed.insert(*v, val);
            } else {
                return None;
            }
        }
        Some(a)
    }

    /// An is-zero flag y common to every term of n, and n / y.
    fn split_on_flag(&self, n: &Norm) -> Option<(u32, Norm)> {
        if !n.c.is_zero() {
            return None;
        }
        let candidates: BTreeSet<u32> = n
            .witnesses()
            .into_iter()
            .filter(|w| self.honest.is_zero.contains_key(w))
            .collect();
        'next: for y in candidates {
            let mut lin = BTreeMap::new();
            let mut c = FieldElement::zero();
            for (k, a, b) in &n.mul {
                let other = if *a == y {
                    *b
                } else if *b == y {
                    *a
                } else {
                    continue 'next;
                };
                *lin.entry(other).or_insert(FieldElement::zero()) += *k;
            }
            for (k, w) in &n.lin {
                if *w != y {
                    continue 'next;
                }
                c += *k;
            }
            return Some((y, Norm::from_maps(BTreeMap::new(), lin, c)));
        }
        None
    }

    /// Interval of an expression under the honest hints, splitting on an
    /// is-zero flag that multiplies every term. The second value says
    /// whether the split used the truncation-check argument.
    fn honest_interval(&self, n: &Norm) -> (Iv, bool) {
        let direct = self.interval_expr(n, None, DEPTH);
        let Some((y, x)) = self.split_on_flag(n) else {
            return (direct, false);
        };
        let zero = Iv::point(BigInt::from(0));
        let e = match &self.honest.calls[self.honest.is_zero[&y]] {
            HintCall::Invert { e } => e,
            _ => return (direct, false),
        };
        // y * (multiple of E): 0 when y = 0 and when E = 0.
        if x.is_zero() || x.same_up_to_scale(e) {
            return (direct.meet(&zero), false);
        }
        let split = match self.assume_flag(y) {
            None => zero,
            Some(a) => {
                debug_assert_eq!(a.y, y);
                zero.hull(&self.interval_expr(&x, Some(&a), DEPTH))
            }
        };
        (direct.meet(&split), true)
    }

    /// The recognised patterns behind the witnesses of n, through their
    /// definitions.
    fn patterns_of(&self, n: &Norm, truncation: bool) -> BTreeSet<Pattern> {
        let mut out = BTreeSet::new();
        if truncation {
            out.insert(Pattern::Truncation);
        }
        let mut todo: Vec<(u32, u32)> = n.witnesses().into_iter().map(|w| (w, DEPTH)).collect();
        let mut seen = BTreeSet::new();
        while let Some((w, depth)) = todo.pop() {
            if !seen.insert(w) {
                continue;
            }
            match self.honest.roles.get(&w) {
                Some(Role::Quotient(_) | Role::Remainder(_)) => {
                    out.insert(Pattern::Quotient);
                }
                Some(Role::Limb(_)) => {
                    out.insert(Pattern::Radix);
                }
                Some(Role::Inverse(_)) => {
                    out.insert(Pattern::IsZero);
                }
                None => {}
            }
            if self.honest.is_zero.contains_key(&w) {
                out.insert(Pattern::IsZero);
            }
            if depth > 0
                && let Some(def) = self.honest.defs.get(&w)
            {
                todo.extend(def.witnesses().into_iter().map(|x| (x, depth - 1)));
            }
        }
        out
    }

    fn pattern_text(patterns: &BTreeSet<Pattern>) -> String {
        patterns
            .iter()
            .map(|p| p.name())
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// A proof that `RANGE w bits` holds with honest compiler hints.
    pub(super) fn honest_range(&self, w: u32, bits: u32) -> Option<String> {
        let mut iv = self.interval_w(w, None, DEPTH);
        let mut truncation = false;
        let n = match self.honest.defs.get(&w) {
            Some(def) => {
                let (d, t) = self.honest_interval(def);
                if d.canonical() {
                    iv = iv.meet(&d);
                }
                truncation = t;
                def.clone()
            }
            None => Norm::witness(w),
        };
        let patterns = self.patterns_of(&n, truncation);
        if patterns.is_empty() || !(iv.canonical() && iv.hi < pow2(bits)) {
            return None;
        }
        Some(format!(
            "hint-compiler ({}): with the compiler's honest hints {} lies in [{}, {}], below 2^{bits}",
            Self::pattern_text(&patterns),
            wname(w),
            iv.lo,
            iv.hi
        ))
    }

    /// A proof that the assertion n = 0 holds with honest compiler hints.
    pub(super) fn honest_assertion(&self, n: &Norm) -> Option<String> {
        if let Some(text) = self.honest_identity(n) {
            return Some(text);
        }
        if let [(k, a, b)] = n.mul.as_slice()
            && a == b
            && let [(kl, x)] = n.lin.as_slice()
            && x == a
            && n.c.is_zero()
            && (*k + *kl).is_zero()
        {
            // The bound must come from how the circuit computes x, never
            // from a Brillig output's mere range: a hint, or a value
            // selected from one, is whatever the executor or stored data
            // makes it (aztec-nr's `Packable for bool` unpack asserts this
            // on a field read from storage).
            let patterns = self.patterns_of(n, false);
            let how = if self.is_bit(*a) {
                Some("which the compiler's honest hints keep in [0, 1]")
            } else if self.bit_by_cases(*a) {
                Some("which is 0 or 1 for every 0/1 value of the honest bits it is computed from")
            } else {
                None
            };
            if !patterns.is_empty()
                && let Some(how) = how
            {
                return Some(format!(
                    "hint-compiler ({}): booleanity of {}, {how}",
                    Self::pattern_text(&patterns),
                    wname(*a)
                ));
            }
        }
        let (iv, truncation) = self.honest_interval(n);
        let patterns = self.patterns_of(n, truncation);
        if !patterns.is_empty() && iv == Iv::point(BigInt::from(0)) {
            return Some(format!(
                "hint-compiler ({}): with the compiler's honest hints the expression is 0 for every input",
                Self::pattern_text(&patterns)
            ));
        }
        None
    }

    /// The honest value of w lies in [0, 1] by the facts known now: an
    /// is-zero flag, a binary digit, an earlier bound, or a definition
    /// whose interval is that tight. Read before the booleanity assertion
    /// on w is learned from (analyse_assertion), so it is never its own
    /// evidence.
    fn is_bit(&self, w: u32) -> bool {
        let iv = self.interval_w(w, None, DEPTH);
        iv.lo >= BigInt::from(0) && iv.hi <= BigInt::from(1)
    }

    /// The honest value of w is 0 or 1 for every 0/1 value of the bits its
    /// definition is built from (is_bit witnesses, through at most DEPTH
    /// definitions, at most BIT_CASES of them): exclusive or, `a + b - ab`
    /// and other combinations interval arithmetic cannot bound. Taking the
    /// bits as independent covers every value they can take together.
    fn bit_by_cases(&self, w: u32) -> bool {
        let Some(def) = self.honest.defs.get(&w) else {
            return false;
        };
        let mut bits = BTreeSet::new();
        if !def
            .witnesses()
            .into_iter()
            .all(|x| self.case_bits(x, DEPTH - 1, &mut bits))
        {
            return false;
        }
        let bits: Vec<u32> = bits.into_iter().collect();
        (0..1u32 << bits.len()).all(|mask| {
            let env: HashMap<u32, BigInt> = bits
                .iter()
                .enumerate()
                .map(|(i, b)| (*b, BigInt::from((mask >> i) & 1)))
                .collect();
            self.eval_cases(def, &env, DEPTH - 1)
                .is_some_and(|v| v == BigInt::from(0) || v == BigInt::from(1))
        })
    }

    /// Collect the bits x is built from (see bit_by_cases); false when x
    /// rests on anything else or on too many bits.
    fn case_bits(&self, x: u32, depth: u32, bits: &mut BTreeSet<u32>) -> bool {
        if self.w.get(&x).and_then(|i| i.constant).is_some() {
            return true;
        }
        if self.is_bit(x) {
            bits.insert(x);
            return bits.len() <= BIT_CASES;
        }
        match self.honest.defs.get(&x) {
            Some(def) if depth > 0 => def
                .witnesses()
                .into_iter()
                .all(|y| self.case_bits(y, depth - 1, bits)),
            _ => false,
        }
    }

    /// Integer value of n with the bits set by env (see bit_by_cases).
    fn eval_cases(&self, n: &Norm, env: &HashMap<u32, BigInt>, depth: u32) -> Option<BigInt> {
        let value = |x: u32| -> Option<BigInt> {
            if let Some(c) = self.w.get(&x).and_then(|i| i.constant) {
                return Some(to_int(c));
            }
            if let Some(v) = env.get(&x) {
                return Some(v.clone());
            }
            let def = self.honest.defs.get(&x).filter(|_| depth > 0)?;
            self.eval_cases(def, env, depth - 1)
        };
        let mut acc = signed(n.c);
        for (k, a, b) in &n.mul {
            acc += signed(*k) * value(*a)? * value(*b)?;
        }
        for (k, x) in &n.lin {
            acc += signed(*k) * value(*x)?;
        }
        Some(acc)
    }

    /// The quotient and radix identities.
    fn honest_identity(&self, n: &Norm) -> Option<String> {
        let calls: BTreeSet<usize> = n
            .witnesses()
            .into_iter()
            .filter_map(|w| match self.honest.roles.get(&w) {
                Some(Role::Quotient(i) | Role::Remainder(i) | Role::Limb(i)) => Some(*i),
                _ => None,
            })
            .collect();
        let neg = -FieldElement::one();
        for i in calls {
            match &self.honest.calls[i] {
                HintCall::Quotient { a, b, q, r, .. } => {
                    let expected = Norm::witness(*r)
                        .add(&Norm::witness(*q).scale(*b))
                        .add(&a.scale(neg));
                    if n.same_up_to_scale(&expected) {
                        return Some(format!(
                            "hint-compiler (integer-quotient): {} + {}*{} = a is the definition of the honest integer quotient by the constant {}",
                            wname(*r),
                            b,
                            wname(*q),
                            b
                        ));
                    }
                }
                HintCall::ToRadix {
                    x,
                    xmax,
                    radix,
                    limbs,
                } => {
                    let mut expected = x.scale(neg);
                    let mut power = FieldElement::one();
                    for l in limbs {
                        expected = expected.add(&Norm::witness(*l).scale(power));
                        power = power * *radix;
                    }
                    let capacity = pow(&to_int(*radix), limbs.len());
                    if n.same_up_to_scale(&expected) && capacity > *xmax {
                        return Some(format!(
                            "hint-compiler (radix): {} honest base-{} digits recompose x, since {}^{} exceeds its largest value {}",
                            limbs.len(),
                            radix,
                            radix,
                            limbs.len(),
                            xmax
                        ));
                    }
                }
                HintCall::Invert { .. } => {}
            }
        }
        None
    }
}

fn pow(base: &BigInt, exp: usize) -> BigInt {
    let mut out = BigInt::from(1);
    for _ in 0..exp {
        out *= base;
    }
    out
}

#[cfg(test)]
pub(super) fn recognised_bytecode(d: Directive) -> &'static [&'static str] {
    d.bytecode()
}
