//! Witness-knownness dataflow over ACIR, and the classification of every
//! opcode by whether it can fail and who controls the failure.
//!
//! The ACVM solves opcodes strictly in order. Before an opcode runs, a
//! witness is either assigned or not. Circuit parameters start assigned.
//! Every assigned witness carries a taint:
//! - `Input`: computed only from parameters and constants. A constraint
//!   over input-tainted witnesses alone holds or fails depending only on
//!   the inputs.
//! - `Hint`: depends on a Brillig output somewhere upstream. A constraint
//!   touching a hint witness restricts a prover-chosen value; whether the
//!   honest hint always satisfies it is not decidable here.
//!
//! The dataflow also tracks three facts that let some checks be shown
//! harmless: an upper bound in bits (from RANGE checks, booleanity,
//! bounded arithmetic definitions), known constants, and known-nonzero
//! witnesses (from `x*y = c` with `c != 0`).
//!
//! Outputs of the compiler's own hint directives get a fourth fact: what
//! the honest directive computes. Constraints that hold for every input
//! given those honest values are `hint-compiler` (see `compiler`).

use std::collections::{BTreeMap, BTreeSet, HashMap};

use acir::circuit::brillig::{BrilligInputs, BrilligOutputs};
use acir::circuit::opcodes::{BlackBoxFuncCall, FunctionInput, MemOpKind};
use acir::circuit::{Circuit, Opcode, OpcodeLocation, Program};
use acir::native_types::{Expression, Witness};
use acir::{AcirField, FieldElement};

use crate::artifact::{EntryParam, brillig_name};

mod compiler;
pub use compiler::{Directive, Pattern, directives};

/// Who an opcode's source location belongs to. Decided by the innermost
/// call-stack frame that is not in the Noir standard library.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Origin {
    /// A frame in one of the whitelisted library source trees.
    Library,
    /// Any other package frame.
    User,
    /// Only standard-library frames, or no location at all.
    Compiler,
}

/// Where a hint-tainted witness got its taint.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum HintOrigin {
    /// Output of the Brillig function with this id.
    Brillig(u32),
    /// Output of a call to the ACIR function with this id.
    Call(u32),
    /// Assigned by an opcode the lint could not solve.
    Unsolved,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Taint {
    Input,
    Hint(HintOrigin),
}

impl Taint {
    fn join(self, other: Taint) -> Taint {
        match (self, other) {
            (Taint::Hint(h), _) => Taint::Hint(h),
            (_, t) => t,
        }
    }
    pub fn is_hint(self) -> bool {
        matches!(self, Taint::Hint(_))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Kind {
    /// AssertZero over witnesses that are all assigned already.
    Assert,
    /// AssertZero that assigns one fresh witness with a constant coefficient.
    Definition,
    /// AssertZero that assigns a fresh witness whose coefficient depends
    /// on other witnesses; fails when that coefficient is zero.
    ConditionalSolve,
    /// AssertZero the ACVM cannot solve (two or more unassigned witnesses,
    /// or a fresh witness squared).
    Unsolvable,
    Range,
    /// AND / XOR: both inputs must fit the bit width.
    Logic,
    /// Other black-box calls.
    BlackBox,
    MemoryInit,
    MemoryRead,
    MemoryWrite,
    BrilligCall,
    Call,
}

impl Kind {
    pub fn name(self) -> &'static str {
        match self {
            Kind::Assert => "assert",
            Kind::Definition => "definition",
            Kind::ConditionalSolve => "conditional-solve",
            Kind::Unsolvable => "unsolvable",
            Kind::Range => "range",
            Kind::Logic => "logic",
            Kind::BlackBox => "blackbox",
            Kind::MemoryInit => "memory-init",
            Kind::MemoryRead => "memory-read",
            Kind::MemoryWrite => "memory-write",
            Kind::BrilligCall => "brillig-call",
            Kind::Call => "call",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Class {
    /// Cannot fail: assigns fresh witnesses or initialises memory.
    Definition,
    /// Cannot fail here: its predicate is the constant zero, or it is
    /// statically true (constant input in range, constant index in bounds).
    Neutralised,
    /// Can fail only when an earlier opcode has already failed (for
    /// example a RANGE on a witness an earlier RANGE bounds more tightly).
    Implied,
    /// Holds for every input at witness generation, but the proving
    /// backend is allowed to fail on some inputs (ECDSA with a public key
    /// off the curve). Listed for information; does not change the exit code.
    BackendDefined,
    /// Touches only hint witnesses of the compiler's own directives (field
    /// inversion, integer quotient, radix decomposition), in a pattern that
    /// holds for every input when those hints are honest. Whitelisted.
    HintCompiler,
    /// Touches a hint witness and its source is in the library: hint-class,
    /// whitelisted by provenance. Reviewers verify hint-satisfiability.
    HintLibrary,
    /// Touches a hint witness and its source is outside the library. Not
    /// decidable here; reported as possibly input-falsifiable.
    HintUnreviewed,
    /// Equates a hint-derived witness to a constant, possibly under an
    /// input branch condition: the shape of an asserted comparison or flag.
    /// A total circuit returns such a value instead of asserting it, so this
    /// is reported whatever the provenance.
    HintPinned,
    /// Depends only on inputs; source outside the library.
    InputFalsifiable,
    /// Depends only on inputs although its source is in the library.
    LibraryInputFalsifiable,
    /// The ACVM cannot solve the opcode at all.
    Unsolvable,
}

impl Class {
    pub fn name(self) -> &'static str {
        match self {
            Class::Definition => "definition",
            Class::Neutralised => "neutralised",
            Class::Implied => "implied",
            Class::BackendDefined => "backend-defined",
            Class::HintCompiler => "hint-compiler",
            Class::HintLibrary => "hint-library",
            Class::HintUnreviewed => "hint-unreviewed",
            Class::HintPinned => "hint-pinned",
            Class::InputFalsifiable => "input-falsifiable",
            Class::LibraryInputFalsifiable => "library-input-falsifiable",
            Class::Unsolvable => "unsolvable",
        }
    }

    /// Classes that keep the exit code nonzero unless justified.
    pub fn is_reported(self) -> bool {
        matches!(
            self,
            Class::HintUnreviewed
                | Class::HintPinned
                | Class::InputFalsifiable
                | Class::LibraryInputFalsifiable
                | Class::Unsolvable
        )
    }

    pub fn from_name(name: &str) -> Option<Class> {
        Class::ALL.into_iter().find(|c| c.name() == name)
    }

    pub const ALL: [Class; 11] = [
        Class::Definition,
        Class::Neutralised,
        Class::Implied,
        Class::BackendDefined,
        Class::HintCompiler,
        Class::HintLibrary,
        Class::HintUnreviewed,
        Class::HintPinned,
        Class::InputFalsifiable,
        Class::LibraryInputFalsifiable,
        Class::Unsolvable,
    ];
}

/// One classified ACIR opcode.
#[derive(Clone, Debug)]
pub struct Item {
    pub function: usize,
    pub opcode: usize,
    pub kind: Kind,
    pub class: Class,
    /// Short name, e.g. "RANGE 64" or the black-box name.
    pub label: String,
    /// The opcode as text (truncated for long opcodes).
    pub text: String,
    /// Predicate expression, for opcodes that carry one.
    pub predicate: Option<String>,
    /// The constraint's own assertion message, if the circuit has one.
    pub message: Option<String>,
    /// The compiler's range check for a typed parameter of the entry
    /// function: a RANGE on the parameter's witness at the width its ABI
    /// type declares.
    pub entry_param: bool,
    /// Why the item can (or cannot) fail.
    pub why: Vec<String>,
    pub origin: Origin,
}

/// One Brillig call site, with what the trap analysis needs from it.
#[derive(Clone, Debug)]
pub struct BrilligCallSite {
    pub function: usize,
    pub opcode: usize,
    pub callee: u32,
    pub predicate: String,
    pub predicate_zero: bool,
    pub outputs: usize,
    /// Per flattened calldata slot: is the value known nonzero here?
    pub slot_nonzero: Vec<bool>,
}

/// One ACIR call site.
#[derive(Clone, Debug)]
pub struct AcirCallSite {
    pub function: usize,
    pub opcode: usize,
    pub callee: u32,
    pub predicate: String,
    pub predicate_zero: bool,
}

#[derive(Default)]
pub struct Analysis {
    pub items: Vec<Item>,
    pub brillig_calls: Vec<BrilligCallSite>,
    pub acir_calls: Vec<AcirCallSite>,
}

#[derive(Clone, Debug)]
struct WInfo {
    taint: Taint,
    bound: Option<u32>,
    constant: Option<FieldElement>,
    nonzero: bool,
    /// Witnesses common to every term of this witness's definition, when
    /// that definition is a sum of products with no constant: a branch
    /// predicate folded into the value shows up here.
    factors: Vec<u32>,
    /// Assigned directly as a Brillig call output.
    direct: bool,
}

impl WInfo {
    fn new(taint: Taint) -> Self {
        WInfo {
            taint,
            bound: None,
            constant: None,
            nonzero: false,
            factors: Vec::new(),
            direct: false,
        }
    }
}

#[derive(Clone, Debug)]
struct Block {
    len: u32,
    taint: Taint,
    bound: Option<u32>,
}

/// Expression with duplicate terms merged and zero terms dropped. Terms
/// are sorted, so two equal expressions have equal Norms.
#[derive(Clone, Debug, PartialEq)]
struct Norm {
    mul: Vec<(FieldElement, u32, u32)>,
    lin: Vec<(FieldElement, u32)>,
    c: FieldElement,
}

fn normalise(e: &Expression<FieldElement>) -> Norm {
    let mut mul: BTreeMap<(u32, u32), FieldElement> = BTreeMap::new();
    for (k, a, b) in &e.mul_terms {
        let (x, y) = (a.0.min(b.0), a.0.max(b.0));
        let entry = mul.entry((x, y)).or_insert(FieldElement::zero());
        *entry += *k;
    }
    let mut lin: BTreeMap<u32, FieldElement> = BTreeMap::new();
    for (k, w) in &e.linear_combinations {
        let entry = lin.entry(w.0).or_insert(FieldElement::zero());
        *entry += *k;
    }
    Norm {
        mul: mul
            .into_iter()
            .filter(|(_, k)| !k.is_zero())
            .map(|((a, b), k)| (k, a, b))
            .collect(),
        lin: lin
            .into_iter()
            .filter(|(_, k)| !k.is_zero())
            .map(|(w, k)| (k, w))
            .collect(),
        c: e.q_c,
    }
}

impl Norm {
    fn from_maps(
        mul: BTreeMap<(u32, u32), FieldElement>,
        lin: BTreeMap<u32, FieldElement>,
        c: FieldElement,
    ) -> Norm {
        Norm {
            mul: mul
                .into_iter()
                .filter(|(_, k)| !k.is_zero())
                .map(|((a, b), k)| (k, a, b))
                .collect(),
            lin: lin
                .into_iter()
                .filter(|(_, k)| !k.is_zero())
                .map(|(w, k)| (k, w))
                .collect(),
            c,
        }
    }

    fn maps(
        &self,
    ) -> (
        BTreeMap<(u32, u32), FieldElement>,
        BTreeMap<u32, FieldElement>,
    ) {
        (
            self.mul.iter().map(|(k, a, b)| ((*a, *b), *k)).collect(),
            self.lin.iter().map(|(k, w)| (*w, *k)).collect(),
        )
    }

    fn scale(&self, k: FieldElement) -> Norm {
        let (mul, lin) = self.maps();
        Norm::from_maps(
            mul.into_iter().map(|(t, v)| (t, v * k)).collect(),
            lin.into_iter().map(|(t, v)| (t, v * k)).collect(),
            self.c * k,
        )
    }

    fn add(&self, other: &Norm) -> Norm {
        let (mut mul, mut lin) = self.maps();
        for (k, a, b) in &other.mul {
            *mul.entry((*a, *b)).or_insert(FieldElement::zero()) += *k;
        }
        for (k, w) in &other.lin {
            *lin.entry(*w).or_insert(FieldElement::zero()) += *k;
        }
        Norm::from_maps(mul, lin, self.c + other.c)
    }

    fn witness(w: u32) -> Norm {
        Norm {
            mul: vec![],
            lin: vec![(FieldElement::one(), w)],
            c: FieldElement::zero(),
        }
    }

    fn constant(c: FieldElement) -> Norm {
        Norm {
            mul: vec![],
            lin: vec![],
            c,
        }
    }

    /// This linear expression times witness `w`; None if not linear.
    fn times_witness(&self, w: u32) -> Option<Norm> {
        if !self.mul.is_empty() {
            return None;
        }
        let mut mul = BTreeMap::new();
        for (k, x) in &self.lin {
            *mul.entry(((*x).min(w), (*x).max(w)))
                .or_insert(FieldElement::zero()) += *k;
        }
        let mut lin = BTreeMap::new();
        if !self.c.is_zero() {
            lin.insert(w, self.c);
        }
        Some(Norm::from_maps(mul, lin, FieldElement::zero()))
    }

    fn is_zero(&self) -> bool {
        self.mul.is_empty() && self.lin.is_empty() && self.c.is_zero()
    }

    /// Some nonzero multiple of `other` equals self.
    fn same_up_to_scale(&self, other: &Norm) -> bool {
        let pair = |n: &Norm| -> Option<FieldElement> {
            n.mul
                .first()
                .map(|t| t.0)
                .or(n.lin.first().map(|t| t.0))
                .or((!n.c.is_zero()).then_some(n.c))
        };
        match (pair(self), pair(other)) {
            (None, None) => true,
            (Some(a), Some(b)) => &other.scale(a / b) == self,
            _ => false,
        }
    }

    fn witnesses(&self) -> BTreeSet<u32> {
        let mut s = BTreeSet::new();
        for (_, a, b) in &self.mul {
            s.insert(*a);
            s.insert(*b);
        }
        for (_, w) in &self.lin {
            s.insert(*w);
        }
        s
    }
}

/// For a small nonnegative constant k, the least e with k*x < 2^(b+e)
/// for every x < 2^b. None if k is large (a negative coefficient is a
/// large field element).
fn small_bits(k: FieldElement) -> Option<u32> {
    let b = k.num_bits();
    if b > 128 {
        return None;
    }
    let v = k.to_u128();
    Some(if v.is_power_of_two() { b - 1 } else { b })
}

/// Bits of x*y given x < 2^a and y < 2^b. A 0/1 factor adds nothing.
fn product_bits(a: u32, b: u32) -> u32 {
    match (a, b) {
        (0, _) | (_, 0) => 0,
        (1, x) | (x, 1) => x,
        (x, y) => x + y,
    }
}

fn ceil_log2(n: usize) -> u32 {
    if n <= 1 {
        0
    } else {
        usize::BITS - (n - 1).leading_zeros()
    }
}

fn wname(w: u32) -> String {
    format!("w{w}")
}

fn truncate(s: String, max: usize) -> String {
    if s.chars().count() <= max {
        s
    } else {
        let mut t: String = s.chars().take(max).collect();
        t.push_str(" ...");
        t
    }
}

fn opcode_text(op: &Opcode<FieldElement>) -> String {
    truncate(format!("{op}").replace('\n', " "), 160)
}

fn predicate_text(predicate: &Expression<FieldElement>) -> String {
    truncate(format!("{predicate}"), 80)
}

fn function_input_text(fi: &FunctionInput<FieldElement>) -> String {
    match fi {
        FunctionInput::Constant(c) => format!("{c}"),
        FunctionInput::Witness(w) => wname(w.0),
    }
}

/// Classification before provenance is applied.
enum Raw {
    Definition,
    Neutralised,
    Implied,
    BackendDefined,
    HintCompiler,
    Hint,
    HintPinned,
    Deterministic,
    Unsolvable,
}

impl Raw {
    /// Severity order used when one opcode carries several conditions.
    fn rank(&self) -> u8 {
        match self {
            Raw::Definition => 0,
            Raw::Neutralised => 1,
            Raw::Implied | Raw::BackendDefined | Raw::HintCompiler => 2,
            Raw::Hint => 3,
            Raw::HintPinned | Raw::Deterministic => 4,
            Raw::Unsolvable => 5,
        }
    }

    /// The more severe of two; `self` on a tie.
    fn worst(self, other: Raw) -> Raw {
        if other.rank() > self.rank() {
            other
        } else {
            self
        }
    }
}

/// What the analyser decided about one opcode, before provenance.
struct Verdict {
    kind: Kind,
    label: String,
    raw: Raw,
    predicate: Option<String>,
    why: Vec<String>,
    entry_param: bool,
}

impl Verdict {
    /// An AssertZero verdict.
    fn assert(kind: Kind, raw: Raw, why: Vec<String>) -> Verdict {
        Verdict::new(kind, "ASSERT", raw, why)
    }

    fn new(kind: Kind, label: impl Into<String>, raw: Raw, why: Vec<String>) -> Verdict {
        Verdict {
            kind,
            label: label.into(),
            raw,
            predicate: None,
            why,
            entry_param: false,
        }
    }

    fn predicate(mut self, p: Option<String>) -> Verdict {
        self.predicate = p;
        self
    }
}

pub struct Context<'a> {
    pub program: &'a Program<FieldElement>,
    /// Entry-function parameter witnesses with their ABI names and types.
    pub entry_params: &'a BTreeMap<u32, EntryParam>,
    /// Message lookup for assertion payload selectors.
    pub messages: &'a dyn Fn(u64) -> Option<String>,
    /// Provenance of (function, opcode).
    pub origin: &'a dyn Fn(usize, usize) -> Origin,
    /// Brillig functions recognised as the compiler's own directives
    /// (see `directives`).
    pub directives: &'a BTreeMap<u32, Directive>,
}

struct FnAnalyser<'c, 'a> {
    ctx: &'c Context<'a>,
    function: usize,
    w: HashMap<u32, WInfo>,
    blocks: HashMap<u32, Block>,
    entry_params: BTreeSet<u32>,
    /// Honest-value facts for compiler directive outputs and the
    /// definitions built on them.
    honest: compiler::Facts,
}

impl<'c, 'a> FnAnalyser<'c, 'a> {
    fn known(&self, w: u32) -> bool {
        self.w.contains_key(&w)
    }

    fn taint(&self, w: u32) -> Taint {
        self.w
            .get(&w)
            .map(|i| i.taint)
            .unwrap_or(Taint::Hint(HintOrigin::Unsolved))
    }

    fn bound(&self, w: u32) -> Option<u32> {
        let info = self.w.get(&w)?;
        if let Some(c) = info.constant {
            return Some(c.num_bits());
        }
        info.bound
    }

    fn brillig_name(&self, id: u32) -> String {
        brillig_name(self.ctx.program, id)
            .map(str::to_string)
            .unwrap_or_else(|| format!("brillig#{id}"))
    }

    fn origin_text(&self, h: HintOrigin) -> String {
        match h {
            HintOrigin::Brillig(id) => format!("Brillig function {id} ({})", self.brillig_name(id)),
            HintOrigin::Call(id) => format!("call to ACIR function {id}"),
            HintOrigin::Unsolved => "an opcode the lint could not solve".to_string(),
        }
    }

    /// Text naming the hint witnesses among `ws` and where they come from.
    fn hint_text(&self, ws: &BTreeSet<u32>) -> String {
        let mut parts = Vec::new();
        for &w in ws {
            if let Taint::Hint(h) = self.taint(w) {
                parts.push(format!("{} from {}", wname(w), self.origin_text(h)));
                if parts.len() == 4 {
                    parts.push("...".to_string());
                    break;
                }
            }
        }
        parts.join(", ")
    }

    fn join_taint(&self, ws: impl IntoIterator<Item = u32>) -> Taint {
        ws.into_iter()
            .fold(Taint::Input, |t, w| t.join(self.taint(w)))
    }

    fn assign(&mut self, w: u32, info: WInfo) {
        self.w.insert(w, info);
    }

    fn message_for(&self, opcode: usize) -> Option<String> {
        let circuit = &self.ctx.program.functions[self.function];
        circuit
            .assert_messages
            .iter()
            .find_map(|(loc, payload)| match loc {
                OpcodeLocation::Acir(i) if *i == opcode => {
                    (self.ctx.messages)(payload.error_selector)
                }
                _ => None,
            })
    }

    fn finish(&self, opcode: usize, op: &Opcode<FieldElement>, v: Verdict) -> Item {
        let origin = (self.ctx.origin)(self.function, opcode);
        let class = match v.raw {
            Raw::Definition => Class::Definition,
            Raw::Neutralised => Class::Neutralised,
            Raw::Implied => Class::Implied,
            Raw::BackendDefined => Class::BackendDefined,
            Raw::HintCompiler => Class::HintCompiler,
            Raw::Unsolvable => Class::Unsolvable,
            Raw::HintPinned => Class::HintPinned,
            Raw::Hint if origin == Origin::Library => Class::HintLibrary,
            Raw::Hint => Class::HintUnreviewed,
            Raw::Deterministic if origin == Origin::Library && !v.entry_param => {
                Class::LibraryInputFalsifiable
            }
            Raw::Deterministic => Class::InputFalsifiable,
        };
        Item {
            function: self.function,
            opcode,
            kind: v.kind,
            class,
            label: v.label,
            text: opcode_text(op),
            predicate: v.predicate,
            message: self.message_for(opcode),
            entry_param: v.entry_param,
            why: v.why,
            origin,
        }
    }

    /// Classify a requirement "witness or constant `fi` fits `bits` bits".
    /// Returns (raw, reason) for one input.
    fn fits(&self, fi: &FunctionInput<FieldElement>, bits: u32) -> (Raw, String) {
        match fi {
            FunctionInput::Constant(c) => {
                if c.num_bits() <= bits {
                    (Raw::Neutralised, format!("constant {c} fits {bits} bits"))
                } else {
                    (
                        Raw::Deterministic,
                        format!("constant {c} does not fit {bits} bits: always fails"),
                    )
                }
            }
            FunctionInput::Witness(w) => self.witness_fits(w.0, bits),
        }
    }

    fn witness_fits(&self, w: u32, bits: u32) -> (Raw, String) {
        if !self.known(w) {
            return (
                Raw::Unsolvable,
                format!("{} is not assigned when this opcode runs", wname(w)),
            );
        }
        if bits >= FieldElement::max_num_bits() {
            return (
                Raw::Neutralised,
                format!("every field element is below 2^{bits}"),
            );
        }
        if let Some(c) = self.w[&w].constant {
            if c.num_bits() <= bits {
                return (
                    Raw::Neutralised,
                    format!("{} is the constant {c}, which fits {bits} bits", wname(w)),
                );
            }
            return (
                Raw::Deterministic,
                format!(
                    "{} is the constant {c}, which does not fit {bits} bits: always fails",
                    wname(w)
                ),
            );
        }
        if let Some(b) = self.bound(w)
            && b <= bits
        {
            return (
                Raw::Implied,
                format!(
                    "{} is already bounded below 2^{b} by earlier opcodes; this check cannot fail on its own",
                    wname(w)
                ),
            );
        }
        let bound_note = match self.bound(w) {
            Some(b) => format!(" (earlier opcodes bound it only below 2^{b})"),
            None => String::new(),
        };
        match self.taint(w) {
            Taint::Hint(h) => {
                if let Some(proof) = self.honest_range(w, bits) {
                    return (Raw::HintCompiler, proof);
                }
                (
                    Raw::Hint,
                    format!(
                        "fails if {} >= 2^{bits}{bound_note}; {} depends on {}, so whether the honest hint keeps it in range is not decidable here",
                        wname(w),
                        wname(w),
                        self.origin_text(h)
                    ),
                )
            }
            Taint::Input => (
                Raw::Deterministic,
                format!(
                    "fails if {} >= 2^{bits}{bound_note}; {} is computed from inputs only",
                    wname(w),
                    wname(w)
                ),
            ),
        }
    }

    /// Note when a witness was defined with a factor common to every term:
    /// a branch predicate may be folded into it.
    fn product_note(&self, w: u32) -> Option<String> {
        let factors = &self.w.get(&w)?.factors;
        if factors.is_empty() {
            return None;
        }
        let names: Vec<String> = factors.iter().map(|x| wname(*x)).collect();
        Some(format!(
            "every term of {}'s definition contains {}; if that is a branch condition the check is disabled when it is zero, but the lint does not separate predicate from payload",
            wname(w),
            names.join(" or ")
        ))
    }

    fn analyse_assert_zero(
        &mut self,
        opcode: usize,
        op: &Opcode<FieldElement>,
        e: &Expression<FieldElement>,
    ) -> Item {
        let n = normalise(e);
        let ws = n.witnesses();
        let unknown: Vec<u32> = ws.iter().copied().filter(|w| !self.known(*w)).collect();
        let verdict = match unknown.as_slice() {
            [] => self.analyse_assertion(&n, &ws),
            [u] => self.analyse_solve(&n, &ws, *u),
            _ => {
                let why = vec![format!(
                    "{} unassigned witnesses ({}): the ACVM solves for at most one",
                    unknown.len(),
                    unknown
                        .iter()
                        .map(|w| wname(*w))
                        .collect::<Vec<_>>()
                        .join(", ")
                )];
                for u in &unknown {
                    self.assign(*u, WInfo::new(Taint::Hint(HintOrigin::Unsolved)));
                }
                Verdict::assert(Kind::Unsolvable, Raw::Unsolvable, why)
            }
        };
        self.finish(opcode, op, verdict)
    }

    /// An AssertZero with exactly one unassigned witness `u`, which the
    /// ACVM solves for.
    fn analyse_solve(&mut self, n: &Norm, ws: &BTreeSet<u32>, u: u32) -> Verdict {
        let mut why = Vec::new();
        let others: BTreeSet<u32> = ws.iter().copied().filter(|w| *w != u).collect();
        let taint = self.join_taint(others.iter().copied());
        if n.mul.iter().any(|(_, a, b)| *a == u && *b == u) {
            why.push(format!(
                "{} appears squared; the ACVM cannot solve for it",
                wname(u)
            ));
            self.assign(u, WInfo::new(Taint::Hint(HintOrigin::Unsolved)));
            return Verdict::assert(Kind::Unsolvable, Raw::Unsolvable, why);
        }

        let coeff_ws: Vec<(FieldElement, u32)> = n
            .mul
            .iter()
            .filter_map(|(k, a, b)| {
                if *a == u {
                    Some((*k, *b))
                } else if *b == u {
                    Some((*k, *a))
                } else {
                    None
                }
            })
            .collect();
        let lin_u = n
            .lin
            .iter()
            .find(|(_, w)| *w == u)
            .map(|(k, _)| *k)
            .unwrap_or(FieldElement::zero());

        let mut info = WInfo::new(taint);
        if coeff_ws.is_empty() {
            // u = -(rest) / lin_u, lin_u a nonzero constant.
            info.bound = self.definition_bound(n, u, lin_u);
            if others.is_empty() {
                info.constant = Some(-(n.c / lin_u));
            }
            if !n.mul.is_empty() && n.c.is_zero() {
                info.factors = others
                    .iter()
                    .copied()
                    .filter(|p| {
                        n.mul.iter().all(|(_, a, b)| a == p || b == p)
                            && n.lin.iter().all(|(_, x)| *x == u || x == p)
                    })
                    .collect();
            }
            self.assign(u, info);
            if taint.is_hint() {
                self.record_definition(n, u, lin_u);
            }
            return Verdict::assert(Kind::Definition, Raw::Definition, why);
        }

        // The coefficient of u is lin_u + sum(k * v): it varies with v.
        let single_nonzero = lin_u.is_zero()
            && coeff_ws.len() == 1
            && self
                .w
                .get(&coeff_ws[0].1)
                .map(|i| i.nonzero)
                .unwrap_or(false);
        self.assign(u, info);
        if single_nonzero {
            why.push(format!(
                "solves {} with coefficient {}, which an earlier opcode forces nonzero",
                wname(u),
                wname(coeff_ws[0].1)
            ));
            return Verdict::assert(Kind::Definition, Raw::Definition, why);
        }
        let coeff_set: BTreeSet<u32> = coeff_ws.iter().map(|(_, v)| *v).collect();
        why.push(format!(
            "solves {} by dividing by a coefficient that depends on {}; fails when that coefficient is zero and the rest is not",
            wname(u),
            coeff_set.iter().map(|w| wname(*w)).collect::<Vec<_>>().join(", ")
        ));
        let raw = if taint.is_hint() {
            why.push(format!(
                "involves hint witnesses: {}",
                self.hint_text(&others)
            ));
            Raw::Hint
        } else {
            why.push("every other witness is computed from inputs only".into());
            Raw::Deterministic
        };
        Verdict::assert(Kind::ConditionalSolve, raw, why)
    }

    /// Upper bound in bits for u = -(rest)/lin_u when every rescaled
    /// coefficient is a small nonnegative constant and every other witness
    /// has a bound.
    fn definition_bound(&self, n: &Norm, u: u32, lin_u: FieldElement) -> Option<u32> {
        let scale = -(FieldElement::one() / lin_u);
        let mut terms = Vec::new();
        for (k, a, b) in &n.mul {
            let kb = small_bits(*k * scale)?;
            terms.push(kb + product_bits(self.bound(*a)?, self.bound(*b)?));
        }
        for (k, w) in &n.lin {
            if *w == u {
                continue;
            }
            let kb = small_bits(*k * scale)?;
            terms.push(kb + self.bound(*w)?);
        }
        if !n.c.is_zero() {
            // A constant c is below 2^num_bits(c).
            let k = n.c * scale;
            small_bits(k)?;
            terms.push(k.num_bits());
        }
        let max = terms.iter().copied().max().unwrap_or(0);
        let total = max + ceil_log2(terms.len());
        if total <= 253 { Some(total) } else { None }
    }

    /// Facts an assertion over assigned witnesses establishes for later
    /// opcodes: booleanity bounds a witness to one bit, and `x*y = c` with
    /// c nonzero makes both factors nonzero.
    fn learn_from_assertion(&mut self, n: &Norm, why: &mut Vec<String>) {
        if n.mul.len() == 1 && n.lin.len() == 1 && n.c.is_zero() {
            let (k, a, b) = n.mul[0];
            let (kl, wl) = n.lin[0];
            if a == b && a == wl && (k + kl).is_zero() {
                if let Some(info) = self.w.get_mut(&a) {
                    info.bound = Some(info.bound.map_or(1, |x| x.min(1)));
                }
                why.push(format!("booleanity of {}", wname(a)));
            }
        }
        if n.mul.len() == 1 && n.lin.is_empty() && !n.c.is_zero() {
            let (_, a, b) = n.mul[0];
            for x in [a, b] {
                if let Some(info) = self.w.get_mut(&x) {
                    info.nonzero = true;
                }
            }
        }
    }

    fn analyse_assertion(&mut self, n: &Norm, ws: &BTreeSet<u32>) -> Verdict {
        let mut why = Vec::new();
        if ws.is_empty() {
            let (raw, text) = if n.c.is_zero() {
                (Raw::Neutralised, "constant zero: always holds".to_string())
            } else {
                (
                    Raw::Deterministic,
                    format!("constant {}: always fails", n.c),
                )
            };
            return Verdict::assert(Kind::Assert, raw, vec![text]);
        }

        // Decided before learning from this assertion: booleanity bounds
        // its witness to one bit, which must not count as evidence that
        // the same booleanity holds (honest_assertion reads that bound).
        let taint = self.join_taint(ws.iter().copied());
        let honest = if taint.is_hint() {
            self.honest_assertion(n)
        } else {
            None
        };

        self.learn_from_assertion(n, &mut why);

        if let Some(proof) = honest {
            why.insert(
                0,
                format!(
                    "checks assigned witnesses; involves hint witnesses: {}",
                    self.hint_text(ws)
                ),
            );
            why.push(proof);
            return Verdict::assert(Kind::Assert, Raw::HintCompiler, why);
        }

        if let Some(v) = self.pinned(n, ws) {
            return v;
        }

        let mut explained = false;
        if let Some(v) = self.nonzero_check(n, ws, &mut why, &mut explained) {
            return v;
        }

        // A witness common to every term may be a flattened branch predicate.
        if !n.mul.is_empty() && n.c.is_zero() {
            let factor = ws.iter().copied().find(|p| {
                n.mul.iter().all(|(_, a, b)| a == p || b == p) && n.lin.iter().all(|(_, w)| w == p)
            });
            if let Some(p) = factor {
                why.push(format!(
                    "every term contains {}; if {} is a branch condition this assert is disabled when it is zero, but the lint does not separate predicate from payload and classifies the whole product",
                    wname(p),
                    wname(p)
                ));
            }
        } else if !n.mul.is_empty() && !explained {
            why.push("contains products of witnesses; a flattened branch predicate, if any, is multiplied into the expression and the lint cannot separate it".into());
        }

        let raw = if taint.is_hint() {
            why.insert(
                0,
                format!(
                    "checks assigned witnesses; involves hint witnesses: {}",
                    self.hint_text(ws)
                ),
            );
            Raw::Hint
        } else {
            why.insert(0, "checks witnesses that are all computed from inputs only: whether it holds depends only on the inputs".into());
            Raw::Deterministic
        };
        Verdict::assert(Kind::Assert, raw, why)
    }

    /// E = h*L + c with c != 0 and h in every term fails when h = 0 or
    /// when L = 0, whatever the other factor is. Inverse-based checks
    /// lower this way: x != 0 is x*inv - 1, x != k is (x - k)*inv - 1.
    /// Returns the verdict when the check is decided by inputs; otherwise
    /// adds an explanation for the hint case and sets `explained`.
    fn nonzero_check(
        &self,
        n: &Norm,
        ws: &BTreeSet<u32>,
        why: &mut Vec<String>,
        explained: &mut bool,
    ) -> Option<Verdict> {
        if n.c.is_zero() || n.mul.is_empty() {
            return None;
        }
        for h in ws.iter().copied() {
            let shared = n.mul.iter().all(|(_, a, b)| (*a == h) != (*b == h))
                && n.lin.iter().all(|(_, w)| *w == h);
            if !shared {
                continue;
            }
            let cof: BTreeSet<u32> = n
                .mul
                .iter()
                .map(|(_, a, b)| if *a == h { *b } else { *a })
                .collect();
            if !self.taint(h).is_hint() {
                why.push(format!(
                    "is {} times something plus the nonzero constant {}: fails when {} = 0 whatever any hint is (a nonzero check), and {} is computed from inputs only",
                    wname(h),
                    n.c,
                    wname(h),
                    wname(h)
                ));
                return Some(Verdict::assert(
                    Kind::Assert,
                    Raw::Deterministic,
                    std::mem::take(why),
                ));
            }
            let cof_names = cof.iter().map(|w| wname(*w)).collect::<Vec<_>>().join(", ");
            if cof.iter().all(|w| !self.taint(*w).is_hint()) {
                why.push(format!(
                    "is {} times a linear form in {} plus the nonzero constant {}: fails whenever that form is zero, whatever {} is (a nonzero check such as x != k with a hinted inverse), and {} only depend on inputs",
                    wname(h),
                    cof_names,
                    n.c,
                    wname(h),
                    cof_names
                ));
                return Some(Verdict::assert(
                    Kind::Assert,
                    Raw::Deterministic,
                    std::mem::take(why),
                ));
            }
            why.push(format!(
                "a nonzero check on {} times a form in {}, which involve hint-derived witnesses; if they are determined by the inputs (a quotient, a comparison result, an ok flag) this check is input-falsifiable",
                wname(h),
                cof_names
            ));
            *explained = true;
            break;
        }
        None
    }

    /// A hint-derived witness equated to a constant: `k*x + c = 0` with x
    /// hint-derived, or, under a branch condition p computed from inputs
    /// only, `p*(k*x + c) = 0` with x a direct Brillig output. That is how
    /// an asserted comparison (`assert(a < b)` pins the comparison's
    /// borrow) or an asserted flag lowers. The second shape requires a
    /// direct output so that the is-zero gadget `x*z = 0`, whose z is
    /// defined from the inverse hint, is not mistaken for it.
    fn pinned(&self, n: &Norm, ws: &BTreeSet<u32>) -> Option<Verdict> {
        let (x, under) = if n.mul.is_empty() && n.lin.len() == 1 {
            let x = n.lin[0].1;
            (x, None)
        } else if !n.mul.is_empty() && n.c.is_zero() {
            ws.iter().find_map(|&p| {
                if self.taint(p).is_hint() || n.lin.iter().any(|(_, w)| *w != p) {
                    return None;
                }
                let mut cof = BTreeSet::new();
                for (_, a, b) in &n.mul {
                    match (*a == p, *b == p) {
                        (true, false) => cof.insert(*b),
                        (false, true) => cof.insert(*a),
                        _ => return None,
                    };
                }
                let x = *cof.first()?;
                let direct = self.w.get(&x).is_some_and(|i| i.direct);
                (cof.len() == 1 && direct).then_some((x, Some(p)))
            })?
        } else {
            return None;
        };
        if !self.taint(x).is_hint() {
            return None;
        }
        let mut why = vec![format!(
            "checks assigned witnesses; involves hint witnesses: {}",
            self.hint_text(ws)
        )];
        let pins = match under {
            None => format!("pins {}, which is hint-derived, to a constant", wname(x)),
            Some(p) => format!(
                "pins {}, a Brillig output, to a constant whenever {} (computed from inputs only, likely a branch condition) is nonzero",
                wname(x),
                wname(p)
            ),
        };
        why.push(format!(
            "{pins}: the shape of an asserted comparison or flag; a total circuit returns such a value instead of asserting it, so this is reported whatever its provenance"
        ));
        Some(Verdict::assert(Kind::Assert, Raw::HintPinned, why))
    }

    fn analyse_range(
        &mut self,
        opcode: usize,
        op: &Opcode<FieldElement>,
        input: &FunctionInput<FieldElement>,
        bits: u32,
    ) -> Item {
        let (raw, reason) = self.fits(input, bits);
        let mut why = vec![reason];
        let mut entry = false;
        let mut forced = false;
        let mut label = format!("RANGE {bits}");
        if let FunctionInput::Witness(w) = input {
            if self.entry_params.contains(&w.0) {
                match self.ctx.entry_params.get(&w.0) {
                    Some(p) if p.width == Some(bits) => {
                        entry = true;
                        label = format!("RANGE {bits} on entry parameter {}: {}", p.name, p.ty);
                        why.push(format!(
                            "{} is entry parameter {}: {}; this is the compiler's range check for the typed parameter, always input-falsifiable",
                            wname(w.0),
                            p.name,
                            p.ty
                        ));
                    }
                    Some(p) => {
                        label = format!("RANGE {bits} on entry parameter {}: {}", p.name, p.ty);
                        why.push(format!(
                            "{} is entry parameter {}: {}",
                            wname(w.0),
                            p.name,
                            p.ty
                        ));
                    }
                    None => {
                        forced = true;
                        label = format!("RANGE {bits} on entry parameter {}", wname(w.0));
                        why.push(format!(
                            "{} is a parameter of the entry function; the ABI does not name it",
                            wname(w.0)
                        ));
                    }
                }
            }
            if let Some(note) = self.product_note(w.0) {
                why.push(note);
            }
            if let Some(info) = self.w.get_mut(&w.0) {
                info.bound = Some(info.bound.map_or(bits, |b| b.min(bits)));
            }
        }
        // The typed-parameter check is always reported, even when an earlier
        // opcode happens to bound the same witness.
        let raw = if entry || forced {
            Raw::Deterministic
        } else {
            raw
        };
        let mut v = Verdict::new(Kind::Range, label, raw, why);
        v.entry_param = entry;
        self.finish(opcode, op, v)
    }

    fn analyse_blackbox(
        &mut self,
        opcode: usize,
        op: &Opcode<FieldElement>,
        call: &BlackBoxFuncCall<FieldElement>,
    ) -> Item {
        if let BlackBoxFuncCall::RANGE { input, num_bits } = call {
            return self.analyse_range(opcode, op, input, *num_bits);
        }
        let inputs = call.get_inputs_vec();
        let predicate = blackbox_predicate(call);
        let input_taint = inputs.iter().fold(Taint::Input, |t, fi| match fi {
            FunctionInput::Witness(w) => t.join(self.taint(w.0)),
            FunctionInput::Constant(_) => t,
        });
        let (width, out_bits) = blackbox_widths(call);
        let pred_zero = matches!(predicate, Some(FunctionInput::Constant(c)) if c.is_zero());
        let is_logic = matches!(
            call,
            BlackBoxFuncCall::AND { .. } | BlackBoxFuncCall::XOR { .. }
        );

        let mut why = Vec::new();
        let raw = if pred_zero {
            why.push("predicate is the constant 0: the call is skipped".into());
            Raw::Neutralised
        } else if let Some(what) = semantic_failure(call) {
            why.push(what.to_string());
            self.semantic_raw(call, &inputs, predicate, input_taint, &mut why)
        } else if let Some(width) = width {
            self.width_raw(&inputs, predicate, width, is_logic, &mut why)
        } else {
            why.push("defines its outputs; no input condition".into());
            Raw::Definition
        };
        let is_ecdsa = matches!(
            call,
            BlackBoxFuncCall::EcdsaSecp256k1 { .. } | BlackBoxFuncCall::EcdsaSecp256r1 { .. }
        );
        let raw = if is_ecdsa && !pred_zero {
            why.push("backend-defined: witness generation returns false for a bad signature or a malformed key, but the ACIR spec lets the backend fail to prove this opcode when the public key is not on the curve; validate the key before calling if that matters".into());
            if matches!(raw, Raw::Definition) {
                Raw::BackendDefined
            } else {
                raw
            }
        } else {
            raw
        };

        for o in call.get_outputs_vec() {
            let mut info = WInfo::new(input_taint);
            info.bound = out_bits;
            self.assign(o.0, info);
        }
        let kind = if is_logic {
            Kind::Logic
        } else {
            Kind::BlackBox
        };
        let name = call.name().to_string();
        let label = match call.bit_size() {
            Some(b) => format!("{name} {b}"),
            None => name,
        };
        let v = Verdict::new(kind, label, raw, why)
            .predicate(predicate.map(|p| function_input_text(&p)));
        self.finish(opcode, op, v)
    }

    /// Classification of MSM, EC add and recursive aggregation: they can
    /// fail on their input values, so the taint of the inputs decides.
    fn semantic_raw(
        &self,
        call: &BlackBoxFuncCall<FieldElement>,
        inputs: &[FunctionInput<FieldElement>],
        predicate: Option<FunctionInput<FieldElement>>,
        input_taint: Taint,
        why: &mut Vec<String>,
    ) -> Raw {
        if matches!(call, BlackBoxFuncCall::RecursiveAggregation { .. }) {
            why.push(match predicate {
                Some(FunctionInput::Witness(w)) => format!(
                    "predicated on w{}: with it 0 bb proves the circuit whatever the proof bytes; total only if the prover can make it 0 whenever it holds no verifying proof, which the lint does not decide",
                    w.0
                ),
                _ => "unpredicated (constant predicate): every input with a proof that does not verify leaves the circuit unprovable".to_string(),
            });
        }
        let ws: BTreeSet<u32> = inputs
            .iter()
            .filter_map(|fi| match fi {
                FunctionInput::Witness(w) => Some(w.0),
                FunctionInput::Constant(_) => None,
            })
            .collect();
        if input_taint.is_hint() {
            why.push(format!(
                "inputs include hint witnesses: {}",
                self.hint_text(&ws)
            ));
            Raw::Hint
        } else {
            why.push("inputs are computed from inputs only".into());
            Raw::Deterministic
        }
    }

    /// Classification of a black box whose solver requires every input to
    /// fit `width` bits.
    fn width_raw(
        &self,
        inputs: &[FunctionInput<FieldElement>],
        predicate: Option<FunctionInput<FieldElement>>,
        width: u32,
        is_logic: bool,
        why: &mut Vec<String>,
    ) -> Raw {
        let mut worst = Raw::Definition;
        let mut reasons = Vec::new();
        for fi in inputs {
            if Some(*fi) == predicate {
                continue;
            }
            let (r, reason) = self.fits(fi, width);
            if matches!(r, Raw::Hint | Raw::Deterministic | Raw::Unsolvable) && reasons.len() < 3 {
                reasons.push(reason);
            }
            worst = worst.worst(r);
        }
        let raw = match worst {
            Raw::Neutralised | Raw::Implied if !is_logic => Raw::Definition,
            other => other,
        };
        match raw {
            Raw::Definition => why.push(format!(
                "every input is already bounded to {width} bits; the outputs are defined"
            )),
            Raw::Neutralised | Raw::Implied => {
                why.push(format!("every input is already bounded to {width} bits"))
            }
            Raw::HintCompiler => why.push(format!(
                "every input fits {width} bits with the compiler's honest hints"
            )),
            _ => {
                why.push(format!(
                    "the solver requires every input to fit {width} bits"
                ));
                why.extend(reasons);
            }
        }
        raw
    }

    fn analyse_memory_init(
        &mut self,
        opcode: usize,
        op: &Opcode<FieldElement>,
        block_id: u32,
        init: &[Witness],
    ) -> Item {
        let taint = self.join_taint(init.iter().map(|w| w.0));
        let bound = init
            .iter()
            .try_fold(0u32, |m, w| self.bound(w.0).map(|b| m.max(b)));
        self.blocks.insert(
            block_id,
            Block {
                len: init.len() as u32,
                taint,
                bound,
            },
        );
        let why = vec![format!(
            "initialises block b{block_id} with {} elements",
            init.len()
        )];
        self.finish(
            opcode,
            op,
            Verdict::new(Kind::MemoryInit, "INIT", Raw::Definition, why),
        )
    }

    /// Whether the index of a memory access can go out of bounds.
    fn index_raw(&self, b: u32, block: &Block, idx: u32, why: &mut Vec<String>) -> Raw {
        if !self.known(idx) {
            why.push(format!(
                "index {} is not assigned when this opcode runs",
                wname(idx)
            ));
            return Raw::Unsolvable;
        }
        if let Some(c) = self.w[&idx].constant {
            if c.num_bits() <= 32 && c.to_u128() < block.len as u128 {
                why.push(format!(
                    "index is the constant {c}, inside the {}-element block",
                    block.len
                ));
                return Raw::Neutralised;
            }
            why.push(format!(
                "index is the constant {c}, outside the {}-element block: always fails",
                block.len
            ));
            return Raw::Deterministic;
        }
        if let Some(k) = self.bound(idx)
            && k < 32
            && (1u64 << k) <= block.len as u64
        {
            why.push(format!(
                "index {} is bounded below 2^{k} <= {} by earlier opcodes; cannot go out of bounds on its own",
                wname(idx),
                block.len
            ));
            return Raw::Implied;
        }
        why.push(format!(
            "fails when index {} >= {} (block b{b} length)",
            wname(idx),
            block.len
        ));
        if let Some(note) = self.product_note(idx) {
            why.push(note);
        }
        match self.taint(idx) {
            Taint::Hint(h) => {
                why.push(format!("the index depends on {}", self.origin_text(h)));
                Raw::Hint
            }
            Taint::Input => {
                why.push("the index is computed from inputs only".into());
                Raw::Deterministic
            }
        }
    }

    fn analyse_memory_op(
        &mut self,
        opcode: usize,
        op: &Opcode<FieldElement>,
        b: u32,
        mem: &acir::circuit::opcodes::MemOp,
    ) -> Item {
        let idx = mem.index.0;
        let val = mem.value.0;
        let is_read = mem.operation == MemOpKind::Read;
        let (kind, label) = if is_read {
            (Kind::MemoryRead, "READ")
        } else {
            (Kind::MemoryWrite, "WRITE")
        };
        let mut why = Vec::new();
        let Some(block) = self.blocks.get(&b).cloned() else {
            why.push(format!("block b{b} is used before it is initialised"));
            return self.finish(opcode, op, Verdict::new(kind, label, Raw::Unsolvable, why));
        };
        let raw = self.index_raw(b, &block, idx, &mut why);
        let raw = if is_read && self.known(val) {
            // The ACVM compares an assigned read value with the stored
            // element, so the read can fail on the value even when the
            // index is in bounds.
            let t = block.taint.join(self.taint(idx)).join(self.taint(val));
            why.push(format!(
                "the read value {} is already assigned, so the read also checks that it equals the stored element; fails when they differ",
                wname(val)
            ));
            let value_raw = if t.is_hint() {
                why.push("the value or the block depends on hint witnesses".into());
                Raw::Hint
            } else {
                why.push("the value and the block are computed from inputs only".into());
                Raw::Deterministic
            };
            raw.worst(value_raw)
        } else {
            raw
        };
        if is_read {
            if !self.known(val) {
                let mut info = WInfo::new(block.taint.join(self.taint(idx)));
                info.bound = block.bound;
                self.assign(val, info);
            }
        } else {
            let t = block.taint.join(self.taint(val)).join(self.taint(idx));
            let bound = match (block.bound, self.bound(val)) {
                (Some(a), Some(c)) => Some(a.max(c)),
                _ => None,
            };
            self.blocks.insert(
                b,
                Block {
                    len: block.len,
                    taint: t,
                    bound,
                },
            );
        }
        self.finish(opcode, op, Verdict::new(kind, label, raw, why))
    }

    fn analyse_brillig_call(
        &mut self,
        opcode: usize,
        op: &Opcode<FieldElement>,
        out: &mut Analysis,
    ) -> Item {
        let Opcode::BrilligCall {
            id,
            inputs,
            outputs,
            predicate,
        } = op
        else {
            unreachable!("analyse_brillig_call on another opcode");
        };
        let id = id.as_u32();
        let pred_zero = is_const_zero(predicate);
        let mut slot_nonzero = Vec::new();
        for input in inputs {
            match input {
                BrilligInputs::Single(e) => slot_nonzero.push(self.expr_nonzero(e)),
                BrilligInputs::Array(es) => {
                    slot_nonzero.extend(es.iter().map(|e| self.expr_nonzero(e)))
                }
                BrilligInputs::MemoryArray(b) => {
                    let len = self.blocks.get(&b.as_u32()).map(|bl| bl.len).unwrap_or(0);
                    slot_nonzero.extend(std::iter::repeat_n(false, len as usize));
                }
            }
        }
        // Read the directive's inputs before its outputs are assigned.
        let directive = self.directive_call(id, inputs, outputs, predicate);
        let mut n_out = 0;
        for o in outputs {
            let ws: Vec<Witness> = match o {
                BrilligOutputs::Simple(w) => vec![*w],
                BrilligOutputs::Array(ws) => ws.clone(),
            };
            for w in ws {
                n_out += 1;
                let mut info = WInfo::new(Taint::Hint(HintOrigin::Brillig(id)));
                info.direct = true;
                self.assign(w.0, info);
            }
        }
        if let Some(call) = directive {
            self.record_directive(call, outputs);
        }
        let pred_text = predicate_text(predicate);
        out.brillig_calls.push(BrilligCallSite {
            function: self.function,
            opcode,
            callee: id,
            predicate: pred_text.clone(),
            predicate_zero: pred_zero,
            outputs: n_out,
            slot_nonzero,
        });
        let mut why = vec![format!(
            "runs Brillig function {id} ({}) and assigns {n_out} hint witnesses; adds no constraint",
            self.brillig_name(id)
        )];
        let raw = if pred_zero {
            why.push(
                "predicate is the constant 0: the call is skipped and its outputs are zero".into(),
            );
            Raw::Neutralised
        } else {
            Raw::Definition
        };
        let label = format!("BRILLIG {}", self.brillig_name(id));
        self.finish(
            opcode,
            op,
            Verdict::new(Kind::BrilligCall, label, raw, why).predicate(Some(pred_text)),
        )
    }

    fn analyse_call(
        &mut self,
        opcode: usize,
        op: &Opcode<FieldElement>,
        summaries: &HashMap<u32, bool>,
        out: &mut Analysis,
    ) -> Item {
        let Opcode::Call {
            id,
            inputs,
            outputs,
            predicate,
        } = op
        else {
            unreachable!("analyse_call on another opcode");
        };
        let pred_zero = is_const_zero(predicate);
        let returns_hint = summaries.get(&id.as_u32()).copied().unwrap_or(true);
        let mut t = self.join_taint(inputs.iter().map(|w| w.0));
        if returns_hint {
            t = t.join(Taint::Hint(HintOrigin::Call(id.as_u32())));
        }
        for o in outputs {
            self.assign(o.0, WInfo::new(t));
        }
        let pred_text = predicate_text(predicate);
        out.acir_calls.push(AcirCallSite {
            function: self.function,
            opcode,
            callee: id.as_u32(),
            predicate: pred_text.clone(),
            predicate_zero: pred_zero,
        });
        let mut why = vec![format!(
            "calls ACIR function {}; its own opcodes are classified under that function, with its parameters treated as inputs",
            id.as_u32()
        )];
        let raw = if pred_zero {
            why.push("predicate is the constant 0: the call is skipped".into());
            Raw::Neutralised
        } else {
            Raw::Definition
        };
        let label = format!("CALL {}", id.as_u32());
        self.finish(
            opcode,
            op,
            Verdict::new(Kind::Call, label, raw, why).predicate(Some(pred_text)),
        )
    }

    fn analyse(
        &mut self,
        circuit: &Circuit<FieldElement>,
        summaries: &HashMap<u32, bool>,
        out: &mut Analysis,
    ) {
        for (i, op) in circuit.opcodes.iter().enumerate() {
            let item = match op {
                Opcode::AssertZero(e) => self.analyse_assert_zero(i, op, e),
                Opcode::BlackBoxFuncCall(call) => self.analyse_blackbox(i, op, call),
                Opcode::MemoryInit { block_id, init, .. } => {
                    self.analyse_memory_init(i, op, block_id.as_u32(), init)
                }
                Opcode::MemoryOp { block_id, op: mem } => {
                    self.analyse_memory_op(i, op, block_id.as_u32(), mem)
                }
                Opcode::BrilligCall { .. } => self.analyse_brillig_call(i, op, out),
                Opcode::Call { .. } => self.analyse_call(i, op, summaries, out),
            };
            out.items.push(item);
        }
    }

    /// Known nonzero: a nonzero constant, or k*w with w known nonzero.
    fn expr_nonzero(&self, e: &Expression<FieldElement>) -> bool {
        if let Some(c) = e.to_const() {
            return !c.is_zero();
        }
        let n = normalise(e);
        if n.mul.is_empty() && n.lin.len() == 1 && n.c.is_zero() {
            let w = n.lin[0].1;
            return self
                .w
                .get(&w)
                .is_some_and(|i| i.nonzero || i.constant.is_some_and(|c| !c.is_zero()));
        }
        false
    }
}

/// Input width and output width of a black box whose solver requires its
/// inputs to fit a width.
fn blackbox_widths(call: &BlackBoxFuncCall<FieldElement>) -> (Option<u32>, Option<u32>) {
    match call {
        BlackBoxFuncCall::AND { num_bits, .. } | BlackBoxFuncCall::XOR { num_bits, .. } => {
            (Some(*num_bits), Some(*num_bits))
        }
        BlackBoxFuncCall::Blake2s { .. }
        | BlackBoxFuncCall::Blake3 { .. }
        | BlackBoxFuncCall::AES128Encrypt { .. } => (Some(8), Some(8)),
        BlackBoxFuncCall::Sha256Compression { .. } => (Some(32), Some(32)),
        BlackBoxFuncCall::Keccakf1600 { .. } => (Some(64), Some(64)),
        BlackBoxFuncCall::EcdsaSecp256k1 { .. } | BlackBoxFuncCall::EcdsaSecp256r1 { .. } => {
            (Some(8), Some(1))
        }
        _ => (None, None),
    }
}

/// How a black box that can fail on its input values fails.
fn semantic_failure(call: &BlackBoxFuncCall<FieldElement>) -> Option<&'static str> {
    Some(match call {
        BlackBoxFuncCall::MultiScalarMul { .. } => {
            "fails when a point is not on the curve or a scalar limb is out of range"
        }
        BlackBoxFuncCall::EmbeddedCurveAdd { .. } => {
            "fails when an input point is not on the curve"
        }
        BlackBoxFuncCall::RecursiveAggregation { .. } => {
            "backend-defined: the ACVM solver does not check the proof (witness generation succeeds for any proof bytes); the proving backend cannot prove the circuit when the predicate is nonzero and the proof does not verify"
        }
        _ => return None,
    })
}

/// True when the expression is the constant zero after merging terms.
fn is_const_zero(e: &Expression<FieldElement>) -> bool {
    let n = normalise(e);
    n.mul.is_empty() && n.lin.is_empty() && n.c.is_zero()
}

fn blackbox_predicate(
    call: &BlackBoxFuncCall<FieldElement>,
) -> Option<FunctionInput<FieldElement>> {
    match call {
        BlackBoxFuncCall::EcdsaSecp256k1 { predicate, .. }
        | BlackBoxFuncCall::EcdsaSecp256r1 { predicate, .. }
        | BlackBoxFuncCall::MultiScalarMul { predicate, .. }
        | BlackBoxFuncCall::EmbeddedCurveAdd { predicate, .. }
        | BlackBoxFuncCall::RecursiveAggregation { predicate, .. } => Some(*predicate),
        _ => None,
    }
}

/// Classify every opcode of every ACIR function in the program.
pub fn analyse(ctx: &Context) -> Analysis {
    let program = ctx.program;
    let mut out = Analysis::default();
    // Summaries: does function g return hint-tainted witnesses (with its
    // parameters treated as inputs)? Functions are analysed callees first;
    // a call cycle is treated as returning hints.
    let order = call_order(program);
    let mut summaries: HashMap<u32, bool> = HashMap::new();
    let mut per_fn: BTreeMap<usize, Analysis> = BTreeMap::new();
    for f in order {
        let circuit = &program.functions[f];
        let mut a = FnAnalyser {
            ctx,
            function: f,
            w: HashMap::new(),
            blocks: HashMap::new(),
            entry_params: BTreeSet::new(),
            honest: compiler::Facts::default(),
        };
        for w in circuit
            .private_parameters
            .iter()
            .chain(circuit.public_parameters.0.iter())
        {
            a.assign(w.0, WInfo::new(Taint::Input));
        }
        if f == 0 {
            a.entry_params = circuit
                .private_parameters
                .iter()
                .chain(circuit.public_parameters.0.iter())
                .map(|w| w.0)
                .collect();
        }
        let mut fa = Analysis::default();
        a.analyse(circuit, &summaries, &mut fa);
        let returns_hint = circuit
            .return_values
            .0
            .iter()
            .any(|w| a.taint(w.0).is_hint());
        summaries.insert(f as u32, returns_hint);
        per_fn.insert(f, fa);
    }
    for (_, fa) in per_fn {
        out.items.extend(fa.items);
        out.brillig_calls.extend(fa.brillig_calls);
        out.acir_calls.extend(fa.acir_calls);
    }
    out
}

/// Post-order over the ACIR call graph from every function, so callees
/// come before callers where there is no cycle.
fn call_order(program: &Program<FieldElement>) -> Vec<usize> {
    let n = program.functions.len();
    let mut state = vec![0u8; n];
    let mut order = Vec::new();
    fn visit(
        f: usize,
        program: &Program<FieldElement>,
        state: &mut Vec<u8>,
        order: &mut Vec<usize>,
    ) {
        if state[f] != 0 {
            return;
        }
        state[f] = 1;
        for op in &program.functions[f].opcodes {
            if let Opcode::Call { id, .. } = op {
                let g = id.as_usize();
                if g < state.len() {
                    visit(g, program, state, order);
                }
            }
        }
        state[f] = 2;
        order.push(f);
    }
    for f in 0..n {
        visit(f, program, &mut state, &mut order);
    }
    order
}

#[cfg(test)]
mod tests;
