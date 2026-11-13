//! Witness-generation liveness: where Brillig (unconstrained) code can
//! abort.
//!
//! A Brillig function aborts on an explicit Trap (failed assert, overflow
//! check, index bounds check, unreachable code), on division by zero, on
//! a failing curve operation, or on an oracle call the executor cannot
//! answer, or on a radix decomposition (`to_le_bits`, `to_le_bytes` and
//! friends in unconstrained code) whose input needs more limbs than
//! requested. Every abort stops witness generation, so the circuit has no
//! honest witness for that input even if all constraints would hold.
//!
//! Each function is walked from its entry with a small constant
//! propagation (per register: constant, known nonzero, a calldata slot,
//! "is register x zero", or an integer bit width). Branches on known
//! constants follow one side only, so compiler checks such as `64 < 128` before a shift prove their
//! trap unreachable, and `0 < x` on an x known nonzero (the check before
//! an integer remainder, inside an `x == 0` branch's else) is true. A
//! division the walk cannot clear is checked again with a walk that keeps
//! a register's facts across pointer writes and procedure calls that do
//! not write it (walk_relaxed), so a constant divisor hoisted above a
//! rolled loop is still known inside it, and then by naming the divisor
//! from the straight-line code before it (local_nonzero), which clears
//! an operand plus its own is-zero bit, x + (x == 0), through casts that
//! cannot truncate it.
//! Everything else that can abort and is reachable is reported; a
//! reachable site is not proof that some input reaches it.
//!
//! One oracle call is also a hazard for a later reader rather than an
//! abort here: aztec-nr v6's `aztec_prv_notifyCreatedNote` with a packed
//! note wider than MAX_NOTE_PACKED_LEN (note_width). The PXE keeps that
//! pending note, and every later `getNotes` at its storage slot in the
//! same transaction then has an answer wider than the reader's buffer,
//! which the PXE refuses: an honest reader fails. Such a call is a
//! second site, of kind note-width, beside its ordinary oracle site.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

use acir::brillig::{
    BinaryFieldOp, BinaryIntOp, BitSize, BlackBoxOp, HeapValueType, MemoryAddress, Opcode as BOp,
    ValueOrArray,
};
use acir::{AcirField, FieldElement};

use crate::analysis::BrilligCallSite;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TrapKind {
    /// An explicit Trap opcode.
    Trap,
    DivisionByZero,
    CurveOperation,
    Oracle,
    /// Radix decomposition into too few limbs.
    Radix,
    /// aztec-nr v6's `aztec_prv_notifyCreatedNote` with a packed note
    /// wider than MAX_NOTE_PACKED_LEN: the PXE then refuses later reads of
    /// its storage slot in the same transaction (see note_width).
    NoteWidth,
}

impl TrapKind {
    pub fn name(self) -> &'static str {
        match self {
            TrapKind::Trap => "trap",
            TrapKind::DivisionByZero => "division",
            TrapKind::CurveOperation => "curve-op",
            TrapKind::Oracle => "oracle",
            TrapKind::Radix => "radix",
            TrapKind::NoteWidth => "note-width",
        }
    }

    /// Whether a site of this kind in library code is whitelisted. A
    /// note-width site is not: it fails a reader of the note, not this
    /// function, so the library's own abort-freedom review does not cover
    /// it.
    pub fn whitelisted_in_library(self) -> bool {
        self != TrapKind::NoteWidth
    }
}

/// The aztec-nr v6 PXE oracle that records a pending note
/// (aztec-nr/aztec/src/oracle/notes.nr, `notify_created_note_oracle`):
/// arguments owner, storage slot, randomness, note type id, packed note
/// (`[Field; N]`), note hash, counter.
pub const NOTIFY_CREATED_NOTE: &str = "aztec_prv_notifyCreatedNote";

/// aztec-nr v6.0.0's MAX_NOTE_PACKED_LEN (aztec/src/messages/logs/note.nr:
/// MAX_MESSAGE_CONTENT_LEN - PRIVATE_NOTE_MSG_PLAINTEXT_RESERVED_FIELDS_LEN
/// = 11 - 3). MAX_MESSAGE_CONTENT_LEN (messages/encoding.nr) is
/// MESSAGE_PLAINTEXT_LEN - MESSAGE_EXPANDED_METADATA_LEN = 12 - 1, with
/// MESSAGE_PLAINTEXT_LEN = ((PRIVATE_LOG_CIPHERTEXT_LEN - 1) * 31 - 16 - 16)
/// / 32 = (14 * 31 - 32) / 32 = 12, and PRIVATE_LOG_CIPHERTEXT_LEN =
/// PRIVATE_LOG_SIZE_IN_FIELDS - 1 = 15 (protocol types constants.nr).
pub const MAX_NOTE_PACKED_LEN: u64 = 8;

#[derive(Clone, Debug)]
pub struct TrapSite {
    pub brillig: u32,
    pub function_name: String,
    pub pc: usize,
    pub kind: TrapKind,
    /// Assertion message, when the revert data names an ABI error.
    pub message: Option<String>,
    /// Brillig pc whose debug location describes this site (the site
    /// itself, or the call into the procedure that contains it).
    pub location_pc: Option<usize>,
    /// The divisor is calldata slot j and every call site passes a value
    /// an ACIR constraint forces nonzero.
    pub guarded_by_callers: bool,
    pub detail: String,
}

#[derive(Clone, Debug, Default)]
pub struct FunctionStats {
    pub opcodes: usize,
    pub reachable: usize,
    pub traps_total: usize,
    pub traps_unreachable: usize,
}

#[derive(Clone, Debug, Default)]
pub struct BrilligReport {
    pub sites: Vec<TrapSite>,
    pub stats: BTreeMap<u32, FunctionStats>,
}

type Addr = (bool, u32);

fn addr(a: &MemoryAddress) -> Addr {
    match a {
        MemoryAddress::Direct(x) => (false, *x),
        MemoryAddress::Relative(x) => (true, *x),
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Val {
    Const(FieldElement),
    NonZero,
    Calldata(u32),
    /// Boolean: "the value at this address is zero".
    EqZero(Addr),
    /// An integer-typed value, or a field cast from one: below 2^bits.
    Bits(u32),
}

type State = BTreeMap<Addr, Val>;

fn write(state: &mut State, dest: Addr, v: Option<Val>) {
    state.retain(|_, val| *val != Val::EqZero(dest));
    if dest == (false, 0) {
        // @0 is the stack pointer: relative facts no longer apply.
        state.retain(|k, _| !k.0);
    }
    match v {
        Some(v) => {
            state.insert(dest, v);
        }
        None => {
            state.remove(&dest);
        }
    }
}

fn konst(state: &State, a: &MemoryAddress) -> Option<FieldElement> {
    match state.get(&addr(a)) {
        Some(Val::Const(c)) => Some(*c),
        _ => None,
    }
}

fn int_value(c: FieldElement) -> Option<u128> {
    if c.num_bits() <= 128 {
        Some(c.to_u128())
    } else {
        None
    }
}

fn fbool(b: bool) -> FieldElement {
    if b {
        FieldElement::one()
    } else {
        FieldElement::zero()
    }
}

fn compare(
    op_eq: bool,
    op_lt: bool,
    op_le: bool,
    a: FieldElement,
    b: FieldElement,
) -> Option<FieldElement> {
    if op_eq {
        return Some(fbool(a == b));
    }
    let (x, y) = (int_value(a)?, int_value(b)?);
    if op_lt {
        return Some(fbool(x < y));
    }
    if op_le {
        return Some(fbool(x <= y));
    }
    None
}

/// Wrap an integer to `bits` bits.
fn wrap(x: u128, bits: u32) -> u128 {
    if bits >= 128 {
        x
    } else {
        x & ((1u128 << bits) - 1)
    }
}

fn step_cast(s: &State, source: &MemoryAddress, bit_size: &BitSize) -> Option<Val> {
    match (konst(s, source), bit_size) {
        (Some(c), BitSize::Field) => Some(Val::Const(c)),
        (Some(c), BitSize::Integer(b)) => {
            int_value(c).map(|x| Val::Const(FieldElement::from(wrap(x, u32::from(*b)))))
        }
        // A cast to Field keeps the value, so an integer width carries over.
        (None, BitSize::Field) => match s.get(&addr(source)) {
            Some(Val::Bits(b)) => Some(Val::Bits(*b)),
            _ => None,
        },
        (None, BitSize::Integer(b)) => Some(Val::Bits(u32::from(*b))),
    }
}

/// `x == 0` with one side the constant zero is the is-zero test of the
/// other side.
fn eq_value(
    a: Option<FieldElement>,
    b: Option<FieldElement>,
    lhs: &MemoryAddress,
    rhs: &MemoryAddress,
) -> Option<Val> {
    match (a, b) {
        (Some(x), Some(y)) => Some(Val::Const(fbool(x == y))),
        (Some(x), None) if x.is_zero() => Some(Val::EqZero(addr(rhs))),
        (None, Some(y)) if y.is_zero() => Some(Val::EqZero(addr(lhs))),
        _ => None,
    }
}

fn step_field_op(
    s: &State,
    op: &BinaryFieldOp,
    lhs: &MemoryAddress,
    rhs: &MemoryAddress,
) -> Option<Val> {
    let (a, b) = (konst(s, lhs), konst(s, rhs));
    match op {
        BinaryFieldOp::Equals => eq_value(a, b, lhs, rhs),
        BinaryFieldOp::LessThan | BinaryFieldOp::LessThanEquals => {
            let (x, y) = (a?, b?);
            compare(
                false,
                *op == BinaryFieldOp::LessThan,
                *op == BinaryFieldOp::LessThanEquals,
                x,
                y,
            )
            .map(Val::Const)
        }
        BinaryFieldOp::Add => a.zip(b).map(|(x, y)| Val::Const(x + y)),
        BinaryFieldOp::Sub => a.zip(b).map(|(x, y)| Val::Const(x - y)),
        BinaryFieldOp::Mul => a.zip(b).map(|(x, y)| Val::Const(x * y)),
        _ => None,
    }
}

fn step_int_op(
    s: &State,
    op: &BinaryIntOp,
    bits: u32,
    lhs: &MemoryAddress,
    rhs: &MemoryAddress,
) -> Option<Val> {
    let (a, b) = (konst(s, lhs), konst(s, rhs));
    let v = match op {
        BinaryIntOp::Equals => eq_value(a, b, lhs, rhs),
        BinaryIntOp::LessThan | BinaryIntOp::LessThanEquals => match (a, b) {
            (Some(x), Some(y)) => compare(
                false,
                *op == BinaryIntOp::LessThan,
                *op == BinaryIntOp::LessThanEquals,
                x,
                y,
            )
            .map(Val::Const),
            // Unsigned 0 < x for an x known nonzero: the check Noir puts
            // before an integer remainder.
            (Some(x), None)
                if x.is_zero()
                    && *op == BinaryIntOp::LessThan
                    && s.get(&addr(rhs)).is_some_and(is_nonzero) =>
            {
                Some(Val::Const(FieldElement::one()))
            }
            _ => None,
        },
        BinaryIntOp::Add | BinaryIntOp::Sub | BinaryIntOp::Mul => {
            let (x, y) = (a.and_then(int_value)?, b.and_then(int_value)?);
            let r = match op {
                BinaryIntOp::Add => x.wrapping_add(y),
                BinaryIntOp::Sub => x.wrapping_sub(y),
                _ => x.wrapping_mul(y),
            };
            Some(Val::Const(FieldElement::from(wrap(r, bits))))
        }
        _ => None,
    };
    // Integer results always fit their bit size (comparisons give u1).
    v.or(Some(Val::Bits(match op {
        BinaryIntOp::Equals | BinaryIntOp::LessThan | BinaryIntOp::LessThanEquals => 1,
        _ => bits,
    })))
}

/// CalldataCopy of `size` slots from `offset`: each register names its
/// slot. Unknown sizes, or addresses past u32::MAX, forget every fact.
fn step_calldata(
    s: &mut State,
    dest: &MemoryAddress,
    size: &MemoryAddress,
    offset: &MemoryAddress,
) {
    let (Some(size), Some(offset)) = (
        konst(s, size).and_then(int_value),
        konst(s, offset).and_then(int_value),
    ) else {
        s.clear();
        return;
    };
    if size > 4096 {
        s.clear();
        return;
    }
    let (rel, base) = addr(dest);
    for i in 0..size as u32 {
        let (Some(d), Some(slot)) = (
            base.checked_add(i),
            u32::try_from(offset).ok().and_then(|o| o.checked_add(i)),
        ) else {
            s.clear();
            return;
        };
        write(s, (rel, d), Some(Val::Calldata(slot)));
    }
}

fn step_jump_if(
    pc: usize,
    s: State,
    condition: &MemoryAddress,
    location: usize,
) -> Vec<(usize, State)> {
    match s.get(&addr(condition)).cloned() {
        Some(Val::Const(c)) if c.is_zero() => vec![(pc + 1, s)],
        Some(Val::Const(_)) => vec![(location, s)],
        Some(Val::EqZero(x)) => {
            let mut taken = s.clone();
            write(&mut taken, x, Some(Val::Const(FieldElement::zero())));
            let mut fall = s;
            fall.insert(x, Val::NonZero);
            vec![(location, taken), (pc + 1, fall)]
        }
        _ => vec![(location, s.clone()), (pc + 1, s)],
    }
}

/// Successor pcs with their states.
fn step(pc: usize, op: &BOp<FieldElement>, pre: &State) -> Vec<(usize, State)> {
    let mut s = pre.clone();
    match op {
        BOp::Const {
            destination, value, ..
        } => write(&mut s, addr(destination), Some(Val::Const(*value))),
        BOp::IndirectConst { .. }
        | BOp::Store { .. }
        | BOp::BlackBox(_)
        | BOp::ForeignCall { .. } => s.clear(),
        BOp::Mov {
            destination,
            source,
        } => {
            let v = s.get(&addr(source)).cloned();
            write(&mut s, addr(destination), v);
        }
        BOp::ConditionalMov {
            destination,
            source_a,
            source_b,
            condition,
        } => {
            let (a, b) = (
                s.get(&addr(source_a)).cloned(),
                s.get(&addr(source_b)).cloned(),
            );
            let v = match konst(&s, condition) {
                Some(c) if !c.is_zero() => a,
                Some(_) => b,
                None if a == b => a,
                None => None,
            };
            write(&mut s, addr(destination), v);
        }
        BOp::Load { destination, .. } => write(&mut s, addr(destination), None),
        BOp::Not {
            destination,
            bit_size,
            ..
        } => write(
            &mut s,
            addr(destination),
            Some(Val::Bits(u32::from(*bit_size))),
        ),
        BOp::Cast {
            destination,
            source,
            bit_size,
        } => {
            let v = step_cast(&s, source, bit_size);
            write(&mut s, addr(destination), v);
        }
        BOp::BinaryFieldOp {
            destination,
            op,
            lhs,
            rhs,
        } => {
            let v = step_field_op(&s, op, lhs, rhs);
            write(&mut s, addr(destination), v);
        }
        BOp::BinaryIntOp {
            destination,
            op,
            bit_size,
            lhs,
            rhs,
        } => {
            let v = step_int_op(&s, op, u32::from(*bit_size), lhs, rhs);
            write(&mut s, addr(destination), v);
        }
        BOp::CalldataCopy {
            destination_address,
            size_address,
            offset_address,
        } => step_calldata(&mut s, destination_address, size_address, offset_address),
        BOp::Jump { location } => return vec![(*location, s)],
        BOp::JumpIf {
            condition,
            location,
        } => return step_jump_if(pc, s, condition, *location),
        BOp::Call { location } => {
            // The callee may clobber anything; continue after it with no facts.
            return vec![(*location, s), (pc + 1, State::new())];
        }
        BOp::Return | BOp::Trap { .. } | BOp::Stop { .. } => return vec![],
    }
    vec![(pc + 1, s)]
}

fn intersect(a: &State, b: &State) -> State {
    a.iter()
        .filter(|(k, v)| b.get(k) == Some(v))
        .map(|(k, v)| (*k, v.clone()))
        .collect()
}

/// Reachable pcs with the facts that hold before each.
fn walk(code: &[BOp<FieldElement>]) -> Vec<Option<State>> {
    walk_impl(code, false)
}

/// Register addresses `op` writes, besides heap memory reached through a
/// pointer; None when it may write any (a CalldataCopy, or a write to @0,
/// which moves every relative address). Call is handled by callee_writes.
fn reg_writes(op: &BOp<FieldElement>) -> Option<Vec<Addr>> {
    let one = |a: &MemoryAddress| {
        let a = addr(a);
        if a == (false, 0) { None } else { Some(vec![a]) }
    };
    match op {
        BOp::Const { destination, .. }
        | BOp::Mov { destination, .. }
        | BOp::ConditionalMov { destination, .. }
        | BOp::Load { destination, .. }
        | BOp::Not { destination, .. }
        | BOp::Cast { destination, .. }
        | BOp::BinaryFieldOp { destination, .. }
        | BOp::BinaryIntOp { destination, .. } => one(destination),
        BOp::BlackBox(
            BlackBoxOp::EcdsaSecp256k1 { result, .. } | BlackBoxOp::EcdsaSecp256r1 { result, .. },
        ) => one(result),
        // The other black boxes write only through their output pointers.
        BOp::BlackBox(_) => Some(vec![]),
        BOp::ForeignCall { destinations, .. } => {
            let mut w = Vec::new();
            for dest in destinations {
                match dest {
                    ValueOrArray::MemoryAddress(a) => w.push(addr(a)),
                    ValueOrArray::HeapArray(h) => w.push(addr(&h.pointer)),
                    ValueOrArray::HeapVector(v) => {
                        w.push(addr(&v.pointer));
                        w.push(addr(&v.size));
                    }
                }
            }
            if w.contains(&(false, 0)) {
                None
            } else {
                Some(w)
            }
        }
        BOp::CalldataCopy { .. } => None,
        BOp::IndirectConst { .. }
        | BOp::Store { .. }
        | BOp::Jump { .. }
        | BOp::JumpIf { .. }
        | BOp::Call { .. }
        | BOp::Return
        | BOp::Trap { .. }
        | BOp::Stop { .. } => Some(vec![]),
    }
}

/// Every register address the procedure entered at `entry` may write,
/// through the procedures it calls as well; None when it may write any
/// (see reg_writes) or recurses.
fn callee_writes(
    code: &[BOp<FieldElement>],
    entry: usize,
    memo: &mut BTreeMap<usize, Option<BTreeSet<Addr>>>,
    active: &mut BTreeSet<usize>,
) -> Option<BTreeSet<Addr>> {
    if let Some(w) = memo.get(&entry) {
        return w.clone();
    }
    if !active.insert(entry) {
        return None;
    }
    let mut writes = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut todo = vec![entry];
    let mut result = Some(());
    while let Some(pc) = todo.pop() {
        if pc >= code.len() || !seen.insert(pc) {
            continue;
        }
        let op = &code[pc];
        match op {
            BOp::Return | BOp::Trap { .. } | BOp::Stop { .. } => continue,
            BOp::Jump { location } => {
                todo.push(*location);
                continue;
            }
            BOp::JumpIf { location, .. } => todo.push(*location),
            BOp::Call { location } => match callee_writes(code, *location, memo, active) {
                Some(w) => writes.extend(w),
                None => {
                    result = None;
                    break;
                }
            },
            _ => match reg_writes(op) {
                Some(w) => writes.extend(w),
                None => {
                    result = None;
                    break;
                }
            },
        }
        todo.push(pc + 1);
    }
    active.remove(&entry);
    let w = result.map(|_| writes);
    memo.insert(entry, w.clone());
    w
}

/// Like walk, but keeps a register's facts across the opcodes that do not
/// write it: a pointer write (IndirectConst, Store), a black box or oracle
/// call other than on its register outputs, and a call into a procedure
/// that does not write it (callee_writes). Pointer writes are taken to hit
/// heap allocations, never registers, as in compiler output (local_sym
/// makes the same assumption). Where two paths meet, a register nonzero on
/// both stays known nonzero. A constant hoisted above a loop whose body
/// stores or calls a procedure thus stays known at the loop header. Used
/// only to clear divisions the plain walk cannot.
fn walk_relaxed(code: &[BOp<FieldElement>]) -> Vec<Option<State>> {
    walk_impl(code, true)
}

fn is_nonzero(v: &Val) -> bool {
    match v {
        Val::Const(c) => !c.is_zero(),
        Val::NonZero => true,
        _ => false,
    }
}

fn walk_impl(code: &[BOp<FieldElement>], relaxed: bool) -> Vec<Option<State>> {
    let mut memo = BTreeMap::new();
    let mut states: Vec<Option<State>> = vec![None; code.len()];
    if code.is_empty() {
        return states;
    }
    states[0] = Some(State::new());
    let mut work = vec![0usize];
    let mut budget = 200_000usize.max(code.len() * 64);
    while let Some(pc) = work.pop() {
        if budget == 0 {
            // Give up on precision: everything not yet seen is reachable
            // with no facts.
            for s in states.iter_mut() {
                if s.is_none() {
                    *s = Some(State::new());
                }
            }
            break;
        }
        budget -= 1;
        let Some(pre) = states[pc].clone() else {
            continue;
        };
        let mut succs = step(pc, &code[pc], &pre);
        if relaxed {
            // The state after the opcode, when only its own writes change it.
            let kept = |w: Option<Vec<Addr>>| {
                w.map(|w| {
                    let mut s = pre.clone();
                    for a in w {
                        write(&mut s, a, None);
                    }
                    s
                })
            };
            match &code[pc] {
                op @ (BOp::IndirectConst { .. }
                | BOp::Store { .. }
                | BOp::BlackBox(_)
                | BOp::ForeignCall { .. }) => {
                    if let (Some(s), Some(succ)) = (kept(reg_writes(op)), succs.first_mut()) {
                        succ.1 = s;
                    }
                }
                BOp::Call { location } => {
                    let w = callee_writes(code, *location, &mut memo, &mut BTreeSet::new());
                    if let (Some(s), Some(succ)) = (kept(w.map(Vec::from_iter)), succs.get_mut(1)) {
                        succ.1 = s;
                    }
                }
                _ => {}
            }
        }
        for (succ, st) in succs {
            if succ >= code.len() {
                continue;
            }
            let merged = match &states[succ] {
                None => st,
                Some(old) if relaxed => old
                    .iter()
                    .filter_map(|(k, v)| match st.get(k) {
                        Some(w) if w == v => Some((*k, v.clone())),
                        Some(w) if is_nonzero(v) && is_nonzero(w) => Some((*k, Val::NonZero)),
                        _ => None,
                    })
                    .collect(),
                Some(old) => intersect(old, &st),
            };
            if states[succ].as_ref() != Some(&merged) {
                states[succ] = Some(merged);
                work.push(succ);
            }
        }
    }
    states
}

fn trap_message(
    code: &[BOp<FieldElement>],
    pc: usize,
    selectors: &BTreeMap<u64, String>,
) -> Option<String> {
    for back in 1..=4 {
        let i = pc.checked_sub(back)?;
        let value = match &code[i] {
            BOp::IndirectConst { value, .. } | BOp::Const { value, .. } => *value,
            _ => continue,
        };
        if let Some(sel) = value.try_to_u64()
            && let Some(m) = selectors.get(&sel)
        {
            return Some(m.clone());
        }
    }
    None
}

/// A value in straight-line code, named by how it was computed (see
/// local_nonzero). Two reads that name the same Sym hold the same value:
/// the region has no jump target inside it, so no opcode in it runs twice
/// between them.
#[derive(Clone, Debug, PartialEq)]
enum Sym {
    /// The register's value where the region begins (pc of its start).
    Entry(Addr, usize),
    /// The value an opcode not modelled here wrote at this pc, with its
    /// integer width when the opcode fixes one.
    At(usize, Option<u32>),
    Const(FieldElement),
    /// An integer cast that may truncate: the value mod 2^bits.
    Trunc(u32, Box<Sym>),
    /// 1 when the value is zero, else 0.
    IsZero(Box<Sym>),
    /// A sum, in the field or of integers (an integer sum sits under the
    /// Trunc of its width unless it provably fits).
    Add(Box<Sym>, Box<Sym>),
}

/// x + (x == 0), either way round: x itself when x is nonzero, 1 when it
/// is zero, so never zero, in the field and as an integer. The operand x.
fn plus_own_is_zero(e: &Sym) -> Option<&Sym> {
    let Sym::Add(l, r) = e else { return None };
    match (&**l, &**r) {
        (x, Sym::IsZero(y)) | (Sym::IsZero(y), x) if x == &**y => Some(x),
        _ => None,
    }
}

/// Bits that bound the value (it is below 2^bits), when known.
fn sym_bits(e: &Sym) -> Option<u32> {
    match e {
        Sym::Const(c) => Some(c.num_bits()),
        Sym::Trunc(bits, _) => Some(*bits),
        Sym::IsZero(_) => Some(1),
        Sym::At(_, bits) => *bits,
        // x < 2^b, and x + (x == 0) is x or 1: below 2^b for b >= 1
        Sym::Add(..) => plus_own_is_zero(e).and_then(sym_bits).map(|b| b.max(1)),
        Sym::Entry(..) => None,
    }
}

fn sym_nonzero(e: &Sym) -> bool {
    match e {
        Sym::Const(c) => !c.is_zero(),
        _ => plus_own_is_zero(e).is_some(),
    }
}

/// The value cast or wrapped to `bits` bits: itself when it provably fits.
fn sym_trunc(bits: u32, e: Sym) -> Sym {
    if sym_bits(&e).is_some_and(|b| b <= bits) {
        e
    } else {
        Sym::Trunc(bits, Box::new(e))
    }
}

/// Name the value in `a` just before `pc` by walking back through the
/// straight-line code before it, to the nearest jump target. Pointer
/// writes (IndirectConst, Store) are taken not to hit registers, as in
/// compiler output, where they target heap allocations. None where an
/// opcode may write registers it does not name (a procedure call, a
/// CalldataCopy, a write to the stack pointer). Each register looked up
/// spends one unit of `budget`; an operand looked up with none left is
/// named by the opcode that uses it, so nothing is lost but precision.
fn local_sym(
    code: &[BOp<FieldElement>],
    pc: usize,
    a: &MemoryAddress,
    jump_targets: &BTreeSet<usize>,
    budget: &Cell<u32>,
) -> Option<Sym> {
    let target = addr(a);
    let mut i = pc;
    loop {
        if i == 0 || jump_targets.contains(&i) {
            return Some(Sym::Entry(target, i));
        }
        i -= 1;
        let op = &code[i];
        match op {
            BOp::JumpIf { .. } | BOp::IndirectConst { .. } | BOp::Store { .. } => continue,
            BOp::Jump { .. }
            | BOp::Call { .. }
            | BOp::Return
            | BOp::Trap { .. }
            | BOp::Stop { .. } => return None,
            _ => {}
        }
        let writes = reg_writes(op)?;
        if !writes.contains(&target) {
            continue;
        }
        let sub = |x: &MemoryAddress| {
            let left = budget.get().checked_sub(1)?;
            budget.set(left);
            local_sym(code, i, x, jump_targets, budget)
        };
        let eq_zero = |l: &MemoryAddress, r: &MemoryAddress| match (sub(l), sub(r)) {
            (Some(Sym::Const(c)), Some(x)) | (Some(x), Some(Sym::Const(c))) if c.is_zero() => {
                Some(Sym::IsZero(Box::new(x)))
            }
            _ => None,
        };
        let at = |bits: Option<u32>| Some(Sym::At(i, bits));
        return match op {
            BOp::Const { value, .. } => Some(Sym::Const(*value)),
            BOp::Mov { source, .. } => sub(source).or_else(|| at(None)),
            BOp::Cast {
                source, bit_size, ..
            } => match (sub(source), bit_size) {
                (Some(e), BitSize::Field) => Some(e),
                (Some(e), BitSize::Integer(b)) => Some(sym_trunc(u32::from(*b), e)),
                (None, BitSize::Field) => at(None),
                (None, BitSize::Integer(b)) => at(Some(u32::from(*b))),
            },
            BOp::BinaryFieldOp { op, lhs, rhs, .. } => match op {
                BinaryFieldOp::Equals => eq_zero(lhs, rhs).or_else(|| at(Some(1))),
                BinaryFieldOp::LessThan | BinaryFieldOp::LessThanEquals => at(Some(1)),
                BinaryFieldOp::Add => match (sub(lhs), sub(rhs)) {
                    (Some(l), Some(r)) => Some(Sym::Add(Box::new(l), Box::new(r))),
                    _ => at(None),
                },
                _ => at(None),
            },
            BOp::BinaryIntOp {
                op,
                bit_size,
                lhs,
                rhs,
                ..
            } => {
                let bits = u32::from(*bit_size);
                match op {
                    BinaryIntOp::Equals => eq_zero(lhs, rhs).or_else(|| at(Some(1))),
                    BinaryIntOp::LessThan | BinaryIntOp::LessThanEquals => at(Some(1)),
                    // wraps mod 2^bits
                    BinaryIntOp::Add => match (sub(lhs), sub(rhs)) {
                        (Some(l), Some(r)) => {
                            Some(sym_trunc(bits, Sym::Add(Box::new(l), Box::new(r))))
                        }
                        _ => at(Some(bits)),
                    },
                    _ => at(Some(bits)),
                }
            }
            BOp::Not { bit_size, .. } => at(Some(u32::from(*bit_size))),
            _ => at(None),
        };
    }
}

/// Whether the value in `a` just before `pc` is nonzero by how the
/// straight-line code before it computed it: a constant, or an operand
/// plus its own is-zero bit, x + (x == 0), through casts that cannot
/// truncate it (a hint's divisor made nonzero without a branch, as in
/// `let d = ((b as Field) + ((b == 0) as Field)) as u128`).
fn local_nonzero(
    code: &[BOp<FieldElement>],
    pc: usize,
    a: &MemoryAddress,
    jump_targets: &BTreeSet<usize>,
) -> bool {
    local_sym(code, pc, a, jump_targets, &Cell::new(64)).is_some_and(|e| sym_nonzero(&e))
}

/// Why a ToRadix at `pc` can abort, or None when it cannot: the VM fails
/// when the input does not fit `num_limbs` limbs of base `radix`.
fn radix_risk(
    code: &[BOp<FieldElement>],
    pc: usize,
    pre: &State,
    input: &MemoryAddress,
    radix: &MemoryAddress,
    num_limbs: &MemoryAddress,
    jump_targets: &BTreeSet<usize>,
) -> Option<String> {
    let val = |a: &MemoryAddress| {
        pre.get(&addr(a)).cloned().or_else(|| {
            let sym = local_sym(code, pc, a, jump_targets, &Cell::new(8))?;
            match sym {
                Sym::Const(c) => Some(Val::Const(c)),
                other => sym_bits(&other).map(Val::Bits),
            }
        })
    };
    let known = |a: &MemoryAddress| match val(a) {
        Some(Val::Const(c)) => int_value(c),
        _ => None,
    };
    let (Some(r), Some(n)) = (known(radix), known(num_limbs)) else {
        return Some(
            "limb count or radix not known; aborts when the input needs more limbs".into(),
        );
    };
    if !(2..=256).contains(&r) {
        return Some(format!("radix {r} is outside 2..=256: the VM rejects it"));
    }
    // r^n >= 2^(n * floor(log2 r)); the input fits when its width is at most that.
    let capacity = n.saturating_mul(127 - r.leading_zeros() as u128);
    let input_bits = match val(input) {
        Some(Val::Const(c)) => c.num_bits() as u128,
        Some(Val::Bits(b)) => b as u128,
        _ => FieldElement::max_num_bits() as u128,
    };
    if capacity >= input_bits {
        return None;
    }
    let width = if input_bits >= FieldElement::max_num_bits() as u128 {
        "input width not known".to_string()
    } else {
        format!("input known below 2^{input_bits}")
    };
    Some(format!(
        "{n} limbs of radix {r} hold {capacity} bits; aborts when the input needs more ({width})"
    ))
}

/// Brillig pc whose debug location describes `pc`: the pc itself when the
/// debug info knows it, else the located call into the procedure that
/// contains it, else the nearest located pc before it.
fn locate(
    code: &[BOp<FieldElement>],
    states: &[Option<State>],
    id: u32,
    pc: usize,
    has_location: &dyn Fn(u32, usize) -> bool,
) -> Option<usize> {
    if has_location(id, pc) {
        return Some(pc);
    }
    let call_targets: BTreeSet<usize> = code
        .iter()
        .enumerate()
        .filter(|(pc, _)| states[*pc].is_some())
        .filter_map(|(_, op)| {
            if let BOp::Call { location } = op {
                Some(*location)
            } else {
                None
            }
        })
        .collect();
    if let Some(&entry) = call_targets.range(..=pc).next_back() {
        for (cpc, op) in code.iter().enumerate() {
            if matches!(op, BOp::Call { location } if *location == entry)
                && states[cpc].is_some()
                && has_location(id, cpc)
            {
                return Some(cpc);
            }
        }
    }
    (0..pc).rev().find(|p| has_location(id, *p))
}

/// Whether every call site passes a divisor argument (calldata slot j) an
/// ACIR constraint or a constant makes nonzero, and the site's detail.
fn argument_divisor(j: usize, calls: &[&BrilligCallSite]) -> (bool, String) {
    let guarded = !calls.is_empty()
        && calls
            .iter()
            .all(|c| c.slot_nonzero.get(j).copied().unwrap_or(false));
    let detail = if guarded {
        format!(
            "divides by argument {j}; every call site passes a constant or a value an earlier ACIR constraint forces nonzero"
        )
    } else {
        format!("divides by argument {j}; aborts when a caller passes zero")
    };
    (guarded, detail)
}

/// One Brillig function being scanned for abort sites.
struct FunctionScan<'c> {
    code: &'c [BOp<FieldElement>],
    states: Vec<Option<State>>,
    /// Built on demand: the walk that keeps facts across pointer writes.
    relaxed: Option<Vec<Option<State>>>,
    jump_targets: BTreeSet<usize>,
    /// The call sites that run this function.
    calls: Vec<&'c BrilligCallSite>,
}

impl FunctionScan<'_> {
    /// Why a division at `pc` by the value in `rhs` can abort, with
    /// whether every caller guards it; None when it cannot.
    fn division(&mut self, pc: usize, pre: &State, rhs: &MemoryAddress) -> Option<(String, bool)> {
        match pre.get(&addr(rhs)) {
            Some(Val::Const(c)) if !c.is_zero() => return None,
            Some(Val::NonZero) => return None,
            Some(Val::Calldata(j)) => {
                let (guarded, detail) = argument_divisor(*j as usize, &self.calls);
                return Some((detail, guarded));
            }
            _ => {}
        }
        let code = self.code;
        let relaxed = self.relaxed.get_or_insert_with(|| walk_relaxed(code));
        let fact = relaxed[pc].as_ref().and_then(|s| s.get(&addr(rhs)));
        if let Some(Val::Calldata(j)) = fact {
            let (guarded, detail) = argument_divisor(*j as usize, &self.calls);
            return Some((detail, guarded));
        }
        if fact.is_some_and(is_nonzero) || local_nonzero(code, pc, rhs, &self.jump_targets) {
            return None;
        }
        Some(("divisor not known nonzero".into(), false))
    }

    /// The abort site at a reachable `pc`: (kind, detail, guarded, message).
    fn site(
        &mut self,
        pc: usize,
        pre: &State,
        selectors: &BTreeMap<u64, String>,
    ) -> Option<(TrapKind, String, bool, Option<String>)> {
        let code = self.code;
        match &code[pc] {
            BOp::Trap { .. } => Some((
                TrapKind::Trap,
                "explicit trap".into(),
                false,
                trap_message(code, pc, selectors),
            )),
            BOp::BinaryIntOp {
                op: BinaryIntOp::Div,
                rhs,
                ..
            }
            | BOp::BinaryFieldOp {
                op: BinaryFieldOp::Div | BinaryFieldOp::IntegerDiv,
                rhs,
                ..
            } => self
                .division(pc, pre, rhs)
                .map(|(detail, guarded)| (TrapKind::DivisionByZero, detail, guarded, None)),
            BOp::BlackBox(
                BlackBoxOp::MultiScalarMul { .. } | BlackBoxOp::EmbeddedCurveAdd { .. },
            ) => Some((
                TrapKind::CurveOperation,
                "fails on points not on the curve".into(),
                false,
                None,
            )),
            BOp::ForeignCall { function, .. } if function != "print" => Some((
                TrapKind::Oracle,
                format!("oracle {function:?}: depends on the executor"),
                false,
                None,
            )),
            BOp::BlackBox(BlackBoxOp::ToRadix {
                input,
                radix,
                num_limbs,
                ..
            }) => radix_risk(code, pc, pre, input, radix, num_limbs, &self.jump_targets)
                .map(|detail| (TrapKind::Radix, detail, false, None)),
            _ => None,
        }
    }

    /// Why a reachable `pc` is a note-width site (see note_width), or None.
    fn note_width_site(&self, pc: usize, pre: &State) -> Option<String> {
        let BOp::ForeignCall {
            function,
            inputs,
            input_value_types,
            ..
        } = &self.code[pc]
        else {
            return None;
        };
        if function != NOTIFY_CREATED_NOTE {
            return None;
        }
        let size = |a: &MemoryAddress| {
            konst(pre, a).or_else(|| {
                match local_sym(self.code, pc, a, &self.jump_targets, &Cell::new(8))? {
                    Sym::Const(c) => Some(c),
                    _ => None,
                }
            })
        };
        note_width(inputs, input_value_types, size)
    }
}

/// Fields one value of this type occupies; None for a vector, whose
/// length is only known at run time.
fn flat_width(t: &HeapValueType) -> Option<u64> {
    match t {
        HeapValueType::Simple(_) => Some(1),
        HeapValueType::Array { value_types, size } => value_types
            .iter()
            .try_fold(0u64, |acc, v| acc.checked_add(flat_width(v)?))?
            .checked_mul(u64::from(size.0)),
        HeapValueType::Vector { .. } => None,
    }
}

/// The detail of a call to aztec_prv_notifyCreatedNote whose packed note
/// is wider than MAX_NOTE_PACKED_LEN, or None when it is not. The packed
/// note is the fifth of the seven arguments (owner, an AztecAddress, is
/// one field), or the only array argument of a call with another arity.
/// A vector's length is read from its size register through `size` (a
/// known constant there); when the width is not known the call is
/// reported, as it may be wide. The v6 PXE refuses a call of this oracle
/// with any other number of argument slots than seven (its oracle
/// registry checks the count), so a call of another arity creates no
/// pending note, and this is the only oracle that adds one: matching the
/// name sees every route, whichever wrapper declares the oracle.
fn note_width(
    inputs: &[ValueOrArray],
    types: &[HeapValueType],
    size: impl Fn(&MemoryAddress) -> Option<FieldElement>,
) -> Option<String> {
    let is_array = |t: &HeapValueType| !matches!(t, HeapValueType::Simple(_));
    let index = if inputs.len() == 7 && types.get(4).is_some_and(is_array) {
        4
    } else {
        let arrays: Vec<usize> = (0..types.len()).filter(|i| is_array(&types[*i])).collect();
        match arrays.as_slice() {
            [i] => *i,
            _ => return None,
        }
    };
    let width = match (inputs.get(index)?, &types[index]) {
        (ValueOrArray::HeapVector(v), HeapValueType::Vector { value_types }) => {
            let per = value_types
                .iter()
                .try_fold(0u64, |acc, t| acc.checked_add(flat_width(t)?));
            size(&v.size)
                .filter(|c| c.num_bits() <= 32)
                .zip(per)
                .and_then(|(n, per)| per.checked_mul(n.to_u128() as u64))
        }
        (_, t) => flat_width(t),
    };
    match width {
        Some(w) if w <= MAX_NOTE_PACKED_LEN => None,
        Some(w) => Some(format!(
            "oracle {NOTIFY_CREATED_NOTE:?} with a packed note of {w} fields, above aztec-nr v6's MAX_NOTE_PACKED_LEN of {MAX_NOTE_PACKED_LEN}"
        )),
        None => Some(format!(
            "oracle {NOTIFY_CREATED_NOTE:?} with a packed note whose width is not known statically; aztec-nr v6's MAX_NOTE_PACKED_LEN is {MAX_NOTE_PACKED_LEN}"
        )),
    }
}

/// Scan every Brillig function. `has_location(fn, pc)` says whether the
/// debug info knows a source location for that pc.
pub fn scan(
    functions: &[(String, &[BOp<FieldElement>])],
    calls: &[BrilligCallSite],
    selectors: &BTreeMap<u64, String>,
    has_location: &dyn Fn(u32, usize) -> bool,
) -> BrilligReport {
    let mut report = BrilligReport::default();
    for (id, (name, code)) in functions.iter().enumerate() {
        let id = id as u32;
        let mut f = FunctionScan {
            code,
            states: walk(code),
            relaxed: None,
            jump_targets: code
                .iter()
                .filter_map(|op| match op {
                    BOp::Jump { location }
                    | BOp::JumpIf { location, .. }
                    | BOp::Call { location } => Some(*location),
                    _ => None,
                })
                .collect(),
            calls: calls
                .iter()
                .filter(|c| c.callee == id && !c.predicate_zero)
                .collect(),
        };
        let mut stats = FunctionStats {
            opcodes: code.len(),
            reachable: f.states.iter().filter(|s| s.is_some()).count(),
            ..Default::default()
        };
        for (pc, op) in code.iter().enumerate() {
            let is_trap = matches!(op, BOp::Trap { .. });
            stats.traps_total += usize::from(is_trap);
            let Some(pre) = f.states[pc].clone() else {
                stats.traps_unreachable += usize::from(is_trap);
                continue;
            };
            let note_width = f
                .note_width_site(pc, &pre)
                .map(|detail| (TrapKind::NoteWidth, detail, false, None));
            for (kind, detail, guarded, message) in
                f.site(pc, &pre, selectors).into_iter().chain(note_width)
            {
                report.sites.push(TrapSite {
                    brillig: id,
                    function_name: name.clone(),
                    pc,
                    kind,
                    message,
                    location_pc: locate(code, &f.states, id, pc, has_location),
                    guarded_by_callers: guarded,
                    detail,
                });
            }
        }
        report.stats.insert(id, stats);
    }
    report
}

/// An opcode the MPC Brillig VM of co-noir (co-snarks, co-brillig) does not
/// execute: an integer And, Or, Xor, Shl or Shr (its handlers are todo!(),
/// and it reads a shift's right operand as u8, where nargo emits it at the
/// left operand's width), a ConditionalMov (todo!() as well), or a black box
/// other than ToRadix (blake2s, blake3, keccakf1600, sha256_compression,
/// poseidon2_permutation, aes_128_encrypt, the ECDSA verifications,
/// multi_scalar_mul, embedded_curve_add: todo!()). Unconstrained code that
/// reaches one cannot run in co-noir's witness extension, whether its
/// operands are public or secret-shared. Field arithmetic, integer
/// Add/Sub/Mul/Div, comparisons, Not, casts and ToRadix do run.
#[derive(Clone, Debug)]
pub struct MpcOpSite {
    pub brillig: u32,
    pub function_name: String,
    pub pc: usize,
    /// "and", "or", "xor", "shl", "shr", "cmov", or the black box's name as
    /// the Brillig listing prints it ("blake2s", "sha256_compression", ...).
    pub op: &'static str,
    /// Operand width in bits (0 for ConditionalMov and black boxes).
    pub bit_size: u32,
    /// False when the constant propagation proves the opcode unreachable
    /// (behind a branch on a compile-time constant).
    pub reachable: bool,
    pub location_pc: Option<usize>,
    /// For a ConditionalMov with no debug location of its own (nargo gives
    /// the `if` it comes from none): the first located pc after it in the
    /// same procedure. The `if` lies between location_pc and this pc.
    pub next_location_pc: Option<usize>,
}

/// Every integer bitwise or shift opcode, every ConditionalMov and every
/// black box but ToRadix in every Brillig function (see MpcOpSite).
pub fn mpc_unsupported_ops(
    functions: &[(String, &[BOp<FieldElement>])],
    has_location: &dyn Fn(u32, usize) -> bool,
) -> Vec<MpcOpSite> {
    let mut sites = Vec::new();
    for (id, (name, code)) in functions.iter().enumerate() {
        let id = id as u32;
        let mut states: Option<Vec<Option<State>>> = None;
        for (pc, op) in code.iter().enumerate() {
            let (kind, bit_size) = match op {
                BOp::BinaryIntOp { op, bit_size, .. } => {
                    let kind = match op {
                        BinaryIntOp::And => "and",
                        BinaryIntOp::Or => "or",
                        BinaryIntOp::Xor => "xor",
                        BinaryIntOp::Shl => "shl",
                        BinaryIntOp::Shr => "shr",
                        _ => continue,
                    };
                    (kind, bit_size.to_u32())
                }
                BOp::ConditionalMov { .. } => ("cmov", 0),
                BOp::BlackBox(bb) => match black_box_name(bb) {
                    Some(name) => (name, 0),
                    None => continue,
                },
                _ => continue,
            };
            let states = states.get_or_insert_with(|| walk(code));
            let next_location_pc = if kind == "cmov" && !has_location(id, pc) {
                (pc + 1..code.len())
                    .take_while(|p| {
                        !matches!(
                            code[*p - 1],
                            BOp::Return | BOp::Stop { .. } | BOp::Trap { .. }
                        )
                    })
                    .find(|p| has_location(id, *p))
            } else {
                None
            };
            sites.push(MpcOpSite {
                brillig: id,
                function_name: name.clone(),
                pc,
                op: kind,
                bit_size,
                reachable: states[pc].is_some(),
                location_pc: locate(code, states, id, pc, has_location),
                next_location_pc,
            });
        }
    }
    sites
}

/// The name the Brillig listing gives a black box co-brillig does not run;
/// None for ToRadix, the one it runs.
fn black_box_name(op: &BlackBoxOp) -> Option<&'static str> {
    Some(match op {
        BlackBoxOp::ToRadix { .. } => return None,
        BlackBoxOp::AES128Encrypt { .. } => "aes_128_encrypt",
        BlackBoxOp::Blake2s { .. } => "blake2s",
        BlackBoxOp::Blake3 { .. } => "blake3",
        BlackBoxOp::Keccakf1600 { .. } => "keccakf1600",
        BlackBoxOp::EcdsaSecp256k1 { .. } => "ecdsa_secp256k1",
        BlackBoxOp::EcdsaSecp256r1 { .. } => "ecdsa_secp256r1",
        BlackBoxOp::MultiScalarMul { .. } => "multi_scalar_mul",
        BlackBoxOp::EmbeddedCurveAdd { .. } => "embedded_curve_add",
        BlackBoxOp::Poseidon2Permutation { .. } => "poseidon2_permutation",
        BlackBoxOp::Sha256Compression { .. } => "sha256_compression",
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use acir::brillig::lengths::{SemanticLength, SemiFlattenedLength};
    use acir::brillig::{HeapArray, HeapVector, IntegerBitSize};

    fn d(a: u32) -> MemoryAddress {
        MemoryAddress::Direct(a)
    }

    fn cnst(dest: u32, v: u128) -> BOp<FieldElement> {
        BOp::Const {
            destination: d(dest),
            bit_size: BitSize::Integer(IntegerBitSize::U32),
            value: FieldElement::from(v),
        }
    }

    fn fconst(dest: u32, v: u128) -> BOp<FieldElement> {
        BOp::Const {
            destination: d(dest),
            bit_size: BitSize::Field,
            value: FieldElement::from(v),
        }
    }

    fn hv() -> HeapVector {
        HeapVector {
            pointer: d(1),
            size: d(2),
        }
    }

    fn calldata(dest: u32, n: u128) -> Vec<BOp<FieldElement>> {
        vec![
            cnst(21, n),
            cnst(20, 0),
            BOp::CalldataCopy {
                destination_address: d(dest),
                size_address: d(21),
                offset_address: d(20),
            },
        ]
    }

    fn call_site(callee: u32, slot_nonzero: Vec<bool>) -> BrilligCallSite {
        BrilligCallSite {
            function: 0,
            opcode: 0,
            callee,
            predicate: "1".into(),
            predicate_zero: false,
            outputs: 1,
            slot_nonzero,
        }
    }

    fn scan_one(code: Vec<BOp<FieldElement>>, calls: &[BrilligCallSite]) -> BrilligReport {
        let sel: BTreeMap<u64, String> = [(77u64, "boom".to_string())].into_iter().collect();
        let fns = vec![("f".to_string(), code.as_slice())];
        scan(&fns, calls, &sel, &|_, _| false)
    }

    #[test]
    fn invert_directive_division_is_guarded_by_zero_test() {
        // if x == 0 skip; else x = 1 / x
        let mut code = calldata(0, 1);
        code.extend([
            fconst(2, 0),
            BOp::BinaryFieldOp {
                destination: d(3),
                op: BinaryFieldOp::Equals,
                lhs: d(0),
                rhs: d(2),
            },
            BOp::JumpIf {
                condition: d(3),
                location: 8,
            },
            fconst(1, 1),
            BOp::BinaryFieldOp {
                destination: d(0),
                op: BinaryFieldOp::Div,
                lhs: d(1),
                rhs: d(0),
            },
            BOp::Stop { return_data: hv() },
        ]);
        let r = scan_one(code, &[]);
        assert!(r.sites.is_empty(), "{:?}", r.sites);
    }

    fn int_op(dest: u32, op: BinaryIntOp, lhs: u32, rhs: u32) -> BOp<FieldElement> {
        BOp::BinaryIntOp {
            destination: d(dest),
            op,
            bit_size: IntegerBitSize::U128,
            lhs: d(lhs),
            rhs: d(rhs),
        }
    }

    fn cast(dest: u32, src: u32, bit_size: BitSize) -> BOp<FieldElement> {
        BOp::Cast {
            destination: d(dest),
            source: d(src),
            bit_size,
        }
    }

    const U128: BitSize = BitSize::Integer(IntegerBitSize::U128);

    fn u128_zero(dest: u32) -> BOp<FieldElement> {
        BOp::Const {
            destination: d(dest),
            bit_size: U128,
            value: FieldElement::zero(),
        }
    }

    /// A guarded u128 remainder: if b == 0 { 0 } else { a % b }, where Noir
    /// guards the remainder with 0 < b and a call to a trapping procedure.
    fn remainder_code(branch_on_zero: bool) -> Vec<BOp<FieldElement>> {
        let mut code = calldata(0, 2);
        code.extend([
            cast(3, 1, U128),
            u128_zero(4),
            int_op(5, BinaryIntOp::Equals, 3, 4),
        ]);
        let skip = code.len() + 9;
        code.push(if branch_on_zero {
            BOp::JumpIf {
                condition: d(5),
                location: skip,
            }
        } else {
            cnst(9, 0)
        });
        let after_check = code.len() + 3;
        code.extend([
            int_op(7, BinaryIntOp::LessThan, 4, 3),
            BOp::JumpIf {
                condition: d(7),
                location: after_check,
            },
            BOp::Call { location: skip + 1 },
            int_op(8, BinaryIntOp::Div, 0, 3),
            int_op(9, BinaryIntOp::Mul, 8, 3),
            int_op(6, BinaryIntOp::Sub, 0, 9),
            BOp::Jump { location: skip },
            cnst(6, 0),
        ]);
        assert_eq!(code.len(), skip);
        code.extend([
            BOp::Stop { return_data: hv() },
            BOp::Trap { revert_data: hv() },
        ]);
        code
    }

    #[test]
    fn remainder_check_inside_a_nonzero_branch_cannot_abort() {
        let r = scan_one(remainder_code(true), &[]);
        assert!(r.sites.is_empty(), "{:?}", r.sites);
        assert_eq!(r.stats[&0].traps_unreachable, 1);
        // without the branch, b may be zero: both the check's trap and
        // the division are reported
        let r = scan_one(remainder_code(false), &[]);
        let kinds: Vec<TrapKind> = r.sites.iter().map(|s| s.kind).collect();
        assert_eq!(kinds, vec![TrapKind::DivisionByZero, TrapKind::Trap]);
    }

    /// A u128 quotient a / d with d = ((b as Field) + ((b == 0) as Field))
    /// as u128, the register of b reused for the is-zero bit as nargo
    /// does. `variant` breaks one step of the argument.
    fn plus_own_is_zero_code(variant: u32) -> Vec<BOp<FieldElement>> {
        let mut code = calldata(0, 2);
        code.extend([
            // 1: b is the raw field argument, never cast to u128
            if variant == 1 {
                BOp::Mov {
                    destination: d(3),
                    source: d(1),
                }
            } else {
                cast(3, 1, U128)
            },
            cast(4, 3, BitSize::Field),
            u128_zero(5),
            // 2: the is-zero bit of a, not of b
            int_op(6, BinaryIntOp::Equals, if variant == 2 { 0 } else { 3 }, 5),
            cast(3, 6, BitSize::Field),
            BOp::BinaryFieldOp {
                destination: d(7),
                op: BinaryFieldOp::Add,
                lhs: d(4),
                rhs: d(3),
            },
            // 3: the sum cast to 64 bits, which may truncate it to 0
            cast(
                8,
                7,
                if variant == 3 {
                    BitSize::Integer(IntegerBitSize::U64)
                } else {
                    U128
                },
            ),
            cast(9, 0, U128),
            int_op(10, BinaryIntOp::Div, 9, 8),
            BOp::Stop { return_data: hv() },
        ]);
        code
    }

    #[test]
    fn divisor_plus_its_own_is_zero_bit_cannot_abort() {
        let r = scan_one(plus_own_is_zero_code(0), &[]);
        assert!(r.sites.is_empty(), "{:?}", r.sites);
        for variant in 1..=3 {
            let r = scan_one(plus_own_is_zero_code(variant), &[]);
            assert_eq!(r.sites.len(), 1, "variant {variant}");
            assert_eq!(r.sites[0].kind, TrapKind::DivisionByZero);
        }
    }

    #[test]
    fn division_by_argument_depends_on_call_sites() {
        let mut code = calldata(0, 2);
        code.extend([
            BOp::BinaryFieldOp {
                destination: d(2),
                op: BinaryFieldOp::IntegerDiv,
                lhs: d(0),
                rhs: d(1),
            },
            BOp::Stop { return_data: hv() },
        ]);
        let guarded = scan_one(
            code.clone(),
            &[
                call_site(0, vec![false, true]),
                call_site(0, vec![true, true]),
            ],
        );
        assert_eq!(guarded.sites.len(), 1);
        assert!(guarded.sites[0].guarded_by_callers);
        let live = scan_one(
            code,
            &[
                call_site(0, vec![false, true]),
                call_site(0, vec![false, false]),
            ],
        );
        assert!(!live.sites[0].guarded_by_callers);
        assert_eq!(live.sites[0].kind, TrapKind::DivisionByZero);
    }

    #[test]
    fn calldata_copy_past_the_last_address_forgets_facts() {
        // Two slots copied to u32::MAX and one past it: the second write
        // must not wrap onto register 0, which the division then uses.
        let mut code = calldata(u32::MAX, 2);
        code.extend([
            BOp::BinaryFieldOp {
                destination: d(2),
                op: BinaryFieldOp::IntegerDiv,
                lhs: d(5),
                rhs: d(0),
            },
            BOp::Stop { return_data: hv() },
        ]);
        let r = scan_one(code, &[call_site(0, vec![true, true])]);
        assert_eq!(r.sites.len(), 1);
        assert!(!r.sites[0].guarded_by_callers);
    }

    #[test]
    fn mpc_unsupported_ops_are_listed_with_reachability() {
        // A shift and a mask that run, a ConditionalMov that runs, and an
        // Xor behind the constant-true check 64 < 128 (never reached).
        // Div and LessThan are not listed: the MPC VM runs them.
        let mut code = calldata(0, 1);
        code.extend([
            cnst(4, 64),
            cnst(7, 128),
            BOp::BinaryIntOp {
                destination: d(8),
                op: BinaryIntOp::Shr,
                bit_size: IntegerBitSize::U128,
                lhs: d(0),
                rhs: d(4),
            },
            BOp::BinaryIntOp {
                destination: d(8),
                op: BinaryIntOp::And,
                bit_size: IntegerBitSize::U64,
                lhs: d(8),
                rhs: d(4),
            },
            BOp::BinaryIntOp {
                destination: d(9),
                op: BinaryIntOp::Div,
                bit_size: IntegerBitSize::U128,
                lhs: d(0),
                rhs: d(4),
            },
            BOp::ConditionalMov {
                destination: d(10),
                source_a: d(8),
                source_b: d(9),
                condition: d(6),
            },
            BOp::BinaryIntOp {
                destination: d(6),
                op: BinaryIntOp::LessThan,
                bit_size: IntegerBitSize::U128,
                lhs: d(4),
                rhs: d(7),
            },
        ]);
        let jump = code.len();
        code.extend([
            BOp::JumpIf {
                condition: d(6),
                location: jump + 2,
            },
            BOp::BinaryIntOp {
                destination: d(8),
                op: BinaryIntOp::Xor,
                bit_size: IntegerBitSize::U32,
                lhs: d(8),
                rhs: d(4),
            },
            BOp::Stop { return_data: hv() },
        ]);
        let functions = [("f".to_string(), code.as_slice())];
        let sites = mpc_unsupported_ops(&functions, &|_, _| false);
        let got: Vec<(&str, u32, bool)> = sites
            .iter()
            .map(|s| (s.op, s.bit_size, s.reachable))
            .collect();
        assert_eq!(
            got,
            vec![
                ("shr", 128, true),
                ("and", 64, true),
                ("cmov", 0, true),
                ("xor", 32, false)
            ]
        );
        assert!(
            sites
                .iter()
                .all(|s| s.function_name == "f" && s.location_pc.is_none())
        );
    }

    #[test]
    fn mpc_unsupported_black_boxes_are_listed() {
        // A blake2s that runs and a sha256_compression behind the
        // constant-true check 64 < 128 (never reached) are listed; the
        // ToRadix is not: co-brillig runs it and no other black box.
        let arr = |p: u32| HeapArray {
            pointer: d(p),
            size: acir::brillig::lengths::SemiFlattenedLength(2),
        };
        let mut code = calldata(0, 1);
        code.extend([
            cnst(3, 2),
            cnst(7, 254),
            to_radix(0, 3, 7),
            BOp::BlackBox(BlackBoxOp::Blake2s {
                message: arr(10),
                output: arr(11),
            }),
            // A black box clears the facts, so the constants come after it.
            cnst(4, 64),
            cnst(7, 128),
            BOp::BinaryIntOp {
                destination: d(6),
                op: BinaryIntOp::LessThan,
                bit_size: IntegerBitSize::U128,
                lhs: d(4),
                rhs: d(7),
            },
        ]);
        let jump = code.len();
        code.extend([
            BOp::JumpIf {
                condition: d(6),
                location: jump + 2,
            },
            BOp::BlackBox(BlackBoxOp::Sha256Compression {
                input: arr(12),
                hash_values: arr(13),
                output: arr(14),
            }),
            BOp::Stop { return_data: hv() },
        ]);
        let functions = [("f".to_string(), code.as_slice())];
        let sites = mpc_unsupported_ops(&functions, &|_, _| false);
        let got: Vec<(&str, u32, bool)> = sites
            .iter()
            .map(|s| (s.op, s.bit_size, s.reachable))
            .collect();
        assert_eq!(
            got,
            vec![("blake2s", 0, true), ("sha256_compression", 0, false)]
        );
    }

    #[test]
    fn trap_behind_constant_check_is_unreachable() {
        // 64 < 128 always holds, so the trap procedure is never called.
        let code = vec![
            cnst(4, 64),
            cnst(7, 128),
            BOp::BinaryIntOp {
                destination: d(6),
                op: BinaryIntOp::LessThan,
                bit_size: IntegerBitSize::U128,
                lhs: d(4),
                rhs: d(7),
            },
            BOp::JumpIf {
                condition: d(6),
                location: 5,
            },
            BOp::Call { location: 6 },
            BOp::Stop { return_data: hv() },
            BOp::Trap { revert_data: hv() },
            BOp::Return,
        ];
        let r = scan_one(code, &[]);
        assert!(r.sites.is_empty());
        assert_eq!(r.stats[&0].traps_total, 1);
        assert_eq!(r.stats[&0].traps_unreachable, 1);
    }

    #[test]
    fn trap_behind_unknown_check_is_reported_with_message() {
        let mut code = calldata(0, 1);
        code.extend([
            cnst(4, 10),
            BOp::BinaryIntOp {
                destination: d(6),
                op: BinaryIntOp::LessThan,
                bit_size: IntegerBitSize::U32,
                lhs: d(0),
                rhs: d(4),
            },
            BOp::JumpIf {
                condition: d(6),
                location: 8,
            },
            BOp::IndirectConst {
                destination_pointer: d(1),
                bit_size: BitSize::Integer(IntegerBitSize::U64),
                value: FieldElement::from(77u128),
            },
            BOp::Trap { revert_data: hv() },
            BOp::Stop { return_data: hv() },
        ]);
        let r = scan_one(code, &[]);
        assert_eq!(r.sites.len(), 1);
        assert_eq!(r.sites[0].kind, TrapKind::Trap);
        assert_eq!(r.sites[0].message.as_deref(), Some("boom"));
    }

    #[test]
    fn constant_and_unknown_divisors() {
        let code = vec![
            BOp::Load {
                destination: d(0),
                source_pointer: d(9),
            },
            cnst(1, 3),
            BOp::BinaryIntOp {
                destination: d(2),
                op: BinaryIntOp::Div,
                bit_size: IntegerBitSize::U32,
                lhs: d(0),
                rhs: d(1),
            },
            BOp::BinaryIntOp {
                destination: d(2),
                op: BinaryIntOp::Div,
                bit_size: IntegerBitSize::U32,
                lhs: d(1),
                rhs: d(0),
            },
            BOp::Stop { return_data: hv() },
        ];
        let r = scan_one(code, &[]);
        assert_eq!(r.sites.len(), 1);
        assert_eq!(r.sites[0].pc, 3);
    }

    /// `for i in 0..4 { v = v / 2 }` with the constant 2 hoisted above the
    /// loop and a store and a procedure call in its body, as nargo emits a
    /// rolled loop that writes an array (a bit decomposition at a large
    /// exponent).
    /// `clobber` is an extra opcode for the procedure's body.
    fn rolled_division_loop(clobber: Option<BOp<FieldElement>>) -> Vec<BOp<FieldElement>> {
        let mut code = calldata(30, 1);
        code.extend([
            cnst(8, 2), // 3: hoisted divisor
            cnst(3, 0), // 4: i = 0
            cnst(6, 4), // 5: bound
            cnst(9, 1), // 6: step
            // 7: loop header, entered from 6 and from the back edge at 14
            BOp::BinaryIntOp {
                destination: d(5),
                op: BinaryIntOp::LessThan,
                bit_size: IntegerBitSize::U32,
                lhs: d(3),
                rhs: d(6),
            },
            BOp::JumpIf {
                condition: d(5),
                location: 10,
            },
            BOp::Stop { return_data: hv() }, // 9
            BOp::Call { location: 15 },      // 10: copy-on-write procedure
            BOp::Store {
                destination_pointer: d(10),
                source: d(30),
            }, // 11
            BOp::BinaryIntOp {
                destination: d(30),
                op: BinaryIntOp::Div,
                bit_size: IntegerBitSize::U128,
                lhs: d(30),
                rhs: d(8),
            }, // 12
            BOp::BinaryIntOp {
                destination: d(3),
                op: BinaryIntOp::Add,
                bit_size: IntegerBitSize::U32,
                lhs: d(3),
                rhs: d(9),
            }, // 13
            BOp::Jump { location: 7 },       // 14
            // 15: the procedure: writes @10 and stores through it
            BOp::Mov {
                destination: d(10),
                source: d(1),
            },
            BOp::Store {
                destination_pointer: d(10),
                source: d(3),
            },
        ]);
        code.extend(clobber);
        code.push(BOp::Return);
        code
    }

    #[test]
    fn constant_divisor_hoisted_above_a_rolled_loop() {
        assert!(scan_one(rolled_division_loop(None), &[]).sites.is_empty());
        // The procedure overwrites the divisor: the division is reported.
        let load = BOp::Load {
            destination: d(8),
            source_pointer: d(10),
        };
        let r = scan_one(rolled_division_loop(Some(load)), &[]);
        assert_eq!(r.sites.len(), 1);
        assert_eq!(
            (r.sites[0].pc, r.sites[0].kind),
            (12, TrapKind::DivisionByZero)
        );
        // A procedure that moves the stack pointer may write any register.
        let sp = BOp::Mov {
            destination: d(0),
            source: d(1),
        };
        assert_eq!(scan_one(rolled_division_loop(Some(sp)), &[]).sites.len(), 1);
    }

    #[test]
    fn oracle_calls_other_than_print() {
        let fc = |name: &str| BOp::ForeignCall {
            function: name.to_string(),
            destinations: vec![],
            destination_value_types: vec![],
            inputs: vec![],
            input_value_types: vec![],
        };
        let r = scan_one(
            vec![fc("print"), fc("get_note"), BOp::Stop { return_data: hv() }],
            &[],
        );
        assert_eq!(r.sites.len(), 1);
        assert_eq!(r.sites[0].kind, TrapKind::Oracle);
    }

    /// A call to `name` with aztec-nr v6's notify_created_note_oracle
    /// arguments: owner, storage slot, randomness, note type id, the
    /// packed note `note`, note hash, counter.
    fn notify(name: &str, note: (ValueOrArray, HeapValueType)) -> BOp<FieldElement> {
        let field = HeapValueType::Simple(BitSize::Field);
        let mut inputs: Vec<ValueOrArray> = (0..4)
            .map(|i| ValueOrArray::MemoryAddress(d(40 + i)))
            .collect();
        let mut input_value_types = vec![field.clone(); 4];
        inputs.push(note.0);
        input_value_types.push(note.1);
        inputs.extend([45, 46].map(|i| ValueOrArray::MemoryAddress(d(i))));
        input_value_types.extend([field, HeapValueType::Simple(U32)]);
        BOp::ForeignCall {
            function: name.to_string(),
            destinations: vec![],
            destination_value_types: vec![],
            inputs,
            input_value_types,
        }
    }

    fn packed_array(n: u32) -> (ValueOrArray, HeapValueType) {
        (
            ValueOrArray::HeapArray(HeapArray {
                pointer: d(50),
                size: SemiFlattenedLength(n),
            }),
            HeapValueType::Array {
                value_types: vec![HeapValueType::Simple(BitSize::Field)],
                size: SemanticLength(n),
            },
        )
    }

    fn packed_vector() -> (ValueOrArray, HeapValueType) {
        (
            ValueOrArray::HeapVector(HeapVector {
                pointer: d(50),
                size: d(51),
            }),
            HeapValueType::Vector {
                value_types: vec![HeapValueType::Simple(BitSize::Field)],
            },
        )
    }

    const U32: BitSize = BitSize::Integer(IntegerBitSize::U32);

    fn note_width_details(code: Vec<BOp<FieldElement>>) -> Vec<(TrapKind, String)> {
        scan_one(code, &[])
            .sites
            .into_iter()
            .map(|s| (s.kind, s.detail))
            .collect()
    }

    #[test]
    fn a_packed_note_wider_than_the_limit_is_a_note_width_site() {
        let stop = || BOp::Stop { return_data: hv() };
        // One field over MAX_NOTE_PACKED_LEN: the oracle site and a
        // note-width site at the same pc.
        let wide = note_width_details(vec![notify(NOTIFY_CREATED_NOTE, packed_array(9)), stop()]);
        assert_eq!(wide.len(), 2, "{wide:?}");
        assert_eq!(wide[0].0, TrapKind::Oracle);
        assert_eq!(wide[1].0, TrapKind::NoteWidth);
        assert!(wide[1].1.contains("packed note of 9 fields"), "{wide:?}");
        assert!(wide[1].1.contains("MAX_NOTE_PACKED_LEN of 8"));
        // Exactly the limit, or a wide array to another oracle: the
        // oracle site only.
        for code in [
            vec![notify(NOTIFY_CREATED_NOTE, packed_array(8)), stop()],
            vec![notify("aztec_prv_notifyOther", packed_array(9)), stop()],
        ] {
            let sites = note_width_details(code);
            assert_eq!(sites.len(), 1, "{sites:?}");
            assert_eq!(sites[0].0, TrapKind::Oracle);
        }
        // A vector: its length is read from the size register when known.
        let vector = |len: Option<u128>| {
            let mut code: Vec<BOp<FieldElement>> = len.map(|n| cnst(51, n)).into_iter().collect();
            code.extend([notify(NOTIFY_CREATED_NOTE, packed_vector()), stop()]);
            note_width_details(code)
        };
        assert_eq!(vector(Some(8)).len(), 1);
        let v9 = vector(Some(9));
        assert_eq!(v9[1].0, TrapKind::NoteWidth);
        assert!(v9[1].1.contains("packed note of 9 fields"));
        let unknown = vector(None);
        assert_eq!(unknown[1].0, TrapKind::NoteWidth);
        assert!(unknown[1].1.contains("not known statically"));
        assert!(!TrapKind::NoteWidth.whitelisted_in_library());
        assert!(TrapKind::Oracle.whitelisted_in_library());
    }

    fn to_radix(input: u32, radix: u32, limbs: u32) -> BOp<FieldElement> {
        BOp::BlackBox(BlackBoxOp::ToRadix {
            input: d(input),
            radix: d(radix),
            output_pointer: d(30),
            num_limbs: d(limbs),
            output_bits: d(31),
        })
    }

    fn radix_code(
        radix: u128,
        limbs: u128,
        prep: Vec<BOp<FieldElement>>,
    ) -> Vec<BOp<FieldElement>> {
        // The input sits in @10: @0 is the stack pointer.
        let mut code = calldata(10, 1);
        code.extend(prep);
        code.extend([
            cnst(3, radix),
            // The compiler writes the array header through a pointer here.
            BOp::IndirectConst {
                destination_pointer: d(30),
                bit_size: BitSize::Integer(IntegerBitSize::U32),
                value: FieldElement::from(1u128),
            },
            cnst(7, limbs),
            to_radix(10, 3, 7),
            BOp::Stop { return_data: hv() },
        ]);
        code
    }

    #[test]
    fn short_radix_decomposition_is_an_abort_site() {
        // to_le_bytes::<1>: one radix-256 limb holds 8 bits.
        let r = scan_one(radix_code(256, 1, vec![]), &[]);
        assert_eq!(r.sites.len(), 1);
        assert_eq!(r.sites[0].kind, TrapKind::Radix);
        assert!(
            r.sites[0]
                .detail
                .contains("1 limbs of radix 256 hold 8 bits")
        );
    }

    #[test]
    fn full_width_radix_decompositions_cannot_abort() {
        // to_le_bits (254 bits), to_le_bytes::<32> (256 bits).
        assert!(scan_one(radix_code(2, 254, vec![]), &[]).sites.is_empty());
        assert!(scan_one(radix_code(256, 32, vec![]), &[]).sites.is_empty());
        // 253 bits is not enough for every Field.
        assert_eq!(scan_one(radix_code(2, 253, vec![]), &[]).sites.len(), 1);
    }

    #[test]
    fn radix_of_a_known_width_input() {
        // (x as u8) as Field decomposed into one byte cannot abort; as u16 it can.
        let cast = |bits| {
            vec![
                BOp::Cast {
                    destination: d(10),
                    source: d(10),
                    bit_size: BitSize::Integer(bits),
                },
                BOp::Cast {
                    destination: d(10),
                    source: d(10),
                    bit_size: BitSize::Field,
                },
            ]
        };
        assert!(
            scan_one(radix_code(256, 1, cast(IntegerBitSize::U8)), &[])
                .sites
                .is_empty()
        );
        assert_eq!(
            scan_one(radix_code(256, 1, cast(IntegerBitSize::U16)), &[])
                .sites
                .len(),
            1
        );
    }

    #[test]
    fn radix_with_unknown_limb_count_is_reported() {
        let mut code = calldata(0, 2);
        code.extend([
            cnst(3, 2),
            to_radix(0, 3, 1),
            BOp::Stop { return_data: hv() },
        ]);
        let r = scan_one(code, &[]);
        assert_eq!(r.sites.len(), 1);
        assert!(r.sites[0].detail.contains("not known"));
    }
}
