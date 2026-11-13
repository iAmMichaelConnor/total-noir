//! Selection and control helpers: the Select trait, the Outcome
//! accumulator, and some_or, the flagged Option::unwrap.
//!
//! Everything in this module is select arithmetic. No entry calls an
//! unconstrained function, emits a range check, or asserts, so no entry
//! has a failure source: for every input the outputs are defined by
//! AssertZero definitions the ACVM solves directly. These are the tools
//! for neutralising a fallible step without a branch: compute the step on
//! clamped inputs, then select its result on the step's ok flag.
//!
//! Constraint shapes per impl (c is the condition, already a bool):
//! - Field: c*(t - f) + f, one degree-2 definition.
//! - bool: (c & t) | (!c & f). On bool values & is a product, ! is 1 - x
//!   and | is a + b - a*b, so the result is boolean by arithmetic and no
//!   booleanity constraint is added.
//! - u8, u16, u32, u64, u128, i8, i16, i32, i64: c*(t - f) + f, one
//!   definition with no range check.
//! - arrays and tuples: the element impls, once per element.

use crate::core::select_field;

/// Total selection between two values of the same type: returns t when c
/// is true and f otherwise.
///
/// Implement it for your own types field by field. For a struct
///
/// ```noir
/// struct Pair { a: Field, b: bool }
///
/// impl Select for Pair {
///     fn select(c: bool, t: Self, f: Self) -> Self {
///         Pair { a: Select::select(c, t.a, f.a), b: Select::select(c, t.b, f.b) }
///     }
/// }
/// ```
///
/// the impl inherits totality from its field impls: it is select
/// arithmetic on each field and nothing else. The tests in this module
/// compile and exercise exactly this example.
pub trait Select {
    fn select(c: bool, t: Self, f: Self) -> Self;
}

/// Field selection, core::select_field. Total: one arithmetic definition,
/// no failure source.
impl Select for Field {
    fn select(c: bool, t: Field, f: Field) -> Field {
        select_field(c, t, f)
    }
}

/// bool selection, (c & t) | (!c & f). Total: products and sums of bool
/// values, no failure source.
impl Select for bool {
    fn select(c: bool, t: bool, f: bool) -> bool {
        (c & t) | (!c & f)
    }
}

// Unsigned integer selection, `if c { t } else { f }`: it lowers to the
// arithmetic definition c*(t - f) + f with no range check (the result
// is one of two values that already satisfy the type's range). Total:
// one definition, no failure source.

impl Select for u8 {
    fn select(c: bool, t: u8, f: u8) -> u8 {
        if c {
            t
        } else {
            f
        }
    }
}

impl Select for u16 {
    fn select(c: bool, t: u16, f: u16) -> u16 {
        if c {
            t
        } else {
            f
        }
    }
}

impl Select for u32 {
    fn select(c: bool, t: u32, f: u32) -> u32 {
        if c {
            t
        } else {
            f
        }
    }
}

impl Select for u64 {
    fn select(c: bool, t: u64, f: u64) -> u64 {
        if c {
            t
        } else {
            f
        }
    }
}

impl Select for u128 {
    fn select(c: bool, t: u128, f: u128) -> u128 {
        if c {
            t
        } else {
            f
        }
    }
}

// Signed integer selection: the same `if c { t } else { f }` on the bit
// patterns, one arithmetic definition with no range check. Total.

impl Select for i8 {
    fn select(c: bool, t: i8, f: i8) -> i8 {
        if c {
            t
        } else {
            f
        }
    }
}

impl Select for i16 {
    fn select(c: bool, t: i16, f: i16) -> i16 {
        if c {
            t
        } else {
            f
        }
    }
}

impl Select for i32 {
    fn select(c: bool, t: i32, f: i32) -> i32 {
        if c {
            t
        } else {
            f
        }
    }
}

impl Select for i64 {
    fn select(c: bool, t: i64, f: i64) -> i64 {
        if c {
            t
        } else {
            f
        }
    }
}

/// Element-wise selection over a fixed-size array. The loop index is a
/// compile-time constant, so every access is a constant index (no memory
/// opcodes). Total: L element selects, no failure source.
impl<T, let L: u32> Select for [T; L]
where
    T: Select,
{
    fn select(c: bool, t: [T; L], f: [T; L]) -> [T; L] {
        let mut out = f;
        for i in 0..L {
            out[i] = T::select(c, t[i], f[i]);
        }
        out
    }
}

/// Component-wise selection over a pair. Total: two component selects,
/// no failure source.
impl<A, B> Select for (A, B)
where
    A: Select,
    B: Select,
{
    fn select(c: bool, t: (A, B), f: (A, B)) -> (A, B) {
        (A::select(c, t.0, f.0), B::select(c, t.1, f.1))
    }
}

/// Component-wise selection over a triple. Total: three component
/// selects, no failure source.
impl<A, B, C> Select for (A, B, C)
where
    A: Select,
    B: Select,
    C: Select,
{
    fn select(c: bool, t: (A, B, C), f: (A, B, C)) -> (A, B, C) {
        (A::select(c, t.0, f.0), B::select(c, t.1, f.1), C::select(c, t.2, f.2))
    }
}

/// Component-wise selection over a 4-tuple. Total: four component
/// selects, no failure source.
impl<A, B, C, D> Select for (A, B, C, D)
where
    A: Select,
    B: Select,
    C: Select,
    D: Select,
{
    fn select(c: bool, t: (A, B, C, D), f: (A, B, C, D)) -> (A, B, C, D) {
        (
            A::select(c, t.0, f.0), B::select(c, t.1, f.1), C::select(c, t.2, f.2),
            D::select(c, t.3, f.3),
        )
    }
}

/// An accumulated success flag plus the code of the first check that
/// failed.
///
/// Thread one Outcome through a sequence of checks with require. ok is
/// the AND of every flag passed in. code is 0 while ok holds and becomes
/// the code of the first failing check; later failures do not overwrite
/// it. Use nonzero codes, so that code == 0 exactly when ok is true.
///
/// Every field is computed by select arithmetic from the flags, so both
/// ok and code are determined whenever the flags passed in are
/// determined.
pub struct Outcome {
    pub ok: bool,
    pub code: Field,
}

impl Outcome {
    /// The passing outcome: ok = true, code = 0. Constants only.
    pub fn good() -> Outcome {
        Outcome { ok: true, code: 0 }
    }

    /// Record one check. fail_now = self.ok & !flag;
    /// code' = select(fail_now, code, self.code); ok' = self.ok & flag.
    /// So the first failing check's code sticks. Total: bool products and
    /// one Field select, no failure source.
    pub fn require(self, flag: bool, code: Field) -> Outcome {
        let fail_now = self.ok & !flag;
        Outcome { ok: self.ok & flag, code: select_field(fail_now, code, self.code) }
    }

    /// Combine two outcomes, treating self as the earlier one: ok is the
    /// AND of both, code is self's code if self failed, else other's
    /// code. Total: one bool product and one Field select, no failure
    /// source.
    pub fn and_outcome(self, other: Outcome) -> Outcome {
        Outcome { ok: self.ok & other.ok, code: select_field(self.ok, other.code, self.code) }
    }

    /// new when ok holds, else old. This is how a state update guarded by
    /// the checks is applied without a branch. Total: Select::select, no
    /// failure source.
    pub fn guard<T>(self, new: T, old: T) -> T
    where
        T: Select,
    {
        T::select(self.ok, new, old)
    }

    /// x when ok holds, else 0. Total: one Field select, no failure
    /// source.
    pub fn mask_field(self, x: Field) -> Field {
        select_field(self.ok, x, 0)
    }

    /// Element-wise mask_field: xs when ok holds, else all zeros. Total:
    /// L Field selects, no failure source.
    pub fn mask_array<let L: u32>(self, xs: [Field; L]) -> [Field; L] {
        let mut out = [0; L];
        for i in 0..L {
            out[i] = select_field(self.ok, xs[i], 0);
        }
        out
    }
}

/// The flagged form of Option::unwrap and Option::expect: returns
/// (value, ok) with ok = opt.is_some(), value = the contained value when
/// ok, else std::mem::zeroed(). unwrap and expect assert is_some, so a
/// None reaching them fails the circuit; this returns the flag instead.
/// For a fallback other than zero, select on ok: Select::select(ok, v,
/// fallback), or Option::unwrap_or, which is total as it stands.
///
/// Constraints: one Select::select of T on opt's is_some flag (select
/// arithmetic, no assert, no hint). unwrap_unchecked reads the value slot
/// without a check; for a None the slot holds whatever the Option was
/// built with, and the select discards it. Total for every Option.
/// Determined: ok is opt's own flag and value is a function of opt.
pub fn some_or<T>(opt: Option<T>) -> (T, bool)
where
    T: Select,
{
    let ok = opt.is_some();
    (T::select(ok, opt.unwrap_unchecked(), std::mem::zeroed()), ok)
}

mod tests {
    use super::{Outcome, Select, some_or};

    // The doc example from the Select trait, compiled.
    struct Pair {
        a: Field,
        b: bool,
    }

    impl Select for Pair {
        fn select(c: bool, t: Self, f: Self) -> Self {
            Pair { a: Select::select(c, t.a, f.a), b: Select::select(c, t.b, f.b) }
        }
    }

    global P_MINUS_1: Field = 0 - 1;

    #[test]
    fn select_field_sides_and_edges() {
        assert_eq(Field::select(true, 7, 9), 7);
        assert_eq(Field::select(false, 7, 9), 9);
        assert_eq(Field::select(true, P_MINUS_1, 0), P_MINUS_1);
        assert_eq(Field::select(false, 0, P_MINUS_1), P_MINUS_1);
        assert_eq(Field::select(true, 5, 5), 5);
    }

    #[test]
    fn select_bool_truth_table() {
        let vals = [false, true];
        for ci in 0..2 {
            for ti in 0..2 {
                for fi in 0..2 {
                    let c = vals[ci];
                    let t = vals[ti];
                    let f = vals[fi];
                    let expected = if c { t } else { f };
                    assert_eq(bool::select(c, t, f), expected);
                }
            }
        }
    }

    #[test]
    fn select_arrays_elementwise() {
        let t = [1, 2, 3];
        let f = [4, 5, 6];
        assert_eq(Select::select(true, t, f), t);
        assert_eq(Select::select(false, t, f), f);
        let nt = [[1, 2], [3, 4]];
        let nf = [[5, 6], [7, P_MINUS_1]];
        assert_eq(Select::select(true, nt, nf), nt);
        assert_eq(Select::select(false, nt, nf), nf);
        let empty_t: [Field; 0] = [];
        let empty_f: [Field; 0] = [];
        assert_eq(Select::select(true, empty_t, empty_f), empty_t);
    }

    #[test]
    fn select_tuples() {
        let t2: (Field, bool) = (1, true);
        let f2: (Field, bool) = (2, false);
        assert_eq(Select::select(true, t2, f2), t2);
        assert_eq(Select::select(false, t2, f2), f2);
        let t3: (Field, [Field; 2], bool) = (1, [2, 3], false);
        let f3: (Field, [Field; 2], bool) = (4, [5, 6], true);
        assert_eq(Select::select(true, t3, f3), t3);
        assert_eq(Select::select(false, t3, f3), f3);
        let t4: (Field, bool, u8, i16) = (1, true, 255, -3);
        let f4: (Field, bool, u8, i16) = (P_MINUS_1, false, 0, 32767);
        assert_eq(Select::select(true, t4, f4), t4);
        assert_eq(Select::select(false, t4, f4), f4);
    }

    #[test]
    fn select_signed_integers() {
        assert_eq(i8::select(true, -128, 127), -128);
        assert_eq(i8::select(false, -128, 127), 127);
        assert_eq(i16::select(false, 1, -32768), -32768);
        assert_eq(i32::select(true, -1, 0), -1);
        assert_eq(i64::select(false, 5, -9223372036854775808), -9223372036854775808);
    }

    #[test]
    fn select_user_struct() {
        let t = Pair { a: 10, b: true };
        let f = Pair { a: 20, b: false };
        let r1 = Pair::select(true, t, f);
        assert_eq(r1.a, 10);
        assert(r1.b);
        let r2 = Pair::select(false, t, f);
        assert_eq(r2.a, 20);
        assert(!r2.b);
    }

    #[test]
    fn outcome_good_is_ok_with_zero_code() {
        let o = Outcome::good();
        assert(o.ok);
        assert_eq(o.code, 0);
    }

    #[test]
    fn outcome_require_passing_keeps_good() {
        let o = Outcome::good().require(true, 1).require(true, 2);
        assert(o.ok);
        assert_eq(o.code, 0);
    }

    #[test]
    fn outcome_first_failure_code_sticks() {
        let o =
            Outcome::good().require(true, 1).require(false, 2).require(false, 3).require(true, 4);
        assert(!o.ok);
        assert_eq(o.code, 2);
    }

    #[test]
    fn outcome_failure_at_first_check() {
        let o = Outcome::good().require(false, P_MINUS_1).require(false, 7);
        assert(!o.ok);
        assert_eq(o.code, P_MINUS_1);
    }

    #[test]
    fn outcome_and_combinations() {
        let good = Outcome::good();
        let bad_a = Outcome::good().require(false, 11);
        let bad_b = Outcome::good().require(false, 22);

        let gg = good.and_outcome(good);
        assert(gg.ok);
        assert_eq(gg.code, 0);

        let gb = good.and_outcome(bad_b);
        assert(!gb.ok);
        assert_eq(gb.code, 22);

        let bg = bad_a.and_outcome(good);
        assert(!bg.ok);
        assert_eq(bg.code, 11);

        let bb = bad_a.and_outcome(bad_b);
        assert(!bb.ok);
        assert_eq(bb.code, 11);
    }

    #[test]
    fn outcome_guard_and_masks() {
        let good = Outcome::good();
        let bad = Outcome::good().require(false, 5);

        assert_eq(good.guard(1, 2), 1);
        assert_eq(bad.guard(1, 2), 2);
        let gt: (Field, bool) = good.guard((3, true), (4, false));
        assert_eq(gt, (3, true));
        let bt: (Field, bool) = bad.guard((3, true), (4, false));
        assert_eq(bt, (4, false));

        assert_eq(good.mask_field(P_MINUS_1), P_MINUS_1);
        assert_eq(bad.mask_field(P_MINUS_1), 0);
        assert_eq(good.mask_array([1, 2, 3]), [1, 2, 3]);
        assert_eq(bad.mask_array([1, 2, 3]), [0, 0, 0]);
    }

    #[test]
    fn some_or_some_and_none() {
        assert_eq(some_or(Option::some(P_MINUS_1)), (P_MINUS_1, true));
        assert_eq(some_or(Option::<Field>::none()), (0, false));
        let some_pair: (Field, bool) = some_or(Option::some((3, true))).0;
        assert_eq(some_pair, (3, true));
        let (none_arr, ok) = some_or(Option::<[Field; 2]>::none());
        assert(!ok);
        assert_eq(none_arr, [0, 0]);
        assert_eq(some_or(Option::<u8>::none()), (0, false));
    }
}
