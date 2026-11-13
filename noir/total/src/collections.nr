//! Array access, windows, sums, search, min and max, sortedness and
//! sorting, total for every input.
//!
//! No entry indexes an array with a witness. A runtime index i is turned
//! into equality flags e_j = (i == j) against the constants j = 0..N-1,
//! and the element is picked with Select. So there are no memory
//! opcodes and no bounds asserts; an index out of bounds gives the zero
//! value and ok = false. The price is O(N) constraints per access,
//! documented per entry.
//!
//! The library-wide conventions (lib.nr), as they apply here:
//! - On ok = false an entry that produces a value returns the zero value
//!   of its type (0, false, an all-zero array, std::mem::zeroed() for a
//!   generic T); an entry that updates a container (set_or here, the
//!   BoundedVec push, set and extend forms) returns the container
//!   unchanged, except that a BoundedVec whose length already exceeds
//!   MaxLen comes back empty (bounded_vec.nr).
//! - Free functions that take untrusted data take indices, lengths and
//!   shift amounts as Field, so any value, including p - 1, is flagged
//!   rather than range-checked at the boundary. Trait methods on native
//!   types take native types, like the std methods they replace (a u32
//!   index on BoundedVec, a shift amount of the operand's type in
//!   bitwise::TotalShift).
//!
//! Gadgets used, all from core and range:
//! - eq / is_zero: the inversion gadget, hint-satisfiable for every
//!   input, determined both ways.
//! - range::clamp_bits_or::<W> (1 <= W <= 128): canonical limbs and one
//!   split, hint-satisfiable for every Field, determined.
//! - lt_bounded::<W>: called only on values already clamped below 2^W,
//!   which is its precondition, so its range check is hint-satisfiable.
//! Everything else is select arithmetic and bool products, apart from
//! sort_or's hinted permutation (its own section).
//!
//! The flags e_j for distinct constants j are mutually exclusive: at
//! most one constant equals i. So their OR, which equals their sum, is
//! the in-bounds flag. Each e_j is determined, so every flag built from
//! them is determined.
//!
//! std status: arrays' sort, sort_via, any, all, fold, map, concat and
//! the like loop over the array with constant indices; on native integer
//! or Field elements they are total as they stand (sort is a hinted
//! permutation std checks with constraints its own hint always meets).
//! The entries here exist for Field arrays whose elements are untrusted
//! and must first be flagged against a width, and for runtime indices.
//!
//! Unrolled loop indices, numeric generics, and arithmetic or casts to
//! Field on them are compile-time constants and emit no constraint.
//!
//! Submodule bounded_vec: flagged forms of std's BoundedVec operations,
//! built on index_flags_or and prefix_mask_or.

use crate::core::{eq, lt_bounded, select_field};
use crate::ctl::Select;
use crate::range::clamp_bits_or;
use std::mem::zeroed;
use std::static_assert;

pub mod bounded_vec;

/// Equality flags of a runtime index against 0..N-1: flags[j] = (i == j),
/// and ok = (i < N) as an integer, meaning i is one of the N constants.
///
/// Constraints: N eq gadgets (hint-satisfiable, determined) and an OR
/// chain over the flags (bool arithmetic, no hint). At most one flag is
/// set, so the OR equals their sum, the in-bounds flag. Total for every
/// Field i, including p - 1 and values at or above 2^128. Cost: N eq
/// gadgets and N - 1 bool ORs.
pub fn index_flags_or<let N: u32>(i: Field) -> ([bool; N], bool) {
    let mut flags = [false; N];
    let mut ok = false;
    for j in 0..N {
        let e = eq(i, j as Field);
        flags[j] = e;
        ok = ok | e;
    }
    (flags, ok)
}

/// Prefix mask of a runtime length: mask[j] = (j < len1) where
/// len1 = len when len <= N and len1 = 0 otherwise; ok = (len <= N).
/// The clamped length is recoverable as the sum of the mask.
///
/// Constraints: N + 1 eq gadgets e_k = (len == k) for k = 0..N
/// (hint-satisfiable, determined), then mask[j] = e_(j+1) | ... | e_N by a
/// running OR from the top, and ok = e_0 | mask[0]. When len > N every
/// e_k is false, so the mask is all false and ok is false. Total for
/// every Field len. Cost: N + 1 eq gadgets and N bool ORs.
pub fn prefix_mask_or<let N: u32>(len: Field) -> ([bool; N], bool) {
    let mut mask = [false; N];
    let mut above = eq(len, N as Field);
    for k in 0..N {
        let j = N - 1 - k;
        mask[j] = above;
        above = above | eq(len, j as Field);
    }
    // After the loop, above = e_0 | e_1 | ... | e_N.
    (mask, above)
}

/// arr[i] when i < N, else the zero value; ok = (i < N).
///
/// Built from index_flags_or and a select fold starting at
/// std::mem::zeroed(): acc = select(e_j, arr[j], acc). At most one e_j is
/// set, so the fold returns arr[i] in bounds and zeroed() out of bounds.
/// No memory opcodes, no bounds assert. Constraints: those of
/// index_flags_or plus N selects of T (select arithmetic). Total for every
/// Field i; ok is determined. Cost: N eq gadgets, N - 1 bool ORs and N
/// T-selects.
pub fn index_or<T, let N: u32>(arr: [T; N], i: Field) -> (T, bool)
where
    T: Select,
{
    let (flags, ok) = index_flags_or::<N>(i);
    let mut acc = zeroed();
    for j in 0..N {
        acc = T::select(flags[j], arr[j], acc);
    }
    (acc, ok)
}

/// arr with position i replaced by v when i < N, else arr unchanged;
/// ok = (i < N).
///
/// out[j] = select(e_j, v, arr[j]). Constraints: those of index_flags_or plus
/// N selects of T. Total for every Field i; ok is determined. Cost: N eq
/// gadgets, N - 1 bool ORs and N T-selects.
pub fn set_or<T, let N: u32>(arr: [T; N], i: Field, v: T) -> ([T; N], bool)
where
    T: Select,
{
    let (flags, ok) = index_flags_or::<N>(i);
    let mut out = arr;
    for j in 0..N {
        out[j] = T::select(flags[j], v, arr[j]);
    }
    (out, ok)
}

/// The window arr[start .. start + M] when start + M <= N, else M zero
/// values; ok = (start <= N - M) as integers. Requires M <= N at compile
/// time.
///
/// The start is compared only against the N - M + 1 constant positions a
/// window can begin at: (e_s, ok) = index_flags_or::<N - M + 1>(start). Then
/// out[k] = fold over s of select(e_s, arr[s + k], acc) from zeroed().
/// Out of range, every e_s is false, so every element is zeroed(). Because
/// start is never added to anything, a huge start such as p - 1 cannot
/// wrap into range. Constraints: N - M + 1 eq gadgets, the OR chain, and
/// M*(N - M + 1) T-selects. Total for every Field start; ok is
/// determined.
pub fn subarray_or<T, let N: u32, let M: u32>(arr: [T; N], start: Field) -> ([T; M], bool)
where
    T: Select,
{
    static_assert(M <= N, "subarray_or: window longer than the array");
    // index_flags_or::<N - M + 1>(start), written out: N - M in a generic
    // position fails to compile for M > N before the static_assert above
    // can report it, while this runtime count is folded after it.
    let starts = if M <= N { N - M + 1 } else { 0 };
    let mut flags = [false; N + 1];
    let mut ok = false;
    for s in 0..starts {
        let e = eq(start, s as Field);
        flags[s] = e;
        ok = ok | e;
    }
    let mut out = [zeroed(); M];
    for k in 0..M {
        let mut acc = zeroed();
        for s in 0..starts {
            acc = T::select(flags[s], arr[s + k], acc);
        }
        out[k] = acc;
    }
    (out, ok)
}

/// Exact sum of W-bit elements, wider than W bits: (sum, true) when
/// every element is below 2^W; (0, false) otherwise.
///
/// No-wrap bound: each clamped element is below 2^W <= 2^128 and N is a
/// u32, so the sum is below 2^32 * 2^128 = 2^160 < p. The returned value
/// is therefore the exact integer sum, with no condition on N.
/// Constraints: N clamp_bits_or::<W> (hint-satisfiable, determined),
/// linear additions and one select to 0. Total for every input. Cost: N
/// fits_bits gadgets. 1 <= W <= 128.
pub fn sum_wide_or<let N: u32, let W: u32>(arr: [Field; N]) -> (Field, bool) {
    static_assert((W >= 1) & (W <= 128), "sum_wide_or: W must be in 1..=128");
    let mut sum: Field = 0;
    let mut ok = true;
    for j in 0..N {
        let (v, in_range) = clamp_bits_or::<W>(arr[j]);
        sum += v;
        ok = ok & in_range;
    }
    (select_field(ok, sum, 0), ok)
}

/// Sum that must stay within W bits: (sum, true) when every element is
/// below 2^W and so is their sum; (0, false) otherwise. The value always
/// satisfies the W-bit invariant.
///
/// sum_wide_or::<N, W>, then clamp_bits_or::<W> on the exact sum (total
/// for any Field), then a select to 0. Constraints: N + 1 clamp_bits_or
/// gadgets and two selects. Total for every input; ok is determined.
/// Cost: N + 1 fits_bits gadgets. 1 <= W <= 128.
pub fn sum_or<let N: u32, let W: u32>(arr: [Field; N]) -> (Field, bool) {
    static_assert((W >= 1) & (W <= 128), "sum_or: W must be in 1..=128");
    let (sum, elems_ok) = sum_wide_or::<N, W>(arr);
    let (clamped, sum_ok) = clamp_bits_or::<W>(sum);
    let ok = elems_ok & sum_ok;
    (select_field(ok, clamped, 0), ok)
}

/// Position of the first true flag: (j, true) for the smallest j with
/// flags[j], or (0, false) when no flag is set.
///
/// Scan with a taken flag: hit_j = flags[j] & !taken; index += hit_j * j;
/// taken = taken | flags[j]. Exactly one hit is set when any flag is, so
/// the index is exact. Constraints: bool products and linear sums only,
/// no hint, no failure source. Use it to search arrays of any type:
/// compute one flag per element with your own comparison, then scan.
/// Cost: N steps of bool arithmetic.
pub fn first_true_or<let N: u32>(flags: [bool; N]) -> (Field, bool) {
    let mut taken = false;
    let mut index: Field = 0;
    for j in 0..N {
        let hit = flags[j] & !taken;
        index += (hit as Field) * (j as Field);
        taken = taken | flags[j];
    }
    (index, taken)
}

/// Position of the first element equal to x: (j, true) for the smallest
/// such j, or (0, false) when x does not occur. For other element types,
/// compute one flag per element and call first_true_or.
///
/// N eq gadgets (hint-satisfiable, determined) feeding first_true_or.
/// Total for every input; both outputs are determined. Cost: N eq
/// gadgets plus the scan.
pub fn first_index_of_or<let N: u32>(arr: [Field; N], x: Field) -> (Field, bool) {
    let mut flags = [false; N];
    for j in 0..N {
        flags[j] = eq(arr[j], x);
    }
    first_true_or(flags)
}

/// Non-decreasing check over W-bit values: returns (sorted, ok) where
/// ok = every element is below 2^W, and sorted = ok and
/// arr[j] <= arr[j + 1] for every j. When ok is false, sorted is false.
///
/// Every element is clamped first (clamp_bits_or::<W>, hint-satisfiable,
/// determined), so lt_bounded::<W> runs only on values below 2^W, which
/// is its precondition: its hinted flag is forced by the W-bit range
/// check on the difference and the honest hint always satisfies it.
/// a <= b is computed as !(b < a). Constraints: N clamp_bits_or and N - 1
/// lt_bounded gadgets. Total for every input; both flags are determined.
/// Arrays of length 0 or 1 are sorted. 1 <= W <= 128 (the bound of both
/// gadgets).
pub fn is_sorted_or<let N: u32, let W: u32>(arr: [Field; N]) -> (bool, bool) {
    static_assert((W >= 1) & (W <= 128), "is_sorted_or: W must be in 1..=128");
    let mut clamped = [0; N];
    let mut ok = true;
    for j in 0..N {
        let (v, in_range) = clamp_bits_or::<W>(arr[j]);
        clamped[j] = v;
        ok = ok & in_range;
    }
    let mut sorted = true;
    for j in 1..N {
        let descends = lt_bounded::<W>(clamped[j], clamped[j - 1]);
        sorted = sorted & !descends;
    }
    (sorted & ok, ok)
}

/// True when any flag is set; false for N = 0. Bool arithmetic only
/// (an OR chain), no failure source.
pub fn any<let N: u32>(flags: [bool; N]) -> bool {
    let mut r = false;
    for j in 0..N {
        r = r | flags[j];
    }
    r
}

/// True when every flag is set; true for N = 0. Bool products only, no
/// failure source.
pub fn all<let N: u32>(flags: [bool; N]) -> bool {
    let mut r = true;
    for j in 0..N {
        r = r & flags[j];
    }
    r
}

/// True when some element equals x; false for N = 0.
///
/// Uses T's Eq. For Field, bool, the integer types, and arrays and tuples
/// of them, std's `==` is one inversion gadget per Field-sized component
/// (hint-satisfiable for every input, determined), so the result is total
/// and determined; for a type of your own, totality is that of its Eq.
/// Constraints: N equalities and an OR chain. Cost: N equalities.
pub fn contains<T, let N: u32>(arr: [T; N], x: T) -> bool
where
    T: Eq,
{
    let mut r = false;
    for j in 0..N {
        r = r | (arr[j] == x);
    }
    r
}

/// The number of elements equal to x, as a Field (exact: at most
/// N < 2^32). Same equality and totality argument as contains.
/// Constraints: N equalities and linear sums. Cost: N equalities.
pub fn count_of<T, let N: u32>(arr: [T; N], x: T) -> Field
where
    T: Eq,
{
    let mut r: Field = 0;
    for j in 0..N {
        r += (arr[j] == x) as Field;
    }
    r
}

/// Shared body of min_of_or and max_of_or: clamp every element, then fold
/// with lt_bounded::<W> and a select, keeping the first element on ties.
/// For max the comparison is swapped.
fn extremum<let N: u32, let W: u32>(arr: [Field; N], want_max: bool) -> (Field, bool) {
    let mut ok = N != 0;
    let mut m: Field = 0;
    for j in 0..N {
        let (v, in_range) = clamp_bits_or::<W>(arr[j]);
        ok = ok & in_range;
        if j == 0 {
            m = v;
        } else {
            let better = if want_max {
                lt_bounded::<W>(m, v)
            } else {
                lt_bounded::<W>(v, m)
            };
            m = select_field(better, v, m);
        }
    }
    (select_field(ok, m, 0), ok)
}

/// The least element of an array of W-bit values: (min, true) when N >= 1
/// and every element is below 2^W; (0, false) otherwise.
///
/// Constraints: N clamp_bits_or::<W> (hint-satisfiable for every Field,
/// determined); N - 1 lt_bounded::<W> on clamped values (its precondition,
/// so hint-satisfiable; determined) and N - 1 selects; one select to 0.
/// Total for every input. Cost: N fits_bits gadgets and N - 1
/// lt_bounded. 1 <= W <= 128.
pub fn min_of_or<let N: u32, let W: u32>(arr: [Field; N]) -> (Field, bool) {
    static_assert((W >= 1) & (W <= 128), "min_of_or: W must be in 1..=128");
    extremum::<N, W>(arr, false)
}

/// The greatest element of an array of W-bit values: (max, true) when
/// N >= 1 and every element is below 2^W; (0, false) otherwise. Same
/// constraints and cost as min_of_or. 1 <= W <= 128.
pub fn max_of_or<let N: u32, let W: u32>(arr: [Field; N]) -> (Field, bool) {
    static_assert((W >= 1) & (W <= 128), "max_of_or: W must be in 1..=128");
    extremum::<N, W>(arr, true)
}

// ---------------------------------------------------------------------
// Sorting
// ---------------------------------------------------------------------

/// Hint for sort_or: the permutation matrix m with m[k][j] = true exactly
/// when element j lands at position k of the non-decreasing order. With
/// v the values cast to u128 (truncating; exact for the clamped values
/// sort_or passes, all below 2^128), element j's position is its stable
/// rank, #{i : v[i] < v[j]} + #{i < j : v[i] == v[j]}. The ranks of N
/// values are a bijection onto 0..N-1: for i != j either the values
/// differ, and the smaller one's rank is lower, or they are equal, and the
/// earlier one's rank is lower. Truncating casts, u128 comparisons and
/// equalities cast to u32, counts below N, and equality tests between loop
/// indices: no branch on the values, no index derived from them, no
/// integer And or Or, no arithmetic that can overflow. Trap-free for every
/// argument and within the co-noir hint rules (core.nr).
unconstrained fn hint_sort_matrix<let N: u32>(c: [Field; N]) -> [[bool; N]; N] {
    let mut v = [0; N];
    for j in 0..N {
        v[j] = c[j] as u128;
    }
    let mut rank = [0; N];
    for j in 0..N {
        let mut r: u32 = 0;
        for i in 0..N {
            r += (v[i] < v[j]) as u32;
        }
        for i in 0..j {
            r += (v[i] == v[j]) as u32;
        }
        rank[j] = r;
    }
    let mut m = [[false; N]; N];
    for k in 0..N {
        for j in 0..N {
            m[k][j] = rank[j] == k;
        }
    }
    m
}

/// Constraint half of sort_or, split out so tests can feed wrong hints.
/// PRECONDITION: every c[j] < 2^W (the caller's clamp), 1 <= W <= 128.
/// Constraints on the hinted bool matrix m:
/// 1. booleanity of every entry (the compiler's type constraint on the
///    hint's [[bool; N]; N] return);
/// 2. every row sum and every column sum equals 1 (2N assertions);
/// 3. s[k] = sum_j m[k][j] * c[j] (definitions);
/// 4. for 1 <= k < N, RANGE (s[k] - s[k - 1]) to W bits.
/// Returns s.
/// Hint-satisfiable: the honest m is the permutation matrix of the stable
/// ranks (hint_sort_matrix), so each row and column holds exactly one
/// true, s is c in non-decreasing order, and each difference is in
/// [0, 2^W).
/// Determined: a sum of at most N < p bools equals 1 in the field only
/// when exactly one is true, so m is a permutation matrix and s is a
/// rearrangement of c, every s[k] below 2^W. If s[k] < s[k - 1] the field
/// difference is p - d for some 1 <= d < 2^W, at least p - 2^128 > 2^W, so
/// the range fails: s is non-decreasing. A multiset has exactly one
/// non-decreasing arrangement, so s is determined (m itself is not unique
/// when c has repeated values, which does not matter).
/// Load-bearing: without the column sums, two rows may pick one element
/// and drop another; without the ranges, any permutation passes.
pub(crate) fn constrain_sort<let N: u32, let W: u32>(
    c: [Field; N],
    m: [[bool; N]; N],
) -> [Field; N] {
    let mut s = [0; N];
    for k in 0..N {
        let mut row: Field = 0;
        let mut col: Field = 0;
        let mut v: Field = 0;
        for j in 0..N {
            row += m[k][j] as Field;
            col += m[j][k] as Field;
            v += (m[k][j] as Field) * c[j];
        }
        assert_eq(row, 1);
        assert_eq(col, 1);
        s[k] = v;
    }
    for k in 1..N {
        (s[k] - s[k - 1]).assert_max_bit_size::<W>();
    }
    s
}

/// Total sort of an array of W-bit values: (sorted, true) with sorted the
/// elements in non-decreasing order when every element is below 2^W;
/// (all zeros, false) otherwise.
///
/// Every element is clamped (clamp_bits_or::<W>), a hinted permutation
/// matrix sorts the clamped values, and constrain_sort pins it: row and
/// column sums make it a bijection, and a W-bit range on each adjacent
/// difference makes the result non-decreasing (argument at
/// constrain_sort). The hint runs on the clamped values, which are
/// determined, so the honest matrix exists for every input. Finally N
/// selects to 0 on ok.
///
/// Constraints: N clamp_bits_or::<W> (hint-satisfiable for every Field,
/// determined); N^2 booleanity constraints, 2N sums of N terms, N sums of N
/// products, N - 1 W-bit RANGEs (all hint-satisfiable, the result
/// determined); N selects. Cost O(N^2): N fits_bits gadgets plus about
/// 4N^2 gates for the matrix; with bb 6.0.0 at W = 64 one call adds about
/// 240, 600 and 1600 gates for N = 4, 8 and 16. It suits short arrays. For
/// arrays of native integers or of Fields known to be in range, std's
/// sort is cheaper and already total. 1 <= W <= 128.
pub fn sort_or<let N: u32, let W: u32>(arr: [Field; N]) -> ([Field; N], bool) {
    static_assert((W >= 1) & (W <= 128), "sort_or: W must be in 1..=128");
    let mut c = [0; N];
    let mut ok = true;
    for j in 0..N {
        let (v, in_range) = clamp_bits_or::<W>(arr[j]);
        c[j] = v;
        ok = ok & in_range;
    }
    // Safety: constrain_sort pins the result (its argument).
    let m = unsafe { hint_sort_matrix(c) };
    let s = constrain_sort::<N, W>(c, m);
    let mut out = [0; N];
    for k in 0..N {
        out[k] = select_field(ok, s[k], 0);
    }
    (out, ok)
}

mod tests {
    use crate::core::two_pow;
    use crate::test_support::wit;
    use super::{
        all, any, constrain_sort, contains, count_of, first_index_of_or, first_true_or,
        hint_sort_matrix, index_flags_or, index_or, is_sorted_or, max_of_or, min_of_or,
        prefix_mask_or, set_or, sort_or, subarray_or, sum_or, sum_wide_or,
    };

    global P_MINUS_1: Field = 0 - 1;
    global TWO_POW_128: Field = 0x100000000000000000000000000000000;

    #[test]
    fn index_flags_in_and_out_of_bounds() {
        let (f0, ok0) = index_flags_or::<4>(wit(0));
        assert(ok0);
        assert_eq(f0, [true, false, false, false]);
        let (f3, ok3) = index_flags_or::<4>(wit(3));
        assert(ok3);
        assert_eq(f3, [false, false, false, true]);
        let (f4, ok4) = index_flags_or::<4>(wit(4));
        assert(!ok4);
        assert_eq(f4, [false; 4]);
        let (fp, okp) = index_flags_or::<4>(wit(P_MINUS_1));
        assert(!okp);
        assert_eq(fp, [false; 4]);
        let (fe, oke) = index_flags_or::<0>(wit(0));
        assert(!oke);
        assert_eq(fe, []);
    }

    #[test]
    fn index_or_positive() {
        let arr = [10, 11, 12, 13, P_MINUS_1];
        let (v0, ok0) = index_or(wit(arr), wit(0));
        assert(ok0);
        assert_eq(v0, 10);
        let (v2, ok2) = index_or(wit(arr), wit(2));
        assert(ok2);
        assert_eq(v2, 12);
        let (v4, ok4) = index_or(wit(arr), wit(4));
        assert(ok4);
        assert_eq(v4, P_MINUS_1);
    }

    #[test]
    fn index_or_out_of_bounds_gives_default() {
        let arr = [10, 11, 12];
        let bad = [3, 4, 0x10000000000000000, TWO_POW_128, TWO_POW_128 + 1, P_MINUS_1];
        for b in 0..6 {
            let (v, ok) = index_or(wit(arr), wit(bad[b]));
            assert(!ok);
            assert_eq(v, 0);
        }
        let empty: [Field; 0] = [];
        let (ve, oke) = index_or(wit(empty), wit(0));
        assert(!oke);
        assert_eq(ve, 0);
    }

    #[test]
    fn index_or_compound_elements() {
        let arr: [(Field, bool); 3] = [(1, true), (2, false), (3, true)];
        let (v, ok) = index_or(wit(arr), wit(1));
        assert(ok);
        assert_eq(v, (2, false));
        let (d, okd) = index_or(wit(arr), wit(3));
        assert(!okd);
        assert_eq(d, (0, false));
        let rows = [[1, 2], [3, 4]];
        let (r, okr) = index_or(wit(rows), wit(1));
        assert(okr);
        assert_eq(r, [3, 4]);
    }

    #[test]
    fn set_or_writes_one_position() {
        let arr = [1, 2, 3, 4];
        let (out, ok) = set_or(wit(arr), wit(2), wit(9));
        assert(ok);
        assert_eq(out, [1, 2, 9, 4]);
        let (out0, ok0) = set_or(wit(arr), wit(0), wit(P_MINUS_1));
        assert(ok0);
        assert_eq(out0, [P_MINUS_1, 2, 3, 4]);
        let (out3, ok3) = set_or(wit(arr), wit(3), wit(0));
        assert(ok3);
        assert_eq(out3, [1, 2, 3, 0]);
    }

    #[test]
    fn set_or_out_of_bounds_leaves_array() {
        let arr = [1, 2, 3, 4];
        let bad = [4, 5, TWO_POW_128, P_MINUS_1];
        for b in 0..4 {
            let (out, ok) = set_or(wit(arr), wit(bad[b]), wit(9));
            assert(!ok);
            assert_eq(out, arr);
        }
    }

    #[test]
    fn subarray_or_windows() {
        let arr = [10, 11, 12, 13, 14];
        let (w0, ok0) = subarray_or::<Field, 5, 3>(wit(arr), wit(0));
        assert(ok0);
        assert_eq(w0, [10, 11, 12]);
        let (w2, ok2) = subarray_or::<Field, 5, 3>(wit(arr), wit(2));
        assert(ok2);
        assert_eq(w2, [12, 13, 14]);
        let (wf, okf) = subarray_or::<Field, 5, 5>(wit(arr), wit(0));
        assert(okf);
        assert_eq(wf, arr);
        let (wz, okz) = subarray_or::<Field, 5, 0>(wit(arr), wit(5));
        assert(okz);
        assert_eq(wz, []);
    }

    #[test]
    fn subarray_or_overrun_gives_defaults() {
        let arr = [10, 11, 12, 13, 14];
        // start 3 would need positions 3, 4, 5; start p - 1 must not wrap to 0.
        let bad = [3, 4, 5, TWO_POW_128, P_MINUS_1];
        for b in 0..5 {
            let (w, ok) = subarray_or::<Field, 5, 3>(wit(arr), wit(bad[b]));
            assert(!ok);
            assert_eq(w, [0, 0, 0]);
        }
        let (wz, okz) = subarray_or::<Field, 5, 0>(wit(arr), wit(6));
        assert(!okz);
        assert_eq(wz, []);
    }

    #[test]
    fn prefix_mask_lengths() {
        let (m0, ok0) = prefix_mask_or::<4>(wit(0));
        assert(ok0);
        assert_eq(m0, [false; 4]);
        let (m1, ok1) = prefix_mask_or::<4>(wit(1));
        assert(ok1);
        assert_eq(m1, [true, false, false, false]);
        let (m3, ok3) = prefix_mask_or::<4>(wit(3));
        assert(ok3);
        assert_eq(m3, [true, true, true, false]);
        let (m4, ok4) = prefix_mask_or::<4>(wit(4));
        assert(ok4);
        assert_eq(m4, [true; 4]);
        let bad = [5, 6, TWO_POW_128, P_MINUS_1];
        for b in 0..4 {
            let (m, ok) = prefix_mask_or::<4>(wit(bad[b]));
            assert(!ok);
            assert_eq(m, [false; 4]);
        }
        let (me, oke) = prefix_mask_or::<0>(wit(0));
        assert(oke);
        assert_eq(me, []);
        let (_, okb) = prefix_mask_or::<0>(wit(1));
        assert(!okb);
    }

    #[test]
    fn sum_wide_exact_and_clamped() {
        let (s, ok) = sum_wide_or::<3, 8>(wit([1, 2, 3]));
        assert(ok);
        assert_eq(s, 6);
        let (smax, okmax) = sum_wide_or::<3, 8>(wit([255, 255, 255]));
        assert(okmax);
        assert_eq(smax, 765);
        // out-of-range elements contribute 0 and clear ok
        let (s1, ok1) = sum_wide_or::<3, 8>(wit([1, 256, 3]));
        assert(!ok1);
        assert_eq(s1, 0);
        let (s2, ok2) = sum_wide_or::<3, 8>(wit([1, P_MINUS_1, 3]));
        assert(!ok2);
        assert_eq(s2, 0);
        let (s3, ok3) = sum_wide_or::<2, 8>(wit([257, TWO_POW_128]));
        assert(!ok3);
        assert_eq(s3, 0);
    }

    #[test]
    fn sum_wide_widest_does_not_wrap() {
        let m = two_pow::<127>() - 1;
        let (s, ok) = sum_wide_or::<4, 127>(wit([m, m, m, m]));
        assert(ok);
        assert_eq(s, 4 * m);
        let (s0, ok0) = sum_wide_or::<0, 8>(wit([]));
        assert(ok0);
        assert_eq(s0, 0);
        let m128 = two_pow::<128>() - 1;
        let (s1, ok1) = sum_wide_or::<3, 128>(wit([m128, m128, m128]));
        assert(ok1);
        assert_eq(s1, 3 * m128);
        let (s2, ok2) = sum_or::<2, 128>(wit([m128 - 1, 1]));
        assert(ok2);
        assert_eq(s2, m128);
        let (s3, ok3) = sum_or::<2, 128>(wit([m128, 1]));
        assert(!ok3);
        assert_eq(s3, 0);
    }

    #[test]
    fn sum_or_fits_and_overflows() {
        let (s, ok) = sum_or::<2, 8>(wit([100, 155]));
        assert(ok);
        assert_eq(s, 255);
        let (s0, ok0) = sum_or::<2, 8>(wit([0, 0]));
        assert(ok0);
        assert_eq(s0, 0);
        // sum 256 does not fit 8 bits
        let (s1, ok1) = sum_or::<2, 8>(wit([100, 156]));
        assert(!ok1);
        assert_eq(s1, 0);
        // element out of range even though the clamped sum fits
        let (s2, ok2) = sum_or::<2, 8>(wit([1, 256]));
        assert(!ok2);
        assert_eq(s2, 0);
        let (s3, ok3) = sum_or::<2, 8>(wit([P_MINUS_1, 1]));
        assert(!ok3);
        assert_eq(s3, 0);
        let m = two_pow::<64>() - 1;
        let (s4, ok4) = sum_or::<2, 64>(wit([m, 1]));
        assert(!ok4);
        assert_eq(s4, 0);
        let (s5, ok5) = sum_or::<2, 64>(wit([m - 1, 1]));
        assert(ok5);
        assert_eq(s5, m);
    }

    #[test]
    fn first_true_positions() {
        let (i0, f0) = first_true_or(wit([true, true, false]));
        assert(f0);
        assert_eq(i0, 0);
        let (i1, f1) = first_true_or(wit([false, true, true]));
        assert(f1);
        assert_eq(i1, 1);
        let (i2, f2) = first_true_or(wit([false, false, true]));
        assert(f2);
        assert_eq(i2, 2);
        let (in_, fn_) = first_true_or(wit([false, false, false]));
        assert(!fn_);
        assert_eq(in_, 0);
        let (ie, fe) = first_true_or(wit([]));
        assert(!fe);
        assert_eq(ie, 0);
    }

    #[test]
    fn first_index_of_cases() {
        let arr = [5, 7, 5, P_MINUS_1, 7];
        let (i, found) = first_index_of_or(wit(arr), wit(7));
        assert(found);
        assert_eq(i, 1);
        let (i5, f5) = first_index_of_or(wit(arr), wit(5));
        assert(f5);
        assert_eq(i5, 0);
        let (ip, fp) = first_index_of_or(wit(arr), wit(P_MINUS_1));
        assert(fp);
        assert_eq(ip, 3);
        let (in_, fn_) = first_index_of_or(wit(arr), wit(6));
        assert(!fn_);
        assert_eq(in_, 0);
        let (iz, fz) = first_index_of_or(wit(arr), wit(0));
        assert(!fz);
        assert_eq(iz, 0);
    }

    #[test]
    fn is_sorted_or_cases() {
        let (s, ok) = is_sorted_or::<4, 8>(wit([0, 1, 1, 255]));
        assert(ok);
        assert(s);
        let (su, oku) = is_sorted_or::<4, 8>(wit([0, 2, 1, 255]));
        assert(oku);
        assert(!su);
        let (sd, okd) = is_sorted_or::<2, 8>(wit([255, 0]));
        assert(okd);
        assert(!sd);
        let (s1, ok1) = is_sorted_or::<1, 8>(wit([7]));
        assert(ok1);
        assert(s1);
        let (s0, ok0) = is_sorted_or::<0, 8>(wit([]));
        assert(ok0);
        assert(s0);
        let m = two_pow::<126>() - 1;
        let (sw, okw) = is_sorted_or::<3, 126>(wit([0, m - 1, m]));
        assert(okw);
        assert(sw);
        let (sw2, okw2) = is_sorted_or::<2, 126>(wit([m, 0]));
        assert(okw2);
        assert(!sw2);
        let m127 = two_pow::<127>() - 1;
        assert_eq(is_sorted_or::<3, 127>(wit([0, m127 - 1, m127])), (true, true));
        let m128 = two_pow::<128>() - 1;
        assert_eq(is_sorted_or::<3, 128>(wit([0, m128 - 1, m128])), (true, true));
        assert_eq(is_sorted_or::<2, 128>(wit([m128, 0])), (false, true));
        assert_eq(is_sorted_or::<2, 128>(wit([0, m128 + 1])), (false, false));
    }

    #[test]
    fn is_sorted_or_out_of_range() {
        // 256 is out of 8-bit range: ok false and sorted forced false,
        // even though the raw values ascend.
        let (s, ok) = is_sorted_or::<3, 8>(wit([1, 2, 256]));
        assert(!ok);
        assert(!s);
        let (sp, okp) = is_sorted_or::<2, 8>(wit([0, P_MINUS_1]));
        assert(!okp);
        assert(!sp);
        let (sh, okh) = is_sorted_or::<2, 64>(wit([0, TWO_POW_128]));
        assert(!okh);
        assert(!sh);
    }

    #[test]
    fn any_all_cases() {
        assert(any(wit([false, true, false])));
        assert(!any(wit([false, false])));
        assert(!any(wit([])));
        assert(all(wit([true, true])));
        assert(!all(wit([true, false, true])));
        assert(all(wit([])));
    }

    #[test]
    fn contains_and_count() {
        let arr = [5, 7, 5, P_MINUS_1];
        assert(contains(wit(arr), wit(7)));
        assert(contains(wit(arr), wit(P_MINUS_1)));
        assert(!contains(wit(arr), wit(6)));
        assert(!contains(wit(arr), wit(0)));
        let empty: [Field; 0] = [];
        assert(!contains(wit(empty), wit(0)));
        assert_eq(count_of(wit(arr), wit(5)), 2);
        assert_eq(count_of(wit(arr), wit(6)), 0);
        assert_eq(count_of(wit(empty), wit(0)), 0);
        assert(contains(wit([true, false]), wit(false)));
        assert(!contains(wit([true, true]), wit(false)));
        assert_eq(count_of(wit([3 as u8, 3, 4]), wit(3)), 2);
        assert(contains(wit([(1, true), (2, false)]), wit((2, false))));
        assert(!contains(wit([(1, true), (2, false)]), wit((2, true))));
    }

    #[test]
    fn min_max_cases() {
        assert_eq(min_of_or::<4, 8>(wit([7, 3, 255, 3])), (3, true));
        assert_eq(max_of_or::<4, 8>(wit([7, 3, 255, 3])), (255, true));
        assert_eq(min_of_or::<1, 8>(wit([9])), (9, true));
        assert_eq(max_of_or::<1, 8>(wit([0])), (0, true));
        // empty: no extremum
        assert_eq(min_of_or::<0, 8>(wit([])), (0, false));
        assert_eq(max_of_or::<0, 8>(wit([])), (0, false));
        // out of range elements
        assert_eq(min_of_or::<3, 8>(wit([7, 256, 3])), (0, false));
        assert_eq(max_of_or::<2, 8>(wit([P_MINUS_1, 3])), (0, false));
        let m = two_pow::<128>() - 1;
        assert_eq(min_of_or::<3, 128>(wit([m, 0, m - 1])), (0, true));
        assert_eq(max_of_or::<3, 128>(wit([m - 1, 0, m])), (m, true));
        assert_eq(max_of_or::<2, 128>(wit([m, TWO_POW_128])), (0, false));
        assert_eq(min_of_or::<2, 1>(wit([1, 0])), (0, true));
    }

    #[test]
    fn sort_or_cases() {
        assert_eq(sort_or::<5, 8>(wit([3, 1, 255, 0, 1])), ([0, 1, 1, 3, 255], true));
        assert_eq(sort_or::<3, 8>(wit([1, 2, 3])), ([1, 2, 3], true));
        assert_eq(sort_or::<3, 8>(wit([3, 2, 1])), ([1, 2, 3], true));
        assert_eq(sort_or::<4, 8>(wit([7, 7, 7, 7])), ([7, 7, 7, 7], true));
        assert_eq(sort_or::<1, 8>(wit([9])), ([9], true));
        assert_eq(sort_or::<0, 8>(wit([])), ([], true));
        let m = two_pow::<128>() - 1;
        assert_eq(sort_or::<3, 128>(wit([m, 0, m - 1])), ([0, m - 1, m], true));
        let m126 = two_pow::<126>() - 1;
        assert_eq(sort_or::<3, 126>(wit([m126, 5, m126])), ([5, m126, m126], true));
    }

    #[test]
    fn sort_or_out_of_range() {
        assert_eq(sort_or::<3, 8>(wit([3, 256, 1])), ([0, 0, 0], false));
        assert_eq(sort_or::<2, 8>(wit([P_MINUS_1, 0])), ([0, 0], false));
        assert_eq(sort_or::<2, 128>(wit([TWO_POW_128, 1])), ([0, 0], false));
    }

    #[test]
    unconstrained fn sort_hint_is_a_stable_permutation() {
        let m = hint_sort_matrix([5, 2, 5, 0]);
        // ranks: 5 -> 2, 2 -> 1, 5 -> 3, 0 -> 0
        assert_eq(m[0], [false, false, false, true]);
        assert_eq(m[1], [false, true, false, false]);
        assert_eq(m[2], [true, false, false, false]);
        assert_eq(m[3], [false, false, true, false]);
        let _ = hint_sort_matrix([P_MINUS_1, 0, TWO_POW_128]);
        let _ = hint_sort_matrix([]);
    }

    // Wrong hints for constrain_sort on c = [5, 2, 9].

    #[test]
    fn sort_honest_and_alternative_hints_accepted() {
        let s = constrain_sort::<3, 8>(
            wit([5, 2, 9]),
            wit(
                [[false, true, false], [true, false, false], [false, false, true]],
            ),
        );
        assert_eq(s, [2, 5, 9]);
        // with a repeated value either matching is accepted; s is the same
        let a = constrain_sort::<2, 8>(wit([4, 4]), wit([[true, false], [false, true]]));
        let b = constrain_sort::<2, 8>(wit([4, 4]), wit([[false, true], [true, false]]));
        assert_eq(a, b);
    }

    #[test(should_fail)]
    fn sort_unsorted_permutation_rejected() {
        let _ = constrain_sort::<3, 8>(
            [5, 2, 9],
            [[true, false, false], [false, true, false], [false, false, true]],
        );
    }

    #[test(should_fail)]
    fn sort_row_with_two_entries_rejected() {
        // rows 0 and 1 together pick 2 + 5 = 7 at position 0
        let _ = constrain_sort::<3, 8>(
            [5, 2, 9],
            [[true, true, false], [false, false, false], [false, false, true]],
        );
    }

    #[test(should_fail)]
    fn sort_duplicated_element_rejected() {
        // rows pick 2, 2, 9: row sums are 1 but column 1 is used twice
        let _ = constrain_sort::<3, 8>(
            [5, 2, 9],
            [[false, true, false], [false, true, false], [false, false, true]],
        );
    }

    #[test(should_fail)]
    fn sort_wrapped_difference_rejected() {
        // [2^8 - 1, 0] in the wrong order: the difference is p - 255
        let _ = constrain_sort::<2, 8>([255, 0], [[true, false], [false, true]]);
    }
}
