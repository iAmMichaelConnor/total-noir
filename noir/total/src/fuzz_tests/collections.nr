// collections: indexing, windows, flag folds and searches, and the
// W-bit sums, extrema, sortedness and sort.
use crate::collections::{
    all, any, contains, count_of, first_index_of_or, first_true_or, index_flags_or, index_or,
    is_sorted_or, max_of_or, min_of_or, prefix_mask_or, set_or, sort_or, subarray_or, sum_or,
    sum_wide_or,
};
use super::{fits, or_zero, shape};

global L: u32 = 5;

/// A position for an array of length L chosen by sel: each of 0..=L + 1,
/// p - 1, or i itself.
unconstrained fn shape_index(sel: u8, i: Field) -> Field {
    let k = (sel % 9) as Field;
    if k == 7 {
        0 - 1
    } else if k == 8 {
        i
    } else {
        k
    }
}

/// index_or, set_or, index_flags_or, prefix_mask_or at position i.
unconstrained fn index_model(
    arr: [Field; L],
    i: Field,
    v: Field,
) -> ((Field, bool), ([Field; L], bool), ([bool; L], bool), ([bool; L], bool)) {
    let inside = i.lt(L as Field);
    let mut set = arr;
    let mut flags = [false; L];
    let mut mask = [false; L];
    let mut read = 0;
    let len_ok = i.lt(L as Field + 1);
    for j in 0..L {
        if i == j as Field {
            read = arr[j];
            set[j] = v;
            flags[j] = true;
        }
        mask[j] = len_ok & (j as Field).lt(i);
    }
    ((read, inside), (set, inside), (flags, inside), (mask, len_ok))
}

/// The window arr[start..start + M] when it fits, else zeros.
unconstrained fn window_model<let M: u32>(arr: [Field; L], start: Field) -> ([Field; M], bool) {
    let ok = start.lt((L - M + 1) as Field);
    let mut out = [0; M];
    if ok {
        let s = start as u32;
        for k in 0..M {
            out[k] = arr[s + k];
        }
    }
    (out, ok)
}

fn check_window<let M: u32>(arr: [Field; L], start: Field) {
    // Safety: reference model, compared below.
    let want = unsafe { window_model::<M>(arr, start) };
    assert_eq(subarray_or::<Field, L, M>(arr, start), want);
}

#[test]
fn index_and_window(arr: [Field; L], si: u8, i: Field, v: Field) {
    // Safety: input selection; the value reaches the library as a witness.
    let i = unsafe { shape_index(si, i) };
    // Safety: reference model, compared below.
    let (read, set, flags, mask) = unsafe { index_model(arr, i, v) };
    assert_eq(index_or(arr, i), read);
    assert_eq(set_or(arr, i, v), set);
    assert_eq(index_flags_or::<L>(i), flags);
    assert_eq(prefix_mask_or::<L>(i), mask);
    check_window::<1>(arr, i);
    check_window::<3>(arr, i);
    check_window::<L>(arr, i);
}

// ---------------------------------------------------------------------
// Folds and searches
// ---------------------------------------------------------------------

/// any, all, first_true_or.
unconstrained fn flags_model<let N: u32>(flags: [bool; N]) -> (bool, bool, (Field, bool)) {
    let (mut some, mut every) = (false, true);
    let mut first = (0, false);
    for j in 0..N {
        if flags[j] & !some {
            first = (j as Field, true);
        }
        some = some | flags[j];
        every = every & flags[j];
    }
    (some, every, first)
}

fn check_flags<let N: u32>(flags: [bool; N]) {
    // Safety: reference model, compared below.
    let (some, every, first) = unsafe { flags_model(flags) };
    assert_eq((any(flags), all(flags)), (some, every));
    assert_eq(first_true_or(flags), first);
}

/// contains, count_of and the first position of x.
unconstrained fn search_model<T: Eq, let N: u32>(
    arr: [T; N],
    x: T,
) -> (bool, Field, (Field, bool)) {
    let mut count = 0;
    let mut first = (0, false);
    for j in 0..N {
        if arr[j] == x {
            if count == 0 {
                first = (j as Field, true);
            }
            count += 1;
        }
    }
    (count != 0, count, first)
}

#[test]
fn folds_and_search(flags: [bool; 6], arr: [Field; 6], sx: u8, x: Field, small: [u8; 6], y: u8) {
    check_flags(flags);
    // Flags from two-bit values: all set about one time in six.
    let mut dense = [false; 6];
    let mut tiny = [0; 6];
    for j in 0..6 {
        dense[j] = small[j] % 4 != 0;
        tiny[j] = small[j] % 4;
    }
    check_flags(dense);
    // x is a copy of an element two times in three.
    let x = if sx % 3 == 2 { x } else { arr[(sx % 6) as u32] };
    // Safety: reference model, compared below.
    let (has, count, first) = unsafe { search_model(arr, x) };
    assert_eq((contains(arr, x), count_of(arr, x)), (has, count));
    assert_eq(first_index_of_or(arr, x), first);
    // Repeats on the two-bit values, through T = u8.
    let y = y % 4;
    // Safety: reference model, compared below.
    let (has, count, _) = unsafe { search_model(tiny, y) };
    assert_eq((contains(tiny, y), count_of(tiny, y)), (has, count));
}

// ---------------------------------------------------------------------
// W-bit sums, extrema, sortedness and sort
// ---------------------------------------------------------------------

/// arr in non-decreasing order of canonical values (insertion sort).
unconstrained fn sorted<let N: u32>(arr: [Field; N]) -> [Field; N] {
    let mut out = arr;
    for i in 1..N {
        for k in 0..i {
            let j = i - k;
            if out[j].lt(out[j - 1]) {
                let t = out[j];
                out[j] = out[j - 1];
                out[j - 1] = t;
            }
        }
    }
    out
}

/// Elements for width w from the shaper, put in order when asked.
unconstrained fn shape_elements<let N: u32>(
    sel: [u8; N],
    arr: [Field; N],
    w: u32,
    presort: bool,
) -> [Field; N] {
    let mut out = [0; N];
    for j in 0..N {
        out[j] = shape(sel[j], arr[j], w);
    }
    if presort {
        sorted(out)
    } else {
        out
    }
}

/// sum_wide_or, sum_or, min_of_or, max_of_or, is_sorted_or (sorted, ok)
/// and sort_or, on W-bit elements.
unconstrained fn elements_model<let N: u32>(
    arr: [Field; N],
    w: u32,
) -> ([(Field, bool); 4], (bool, bool), ([Field; N], bool)) {
    let mut ok = true;
    let mut sum = 0;
    let mut ascending = true;
    let (mut lo, mut hi) = (arr[0], arr[0]);
    for j in 0..N {
        ok = ok & fits(arr[j], w);
        sum += arr[j];
        if arr[j].lt(lo) {
            lo = arr[j];
        }
        if hi.lt(arr[j]) {
            hi = arr[j];
        }
        if j > 0 {
            ascending = ascending & !arr[j].lt(arr[j - 1]);
        }
    }
    let ok_sum = ok & fits(sum, w);
    (
        [or_zero(ok, sum), or_zero(ok_sum, sum), or_zero(ok, lo), or_zero(ok, hi)],
        (ok & ascending, ok), (if ok { sorted(arr) } else { [0; N] }, ok),
    )
}

fn check_elements<let W: u32>(sel: [u8; L], arr: [Field; L], presort: bool) {
    // Safety: input selection; the values reach the library as witnesses.
    let arr = unsafe { shape_elements(sel, arr, W, presort) };
    // Safety: reference model, compared below.
    let (m, is_sorted, sorted) = unsafe { elements_model(arr, W) };
    assert_eq(sum_wide_or::<L, W>(arr), m[0]);
    assert_eq(sum_or::<L, W>(arr), m[1]);
    assert_eq(min_of_or::<L, W>(arr), m[2]);
    assert_eq(max_of_or::<L, W>(arr), m[3]);
    assert_eq(is_sorted_or::<L, W>(arr), is_sorted);
    assert_eq(sort_or::<L, W>(arr), sorted);
}

#[test]
fn sums_extrema_sort(sel: [u8; L], arr: [Field; L], presort: bool) {
    check_elements::<1>(sel, arr, presort);
    check_elements::<8>(sel, arr, presort);
    check_elements::<128>(sel, arr, presort);
}
