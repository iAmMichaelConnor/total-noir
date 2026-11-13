use crate::ctl::{Outcome, Select};
use crate::test_support::wit;
use super::{from_parts_or, from_prefix_or, TotalBoundedVec};

global P_MINUS_1: Field = 0 - 1;

/// [10, 20, 30] in a BoundedVec of capacity 4 (one free slot).
fn three() -> BoundedVec<Field, 4> {
    BoundedVec::from_array([10, 20, 30])
}

fn full() -> BoundedVec<Field, 4> {
    BoundedVec::from_array([10, 20, 30, 40])
}

fn empty() -> BoundedVec<Field, 4> {
    BoundedVec::new()
}

/// Same length and the same storage, tail included (std's Eq ignores the
/// tail; the normal form is checked through storage()).
fn same<let M: u32>(a: BoundedVec<Field, M>, b: BoundedVec<Field, M>) -> bool {
    (a.len() == b.len()) & (a.storage() == b.storage())
}

#[test]
fn get_in_and_out_of_range() {
    let v = three();
    assert_eq(wit(v).get_or(wit(0)), (10, true));
    assert_eq(wit(v).get_or(wit(2)), (30, true));
    // past len but inside the storage, at MaxLen, far past it
    assert_eq(wit(v).get_or(wit(3)), (0, false));
    assert_eq(wit(v).get_or(wit(4)), (0, false));
    assert_eq(wit(v).get_or(wit(4294967295)), (0, false));
    assert_eq(empty().get_or(wit(0)), (0, false));
    assert_eq(full().get_or(wit(3)), (40, true));
}

#[test]
fn set_in_and_out_of_range() {
    let (w, ok) = three().set_or(wit(1), wit(21));
    assert(ok);
    assert(same(w, BoundedVec::from_array([10, 21, 30])));
    let (w, ok) = three().set_or(wit(3), wit(99));
    assert(!ok);
    assert(same(w, three()));
    let (w, ok) = three().set_or(wit(4294967295), wit(99));
    assert(!ok);
    assert(same(w, three()));
    let (w, ok) = empty().set_or(wit(0), wit(1));
    assert(!ok);
    assert(same(w, empty()));
    let (w, ok) = full().set_or(wit(3), wit(P_MINUS_1));
    assert(ok);
    assert_eq(wit(w).get_or(wit(3)), (P_MINUS_1, true));
}

#[test]
fn push_until_full() {
    let (w, ok) = empty().push_or(wit(7));
    assert(ok);
    assert(same(w, BoundedVec::from_array([7])));
    let (w, ok) = three().push_or(wit(40));
    assert(ok);
    assert(same(w, full()));
    let (w, ok) = full().push_or(wit(50));
    assert(!ok);
    assert(same(w, full()));
    // capacity 1 and capacity 0
    let one: BoundedVec<Field, 1> = BoundedVec::new();
    let (w, ok) = wit(one).push_or(wit(5));
    assert(ok);
    let (w2, ok2) = wit(w).push_or(wit(6));
    assert(!ok2);
    assert(same(w2, w));
    let none: BoundedVec<Field, 0> = BoundedVec::new();
    let (w, ok) = wit(none).push_or(wit(5));
    assert(!ok);
    assert_eq(w.len(), 0);
}

#[test]
fn pop_until_empty() {
    let (w, x, ok) = full().pop_or();
    assert(ok);
    assert_eq(x, 40);
    // the vacated slot is zeroed (normal form)
    assert(same(w, three()));
    let (w, x, ok) = BoundedVec::<Field, 4>::from_array([5]).pop_or();
    assert(ok);
    assert_eq(x, 5);
    assert(same(w, empty()));
    let (w, x, ok) = empty().pop_or();
    assert(!ok);
    assert_eq(x, 0);
    assert(same(w, empty()));
    let none: BoundedVec<Field, 0> = BoundedVec::new();
    let (_, x, ok) = wit(none).pop_or();
    assert(!ok);
    assert_eq(x, 0);
}

#[test]
fn set_len_grow_shrink_and_past_capacity() {
    // shrinking zeroes the dropped positions
    let (w, ok) = full().set_len_or(wit(2));
    assert(ok);
    assert(same(w, BoundedVec::from_array([10, 20])));
    assert(w == BoundedVec::from_array([10, 20]));
    // growing exposes the storage, as std's set_len does
    let raw: BoundedVec<Field, 4> = BoundedVec::from_parts([1, 2, 3, 4], 1);
    let (w, ok) = wit(raw).set_len_or(wit(3));
    assert(ok);
    assert_eq(w.storage(), [1, 2, 3, 0]);
    assert_eq(w.len(), 3);
    let (w, ok) = three().set_len_or(wit(4));
    assert(ok);
    assert_eq(w.len(), 4);
    let (w, ok) = three().set_len_or(wit(0));
    assert(ok);
    assert(same(w, empty()));
    // past MaxLen: unchanged
    let (w, ok) = three().set_len_or(wit(5));
    assert(!ok);
    assert(same(w, three()));
    let (w, ok) = full().set_len_or(wit(4294967295));
    assert(!ok);
    assert(same(w, full()));
}

#[test]
fn extend_from_array_fits_and_overflows() {
    let (w, ok) = empty().extend_from_array_or(wit([1, 2, 3, 4]));
    assert(ok);
    assert(same(w, BoundedVec::from_array([1, 2, 3, 4])));
    let (w, ok) = BoundedVec::<Field, 4>::from_array([1]).extend_from_array_or(wit([2, 3]));
    assert(ok);
    assert(same(w, BoundedVec::from_array([1, 2, 3])));
    let (w, ok) = three().extend_from_array_or(wit([40]));
    assert(ok);
    assert(same(w, full()));
    // one too many: unchanged
    let (w, ok) = three().extend_from_array_or(wit([40, 50]));
    assert(!ok);
    assert(same(w, three()));
    let (w, ok) = full().extend_from_array_or(wit([50]));
    assert(!ok);
    assert(same(w, full()));
    // empty array always fits
    let (w, ok) = full().extend_from_array_or(wit([]));
    assert(ok);
    assert(same(w, full()));
}

#[test]
fn extend_from_bounded_vec_fits_and_overflows() {
    let src: BoundedVec<Field, 3> = BoundedVec::from_array([7, 8]);
    let (w, ok) = BoundedVec::<Field, 4>::from_array([1, 2]).extend_from_bounded_vec_or(wit(src));
    assert(ok);
    assert(same(w, BoundedVec::from_array([1, 2, 7, 8])));
    let (w, ok) = empty().extend_from_bounded_vec_or(wit(src));
    assert(ok);
    assert(same(w, BoundedVec::from_array([7, 8])));
    // three + two > 4: unchanged
    let (w, ok) = three().extend_from_bounded_vec_or(wit(src));
    assert(!ok);
    assert(same(w, three()));
    // an empty source always fits, even onto a full vector
    let none: BoundedVec<Field, 3> = BoundedVec::new();
    let (w, ok) = full().extend_from_bounded_vec_or(wit(none));
    assert(ok);
    assert(same(w, full()));
    // a source wider than the destination, holding few elements
    let wide: BoundedVec<Field, 6> = BoundedVec::from_array([5]);
    let (w, ok) = three().extend_from_bounded_vec_or(wit(wide));
    assert(ok);
    assert(same(w, BoundedVec::from_array([10, 20, 30, 5])));
    let wide_full: BoundedVec<Field, 6> = BoundedVec::from_array([1, 2, 3, 4, 5, 6]);
    let (w, ok) = empty().extend_from_bounded_vec_or(wit(wide_full));
    assert(!ok);
    assert(same(w, empty()));
    // the source's tail past its length is not copied
    let dirty: BoundedVec<Field, 3> = BoundedVec::from_parts([9, 9, 9], 1);
    let (w, ok) = BoundedVec::<Field, 4>::from_array([1]).extend_from_bounded_vec_or(wit(dirty));
    assert(ok);
    assert_eq(w.storage(), [1, 9, 0, 0]);
    assert_eq(w.len(), 2);
}

#[test]
fn from_parts_flags_length_and_tail() {
    let (v, ok) = from_parts_or(wit([1, 2, 0, 0]), wit(2));
    assert(ok);
    assert(same(v, BoundedVec::from_array([1, 2])));
    let (v, ok) = from_parts_or(wit([1, 2, 3, 4]), wit(4));
    assert(ok);
    assert(same(v, BoundedVec::from_array([1, 2, 3, 4])));
    // a non-zero tail: flagged, empty
    let (v, ok) = from_parts_or(wit([1, 2, 3, 0]), wit(2));
    assert(!ok);
    assert(same(v, empty()));
    // length past MaxLen: flagged, empty
    let (v, ok) = from_parts_or(wit([0, 0, 0, 0]), wit(5));
    assert(!ok);
    assert(same(v, empty()));
    let (v, ok) = from_parts_or(wit([1, 0, 0, 0]), wit(4294967295));
    assert(!ok);
    assert(same(v, empty()));
    let (v, ok) = from_parts_or(wit([0, 0, 0, 0]), wit(0));
    assert(ok);
    assert(same(v, empty()));
}

#[test]
fn from_prefix_zeroes_the_tail() {
    let (v, ok) = from_prefix_or(wit([1, 2, 3, 4]), wit(2));
    assert(ok);
    assert(same(v, BoundedVec::from_array([1, 2])));
    let (v, ok) = from_prefix_or(wit([1, 2, 3, 4]), wit(4));
    assert(ok);
    assert_eq(v.storage(), [1, 2, 3, 4]);
    let (v, ok) = from_prefix_or(wit([1, 2, 3, 4]), wit(0));
    assert(ok);
    assert(same(v, empty()));
    let (v, ok) = from_prefix_or(wit([1, 2, 3, 4]), wit(5));
    assert(!ok);
    assert(same(v, empty()));
}

#[test]
fn validity_select_and_guard() {
    assert(three().is_valid());
    assert(empty().is_valid());
    assert(same(Select::select(true, three(), full()), three()));
    assert(same(Select::select(false, three(), full()), full()));
    let (pushed, ok) = full().push_or(wit(1));
    let state = Outcome::good().require(ok, 1).guard(pushed, full());
    assert(same(state, full()));
}

#[test]
fn other_element_types() {
    let v: BoundedVec<u8, 3> = BoundedVec::from_array([1, 255]);
    let (w, ok) = wit(v).push_or(wit(7));
    assert(ok);
    assert_eq(wit(w).get_or(wit(2)), (7, true));
    assert_eq(wit(w).get_or(wit(3)), (0, false));
    let pairs: BoundedVec<(Field, bool), 2> = BoundedVec::from_array([(1, true)]);
    let (w, ok) = wit(pairs).push_or(wit((2, false)));
    assert(ok);
    let (_, last, ok) = wit(w).pop_or();
    assert(ok);
    assert_eq(last, (2, false));
    let big: BoundedVec<u128, 2> = BoundedVec::from_array([0xffffffffffffffffffffffffffffffff]);
    assert_eq(wit(big).get_or(wit(0)), (0xffffffffffffffffffffffffffffffff, true));
    let (_, ok) = from_parts_or(wit([1 as u128, 2]), wit(1));
    assert(!ok);
}
