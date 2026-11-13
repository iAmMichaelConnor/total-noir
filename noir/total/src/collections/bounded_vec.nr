//! Flagged forms of std's BoundedVec<T, MaxLen> operations, total for
//! every input.
//!
//! std status (nargo 1.0.0-rc.3, std::collections::bounded_vec):
//! - Input-falsifiable, flagged here: get (index >= len), set (index >=
//!   len), push (full), pop (empty), set_len (len > MaxLen),
//!   extend_from_array and extend_from_bounded_vec (the result past
//!   MaxLen), from_parts (len > MaxLen; this module also flags a tail that
//!   is not zeroed). Each asserts, and get, set, push and pop also index
//!   the storage with a witness, which emits a memory opcode.
//! - get_unchecked and set_unchecked fail on an index at or past MaxLen
//!   (an out-of-bounds memory access): use collections::index_or and
//!   set_or on v.storage().
//! - extend_from_vector takes a vector whose length is not a compile-time
//!   constant: not provided; convert it to an array and use
//!   extend_from_array_or.
//! - Total as they stand: new, len, max_len, storage, from_array (its
//!   bound is a static_assert), truncate, Eq, and any, map, mapi,
//!   for_each, for_eachi (each loops to MaxLen with constant indices; the
//!   closure's own constraints are the caller's).
//!
//! API: the trait TotalBoundedVec, implemented for BoundedVec<T, MaxLen>
//! with T: Select, so the forms read as methods (v.push_or(x)); each
//! returns the new vector and a determined flag instead of mutating, and
//! on ok = false returns the input unchanged (the one exception, a broken
//! length, is below). An element read on ok = false is zeroed(). The constructors
//! from_parts_or and from_prefix_or are free functions. Select is
//! implemented for BoundedVec, so ctl::Outcome::guard applies to it.
//! Indices and lengths are u32 like std's, so the u32 type invariant
//! bounds them below 2^32, and comparisons between them are one
//! core::lt_bounded::<32> each (a hinted bit and one 32-bit RANGE).
//!
//! Lengths that break the invariant. std's constructors and mutators
//! assert or keep len <= MaxLen, but a BoundedVec entry-point parameter
//! (an ordinary Prover.toml input) and one returned by an unconstrained
//! function carry only the u32 range check on len, so len > MaxLen is an
//! input like any other. Every form here checks the length: on
//! len > MaxLen the flag is false and a returned vector is empty, with
//! zeroed storage (such a vector cannot be returned unchanged, because
//! from_parts asserts len <= MaxLen). The output length is always selected from values the
//! constraints bound by MaxLen, so BoundedVec::from_parts' own assert
//! holds for every satisfying witness; implied_range::<32> before the cast
//! to u32 makes the cast exact. Unit tests cannot build such a vector (no
//! std function does); noir/total_witness_check executes every form on
//! entry-point vectors with len = 9 and len = 2^32 - 1.
//!
//! Normal form: positions at or past len hold zeroed values
//! (std::mem::zeroed). from_parts_or and from_prefix_or return it;
//! push_or, set_or, the extends and Select keep it, and return it on a
//! broken length; pop_or and set_len_or keep it too by zeroing the
//! positions they drop, where std leaves the old values in storage. A
//! valid input that is not in normal form (only a prover-altered witness
//! can be one) passes through with its tail as it was. std's Eq ignores
//! positions at or past len, so every result is == to std's.
//!
//! No memory opcodes. Every position is reached through equality flags
//! against constants (collections::index_flags_or and prefix_mask_or) and
//! selects, never through a witness index. Costs below count eq gadgets
//! (the inversion gadget), T-selects (one Select of T), lt_bounded::<32>
//! checks, and the output rebuild (one 32-bit RANGE and from_parts'
//! comparison).

use crate::collections::{index_flags_or, prefix_mask_or};
use crate::core::{eq, implied_range, lt_bounded, select_field};
use crate::ctl::Select;
use std::mem::zeroed;
use std::static_assert;

/// len <= MaxLen for a u32 length (below 2^32 by the type, the
/// precondition of lt_bounded::<32> on both sides). One lt_bounded::<32>.
fn len_ok<let MaxLen: u32>(len: Field) -> bool {
    !lt_bounded::<32>(MaxLen as Field, len)
}

/// BoundedVec from storage and a length that the caller's constraints
/// bound by MaxLen for every satisfying witness (PRECONDITION). The
/// 32-bit RANGE and from_parts' len <= MaxLen then hold whenever the
/// earlier constraints do, so they add no failure source.
fn rebuild<T, let MaxLen: u32>(storage: [T; MaxLen], len: Field) -> BoundedVec<T, MaxLen> {
    BoundedVec::from_parts(storage, implied_range::<32>(len) as u32)
}

/// The element at the one set flag, zeroed when no flag is set: a fold
/// of T-selects from zeroed(). At most one flag may be set
/// (PRECONDITION; true for index_flags_or). M T-selects.
pub(crate) fn pick<T, let M: u32>(arr: [T; M], flags: [bool; M]) -> T
where
    T: Select,
{
    let mut v = zeroed();
    for j in 0..M {
        v = T::select(flags[j], arr[j], v);
    }
    v
}

/// arr with positions at or past len zeroed, and ok = (len <= M); when
/// len > M every position is zeroed. Constraints: prefix_mask_or::<M>(len)
/// (M + 1 eq gadgets, hint-satisfiable for every Field len, determined)
/// and M T-selects.
pub(crate) fn keep_prefix<T, let M: u32>(arr: [T; M], len: Field) -> ([T; M], bool)
where
    T: Select,
{
    let (mask, ok) = prefix_mask_or::<M>(len);
    let mut out = arr;
    for j in 0..M {
        out[j] = T::select(mask[j], arr[j], zeroed());
    }
    (out, ok)
}

/// Flagged BoundedVec operations; see the module comment for the shared
/// conventions (input unchanged on ok = false, empty and zeroed on a
/// broken length, normal form kept, no memory opcodes).
pub trait TotalBoundedVec<T> {
    /// len <= MaxLen. Cost: one lt_bounded::<32>.
    fn is_valid(self) -> bool;
    /// (element at index, ok) with ok = index < len <= MaxLen; zeroed when
    /// ok is false.
    fn get_or(self, index: u32) -> (T, bool);
    /// The vector with position index replaced, ok = index < len <= MaxLen.
    fn set_or(self, index: u32, value: T) -> (Self, bool);
    /// The vector with elem appended, ok = len < MaxLen.
    fn push_or(self, elem: T) -> (Self, bool);
    /// (the vector without its last element, that element, ok) with
    /// ok = 1 <= len <= MaxLen; the element is zeroed when ok is false.
    fn pop_or(self) -> (Self, T, bool);
    /// The vector with length len, ok = len <= MaxLen.
    fn set_len_or(self, len: u32) -> (Self, bool);
    /// The vector with array appended, ok = len + Len <= MaxLen.
    fn extend_from_array_or<let Len: u32>(self, array: [T; Len]) -> (Self, bool);
    /// The vector with vec's elements appended, ok = len <= MaxLen,
    /// vec.len() <= Len and len + vec.len() <= MaxLen.
    fn extend_from_bounded_vec_or<let Len: u32>(self, vec: BoundedVec<T, Len>) -> (Self, bool);
}

impl<T, let MaxLen: u32> TotalBoundedVec<T> for BoundedVec<T, MaxLen>
where
    T: Select,
{
    fn is_valid(self) -> bool {
        len_ok::<MaxLen>(self.len() as Field)
    }

    /// Constraints: index_flags_or::<MaxLen>(index) (MaxLen eq gadgets);
    /// ok = lt_bounded::<32>(index, len) & len_ok (both sides below 2^32
    /// by the u32 type); pick, and one final select that zeroes the value
    /// when index is below MaxLen but not below len. Determined: the flags
    /// and both comparisons are. Cost: MaxLen eq gadgets, MaxLen + 1
    /// T-selects, two lt_bounded::<32>.
    fn get_or(self, index: u32) -> (T, bool) {
        let len = self.len() as Field;
        let i = index as Field;
        let ok = lt_bounded::<32>(i, len) & len_ok::<MaxLen>(len);
        let (at, _) = index_flags_or::<MaxLen>(i);
        (T::select(ok, pick(self.storage(), at), zeroed()), ok)
    }

    /// ok as get_or. The write position is select(ok, index, MaxLen),
    /// a value no flag matches when ok is false, so the eq-scan of it
    /// writes nothing then: out[j] = select(e_j, value, kept_j) with
    /// kept_j = select(valid, storage[j], zeroed). Output: len and the
    /// storage on a valid length, else empty and zeroed. Cost: MaxLen eq
    /// gadgets, 2*MaxLen T-selects, two lt_bounded::<32>, the rebuild.
    fn set_or(self, index: u32, value: T) -> (Self, bool) {
        let len = self.len() as Field;
        let i = index as Field;
        let valid = len_ok::<MaxLen>(len);
        let ok = lt_bounded::<32>(i, len) & valid;
        let (at, _) = index_flags_or::<MaxLen>(select_field(ok, i, MaxLen as Field));
        let s = self.storage();
        let mut out = s;
        for j in 0..MaxLen {
            out[j] = T::select(at[j], value, T::select(valid, s[j], zeroed()));
        }
        (rebuild(out, select_field(valid, len, 0)), ok)
    }

    /// (e_j, room) = index_flags_or::<MaxLen>(len): e_j = (len == j) and
    /// room = len < MaxLen, the flag. full = (len == MaxLen) (one eq
    /// gadget); valid = room | full (exclusive). out[j] = select(e_j,
    /// elem, select(valid, storage[j], zeroed)) writes position len only,
    /// and zeroes the storage on a broken length. Output length
    /// room*(len + 1) + full*MaxLen: len + 1 on ok, len when full, 0 on a
    /// broken length, never above MaxLen. Cost: MaxLen + 1 eq gadgets,
    /// 2*MaxLen T-selects, the rebuild.
    fn push_or(self, elem: T) -> (Self, bool) {
        let len = self.len() as Field;
        let (at, room) = index_flags_or::<MaxLen>(len);
        let full = eq(len, MaxLen as Field);
        let valid = room | full;
        let s = self.storage();
        let mut out = s;
        for j in 0..MaxLen {
            out[j] = T::select(at[j], elem, T::select(valid, s[j], zeroed()));
        }
        let new_len = (room as Field) * (len + 1) + (full as Field) * (MaxLen as Field);
        (rebuild(out, new_len), room)
    }

    /// (e_j, ok) = index_flags_or::<MaxLen>(len - 1): e_j = (len - 1 == j),
    /// and their OR is exactly 1 <= len <= MaxLen (len = 0 gives p - 1,
    /// which matches no constant). valid = ok | (len == 0) (one eq gadget).
    /// The element is pick(storage, e), and the vacated slot is zeroed, as
    /// is every slot on a broken length: out[j] = select(e_j | !valid,
    /// zeroed, s[j]). Output length ok*(len - 1): when ok is false the
    /// length was 0 (the input is returned unchanged) or broken (empty
    /// and zeroed). Cost: MaxLen + 1 eq gadgets, 2*MaxLen T-selects, the
    /// rebuild.
    fn pop_or(self) -> (Self, T, bool) {
        let len = self.len() as Field;
        let (at, ok) = index_flags_or::<MaxLen>(len - 1);
        let valid = ok | eq(len, 0);
        let s = self.storage();
        let mut out = s;
        for j in 0..MaxLen {
            out[j] = T::select(at[j] | !valid, zeroed(), s[j]);
        }
        (rebuild(out, (ok as Field) * (len - 1)), pick(s, at), ok)
    }

    /// (mask, fits) = prefix_mask_or::<MaxLen>(len): mask[j] = (j < len),
    /// fits = (len <= MaxLen); ok = fits and the input length is valid. On
    /// ok, positions below len are kept and the rest zeroed (std keeps the
    /// old values; growing exposes the storage as std does); on ok = false
    /// the input is unchanged when its length is valid, else empty and
    /// zeroed: out[j] = select(old_valid & (mask[j] | !fits), s[j],
    /// zeroed). Output length: len on ok, else the old length if valid,
    /// else 0. Cost: MaxLen + 1 eq gadgets, MaxLen T-selects, one
    /// lt_bounded::<32>, the rebuild.
    fn set_len_or(self, len: u32) -> (Self, bool) {
        let old = self.len() as Field;
        let new = len as Field;
        let (mask, fits) = prefix_mask_or::<MaxLen>(new);
        let old_valid = len_ok::<MaxLen>(old);
        let ok = fits & old_valid;
        let s = self.storage();
        let mut out = s;
        for j in 0..MaxLen {
            out[j] = T::select(old_valid & (mask[j] | !fits), s[j], zeroed());
        }
        let keep = select_field(old_valid, old, 0);
        (rebuild(out, select_field(ok, new, keep)), ok)
    }

    /// Requires Len <= MaxLen at compile time (a longer array can never
    /// fit; std's from_array has the same static_assert).
    /// (e_t, ok) = index_flags_or::<MaxLen - Len + 1>(len): e_t = (len == t)
    /// for the start positions t = 0..=MaxLen - Len, and ok, their OR, is
    /// exactly len + Len <= MaxLen. For each t and k < Len,
    /// out[t + k] = select(e_t, array[k], out[t + k]): only t = len writes,
    /// so positions len..len + Len receive the array and nothing is
    /// written when ok is false. A last pass zeroes the storage on a broken
    /// length. Output length: len + Len on ok, else len if valid, else 0.
    /// Cost: MaxLen - Len + 1 eq gadgets, (MaxLen - Len + 1)*Len + MaxLen
    /// T-selects, one lt_bounded::<32>, the rebuild.
    fn extend_from_array_or<let Len: u32>(self, array: [T; Len]) -> (Self, bool) {
        static_assert(
            Len <= MaxLen,
            "extend_from_array_or: array longer than MaxLen",
        );
        let len = self.len() as Field;
        // index_flags_or::<MaxLen - Len + 1>(len), written out: MaxLen - Len
        // in a generic position fails to compile for Len > MaxLen before
        // the static_assert above can report it, while this runtime count
        // is folded after it.
        let starts = if Len <= MaxLen { MaxLen - Len + 1 } else { 0 };
        let mut at = [false; MaxLen + 1];
        let mut ok = false;
        for t in 0..starts {
            let e = eq(len, t as Field);
            at[t] = e;
            ok = ok | e;
        }
        let mut out = self.storage();
        for t in 0..starts {
            for k in 0..Len {
                out[t + k] = T::select(at[t], array[k], out[t + k]);
            }
        }
        let valid = len_ok::<MaxLen>(len);
        for j in 0..MaxLen {
            out[j] = T::select(valid, out[j], zeroed());
        }
        let keep = select_field(valid, len, 0);
        (rebuild(out, select_field(ok, len + (Len as Field), keep)), ok)
    }

    /// (e_t, valid) = index_flags_or::<MaxLen + 1>(len) for t = 0..=MaxLen
    /// (valid = len <= MaxLen); (mask2, ok2) = prefix_mask_or::<Len>(vec's
    /// len) (mask2[k] = k < len2, ok2 = len2 <= Len); fits =
    /// len + len2 <= MaxLen by one lt_bounded::<33> (both sides below 2^33).
    /// ok = valid & ok2 & fits. For each t, k with t + k < MaxLen,
    /// out[t + k] = select(e_t & ok & mask2[k], vec[k], out[t + k]): only
    /// t = len writes, only the k below len2, and nothing when ok is
    /// false. A last pass zeroes the storage on a broken length. Output
    /// length: len + len2 on ok, else len if valid, else 0. Cost:
    /// MaxLen + Len + 2 eq gadgets, about MaxLen*Len bool products and
    /// T-selects (the pairs with t + k < MaxLen) plus MaxLen T-selects, one
    /// lt_bounded::<33>, the rebuild.
    fn extend_from_bounded_vec_or<let Len: u32>(self, vec: BoundedVec<T, Len>) -> (Self, bool) {
        let len = self.len() as Field;
        let len2 = vec.len() as Field;
        let (at, valid) = index_flags_or::<MaxLen + 1>(len);
        let (mask2, ok2) = prefix_mask_or::<Len>(len2);
        let sum = len + len2;
        let ok = valid & ok2 & !lt_bounded::<33>(MaxLen as Field, sum);
        let src = vec.storage();
        let mut out = self.storage();
        for t in 0..(MaxLen + 1) {
            let g = at[t] & ok;
            for k in 0..Len {
                if t + k < MaxLen {
                    out[t + k] = T::select(g & mask2[k], src[k], out[t + k]);
                }
            }
        }
        for j in 0..MaxLen {
            out[j] = T::select(valid, out[j], zeroed());
        }
        let keep = select_field(valid, len, 0);
        (rebuild(out, select_field(ok, sum, keep)), ok)
    }
}

/// Selection between two vectors: the storage by T-selects, the length by
/// a Field select. A broken selected length (above MaxLen, only from a
/// prover-altered witness) gives the empty vector with zeroed storage, so
/// the rebuild holds and the result is in normal form. Total: 2*MaxLen
/// T-selects, one lt_bounded::<32> (the selected length is one of two u32
/// values, below 2^32), the rebuild.
impl<T, let MaxLen: u32> Select for BoundedVec<T, MaxLen>
where
    T: Select,
{
    fn select(c: bool, t: Self, f: Self) -> Self {
        let mut storage = Select::select(c, t.storage(), f.storage());
        let len = select_field(c, t.len() as Field, f.len() as Field);
        let valid = len_ok::<MaxLen>(len);
        for j in 0..MaxLen {
            storage[j] = T::select(valid, storage[j], zeroed());
        }
        rebuild(storage, select_field(valid, len, 0))
    }
}

/// from_parts with both of its conditions flagged: ok = len <= MaxLen
/// and every element at position >= len equals zeroed(). On ok the value
/// is exactly from_parts(array, len); on ok = false it is the empty vector
/// (zeroed storage, length 0).
/// Constraints: prefix_mask_or::<MaxLen>(len) (MaxLen + 1 eq gadgets,
/// hint-satisfiable, determined); MaxLen T equalities against zeroed()
/// (T's Eq; for Field and the integers one eq gadget each) and bool
/// arithmetic; MaxLen T-selects on mask[j] & ok; the rebuild. Total for
/// every input; ok determined. Cost: MaxLen + 1 eq gadgets, MaxLen
/// T-selects and MaxLen T equalities.
pub fn from_parts_or<T, let MaxLen: u32>(
    array: [T; MaxLen],
    len: u32,
) -> (BoundedVec<T, MaxLen>, bool)
where
    T: Select + Eq,
{
    let l = len as Field;
    let (mask, valid) = prefix_mask_or::<MaxLen>(l);
    let mut zero_tail = true;
    for j in 0..MaxLen {
        zero_tail = zero_tail & (mask[j] | (array[j] == zeroed()));
    }
    let ok = valid & zero_tail;
    let mut out = array;
    for j in 0..MaxLen {
        out[j] = T::select(mask[j] & ok, array[j], zeroed());
    }
    (rebuild(out, (ok as Field) * l), ok)
}

/// The first len elements of array as a BoundedVec in normal form (the
/// rest zeroed), ok = len <= MaxLen; empty when ok is false. The form for
/// an array whose tail is not known to be zero. Constraints: keep_prefix
/// and the rebuild. Cost: MaxLen + 1 eq gadgets and MaxLen T-selects.
pub fn from_prefix_or<T, let MaxLen: u32>(
    array: [T; MaxLen],
    len: u32,
) -> (BoundedVec<T, MaxLen>, bool)
where
    T: Select,
{
    let l = len as Field;
    let (out, ok) = keep_prefix(array, l);
    (rebuild(out, (ok as Field) * l), ok)
}

mod tests;
