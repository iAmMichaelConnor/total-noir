// collections::bounded_vec: every TotalBoundedVec method and both
// constructors. The vectors are fuzzed parameters, so a length can break
// the invariant (len > MaxLen) and a tail need not be zero; most of the
// time the storage is rebuilt with a short length to reach the valid cases.
use crate::collections::bounded_vec::{from_parts_or, from_prefix_or, TotalBoundedVec};

global M: u32 = 4;

/// Its storage with the length sel % 8 when that is at most N, else v
/// itself.
fn shape_vec<let N: u32>(sel: u8, v: BoundedVec<Field, N>) -> BoundedVec<Field, N> {
    let k = (sel % 8) as u32;
    if k <= N {
        BoundedVec::from_parts(v.storage(), k)
    } else {
        v
    }
}

/// A length or position for capacity M chosen by sel: each of 0..=M + 1,
/// 2^32 - 1, or x itself.
unconstrained fn shape_len(sel: u8, x: u32) -> u32 {
    let k = (sel % 8) as u32;
    if k <= M + 1 {
        k
    } else if k == M + 2 {
        0xffffffff
    } else {
        x
    }
}

/// get_or, then set_or, push_or as (storage, len, ok), then pop_or as
/// (storage, len, element, ok).
unconstrained fn read_write_model(
    s: [Field; M],
    len: u32,
    index: u32,
    x: Field,
) -> ((Field, bool), [([Field; M], u32, bool); 2], ([Field; M], u32, Field, bool)) {
    let valid = len <= M;
    let ok = valid & (index < len);
    let get = if ok { (s[index], true) } else { (0, false) };
    let broken = ([0; M], 0, false);
    let set = if !valid {
        broken
    } else if ok {
        let mut t = s;
        t[index] = x;
        (t, len, true)
    } else {
        (s, len, false)
    };
    let push = if len < M {
        let mut t = s;
        t[len] = x;
        (t, len + 1, true)
    } else if len == M {
        (s, len, false)
    } else {
        broken
    };
    let pop = if valid & (len >= 1) {
        let mut t = s;
        t[len - 1] = 0;
        (t, len - 1, s[len - 1], true)
    } else if len == 0 {
        (s, 0, 0, false)
    } else {
        ([0; M], 0, 0, false)
    };
    (get, [set, push], pop)
}

#[test]
fn bvec_read_write(sv: u8, v: BoundedVec<Field, M>, si: u8, index: u32, x: Field) {
    let v = shape_vec(sv, v);
    // Safety: input selection; the value reaches the library as a witness.
    let index = unsafe { shape_len(si, index) };
    let len = v.len();
    // Safety: reference model, compared below.
    let (get, m, pop) = unsafe { read_write_model(v.storage(), len, index, x) };
    assert_eq(v.is_valid(), len <= M);
    assert_eq(v.get_or(index), get);
    let (w, ok) = v.set_or(index, x);
    assert_eq((w.storage(), w.len(), ok), m[0]);
    let (w, ok) = v.push_or(x);
    assert_eq((w.storage(), w.len(), ok), m[1]);
    let (w, e, ok) = v.pop_or();
    assert_eq((w.storage(), w.len(), e, ok), pop);
}

/// set_len_or, extend_from_array_or, extend_from_bounded_vec_or as
/// (storage, len, ok): unchanged on ok = false with a valid length, empty
/// and zeroed on a broken one.
unconstrained fn resize_model(
    s: [Field; M],
    len: u32,
    new_len: u32,
    arr: [Field; 2],
    other: [Field; 3],
    other_len: u32,
) -> [([Field; M], u32, bool); 3] {
    let valid = len <= M;
    let mut r = [([0; M], 0, false); 3];
    if valid {
        r = [(s, len, false); 3];
        if new_len <= M {
            let mut t = s;
            for j in 0..M {
                if j >= new_len {
                    t[j] = 0;
                }
            }
            r[0] = (t, new_len, true);
        }
        if len + 2 <= M {
            let mut t = s;
            t[len] = arr[0];
            t[len + 1] = arr[1];
            r[1] = (t, len + 2, true);
        }
        if other_len <= 3 {
            if len + other_len <= M {
                let mut t = s;
                for k in 0..3 {
                    if k < other_len {
                        t[len + k] = other[k];
                    }
                }
                r[2] = (t, len + other_len, true);
            }
        }
    }
    r
}

/// from_parts_or and from_prefix_or as (storage, len, ok).
unconstrained fn construct_model(a: [Field; M], len: u32) -> [([Field; M], u32, bool); 2] {
    let mut zero_tail = true;
    let mut prefix = a;
    for j in 0..M {
        if j >= len {
            zero_tail = zero_tail & (a[j] == 0);
            prefix[j] = 0;
        }
    }
    let empty = ([0; M], 0, false);
    [
        if (len <= M) & zero_tail {
            (a, len, true)
        } else {
            empty
        },
        if len <= M { (prefix, len, true) } else { empty },
    ]
}

/// a with the positions at or past len zeroed when asked, so that
/// from_parts_or can succeed.
unconstrained fn clear_tail(a: [Field; M], len: u32, clear: bool) -> [Field; M] {
    let mut out = a;
    for j in 0..M {
        if clear & (j >= len) {
            out[j] = 0;
        }
    }
    out
}

#[test]
fn bvec_resize_extend(
    sv: u8,
    v: BoundedVec<Field, M>,
    sn: u8,
    new_len: u32,
    arr: [Field; 2],
    so: u8,
    o: BoundedVec<Field, 3>,
    clear: bool,
) {
    let (v, o) = (shape_vec(sv, v), shape_vec(so, o));
    // Safety: input selection; the value reaches the library as a witness.
    let new_len = unsafe { shape_len(sn, new_len) };
    let storage = v.storage();
    // Safety: reference model, compared below.
    let m = unsafe { resize_model(storage, v.len(), new_len, arr, o.storage(), o.len()) };
    let (w, ok) = v.set_len_or(new_len);
    assert_eq((w.storage(), w.len(), ok), m[0]);
    let (w, ok) = v.extend_from_array_or(arr);
    assert_eq((w.storage(), w.len(), ok), m[1]);
    let (w, ok) = v.extend_from_bounded_vec_or(o);
    assert_eq((w.storage(), w.len(), ok), m[2]);

    // Safety: input selection; the values reach the library as witnesses.
    let a = unsafe { clear_tail(storage, new_len, clear) };
    // Safety: reference model, compared below.
    let c = unsafe { construct_model(a, new_len) };
    let (w, ok) = from_parts_or(a, new_len);
    assert_eq((w.storage(), w.len(), ok), c[0]);
    let (w, ok) = from_prefix_or(a, new_len);
    assert_eq((w.storage(), w.len(), ok), c[1]);
}
