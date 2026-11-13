// ctl: Select on every implementing type, Outcome, some_or.
use crate::ctl::{Outcome, Select, some_or};

/// t when c, else f.
unconstrained fn pick<T>(c: bool, t: T, f: T) -> T {
    if c {
        t
    } else {
        f
    }
}

fn check_select<T>(c: bool, t: T, f: T)
where
    T: Select + Eq,
{
    // Safety: reference model, compared below.
    let want = unsafe { pick(c, t, f) };
    assert(T::select(c, t, f) == want);
}

#[test]
fn select_all(
    c: bool,
    f: [Field; 2],
    b: [bool; 2],
    u: (u8, u16, u32, u64, u128),
    v: (u8, u16, u32, u64, u128),
    i: (i8, i16, i32, i64),
    j: (i8, i16, i32, i64),
) {
    check_select(c, f[0], f[1]);
    check_select(c, b[0], b[1]);
    check_select(c, u.0, v.0);
    check_select(c, u.1, v.1);
    check_select(c, u.2, v.2);
    check_select(c, u.3, v.3);
    check_select(c, u.4, v.4);
    check_select(c, i.0, j.0);
    check_select(c, i.1, j.1);
    check_select(c, i.2, j.2);
    check_select(c, i.3, j.3);
    check_select(c, f, [f[1], f[0]]);
    check_select(c, (f[0], b[0]), (f[1], b[1]));
    check_select(c, (u.0, i.0, f[0]), (v.0, j.0, f[1]));
    check_select(c, (u.4, i.3, b[0], f[0]), (v.4, j.3, b[1], f[1]));
}

/// The Outcome of requiring each flag in turn: ok is their AND and code
/// is the code of the first failing check, 0 if none fails.
unconstrained fn outcome_model<let N: u32>(flags: [bool; N], codes: [Field; N]) -> (bool, Field) {
    let mut ok = true;
    let mut code = 0;
    for k in 0..N {
        if ok & !flags[k] {
            code = codes[k];
        }
        ok = ok & flags[k];
    }
    (ok, code)
}

#[test]
fn outcome_and_some_or(
    flags: [bool; 4],
    codes: [Field; 4],
    x: Field,
    y: Field,
    xs: [Field; 3],
    is_some: bool,
) {
    // Two flags in three set, so a run of checks passes now and then.
    let mut fs = flags;
    for k in 0..4 {
        fs[k] = flags[k] | (codes[k] as u8 % 3 == 0);
    }
    let mut first = Outcome::good();
    let mut second = Outcome::good();
    let mut all = Outcome::good();
    for k in 0..4 {
        all = all.require(fs[k], codes[k]);
        if k < 2 {
            first = first.require(fs[k], codes[k]);
        } else {
            second = second.require(fs[k], codes[k]);
        }
    }
    // Safety: reference model, compared below.
    let (ok, code) = unsafe { outcome_model(fs, codes) };
    assert_eq((all.ok, all.code), (ok, code));
    let joined = first.and_outcome(second);
    assert_eq((joined.ok, joined.code), (ok, code));
    assert_eq(all.guard(x, y), if ok { x } else { y });
    assert_eq(all.mask_field(x), if ok { x } else { 0 });
    assert_eq(all.mask_array(xs), if ok { xs } else { [0; 3] });

    let opt = if is_some {
        Option::some(x)
    } else {
        Option::none()
    };
    assert_eq(some_or(opt), (if is_some { x } else { 0 }, is_some));
}
