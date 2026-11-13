// range: fits_bits and clamp_bits_or from 1 to 253 bits, and the
// fixed-width shorthands.
use crate::range::{
    clamp_bits_or, fits_bits, fits_u1, fits_u128, fits_u16, fits_u32, fits_u64, fits_u8,
};
use super::{fits, shape};

fn check_fits<let N: u32>(s: u8, x: Field) {
    // Safety: input selection; the value reaches the library as a witness.
    let x = unsafe { shape(s, x, N) };
    // Safety: reference model, compared below.
    let ok = unsafe { fits(x, N) };
    assert_eq(fits_bits::<N>(x), ok);
    assert_eq(clamp_bits_or::<N>(x), (if ok { x } else { 0 }, ok));
}

#[test]
fn fits_and_clamp(s: u8, x: Field) {
    check_fits::<1>(s, x);
    check_fits::<8>(s, x);
    check_fits::<64>(s, x);
    check_fits::<127>(s, x);
    check_fits::<128>(s, x);
    check_fits::<129>(s, x);
    check_fits::<200>(s, x);
    check_fits::<252>(s, x);
    check_fits::<253>(s, x);
}

fn check_fixed<let N: u32>(s: u8, x: Field, f: fn(Field) -> bool) {
    // Safety: input selection; the value reaches the library as a witness.
    let x = unsafe { shape(s, x, N) };
    // Safety: reference model, compared below.
    let ok = unsafe { fits(x, N) };
    assert_eq(f(x), ok);
}

#[test]
fn fits_fixed_widths(s: u8, x: Field) {
    check_fixed::<1>(s, x, fits_u1);
    check_fixed::<8>(s, x, fits_u8);
    check_fixed::<16>(s, x, fits_u16);
    check_fixed::<32>(s, x, fits_u32);
    check_fixed::<64>(s, x, fits_u64);
    check_fixed::<128>(s, x, fits_u128);
}
