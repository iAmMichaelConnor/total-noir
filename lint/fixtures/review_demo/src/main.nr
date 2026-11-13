// Regression fixture for total-lint: justification markers must come from
// this package only, hint radix decompositions that can abort must be
// listed, asserted comparisons in the library must stay reported, and
// ECDSA must stay visible as backend-defined.

use review_vendor::{apply, first_byte, low_bit, vendor_assert, vendor_le_if, vendor_lt};

fn check7(v: Field) -> Field {
    assert(v == 7);
    v
}

fn main(
    x: Field,
    y: Field,
    z: Field,
    w: Field,
    pk_x: [u8; 32],
    pk_y: [u8; 32],
    sig: [u8; 64],
    msg: [u8; 32],
    lo: u64,
    hi: u64,
    c: bool,
) -> pub (u8, bool, Field, bool) {
    let b = first_byte(x);
    let bit = low_bit(x);
    vendor_assert(y);
    let v = apply(check7, x);
    vendor_lt(lo, hi);
    vendor_le_if(c, lo, hi);
    // The author's own sign-off counts.
    // total-lint: allow the caller guarantees z != 5
    assert(z != 5);
    // A marker inside a string literal does not count.
    assert(w != 9, "total-lint: allow this is only a message");
    let ok = std::ecdsa_secp256k1::verify_signature(pk_x, pk_y, sig, msg);
    (b, bit, v, ok)
}
