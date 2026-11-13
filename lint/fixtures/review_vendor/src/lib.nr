// A stand-in dependency for total-lint regression tests. It plants what a
// dependency must not get away with: a hint whose radix decomposition can
// abort, a justification marker on its own input assert, a marker on the
// call of a caller-supplied function, and asserted integer comparisons,
// which stay reported even when this package is the whitelisted library.
// It also has a full-width decomposition, which cannot abort and must not
// be reported.

/// Low byte of x through a one-limb decomposition: the hint aborts
/// witness generation when x >= 256.
pub fn first_byte(x: Field) -> u8 {
    // Safety: fixture; the RANGE on the u8 return is the only check.
    unsafe {
        low_byte(x)
    }
}

unconstrained fn low_byte(x: Field) -> u8 {
    let b: [u8; 1] = x.to_le_bytes();
    b[0]
}

/// Lowest bit of x through a full-width decomposition.
pub fn low_bit(x: Field) -> bool {
    // Safety: fixture; the booleanity check on the return is the only check.
    unsafe {
        full_low_bit(x)
    }
}

unconstrained fn full_low_bit(x: Field) -> bool {
    let bits: [bool; 254] = x.to_le_bits();
    bits[0]
}

pub fn vendor_assert(x: Field) {
    // total-lint: allow vendor reviewed this constraint
    assert(x == 3);
}

/// An asserted comparison: fails for some inputs, though every constraint
/// it lowers to touches the comparison's hint.
pub fn vendor_lt(a: u64, b: u64) {
    assert(a < b);
}

/// The same under a branch condition.
pub fn vendor_le_if(c: bool, a: u64, b: u64) {
    if c {
        assert(a <= b);
    }
}

pub fn apply(f: fn(Field) -> Field, x: Field) -> Field {
    // total-lint: allow vendor says the callback is fine
    f(x)
}
