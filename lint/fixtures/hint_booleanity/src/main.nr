// Fixture for total-lint's booleanity rule: `assert(v * v == v)`, the
// check aztec-nr v6's `Packable for bool` makes in `unpack`, is
// falsifiable when v comes from a hint (stored data its author can set to
// 2), whether or not v also passes through a compiler directive. The same
// check on bits the circuit computes from the compiler's own directives
// stays hint-compiler.

unconstrained fn stored_flag(x: Field) -> Field {
    x
}

fn main(x: Field, y: Field, s: Field) -> pub bool {
    // Safety: fixture; stands for a stored value read through an oracle.
    let v = unsafe { stored_flag(x) };
    assert(v * v == v);
    // Safety: fixture; the same kind of hint, then selected by a comparison
    // the compiler lowers through its own directive.
    let h = unsafe { stored_flag(y) };
    let w = if s == 3 { h } else { 0 };
    assert(w * w == w);
    // Bits the circuit computes: the negated is-zero flag of s - 3, and the
    // exclusive or of two binary digits of y.
    let e = 1 - ((s == 3) as Field);
    assert(e * e == e);
    let bits: [bool; 8] = (y as u8 as Field).to_le_bits();
    let (b0, b1) = (bits[0] as Field, bits[1] as Field);
    let k = b0 + b1 - 2 * b0 * b1;
    assert(k * k == k);
    v == 1
}
