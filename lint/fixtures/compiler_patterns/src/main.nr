// Fixture for total-lint's hint-compiler class: each line of main is one
// operation. The first group lowers to compiler directives in patterns
// that hold for every input; the second fails for some inputs or uses a
// hint that only looks like a directive.

unconstrained fn directive_invert(x: Field) -> Field {
    x + 7
}

fn main(
    x: Field,
    i: Field,
    t: Field,
    w: Field,
    d: u32,
) -> pub (bool, u8, bool, u32, u32, u32, [u8; 4], [u8; 1], u32) {
    let eq = x == 5;
    let byte = i as u8;
    let small = byte < 7;
    let s = t as u32;
    let masked = s & 3;
    let half = s / 2;
    let le: [u8; 4] = (s as Field).to_le_bytes();
    let short: [u8; 1] = w.to_le_bytes();
    let q = s / d;
    // Safety: fixture; a user hint named like the compiler's directive.
    let z = unsafe { directive_invert(w) };
    let y = 1 - w * z;
    assert(w * y == 0);
    (eq, byte, small, masked, half, s, le, short, q)
}
