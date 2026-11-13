// A dependency in a directory named `total` whose asserts fail for some
// inputs.

unconstrained fn guess(x: Field) -> Field {
    x
}

pub fn checked_root(x: Field) -> Field {
    // Safety: fixture; the square is checked below.
    let r = unsafe { guess(x) };
    assert(r * r == x);
    r
}

pub fn flags(x: Field, y: Field, z: Field) {
    let f = x == y;
    let g = y == z;
    assert(f == g);
}
