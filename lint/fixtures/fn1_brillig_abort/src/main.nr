// Regression fixture for total-lint: a reachable abort in unconstrained
// code fails the run unless a marker justifies it.

unconstrained fn f(x: Field) -> Field {
    assert(x != 0, "boom");
    x
}

unconstrained fn quot(a: Field, b: Field) -> Field {
    // total-lint: allow fixture: the marker covers this division only
    a / b
}

fn main(x: Field, a: Field, b: Field) -> pub (Field, Field) {
    // Safety: fixture; both hints are deliberately unconstrained.
    unsafe {
        (f(x), quot(a, b))
    }
}
