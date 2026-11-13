// Regression fixture for total-lint: a marker after code justifies its own
// line only; an unused marker is reported as such.

fn main(x: Field, y: Field) -> pub Field {
    assert(x != 0); // total-lint: allow x is never zero
    assert(y != 0);
    // total-lint: allow nothing here can fail
    let s = x + y;
    s
}
