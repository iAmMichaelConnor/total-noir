// A deliberately fallible circuit: each statement in main plants one
// failure source that an input can trigger. total-lint must find and
// classify every one of them.

fn main(
    a: u64,
    b: u64,
    x: Field,
    y: Field,
    d: Field,
    table: [Field; 4],
    idx: u32,
    c: bool,
) -> pub Field {
    // Top-level assert on inputs.
    assert(x == y + 1, "x must be y + 1");
    // u64 addition: the compiler adds an overflow range check on the sum.
    let s = a + b;
    // Dynamic array index: out-of-bounds idx fails.
    let t = table[idx];
    // Field division by a witness: fails when d is zero.
    let q = x / d;
    // Integer division by a witness: fails when b is zero.
    let r = a / b;
    // Explicit range assertion on an input.
    y.assert_max_bit_size::<32>();
    // Assert inside a branch: the compiler multiplies it by the condition.
    if c {
        assert(y == 3, "y must be 3 when c");
    }
    t + q + (s as Field) + (r as Field)
}
