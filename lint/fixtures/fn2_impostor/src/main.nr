// Regression fixture for total-lint: a dependency vendored in a directory
// named `total` is not the library unless its directory is passed.

fn main(x: Field, y: Field, z: Field) -> pub Field {
    helper::flags(x, y, z);
    helper::checked_root(x)
}
