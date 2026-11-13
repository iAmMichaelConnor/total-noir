// A plain Noir contract for total-lint: one total function, one that
// fails for some inputs, and one unconstrained function.

contract Demo {
    fn ok(x: Field) -> pub bool {
        x == 1
    }

    fn bad(x: Field) {
        assert(x != 0);
    }

    unconstrained fn view(x: Field) -> pub Field {
        x + 1
    }
}
