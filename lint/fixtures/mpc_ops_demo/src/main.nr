// Hints co-noir's MPC Brillig VM (co-snarks co-brillig) cannot run, for
// `total-lint --brillig-ops`, and one it can. Each hint's output is
// constrained in main, so the circuit is sound; the point is what its
// Brillig holds.

// A black box other than ToRadix: co-brillig runs no other one.
unconstrained fn hint_digest(a: u8, b: u8) -> [u8; 32] {
    std::hash::blake2s([a, b])
}

// A data-dependent `if` that nargo turns into a ConditionalMov. Its
// condition is a plain variable, so no opcode carries the `if`'s line; the
// report still names it.
unconstrained fn hint_sub_if_ge(r: Field, d: Field) -> Field {
    let mut out = r;
    let ge = !r.lt(d);
    if ge {
        out = r - d;
    }
    out
}

// Runs in co-brillig: remainder and quotient by the constant 2. At E = 126
// nargo keeps the loop rolled, with the divisor hoisted above it, and the
// abort scan must still see that the division cannot fail.
unconstrained fn hint_low_bits<let E: u32>(x: Field) -> [bool; E] {
    let mut v = x as u128;
    let mut bits = [false; E];
    for i in 0..E {
        bits[i] = (v % 2) == 1;
        v = v / 2;
    }
    bits
}

// Divisions that cannot fail, the two shapes of total's u128 division
// hints (arith::hint_div_128): a remainder inside the
// else of `b == 0`, which Noir guards with `0 < b`, and a quotient by
// b + (b == 0), nonzero without a branch.
unconstrained fn hint_div_branch(a: Field, b: Field) -> (Field, Field) {
    let ai = a as u128;
    let bi = b as u128;
    if bi == 0 {
        (0, 0)
    } else {
        ((ai / bi) as Field, (ai % bi) as Field)
    }
}

unconstrained fn hint_div_branch_free(a: Field, b: Field) -> (Field, Field) {
    let ai = a as u128;
    let bi = b as u128;
    let z = (bi == 0) as Field;
    let d = ((bi as Field) + z) as u128;
    let q = ((ai / d) as Field) * (1 - z);
    (q, ((ai as Field) - q * (bi as Field)) * (1 - z))
}

fn main(a: u8, b: u8, e: Field, r: Field, d: Field) -> pub (u8, Field) {
    // Safety: checked against the constrained blake2s below.
    let digest = unsafe { hint_digest(a, b) };
    assert_eq(digest, std::hash::blake2s([a, b]));
    // Safety: the bits must recompose e.
    let bits = unsafe { hint_low_bits::<126>(e) };
    let mut acc = 0;
    let mut p = 1;
    for i in 0..126 {
        acc += (bits[i] as Field) * p;
        p *= 2;
    }
    assert(acc == e);
    // Safety: out is r or r - d, and below d exactly when it is the
    // reduced value (d nonzero, r < 2d).
    let out = unsafe { hint_sub_if_ge(r, d) };
    assert((out == r) | (out == r - d));
    assert(out.lt(d));
    // Safety: each pair must recompose r.
    let (q, m) = unsafe { hint_div_branch(r, e) };
    assert(q * e + m == r);
    // Safety: as above.
    let (q2, m2) = unsafe { hint_div_branch_free(r, e) };
    assert(q2 * e + m2 == r);
    (digest[0], out)
}
