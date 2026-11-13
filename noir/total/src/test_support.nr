//! Witness construction for the unit tests; no entry uses it.
//!
//! nargo executes an unconstrained call with constant arguments at compile
//! time and folds its result, so a plain identity hint on a literal makes
//! no witness and the test never reaches the constraints. opaque calls the
//! print oracle (an empty string, so nothing is printed), which keeps the
//! call, and its result is a witness the circuit cannot fold.

pub(crate) unconstrained fn opaque<T>(x: T) -> T {
    std::print("");
    x
}

/// x as a witness.
pub(crate) fn wit<T>(x: T) -> T {
    // Safety: test-only witness construction; no constraint needed.
    unsafe {
        opaque(x)
    }
}

/// vals with every element taken through opaque.
pub(crate) fn witnesses<T, let K: u32>(vals: [T; K]) -> [T; K] {
    let mut w = vals;
    for i in 0..K {
        // Safety: test-only witness construction; no constraint needed.
        w[i] = unsafe { opaque(vals[i]) };
    }
    w
}
