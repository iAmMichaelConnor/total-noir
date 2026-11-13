//! total: always-satisfiable building blocks for Noir circuits.
//!
//! Every public entry either returns a value that is defined for every
//! input, or a (value, ok) pair where ok is a determined flag. No entry
//! emits a constraint an input can falsify: the only asserts are on
//! prover-chosen hints, and for every input the honest hint satisfies
//! them. Each entry's doc comment lists the constraints it emits and
//! why each one is hint-satisfiable.
//!
//! Naming and value conventions, library-wide:
//! 1. A public function's name ends in `_or` iff it returns a tuple whose
//!    last element is an `ok: bool` flag.
//! 2. On ok = false, an entry that produces a value returns the zero value
//!    of its type (0, false, a zeroed array), and an entry that updates a
//!    container returns the container unchanged. The exceptions, each
//!    documented at the entry:
//!    - convert::truncate_or returns the real low bits and dropped part;
//!    - `wrapping_*_or` and `saturating_*_or` compute on each out-of-range
//!      input clamped to 0 (wrapping_add_or::<8>(300, 3) = (3, false));
//!      their flag reports only whether the inputs were in range;
//!    - ec entries return the point at infinity, Point's zero value;
//!    - TotalBoundedVec updates return an empty vector when the input
//!      vector's length already exceeds MaxLen.
//! 3. Field-domain free functions take arbitrary `Field` inputs and a bit
//!    width `::<N>`, and flag inputs that do not fit it. Trait methods on
//!    the native integer types have the same base name and result shape.
//!
//! The entries built on third-party libraries (ecdsa over the std ECDSA
//! black boxes; hash::sha256_var_or and hash::keccak256_var_or over
//! noir-lang/sha256 and noir-lang/keccak256) call them only on inputs they
//! handle without failing: every precondition the library would assert is
//! flagged first, an input that fails a flag is swapped for a fixed
//! known-good one (a valid dummy signature, a zero length) before the
//! call, and the flags are ANDed into the result (the select-to-dummy
//! pattern). The library then never sees an input that can make it fail,
//! and the flags keep the substitute's answer out of the result.
//!
//! Backend black boxes need one more step: bb 6.0.0's MSM and ECDSA
//! gadgets have no proof for some valid inputs. The ECDSA wrappers pass
//! the black box a key blinded by an in-circuit multiple of G, with the
//! hash adjusted so that its verdict equals the verdict on the inputs for
//! every hint the constraints accept, and the honest hint picks a blind
//! the gadget can prove (see ecdsa.nr). ec::msm_or validates its inputs
//! and then passes the black box bases blinded by hinted points, so that
//! every input has a proof, with constraints that make the output the true
//! MSM for every hint they accept (see ec.nr). schnorr::schnorr_verify
//! computes noir-lang/schnorr's verification over msm_or instead of
//! calling that library.
//!
//! Statements in these comments about what a native operation or cast
//! lowers to describe nargo 1.0.0-rc.3 and later semantics.

pub mod core;
pub mod range;
pub mod cmp;
pub mod convert;
pub mod arith;
pub mod signed;
pub mod bitwise;
pub mod ctl;
pub mod collections;
pub mod hash;
pub mod merkle;
pub mod ec;
pub mod encode;
pub mod schnorr;
pub mod secp;
pub mod ecdsa;
mod test_support;
mod fuzz_tests;

// Flat surface for the most-used entries. Everything else is reached
// through its group module.
pub use arith::{add_or, div_or, div_rem_or, inverse_or, mod_or, mul_or, sub_or};
pub use cmp::{eq, gt, gte, lt, lte, neq};
pub use collections::{index_or, set_or};
pub use convert::bool_or;
pub use core::{is_zero, select_field};
pub use ctl::{Outcome, Select};
pub use ecdsa::{ecdsa_k1_verify, ecdsa_k1_verify_fields, ecdsa_r1_verify, ecdsa_r1_verify_fields};
pub use range::{clamp_bits_or, fits_bits};
pub use schnorr::schnorr_verify;
