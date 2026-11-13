//! Differential tests of `total` against references outside Noir.
//!
//! Every test takes arguments, so nargo's fuzzer supplies them: a seed from
//! which the oracle server (oracle_server.ts at the repository root) builds a
//! case and its expected answer, or the inputs themselves, which the server
//! answers for. The test then runs the library entry and asserts that it
//! returns the server's answer.
//!
//! The tests are constrained functions: only the oracle call is unconstrained.
//! The fuzzer executes each test both as ACIR, where the entry's constraints
//! must be satisfied by the solver's witness, and as Brillig, and fails if
//! either fails or they disagree. So a failing test means the entry gave a
//! wrong answer or could not be executed for that input.
//!
//! Run with scripts/run.sh, which builds and starts the server and runs
//! `nargo test --oracle-resolver`. Plain `nargo test` here fails at the first
//! oracle call.

mod secp;
mod ecdsa;
mod hash;
mod merkle;
mod schnorr;
