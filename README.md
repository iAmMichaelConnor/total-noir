# total-noir

> [!WARNING]
> **This library is experimental software. It has not been audited and is not guaranteed to be secure. Expect bugs!**
>
> total-noir is provided "as is", without warranty of any kind (see [LICENSE](LICENSE)). Bugs in this library can lead to under-constrained circuits, allowing invalid proofs to be accepted. Do not rely on it to protect real assets or sensitive data without your own independent review.
>
> If you find a vulnerability, please **do not** open a public issue. Report it privately via [GitHub's "Report a vulnerability"](https://github.com/iAmMichaelConnor/total-noir/security/advisories/new) form instead.

**Noir circuits that cannot be made unprovable.**

total-noir is a Noir library, an Aztec companion library and a lint tool for
writing **total** circuits: circuits that have a proof for every input.

An ordinary circuit says no by failing. `assert(x < y)`, an overflowing
`a + b`, a division by zero, an out-of-range index, a typed `u64` parameter:
on a bad input, no proof exists. That is fine when the person choosing the
inputs is the only one who needs the proof. It is a denial of service when
one party chooses the code or the inputs and another party has to prove.

In a total circuit, each operation that could fail returns `(value, ok)`
instead. The circuit carries the flag to the end and decides there:

```
new_state = select(ok, f(state, inputs), state)
```

A bad input becomes a proved `ok = false`, not a missing proof.

## Threat models

Two parties meet at a circuit: a **requester**, who wants it executed on
some inputs, and an **executor**, who generates the witness and the proof.
The circuit's author may be a third party. The library defends against two
attacks.

### A. Hostile code and inputs, honest executor

The executor must prove a circuit that somebody else wrote, on inputs or
state that somebody else chose. The adversary is whoever controls those:
the requester, the owner of the state being read, or the circuit's author.
They win if the honest executor cannot produce a proof.

- A sequencer or MPC network that must process a queue in order: one
  request nobody can prove stalls the queue forever.
- A transaction that runs another party's contract code against state that
  party controls: one malformed note or key, and the caller's whole
  transaction dies.

Defence: **every input has a satisfying witness, and the honest hints find
it.** No library entry emits a constraint that an input can falsify, and
the lint reports every opcode in a compiled circuit that still can.

### B. Hostile executor, honest requester

The requester hands over inputs and depends on the executor for the
result. The adversary is the executor, who chooses every hint (every value
computed by unconstrained code). They win if they can make the execution
fail and blame the inputs, or steer the outcome by reporting a failure
that did not happen.

Defence: **flags are determined by the inputs.** Every valid proof of the
same inputs carries the same `ok`, so the executor cannot lie about it;
the few places where a hint has a free choice are named in the entry's doc
comment (the sign of `sqrt_or`'s root, for example). And because a
satisfying witness exists for every input (model A), a missing proof is
always the executor's fault, never the input's.

### What is not covered

- An executor who refuses to prove at all. That is a liveness assumption
  about the executor; totality makes a refusal attributable to them.
- What the circuit does when `ok` is false. That is your design.
- Flags backed by an Aztec PXE oracle. In `total_aztec`, whether a note
  was `found` is the executor's choice, so model B holds there only for
  the entries documented as determined.
- Other backends. For the entries built on backend black boxes (ECDSA and
  the Grumpkin multi-scalar multiplication), "every input has a proof" is
  argued and tested for nargo 1.0.0-rc.3 with bb 6.0.0 only.

[docs/limitations.md](docs/limitations.md) has the full list, and
[docs/design.md](docs/design.md) the definitions.

## What is in this repository

Writing total circuits by hand is error-prone: nearly every Noir operator
hides an assertion, and the fix is easy to get subtly wrong in either
direction. The fix is a hint pinned by constraints that the honest hint
always satisfies. This repository does it once:

- [`total`](noir/total): flagged replacements for the Noir operations that
  can fail.
- [`total_aztec`](noir/total_aztec): flagged forms of the aztec-nr v6 reads
  that a state's owner can otherwise make fail. Extremely experimental.
- [`total-lint`](lint/total-lint): a tool that reads a compiled circuit and
  reports every opcode that can still fail.

## Installation

In your _Nargo.toml_ file:

```toml
[dependencies]
total = { tag = "v0.1.0", git = "https://github.com/iAmMichaelConnor/total-noir", directory = "noir/total" }
```

`v0.1.0` is the first release.

`total` depends on noir-lang/schnorr v0.4.0, noir-lang/sha256 v0.3.0 and
noir-lang/keccak256 v0.1.3, the tags Aztec v6.0.0 uses, so a contract that
also depends on aztec-nr resolves one copy of each.

## Usage

```rust
use total::arith::TotalArith;
use total::convert::to_u64_or;
use total::ctl::Select;

// Pay `amount` out of `balance`. Every input can be proved: an input that does
// not fit in a u64, or an overdraft, returns the old balance and ok = false.
fn main(balance: Field, amount: Field) -> pub (Field, bool) {
    let (b, b_ok) = to_u64_or(balance);
    let (a, a_ok) = to_u64_or(amount);
    let (rest, sub_ok) = b.sub_or(a);
    let ok = b_ok & a_ok & sub_ok;
    (Select::select(ok, rest as Field, balance), ok)
}
```

The rules for writing a total circuit:

- Take `Field` at trust boundaries and convert with a flagged conversion. A
  typed parameter such as `x: u64` is a range check that the input can fail.
- Don't assert, except for one deliberate check where refusing is the point.
- Use the flagged forms of arithmetic, division, shifts and casts, and index
  arrays with `index_or`.
- Select on the flag before you use a value: when `ok` is false the value is
  defined but is not the answer (see the conventions below).
- Write hints that cannot trap, and pin their outputs with constraints the
  honest hint always satisfies.
- Run the lint on the compiled circuit, and execute it on adversarial inputs.

[docs/design.md](docs/design.md) has the definitions, the full checklist and
the limits. [docs/noir-coverage.md](docs/noir-coverage.md) lists every way
Noir's language and standard library can fail and what replaces it.

## What the library provides

A public function whose name ends in `_or` returns a tuple whose last
element is the `ok: bool` flag. On `ok = false` the value is zero and an
updated container is returned unchanged (the few exceptions are listed with
the conventions in the API reference).

| Module | Covers |
|---|---|
| `range` | Range flags and clamps up to 253 bits |
| `convert` | `Field` to and from native integers and `bool`, narrowing, truncation, bit and byte decompositions |
| `arith` | Flagged, wrapping and saturating arithmetic on native unsigned integers and on `Field`; division, `mul_div`, powers, inverse, square root |
| `signed` | The same traits on `i8` … `i64`, with negation, absolute value, floor and Euclidean division |
| `cmp` | Comparison flags, `min`, `max`, `clamp` |
| `bitwise` | Bit operations, shifts and rotations with flagged amounts |
| `ctl` | `Select`, the `Outcome` flag-and-error-code type, flagged `Option` unwrap |
| `collections` | Flagged array indexing, windows, sums, search, sorting, and the `BoundedVec` methods |
| `hash` | Poseidon2 (fixed and variable length, sponge), SHA-256 and Keccak-256 with flagged lengths |
| `merkle` | Poseidon2 Merkle roots and membership flags |
| `ec` | Grumpkin: flagged decoding, complete addition, scalar multiplication, multi-scalar multiplication |
| `secp` | On-curve flags for secp256k1 and secp256r1 |
| `schnorr`, `ecdsa` | Signature verification where a malformed key or signature is `false`, and every key has a proof |
| `encode` | Canonical-encoding flags, byte conversions, 31-byte packing |

[docs/api.md](docs/api.md) lists every entry with its signature, and
[docs/limitations.md](docs/limitations.md) the widths and other limits.

### `total_aztec`

> [!CAUTION]
> **`total_aztec` is extremely experimental, more so than the rest of this repository.** The PXE's oracles and aztec-nr were not designed for total circuits, and this package works around them. Several ways remain for a contract or a state to make a private function unprovable (see [docs/limitations.md](docs/limitations.md) and [docs/design.md](docs/design.md)), its guarantees are tied to aztec-nr v6.0.0 exactly, and its API will change. Treat it as a research prototype.

```toml
total_aztec = { tag = "v0.1.0", git = "https://github.com/iAmMichaelConnor/total-noir", directory = "noir/total_aztec" }
aztec = { git = "https://github.com/aztec-labs-eng/aztec-node", tag = "v6.0.0", directory = "noir-projects/aztec-nr/aztec" }
```

Depend on aztec-nr with exactly this `git`, `tag` and `directory`, so that
both packages resolve to one `aztec` crate, and give `total` and
`total_aztec` the same tag, so that both resolve to one `total` crate.

It provides note reads that return `found` instead of asserting, existence
flags at the anchor block, public-state reads from private, stored-key
checks, flagged static calls, and consumption of another owner's note by a
recursive proof of nullification
([docs/api.md](docs/api.md#total_aztec-aztec-nr-v6)). These are wrappers
alongside aztec-nr, not a replacement for it, and a contract is total only
where it uses them.
[docs/aztec-nr-coverage.md](docs/aztec-nr-coverage.md) surveys how aztec-nr
operations can fail and which of those are covered.

[`examples/`](examples) has three worked contracts:
[an account](examples/total_account) other users can call safely,
[a caller](examples/total_caller) that a total callee's owner cannot fail, and
[third-party consumption of an owned note](examples/nullification_proof).

## The lint

`total-lint` decodes a nargo artifact, a program or a contract, and reports
every opcode that can fail and every place a hint can abort. It tells
input-falsifiable constraints from constraints on hints, recognises the
compiler's own hints where they hold for every input (`==`, casts, `&`,
`to_le_bytes`), whitelists the library directories you pass, and honours
`total-lint: allow <reason>` markers in your own package.

```bash
scripts/total-lint.sh target/my_circuit.json --lib-src /path/to/noir/total/src
```

The script builds the tool from this checkout (Rust 1.89 or later) and runs
it. Exit status 0 means nothing reported remains unjustified. A marker after
code covers its own line; a marker in the comment block above a statement
covers that statement. `--lib-src DIR` whitelists a library's hints (none by
default), `--allow-src DIR` honours markers under another directory (an
`#[aztec]` contract passes its own `src`), and `--baseline FILE` (written by
`--write-baseline`) accepts a recorded set of items so only new ones fail.
`--help` lists the other options.

It is a review aid, not a proof of totality. It is tested on nargo
1.0.0-rc.3 artifacts and warns on others.
[docs/design.md](docs/design.md#the-lint) describes the classes and limits.

## Repository layout

| Path | Holds |
|---|---|
| `noir/total` | The library |
| `noir/total_aztec` | The aztec-nr v6 companion library |
| `noir/total_aztec_driver`, `noir/total_oracle_tests`, `noir/total_witness_check`, `noir/total_prove_check`, `noir/total_ecdsa_prove_check`, `noir/total_bench` | Test, proving-check and benchmark packages ([CONTRIBUTING.md](CONTRIBUTING.md#checks)) |
| `lint/total-lint`, `lint/fixtures` | The lint tool and the circuits its tests compile |
| `examples` | Worked Aztec contracts |
| `docs` | Design, API reference, limitations, coverage tables and the ECDSA totality proof |
| `scripts` | Check runners, benchmark reports and the ECDSA model and table generators |
| `oracle_server.ts` | Reference implementations served to the oracle tests |

## Noir version compatibility

CI tests `total` with Noir 1.0.0, and proves its black-box entries with
bb 6.0.0. It also fuzzes the secp, ECDSA, Schnorr, hash and Merkle entries
against references written outside Noir
([CONTRIBUTING.md](CONTRIBUTING.md#oracle-tests)). A nightly job runs the
same tests on the latest Noir nightly.

`total_aztec` and the examples follow aztec-nr v6.0.0, which needs nargo
1.0.0-rc.3 and bb 6.0.0.

## Benchmarks

Benchmarks are ignored by `git` and checked on pull requests. Generate them
with:

```bash
(cd noir/total_bench && nargo export) && scripts/build-gates-report.sh
(cd noir/total_bench && nargo export --force-brillig) && scripts/build-brillig-report.sh
```

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

Licensed under the [Apache License, Version 2.0](LICENSE).

The authenticated encryption in `examples/total_account/src/ecies.nr` is
adapted from `ae.nr` in
[TaceoLabs/monty-hall-aztec](https://github.com/TaceoLabs/monty-hall-aztec)
(MIT License, Copyright (c) 2025 TaceoLabs; the notice is reproduced in that
file). Its ECDH follows the shape of that repository's `dh.nr` without using
its code.
