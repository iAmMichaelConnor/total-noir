# Contributing

This guide covers how changes are checked, how pull requests are titled, and
how releases are made.

## Checks

CI (`.github/workflows/test.yml`) runs on every pull request and every push to
`main`. You can run the same checks locally:

| Check | Command | Toolchain |
|---|---|---|
| Library tests | `nargo test` in `noir/total`, then `noir/total_witness_check/run.sh` | Noir 1.0.0 |
| Oracle tests | `yarn install`, then `scripts/run.sh` ([below](#oracle-tests)) | Noir 1.0.0; Node.js 22 |
| Backend proofs of the MSM-based entries | `noir/total_prove_check/run.sh` (msm_or and schnorr_verify proved and verified with bb on inputs bb's MSM gadget cannot prove unblinded) | nargo 1.0.0-rc.3, bb 6.0.0 |
| Backend proofs of the ECDSA entries | `noir/total_ecdsa_prove_check/run.sh` (ecdsa_k1_verify and ecdsa_r1_verify proved and verified with bb on inputs bb's ECDSA gadgets cannot prove unblinded) | nargo 1.0.0-rc.3, bb 6.0.0 |
| ECDSA totality: computed facts | `scripts/ecdsa_totality_checks.py` (seconds); `scripts/ecdsa_alias_multiplicity.py` (minutes, many cores; not per-PR) | Python 3 |
| ECDSA totality: model, emulation and bb | `scripts/ecdsa_differential.py` (not per-PR; run on any change to `noir/total/src/ecdsa/` and on a bb bump) | nargo 1.0.0-rc.3, bb 6.0.0, Python 3 |
| Aztec packages and examples | `scripts/test-aztec.sh` | nargo 1.0.0-rc.3, bb 6.0.0, `@aztec-labs/txe` 6.0.0 |
| Formatting | `nargo fmt --check` in every package | Noir 1.0.0 |
| Lint tool | `cargo fmt --check`, `cargo clippy --locked --all-targets -- -D warnings`, `cargo test --locked` in `lint/total-lint` | stable Rust, nargo 1.0.0-rc.3 |
| co-noir hints | `scripts/mpc-check.sh` ([docs/co-noir.md](docs/co-noir.md)) | nargo 1.0.0-rc.3, stable Rust |

`scripts/test-aztec.sh` runs `noir/total_aztec`'s unit tests and each
contract's `run.sh` (compile, lint, TXE tests). Install bb with
`bbup -v 6.0.0` and the TXE with `npm install -g @aztec-labs/txe@6.0.0`, or set
`SKIP_TXE=1` to skip the TXE tests; `scripts/txe.sh` lists the settings.
The lint step fails on any unjustified item not in the
`total-lint-baseline.json` next to the script (aztec-nr's own items). After
reviewing a change, rerun that lint command with `--write-baseline` in place
of `--baseline` to rewrite it.

The lint tool's tests compile the packages under `lint/fixtures` with nargo
1.0.0-rc.3. They are skipped when nargo is missing, unless
`TOTAL_LINT_REQUIRE_NARGO=1` is set (as in CI).

A nightly workflow runs the library tests on the latest Noir nightly and opens
an issue when they break. A benchmark workflow reports gate-count changes of
the functions in `noir/total_bench` on every pull request.

### Oracle tests

`noir/total_oracle_tests` holds differential tests: each test takes
arguments, so `nargo test` fuzzes it, and fetches the expected answer from a
JSON-RPC oracle server (`oracle_server.ts`, TypeScript) through an
`#[oracle]` call. The server's references share no code with the library:

| Entries | Reference |
|---|---|
| `secp256k1_on_curve`, `secp256r1_on_curve` | BigInt arithmetic |
| `ecdsa_k1_verify`, `ecdsa_r1_verify`, the `_fields` variants and the `ecdsa_*_sig_admissible` flags | `@noble/curves` (low s, no prehash) with the documented gate |
| `sha256_var_or`, `keccak256_var_or` | Node's `crypto`, `@noble/hashes` |
| `p2_hash`, `p2_hash_sep`, `p2_hash_var_or`, `p2_hash_sep_var_or` | Barretenberg's Poseidon2 (`@aztec-foundation/bb.js` 6.0.0) |
| `merkle_root_or`, `merkle_root_sep_or`, `is_member`, `is_member_sep` | a TypeScript tree over that Poseidon2 |
| `schnorr_inputs_ok`, `schnorr_verify` | a TypeScript Grumpkin model of noir-lang/schnorr v0.4.0, checked against bb.js's native verifier |

Most tests take a seed, from which the server builds a case: valid inputs
and the invalid and edge classes listed at the top of each test file
(off-curve and out-of-range keys, malformed and malleated signatures, the
excluded ECDSA classes, lengths and indices out of range). A failure prints
the seed, which rebuilds the same case. The tests are constrained, and
nargo's fuzzer executes each input both as ACIR and as Brillig, so a test
also fails when an input makes the entry unexecutable.

```bash
yarn install
scripts/run.sh                                   # builds and starts the server on port 8095, runs the tests, stops it
FUZZ_TIMEOUT=60 scripts/run.sh --fuzz-max-executions 1000000  # longer runs; extra arguments go to nargo test
NARGO=/path/to/nargo scripts/run.sh              # another nargo
```

The package is outside `noir/total`, so plain `nargo test` there needs no
server. By default each test is fuzzed for 5 seconds or 100000 executions,
whichever comes first. CI runs it in the `test` job.

## Bumping bb

The ECDSA entries are total only for the bb version their argument was
made for ([docs/ecdsa-totality.md](docs/ecdsa-totality.md), bb 6.0.0,
commit `0219f11d`). Soundness does not depend on bb's internals; whether
every input has a proof does. A change of bb version must not be merged
before:

1. Section 3 of that document ("bb source facts") is re-read against the
   new source: `stdlib/encryption/ecdsa`, `stdlib/primitives/biggroup`
   (the secp256k1 and secp256r1 multiplications, the Montgomery ladder,
   the complete addition and doubling, the wNAF and table code),
   `stdlib/primitives/bigfield` (`assert_is_not_equal`, the divisor
   checks, the maximum-value bookkeeping), the secp256r1 fixed-base
   plookup tables and both offset generators, and the endomorphism split.
   Any new or changed witness-dependent assertion needs the proof redone.
2. The constants in `scripts/gen_ecdsa_tables.py` (the `K1_ALIAS_K_*` and
   `R1_ALIAS_K_*` ranges, the split constants, the table generator and
   windows) match, the emulations in `noir/total/src/ecdsa/k1_emul.nr` and
   `r1_emul.nr` and the model `scripts/ecdsa_bb_model.py` follow the new
   code, and `scripts/ecdsa_totality_checks.py` and
   `scripts/ecdsa_alias_multiplicity.py` pass.
3. `scripts/ecdsa_differential.py` passes at scale (thousands of cases per
   curve) with the new bb, and its summary replaces section 9 of the
   document; `noir/total_ecdsa_prove_check/run.sh` passes.

The MSM-based entries have the same kind of dependence
([ec.nr](noir/total/src/ec.nr), `noir/total_prove_check/run.sh`).

## Pull requests

Keep commits small and focused, and keep a pull request to one change; do
prerequisite work in its own pull request.

Titles follow [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/),
checked by CI:

```
<type>[optional scope]: <description>
```

The types are `feat` (shows up in the changelog), `fix` (shows up in the
changelog) and `chore` (does not, unless breaking). Mark a breaking change with
`!` before the colon, as in `feat(total)!: rename an entry`. A scope names the
package: `total`, `total_aztec`, `total-lint`.

A change to a constraint must keep its soundness and totality argument in the
doc comment up to date, and come with tests for wrong hints as well as right
ones. For a breaking change, say what breaks in the pull request body; the
changelog is generated from the commit titles and messages.

## Releases

[Release Please](https://github.com/googleapis/release-please) runs on every
push to `main`, reads the Conventional Commit titles and keeps a release pull
request open with the version and changelog. Merging it creates the tag.

The release workflow uses the built-in `GITHUB_TOKEN`, so the repository setting
"Allow GitHub Actions to create and approve pull requests" must be on. The benchmark
workflow stores its history on a `gh-pages` branch, which must exist before
its first run.
