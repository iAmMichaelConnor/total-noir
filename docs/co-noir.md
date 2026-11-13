# co-noir compatibility of the library's hints

co-noir (TACEO's co-snarks) extends a circuit's witness in MPC: every
unconstrained hint runs inside co-brillig, its Brillig VM over
secret-shared values. This file records what that VM cannot run, the rules
the library's hints follow so that they run there, the entries that do not
run there (`sqrt_or` and `sqrt_canonical_or` for their own hint;
`sha256_var_or`, `keccak256_var_or` and the four ECDSA entries for the
libraries and black boxes they call, and the ECDSA entries also for their
own hint), and how to check a circuit.

Toolchains: co-noir 0.7.0 built from the `main` branch of the co-snarks fork
<https://github.com/iAmMichaelConnor/co-snarks>, at rev
8ec1568ebf16aaf8466ae789a9284acb19e514b9 (`cargo +1.90.0 build --release
-p co-noir --bin co-noir`); nargo 1.0.0 (275d3ab), which is what that rev
reads; nargo 1.0.0-rc.3 (5a7ee9bf) and bb 6.0.0 for the library's own
pins. The results below are pinned to this fork revision, not to an upstream
TaceoLabs/co-snarks release; upstream may lift some of the limits.

## What co-brillig does not run at this rev

From `co-noir/co-brillig/src` at 8ec1568:

- `int_ops.rs`: integer `And`, `Or`, `Xor`, `Shl`, `Shr` are `todo!()`.
  Before reaching them it reads a shift's right operand as u8, while
  nargo 1.0.0 emits it at the left operand's width, so a u128 shift
  fails first with `expected int with size: u8, but got Int(64, U128)`.
- `brillig_vm.rs`: `ConditionalMov` is `todo!()`.
- `mpc/rep3.rs`: an integer remainder by a secret-shared divisor panics
  (`type mismatch. Can only sub matching values`; Noir lowers `%` to a
  multiply and a subtract whose operand types the driver does not
  match). Division by a shared divisor and remainder or division by a
  constant run.
- `brillig_vm.rs`: a branch on a shared value forks the VM once; a second
  shared branch in the same call fails (`we can only support one shared
  if atm`). Checked integer arithmetic on shared values emits such
  branches (overflow checks).
- `blackbox.rs`: of the Brillig black boxes only `ToRadix` runs; every
  other one (a hash such as blake2s or sha256_compression in a hint,
  poseidon2_permutation, aes_128_encrypt, the ECDSA verifications,
  multi_scalar_mul, embedded_curve_add) panics with `not yet implemented:
  unimplemented blackbox`. In ACIR, co-acvm does not solve the ECDSA black
  boxes or keccakf1600 (`co-acvm/src/solver/blackbox_solver.rs` falls to
  `todo!` for them), and co-builder does not build keccakf1600
  (`co-builder/src/acir_format.rs`: `todo!("BlackBoxFuncCall::Keccakf1600")`).
  sha256_compression, AND and XOR are solved.

Three of the five are opcodes, which `total-lint --brillig-ops` lists:
the integer bit ops, ConditionalMov and the Brillig black boxes other than
ToRadix (a hint calling `std::hash::blake2s` compiles to a Brillig
`blake2s` black box and no bit op; `lint/fixtures/mpc_ops_demo` holds it).
The shared remainder and the one-shared-branch limit are not opcodes, nor
are the ACIR ECDSA and keccakf1600 limits Brillig ones, so only a co-noir
run shows them.

## Rules for hint authors

Every hint in `noir/total` except those named below follows these, so its
witness extension runs in co-noir:

- No integer shifts or bitwise operations. Split with `%` and `/` by a
  constant instead: `x % 2^N` and `x / 2^N` for a split at bit N, `v % 2`
  then `v / 2` per bit for a bit decomposition.
- No branch that compiles to `ConditionalMov`. Write the select as Field
  arithmetic: `r = r - bit*d1`, not `if bit { r = r - d1 }`.
- No Brillig black box other than `ToRadix`.
- No remainder by a secret-shared divisor. Divide, then take the remainder
  in the field: `q = a / b`, `r = a - q*b`.
- At most one branch on a shared value per call; avoid checked integer
  arithmetic on shared values, which branches on overflow.

The rules constrain only the hint bodies. The constraint halves, which pin
the hints' outputs, do not depend on how a hint computes them.

The exception is `sqrt_or` (and `sqrt_canonical_or`, built on it). Its
hint runs Tonelli-Shanks, which loops and branches on the data: the
compiled hint holds ConditionalMov opcodes and needs more than one shared
branch. A co-noir-safe square root needs a hint whose control flow does
not depend on the value, which the library does not provide. Do not call
`sqrt_or` in a circuit whose witness co-noir extends.

Further entries are exceptions because of the third-party libraries and
black boxes they call (the ECDSA entries also because of their own hint):

- `hash::sha256_var_or` calls noir-lang/sha256 v0.3.0, whose block-packing
  hint (`build_msg_block_helper`, `msg_item << 8`) and length hint
  (`encode_len`, `>>` and `&`) use integer shifts and a bitwise AND. On
  a circuit calling `sha256_var_or::<64>`, `--brillig-ops` reports 4
  reachable opcodes (three `shl u32`, one `shr u64`) and exits 1. Its
  ACIR (sha256_compression) is within what co-acvm solves.
- `hash::keccak256_var_or` calls noir-lang/keccak256 v0.1.3, which has no
  hint of its own: on a circuit calling `keccak256_var_or::<136>`,
  `--brillig-ops` reports 0 reachable opcodes and exits 0. Its circuit
  is built on the keccakf1600 black box, which co-acvm does not solve
  and co-builder does not build at this rev, so co-noir cannot extend
  or prove it.
- `ecdsa::ecdsa_k1_verify`, `ecdsa_r1_verify` and their `_fields`
  variants call the ECDSA black boxes, which co-acvm does not solve at
  this rev. Their key-blinding hint (`noir/total/src/ecdsa/blind_hint.nr`,
  `k1_emul.nr`, `bignum.nr`) also breaks the rules on purpose: 256-bit
  arithmetic on u64 limbs with integer shifts, Or, ConditionalMov and
  checked integer operations, and the Poseidon2 black box (on a circuit
  calling both `_fields` variants, `--brillig-ops` reports 1,515
  reachable opcodes and exits 1). Written for co-noir it would be far slower, and the black box
  after it cannot run there anyway.

None of these is called in `lint/fixtures/co_noir_hints`.

The secp on-curve hints follow the rules (the fixture calls both flags).
So do `ec::msm_or`'s hints (`noir/total/src/ec/msm_hint.nr`: two blinding
points and a correction scalar): the Poseidon2 permutation and the
scalar multiplication by G there are written in Field arithmetic rather
than with the poseidon2_permutation and multi_scalar_mul black boxes,
bits come from ToRadix, selects are arithmetic, and no branch depends on
the data. `schnorr_verify` has no hints beyond msm_or's and the inversion
gadgets'. The fixture calls both. total_aztec has no hints of its own
that break the rules, but the fixture does not call it, so
`scripts/mpc-check.sh` does not show that it runs in co-noir. Code it
reaches in aztec-nr and that library's dependencies does break the rules
(Brillig black boxes such as poseidon2_permutation, multi_scalar_mul,
embedded_curve_add and aes_128_encrypt, and integer bit ops), but in an
Aztec contract that code runs in utility functions and other PXE-side
hints, not in an MPC witness extension.

## The check

`scripts/total-lint.sh <artifact.json> --brillig-ops` lists every
integer And/Or/Xor/Shl/Shr, ConditionalMov and Brillig black box other
than ToRadix per Brillig function, with its source location and
reachability, and exits 1 when one is reachable. A ConditionalMov carries
no debug location of its own; the report names the `if` it comes from.
The check cannot see the shared remainder or the one-shared-branch limit.
It is opt-in, for circuits whose witness co-noir extends; the default lint
run does not use it.

`scripts/mpc-check.sh` compiles `lint/fixtures/co_noir_hints`, a fixture
that calls the library's entries on private inputs, and runs the
`--brillig-ops` check on it. With `CO_NOIR` set to a co-noir binary it
then runs the fixture's three-party REP3 witness extension on localhost
and fails if a party fails:

```
scripts/mpc-check.sh                                   # static check only
CO_NOIR=<co-snarks>/target/release/co-noir scripts/mpc-check.sh
```

`CO_SNARKS` names the co-snarks checkout whose
`co-noir/co-noir/examples/data` holds the example TLS keys (default: the
directory that holds `CO_NOIR`'s `target/release`), and `CO_NOIR_PORT` the first
of three localhost ports (default 21510). The co-noir run needs nargo
1.0.0 on PATH, since the pinned rev reads nargo 1.0.0 artifacts.

## A full co-noir run

The three-party sequence, run from a directory holding `party0..2.toml`
(localhost ports, the example TLS keys of `co-noir/co-noir/examples/data`)
and the CRS:

```
co-noir split-input --circuit C.json --input Prover.toml --protocol REP3 --out-dir out
# i = 0, 1, 2 in parallel
co-noir generate-witness --input out/Prover.toml.$i.shared --circuit C.json \
  --protocol REP3 --config party$i.toml --out out/witness.gz.$i.shared
co-noir create-vk --circuit C.json --crs bn254_g1.dat --hasher poseidon2 --vk out/vk
# i = 0, 1, 2 in parallel
co-noir build-and-generate-proof --witness out/witness.gz.$i.shared --circuit C.json \
  --crs bn254_g1.dat --protocol REP3 --hasher poseidon2 --fields-as-json \
  --config party$i.toml --vk out/vk --out out/proof.$i.json --public-input out/public_input.$i.json
co-noir verify --proof out/proof.0.json --public-input out/public_input.0.json \
  --vk out/vk --hasher poseidon2 --crs bn254_g2.dat
```

The circuit, compiled with nargo 1.0.0, all inputs private:

```
fn main(x: Field, a: u64, b: u64, d: u64, m: Field, n: Field) -> pub (...) {
    let f = fits_bits::<64>(x);
    let (y, y_ok) = to_u64_or(x);
    let (s, s_ok) = a.add_or(b);
    let (q, q_ok) = a.div_or(d);
    let (mq, mr, m_ok) = a.mul_div_or(b, d);
    let (w, w_ok) = and_bits_or::<64>(m, n);
    (f, y, y_ok, s, s_ok, q, q_ok, mq, mr, m_ok, w, w_ok)
}
```

with `x = 12345678901234567, a = 1000000007, b = 2000000011, d = 12345,
m = 0xf0f0f0f0f0f0f0f0, n = 0x00ff00ff00ff00ff`. nargo execute gives
`(true, 12345678901234567, true, 3000000018, true, 81004, true,
162008912515188, 4217, true, 0xf000f000f000f0, true)`.

With hints that follow the rules, `--brillig-ops` reports 0 reachable
opcodes (exit 0); `generate-witness` succeeds on all three parties, the
REP3 proof is built (`Proof generation finished successfully` on each
party) and `co-noir verify` prints `Proof verified successfully`. The
opened public inputs are
`["1","12345678901234567","1","3000000018","1","81004","1","162008912515188","4217","1","67555025218437360","1"]`,
nargo's outputs (0xf000f000f000f0 = 67555025218437360).

A hint that breaks the rules fails at witness extension, on every party.
A u128 shift, for example:

```
Error: while running witness generation

Caused by:
   0: while getting rhs for int binary op
   1: expected int with size: u8, but got Int(64, U128)
```
