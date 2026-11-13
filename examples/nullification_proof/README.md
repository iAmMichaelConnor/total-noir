# Proof of nullification: a third party consumes an owner's note

Account B owns a note in contract A. An executor E wants A to consume
that note in E's own transaction: read its value and push its
nullifier, so the note is spent exactly as if B had spent it. E's PXE
has no access to B's nullifier hiding key, so aztec-nr's own spend
cannot run there. B consents off-line instead: B's PXE proves a small
standalone circuit and hands E the proof.

## Pieces

- `prove_nullification/` (bin): the owner's circuit. Public inputs:
  contract address, storage slot, owner, `executor` and `expiry` (B's
  optional binding, below), the note's packed fields. Private:
  randomness, nonce, `nhk_app` (B's app-siloed nullifier hiding key for
  A, aztec-nr v6's name for what is elsewhere called nsk_app). Returns
  `(leaf, nullifier, npk_app_hash)`. No asserts. Public-input layout:
  `[contract_address, storage_slot, owner, executor, expiry, fields...,
  leaf, nullifier, npk_app_hash]`.
- `noir/total_aztec/src/nullification_proof.nr`: the executor side,
  `consume_with_nullification_proof_or`. It takes the handoff
  `NullificationProof { vk, proof, executor, expiry, fields, leaf,
  leaf_index, sibling_path, nullifier }` as an argument, checks the
  leaf's path to the anchor block's note-hash-tree root as a flag (no
  oracle, no kernel read request), checks the binding as flags against
  `msg_sender` and the anchor block number, and under
  `ok = vk_ok & pin_ok & in_tree & !spent & bound_ok & !static & room`,
  with `bound_ok = executor_ok & expiry_ok`, verifies the proof
  recursively and pushes the nullifier.
- `executor/` (contract `NullificationExecutor`): contract A. `register`
  is B's one-time registration (the pin); `consume(owner, handoff)` is
  E's call, returning `(value, ok)`. B's verification key, which A's pin commits
  to, is in `executor/src/owner_vk.nr`.
- `executor_outer/` (bin): the executor's binding flags and recursive
  check with the library's public-input layout, outside Aztec, so bb can
  prove it.
- `make_fixture.py`: both off-chain sides, B's proofs and the reference
  implementation of the executor's pre-check.
- `outer_check.py`: proves and verifies `executor_outer` on B's real
  proofs.

## Passing the handoff

`consume` takes the handoff as an argument, so it is hashed into the
call's arguments like any other input, and every member is a Field. E
adds the leaf's index and sibling path in the note hash tree at the
block its PXE will anchor to (an Aztec node's `findLeavesIndexes` and
`getNoteHashSiblingPath`). With nothing to consume E passes
`NullificationProof::withheld()` (all zeros), which reads as
`ok = false`. Replay is prevented by the nullifier. `consume` works as
the transaction's first call and when reached through another contract.

The handoff is not a capsule: PXE 6.0.0 returns a stored capsule at its
stored length, so a capsule of another length stops the reader, and A's
own code can store one at any slot of A in the global scope
(`noir/total_aztec/src/nullification_proof.nr`, "Why arguments, not a
capsule"; the driver's TXE tests show both).

## The executor's pre-check

Before passing B's handoff
`(vk, proof, executor, expiry, fields, leaf, nullifier)`, E:

1. builds the public-input array itself, in the layout of
   `nullification_public_inputs`: `[A's address, the slot, the owner,
   B's claimed executor, B's claimed expiry, B's claimed fields, B's
   claimed leaf, B's claimed nullifier, pin_of(owner) read from A]`. A
   public-input list B supplies is input to nothing;
2. takes the vk A pins: its own vk of the owner circuit
   (`bb write_vk -t noir-recursive` on the published bytecode), or B's
   after checking its hash (poseidon2 over the 115 fields, bb's
   `vk.json` `hash`) equals A's `OWNER_CIRCUIT_VK_HASH`;
3. verifies B's proof natively against that vk and that array
   (`bb verify -t noir-recursive`, or bb.js), and passes the withheld
   handoff if it fails;
4. evaluates A's binding flags: `executor_ok` (executor is 0 or the
   address that will be A's `msg_sender`) and `expiry_ok` (expiry is 0
   or above the anchor block number E's PXE will use);
5. checks settledness (the leaf is in the note hash tree, e.g. an Aztec
   node's `findLeavesIndexes`, which also gives the index for the
   handoff's path) and freshness (the nullifier is not in the nullifier
   tree).

None of this is needed for totality: E can always pass the withheld
handoff and get `ok = false`. Steps 1-3 catch the one handoff A cannot
flag, a proof that does not verify for A's public inputs, which
simulates with `ok = true` and then fails E's proving (E would retry
with the withheld handoff). Steps 4-5 predict whether A returns `ok = true`. The pre-check
assumes bb's native verifier accepts exactly what the recursive verifier
accepts; `outer_check.py` checks that on the example's proofs.
`make_fixture.py` is the reference implementation.

## Threat model and what is proved

The owner controls the note and can withhold, delay or corrupt its
proof, and can prove over any preimage with any key. Nothing B does
makes E's transaction unprovable: the recursive verification is
predicated ([toolchain semantics](../../docs/toolchain-semantics.md),
section 3), so with the withheld handoff `ok = false` and bb proves the
circuit whatever the proof bytes. Every term of `ok` is computed from
the handoff, the pin and the anchor block, so `ok` is determined by
them. What remains:

- A handoff whose flags all hold and whose proof does not verify for A's
  public inputs: no flag form of recursive verification exists, so it
  fails proving. Whoever passes the handoff chooses this (E, or the code
  of a contract that passes it to A); `consume`'s call site carries the
  `total-lint: allow` marker that says so, and E's pre-check catches it.
- B spending the note between E's anchor block and E's inclusion is a
  race at inclusion (duplicate nullifier), as for any note two parties
  can spend.
- An unbound proof (`executor = 0`, `expiry = 0`) is bearer consent:
  whoever holds the handoff can have A consume the note in any
  transaction, at any later time, until the note is spent. B's only
  revocation is to spend the note itself, racing every holder.
- A bound proof is usable only with that address as A's `msg_sender`,
  which is A's immediate caller: E's account when E's entrypoint calls A,
  the intermediate contract when one calls A for E. A proof bound to a
  contract is usable by whoever can make that contract call A. With no
  `msg_sender` (A's function as the first call) only `executor = 0`
  admits.
- A proof with expiry X admits a transaction whose anchor block number
  n (E's PXE picks it) satisfies n < X, so it can land as late as
  timestamp(X - 1) + 86400 s (`MAX_TX_LIFETIME`). B converts its deadline
  with the chain's block time and subtracts the 24-hour margin.
- Revoking an unused proof is only B's self-spend or waiting out the
  expiry. A one-time nonce (a nullifier A checks and pushes on use, which
  B could emit to revoke) would be one more public input; not
  implemented.
- No chain id or protocol version is bound: the proof is replayable only
  where the same contract address holds the same leaf under the same pin
  (a fork or re-genesis with identical state).

Soundness depends on the pin. The owner circuit cannot check that
`nhk_app` is B's canonical key, so anyone who knows a note's preimage can
prove with any key k. A therefore pins `npk_app_hash` from B's own
registration, where the kernel validates `nhk_app` against B's
`npk_m_hash` and `get_public_keys` proves that against B's address. With
the pin, the nullifier E pushes is the one B's own spend would push (the
TXE test checks it against aztec-nr's formula), so the note is spent once.
The vk is pinned by hash in A's code.

## Run

```
./run.sh      # needs nargo 1.0.0-rc.3, bb 6.0.0 and python3 on PATH
```

`run.sh` first builds `total-lint` with cargo (Rust 1.89 or later); set
`TOTAL_LINT` to a built binary to skip that.

The TXE tests use the stock `txe` server of `@aztec-labs/txe` 6.0.0
(`npm install -g @aztec-labs/txe@6.0.0`); set `TXE` to another start
command, or `SKIP_TXE=1` to skip them (and the proving steps that need
their values). Scratch files, and `TMPDIR`, go in a `mktemp -d` directory
under `${TXE_TMP_ROOT:-${TMPDIR:-/tmp}}`, deleted on exit; keep that root
short, because the TXE's Unix socket paths fail past 107 bytes.

The TXE does not check recursive proofs, so the TXE tests show the flow,
the flags, the leaf's membership path against the real tree and the
nullifier's canonical value; `outer_check.py` shows the proof verifies
under A's public-input layout, binding included, and fails under a wrong
one.

After changing the owner circuit, run `python3 make_fixture.py --vk --update`
to rewrite `executor/src/owner_vk.nr` and A's pin.

## Gate counts

On nargo 1.0.0-rc.3 and bb 6.0.0:

| Circuit | ACIR opcodes | Gates | Prover |
|---|---|---|---|
| `prove_nullification` (owner, one-field note) | 20 | 478 | UltraHonk (`bb gates -t noir-recursive`) |
| `NullificationExecutor.consume` (executor, one verification, the 621-Field handoff argument, leaf membership flag, binding flags) | 3560 | 30180 | Chonk (`bb gates -s chonk`) |
| `TotalAztecDriver.consume_with_proof` (the library entry in the driver) | 2683 | 26807 | Chonk |
| `NullificationExecutor.register` (owner's registration) | 937 | 5877 | Chonk |
| `executor_outer` (binding flags and the recursive check outside Aztec) | 214 | 707347 | UltraHonk |
| `docs/recagg-probe/outer` (one verification under `if present`) | 2 | 703984 | UltraHonk |
