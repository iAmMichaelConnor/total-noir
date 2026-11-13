# total_caller: a caller that a total callee's owner cannot fail

Contract A (`Caller`) has a private function that calls a function of an
account B: `seal_to(account, plaintext, randomness)` asks B to encrypt four
fields to B's owner through `encrypt_for_owner` and returns B's output
with a flag. The workspace has three members: `caller` (A, with the TXE
tests), `grief_account` (one of the two Bs; the other B is
`examples/total_account`) and `short_account` (a test-only callee with
the same selector and a two-Field return).

## Threat model

- B's owner controls B's code (the class B was deployed with) and B's
  state: what B stores, whether B was ever initialised, what B's own
  writers let the owner change.
- A's user's PXE supplies every witness of A's transaction, including
  B's part: it executes B's code against B's state as A's PXE sees it.
  A's PXE holds only A's user's own keys and cannot read B's notes, so
  anything B wants callers to read sits in public state, read from
  private at the anchor block.
- A must not be failable by B. A failed private call fails the whole
  transaction, so if B's owner can put B into a state in which B's
  function has no witness, B's owner can stop A's transaction.

A cannot defend against that inside its own circuit: B's call either has
a witness or it does not. What A can do is (1) be total over whatever B
returns within the interface A calls, and (2) call only Bs whose code is
total. The two Bs here have the same interface and differ only in that.
`GriefAccount` (grief_account/) is the ordinary aztec-nr way of writing
the same function with a key callers can read. Do not copy it.

## What A does

A makes one call, `total_aztec::static_call_flagged_or`, the library form
of this pattern:

- a static call by selector, so B cannot add note hashes, nullifiers or
  logs to A's transaction (a nullifier that already exists would fail
  it);
- B's returns read as `[Field; 8]`, so no typed decoding can fail, with
  B's flag taken by `total::convert::bool_or`: ok only when the last
  Field is exactly 1;
- the seven output Fields masked to 0 when the flag is false.

The return arity is part of the interface A trusts. A is total over any
eight-Field return, but a callee with the same selector and a different
number of return Fields fails A's call at the returns-preimage oracle
(TXE test against `short_account`: "Foreign call return value does not
match expected size"), before any constraint of A's runs. That is a
property of B's class, like every other way B's code can fail: check the
class, not only the selector, before relying on it (and see
`noir/total_aztec/src/lib.nr` on class upgrades).

## Results (TXE tests, `caller/src/test.nr`)

A's user holds only its own scope in every test, so every row is what A
gets in production.

| owner-controlled state | TotalAccount: A's transaction | GriefAccount: A's transaction |
|---|---|---|
| good key (control) | completes, `ok = true`, owner decrypts | completes, `ok = true` |
| owner rotated the key, delay not passed | completes, `ok = true`, encrypted to the current key | (no rotation: PublicImmutable) |
| owner rotated the key, delay passed | completes, `ok = true`, encrypted to the new key | (no rotation: PublicImmutable) |
| account never constructed | completes, `ok = false` | fails: "Trying to read from uninitialized PublicImmutable" |
| off-curve key, or (p - 1, p - 1) | not reachable: the owner's write fails ("encryption key is not a finite curve point"); planted in storage anyway, A completes with `ok = false` | reachable (stored unchecked); fails: MSM "is not on curve" |
| key (0, 0), std's infinity encoding | not reachable through the writer (refused) and the same storage as no key; planted, A completes with `ok = false` | reachable; completes with `ok = true` and an AE key of 0: anyone can open the ciphertext (a confidentiality failure, not griefing; the test recovers the plaintext from the public output) |

## Running

```sh
./run.sh      # needs nargo 1.0.0-rc.3, bb 6.0.0 and python3 on PATH
```

`run.sh` first builds `total-lint` with cargo (Rust 1.89 or later); set
`TOTAL_LINT` to a built binary to skip that.

The TXE tests use the stock `txe` server of `@aztec-labs/txe` 6.0.0
(`npm install -g @aztec-labs/txe@6.0.0`); set `TXE` to another start
command, or `SKIP_TXE=1` to skip them.

The tests deploy TotalAccount as `../total_account@total_account/TotalAccount`
(workspace-relative `dir@package/contract`): TXE 6.0.0 drops the directory
from the plain `dir/contract` form. `run.sh` makes its scratch directory
with `mktemp -d` under `${TXE_TMP_ROOT:-${TMPDIR:-/tmp}}` and exports it as
`TMPDIR`: TXE puts Unix sockets there, and a socket path over 107 bytes
fails with EINVAL, so keep the root short.
