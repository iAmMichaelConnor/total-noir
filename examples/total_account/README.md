# TotalAccount: an account contract other users can call safely

An Aztec v6 Schnorr account contract (aztec-nr, `#[aztec]`) with one
function meant for other people's transactions: `encrypt_for_owner`, which
encrypts four fields to the account owner's encryption key.

## Threat model

When user A's transaction calls account B's `encrypt_for_owner`, A's PXE
executes B's code against state B's owner controls: the stored encryption
key, or its absence. B's owner must not be able to make an honest
execution of A's transaction fail. Every failure B's owner can cause in
`encrypt_for_owner`'s body comes back as `ok = false`, with every other
returned Field set to 0. Outside the body, and not covered: B's
`sync_state`, which A's PXE runs before the call (a planted trap there
aborts A's simulation), an upgrade of B's class, and the expiration
window below (`noir/total_aztec/src/lib.nr` lists these).

The key is public state in a `DelayedPublicMutable` that only the owner
writes (`set_encryption_key`, a public `#[only_self]` function), read from
private with total_aztec's `delayed_public_mutable_read_or`, which proves
every slot at the anchor block and flags a stored state the variable's
own functions cannot produce: a change takes effect only after the
delay, and the read sets the caller's transaction expiration so the key
cannot go stale before inclusion ([below](#delay-and-expiration)).

All rows below are what a third party gets in production (the TXE tests
run A with its own scope only):

| owner-controlled condition | reachable with this class? | result for A |
|---|---|---|
| good key, current | yes | `ok = true`; the owner decrypts |
| first key scheduled, delay not passed | yes (every new account, for the initial delay) | `ok = false`; the key is not current yet |
| key rotated by the owner, new key pending | yes | `ok = true`, to the key current at A's anchor block |
| key rotated, new key current | yes | `ok = true`, to the new key |
| account never constructed (no initialization nullifier, key slot (0, 0)) | yes | `ok = false` (`#[noinitcheck]`; (0, 0) is refused) |
| owner tries to store an off-curve, (0, 0) or (p - 1, p - 1) key | yes | the owner's own transaction fails; the stored key is unchanged |
| key slot holds an off-curve or (p - 1, p - 1) key | no (the only writer refuses it); planted in the tests | `ok = false` |

Inputs A controls are flagged the same way (randomness 0 gives
`ok = false`). The constructor and `set_encryption_key` refuse a key that
is not a finite curve point, so the contract never stores a bad key;
the read path flags one anyway.

## Functions

| function | kind | who runs it | failure sources of its own |
|---|---|---|---|
| `constructor(signing_pub_key_x, signing_pub_key_y, enc_pk_x, enc_pk_y)` | private, initializer | deployer | two write-time key refusals; records its arguments for later calls of its transaction (no failure source) |
| `set_encryption_key(x, y)` | public, `#[only_self]`, `#[noinitcheck]` | owner (a public call in a payload signed through the entrypoint; enqueued by the constructor) | one write-time key refusal; schedules the key after the current delay |
| `encrypt_for_owner(plaintext: [Field; 4], randomness)` -> `(eph_pk_x, eph_pk_y, ciphertext: [Field; 5], ok)` | private, `#[noinitcheck]` | anyone | none |
| `decrypt_for_owner(enc_sk, eph_pk_x, eph_pk_y, ciphertext)` -> `([Field; 4], ok)` | utility | owner's PXE | none (unconstrained, trap-free); takes the secret key as an argument, which stays in the owner's PXE but passes through the wallet's call path |
| `entrypoint(app_payload, fee_payment_method, cancellable)` | private | owner, including in the account's own deployment transaction | AccountActions' signature assert ([two-phase key](#two-phase-signing-key)) |
| `verify_private_authwit(inner_hash)` | private, view | callers checking an authwit | AccountActions' "not authorized" assert ([two-phase key](#two-phase-signing-key)) |
| `lookup_validity(consumer, inner_hash)` | utility | wallets | none of its own (reads the key note, so it fails before the account is initialised) |

## Two-phase signing key

A self-paid deployment (aztec.js v6 `DeployAccountMethod` with
`NO_FROM`) is one transaction that calls the constructor and then the
account's own `entrypoint`, which pays the fee. The constructor creates the
signing key note there, and to `entrypoint` it is a pending note of another
call: total_aztec's note reads find a pending note only in the call that
pushed its note hash, because only the kernel can check another call's
(`noir/total_aztec/src/note.nr`). So the signature check has two phases
(`src/signing_key.nr`):

- **Before the account is initialised at the anchor block** (its private
  initialisation nullifier, `poseidon2(address, initialization hash)`
  siloed by the address, is absent from the anchor block's nullifier
  tree), the signing key the deployer passed to the constructor. The
  constructor records its arguments with total_aztec's
  `record_initializer_args` (a PXE transient array, seen only by this
  contract's later frames in the same transaction), and `is_valid_impl`
  reads them with `initializer_args_or`, which checks them against the
  initialization hash in the account's address (`bound`), and proves the
  nullifier's absence or presence with one indexed-tree witness.
- **Once it is initialised**, the key note, exactly as before.

```
valid = (!initialized & bound & schnorr(constructor key))
      | (initialized & found & schnorr(note key))
```

`initialized` is determined by the anchor block, and `bound` is true only
for the arguments the address commits to, so whoever executes the check
can make it false (as always, by withholding the hint, the note or the
witness) but can make it true only with a signature by the key of the
phase the anchor block puts it in. No record makes the check unprovable:
a missing, wrong or wrong-length record is `bound = false`. What would
make the hint abort is an element wider than one Field at the record's
slot, which only this contract's own code could write, with the raw
transient oracles; this contract writes the slot only through
`record_initializer_args` (TXE test
`a_wider_element_written_outside_the_library_fails_the_reader`).

An honest PXE has the record only in the deployment transaction, after the
constructor; a never-constructed account authorises nothing, as before.

**Caveat: the anchor block decides the phase, and the executor chooses
it.** A transaction anchored at any block before the one that includes the
deployment sees the account as not initialised, and a dishonest executor
can supply the constructor's arguments (they are no secret to whoever holds
the instance), so the constructor's key keeps authorising such
transactions even after the key note says otherwise. The protocol bounds
how old an anchor can be at inclusion: the kernel caps a transaction's
expiration at its anchor block's timestamp plus `MAX_TX_LIFETIME` (86400
seconds in v6), and a block includes a transaction only up to that
expiration. So the constructor's key can authorise transactions included
up to one day after the last block before the deployment's block. In this
account the key note is a `SinglePrivateImmutable` holding the same key,
so the caveat changes nothing here; it matters for an account whose key
note can change, which then has to treat the first day after deployment as
a period in which the first key is still valid.

`lookup_validity` (a utility function wallets call off the chain) still
reads the key note only.

## Encryption scheme

E = [r]G, S = [r]PK, AE key S.x, AE nonce E.x. The AE is the SAFE-API
Poseidon2 duplex of Taceo's `pss_utils/src/ae.nr`, extended past one rate
block; `src/ecies.nr` documents it.

Both the AE key and the nonce derive from the caller's `randomness`, so
two encryptions to the same key with the same `randomness` share a
keystream: `randomness` must be fresh for every message (only 0 is
refused). The scheme has no KDF and binds no recipient, contract or chain
into the key or tag. It is example code for totality over an
owner-controlled key, not a vetted encryption scheme: do not copy it.

Known property: (E, c) and (-E, c) both decrypt, since -E gives the same
shared x and the same nonce. Ciphertext re-encoding, not a forgery
(pinned by a test).

## Delay and expiration

- The delay. A key takes effect only after the delay
  (`ENC_KEY_INITIAL_DELAY`, one day, a `DEV DECISION` in `src/enc_key.nr`,
  fixed for the life of the account). A key set in the constructor is therefore
  current only a day after deployment: until then `encrypt_for_owner` gives
  `ok = false`.
- The expiration. A read lowers the transaction's expiration to the
  variable's time horizon: anchor + delay - 1 second with nothing
  pending, or one second before a pending key change.
- The owner cannot change the delay: this contract never calls
  `schedule_delay_change`. A pending key change can leave a reader
  anchored just before its public activation time too little time to be
  included, but this costs a retry, not a failure: it can happen at most
  once per delay period, and a reader anchored at or after the change has
  the full window again.
- The key and every rotation are public and linkable to the account.

## Running

```sh
./run.sh      # needs nargo 1.0.0-rc.3, bb 6.0.0 and python3 on PATH
```

`run.sh` first builds `total-lint` with cargo (Rust 1.89 or later); set
`TOTAL_LINT` to a built binary to skip that.

The TXE tests use the stock `txe` server of `@aztec-labs/txe` 6.0.0
(`npm install -g @aztec-labs/txe@6.0.0`); set `TXE` to another start
command, or `SKIP_TXE=1` to skip them. The self-paid deployment tests
deploy `../total_account_multicall`, a test contract that makes the two
calls of that transaction (the TXE runs one top-level call per
transaction). Scratch files, and `TMPDIR`, go in
a `mktemp -d` directory under `${TXE_TMP_ROOT:-${TMPDIR:-/tmp}}`, deleted
on exit; keep that root short, because the TXE's Unix socket paths fail
past 107 bytes.

## Attribution

The authenticated encryption in `src/ecies.nr` is adapted from
`noir_logic/pss_utils/src/ae.nr` of TaceoLabs' Monty Hall application,
<https://github.com/TaceoLabs/monty-hall-aztec> (MIT License, Copyright (c)
2025 TaceoLabs; the notice is reproduced in `src/ecies.nr`). The ECDH
follows the shape of that repository's `dh.nr` (an ephemeral key pair, the
shared point's x-coordinate as the key) without using its code. The
contract layout follows aztec-nr's v6 `schnorr_account_contract`.
