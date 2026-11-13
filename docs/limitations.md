# Known limitations

What the library does not cover, and what its guarantees depend on.

- **Widths.** Range flags, clamps, `cmp_bits`, `truncate_or` and the bit
  decompositions go up to 253 bits, the byte decompositions to 31 bytes, and
  `ec::mul_or` scalars to 254 bits. Field-domain arithmetic, the bitwise
  entries and the W-bit collection entries stop at 128 bits (127 for `neg_or`
  and `wrapping_neg_or`, 126 for the exponent width of `pow_or`, 84 for
  `mul_div_or`, whose wide form covers 85 to 128). Merkle depth stops at 128.
- **Black boxes.** The ECDSA entries call backend black boxes on inputs
  they have validated, with the key blinded by an in-circuit multiple of G
  and the hash adjusted to match; the verdict is the black box's on the
  inputs for every hint the constraints accept, given that bb's ECDSA
  gadget is sound. That every input has a proof is a statement about the
  pinned toolchain (nargo 1.0.0-rc.3, bb 6.0.0), not about constraints the
  library emits; [docs/ecdsa-totality.md](ecdsa-totality.md) states
  and proves it from bb's source. bb's ECDSA gadgets fail on some inputs
  the solver accepts: exact x-coordinate collisions in their incomplete
  additions, and "aliasing" in bb's non-equality check, which compares
  integers modulo the circuit's native modulus only (so it also fails in
  the "complete" additions and doublings). The wrappers let the prover
  choose the scalar `u1 = z'/s` the black box sees; for every admissible
  input a choice exists that bb can prove, by a counting argument with
  finite computations (`scripts/ecdsa_totality_checks.py`,
  `scripts/ecdsa_alias_multiplicity.py`), under one named assumption:
  aliasing between two x-coordinates that both move with the key happens
  for a negligible fraction of keys (the heuristic bb itself relies on for
  honest inputs). The honest hint finds such a choice by emulating bb's
  multiplication ([k1_emul.nr](../noir/total/src/ecdsa/k1_emul.nr),
  [r1_emul.nr](../noir/total/src/ecdsa/r1_emul.nr)) and retrying; that the
  emulation matches bb is tested against `bb prove` in both directions
  (`scripts/ecdsa_differential.py`), not proved. On secp256r1 the emulation
  leaves out bb's two-point multiplication, whose exact failures exclude
  at most 383 keys. A different bb needs the proof, the emulations and the
  differential run redone ([CONTRIBUTING.md](../CONTRIBUTING.md)).
  `msm_or`, and `schnorr_verify` built on it, pass the MSM black box bases
  blinded by hinted points; their output is the true MSM for every hint the
  constraints accept, given that bb's MSM gadget is sound. That every input
  has a proof rests on bb 6.0.0's gadget failing valid inputs only through
  the x-coordinate assertions [ec.nr](../noir/total/src/ec.nr) lists (read from
  its source, checked by proving the inputs that break it unblinded in
  [total_prove_check](../noir/total_prove_check)), and on the hint's Poseidon2
  derivation of the blinds, which misses the excluded values except with
  probability below 158 (N + 2) / 2^252. A backend or bb version whose MSM
  gadget asserts something else needs the argument redone.
- **ECDSA.** `ecdsa_k1_verify` and `ecdsa_r1_verify` reject a valid
  signature with probability about 2^-128 (k1) and 2^-130 (r1): those in the
  input classes the wrappers exclude (see `*_sig_admissible`; `r >= n`, also
  excluded, is never valid). Blinding does not change the verdict, so it
  adds no rejections. The honest prover fails to find a provable blind
  with probability below 2^-90 (k1) for any input, in the random-oracle
  model and under the assumptions named in
  [docs/ecdsa-totality.md](ecdsa-totality.md); on secp256k1 inputs
  exist for which about half of all blinds are unprovable, so the hint may
  try several candidates (at most 256).
- **Aztec.** Four limits no code in a callee's functions can reach
  ([total_aztec/src/lib.nr](../noir/total_aztec/src/lib.nr)): a callee's
  `sync_state` runs in the caller's PXE before the call, outside every
  wrapper; a callee's owner can schedule a class upgrade, which the caller's
  circuit cannot pin or flag; the transaction's expiration window and code
  outside these entries are not covered; and simulation and proving are
  separate executions, so hint-backed flags can differ between them. Note
  reads find a pending note only when the reading call itself pushed its
  note hash (no oracle exposes another call's note hashes), so a note
  created earlier in the transaction by another call reads as not found
  ([note.nr](../noir/total_aztec/src/note.nr), "The note hash the read
  request names"), which is why the example account checks its
  constructor's key, bound to its address, until it is initialised at the
  anchor block, so that a self-paid deployment works (for up to a day
  after deployment an older anchor still selects that key; see
  [its README](../examples/total_account/README.md#two-phase-signing-key)); and a class that writes a `DelayedPublicMutable`'s
  slots directly can make a reader's expiration fall at its anchor block.
  The lint accepts aztec-nr's own items through per-contract baselines
  without analysing them ([docs/design.md](design.md#what-it-cannot-decide-by-construction)).
- **co-noir.** The library's own hints all run in co-noir's MPC witness
  extension except those of `sqrt_or` (and `sqrt_canonical_or`) and of the
  ECDSA entries' key blinding. `sha256_var_or`, `keccak256_var_or` and the
  ECDSA entries call third-party hints or black boxes co-noir cannot run
  ([docs/co-noir.md](co-noir.md)).
- **A total circuit can still be wrong.** Within these limits, the library
  guarantees a proof exists and the flag is honest. What to do when `ok` is
  false is your design.
