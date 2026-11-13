# Toolchain semantics (nargo 1.0.0-rc.3, bb 6.0.0)

Checked on noirc 1.0.0-rc.3+5a7ee9bf. Every claim below comes from a
compiled probe (`nargo compile --print-acir`), a real `nargo execute`, or
both, on this toolchain.

Witness naming in excerpts: `w0, w1, ...` are ACIR witnesses; `RANGE input:
wN, bits: K` is the range blackbox; `ASSERT` is an AssertZero written as an
equation. The probe sources are not included: each probe is a one-line bin
package (`fn main(...)` around the operation named in the probe), compiled
and executed at the listed inputs. Two exceptions: the RecursiveAggregation
probe (section 3) is in `recagg-probe/`, and section 5 compiles the
library's own `core.nr`.

## 1. Native operator behaviour

### Unsigned u8/u16/u32/u64/u128

Add, sub, mul emit one input-falsifiable RANGE on the raw result:

    ASSERT w3 = w0 + w1
    RANGE w3, 8 bits // attempt to add with overflow

Executes: 255+1, 0-1, 255*2 (u8), same shapes at u64, u128, u16 add,
u32 mul all fail witness generation; in-range values pass.

Division emits a hinted inverse with `ASSERT 0 = w1*w3 - 1` (the
divisor-nonzero check, falsifiable at b = 0), then the Euclidean split
(hinted q, r; RANGE both; `ASSERT w5 = -w1*w4 + w0`; r < b via
`ASSERT w6 = w1 - w5 - 1` + RANGE). 7/0 and 7%0 fail with "Cannot satisfy
constraint"; 0/7 is fine. Note this is exactly the library's div_split
constraint set plus the falsifiable nonzero check.

Shifts: the shift amount must have the same type as the left operand. Two
separate behaviours, from the u8 ACIR:

    ASSERT w3 = 0 // attempt to bit-shift with overflow   <- s >= width asserts
    ...pow2 by squaring over the bits of s...
    BRILLIG CALL ... inputs: [w0*w13, 256] ...            <- product truncated
    ASSERT w15 = w0*w13 - 256*w14                          <- silently (hinted split)

So `a << s` asserts iff s >= width (1u8 << 8 fails) and silently drops bits
shifted out the top (255u8 << 1 == 254, 64i8 << 1 == -128). `>>` asserts on
s >= width, otherwise total (logical for uN, arithmetic/sign-extending for
iN: -3i8 >> 1 == -2).

Bitwise & | ^ lower to AND/XOR blackboxes (u8_and is a single
`BLACKBOX::AND ... bits: 8`); `!a` is pure arithmetic (`w1 = 255 - w0`).
Total.

Comparisons: `==`/`!=` use the inversion gadget (below); `<` and friends use
a hinted borrow decomposition of a - b + 2^N:

    BRILLIG CALL ... inputs: [w0 - w1 + 256, 256], outputs: [w11, w12]
    RANGE w11, 1 bit        <- borrow
    RANGE w12, 8 bits       <- remainder
    ASSERT w12 = w0 - w1 - 256*w11 + 256

For in-range operands a - b + 2^N is in [1, 2^(N+1) - 1], so the split always
exists: hint-satisfiable, total. (The mechanism for u-type compares is this
borrow split, not a bb lookup; RANGE may be lookup-backed inside bb, but that
is a backend detail.) u128 uses the same shape with an extra two-sided
128-bit range on the remainder. Executes at (1, max), (max, 1), (x, x) pass
for u8/u64/u128 and give the right flags.

### Signed i8/i16/i32/i64

Add/sub/mul extract sign bits via hinted splits and assert a
"same signs in, different sign out" flag:

    ASSERT w11 = w11*w16 // attempt to add with overflow

127i8+1, -128i8-1, -128i8*-1, i64 equivalents, 32767i16+1 all fail; in-range
passes. Division rounds toward zero (-7/2 == -3), asserts on b = 0 and on
MIN / -1 (result overflow). Modulo takes the dividend's sign (-7%2 == -1,
7%-2 == 1), asserts on b = 0 and on MIN % -1. Unary minus asserts exactly at MIN
(-(-128i8) fails, i32 MIN fails). Bitwise and comparisons total, signed
order (-1 < 1 true).

### Field

+, -, *, unary minus: total, wrap mod p: (p-1)+1 == 0,
0-1 == p-1, (p-1)*(p-1) == 1, -1 == p-1.

`/` is not total. ACIR:

    BRILLIG CALL func: 0 (invert), inputs: [w1], outputs: [w3]
    ASSERT 0 = w1*w3 - 1          <- falsifiable at w1 = 0
    ASSERT w2 = w0*w3

6/0 and 0/0 both fail ("Cannot satisfy constraint"). Treat native Field
division as an asserting op; inverse_or/field_div_or is the total form.

`==`/`!=`: the inversion gadget, total, from the probe:

    BRILLIG CALL (invert) inputs: [w4], outputs: [w5]   w4 = a - b
    ASSERT w6 = -w4*w5 + 1                              z := 1 - d*inv
    ASSERT 0 = w4*w6                                    d*z == 0

Hint-satisfiable for every input (d = 0: inv free, z = 1 forced; d != 0:
z = 0, inv = 1/d forced); z is determined both ways. There is no
separate booleanity constraint on z: z is a defined witness, and the two
equations force it to exactly 0 or 1.

%, <<, >>, &, |, ^, !, <, <=, >, >= on Field: compile errors
("Bitwise operations are invalid on Field types", "Fields cannot be
compared", "Cannot do modulo on Fields").

### bool

& | ^ ! == != total, pure arithmetic (`w2 = w0*w1`, `w3 = w0 + w1 - w0*w1`,
xor, `1 - w0`; eq via the inversion gadget). Order comparisons < <= > >=
compile and are total (false < true); same borrow-split shape at base 2.
+ - * / % unary-minus << >>: compile errors.

### Entry-point parameters

Every integer/bool parameter gets an unconditional RANGE on its input
witness (`RANGE w0, 8 bits` for a u8 param; 1 bit for bool). There is no
predicate on a RANGE opcode. nargo's ABI additionally rejects out-of-range
Prover.toml values before solving ("Value Field(256) does not fall within
range ... width: 8").

## 2. Casts

All 110 ordered pairs over {Field, u8..u128, i8..i64, bool} compiled and the
compiling ones executed at boundary values. No cast ever fails at runtime:
every compiling cast is total, and lossy ones truncate silently.

- uN -> wider uN/iN: zero-extend, literally free in ACIR
  (`cast_u8_i16` is `ASSERT w1 = w0`).
- uN -> narrower: hinted quotient split (`ASSERT w3 = w0 - 256*w2` with
  RANGE on both parts): value mod 2^M, hint-satisfiable, silent.
- uN -> iN same width: reinterpret (255u8 as i8 == -1).
- iN -> wider iN: sign-extend (-1 -> -1, MIN -> MIN).
- iN -> uM, any M: two's complement value mod 2^M, i.e. sign-extend then
  truncate: -1i8 as u128 == 2^128 - 1; i64 MIN as u128 == 2^128 - 2^63;
  -128i8 as u16 == 0xFF80. ACIR extracts the sign bit and adds
  (2^M - 2^N)*sign.
- iN -> narrower iN: truncate the pattern (i64 MIN as i8 == 0).
- Field -> uN/iN: truncation of the canonical integer value (as
  convert.nr assumes): (p-1) as u8 == 0 (p ≡ 1 mod 2^28),
  300 as u8 == 44, (p-1) as u128 == p-1 mod 2^128, (p-1) as i32 ==
  -268435456 (pattern 0xF0000000). The ACIR is a hinted split
  x = Q*2^N + r with RANGE 246 on Q, RANGE N on r, plus a canonicity
  gadget: Q <= (p-1)/2^N enforced by a 246-bit RANGE on (p-1)/2^N - Q, and
  an is-zero gadget forcing r = 0 when Q is at its maximum. All
  hint-satisfiable for every Field element; the split is pinned to the
  canonical value, so the result is determined.
- uN -> Field: exact injection, free. iN -> Field: compile error ("Only
  unsigned integer types may be casted to Field"); the signed facade goes
  `as uN as Field`, which gives the two's complement pattern.
- bool -> anything numeric/Field: 0/1, total. anything -> bool: compile
  error ("Cannot cast `u8` as `bool`").

## 3. Predication of failure sources under a dynamic `if`

Every probe has the shape `if c { <failing op> }` with c a runtime bool
input and inputs that make the op fail; "taken" = c true (must fail),
"not-taken" = c false (passes iff predicated). Result: every probed source
is predicated (RecursiveAggregation with a backend-defined failure, below),
so clamp-and-select can be relaxed to `if ok { risky }` for these op
classes once ok is computed totally.

Mechanisms seen in ACIR:

- assert / assert_eq: constraint multiplied by c:
  `ASSERT 0 = w0*w1 // pred assert`.
- Integer overflow (+ - *): operands gated: `ASSERT w4 = w0*w1 + w0*w2;
  RANGE w4, 8 bits`, vacuous when c = 0.
- Division/modulo by zero: the nonzero check becomes `ASSERT 0 = w0*w5`
  (w5 = is-zero flag of the divisor); the quotient brillig call carries
  `predicate: w0`; the reconstruction is multiplied by c. u128 mul the same
  with limb machinery.
- Array OOB read and write: the index is gated: `ASSERT w6 = w0*w4;
  READ w7 = b0[w6]`; a gated write writes the old value back at slot 0.
  Both fail under c = true ("Index out of bounds, array has size 3, but
  index was 10") and pass under c = false.
- assert_max_bit_size and to_le_bits::<short>: the checked value is gated
  (RANGE/decomposition of c*x).
- User unconstrained calls: `BRILLIG CALL ... predicate: w0`. Under c =
  false the VM does not execute the call (a divide-by-zero hint body does
  not trap) and the outputs are zeroed.
- embedded_curve_add / multi_scalar_mul: the blackbox carries
  `predicate: w0`. With an off-curve point: taken fails with "Failed to
  solve blackbox function: embedded_curve_add, reason: Point (...) is not
  on curve"; not-taken passes. Same for multi_scalar_mul. So these
  blackboxes are failure sources for invalid points, and are predicated.
- poseidon2_permutation: no predicate on the blackbox; it executes under a
  false condition on unmodified inputs (fine, because the permutation is
  total), and only the outputs are gated (`ASSERT w2 = w0*w4`).
- ecdsa_secp256k1::verify_signature: the blackbox has a predicate argument.
  With garbage u8 inputs (invalid pk, invalid sig) it returns false rather
  than failing, both at top level and under a predicate, on this solver.
  Witness generation does not fail, but bb cannot prove the solver's
  witness for some inputs (noir/total/src/ecdsa.nr, module header): where
  the solver and bb disagree, and also for valid on-curve keys on which
  bb's multiplication meets equal x-coordinates in an incomplete addition,
  which a key holder can construct on both curves; treat
  "returns false on malformed input" as verified for this toolchain's
  witness generation only, not as a guarantee that a proof exists or a
  portable guarantee across backends. On released nargo 1.0.0 (275d3ab, same bb
  6.0.0 binary) the solver reduces R.x mod n before comparing it with r
  (noir commit 328684c, #14109; the std wrapper and bb are unchanged), so
  the R.x = r + n class that the rc.3 solver rejects and bb then cannot
  prove returns true there and proves; total's ecdsa wrappers gate the
  class and return false under both toolchains, and pass the black box a
  blinded key so that its multiplication has a proof.
  Aztec v6.0.0's PXE and TXE bundle `@aztec-foundation/noir-acvm_js` 6.0.0,
  built from the rc.3 commit (5a7ee9bf), so inside a v6 PXE the raw black box
  on that class is still unprovable whichever nargo compiled the contract.

- RecursiveAggregation (`std::verify_proof_with_type`, ZK UltraHonk,
  proof_type 6, the type aztec-nr contracts verify), probed with a real
  inner proof. Method extended to proving: a tiny inner
  circuit (`assert(x * x == y)`) proven with `bb prove -t noir-recursive`
  (115 vk fields, 458 proof fields); an outer circuit verifying it under
  `if present`; every case through nargo execute, bb prove and bb verify
  against the vk of the valid case. Sources and the script in
  `recagg-probe/`, output in `recagg-probe/results.txt`. ACIR:

      BLACKBOX::RECURSIVE_AGGREGATION verification_key: [...], proof: [...],
        public_inputs: [w575], key_hash: w574, proof_type: 6, predicate: w0

  (the same call outside a branch has `predicate: 1`). Results:

      case                          execute  bb prove                    bb verify
      present, valid proof          ok       ok                          ok
      absent, garbage vk and proof  ok       ok                          ok
      absent, all-zero              ok       ok                          ok
      absent, valid proof           ok       ok                          ok
      present, garbage              ok       FAILS (remainder assertion)  -
      present, all-zero             ok       FAILS (VK Hash Mismatch)    -
      present, one field flipped    ok       FAILS (proof does not verify) -
      present, wrong public input   ok       FAILS (proof does not verify) -
      present, wrong key_hash       ok       FAILS (VK Hash Mismatch)    -
      unconditional, valid          ok       ok                          ok
      unconditional, garbage        ok       FAILS (remainder assertion)  -

  So it is predicated, but differently from the other black boxes: the
  ACVM solver never checks the proof (witness generation succeeds even
  for garbage under a true predicate), and the failure, when there is
  one, is bb's: an invalid proof under a true predicate leaves the
  circuit unprovable. Under a false predicate bb proves and verifies
  whatever the proof bytes, with the same vk (the circuit does not depend
  on the witness). The failure is backend-defined, a proving failure
  rather than a witness failure. Outer circuit: 703984 UltraHonk gates.

  More UltraHonk cases (same toolchain; every one behaved as the claim
  predicts, and every outer package had
  one vk hash across all its cases, so the circuit and vk do not depend
  on the witness):

      predicate from an unconstrained hint (typed bool return, RANGE 1):
        0 + garbage proves and verifies; 1 + valid proves; 1 + garbage fails
      two verifications under two predicates: (1 valid, 0 garbage),
        (0 garbage, 1 valid), (0, 0 garbage), (1 valid, 1 valid of another
        circuit size) prove; (1 garbage, 0 valid) fails
      predicate 0 with a vk of another circuit size (21920 gates, log size
        15 against 5), with a non-ZK proof padded to 458 fields under proof
        type 6, with a ZK proof truncated under proof type 0, and with a
        bigger circuit's vk plus a garbage proof: all prove
      predicate 1 with a valid proof of another circuit size: proves (the
        recursive verifier takes the size from the vk witness)
      predicate 1 with the wrong proof type (non-ZK bytes under type 6, or
        ZK bytes truncated under type 0): fails

  Mechanism, from bb 6.0.0's sources (aztec-packages git tag v6.0.0,
  barretenberg/cpp/src/barretenberg/dsl/acir_format):
  acir_to_constraint_buf.cpp drops a RecursiveAggregation whose predicate
  is the constant 0 ("No constraint if the recursion is disabled");
  honk_recursion_constraint.cpp, step 3: when the predicate is a witness,
  every vk field, every proof field (the ACIR public inputs are prepended
  to the proof first) and the key hash are
  `conditional_assign(predicate, user value, valid value)`, the valid
  values being the proof and vk of a one-gate circuit with the right
  number of public inputs that `construct_arbitrary_valid_honk_proof_and_vk`
  proves at proving time; the recursive verifier then runs on the
  substituted values. So under predicate 0 the user's bytes are never
  examined (no range check, no shape check) and under 1 they are verified
  in full, vk hash included. The predicate is a `bool_ct` (booleanity
  enforced). The only static requirement is that the ACIR proof array
  has the length of its proof type (a BB_ASSERT at circuit construction,
  independent of the witness).

  Chonk. Aztec private functions are proven by the PXE's client-side
  prover (Chonk, ClientIVC over Mega circuits), not by `bb prove`. The
  predicate handling above is one template,
  `create_honk_recursion_constraints<Flavor, IO>`, explicitly
  instantiated for UltraCircuitBuilder and, through
  INSTANTIATE_FOR_EACH_MEGA_BUILDER_WITH_NNF, for every Mega builder;
  `build_constraints` is instantiated for MegaCircuitBuilder,
  MegaAppCircuitBuilder, MegaKernelCircuitBuilder and
  MegaHidingKernelCircuitBuilder and routes RecursiveAggregation through
  the same `create_recursion_constraints`. There is no Mega-specific
  predicate path.

  Checked on an Aztec 6.0.0 local network with client-side proving
  (EmbeddedWallet with proverEnabled; bb.js's bundled bb byte-identical to
  the pinned bb 6.0.0) and the node's proof verifier on (node log
  "Starting QueuedIVCVerifier with 8 concurrent verifiers", a "Chonk
  verification successful" line per transaction, and tampered Chonk
  proofs rejected with "Invalid proof"). The function run is
  `NullificationExecutor.consume` from `examples/nullification_proof`,
  built without the membership flag and the binding described below, so
  that an unknown leaf reaches the PXE's read-request check:

      case                                              simulate     Chonk prove / node
      no capsule                                        (0, false)   proved, verified, mined
      garbage vk and proof staged (vk_ok = 0)           (0, false)   proved, mined; nothing pushed
      pinned vk, garbage proof, a real leaf (ok = 1)    (1000, true) fails ("Deserialized point is not on the curve")
      pinned vk, a genuine owner proof for other
        public inputs, a real leaf (ok = 1)             (1000, true) fails ("Failed to verify the generated proof!")
      pinned vk, garbage proof, an unknown leaf         fails before proving, in the PXE's check of the
                                                        note-hash read request (the case the membership flag removes)
      the owner's real proof                            (1000, true) proved, mined, canonical nullifier pushed
      the same capsule again                            (0, false)   nothing pushed

  The Chonk pipeline honours the predicate exactly as the UltraHonk
  prover does. Scope: the honest bb prover's behaviour; soundness against
  a modified prover is Chonk's.

  Real proofs on a local network. A single `nodeAdmin_setConfig
  {realProofs: true}` on a running local network flips the reported flag
  but does not build the node's proof verifier: the node swaps in its
  bb-backed verifier only on a change of the flag, and only with
  BB_WORKING_DIRECTORY and BB_BINARY_PATH set. Start the network with
  both variables set, then set realProofs false and then true, and
  confirm "Starting QueuedIVCVerifier" in the node log (and a "Chonk
  verification successful" line per transaction). Without that, the node
  mines transactions whose proof has been replaced by random fields.

  Membership flag. `consume_with_nullification_proof_or` proves the
  leaf's path to the anchor block's note-hash-tree root in the circuit,
  as a flag folded into the predicate, instead of pushing a note-hash
  read request; an unknown leaf reads as ok = false. This adds no
  failure source under a false predicate (the path is a flag; its only
  assert is the 42-bit decomposition of the hinted index, which the empty
  witness satisfies).

  Optional binding. The owner circuit has two public inputs, executor
  and expiry (0 = unbound), and `consume` folds `executor_ok`
  (msg_sender) and `expiry_ok` (anchor block number) into the predicate
  as determined flags, adding no failure source. A binding that does not
  admit the call is a false predicate, so bb proves the call
  (`outer_check.py` "wrong executor" and "expired" prove with ok = 0).

  Cost of `consume` (`bb gates -s chonk`):

      build                                   ACIR opcodes   Chonk gates
      without membership flag and binding     -              21261 (RECURSIVE_AGGREGATION 11670)
      with the membership flag                2240           22540
      with membership flag and binding        2287           22675
      the same and the static-call term       2289           22676 (the example as shipped)

Not predicated (and not predicable):

- Entry-parameter range checks: unconditional RANGE opcodes on input
  witnesses, plus the ABI-level rejection (section 1).
- A top-level assert outside any if: plain `ASSERT w1 = 0`; fails for
  every value of unrelated branch flags.

## 4. Brillig (unconstrained) semantics

Trap sources, each checked with a hint called from main, where the
circuit's constraints (just the range on the hint's return) are
satisfiable; the abort is the Brillig VM's, not a constraint failure:

- division by zero: "Assertion failed: 'Attempted to divide by zero'"
- out-of-bounds index: "Assertion failed: Index out of bounds"
- integer overflow: "Assertion failed: attempt to add with overflow"
- assert inside an unconstrained fn: fails with its message.

A brillig call under a false predicate is skipped entirely (the
divide-by-zero body above does not trap when the call's predicate is 0),
outputs zeroed.

Casts inside unconstrained code truncate and never trap: (p-1) as u128
returns the canonical value mod 2^128, (p-1) as u8 returns 0, 300 as u8
returns 44: the same semantics as constrained casts, no range constraint
inside the brillig body.

Typed returns of unconstrained calls are constrained in ACIR: a u8 return
gets `RANGE w2, 8 bits` on the brillig output, a bool return gets a 1-bit
RANGE (seen both in the dedicated probes and on every
hinted carry/borrow in the core gadgets). Hint-satisfiable (honest hints
are in range by type).

Typed public outputs (`-> pub uN`): no extra range constraint is emitted on
the return witness; the circuit binds `w_ret = w_src` and the uN invariant
comes from the producing site (parameter range, overflow check, cast
truncation, or hint-return range). Nothing is constrained at the
output, so a pub uN output adds no failure source, and its well-typedness
is exactly as strong as the computation that produced it; on this
toolchain every producing op establishes it, so the invariant holds.

## 5. Core gadget verification (noir/total/src/core.nr against its doc comments)

The probe packages compile core.nr as a module so the pub(crate) gadgets
are callable. The gadgets checked are those listed below; core.nr has more,
each with its own argument in its doc comment. The library's own suite also
passes on this toolchain, including the wrong-hint should_fail tests (wrong
split, wrong/equal lt flag, wrong carry, wrong mul split, oversized
remainder).

- two_pow::<128>: compiles to a single `ASSERT w0 = 2^128`; the loop is
  constant-folded; no constraints, as claimed.
- is_zero / eq: ACIR is exactly the inversion gadget (section 1), total at
  0, 1, p-1. Hint-satisfiable for every input; flag determined. The flag
  is a defined witness (`z = 1 - d*inv`) and only d*z == 0 is constrained;
  booleanity is a consequence of the two equations, not a separate
  constraint (by contrast, hinted bools such as carry, borrow and the lt
  flag do get an explicit 1-bit range).
- select_field: one arithmetic definition (`w3 = w0*w1 - w0*w2 + w2`);
  total.
- limbs (std bn254::decompose): ACIR matches the claimed set exactly: one
  brillig decompose; RANGE 128 on both limbs; reconstruction
  `w3 = w0 - 2^128*w4`; hinted borrow (RANGE 1); and the two limb-compare
  ranges `RANGE(2^128*borrow + PLO - 1 - lo)` and `RANGE(PHI - hi -
  borrow)`, both 128 bits. Executes at 0, 1, 2^128-1, 2^128, p-1 all pass
  with the canonical limb values ((p-1) -> (PLO-1, PHI) confirmed).
  Satisfiability argument re-checked for all canonical (lo, hi): if
  PLO > lo the borrow 0 branch gives both ranges in [0, 2^128) when
  hi <= PHI; if PLO <= lo the borrow 1 branch needs hi < PHI, exactly the
  lexicographic order, which canonical limbs satisfy. Uniqueness (hence
  determinedness) holds: two in-range pairs below (PLO, PHI) reconstructing
  the same x would differ by a multiple of p while both represent integers
  below p.
- split_128_at::<64>: RANGE 64 + RANGE 64 + `w3 = w0 - 2^64*w4`, as
  claimed. Edge executes: 0, 2^64 pattern value, 2^128-1 pass with correct
  halves; the documented precondition is real: x = 2^128 fails (the hint
  truncates mod 2^128, reconstruction unsatisfiable), which is why it is
  pub(crate).
- fits_bits::<N>: ACIR = limbs set + split of the low limb at N + two
  inversion gadgets + flag product, as documented. Boundary executes: N=64
  at 2^64-1/2^64, N=1 at 1/2, N=127 at the 2^127 boundary, fits_128 at
  2^128-1/2^128, and p-1 (false): all total with the right flags.
- clamp_bits_or::<8>: fits set + `w1 = w0*ok` (select with f = 0); (255 ->
  255, true), (256 -> 0, false).
- lt_bounded::<64>: hinted bool (RANGE 1) and
  `ASSERT w4 = c*(2b - 2a - 1) + a - b` + RANGE 64, which is algebraically
  select(c, b-a-1, a-b) as documented. Executes: lt/gt/eq/adjacent-max all
  correct; precondition breach (a = 2^64) fails. The wrong-flag wrap
  argument re-checked: for a, b < 2^N the wrong c gives d in
  [p - 2^N, p - 1], far above 2^N for any N <= 252, so the documented
  N <= 128 bound (set by the hint's u128 compare) is conservative.
  Determined.
- add_split::<64>, ::<126>: hinted carry bool gets RANGE 1 (the compiler's
  booleanity on a bool hint return, present as the doc comment claims),
  lo defined as a + b - 2^N*carry, RANGE N on lo. maxmax edges at both
  widths give (2^N - 2, carry 1). The wrong-carry analysis holds (either
  branch wraps out of range).
- mul_split::<64>, ::<126>: RANGE N on lo and hi plus
  `ASSERT w4 = w0*w1 - 2^N*w5`. (2^64-1)^2 -> (1, 2^64-2) and (2^126-1)^2
  -> (1, 2^126-2) confirmed; 2^252 < p so no wrap at N = 126.
- div_split::<64>, ::<126>: exactly the four claimed constraints (two
  ranges, reconstruction, b1 - r - 1 range) and nothing else, notably no
  divisor-inversion constraint, which is what makes it total given the
  preconditions. Executes: (17,5), (2^64-1,1), (5,2^64-1), (2^126-1)/3 all
  correct. Precondition breaches both fail as documented: b1 = 0 aborts in
  the hint (a Brillig divide-by-zero trap; the doc comment's "trap-free
  under the caller's precondition" is load-bearing, and div_rem_or selects
  the divisor to 1 before the call); a = 2^64 fails the q range check.

Summary: the hint-satisfiability and determinedness arguments in the doc
comments hold for each gadget listed above on this toolchain, including the 0 / 1 /
2^N-1 / 2^N / p-1 / 2^128 edges, and the implemented constraint sets match
the documented ones exactly.
