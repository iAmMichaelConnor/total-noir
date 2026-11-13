# Totality of the ECDSA entries

`ecdsa_k1_verify` and `ecdsa_r1_verify` (and their `_fields` variants) call
barretenberg's ECDSA black boxes. A black box is total only if the backend
can prove every witness the solver produces, and bb's ECDSA gadgets cannot:
they contain assertions that fail for some inputs. This document states
what the library guarantees about that, proves it, and lists exactly what
the proof takes from bb's source and what it assumes.

Everything here is about **bb 6.0.0** (aztec-packages tag `v6.0.0`, commit
`0219f11d8133970df3974fe5ae65e006bf8c193a`) and nargo 1.0.0-rc.3's ACVM
solver. Soundness of the entries does not depend on bb's internals
(`noir/total/src/ecdsa/blind.nr`); totality does. On any bb change,
sections 3 to 7 must be redone ([CONTRIBUTING.md](../CONTRIBUTING.md),
"Bumping bb").

Labels: **[proved]** a complete argument is given here; **[computed]** a
finite computation, with the script that redoes it; **[source]** a fact
read from bb's source at the commit above (section 3); **[tested]** checked
by running bb (section 8), not proved; **[assumed]** an assumption, named
in section 2.

## 1. Statements

Notation. p is the base-field modulus, n the group order, G the generator,
N the circuit's native modulus (BN254's scalar field). An input is
(Q, r, s, z): key bytes, signature bytes, hash bytes. It is *admissible*
when Q is on the curve with coordinates below p and p - n <= r < n (on
secp256r1 also r != s and r + s != n as integers); the wrappers replace
every other input by a fixed valid one before anything else happens
(`ecdsa.nr`). s' is s mod n, or 1 when that is 0; u2 = r/s' mod n. A
*blind* is a residue beta != 0 mod n with beta G != +-Q; `blind.nr`'s
constraints accept exactly the hints that encode such a beta (as
beta == e b', section 4), and then call the black box on

    Q' = Q + beta G,   z' = z - r beta mod n,   so   u1 := z'/s' = (z - r beta)/s'.

Because r != 0 mod n, beta -> u1 is a bijection of Z_n: the prover can give
the black box any u1 it likes, and Q' = (R - u1 G)/u2 follows, where
R = (z/s') G + u2 Q does not depend on the blind. A blind is *good* when
bb's witness for the blinded call satisfies every constraint of the ECDSA
gadget, with the output the solver computed.

**T1 (a satisfying witness exists).** For every admissible input there is a
good blind. More precisely, the fraction of u1 in Z_n whose blind is not
good is

- secp256k1: at most 0.784 + eps_KDA,
- secp256r1: at most 2.9 * 10^-5 + eps_KDA,

where eps_KDA is the quantity assumption KDA (section 2) says is
negligible. For inadmissible inputs the wrappers run the black box on the
blinded fixed input, to which the same statement applies.

**T2 (the honest hint finds one).** The honest hint (`blind_hint.nr`)
derives candidates u1 from Poseidon2 of the inputs and a counter, and
returns the first whose blind passes its emulation of bb. Model Poseidon2
as a random oracle. Then for every admissible input the returned blind is
good except with probability at most

- secp256k1: 0.784^256 + 256 * 2^-127 + 256 * eps_KDA < 2^-90 + 256 * eps_KDA,
- secp256r1: (2.9 * 10^-5)^256 + 256 * (2^-127 + 2^-246 + eps_KDA),

provided the emulation computes the predicates of section 7 (EMU).

What the numbers mean in practice: on secp256k1 an input can be built for
which half of all blinds are bad (section 5.4; bb fails on the unblinded
call and on half of the blinded ones), so the hint needs retries, and 256
of them leave 2^-90 by the bound proved here (the true worst case is
about 0.57 per candidate, 2^-200 over 256). On honest inputs the first candidate is good
except with negligible probability.

## 2. Assumptions

- **KDA (key-dependent aliasing is negligible).** bb's non-equality check
  compares integers modulo N only (section 3, S2), so it fails for two
  x-coordinates that differ by k p + j N, j != 0. When both operands move
  with the blinded key, the number of keys for which this happens is a
  question about the curve that counting does not answer (section 5.5 says
  why). KDA: for every admissible input, the number of u1 in Z_n for which
  some check of section 5.5's list (secp256k1: the 64 ladder steps that add
  a multiple of Q', the seven table additions and the three closing
  additions of multiples of Q'; secp256r1: the table check, the 127 rounds
  and the two skew subtractions of the two-point multiplication) has
  aliasing operands that both depend on the key is at most eps_KDA * n, with
  eps_KDA negligible. Heuristically each check aliases for about
  2 * 30 / p of the keys, so eps_KDA is about 2^-240. bb's own completeness
  for honest inputs rests on the same heuristic at every incomplete
  addition of `biggroup`.
- **ROM.** Poseidon2 behaves as a random oracle for the candidate
  derivation (T2 only; T1 does not use it).
- **EMU.** `k1_emul.nr` and `r1_emul.nr` compute the predicates of section
  7. This is a statement about the library's own unconstrained code;
  it is [tested] (section 8), not proved. T1 does not use it. If it failed
  for some input, T2's bound would not apply to that input; soundness is
  unaffected.
- **bb as read.** bb 6.0.0 behaves as its source says (section 3) and its
  witness generation is the deterministic one in that source. The facts
  used are listed one by one; each is [source], and the ones that can be
  observed from outside are also [tested].
- Soundness (not the subject here) additionally assumes bb's ECDSA
  constraints are sound, as for any use of the black box.

No discrete-logarithm assumption is used. (bb's two secp256r1 offset
generators have unknown discrete logs, and an input that makes the
*unblinded* call fail can be built from them or found by solving for the
key; the blinded statements above are proved by counting.)

## 3. bb source facts

Paths are under `barretenberg/cpp/src/barretenberg/`.

- **S1 (verdict).** `stdlib/encryption/ecdsa/ecdsa_impl.hpp`,
  `ecdsa_verify_signature`: the output is the AND of: x(R) mod n == r mod n
  for R = u1 G + u2 Q; R is not infinity; the key is not (0, 0), has
  coordinates below p and is on the curve; r < n, r != 0 mod n;
  s < (n + 1)/2, s != 0 mod n; and on secp256r1 u2 not in {0, 1, -1}. s == 0
  mod n is replaced by 1 before the divisions u1 = z/s, u2 = r/s
  (`div_without_denominator_check`, no assertion). Every range and zero
  test is a flag (`is_less_than`, `operator==`), not an assertion.
  `dsl/acir_format/ecdsa_constraints.cpp`: the output wire is asserted
  equal to this value.
- **S2 (non-equality).** `stdlib/primitives/bigfield/bigfield_impl.hpp`,
  `assert_is_not_equal`: for operands with integer witness values a, b it
  asserts prod_{k = -R..L} (a - b - k p) != 0 modulo N, with L, R the
  operands' overload counts (how many multiples of p fit under their
  static maximum values). So it fails exactly when a - b == k p (mod N)
  for some k in [-R, L]: when a == b mod p, or when a - b = k p + j N with
  j != 0 ("aliasing"). `operator/` and `msub_div` with
  `enable_divisor_nz_check` apply the same check to a divisor against 0.
  Remainders of bigfield products are reduced witnesses in [0, p).
  `operator==` is exact (a hinted inverse or zero product).
- **S3 (secp256k1 multiplication).**
  `stdlib/primitives/biggroup/biggroup_secp256k1.hpp`,
  `secp256k1_ecdsa_mul(Q', u1, u2)`: endomorphism wNAFs of u1 (8-bit digits,
  staggers 2 and 3) and u2 (4-bit digits, staggers 0 and 1); tables for G
  (plookup, 8-bit) and Q' (`create_endo_pair_four_bit_table_plookup`:
  one `dbl`, seven complete `operator+`, x times beta); accumulator
  initialised to the table point of u2_lo's first digit; 16 rounds of
  `dbl`, `dbl`, and two `multiple_montgomery_ladder` calls adding, in
  order, the points of u2_hi, u2_lo, u1_hi, u1_lo, u2_hi, u2_lo digits;
  then `+=` (complete) of the fragments of u1_hi, u2_hi, u1_lo; then four
  `conditional_add` of the skew bases G, -lambda G, Q', -lambda Q', each of
  which evaluates the complete addition (base negated for a negative
  skew) and then selects.
- **S4 (ladder step).** `biggroup_impl.hpp`, `multiple_montgomery_ladder`:
  for accumulator A and each added point P, `assert_is_not_equal(x(A),
  x(P))`, then x(A + P), then `assert_is_not_equal(x(A), x(A + P))`, then
  A <- 2A + P; no other witness-dependent assertion (its divisions are
  `div_without_denominator_check` or `msub_div` without the zero check).
- **S5 (complete addition and doubling).** `biggroup_impl.hpp`,
  `add_internal` / `subtract_internal`: flags for equal x, equal y and
  infinite operands; the divisor is 1 when an operand is infinite or the
  sum is infinity, 2y in the doubling case, x2 - x1 otherwise, and is
  checked non-zero by `operator/`. `dbl_internal`: divisor 2y (1 for an
  infinite operand), checked by `msub_div`. The native `BB_ASSERT`s (y != 0)
  cannot fire for a finite point of a curve of odd order.
- **S6 (wNAF).** `biggroup_nafs.hpp`, `compute_secp256k1_endo_wnaf` and
  `compute_secp256k1_single_wnaf`; `ecc/groups/wnaf.hpp`, `fixed_wnaf`;
  `ecc/fields/field_declarations.hpp`, `split_into_endomorphism_scalars`
  (large-modulus path) and `compute_endomorphism_k2`. A half whose residue
  has 130 bits or more is negated; `BB_ASSERT_LT` then requires both
  magnitudes below 2^129; the digits, fragment and skews are witnesses;
  the scalar is asserted equal to (lo reconstruction) - lambda (hi
  reconstruction).
- **S7 (secp256r1 multiplication).** `biggroup_secp256r1.hpp`,
  `secp256r1_ecdsa_mul`: T1 = u1 G by `secp256r1_fixed_base_mul` (38
  looked-up points L_w = d_w 2^off(w) G + 2^w H_t for the windows d_w of u1
  of widths 7 x 19, 3, 7 x 17, 1; `chain_add_start` and 36 `chain_add`,
  each asserting distinct x and nothing else; then the complete
  subtraction of (2^38 - 1) H_t); T2 = u2 Q' as a hinted on-curve point (u2
  read as 2 when it is 0 or +-1) checked by `batch_mul({Q', -+T2}, {alpha,
  |beta|}, 128 bits, no edge cases)` being infinity, with (alpha, beta) the
  half-GCD pair of u2; the result is the complete T1 + T2. `batch_mul`
  here is: one `checked_unconditional_add_sub` on (Q', T2) for the table,
  `chain_add_start` of the offset generator H_o with the first table
  point, 127 ladder steps (S4), two complete skew subtractions, and the
  complete subtraction of 2^127 H_o. H_t ("biggroup table offset
  generator") and H_o ("biggroup offset generator") are different fixed
  points (`ecc/groups/precomputed_generators_secp256r1_impl.hpp`).
- **S8 (overload counts).** The values of k in S2, per kind of site
  (`scripts/gen_ecdsa_tables.py`, `ALIAS_K_*`; generated into
  `table_k1.nr` / `table_r1.nr`). They follow from the operands' static
  maximum values (`bigfield`'s bookkeeping through `operator-`,
  `operator+`, `conditional_assign` and the ROM tables' `limb_max`):
  - x(A) - x(P) and x(A) - x(A + P) in an incomplete addition (ladder
    steps, chain additions): k in {-1, 0, 1}.
  - the divisor x2 - x1 of a complete addition (integer difference of the
    reduced coordinates): k in {-2, ..., 1} when both are witnesses (table
    additions, the fragments of u1_hi and u2_hi, the Q' skew; secp256r1's
    final addition); {-2, ..., 2} when the accumulator's y carries a ROM
    table's maximum (the u1_lo fragment and the -lambda Q' skew); {-2, -1,
    0} when x2 is a constant (the G and -lambda G skews; secp256r1's offset
    subtraction).
  - the divisor 2y, as the integer 2y in (0, 2p): k in {0, 1, 2} for a
    doubling, {0, ..., 4} for the first doubling of round 0 (its operand
    is read from the ROM table); in the doubling branch of a complete
    addition {0, ..., 3}, {0, ..., 4}, {0, 1, 2} for the three kinds above.
  [tested] for secp256k1 at every kind of site a crafted input can reach
  (section 9); the doubling branches, the Q'-stream ladder steps after
  round 0, the u2_hi fragment and secp256r1's offset subtraction are
  [source] only.

The solver: `acvm-repo/blackbox_solver/src/ecdsa` at noir 5a7ee9b
(1.0.0-rc.3) returns true iff r, s in [1, n), s <= n/2, the key is valid,
R != infinity, x(R) < n and x(R) == r; it never aborts on 32-byte
coordinates. (noir 1.0.0 reduces x(R) mod n first; the two agree on
admissible inputs.)

## 4. What the constraints allow

[proved, in `blind.nr`'s header] For every hint C1-C5 accept there is
beta != 0 mod n with beta G != +-Q, Q' = Q + beta G (canonical bytes) and
z' = z - r beta mod n (below n); conversely every such beta has an accepted
hint: beta == e b' with e = +-1 and b' = o + D, o = sum 2 * 16^w,
0 <= D < 15 * 16^63 [computed: `scripts/ecdsa_totality_checks.py`, C5], and
the honest witnesses satisfy C2-C5 for any such (e, b').

**Blind-independent conditions** [proved from S1, S6, S7]. For an
admissible input and any blind:

1. The solver and bb compute the same output. Q' is a finite on-curve
   point with canonical coordinates; r is in [p - n, n) and s is the same
   in both calls; bb's x(R) == r mod n with x(R) < p and r >= p - n forces
   x(R) = r (r + n >= p), which is the solver's test; on secp256r1, with r
   in range, u2 in {0, +-1} means s is out of range (verdict false on both
   sides for another reason) or r = s or r + s = n, which are gated.
2. bb's wNAF assertions hold for every scalar. For every k in [0, n) the
   split gives 0 <= k_lo < 1.47 * 2^128 and -0.19 * 2^128 < k_hi < 1.09 * 2^128
   [computed: C1, from the exact formula k_hi = c2 b2 - c1 m,
   k_lo = k - c2 a2 - c1 b2 with c1 = floor(b2 k / 2^256),
   c2 = floor((m + 1) k / 2^256)], so the magnitude test passes. The
   reconstruction identity holds for every half: with v = |k| >> stagger
   and w = v + [v even], `fixed_wnaf` writes w in odd digits (each digit is
   the window plus the borrow it passes on; the top window absorbs the
   last borrow and stays below its width because an even value plus one
   does not carry), the fragment is (|k| mod 2^stagger) - 2^stagger [v
   even] + [fragment even], and the skew removes the last term; summing
   gives |k|, and negating all of them gives -|k|. Every digit, fragment
   and table index is in its table's range. k_lo - lambda k_hi == k by
   construction of k_lo.
3. On secp256r1, the half-GCD pair has 0 < alpha, |beta| < 2^128 and
   beta u2 == alpha, the NAFs reconstruct, T2 is a finite on-curve point,
   and x(Q') != x(T2) exactly (u2 != +-1 after the substitution).

So a blind is good iff none of the *blind-dependent* assertions fails:
the x-checks and divisor checks of the multiplication.

## 5. secp256k1: the bad set

Write the four digit streams as QL (base Q'), QH (base -lambda Q'), GH
(-lambda G), GL (G). Before a ladder step the accumulator is
A = alpha G + gamma Q' where alpha, gamma are fixed integer combinations
(with lambda) of the digits consumed so far, and R = M A + (rest), where
M is a power of two and the rest is the same kind of combination of the
digits still to come (including fragments and skews). "Prefix" and
"suffix" below mean the consumed and remaining digits of u1.

Two facts about short combinations [computed: C2]: if x - lambda y == 0
mod n with |x|, |y| <= 2^127 then x = y = 0. Hence a combination
x - lambda y of digits spanning fewer than 127 bits per half is 0 mod n
only if both integer parts vanish, and two such combinations are equal mod
n only if equal as pairs.

### 5.1 Exact collisions, non-dense [proved]

A ladder step fails exactly (S4, S2) iff A = P, A = -P or 2A + P = O: a
linear relation c_G + c_Q q' == 0 mod n in q' = dlog Q', where (c_G, c_Q)
are the G- and Q'-coefficients of A -+ P or 2A + P.

- *Parity.* Each step doubles the accumulator before adding, and
  consecutive steps add to different streams, so in A the coefficient of
  the stream being added is even while the added digit is odd: the
  relation's coefficient in that stream is odd, in particular non-zero.
- *Rounds 0 to 7 (prefix form).* All coefficients span fewer than 76 bits.
  If P is a multiple of Q', c_Q != 0 mod n by parity; if P is a multiple
  of G, c_G != 0 mod n by parity, and c_Q is gamma (or 2 gamma), non-zero
  because the QL stream is never empty. Either way each prefix value
  allows at most one q'. At most 2^128 prefix values per step.
- *Rounds 8 to 15 (suffix form).* Substituting the relation into R gives
  R = rho G + tau Q' with rho, tau combinations of the suffix (and of P's
  digit). If tau != 0 mod n, each suffix value allows at most one q'; at
  most 2^143 suffix values. If tau == 0 mod n the relation is *dense*
  (5.2).

Since q' determines u1 (u1 = dlog R - u2 q'), at most 288 * 2^143 < 2^152
values of u1 fail a non-dense relation. (bb's native assertion in
`msub_div` fires in the same exact cases and adds none.)

### 5.2 Exact collisions, dense [proved + computed]

For a relation with tau == 0 the condition reads dlog R == rho mod n, where
rho = rho_lo - lambda rho_hi is built from the suffix of u1's two halves
and is short (rounds 8 to 15: under 2^78), so the pair (rho_lo, rho_hi) is
determined by R. A half x with E unconsumed low bits is x = 2^E X + t with
X odd and t in [-2^E, 2^E) the suffix value, so t determines x mod
2^(E+1) and conversely; when the relation involves the current digit d of
that half (coefficient -1 or 3 times 2^E), d and t are both determined by
rho, because d is odd. So the u1 satisfying one dense relation lie in one
residue class of (k_lo mod 2^i, k_hi mod 2^j), with i + j the number of
pinned bits: at least 7 (the last two steps of the last round, and the
"2A + P = O" case of the step before them), 15, 23, and 16 more per
earlier round.

The split is injective and its image lies in a hexagon of area 1.374 n
[computed: C1], so one residue class holds at most 1.374 n / 2^(i+j)
(1 + 2^-100) scalars (the cells attached to the class's points are
disjoint and inside the hexagon enlarged by one cell). Summing over all
144 relations of rounds 8 to 15 as if every one were dense: at most
**0.0753 n** [computed: C3].

This replaces the earlier "7.1 % assuming near-uniform low digits"
estimate: no uniformity over the blinds is needed because u1 itself is
the free variable, and the bound is over all of Z_n.

### 5.3 Aliasing where one operand does not move with the key [proved]

Take an aliasing condition (S2) at a site where, for a fixed prefix (or
suffix) value, one operand is a fixed point and the other determines q':

- a ladder step adding a multiple of G (rounds 0 to 7, or tau != 0): the
  accumulator must be one of at most 2 |K| points (check 1: x(A) = x(P) +
  delta) or at most 6 |K| points (check 2: x(A) - x(A + P) = delta is a
  polynomial condition of degree 6 in x(A));
- a doubling: 2y(A) takes one of |K| values, at most 3 points each;
- a ladder step adding a multiple of Q' when the accumulator does not
  depend on Q' (tau == 0): x(P) or x(A + P) is pinned to 2 |K| values;
- the closing additions, likewise.

Each (prefix or suffix value, site) then excludes a bounded number of
keys, at most 2^160 values of u1 in total, unless the accumulator is
independent of the key *and* the other operand is too: 5.4.

### 5.4 Aliasing at key-independent sites [proved + computed]

At a site whose operands depend only on R and a suffix of u1 (the
remaining u2-digits cancel, tau == 0, and the added point is a multiple of
G or absent), the condition picks out suffix values, each a residue class
as in 5.2. These are the analogue of the dense exact class, and they are
what made the previous wrapper fail: for R with x(R) = x(-lambda G) + N
and u2 with odd halves, bb's skew addition of -lambda G divides by 0 mod
N for every u1 whose high half is odd.

- *Small sites*: the skew additions of G and -lambda G, the fragment
  additions of u1_lo and u1_hi, and ladder step (15, 3) (suffixes of 1, 2,
  4, 7 and 15 bits). Call a *comparison* an accumulator point together
  with the x-coordinate it is compared with (for check 2 of the ladder
  step, the unordered pair {A, A + P}). [computed:
  `scripts/ecdsa_alias_multiplicity.py`, C6, with the superset |k| <= 6 of
  S8] Over all suffix values of these sites and all aliasing values (6.7
  million (R, site, suffix) triples), no final point R fails two different
  comparisons. One comparison can be reached under several suffix values,
  all found by the search and all structural: suffixes with the same
  signed tails (one residue class of the halves); a ladder digit d and
  -d in check 2 (two classes of 15 bits); and the same accumulator and
  base at a skew addition and at the fragment addition before it (the
  -lambda G skew's one-bit class of k_hi together with one class of 3 + 4
  bits at the u1_hi fragment; the G skew's class of 1 + 1 bits together
  with one of 3 + 1 bits at the u1_lo fragment). So the scalars u1 that
  are bad at these sites for a given R have density at most
  1.374 (1/2 + 1/128) = **0.698**.
- *Other sites* (step (15, 2), the G-steps of rounds 8 to 14, the
  doublings of rounds 8 to 15): at most 256 * 8 |K| suffix values (resp.
  3 |K| points) can fail per site, each a class of 23 or more pinned bits:
  at most **0.0102 n** in total [computed: C4].

### 5.5 Aliasing where both operands move with the key [assumed: KDA]

Left: ladder steps adding a multiple of Q' with tau != 0 (or in rounds 0
to 7), the seven table additions, and the closing additions of multiples
of Q' when the accumulator still depends on Q'. The condition is
x(a G + gamma T) - x(delta T) = c for the key T. Its solutions are the
intersection of the curve {x(S1) - x(S2) = c} with a translate of the
graph of an endomorphism relation between S1 and S2, bounded by
2 (N(m1) + N(m2)) for the norms of the smallest endomorphisms with
m1 gamma == m2 delta. For early and late steps (and for the table) that
is small and a proof by counting goes through; around the middle of the
ladder the norms are about 2^129 while a prefix class has about 2^134
members, and the bound exceeds the class by a factor of about 2^3. We do
not know a proof there, so the whole family is covered by KDA rather than
split.

### 5.6 Total

Bad u1 for secp256k1: at most 0.0753 n (5.2) + 0.698 n + 0.0102 n (5.4)
+ 2^161 (5.1, 5.3) + 3 (beta = 0, +-dlog Q) + eps_KDA n
< **0.784 n + eps_KDA n** [computed: C4]. This is T1 for secp256k1.

## 6. secp256r1: the bad set

- *Fixed-base chain* (S7) [proved + computed]. Site i (i = 1..37) compares
  x(L_i) with x(S_(i-1)), both functions of u1 mod 2^off(i+1) only. Exact:
  S_(i-1) = +-L_i pins u1 mod 2^off(i+1) to at most 2 residues (they are
  the two that would give the discrete log of H_t), 3 values at i = 37.
  Aliasing: for each digit and aliasing value at most 2 accumulators, so
  at most 2 |K| 2^7 residues. Sites 1 and 2 are checked exhaustively (no
  21-bit prefix fails: C4); from site 3 on the residue classes sum to at
  most **2.9 * 10^-5 n**. This set does not depend on the input.
- *Offset subtraction and final addition* [proved]. raw = u1 G + const and
  x(const) - x(raw) aliasing: at most 2 |K| values of u1. T1 + T2 with
  T2 = R - T1 (or +-2 (R - T1)/u2-type relations when u2 was substituted):
  x(T2) - x(T1) = c is a non-constant function of T1 of degree at most 10,
  so at most 10 |K| values; the doubling branch needs T1 = T2, one value.
- *Two-point multiplication* [proved for exact]. Every x-check compares
  2^k H_o + c Q' with d Q' or with their sum: c' q' == c'' h_o with
  c' != 0 or no solution; at most 2 + 3 * 127 = 383 keys.
  Aliasing there: both operands move with the key [assumed: KDA].

Bad u1: at most 2.9 * 10^-5 n + 2^10 + eps_KDA n. This is T1 for secp256r1.
The sentence this replaces ("each assertion excludes at most one blinded
key") was wrong for the chain: its sites exclude residue classes of u1.

## 7. The hint (T2)

Candidate t is u1 = v_t mod n for a 256-bit oracle output v_t (each residue
has probability at most 2/2^256 < (1 + 2^-127)/n); the
blind is beta = (z - s' u1)/r. The hint rejects the candidate if beta = 0,
if x(beta G) = x(Q), or if its emulation says bb fails:

- secp256k1 (`k1_emul.nr`, `k1_bad`): every blind-dependent assertion of
  S3 to S5, exact and aliasing, with S8's values. So an accepted candidate
  is good (given EMU), and all 256 are rejected with probability at most
  (0.784 + eps_KDA)^256 plus the sampling bias.
- secp256r1 (`r1_emul.nr`, `r1_bad`): the fixed-base chain, the offset
  subtraction and the final addition, exact and aliasing. Not the
  two-point multiplication: an accepted candidate can still fail there,
  with probability at most 383 * 2 / n + eps_KDA per candidate (section 6).

The bounds of T2 follow by a union over the at most 256 candidates. An
adversary who grinds inputs gains nothing beyond the number of oracle
queries it makes, each of which meets these bounds.

## 8. Mechanical checks

- `scripts/ecdsa_totality_checks.py`: C1 to C5 (seconds).
- `scripts/ecdsa_alias_multiplicity.py`: C6 (minutes, many cores).
- `scripts/ecdsa_bb_model.py`: a Python model of S1 to S8 on real points.
- `scripts/ecdsa_differential.py`: for random and crafted inputs on both
  curves (exact collisions at random ladder steps, aliasing at ladder and
  closing sites, short final points, collisions with secp256r1's offset
  generator, aliasing in its final addition, and the out-of-range and
  boundary signatures) it checks, in both directions, that the model
  predicts `bb prove` on the raw black box, that the Noir emulation equals
  the model, and that the shipped entries prove with the documented
  verdict. Results of the run made for this version are in section 9.
- `noir/total_ecdsa_prove_check/run.sh` (CI): a fixed sample of the same
  classes through the shipped entries.
- `noir/total/src/ecdsa/blind_tests.nr`: the emulation on inputs with known
  bb outcomes; every hint field altered is rejected.

S8 was obtained by reading bigfield's maximum-value bookkeeping and by
probing bb with inputs whose difference at a chosen site is exactly
k p + j N for each k (section 9).

## 9. Results for this version

nargo 1.0.0-rc.3, bb 6.0.0.

**Overload counts (S8).** 1438 crafted secp256k1 inputs, each with the
integer difference at one chosen site equal to k p + j N for a k in
-8..8 (two per k and site kind, plus controls one or two off), every
other site clean: bb fails exactly for the k of S8 at every site kind
that can be reached (all four operand shapes of both ladder checks; the
doublings; table additions 1, 2, 4, 7; the u1_hi and u1_lo fragment
additions; all four skew additions), 152 failures and 1286 proofs, no
disagreement with the source-derived sets. These inputs are the `extra`
rows below.

**Multiplicity (C6).** `scripts/ecdsa_alias_multiplicity.py --kmax 6`:
6,668,388 (R, site, suffix) triples from 49,856 accumulator points; no
64-bit hash match that is not an exact point match; no R failing two
different comparisons; the only repeated comparisons are the structural
ones listed in 5.4.

**Differential.** `scripts/ecdsa_differential.py --random 1500 --crafted
600 --seed 20261112 --extra <the 1438 inputs>`:

```
curve category                 cases model-bad raw-bb-fail emu-bad shipped-ok
k1    alias-closing              141         0           0       0        141
k1    alias-ladder               137       137         137     137        137
k1    alias-ladder-control        97         0           0       0         97
k1    edge-high-s                  1         0           0       0          1
k1    edge-r=0                     1         0           0       0          1
k1    edge-r=2^256-1               1         0           0       0          1
k1    edge-r=n                     1         0           0       0          1
k1    edge-r=n+1                   1         0           0       0          1
k1    edge-r=n,s=1                 1         0           0       0          1
k1    edge-r=n,z=0                 1         0           0       0          1
k1    edge-r=p-n-1                 1         0           0       0          1
k1    edge-s=0                     1         0           0       0          1
k1    edge-s=n                     1         0           0       0          1
k1    edge-valid                   1         0           0       0          1
k1    exact-eq                   171       171         171     171        171
k1    exact-neg                  211       211         211     211        211
k1    exact-ret                  203       203         203     203        203
k1    extra:cases               1438       152         152     152       1438
k1    random                    1500         0           0       0       1500
k1    short-R                    600         0           0       0        600
r1    alias-final                163        90          90      90        163
r1    alias-final-control        113         0           0       0        113
r1    edge-high-s                  1         0           0       0          1
r1    edge-r=0                     1         0           0       0          1
r1    edge-r=2^256-1               1         0           0       0          1
r1    edge-r=n                     1         0           0       0          1
r1    edge-r=n+1                   1         0           0       0          1
r1    edge-r=n,s=1                 1         0           0       0          1
r1    edge-r=n,z=0                 1         0           0       0          1
r1    edge-r=p-n-1                 1         0           0       0          1
r1    edge-s=0                     1         0           0       0          1
r1    edge-s=n                     1         0           0       0          1
r1    edge-valid                   1         0           0       0          1
r1    exact-msm-eq               198       198         198       0        198
r1    exact-msm-neg              194       194         194       0        194
r1    exact-msm-ret              207       207         207       0        207
r1    random                    1500         0           0       0       1500
raw calls: 6873; model bad and bb fails: 1563; model good and bb proves: 5310; mismatches: 0
emulation vs model mismatches: 0
shipped entries: 6895 runs, 6895 proved with the expected verdict
```

Columns: inputs; of those, how many the model predicts bb cannot prove on
the raw black box; how many `bb prove` did fail; how many the Noir
emulation flags (on secp256r1 it does not follow the two-point
multiplication, hence 0 on the `exact-msm` rows, where the shipped entry
still proves because the blinded key leaves the relation); how many the
shipped entry proved and verified with the documented verdict. Two
generators produced no failing input in this run and so test only the
"proves" direction: `alias-closing` (the closing sites are covered by the
`extra` rows instead) and `short-R` (the dense exact class is covered by
`noir/total_ecdsa_prove_check`'s `Prover_short_r*` inputs and
`blind_tests.nr`'s vectors).

**Not tested by running bb**: an exact collision or aliasing inside
secp256r1's fixed-base chain or offset subtraction (finding one needs a
discrete logarithm or about 2^240 work), aliasing where both operands
depend on the key beyond round 0, and the doubling branch of a complete
addition.

**Gates** (bb 6.0.0 circuit size; before the change in parentheses):
`ecdsa_k1_verify` 62,769 (63,426), `ecdsa_r1_verify` 65,925 (66,582),
`ecdsa_k1_verify_fields` 69,889 (70,546), `ecdsa_r1_verify_fields` 73,045
(73,702).
