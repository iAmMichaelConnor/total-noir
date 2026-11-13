//! Shared constraint gadgets. Every group module builds on these instead
//! of re-deriving limb tricks.
//!
//! Classification vocabulary used in doc comments across this library:
//! - input-falsifiable: whether the constraint holds depends only on the
//!   circuit inputs. A total circuit emits none.
//! - hint-satisfiable: the constraint restricts a prover-chosen witness
//!   (an unconstrained function's output), and for every input the
//!   honest hint satisfies it.
//! - determined: every satisfying witness gives the flag the same value,
//!   so a dishonest prover cannot flip it.
//!
//! The compiler range-constrains integer-typed values returned from
//! unconstrained functions (bool gets a booleanity constraint). Those
//! constraints are hint-satisfiable: the honest hint is in range by
//! construction. Hint bodies below cannot trap under their stated
//! preconditions: casts truncate, no arithmetic can overflow, and no
//! divisor can be zero. Each hint's comment states what it needs.
//!
//! Hints and co-noir. Every hint in this library also runs in co-noir's
//! MPC Brillig VM, which extends the witness of secret-shared inputs. The
//! hints use Field arithmetic and comparison, to_le_bits/to_be_bits,
//! casts, u128 comparison, u128 division by a nonzero value, and
//! remainder and division by a constant: no integer And, Or, Xor, Shl or
//! Shr, no ConditionalMov, no integer remainder by a variable, no black
//! box, and no branch on a value derived from the inputs. The one
//! exception is arith::sqrt_or (and sqrt_canonical_or, built on it),
//! whose Tonelli-Shanks hint branches on such values: those two entries
//! are not co-noir-compatible. Separately, hash::sha256_var_or,
//! hash::keccak256_var_or and the ecdsa entries reach third-party hints
//! or black boxes co-noir cannot run (docs/co-noir.md).
//! `total-lint <artifact> --brillig-ops` lists any opcode a compiled
//! circuit holds that the VM cannot run.
//!
//! Width caps. lt_bounded, add_split and sub_split take N <= 128: their
//! wrap argument needs only p - 2^N >= 2^N, so the cap is not a soundness
//! bound; it is the widest native integer, and lt_bounded's and
//! sub_split's hint compares as u128. split_at takes N + K <= 128, the
//! limit of its u128 hint. mul_split and div_split take N <= 126, and that
//! cap is load-bearing for soundness: the field identity must not reach p
//! (2N <= 252). mul_split_short takes N <= 127 for products known to be
//! below 2^(2N - 1), with a high part one bit narrower (2N - 1 <= 253).
//! The multiply-divide gadgets state their own bounds.
//!
//! Compile-time branches. Several gadgets branch on a numeric generic
//! (`if N == 128`). Only the taken arm reaches the circuit and a
//! static_assert in the other arm does not fire, but nargo still checks
//! that arm's generic arithmetic, so a width that would go negative
//! there is written `N % 128`. The tests at the boundary widths
//! (range fits_u128, convert truncate_or::<128>, mul_div_split::<64, 128>,
//! mul_div_wide_to_or at M = 127, 128, 135) pin each dispatch.

use std::field::bn254;
use std::static_assert;

pub global TWO_POW_64: Field = 0x10000000000000000;
pub global TWO_POW_128: Field = 0x100000000000000000000000000000000;
/// 2^128 - 1, the largest u128.
pub global U128_MAX_FIELD: Field = 0xffffffffffffffffffffffffffffffff;

/// 2^N as a Field constant. The loop multiplies constants, so the
/// compiler folds it; no constraints are emitted.
pub fn two_pow<let N: u32>() -> Field {
    static_assert(N <= 253, "two_pow: N must be in 0..=253");
    let mut r: Field = 1;
    for _ in 0..N {
        r = r * 2;
    }
    r
}

/// Total equality-with-zero flag. Noir Field equality lowers to the
/// inversion gadget: a hinted inverse inv, the defined witness
/// z = 1 - x*inv, and the constraint x*z == 0 (z's booleanity is
/// implied by these equations, not emitted). Hint-satisfiable for
/// every x (x = 0: inv = 0, z = 1; else inv = 1/x, z = 0) and
/// determined in both directions.
pub fn is_zero(x: Field) -> bool {
    x == 0
}

/// Total equality flag; same gadget as is_zero on the difference.
pub(crate) fn eq(a: Field, b: Field) -> bool {
    a == b
}

/// Total selection: c*(t - f) + f. Pure arithmetic, no failure source.
pub fn select_field(c: bool, t: Field, f: Field) -> Field {
    (c as Field) * (t - f) + f
}

/// Range-check v to N bits where earlier constraints already bound v
/// below 2^N for every satisfying witness; returns v. It never adds a
/// failure source (whenever the earlier constraints hold, so does this),
/// and it makes a following `as uN` exact: the truncation is the identity
/// on a value below 2^N, and the compiler emits no constraint for it once
/// the value carries the N-bit range check, where a bare `as uN` on a
/// Field emits a 254-bit truncation. Each caller states the bound it
/// relies on.
pub(crate) fn implied_range<let N: u32>(v: Field) -> Field {
    v.assert_max_bit_size::<N>();
    v
}

/// Canonical 128-bit limb split of any Field element: x = lo + 2^128*hi
/// with (lo, hi) the limbs of the canonical integer representative.
/// Wraps std::field::bn254::decompose. Constraints (all hint-satisfiable
/// for every x, including x = p - 1): 128-bit ranges on the two hinted
/// limbs; the reconstruction equation; and a limb comparison against the
/// modulus limbs built from a hinted borrow bit and two more 128-bit
/// ranges. Canonical limbs exist and are unique for every x, so flags
/// built on them are determined.
pub fn limbs(x: Field) -> (Field, Field) {
    bn254::decompose(x)
}

/// Hint for split_at and split_128_at: (xi mod 2^N, xi / 2^N) for xi
/// the low 128 bits of x (the cast truncates). Remainder and quotient by
/// the constant 2^N. Trap-free for 1 <= N <= 127: the divisor is the
/// nonzero constant 2^N < 2^128, and neither result can overflow.
unconstrained fn hint_split_128_at<let N: u32>(x: Field) -> (Field, Field) {
    let xi = x as u128;
    let p = two_pow::<N>() as u128;
    ((xi % p) as Field, (xi / p) as Field)
}

/// Constraint half of split_at, split out so tests can feed wrong hints.
/// Emits: RANGE lo to N bits, RANGE hi to K bits, and x == lo + hi*2^N.
/// The right-hand side is below 2^(N+K) <= 2^128, so the equation cannot
/// wrap mod p; the split exists and is unique for every x < 2^(N+K), so
/// the constraints are hint-satisfiable under that precondition and the
/// outputs are determined.
pub(crate) fn constrain_split_at<let N: u32, let K: u32>(x: Field, lo: Field, hi: Field) {
    lo.assert_max_bit_size::<N>();
    hi.assert_max_bit_size::<K>();
    assert(x == lo + hi * two_pow::<N>());
}

/// Split a value already constrained below 2^(N+K) at bit N, for N, K >= 1
/// and N + K <= 128: returns (x mod 2^N, x >> N), with x >> N below 2^K.
/// PRECONDITION: x < 2^(N+K) has been constrained by the caller; without
/// it the reconstruction is input-falsifiable, which is why this is
/// pub(crate). A caller that knows a tighter bound than 2^128 passes the
/// smaller K and pays a narrower range check on the high part.
pub(crate) fn split_at<let N: u32, let K: u32>(x: Field) -> (Field, Field) {
    static_assert(
        (N >= 1) & (K >= 1) & (N + K <= 128),
        "split_at: need N, K >= 1, N + K <= 128",
    );
    // Safety: constrain_split_at range-checks both halves and checks the
    // reconstruction, which determines them uniquely.
    let (lo, hi) = unsafe { hint_split_128_at::<N>(x) };
    constrain_split_at::<N, K>(x, lo, hi);
    (lo, hi)
}

/// constrain_split_at with K = 128 - N.
pub(crate) fn constrain_split_128_at<let N: u32>(x: Field, lo: Field, rest: Field) {
    constrain_split_at::<N, 128 - N>(x, lo, rest);
}

/// Split a value already constrained below 2^128 at bit N (1..=127):
/// split_at::<N, 128 - N>. PRECONDITION: x < 2^128; pub(crate).
pub(crate) fn split_128_at<let N: u32>(x: Field) -> (Field, Field) {
    static_assert((N >= 1) & (N <= 127), "split_128_at: N must be in 1..=127");
    split_at::<N, 128 - N>(x)
}

/// Total range flag for 1 <= N <= 127: true iff the canonical integer
/// value of x is below 2^N. Emits only the limbs() constraint set, one
/// split of the low limb, and two is_zero gadgets: hint-satisfiable for
/// every Field element, determined. This is the flag counterpart of
/// assert_max_bit_size and of the implicit range check on integer-typed
/// entry-point parameters. For N = 128 use fits_128, above it
/// fits_bits_wide. The public surface is range::fits_bits and
/// range::clamp_bits_or.
pub(crate) fn fits_bits<let N: u32>(x: Field) -> bool {
    static_assert(
        (N >= 1) & (N <= 127),
        "fits_bits: N out of range; use fits_128",
    );
    let (lo, hi) = limbs(x);
    let (_, rest) = split_128_at::<N>(lo);
    is_zero(hi) & is_zero(rest)
}

/// Total range flag for 128 bits: true iff x's canonical value < 2^128.
pub(crate) fn fits_128(x: Field) -> bool {
    let (_, hi) = limbs(x);
    is_zero(hi)
}

/// Total range flag for 129 <= 128 + K <= 253: true iff the canonical
/// integer value of x is below 2^(128 + K), 1 <= K <= 125. With
/// x = lo + 2^128*hi and lo < 2^128, x < 2^(128 + K) iff hi < 2^K, so the
/// condition is on the high limb alone. Emits the limbs() constraint set,
/// split_128_at::<K> on hi (RANGE K and RANGE 128 - K on the hinted parts
/// and hi == low + rest*2^K; its precondition hi < 2^128 is the limbs
/// RANGE), and is_zero(rest). Hint-satisfiable for every Field; rest is
/// the integer hi >> K, unique, so the flag is determined. K <= 125
/// because hi <= PHI < 2^126: at K = 126 the flag would be the constant
/// true. The public surface is range::fits_bits and range::clamp_bits_or.
pub(crate) fn fits_bits_wide<let K: u32>(x: Field) -> bool {
    static_assert(
        (K >= 1) & (K <= 125),
        "fits_bits_wide: K must be in 1..=125 (width 129..=253)",
    );
    let (_, hi) = limbs(x);
    let (_, rest) = split_128_at::<K>(hi);
    is_zero(rest)
}

/// (value, ok): value is x when x < 2^N, else 0, so the result always
/// satisfies the N-bit invariant. Total; ok is determined.
pub(crate) fn clamp_bits_or<let N: u32>(x: Field) -> (Field, bool) {
    let ok = fits_bits::<N>(x);
    (select_field(ok, x, 0), ok)
}

/// 128-bit variant of clamp_bits_or.
pub(crate) fn clamp_128_or(x: Field) -> (Field, bool) {
    let ok = fits_128(x);
    (select_field(ok, x, 0), ok)
}

/// Hint for low_bit: (lo mod 2, lo >> 1) for the low 128 bits of lo, the
/// bit as a bool. hint_split_128_at::<1> (trap-free) and a Field
/// comparison with 0.
unconstrained fn hint_low_bit(lo: Field) -> (bool, Field) {
    let (bit, rest) = hint_split_128_at::<1>(lo);
    (bit != 0, rest)
}

/// Constraint half of low_bit, split out so tests can feed wrong hints:
/// RANGE rest to 127 bits and lo == bit + 2*rest (bit's booleanity is the
/// bool type; on a hint return it is the compiler's booleanity
/// constraint). The right side is below 2^128 < p, so the equation is an
/// integer one: for lo < 2^128 the pair exists and is unique.
pub(crate) fn constrain_low_bit(lo: Field, bit: bool, rest: Field) {
    rest.assert_max_bit_size::<127>();
    assert(lo == (bit as Field) + 2 * rest);
}

/// The low bit of a value already constrained below 2^128, as a bool.
/// PRECONDITION: lo < 2^128 (for example a limb from limbs()); without it
/// the reconstruction is input-falsifiable, which is why this is
/// pub(crate). Same constraints as split_128_at::<1>, with the bit typed
/// bool so that no comparison is needed to use it as a flag.
pub(crate) fn low_bit(lo: Field) -> bool {
    // Safety: constrain_low_bit range-checks the upper part and checks the
    // reconstruction, which determines the bit.
    let (bit, rest) = unsafe { hint_low_bit(lo) };
    constrain_low_bit(lo, bit, rest);
    bit
}

/// Hint for lt_bounded and sub_split: a < b on the low 128 bits. Trap-free:
/// casts truncate; a u128 compare cannot trap. Exact for a, b < 2^128.
unconstrained fn hint_lt(a: Field, b: Field) -> bool {
    (a as u128) < (b as u128)
}

/// Constraint half of lt_bounded: d = c ? b - a - 1 : a - b must fit N
/// bits. Given a, b < 2^N, the true choice of c gives 0 <= d < 2^N, and
/// the wrong one gives d = -k mod p = p - k for some 1 <= k <= 2^N, which
/// is at least p - 2^N >= 2^N for every N <= 252. So exactly one c
/// passes: c is determined, and the honest hint satisfies the range
/// check.
pub(crate) fn constrain_lt_bounded<let N: u32>(a: Field, b: Field, c: bool) {
    let d = select_field(c, b - a - 1, a - b);
    d.assert_max_bit_size::<N>();
}

/// Less-than flag for values already constrained below 2^N (N <= 128;
/// the cap is the hint's u128 compare, the constraint holds to 252).
/// PRECONDITION: a < 2^N and b < 2^N constrained by the caller; without
/// it the range check is input-falsifiable, which is why this is
/// pub(crate). Callers expose it only behind clamps.
pub(crate) fn lt_bounded<let N: u32>(a: Field, b: Field) -> bool {
    static_assert((N >= 1) & (N <= 128), "lt_bounded: N must be in 1..=128");
    // Safety: constrain_lt_bounded forces c to the true comparison via
    // the N-bit range check on d.
    let c = unsafe { hint_lt(a, b) };
    constrain_lt_bounded::<N>(a, b, c);
    c
}

/// Biased form of an N-bit two's complement pattern: u = pattern XOR
/// 2^(N-1), so that signed order on patterns is unsigned order on u. XOR
/// with 2^(N-1) is its own inverse, so the same map takes u back to the
/// pattern. PRECONDITION: pattern < 2^N (the type invariant when pattern
/// is `(x as uN) as Field` for x: iN); 2 <= N <= 128. pub(crate).
///
/// Constraints: one lt_bounded::<N>(pattern, 2^(N-1)) (the sign test; its
/// precondition holds because both sides are below 2^N) and select
/// arithmetic. Hint-satisfiable under the precondition; u is determined
/// because the sign flag is, and u < 2^N.
pub(crate) fn bias<let N: u32>(pattern: Field) -> Field {
    static_assert((N >= 2) & (N <= 128), "bias: N must be in 2..=128");
    let half = two_pow::<N - 1>();
    let nonneg = lt_bounded::<N>(pattern, half);
    select_field(nonneg, pattern + half, pattern - half)
}

/// Hint for add_split: whether a + b reaches 2^N, compared in the field.
/// Field addition and comparison only, so it is trap-free for every
/// argument; under the precondition (a, b < 2^N) the Field sum is the
/// integer sum and the answer is the true carry.
unconstrained fn hint_carry<let N: u32>(a: Field, b: Field) -> bool {
    !(a + b).lt(two_pow::<N>())
}

/// Constraint half of add_split: lo = a + b - carry*2^N must fit N bits.
/// Given a, b < 2^N the sum is below 2^(N+1): the true carry gives
/// 0 <= lo < 2^N, and the wrong one gives lo >= 2^N or lo = p - k with
/// 1 <= k <= 2^N, at least p - 2^N >= 2^N (N <= 252). So exactly one
/// carry value works: carry is determined and the honest hint satisfies
/// the check.
/// The booleanity of carry is the compiler's type constraint on the
/// hint's return (hint-satisfiable).
pub(crate) fn constrain_add_split<let N: u32>(a: Field, b: Field, carry: bool) -> Field {
    let lo = a + b - (carry as Field) * two_pow::<N>();
    lo.assert_max_bit_size::<N>();
    lo
}

/// (a + b) mod 2^N and the carry bit, for a, b already constrained
/// below 2^N (1 <= N <= 128). PRECONDITION as for lt_bounded; pub(crate).
pub(crate) fn add_split<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "add_split: N must be in 1..=128");
    // Safety: constrain_add_split range-checks the low part, which
    // determines the carry uniquely.
    let carry = unsafe { hint_carry::<N>(a, b) };
    let lo = constrain_add_split::<N>(a, b, carry);
    (lo, carry)
}

/// Constraint half of sub_split: diff = a - b + borrow*2^N must fit N
/// bits. Given a, b < 2^N, a - b lies in (-2^N, 2^N): with borrow = 0
/// diff fits iff a >= b (if a < b it wraps to at least p - 2^N + 1, far
/// above 2^N), and with borrow = 1 diff fits iff a < b (if a >= b it is
/// at least 2^N). Exactly one borrow works, so borrow is determined and
/// the honest hint satisfies the range check. The booleanity of borrow is
/// the compiler's type constraint on the hint's bool return
/// (hint-satisfiable).
pub(crate) fn constrain_sub_split<let N: u32>(a: Field, b: Field, borrow: bool) -> Field {
    let diff = a - b + (borrow as Field) * two_pow::<N>();
    diff.assert_max_bit_size::<N>();
    diff
}

/// (a - b) mod 2^N and the borrow flag (true iff a < b), for a, b
/// already constrained below 2^N (1 <= N <= 128). PRECONDITION as for
/// lt_bounded; pub(crate). One N-bit range check, the same cost as
/// lt_bounded, and the difference itself is the range-checked value, so
/// it can be cast exactly.
pub(crate) fn sub_split<let N: u32>(a: Field, b: Field) -> (Field, bool) {
    static_assert((N >= 1) & (N <= 128), "sub_split: N must be in 1..=128");
    // Safety: constrain_sub_split range-checks the difference, which
    // forces the borrow to the true comparison.
    let borrow = unsafe { hint_lt(a, b) };
    let diff = constrain_sub_split::<N>(a, b, borrow);
    (diff, borrow)
}

/// Hint for mul_split and mul_split_short. Trap-free: the Field product
/// cannot wrap under either caller's precondition (below 2^252 for
/// mul_split, below 2^253 for mul_split_short, both under p), and
/// to_le_bits of any Field is defined in unconstrained code.
unconstrained fn hint_mul_split<let N: u32>(a: Field, b: Field) -> (Field, Field) {
    let p = a * b;
    let bits: [bool; 254] = p.to_le_bits();
    let mut lo: Field = 0;
    let mut hi: Field = 0;
    let mut pw_lo: Field = 1;
    let mut pw_hi: Field = 1;
    for i in 0..254 {
        if i < N {
            lo = lo + (bits[i] as Field) * pw_lo;
            pw_lo = pw_lo * 2;
        } else {
            hi = hi + (bits[i] as Field) * pw_hi;
            pw_hi = pw_hi * 2;
        }
    }
    (lo, hi)
}

/// Constraint half of mul_split: RANGE lo and hi to N bits each and
/// a*b == lo + hi*2^N. For a, b < 2^N the product is below 2^2N <= 2^252,
/// so the equation cannot wrap, the split exists and is unique, and the
/// constraints are hint-satisfiable with determined outputs.
pub(crate) fn constrain_mul_split<let N: u32>(a: Field, b: Field, lo: Field, hi: Field) {
    lo.assert_max_bit_size::<N>();
    hi.assert_max_bit_size::<N>();
    assert(a * b == lo + hi * two_pow::<N>());
}

/// (a*b) mod 2^N and the high part, for a, b already constrained below
/// 2^N (N <= 126; the cap is load-bearing: the identity needs
/// a*b < 2^(2N) <= 2^252 < p). PRECONDITION as above; pub(crate).
pub(crate) fn mul_split<let N: u32>(a: Field, b: Field) -> (Field, Field) {
    static_assert(
        (N >= 1) & (N <= 126),
        "mul_split: N must be in 1..=126 (2N <= 252 keeps a*b below p)",
    );
    // Safety: constrain_mul_split range-checks both parts and checks the
    // reconstruction, which determines them uniquely.
    let (lo, hi) = unsafe { hint_mul_split::<N>(a, b) };
    constrain_mul_split::<N>(a, b, lo, hi);
    (lo, hi)
}

/// Constraint half of mul_split_short: RANGE lo to N bits, RANGE hi to
/// N - 1 bits, and a*b == lo + hi*2^N.
/// Integer identity: a*b = lo + hi*2^N with 0 <= lo < 2^N.
/// Hint-satisfiable: under the precondition a*b < 2^(2N - 1) the honest
/// hi = floor(a*b / 2^N) is below 2^(N - 1).
/// Determined (no wrap): the right side is at most
/// (2^N - 1) + (2^(N - 1) - 1)*2^N < 2^(2N - 1) and the left side is below
/// 2^(2N - 1) by the precondition, and 2^(2N - 1) <= 2^253 < p for
/// N <= 127, so the field equation is an integer one and Euclidean
/// division by 2^N makes (lo, hi) unique. The N - 1 bit range on hi is
/// load-bearing at N = 127: with an N-bit range, lo' = p mod 2^127 and
/// hi' = p >> 127 (about 2^126.6) satisfy the equation for a*b = 0.
pub(crate) fn constrain_mul_split_short<let N: u32>(a: Field, b: Field, lo: Field, hi: Field) {
    lo.assert_max_bit_size::<N>();
    hi.assert_max_bit_size::<N - 1>();
    assert(a * b == lo + hi * two_pow::<N>());
}

/// (a*b) mod 2^N and floor(a*b / 2^N) for 2 <= N <= 127 when the product
/// is known to be below 2^(2N - 1), for example a < 2^N and b <= 2^(N - 1)
/// (a shift by at most N - 1 places). PRECONDITION: a < 2^N and
/// a*b < 2^(2N - 1), constrained by the caller; pub(crate). The tighter
/// bound on the high part is what lets N reach 127, one past mul_split:
/// both sides of the identity stay below 2^253 < p. The hint is
/// hint_mul_split, trap-free here because the Field product is below
/// 2^253 and does not wrap.
pub(crate) fn mul_split_short<let N: u32>(a: Field, b: Field) -> (Field, Field) {
    static_assert(
        (N >= 2) & (N <= 127),
        "mul_split_short: N must be in 2..=127 (2N - 1 <= 253 keeps both sides below p)",
    );
    // Safety: constrain_mul_split_short range-checks both parts and checks
    // the reconstruction, which determines them uniquely.
    let (lo, hi) = unsafe { hint_mul_split::<N>(a, b) };
    constrain_mul_split_short::<N>(a, b, lo, hi);
    (lo, hi)
}

/// Hint for div_split: the u128 quotient q of the truncated operands and
/// the remainder ai - q*bi formed in the field (0 <= ai - q*bi < bi <
/// 2^128, so no wrap; a u128 remainder by a value would be the same
/// number). Trap-free under the caller's precondition b1 >= 1: the
/// divisor cast cannot give zero because b1 < 2^N is nonzero and the
/// cast is exact below 2^128.
unconstrained fn hint_div<let N: u32>(a: Field, b1: Field) -> (Field, Field) {
    let ai = a as u128;
    let bi = b1 as u128;
    let q = ai / bi;
    (q as Field, (ai as Field) - (q as Field) * (bi as Field))
}

/// Constraint half of div_split: RANGE q and r to N bits, a == q*b1 + r,
/// and r < b1 via RANGE on b1 - r - 1. Given a < 2^N and 1 <= b1 < 2^N,
/// Euclidean division gives the unique (q, r) that satisfies all four,
/// and q*b1 + r < 2^252 + 2^126 cannot wrap. All hint-satisfiable;
/// outputs determined. These are exactly the soundness constraints a
/// division needs; removing any of them lets a dishonest prover choose
/// the quotient.
pub(crate) fn constrain_div_split<let N: u32>(a: Field, b1: Field, q: Field, r: Field) {
    q.assert_max_bit_size::<N>();
    r.assert_max_bit_size::<N>();
    assert(a == q * b1 + r);
    let d = b1 - r - 1;
    d.assert_max_bit_size::<N>();
}

/// Euclidean division for a already constrained below 2^N and a divisor
/// already selected into [1, 2^N) (N <= 126). PRECONDITIONS are the
/// caller's job (div_rem_or selects the divisor to 1 when it is zero BEFORE
/// calling, so the hint cannot trap); pub(crate). The cap is
/// load-bearing: the identity needs q*b1 + r < 2^(2N) + 2^N < p.
pub(crate) fn div_split<let N: u32>(a: Field, b1: Field) -> (Field, Field) {
    static_assert(
        (N >= 1) & (N <= 126),
        "div_split: N must be in 1..=126 (keeps q*b1 + r below p)",
    );
    // Safety: constrain_div_split pins (q, r) to the unique Euclidean
    // pair via the ranges, the reconstruction, and r < b1.
    let (q, r) = unsafe { hint_div::<N>(a, b1) };
    constrain_div_split::<N>(a, b1, q, r);
    (q, r)
}

/// Largest operand width of the fused multiply-divide (mul_div_split and
/// the entries built on it). The gadget checks a*b == q*d1 + r in the
/// field, which pins the integers only if neither side can reach p. The
/// left side is below 2^(2N). The right side is bounded by the ranges on
/// the hints: q below 2^(2N), d1 below 2^N, r below d1, so
/// q*d1 + r < 2^(3N). Both sides are below p when 3N <= 253 (p > 2^253),
/// that is N <= 84. The product alone would allow N <= 126; the
/// quotient term is what sets the bound, because q must be allowed the
/// full 2N bits for the honest hint to always satisfy its range.
pub global MUL_DIV_MAX_BITS: u32 = 84;

/// Hint for mul_div_split: floor(a*b / d1) split at bit M as
/// (q mod 2^M, q >> M), and a*b mod d1. Binary long division in Field
/// arithmetic over the big-endian bits of the Field product a*b, so it
/// is trap-free for every argument: there is no integer type to
/// overflow, no division, no index arithmetic (the loop index reads a
/// 254-element array directly), and to_be_bits of any Field is defined.
/// The conditional subtraction is written r - bit*d1 (Field arithmetic,
/// not a branch on the bit). Under the caller's precondition
/// (a, b < 2^N, 1 <= d1 < 2^N, N <= 84) the product is below 2^(2N), so
/// it does not wrap, its top 254 - 2N bits are zero, and the running
/// remainder stays below d1; the result is the Euclidean pair. Outside the precondition the
/// values are meaningless but the hint still returns (d1 = 0 gives a
/// quotient of all ones), and the constraints then decide.
unconstrained fn hint_mul_div<let M: u32>(a: Field, b: Field, d1: Field) -> (Field, Field, Field) {
    let bits: [bool; 254] = (a * b).to_be_bits();
    let mut q_lo: Field = 0;
    let mut q_hi: Field = 0;
    let mut r: Field = 0;
    for k in 0..254 {
        // bits[k] has weight 2^(253 - k): it belongs to the high part of
        // the quotient when 253 - k >= M, i.e. k < 254 - M (a constant).
        r = r * 2 + (bits[k] as Field);
        let bit = !r.lt(d1);
        r = r - (bit as Field) * d1;
        if k < 254 - M {
            q_hi = q_hi * 2 + (bit as Field);
        } else {
            q_lo = q_lo * 2 + (bit as Field);
        }
    }
    (q_lo, q_hi, r)
}

/// hint_mul_div with every quotient bit in the low part (M = 254): the
/// whole quotient floor(a*b / d1) and the remainder, for mul_div_split at
/// M = 2N, where the quotient needs no split. Same arithmetic, so
/// trap-free for every argument. Returning only (q, r) leaves no hint
/// output unconstrained.
unconstrained fn hint_mul_div_full(a: Field, b: Field, d1: Field) -> (Field, Field) {
    let (q, _, r) = hint_mul_div::<254>(a, b, d1);
    (q, r)
}

/// Constraint half of mul_div_split, split out so tests can feed wrong
/// hints. For a, b < 2^N and 1 <= d1 < 2^N (PRECONDITIONS), with
/// 1 <= N <= 84 and 1 <= M <= 2N, it emits:
/// 1. RANGE q_lo to M bits.
/// 2. Only when M < 2N: RANGE q_hi to 2N - M bits, and the inversion
///    gadget is_zero(q_hi), whose value is returned as the fits flag.
///    When M = 2N, q_hi is not used at all and the flag is the constant
///    true; mul_div_split then passes 0 and takes q_lo from
///    hint_mul_div_full, so no hint output goes unconstrained.
/// 3. RANGE r to N bits.
/// 4. RANGE d1 - r - 1 to N bits: r < d1.
/// 5. a*b == q*d1 + r, with q = q_lo + q_hi*2^M (q = q_lo when M = 2N).
/// Classification: every one is hint-satisfiable, so each is an assert,
/// not a flag. The honest quotient is below 2^(2N) (a*b < 2^(2N) and
/// d1 >= 1), so its low M bits satisfy 1 and its high part satisfies
/// the range in 2; is_zero is satisfiable for every value; the honest
/// remainder is below d1 < 2^N, so 3 and 4 hold; 5 is Euclid's identity.
/// Determined: 1 and 2 bound q below 2^(2N), and 3 and 4 bound r below
/// d1, so both sides of 5 are below 2^(3N) <= 2^252 < p
/// (MUL_DIV_MAX_BITS): 5 holds over the integers, and Euclidean
/// division makes (q, r) unique. The split of a q below 2^(2N) at bit M
/// is unique too, so q_lo, q_hi and the fits flag are fixed by the
/// inputs. Each range is load-bearing: without 1 or 2 a quotient
/// q + k*p/d1 (a field element far above 2^(2N)) passes 5; without 3,
/// r = p - k (a "negative" remainder) passes 4 and gives the quotient
/// (a*b + k)/d1; without 4, (q - 1, r + d1) passes.
pub(crate) fn constrain_mul_div<let N: u32, let M: u32>(
    a: Field,
    b: Field,
    d1: Field,
    q_lo: Field,
    q_hi: Field,
    r: Field,
) -> bool {
    q_lo.assert_max_bit_size::<M>();
    let mut q = q_lo;
    let mut fits = true;
    if M < 2 * N {
        q_hi.assert_max_bit_size::<2 * N - M>();
        q = q_lo + q_hi * two_pow::<M>();
        fits = is_zero(q_hi);
    }
    r.assert_max_bit_size::<N>();
    (d1 - r - 1).assert_max_bit_size::<N>();
    assert(a * b == q * d1 + r, "mul_div identity");
    fits
}

/// Fused floor(a*b / d1) for a, b already constrained below 2^N and a
/// divisor already selected into [1, 2^N) (1 <= N <= 84). Returns
/// (q mod 2^M, a*b mod d1, q < 2^M) for 1 <= M <= 2N; with M = 2N the
/// flag is the constant true. PRECONDITIONS are the caller's job (the
/// entries select the divisor to 1 when it is zero BEFORE calling);
/// pub(crate). One hinted quotient and remainder checked against the
/// double-width product directly, where div_or after mul_or would
/// need the product below 2^N.
pub(crate) fn mul_div_split<let N: u32, let M: u32>(
    a: Field,
    b: Field,
    d1: Field,
) -> (Field, Field, bool) {
    static_assert(
        (N >= 1) & (N <= MUL_DIV_MAX_BITS),
        "mul_div: N must be in 1..=84 (3N <= 253 keeps q*d1 + r below p)",
    );
    static_assert((M >= 1) & (M <= 2 * N), "mul_div: M must be in 1..=2N");
    if M == 2 * N {
        // Safety: constrain_mul_div range-checks the quotient to 2N bits
        // and the remainder, checks r < d1 and the identity, which pins
        // the unique Euclidean pair (its doc comment has the argument).
        let (q, r) = unsafe { hint_mul_div_full(a, b, d1) };
        let fits = constrain_mul_div::<N, M>(a, b, d1, q, 0, r);
        (q, r, fits)
    } else {
        // Safety: as above, with the quotient split at bit M.
        let (q_lo, q_hi, r) = unsafe { hint_mul_div::<M>(a, b, d1) };
        let fits = constrain_mul_div::<N, M>(a, b, d1, q_lo, q_hi, r);
        (q_lo, r, fits)
    }
}

// ---------------------------------------------------------------------
// Wide fused multiply-divide: 85 <= N <= 128
// ---------------------------------------------------------------------
//
// Past MUL_DIV_MAX_BITS the identity a*b == q*d1 + r no longer pins the
// integers when checked in the field alone: both sides can reach 2^(3N),
// above p. The wide gadget checks the same identity in the field AND
// shows that the integer difference Z = a*b - q*d1 - r is divisible by a
// power of two 2^K, with one range check per 2^64 or 2^128 "column" on a
// carry that is a linear combination of the operands and hints (no
// hinted carry). p is odd, so p*2^K divides Z, and the ranges bound
// |Z| < p*2^K, so Z = 0 over the integers. The quotient comes back as two
// 128-bit limbs q = q_lo + q_hi*2^128, since it can need 2N > 253 bits.
//
// Two layouts, selected at compile time by N:
// - N <= MUL_DIV_WIDE_UNSPLIT_MAX_BITS (124), "unsplit": K = 128 with
//   one carry, from a*b - q_lo*d1 - r, which stays far enough below p
//   that no operand needs splitting.
// - N >= 125, "split": a*b can reach 2^256 > p, so a, b, d1 and both
//   quotient limbs are split into 64-bit limbs, and two carries give
//   K = 192 (K = 128 would not be enough at N = 128, where |Z| can reach
//   2^384 > p*2^128).
//
// Width rule for library-chosen ranges (the carries here, and the
// carries of arith's 128-bit gadgets): a multiple of 14 bits wherever the
// soundness bound allows. The backend decomposes a range check into
// 14-bit limbs, and a width w with w mod 14 != 0 needs a lookup table for
// its top limb, a fixed per-circuit cost that grows with 2^(w mod 14).
// A wider carry range only loosens the bound the argument needs
// (|carry * 2^k| + |linear part| < p), so each carry below states it with
// the rounded width. Widths fixed by the data (N, 64-bit limbs, 128) are
// not rounded.

/// Largest operand width of the wide fused multiply-divide.
pub global MUL_DIV_WIDE_MAX_BITS: u32 = 128;

/// Largest N for the unsplit layout of the wide multiply-divide. Its one
/// carry c = (a*b - q_lo*d1 - r) / 2^128 lies in (-2^N, 2^N); the check
/// that the field element c is such a small integer proves 2^128 divides
/// the integer a*b - q_lo*d1 - r only while |c*2^128| + |a*b - q_lo*d1 - r|
/// < 2^(N + 129) stays below p, that is N + 129 <= 253.
pub global MUL_DIV_WIDE_UNSPLIT_MAX_BITS: u32 = 124;

/// Largest N for which the unsplit layout's carry range is rounded up
/// to a multiple of 14 bits, W = 14*ceil((N + 1)/14) (the width rule
/// above); above it W = N + 1. The argument needs W + 128 <= 253
/// (constrain_mul_div_wide_unsplit), and the rounded W is at most 112
/// exactly for N <= 111 (N = 112 would round to 126).
global MUL_DIV_WIDE_ROUNDED_CARRY_MAX_BITS: u32 = 111;

/// 1 / 2^64 and 1 / 2^128 in the field (checked by the test
/// wide_inverse_constants). Multiplying by them is the exact division of
/// a multiple of 2^64 or 2^128, and a linear operation, so a carry costs
/// no hint and no gate of its own beyond its range check.
pub(crate) global INV_TWO_POW_64: Field =
    0x24d6ba07f7aa8f04b2d8f06f77f52a93ca478dbeab3c92cd2d3e8053e396ee4d;
pub(crate) global INV_TWO_POW_128: Field =
    0x133100d71fdf35792b16366f4f7684df54ad7e14a329e70f18ee753c76f9dc6f;

/// The integer sum of bits[i] * 2^(i - lo) for lo <= i < hi: the value of
/// a bit field of a little-endian decomposition. Trap-free: Field
/// arithmetic only, and every call site passes hi <= 254.
unconstrained fn le_bits_value(bits: [bool; 254], lo: u32, hi: u32) -> Field {
    let mut v: Field = 0;
    let mut pw: Field = 1;
    for i in lo..hi {
        v = v + (bits[i] as Field) * pw;
        pw = pw * 2;
    }
    v
}

/// Hint for the wide multiply-divide: (q mod 2^128, q >> 128, a*b mod d1)
/// for q = floor(a*b / d1). Field arithmetic only, so it is trap-free for
/// every argument (no integer type to overflow, no division, fixed-size
/// arrays read on constant ranges, to_le_bits/to_be_bits of any Field is
/// defined).
///
/// Under the caller's precondition (a, b < 2^128, 1 <= d1 < 2^128) it
/// forms the 256-bit product from 64-bit limbs,
/// a*b = a0*b0 + (a0*b1 + a1*b0)*2^64 + a1*b1*2^128 = lo + hi*2^128 with
/// lo, hi < 2^128 (the middle term is below 2^129 and is cut at bit 64,
/// the low sum is below 2^129 and is cut at bit 128), then runs binary
/// restoring division over the 256 bits, high limb first: the running
/// remainder stays below d1 < 2^128 before each doubling, so 2r + 1 never
/// wraps. Outside the precondition the values are meaningless but the
/// hint returns, and the constraints decide.
unconstrained fn hint_mul_div_wide(a: Field, b: Field, d1: Field) -> (Field, Field, Field) {
    let ab: [bool; 254] = a.to_le_bits();
    let bb: [bool; 254] = b.to_le_bits();
    let a0 = le_bits_value(ab, 0, 64);
    let a1 = le_bits_value(ab, 64, 128);
    let b0 = le_bits_value(bb, 0, 64);
    let b1 = le_bits_value(bb, 64, 128);
    let mid: [bool; 254] = (a0 * b1 + a1 * b0).to_le_bits();
    let low: [bool; 254] = (a0 * b0 + le_bits_value(mid, 0, 64) * TWO_POW_64).to_le_bits();
    let lo = le_bits_value(low, 0, 128);
    let hi = a1 * b1 + le_bits_value(mid, 64, 254) + le_bits_value(low, 128, 254);
    // bits[k] of a to_be_bits decomposition has weight 2^(253 - k), so a
    // value below 2^128 is bits[126..254], most significant first
    let hb: [bool; 254] = hi.to_be_bits();
    let lb: [bool; 254] = lo.to_be_bits();
    let mut r: Field = 0;
    let mut q_hi: Field = 0;
    for k in 126..254 {
        r = r * 2 + (hb[k] as Field);
        let bit = !r.lt(d1);
        r = r - (bit as Field) * d1;
        q_hi = q_hi * 2 + (bit as Field);
    }
    let mut q_lo: Field = 0;
    for k in 126..254 {
        r = r * 2 + (lb[k] as Field);
        let bit = !r.lt(d1);
        r = r - (bit as Field) * d1;
        q_lo = q_lo * 2 + (bit as Field);
    }
    (q_lo, q_hi, r)
}

/// Constraint half of the wide multiply-divide, unsplit layout
/// (85 <= N <= 124), split out so tests can feed wrong hints. For
/// a, b < 2^N and 1 <= d1 < 2^N (PRECONDITIONS) it emits:
/// 1. RANGE q_lo to 128 bits.
/// 2. RANGE q_hi to 2N - 128 bits.
/// 3. RANGE r to N bits.
/// 4. RANGE d1 - r - 1 to N bits: r < d1.
/// 5. The carry: c = (a*b - q_lo*d1 - r) / 2^128 (a field multiple of
///    the constant 1/2^128, so a linear combination, not a witness of
///    its own), and RANGE c + 2^N to W bits, W = 14*ceil((N + 1)/14) for
///    N <= 111 and W = N + 1 above: c is an integer in
///    [-2^N, 2^W - 2^N).
/// 6. a*b == (q_lo + q_hi*2^128)*d1 + r in the field.
/// Classification: every one restricts a hint (q_lo, q_hi, r), and the
/// honest hint satisfies all six on the whole precondition domain, so
/// each is a hint-satisfiable assert. The honest q = floor(a*b/d1) is
/// below 2^(2N) (a*b < 2^(2N), d1 >= 1), so its limbs fit 1 and 2; the
/// honest remainder is below d1 < 2^N (3, 4); 6 is Euclid's identity; and
/// a*b - q_lo*d1 - r = q_hi*d1*2^128 is a multiple of 2^128 whose
/// quotient lies in (-2^N, 2^(2N - 128)) because the left side lies in
/// (-2^(N + 128), 2^(2N)) for any q_lo < 2^128 and r < 2^N (5).
/// Determined: let Z = a*b - q*d1 - r over the integers, q the integer
/// q_lo + q_hi*2^128. By 1-4, 0 <= q < 2^(2N) and 0 <= r < d1, so
/// |Z| < 2^(3N) <= 2^372. 5: the range gives an integer c in
/// [-2^N, 2^W - 2^N) with c*2^128 = a*b - q_lo*d1 - r in the field. The
/// right side lies in (-2^(N + 128) - 2^N, 2^(N + 128)) and |c*2^128| is
/// at most 2^(W + 128) - 2^(N + 128) (W >= N + 1), so their difference is
/// below 2^(W + 128) + 2^N <= 2^253 + 2^124 < p (W <= 112 for N <= 111,
/// W = N + 1 <= 125 above; MUL_DIV_WIDE_UNSPLIT_MAX_BITS) and the
/// equality is an integer one; then Z = c*2^128 - q_hi*d1*2^128 is a
/// multiple of 2^128. 6: Z is a multiple of p. p is odd, so Z is a
/// multiple of p*2^128 > 2^381 > |Z|, so Z = 0: a*b = q*d1 + r over the
/// integers, and Euclidean division with 0 <= r < d1 makes (q, r) unique,
/// and the split of q at bit 128 with q_lo < 2^128 is unique. Each check
/// is load-bearing: without 5 a quotient off by a multiple of p/d1 (the
/// wrapped witness of the 84-bit gadget) passes 6; without 2 a quotient
/// near p*2^128/d1 passes 5 and 6 (Z = -p*2^128); without 3 a "negative"
/// remainder passes 4; without 4, (q - 1, r + d1) passes; without 1, the
/// field quotient 17/5 passes the rest.
pub(crate) fn constrain_mul_div_wide_unsplit<let N: u32>(
    a: Field,
    b: Field,
    d1: Field,
    q_lo: Field,
    q_hi: Field,
    r: Field,
) {
    q_lo.assert_max_bit_size::<128>();
    q_hi.assert_max_bit_size::<2 * N - 128>();
    r.assert_max_bit_size::<N>();
    (d1 - r - 1).assert_max_bit_size::<N>();
    let c = (a * b - q_lo * d1 - r) * INV_TWO_POW_128;
    if N <= MUL_DIV_WIDE_ROUNDED_CARRY_MAX_BITS {
        (c + two_pow::<N>()).assert_max_bit_size::<14 * ((N + 14) / 14)>();
    } else {
        (c + two_pow::<N>()).assert_max_bit_size::<N + 1>();
    }
    assert(a * b == (q_lo + q_hi * TWO_POW_128) * d1 + r, "mul_div_wide identity");
}

/// Constraint half of the wide multiply-divide, split layout
/// (125 <= N <= 128). limbs = [a0, a1, b0, b1, d0, dh, q0, q1, q2, q3],
/// the 64-bit limbs of a, b, d1, q_lo and q_hi. For a, b < 2^N and
/// 1 <= d1 < 2^N (PRECONDITIONS) it emits:
/// 1-5. constrain_split_128_at::<64> on (a; a0, a1), (b; b0, b1),
///    (d1; d0, dh), (q_lo; q0, q1), (q_hi; q2, q3): each limb RANGEd to
///    64 bits and x == lo + hi*2^64.
/// 6. RANGE r to N bits.
/// 7. RANGE d1 - r - 1 to N bits: r < d1.
/// 8. The low carry: c0 = G0 / 2^128 with
///    G0 = a0*b0 + (a0*b1 + a1*b0)*2^64 - q_lo*d0 - q0*dh*2^64 - r,
///    and RANGE c0 + 2^66 to 70 bits (the width rule).
/// 9. The middle carry: c1 = (c0 + a1*b1 - q1*dh - q2*d0) / 2^64, and
///    RANGE c1 + 2^66 to 70 bits.
/// 10. a*b == (q_lo + q_hi*2^128)*d1 + r in the field.
/// Where these come from: with all limbs below 2^64, expanding
/// Z = a*b - q*d1 - r (q = q_lo + q_hi*2^128) by powers of 2^64 gives
/// Z = G0 + 2^128*(a1*b1 - q1*dh - q2*d0) - 2^192*(q2*dh + q3*d0 + 2^64*q3*dh).
/// Classification: every check restricts a hint (the limbs, q_lo, q_hi,
/// r), and the honest hint satisfies all ten on the precondition domain:
/// the honest limbs are the exact splits (a, b, d1 < 2^128, and
/// q < 2^256 so q_lo, q_hi < 2^128), the honest remainder is below d1,
/// 10 is Euclid's identity, and Z = 0 makes G0 a multiple of 2^128 and
/// then c0 + a1*b1 - q1*dh - q2*d0 a multiple of 2^64, whose quotients
/// lie in (-2^66, 2^66) for ANY limbs below 2^64 and r < 2^128
/// (|G0| < 2^194; |c0 + a1*b1 - q1*dh - q2*d0| < 2^130). Each split is
/// hint-satisfiable rather than input-falsifiable because a, b and d1
/// are below 2^128 by the precondition.
/// Determined: by 1-7, all limbs are integers in [0, 2^64), r in [0, d1),
/// q in [0, 2^256) and d1 < 2^128, so |Z| < 2^384 + 2^128. 8: the range
/// gives an integer c0 in [-2^66, 2^70) with c0*2^128 = G0 in the field;
/// |c0*2^128| < 2^198 and |G0| < 2^194, so the difference is below 2^199
/// < p and the equality is an integer one. 9: the same at 2^64:
/// |c1*2^64| < 2^134 and |c0 + a1*b1 - q1*dh - q2*d0| < 2^131. So Z is a
/// multiple of 2^192, and by 10 of p, hence of p*2^192 > 2^445 > |Z|:
/// Z = 0. Euclid then makes (q, r) unique, and the limb splits are
/// unique. Load-bearing: without 9 a quotient near p*2^128/d1
/// (Z = -p*2^128, d1 > 2^126) passes the rest; without 8 a quotient
/// a*b + p over d1 = 1 does;
/// without the 64-bit range on q3 (in 5) a quotient near p*2^192/d1 does;
/// the ranges on r and d1 - r - 1 as in the unsplit layout.
pub(crate) fn constrain_mul_div_wide_split<let N: u32>(
    a: Field,
    b: Field,
    d1: Field,
    q_lo: Field,
    q_hi: Field,
    r: Field,
    limbs: [Field; 10],
) {
    let (a0, a1, b0, b1, d0, dh) = (limbs[0], limbs[1], limbs[2], limbs[3], limbs[4], limbs[5]);
    let (q0, q1, q2, q3) = (limbs[6], limbs[7], limbs[8], limbs[9]);
    constrain_split_128_at::<64>(a, a0, a1);
    constrain_split_128_at::<64>(b, b0, b1);
    constrain_split_128_at::<64>(d1, d0, dh);
    constrain_split_128_at::<64>(q_lo, q0, q1);
    constrain_split_128_at::<64>(q_hi, q2, q3);
    r.assert_max_bit_size::<N>();
    (d1 - r - 1).assert_max_bit_size::<N>();
    let g0 = a0 * b0 + (a0 * b1 + a1 * b0) * TWO_POW_64 - q_lo * d0 - q0 * dh * TWO_POW_64 - r;
    let c0 = g0 * INV_TWO_POW_128;
    (c0 + two_pow::<66>()).assert_max_bit_size::<70>();
    let c1 = (c0 + a1 * b1 - q1 * dh - q2 * d0) * INV_TWO_POW_64;
    (c1 + two_pow::<66>()).assert_max_bit_size::<70>();
    assert(a * b == (q_lo + q_hi * TWO_POW_128) * d1 + r, "mul_div_wide identity");
}

/// The 64-bit limbs the split layout needs, from hint_split_128_at.
/// Trap-free for every argument (see there).
unconstrained fn hint_wide_limbs(
    a: Field,
    b: Field,
    d1: Field,
    q_lo: Field,
    q_hi: Field,
) -> [Field; 10] {
    let (a0, a1) = hint_split_128_at::<64>(a);
    let (b0, b1) = hint_split_128_at::<64>(b);
    let (d0, dh) = hint_split_128_at::<64>(d1);
    let (q0, q1) = hint_split_128_at::<64>(q_lo);
    let (q2, q3) = hint_split_128_at::<64>(q_hi);
    [a0, a1, b0, b1, d0, dh, q0, q1, q2, q3]
}

/// Fused floor(a*b / d1) for 85 <= N <= 128, for a, b already
/// constrained below 2^N and a divisor already selected into [1, 2^N).
/// Returns (q_lo, q_hi, r): q = floor(a*b/d1) = q_lo + q_hi*2^128 with
/// q_lo < 2^128 and q_hi < 2^(2N - 128), and r = a*b mod d1. q_lo and r
/// are range-checked witnesses in the unsplit layout; in the split layout
/// q_lo is bound below 2^128 by its limb split but carries no RANGE of
/// its own (a caller casting it to u128 adds implied_range). PRECONDITIONS
/// are the caller's job, as for mul_div_split; pub(crate). For N <= 84
/// use mul_div_split, which checks the identity in the field alone and
/// costs less.
pub(crate) fn mul_div_wide_split<let N: u32>(
    a: Field,
    b: Field,
    d1: Field,
) -> (Field, Field, Field) {
    static_assert(
        (N > MUL_DIV_MAX_BITS) & (N <= MUL_DIV_WIDE_MAX_BITS),
        "mul_div_wide: N must be in 85..=128 (for N <= 84 use mul_div_split)",
    );
    // Safety: the constraint half pins (q_lo, q_hi, r) to the unique
    // Euclidean pair (its doc comment has the argument).
    let (q_lo, q_hi, r) = unsafe { hint_mul_div_wide(a, b, d1) };
    if N <= MUL_DIV_WIDE_UNSPLIT_MAX_BITS {
        constrain_mul_div_wide_unsplit::<N>(a, b, d1, q_lo, q_hi, r);
    } else {
        // Safety: each limb pair is pinned by constrain_split_128_at.
        let limbs = unsafe { hint_wide_limbs(a, b, d1, q_lo, q_hi) };
        constrain_mul_div_wide_split::<N>(a, b, d1, q_lo, q_hi, r, limbs);
    }
    (q_lo, q_hi, r)
}

mod tests;
mod mul_div_tests;
mod mul_div_wide_tests;
mod hint_tests;
