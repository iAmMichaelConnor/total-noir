use crate::test_support::wit;
use super::{constrain_mul_div, hint_mul_div, MUL_DIV_MAX_BITS, mul_div_split, two_pow};

global P_MINUS_1: Field = 0 - 1;

#[test]
fn max_bits_is_the_3n_bound() {
    // 3N <= 253 < log2(p): 2^252 is a field element below p and
    // 2^(3*85) = 2^255 is not representable.
    assert_eq(MUL_DIV_MAX_BITS, 84);
    assert(two_pow::<252>().lt(P_MINUS_1));
}

#[test]
fn split_full_width_and_narrow() {
    let m = two_pow::<64>();
    // (2^64 - 1)^2 / 1 at M = 128: the largest quotient there is
    let (q, r, fits) = mul_div_split::<64, 128>(wit(m - 1), wit(m - 1), wit(1));
    assert_eq(q, (m - 1) * (m - 1));
    assert_eq(r, 0);
    assert(fits);
    // the same at M = 64: low 64 bits of 2^128 - 2^65 + 1 is 1
    let (q, r, fits) = mul_div_split::<64, 64>(wit(m - 1), wit(m - 1), wit(1));
    assert_eq(q, 1);
    assert_eq(r, 0);
    assert(!fits);
    // a quotient exactly at the width bound fits
    let (q, r, fits) = mul_div_split::<64, 64>(wit(m - 1), wit(1), wit(1));
    assert_eq(q, m - 1);
    assert_eq(r, 0);
    assert(fits);
    // and one past it does not
    let t32 = two_pow::<32>();
    let (q, r, fits) = mul_div_split::<64, 64>(wit(t32), wit(t32), wit(1));
    assert_eq(q, 0);
    assert_eq(r, 0);
    assert(!fits);
    // a*b near 2^(2N) at N = 84: (2^84 - 1)^2 / 2 = 2^167 - 2^84, r 1
    let w = two_pow::<84>();
    let (q, r, fits) = mul_div_split::<84, 168>(wit(w - 1), wit(w - 1), wit(2));
    assert_eq(q, two_pow::<167>() - w);
    assert_eq(r, 1);
    assert(fits);
    let (q, r, fits) = mul_div_split::<84, 168>(wit(w - 1), wit(w - 1), wit(w - 1));
    assert_eq(q, w - 1);
    assert_eq(r, 0);
    assert(fits);
}

#[test]
fn hint_is_trap_free_outside_the_precondition() {
    // Safety: test of the hint alone; nothing is constrained.
    let _ = unsafe { hint_mul_div::<128>(5, 7, 0) };
    // Safety: test that the hint returns on arguments outside its precondition.
    let _ = unsafe { hint_mul_div::<128>(P_MINUS_1, P_MINUS_1, P_MINUS_1) };
    // Safety: as above.
    let _ = unsafe { hint_mul_div::<1>(P_MINUS_1, 2, 3) };
    // Safety: as above.
    let _ = unsafe { hint_mul_div::<168>(two_pow::<200>(), two_pow::<200>(), 1) };
    // Safety: as above.
    let (q_lo, q_hi, r) = unsafe { hint_mul_div::<64>(two_pow::<64>() + 7, 1, 1) };
    assert_eq(q_lo, 7);
    assert_eq(q_hi, 1);
    assert_eq(r, 0);
}

#[test]
fn honest_hints_pass() {
    assert(constrain_mul_div::<64, 128>(wit(17), wit(1), wit(5), wit(3), wit(0), wit(2)));
    assert(constrain_mul_div::<64, 64>(wit(17), wit(1), wit(5), wit(3), wit(0), wit(2)));
    // 2^64 + 5 at M = 64: q_lo 5, q_hi 1, flag false
    let m = two_pow::<64>();
    assert(!constrain_mul_div::<64, 64>(wit(m + 5), wit(1), wit(1), wit(5), wit(1), wit(0)));
}

#[test]
fn honest_extremes_at_84_bits() {
    let w = two_pow::<84>();
    // (2^84 - 1)^2 / 1: the quotient needs all 168 bits
    let (q, r, fits) = mul_div_split::<84, 168>(wit(w - 1), wit(w - 1), wit(1));
    assert_eq(q, (w - 1) * (w - 1));
    assert_eq(r, 0);
    assert(fits);
    let (q, r, fits) = mul_div_split::<84, 84>(wit(w - 1), wit(w - 1), wit(1));
    assert_eq(q, 1);
    assert_eq(r, 0);
    assert(!fits);
    // (2^84 - 1)^2 / (2^84 - 2) = 2^84 rem 1: one past the 84-bit bound
    let (q, r, fits) = mul_div_split::<84, 168>(wit(w - 1), wit(w - 1), wit(w - 2));
    assert_eq(q, w);
    assert_eq(r, 1);
    assert(fits);
    let (q, r, fits) = mul_div_split::<84, 84>(wit(w - 1), wit(w - 1), wit(w - 2));
    assert_eq(q, 0);
    assert_eq(r, 1);
    assert(!fits);
}

/// [a, b, d, floor(a*b/d), a*b mod d] below 2^84, from a reference
/// implementation (Python integers, seed 84): four near 2^84 - 1,
/// two with small divisors, the rest uniform.
global REF_84: [[Field; 5]; 20] = [
    [
        0xffffffffffffffffffd0a,
        0xffffffffffffffffffe88,
        0xc11918d2b6954daa9826d,
        0x15364727224b261c64849d,
        0x4c2329127668da03b2877,
    ],
    [
        0xfffffffffffffffffff67,
        0xfffffffffffffffffffd0,
        0xb486cf917d54834274d2,
        0x16b06ddf3230e6b8f7a094a,
        0x15a02510d041be9af5fc,
    ],
    [
        0xffffffffffffffffffed4,
        0xffffffffffffffffffd2f,
        0x22bd56c27d031e764f47e,
        0x75e7e0c0bb8d9d584bad91,
        0x2096113fa8477c5b1ab8e,
    ],
    [
        0xffffffffffffffffffdca,
        0xfffffffffffffffffffe1,
        0x771ce12c19e878b4dd166,
        0x226337b8883264068af2c0,
        0x66cb6191c55f4b0b4cc0a,
    ],
    [
        0xcca57b21d5b0b56379c1,
        0x5084830a40432ecea64a6,
        0x386,
        0x124494e07aa086ce554d82ef9517d6a3b8341f1,
        0x0,
    ],
    [
        0x9de5c89aec1505e3ce75a,
        0xfa34cfb02bec1e22fd470,
        0x3b0,
        0x29d9c144befe9dfa26bba2cacb9404b8ce889cad,
        0x170,
    ],
    [
        0xf37af0350643e13ec1b5c,
        0x2c73ded4a65174167fcf0,
        0x25068d442b425a2cb30d5,
        0x12452017b69e596a209c32,
        0x1004b4b8dc3cb8c3ae0a6,
    ],
    [
        0xc7ddd628f2bf7e388b1ef,
        0x8a3609e9ab495a600bccf,
        0xaa4a9fff2c9ac5aa9231d,
        0xa236f20412541143da8b5,
        0x3d04bd98039419da988c0,
    ],
    [
        0x2bb21a5224894553ea4b,
        0x92221ebb7c57bcb0d98ce,
        0xe42425a16da1c9b96629f,
        0x1bfd21e8a8d0edc063de,
        0xddf31de4da873bca50d78,
    ],
    [
        0x2415c973bfe804ef2a928,
        0x71317f9576b579165b69d,
        0xe7512b609f138ea15120a,
        0x11a871e94fed781296398,
        0xe670aca31aec743c59998,
    ],
    [
        0x8515b83214e40437626ef,
        0x13087fcafd9edff2d00a,
        0xddded02ba8d7c674cb92b,
        0xb6aadbe884460f58a32,
        0x9b9f3fc36d62ac2395cf0,
    ],
    [
        0x375d0d1dfd53b466ab143,
        0x94900389451b2226d64aa,
        0x2d41674498dd1b80b7a1b,
        0xb5be9f260d77bf433790d,
        0x8aa921601524faf1ec1f,
    ],
    [
        0x3fad443580eb8d3276e1f,
        0x5af698c01cb50e86dbc2f,
        0x3d66fd3a1e2ce21fa2b22,
        0x5e5533430a9f6505a4fc5,
        0x33031abe5e80f91884c87,
    ],
    [
        0xdb74a50e065fde9900868,
        0xff81a66292ae0a582a86,
        0x90e5ff1b556addd121ea2,
        0x182fa10e4e87280755a66,
        0x7819fcc44c605627e4de4,
    ],
    [
        0x380ab7e573c6ddee8e3ad,
        0x6ec485d2f217a6d312f44,
        0x5baf13004d20cab120608,
        0x43b4f42c32afa2a7bb74d,
        0x2a18e41dd4382a832b48c,
    ],
    [
        0xaf0561f58d2b0e6c385e6,
        0x41afe62ece619e42209,
        0xed88899427c82ad19c96b,
        0x3066695280625386150,
        0x27c6db26e650967b7c4a6,
    ],
    [
        0x3de038e263f80ee0a2db9,
        0xe8e1205647fb2eab2fe2c,
        0x7216654e507e7f4d964e0,
        0x7e4d9ef50bd5bba8007bf,
        0x181c4271d5f7917cb06ac,
    ],
    [
        0x3a55f4eb1423bf628fa2c,
        0x7cfc64f01ec1557223009,
        0x38a7c434e89954ec73ff3,
        0x80b16d1e4e5d03117e02f,
        0x169f8199dd36973d2adef,
    ],
    [
        0xc433528bf37987b3a5cd4,
        0xee36d1e53ac5078d8f483,
        0x5035abf2bc2a6e445ef12,
        0x246b1cd9415f9fa3be8e23,
        0x4e95851b642be7cafe506,
    ],
    [
        0xb197ceebbbc8c8a6acf34,
        0xf645cb2867b7f5e85cb6a,
        0x79dbb9ebe9a75f20aba72,
        0x166e93c4de64393e81c9c9,
        0x636f924c9eebbba4a2206,
    ],
];

#[test]
fn reference_sweep_at_84_bits() {
    let w = two_pow::<84>();
    for i in 0..20 {
        let row = REF_84[i];
        let (a, b, d, q, r) = (row[0], row[1], row[2], row[3], row[4]);
        assert_eq(mul_div_split::<84, 168>(wit(a), wit(b), wit(d)), (q, r, true));
        // at M = 84 the quotient is reduced mod 2^84 and flagged
        let fits = q.lt(w);
        let (q84, r84, fits84) = mul_div_split::<84, 84>(wit(a), wit(b), wit(d));
        assert_eq(r84, r);
        assert_eq(fits84, fits);
        if fits {
            assert_eq(q84, q);
        } else {
            assert(q84.lt(w));
            assert(((q - q84) / w).lt(w));
        }
    }
}

/// The hint on every triple of hostile arguments (zero divisor, the
/// field's -1, powers of two past every width, a "negative" value)
/// at the quotient widths 1, 64, 128 and 168: it must return, never
/// trap.
#[test]
unconstrained fn hint_sweep_on_hostile_arguments() {
    let xs: [Field; 8] = [
        0,
        1,
        P_MINUS_1,
        two_pow::<64>(),
        two_pow::<128>(),
        two_pow::<200>(),
        two_pow::<253>(),
        0 - two_pow::<84>(),
    ];
    for i in 0..8 {
        for j in 0..8 {
            for k in 0..8 {
                let _ = hint_mul_div::<1>(xs[i], xs[j], xs[k]);
                let _ = hint_mul_div::<64>(xs[i], xs[j], xs[k]);
                let _ = hint_mul_div::<128>(xs[i], xs[j], xs[k]);
                let _ = hint_mul_div::<168>(xs[i], xs[j], xs[k]);
            }
        }
    }
}

// Wrong-hint tests. constrain_mul_div has five constraints; the
// four range checks fail with the compiler's one message "call to
// assert_max_bit_size" (a range check takes no message of its own),
// the identity with "mul_div identity". So each test first calls
// only_fails with the constraints its witness violates: that check
// (with a message no test expects) proves every other constraint
// holds, and should_fail_with then pins the failure to the named
// constraint, the first violated one in constrain_mul_div's order.

global Q_LO: u32 = 1; // 1. q_lo < 2^M
global Q_HI: u32 = 2; // 2. q_hi < 2^(2N - M), only when M < 2N
global R: u32 = 4; // 3. r < 2^N
global R_LT_D: u32 = 8; // 4. d1 - r - 1 < 2^N, so r < d1
global IDENTITY: u32 = 16; // 5. a*b == q*d1 + r

/// Asserts that the witness violates exactly the constraints of
/// constrain_mul_div::<N, M> in the bit set `violated`.
fn only_fails<let N: u32, let M: u32>(
    a: Field,
    b: Field,
    d1: Field,
    q_lo: Field,
    q_hi: Field,
    r: Field,
    violated: u32,
) {
    let mut q = q_lo;
    let mut hi_ok = true;
    if M < 2 * N {
        q = q_lo + q_hi * two_pow::<M>();
        hi_ok = q_hi.lt(two_pow::<2 * N - M>());
    }
    let holds = [
        q_lo.lt(two_pow::<M>()),
        hi_ok,
        r.lt(two_pow::<N>()),
        (d1 - r - 1).lt(two_pow::<N>()),
        a * b == q * d1 + r,
    ];
    for i in 0..5 {
        let expect_violated = ((violated >> i) & 1) == 1;
        assert(holds[i] != expect_violated, "only_fails: witness setup");
    }
}

#[test(should_fail_with = "mul_div identity")]
fn wrong_quotient_rejected() {
    // 17 = 3*5 + 2; q = 4 with the honest r breaks the identity
    only_fails::<64, 128>(17, 1, 5, 4, 0, 2, IDENTITY);
    let _ = constrain_mul_div::<64, 128>(17, 1, 5, 4, 0, 2);
}

#[test(should_fail_with = "mul_div identity")]
fn wrong_remainder_rejected() {
    only_fails::<64, 128>(17, 1, 5, 3, 0, 3, IDENTITY);
    let _ = constrain_mul_div::<64, 128>(17, 1, 5, 3, 0, 3);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn remainder_above_divisor_rejected() {
    // 17 = 2*5 + 7: the identity holds, r < d1 must reject it
    only_fails::<64, 128>(17, 1, 5, 2, 0, 7, R_LT_D);
    let _ = constrain_mul_div::<64, 128>(17, 1, 5, 2, 0, 7);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn remainder_equal_to_divisor_rejected() {
    // 15 = 2*5 + 5
    only_fails::<64, 128>(15, 1, 5, 2, 0, 5, R_LT_D);
    let _ = constrain_mul_div::<64, 128>(15, 1, 5, 2, 0, 5);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn negative_remainder_rejected() {
    // 17 = 18*1 + (p - 1) in the field, and d1 - r - 1 = 1 fits:
    // only the N-bit range on r rejects the quotient 18
    only_fails::<64, 128>(17, 1, 1, 18, 0, P_MINUS_1, R);
    let _ = constrain_mul_div::<64, 128>(17, 1, 1, 18, 0, P_MINUS_1);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn wrapped_quotient_rejected() {
    // q = 17/5 in the field satisfies 17 == q*5 + 0 and r < d1:
    // only the range on q rejects it
    let q = 17 / 5;
    only_fails::<64, 128>(17, 1, 5, q, 0, 0, Q_LO);
    let _ = constrain_mul_div::<64, 128>(17, 1, 5, q, 0, 0);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn wrapped_quotient_rejected_when_narrow() {
    let q = 17 / 5;
    only_fails::<64, 64>(17, 1, 5, q, 0, 0, Q_LO);
    let _ = constrain_mul_div::<64, 64>(17, 1, 5, q, 0, 0);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn quotient_flag_cannot_be_forced_true() {
    // q = 2^64 at M = 64: claiming q_hi = 0 with q_lo = 2^64 fails
    // the 64-bit range on q_lo
    let m = two_pow::<64>();
    only_fails::<64, 64>(m, 1, 1, m, 0, 0, Q_LO);
    let _ = constrain_mul_div::<64, 64>(m, 1, 1, m, 0, 0);
}

#[test(should_fail_with = "mul_div identity")]
fn quotient_flag_cannot_be_dropped_to_low_part() {
    // q = 2^64 + 5 at M = 64: (5, 0) breaks the identity
    let m = two_pow::<64>();
    only_fails::<64, 64>(m + 5, 1, 1, 5, 0, 0, IDENTITY);
    let _ = constrain_mul_div::<64, 64>(m + 5, 1, 1, 5, 0, 0);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn quotient_flag_cannot_be_forced_false() {
    // q = 5 at M = 64 as (5 - 2^64) + 1*2^64: identity and the high
    // range hold and the flag would read false; the range on q_lo
    // rejects it
    let m = two_pow::<64>();
    only_fails::<64, 64>(5, 1, 1, 5 - m, 1, 0, Q_LO);
    let _ = constrain_mul_div::<64, 64>(5, 1, 1, 5 - m, 1, 0);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn shifted_witness_at_top_of_range_rejected() {
    // (2^64 - 1)^2 = 2^64*(2^64 - 2) + 1; the shift (q - 1, r + d1)
    // gives r = 2^64 - 1, still inside the 64-bit range on r, so
    // only r < d1 rejects it
    let m = two_pow::<64>();
    only_fails::<64, 128>(m - 1, m - 1, m - 2, m - 1, 0, m - 1, R_LT_D);
    let _ = constrain_mul_div::<64, 128>(m - 1, m - 1, m - 2, m - 1, 0, m - 1);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn whole_product_as_remainder_rejected() {
    // a*b = 2^64 - 1 over d1 = 1 claimed as q = 0, r = a*b
    let m = two_pow::<64>();
    only_fails::<64, 128>(m - 1, 1, 1, 0, 0, m - 1, R_LT_D);
    let _ = constrain_mul_div::<64, 128>(m - 1, 1, 1, 0, 0, m - 1);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn remainder_equal_to_max_divisor_rejected() {
    // (2^64 - 1) / (2^64 - 1) claimed as q = 0, r = d1
    let m = two_pow::<64>();
    only_fails::<64, 128>(m - 1, 1, m - 1, 0, 0, m - 1, R_LT_D);
    let _ = constrain_mul_div::<64, 128>(m - 1, 1, m - 1, 0, 0, m - 1);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn remainder_minus_2_pow_64_rejected() {
    // 17 = (17 + 2^64)*1 - 2^64: r fails its range and r < d1 too
    // (d1 - r - 1 = 2^64); the range on r comes first
    let m = two_pow::<64>();
    only_fails::<64, 128>(17, 1, 1, 17 + m, 0, 0 - m, R + R_LT_D);
    let _ = constrain_mul_div::<64, 128>(17, 1, 1, 17 + m, 0, 0 - m);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn quotient_flag_kept_by_remainder_rejected() {
    // a*b = 2^64 at M = 64 claimed as (2^64 - 1, 0, 1): the identity
    // and both quotient ranges hold and the flag would read true;
    // only r < d1 rejects it
    let t32 = two_pow::<32>();
    let m = two_pow::<64>();
    only_fails::<64, 64>(t32, t32, 1, m - 1, 0, 1, R_LT_D);
    let _ = constrain_mul_div::<64, 64>(t32, t32, 1, m - 1, 0, 1);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn high_quotient_part_minus_one_rejected() {
    // q_hi = p - 1 at M = 64 makes q = 3 - 2^64, and the identity
    // 17 = q*5 + r then needs r = 2 + 5*2^64: the high range rejects
    // first, the two remainder checks would too
    let m = two_pow::<64>();
    let r = 2 + 5 * m;
    only_fails::<64, 64>(17, 1, 5, 3, P_MINUS_1, r, Q_HI + R + R_LT_D);
    let _ = constrain_mul_div::<64, 64>(17, 1, 5, 3, P_MINUS_1, r);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn low_quotient_part_past_its_width_rejected() {
    // q = 2^64 + 5 at M = 64 claimed as (2^64 + 5, 0): the identity
    // holds and the flag would read true; the range on q_lo rejects
    let m = two_pow::<64>();
    only_fails::<64, 64>(m + 5, 1, 1, m + 5, 0, 0, Q_LO);
    let _ = constrain_mul_div::<64, 64>(m + 5, 1, 1, m + 5, 0, 0);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn wrapped_quotient_rejected_at_84_bits() {
    // the field inverse quotient 17/5 at the widest N, q ranged to 168
    let q = 17 / 5;
    only_fails::<84, 168>(17, 1, 5, q, 0, 0, Q_LO);
    let _ = constrain_mul_div::<84, 168>(17, 1, 5, q, 0, 0);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn wrapped_quotient_rejected_at_84_bits_narrow() {
    let q = 17 / 5;
    only_fails::<84, 84>(17, 1, 5, q, 0, 0, Q_LO);
    let _ = constrain_mul_div::<84, 84>(17, 1, 5, q, 0, 0);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn one_bit_quotient_part_rejected() {
    // M = 1: 2 = 2*1 claimed with q_lo = 2, q_hi = 0
    only_fails::<64, 1>(2, 1, 1, 2, 0, 0, Q_LO);
    let _ = constrain_mul_div::<64, 1>(2, 1, 1, 2, 0, 0);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn remainder_one_over_divisor_one_rejected() {
    // 5 = 4*1 + 1
    only_fails::<64, 128>(5, 1, 1, 4, 0, 1, R_LT_D);
    let _ = constrain_mul_div::<64, 128>(5, 1, 1, 4, 0, 1);
}

#[test(should_fail_with = "mul_div identity")]
fn largest_in_range_witness_cannot_wrap() {
    // N = 84 with every range at its maximum: q = 2^168 - 1,
    // d1 = 2^84 - 1, r = 2^84 - 2. q*d1 + r < 2^252 < p cannot wrap
    // onto a*b < 2^168, so the identity fails as a plain inequality
    let w = two_pow::<84>();
    let q = two_pow::<168>() - 1;
    only_fails::<84, 168>(w - 1, w - 1, w - 1, q, 0, w - 2, IDENTITY);
    let _ = constrain_mul_div::<84, 168>(w - 1, w - 1, w - 1, q, 0, w - 2);
}
