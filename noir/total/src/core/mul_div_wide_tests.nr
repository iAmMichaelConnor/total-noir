use crate::test_support::wit;
use super::{
    constrain_mul_div_wide_split, constrain_mul_div_wide_unsplit, hint_mul_div_wide,
    hint_wide_limbs, INV_TWO_POW_128, INV_TWO_POW_64, MUL_DIV_MAX_BITS, MUL_DIV_WIDE_MAX_BITS,
    mul_div_wide_split, MUL_DIV_WIDE_UNSPLIT_MAX_BITS, two_pow, TWO_POW_128, TWO_POW_64,
};

global P_MINUS_1: Field = 0 - 1;

#[test]
fn wide_inverse_constants() {
    assert_eq(INV_TWO_POW_64 * TWO_POW_64, 1);
    assert_eq(INV_TWO_POW_128 * TWO_POW_128, 1);
    assert_eq(TWO_POW_64, two_pow::<64>());
}

#[test]
fn wide_bounds() {
    // the wide range starts where the field-only identity stops
    assert_eq(MUL_DIV_MAX_BITS + 1, 85);
    assert_eq(MUL_DIV_WIDE_MAX_BITS, 128);
    // unsplit layout: |c*2^128 - G0| < 2^(N + 129) must stay below p
    assert_eq(MUL_DIV_WIDE_UNSPLIT_MAX_BITS + 129, 253);
    assert(two_pow::<253>().lt(P_MINUS_1));
}

/// [a, b, d, q mod 2^128, q >> 128, a*b mod d] from a reference
/// implementation (Python integers, seed 128): four rows near 2^N - 1,
/// two with small divisors, (2^N - 1)^2 over 1 and over 2^N - 2, the
/// rest uniform.
global REF_96: [[Field; 6]; 16] = [
    [
        0xfffffffffffffffffffffc3d,
        0xfffffffffffffffffffffc9a,
        0x82f2681e67d9849f3c94f8e1,
        0x1f47a489244b67ea0436acbe4,
        0x0,
        0x7111b1d8bc13fb1f9dab54e,
    ],
    [
        0xfffffffffffffffffffffe8b,
        0xffffffffffffffffffffff76,
        0xfc377c61075dce9e7bb2dae4,
        0x103d70ab8f0e106e0ea1074f0,
        0x0,
        0xb80e161e3f70649ce6e44352,
    ],
    [
        0xffffffffffffffffffffff62,
        0xfffffffffffffffffffffeb9,
        0x40699a838a1d921ca352a3c4,
        0x3f97129f3b7dfe6cc42ac3ecb,
        0x0,
        0xd21da0c9b1891cdea1f7566,
    ],
    [
        0xfffffffffffffffffffffd7b,
        0xfffffffffffffffffffffd53,
        0xe46ab5adb68f9c7d936d4748,
        0x11ee9ff6e263d099cdb1ec7c6,
        0x0,
        0xbf65b9c40c309e9d14a8a431,
    ],
    [
        0xd7273a2f5b2495d1eb090346,
        0xadac784269d0dfa3591bebee,
        0x35f,
        0xba6277b112e479c2d11f66ec976c803c,
        0x2b4c5f7167be61,
        0x2d0,
    ],
    [
        0x6c5ddceb914fe099cdc10bff,
        0xd5e9098ecd1868510a18d7bf,
        0x2f4,
        0x66cd64a7ec714fbb137148cac4fc9e2c,
        0x1ea9905a035f2a,
        0x251,
    ],
    [
        0xffffffffffffffffffffffff,
        0xffffffffffffffffffffffff,
        0x1,
        0xfffffffe000000000000000000000001,
        0xffffffffffffffff,
        0x0,
    ],
    [
        0xffffffffffffffffffffffff,
        0xffffffffffffffffffffffff,
        0xfffffffffffffffffffffffe,
        0x1000000000000000000000000,
        0x0,
        0x1,
    ],
    [
        0x1e7871573f78b92241dcce7,
        0xcea787f97c475f39511e86f4,
        0xef9ea35bc8b63db9c4506aec,
        0x1a474f7434f489ca7dffe10,
        0x0,
        0x25072ea532de5bf2f9095f6c,
    ],
    [
        0x91251db5e9cfdffa1ced8f42,
        0xc9d231898beda2521296de33,
        0xdeb992bdca5d4f3dda5bc2c6,
        0x8385bcea14db391883076cb5,
        0x0,
        0x6e75a93978e46dba9bc48828,
    ],
    [
        0x8d1142fb85b743b111cefb01,
        0x59cd2ac26390b66a49bf4805,
        0x7da9149d8085eca10f10ab9,
        0x64cfd1a2918fd2e569165868d,
        0x0,
        0x6b5c744173e0a669a057120,
    ],
    [
        0x5d5b0fcc3746450181e92b5b,
        0xf3cba123b6fe91ffe181dee1,
        0xc8b11730c3e536ae5bc1195,
        0x7167fe7435cd8f3e63a0634cb,
        0x0,
        0xa3b7ffdf458ff89aa30cfd4,
    ],
    [
        0x99839b5a05b6fda88df1a0bf,
        0xc9f32479a94a0718df65d766,
        0xdaeb0c1e70abb56564410cdc,
        0x8d9d7d0ff356a7e95fc7c745,
        0x0,
        0x48efda89068a66cc0f15f9ce,
    ],
    [
        0x766aea75b7149cb2df051e2d,
        0x5199af74af3b9ee1cefdd24d,
        0x3ca8a527897304403a33237b,
        0x9f4cb3ca4539a31b03c7085c,
        0x0,
        0x18e2314fdd063f98c6aa6555,
    ],
    [
        0xffb3fe907433e1496dce0b1,
        0x58bce1baf60681d9f499b60a,
        0x3d08ecfce016ddadc349f789,
        0x173c37512c5029661dcbcb8d,
        0x0,
        0x1034360dc43db66ae47da375,
    ],
    [
        0x662b240bb526b391748f449f,
        0xe85cf1c2c8797d0697b302a,
        0x9faf9f935a08e4289136fe9c,
        0x94aafcf0472588b7b3b0eb2,
        0x0,
        0x225cf932e7cf6b078fa6819e,
    ],
];

global REF_124: [[Field; 6]; 8] = [
    [
        0xfffffffffffffffffffffffffffff1b,
        0xffffffffffffffffffffffffffffeea,
        0x5d9213f4f0f3bb528698772308e0ef,
        0xbc640bf3f35b183b578e27040e78e439,
        0x2,
        0x18dfe2ca8b9fb6e0811d12c8aa0777,
    ],
    [
        0xffffffffffffffffffffffffffffe18,
        0xffffffffffffffffffffffffffffc36,
        0x9776ce29dc1aceb76c536b5cac64b6,
        0xb0aef5a9eb96527aedeb908ec9a85261,
        0x1,
        0x707d04a0ec946e71ab9779ad02c41a,
    ],
    [
        0xfffffffffffffffffffffffffffff55,
        0xffffffffffffffffffffffffffffca0,
        0xff0d908bf608184315c71e9391caec4,
        0x100f355e52d275b06b1a268cdb0637ee,
        0x0,
        0xe0d8226f0bb8426e6b97289f933aae8,
    ],
    [
        0xffffffffffffffffffffffffffffd50,
        0xffffffffffffffffffffffffffffca9,
        0x7542a448c60b66fc649dd49d912c9da,
        0x22ee4ab81ffda4a43d88d10ceeb1f242,
        0x0,
        0x4769cfc981b1b85b46a25e40aa6db9c,
    ],
    [
        0x899825045fa84f718357b788402145a,
        0x48279369d50aef3d0163737e2d2ba1a,
        0x2e0,
        0x69f3eab554767f526b5d990545ef9776,
        0xd7d3d27b14c8bd68c3eab24b164,
        0x1e4,
    ],
    [
        0x5c867c41960284608431646c5579ff4,
        0x98c3d51146b979f04d876ea21447456,
        0x3e2,
        0x45d20489ee94f4367ea68522ccbbae2d,
        0xe384e9c00bf74e79f0ce71a936f,
        0x13e,
    ],
    [
        0xfffffffffffffffffffffffffffffff,
        0xfffffffffffffffffffffffffffffff,
        0x1,
        0xe0000000000000000000000000000001,
        0xffffffffffffffffffffffffffffff,
        0x0,
    ],
    [
        0xfffffffffffffffffffffffffffffff,
        0xfffffffffffffffffffffffffffffff,
        0xffffffffffffffffffffffffffffffe,
        0x10000000000000000000000000000000,
        0x0,
        0x1,
    ],
];

global REF_125: [[Field; 6]; 8] = [
    [
        0x1ffffffffffffffffffffffffffffc4f,
        0x1ffffffffffffffffffffffffffffcc7,
        0x1f090108cd2218fa2a1010b9bc27f585,
        0x20feacb404f2b9a678f6c6d2d2dba384,
        0x0,
        0x775eea1d1257225e35a1abd67569dd5,
    ],
    [
        0x1ffffffffffffffffffffffffffffdd7,
        0x1fffffffffffffffffffffffffffff94,
        0xc6e44d779b0f3a624dc7057ff973a46,
        0x52605eb2aa478bf26b0f089b7d24f439,
        0x0,
        0x8e74249eb08865cc52ddbb193f237b6,
    ],
    [
        0x1ffffffffffffffffffffffffffffea6,
        0x1fffffffffffffffffffffffffffffd7,
        0x1973e1be5917849e1ad4ec4945db3a00,
        0x283b469c59313ac2d74df9dbcf2e9aa6,
        0x0,
        0x3f75f3309e96bbd5f2f452c66f49b6a,
    ],
    [
        0x1ffffffffffffffffffffffffffffe1b,
        0x1ffffffffffffffffffffffffffffecd,
        0xfcb806a440a60fe75312cf682c93b90,
        0x40d4b84e2b87b21d4596c784d2f4e23d,
        0x0,
        0xd70930eab16a91b03e948e44a39f44f,
    ],
    [
        0xb02460aa0d87ac90cff6e757269178e,
        0x1a43fc80b96904871fb2120fcdf30e70,
        0x9c,
        0xf229f7e8aa44d903cd7d71043adda0ef,
        0x1da82925a8b090dab2789a192e81d,
        0x7c,
    ],
    [
        0x180b2b92d99f60415edbc480cd2eb130,
        0xc7220e5fdb8842529eb195e4a072d05,
        0x2b6,
        0xe3660cc546af279f15e28e240a4df837,
        0x6e62290cdc4004e0338186eac964,
        0xd6,
    ],
    [
        0x1fffffffffffffffffffffffffffffff,
        0x1fffffffffffffffffffffffffffffff,
        0x1,
        0xc0000000000000000000000000000001,
        0x3ffffffffffffffffffffffffffffff,
        0x0,
    ],
    [
        0x1fffffffffffffffffffffffffffffff,
        0x1fffffffffffffffffffffffffffffff,
        0x1ffffffffffffffffffffffffffffffe,
        0x20000000000000000000000000000000,
        0x0,
        0x1,
    ],
];

global REF_128: [[Field; 6]; 16] = [
    [
        0xfffffffffffffffffffffffffffffe13,
        0xfffffffffffffffffffffffffffffd6c,
        0x98aca184b1b690b0c1cf5261f5d72cf4,
        0xad40e7af311181da761e2a839f3a4d99,
        0x1,
        0x6b51a881d9743abf7659ebfa9e9db530,
    ],
    [
        0xfffffffffffffffffffffffffffffd00,
        0xffffffffffffffffffffffffffffffaf,
        0xd1ee581e6639e92df12a025b6514b72,
        0x82dc05157453ab98d09dfb163ac73238,
        0x13,
        0x7e68d45a50574b34327340ec3de2e10,
    ],
    [
        0xfffffffffffffffffffffffffffffcb5,
        0xffffffffffffffffffffffffffffff03,
        0xefe52cb1cff555f34898f3ca70485955,
        0x112f99f275a22195e88b5416e9180733,
        0x1,
        0x34bed7b010aa595e5301f434ea302230,
    ],
    [
        0xfffffffffffffffffffffffffffffd87,
        0xfffffffffffffffffffffffffffffe29,
        0x3e09aa3a97f6f17b111cecfa6dbf221,
        0x6394d618bbcc6ddeb2db1ebd740c9d5,
        0x42,
        0x300d49f86b88ab77ea45e963aa82e2a,
    ],
    [
        0xbee5a3c384a2fec0f69577216f78950a,
        0xfaa64d87aa5e785bc4a840366bc1b222,
        0xcc,
        0x30e940da2c56fc3dd4cffccb9e5a9504,
        0xea8ce2b16547e4c352183fce27d495,
        0x24,
    ],
    [
        0xae62fd3f45128306b42dc7534a4eeec5,
        0x7bef0ee030850536ba4339cb0d68b112,
        0xe6,
        0x1cc0178671bae0d14fbf65490f5d2045,
        0x5df78c7ed7ad31e83aaeb1668d41ab,
        0xdc,
    ],
    [
        0xffffffffffffffffffffffffffffffff,
        0xffffffffffffffffffffffffffffffff,
        0x1,
        0x1,
        0xfffffffffffffffffffffffffffffffe,
        0x0,
    ],
    [
        0xffffffffffffffffffffffffffffffff,
        0xffffffffffffffffffffffffffffffff,
        0xfffffffffffffffffffffffffffffffe,
        0x0,
        0x1,
        0x1,
    ],
    [
        0x705700b12b4e10f469621258ee4b28f3,
        0x875ed6f0b1ccf33afc8ef0102beb51d0,
        0x8b655c42d5b17b4994e3ab6d4d1d49aa,
        0x6d1880463e5de019c61b5ebe7178bd06,
        0x0,
        0x86a1ab1c9b1158e94a23e7cdcd54ec74,
    ],
    [
        0x3a86b4894f6e9e0b2650ae9a255943c9,
        0xe684f348661c4e9ac4bbf40c1158b019,
        0xb326eefc348159c5d51752b9210918c4,
        0x4b4e9c5382708bc4ea70e595375e75bf,
        0x0,
        0x8e3b304ca3add34a8d856460a856c065,
    ],
    [
        0x4684df6af2e8c5227da0e1c8da3edf30,
        0x89a23e2ab007c50658a6922f4d4351d,
        0xa1c17ac7cb6cce141fa86a86decd49cc,
        0x3c00b793d9a6f8009062ac043338167,
        0x0,
        0x360f7de3278769e42b9b655b22a7bb5c,
    ],
    [
        0x141b036fa6658b87bae199c558e13d7e,
        0xa42fc519114d44a5c3af9240daba02f9,
        0xf46940eba83c7b2ad0482edecddc25d1,
        0xd81940172b18b70dfa22171aedbf645,
        0x0,
        0xa9974949ac4e0984bae49e00bea3c439,
    ],
    [
        0x9ccc53fb8222f66de331a666c7e97fdb,
        0xf3f18e42a33ccd1d03e121f301fc6280,
        0x76716c61d660d68f1e2b6279c8a8b306,
        0x42f06d40d0f10153368407e3e2adc644,
        0x1,
        0x13c198e44bf27987dc600d3bfff191e8,
    ],
    [
        0x196cb0040c1da4b9ad61bbbca9bdb04f,
        0x58f4a8583e4d01be5d3c2848f55f9ac9,
        0xd39acf3b0264bae32faee44e7304cd6d,
        0xab0297c37f2346bb52db3a2e2e176fa,
        0x0,
        0x21f9a9fd52a990ee2230b2681a221995,
    ],
    [
        0xdac27ba14cd7e42b49275c589ef1dda6,
        0xfdb292140e11b1d0db638a3608cc126f,
        0x76f31b3aca0df48ab31cc7ed9bc22640,
        0xd292ecc9cd8eb5cea26004fdbcddcc7a,
        0x1,
        0x630bec9ac3be914b48d442fac67b8c7a,
    ],
    [
        0x69a485a2641fb090d9997b87e2707fe1,
        0xad417d285cc343ab6a4d5dfce1f15b34,
        0x8daa46b4daf47ab8e5ccdbdec7f56872,
        0x8133537244b3e3a9bca648e183dd7073,
        0x0,
        0x7e18bf90e82701d8000cc3d26ec6297e,
    ],
];

fn check_rows<let N: u32, let K: u32>(rows: [[Field; 6]; K]) {
    for i in 0..K {
        let row = rows[i];
        assert_eq(
            mul_div_wide_split::<N>(wit(row[0]), wit(row[1]), wit(row[2])),
            (row[3], row[4], row[5]),
        );
    }
}

#[test]
fn reference_rows_unsplit_96() {
    check_rows::<96, 16>(REF_96);
}

#[test]
fn reference_rows_unsplit_124() {
    check_rows::<124, 8>(REF_124);
}

#[test]
fn reference_rows_split_125() {
    check_rows::<125, 8>(REF_125);
}

#[test]
fn reference_rows_split_128() {
    check_rows::<128, 16>(REF_128);
}

#[test]
fn honest_extremes_every_layout() {
    // (2^N - 1)^2 / (2^N - 1) = 2^N - 1, and 0 * anything
    let m96 = two_pow::<96>();
    assert_eq(mul_div_wide_split::<96>(wit(m96 - 1), wit(m96 - 1), wit(m96 - 1)), (m96 - 1, 0, 0));
    assert_eq(mul_div_wide_split::<85>(wit(0), wit(7), wit(3)), (0, 0, 0));
    let m85 = two_pow::<85>();
    // (2^85 - 1) * 2 / 1 = 2^86 - 2, one limb
    assert_eq(mul_div_wide_split::<85>(wit(m85 - 1), wit(2), wit(1)), (2 * m85 - 2, 0, 0));
    let m = TWO_POW_128;
    assert_eq(mul_div_wide_split::<128>(wit(m - 1), wit(m - 1), wit(m - 1)), (m - 1, 0, 0));
    assert_eq(mul_div_wide_split::<128>(wit(m - 1), wit(1), wit(1)), (m - 1, 0, 0));
    // 2^64 * 2^64 / 1 = 2^128: q_lo 0, q_hi 1
    assert_eq(mul_div_wide_split::<128>(wit(TWO_POW_64), wit(TWO_POW_64), wit(1)), (0, 1, 0));
    assert_eq(mul_div_wide_split::<127>(wit(TWO_POW_64), wit(TWO_POW_64), wit(1)), (0, 1, 0));
    assert_eq(mul_div_wide_split::<124>(wit(TWO_POW_64), wit(TWO_POW_64), wit(1)), (0, 1, 0));
    // 5 / (2^128 - 1): remainder only
    assert_eq(mul_div_wide_split::<128>(wit(5), wit(1), wit(m - 1)), (0, 0, 5));
}

/// The hint on every triple of hostile arguments (zero divisor, the
/// field's -1, powers of two past every width, a "negative" value):
/// it must return, never trap.
#[test]
unconstrained fn hint_sweep_on_hostile_arguments() {
    let xs: [Field; 8] = [
        0,
        1,
        P_MINUS_1,
        TWO_POW_64,
        TWO_POW_128 - 1,
        TWO_POW_128,
        two_pow::<253>(),
        0 - TWO_POW_128,
    ];
    for i in 0..8 {
        for j in 0..8 {
            for k in 0..8 {
                let (q_lo, q_hi, _) = hint_mul_div_wide(xs[i], xs[j], xs[k]);
                let _ = hint_wide_limbs(xs[i], xs[j], xs[k], q_lo, q_hi);
            }
        }
    }
}

// Wrong-hint tests, unsplit layout. Six constraints; the five range
// checks fail with the compiler's one message "call to
// assert_max_bit_size", the identity with "mul_div_wide identity". So,
// as for the 84-bit gadget, each test first calls only_fails_unsplit
// with the constraints its witness violates (a check with a message
// no test expects, proving every other constraint holds), and
// should_fail_with then pins the failure to the first violated one.

global Q_LO: u32 = 1; // 1. q_lo < 2^128
global Q_HI: u32 = 2; // 2. q_hi < 2^(2N - 128)
global R: u32 = 4; // 3. r < 2^N
global R_LT_D: u32 = 8; // 4. d1 - r - 1 < 2^N
global CARRY: u32 = 16; // 5. (a*b - q_lo*d1 - r)/2^128 + 2^N < 2^(N + 1)
global IDENTITY: u32 = 32; // 6. a*b == q*d1 + r in the field

fn only_fails_unsplit<let N: u32>(
    a: Field,
    b: Field,
    d1: Field,
    q_lo: Field,
    q_hi: Field,
    r: Field,
    violated: u32,
) {
    let c = (a * b - q_lo * d1 - r) * INV_TWO_POW_128;
    let holds = [
        q_lo.lt(TWO_POW_128),
        q_hi.lt(two_pow::<2 * N - 128>()),
        r.lt(two_pow::<N>()),
        (d1 - r - 1).lt(two_pow::<N>()),
        (c + two_pow::<N>()).lt(two_pow::<N + 1>()),
        a * b == (q_lo + q_hi * TWO_POW_128) * d1 + r,
    ];
    for i in 0..6 {
        let expect_violated = ((violated >> i) & 1) == 1;
        assert(holds[i] != expect_violated, "only_fails: witness setup");
    }
}

#[test]
fn honest_unsplit_hints_pass() {
    let m = two_pow::<96>();
    // Safety: positive controls for the tests below.
    let (q_lo, q_hi, r) = unsafe { hint_mul_div_wide(m - 1, m - 1, 3) };
    only_fails_unsplit::<96>(m - 1, m - 1, 3, q_lo, q_hi, r, 0);
    constrain_mul_div_wide_unsplit::<96>(
        wit(m - 1),
        wit(m - 1),
        wit(3),
        wit(q_lo),
        wit(q_hi),
        wit(r),
    );
    constrain_mul_div_wide_unsplit::<96>(
        wit(TWO_POW_64),
        wit(TWO_POW_64),
        wit(1),
        wit(0),
        wit(1),
        wit(0),
    );
    constrain_mul_div_wide_unsplit::<96>(wit(17), wit(1), wit(5), wit(3), wit(0), wit(2));
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn unsplit_wrapped_low_quotient_rejected() {
    // q = 17/5 in the field satisfies the identity, the carry (its
    // low part a*b - q*5 is 0) and r < d1: only the range on q_lo
    let q = 17 / 5;
    only_fails_unsplit::<96>(17, 1, 5, q, 0, 0, Q_LO);
    constrain_mul_div_wide_unsplit::<96>(17, 1, 5, q, 0, 0);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn unsplit_low_limb_past_its_width_rejected() {
    // 2^64 * 2^64 = 2^128 claimed as q_lo = 2^128, q_hi = 0
    only_fails_unsplit::<96>(TWO_POW_64, TWO_POW_64, 1, TWO_POW_128, 0, 0, Q_LO);
    constrain_mul_div_wide_unsplit::<96>(TWO_POW_64, TWO_POW_64, 1, TWO_POW_128, 0, 0);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn unsplit_quotient_wrapped_by_p_times_2_pow_128_rejected() {
    // q*d1 + r = 15 + p*2^128 with d1 = 2^95 + 1: the identity holds
    // mod p, the low 128 bits match (the carry is a small integer),
    // r < d1; only the 64-bit range on q_hi (q_hi has 159 bits)
    let d1 = 0x800000000000000000000001;
    let q_lo = 0x1231ca4a04e0fd4a48bd602ddb9c6b6b;
    let q_hi = 0x60c89ce5c263405370a08b6c417176eecba14fea;
    let r = 0x7b1f02b5b7429fd2246394a4;
    only_fails_unsplit::<96>(3, 5, d1, q_lo, q_hi, r, Q_HI);
    constrain_mul_div_wide_unsplit::<96>(3, 5, d1, q_lo, q_hi, r);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn unsplit_non_integer_high_quotient_rejected() {
    // a*b = 2^64*(2^64 + 5) over d1 = 2^64: q_lo = 5 with
    // q_hi = 2^64/2^128 in the field keeps the identity, and the low
    // part a*b - 5*2^64 = 2^128 gives carry 1; only the range on q_hi
    let q_hi = TWO_POW_64 * INV_TWO_POW_128;
    only_fails_unsplit::<96>(TWO_POW_64, TWO_POW_64 + 5, TWO_POW_64, 5, q_hi, 0, Q_HI);
    constrain_mul_div_wide_unsplit::<96>(TWO_POW_64, TWO_POW_64 + 5, TWO_POW_64, 5, q_hi, 0);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn unsplit_negative_remainder_rejected() {
    // 17 = 18*1 + (p - 1): d1 - r - 1 = 1 fits; only the range on r
    only_fails_unsplit::<96>(17, 1, 1, 18, 0, P_MINUS_1, R);
    constrain_mul_div_wide_unsplit::<96>(17, 1, 1, 18, 0, P_MINUS_1);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn unsplit_remainder_past_divisor_rejected() {
    // 17 = 2*5 + 7
    only_fails_unsplit::<96>(17, 1, 5, 2, 0, 7, R_LT_D);
    constrain_mul_div_wide_unsplit::<96>(17, 1, 5, 2, 0, 7);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn unsplit_shifted_witness_at_top_of_range_rejected() {
    // (2^96 - 1)^2 = 2^96*(2^96 - 2) + 1; (q - 1, r + d1) keeps r
    // inside 96 bits, so only r < d1 rejects it
    let m = two_pow::<96>();
    only_fails_unsplit::<96>(m - 1, m - 1, m - 2, m - 1, 0, m - 1, R_LT_D);
    constrain_mul_div_wide_unsplit::<96>(m - 1, m - 1, m - 2, m - 1, 0, m - 1);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn unsplit_quotient_wrapped_by_p_rejected() {
    // q*d1 + r = 15 + p with d1 = 2^62 + 1: the identity holds mod p
    // and every range on the hints holds (q < 2^192); the low 128 bits
    // differ by p mod 2^128, so only the carry range rejects it. This
    // is the witness that stops the field-only identity at 84 bits.
    let d1 = 0x4000000000000001;
    let q_lo = 0xdafc2fabf2eb5ee534dee2721b3846b0;
    let q_hi = 0xc19139cb84c680a3;
    let r = 0xf031321d4c7b960;
    only_fails_unsplit::<96>(3, 5, d1, q_lo, q_hi, r, CARRY);
    constrain_mul_div_wide_unsplit::<96>(3, 5, d1, q_lo, q_hi, r);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn unsplit_quotient_wrapped_by_p_rejected_at_124_bits() {
    // the same at the widest unsplit N, d1 = 2^10
    let q_lo = 0x174a0cfa121e6e5c2450f87d64fc0000;
    let q_hi = 0xc19139cb84c680a6e14116da06056;
    only_fails_unsplit::<124>(3, 5, 0x400, q_lo, q_hi, 0x10, CARRY);
    constrain_mul_div_wide_unsplit::<124>(3, 5, 0x400, q_lo, q_hi, 0x10);
}

#[test(should_fail_with = "mul_div_wide identity")]
fn unsplit_wrong_high_quotient_rejected() {
    // q_hi + 1 leaves the low 128 bits (so the carry) unchanged
    let m = two_pow::<96>();
    // Safety: test of the constraint half against a perturbed hint.
    let (q_lo, q_hi, r) = unsafe { hint_mul_div_wide(m - 1, m - 1, 3) };
    only_fails_unsplit::<96>(m - 1, m - 1, 3, q_lo, q_hi + 1, r, IDENTITY);
    constrain_mul_div_wide_unsplit::<96>(m - 1, m - 1, 3, q_lo, q_hi + 1, r);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn unsplit_wrong_low_quotient_rejected() {
    // q_lo + 1 breaks the low bits and the identity; the carry is first
    let m = two_pow::<96>();
    // Safety: as above.
    let (q_lo, q_hi, r) = unsafe { hint_mul_div_wide(m - 1, m - 1, 3) };
    only_fails_unsplit::<96>(m - 1, m - 1, 3, q_lo + 1, q_hi, r, CARRY + IDENTITY);
    constrain_mul_div_wide_unsplit::<96>(m - 1, m - 1, 3, q_lo + 1, q_hi, r);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn unsplit_wrong_remainder_rejected() {
    let m = two_pow::<96>();
    // Safety: as above.
    let (q_lo, q_hi, r) = unsafe { hint_mul_div_wide(m - 1, m - 1, 3) };
    only_fails_unsplit::<96>(m - 1, m - 1, 3, q_lo, q_hi, r + 1, CARRY + IDENTITY);
    constrain_mul_div_wide_unsplit::<96>(m - 1, m - 1, 3, q_lo, q_hi, r + 1);
}

// Wrong-hint tests, split layout (N = 128). Twenty constraints: three
// per limb split (RANGE lo, RANGE hi, the reconstruction, which
// carries no message), then r, r < d1, the two carries and the
// identity, in that order.

global A_LO: u32 = 1 << 0;
global A_HI: u32 = 1 << 1;
global A_RECON: u32 = 1 << 2;
global B_LO: u32 = 1 << 3;
global B_HI: u32 = 1 << 4;
global B_RECON: u32 = 1 << 5;
global D_LO: u32 = 1 << 6;
global D_HI: u32 = 1 << 7;
global D_RECON: u32 = 1 << 8;
global QLO_LO: u32 = 1 << 9;
global QLO_HI: u32 = 1 << 10;
global QLO_RECON: u32 = 1 << 11;
global QHI_LO: u32 = 1 << 12;
global QHI_HI: u32 = 1 << 13;
global QHI_RECON: u32 = 1 << 14;
global S_R: u32 = 1 << 15;
global S_R_LT_D: u32 = 1 << 16;
global C0: u32 = 1 << 17;
global C1: u32 = 1 << 18;
global S_IDENTITY: u32 = 1 << 19;

fn only_fails_split<let N: u32>(
    a: Field,
    b: Field,
    d1: Field,
    q_lo: Field,
    q_hi: Field,
    r: Field,
    l: [Field; 10],
    violated: u32,
) {
    let xs = [a, b, d1, q_lo, q_hi];
    let mut holds = [false; 20];
    for i in 0..5 {
        holds[3 * i] = l[2 * i].lt(TWO_POW_64);
        holds[3 * i + 1] = l[2 * i + 1].lt(TWO_POW_64);
        holds[3 * i + 2] = xs[i] == l[2 * i] + l[2 * i + 1] * TWO_POW_64;
    }
    let g0 = l[0] * l[2] + (l[0] * l[3] + l[1] * l[2]) * TWO_POW_64
        - q_lo * l[4]
        - l[6] * l[5] * TWO_POW_64
        - r;
    let c0 = g0 * INV_TWO_POW_128;
    let c1 = (c0 + l[1] * l[3] - l[7] * l[5] - l[8] * l[4]) * INV_TWO_POW_64;
    holds[15] = r.lt(two_pow::<N>());
    holds[16] = (d1 - r - 1).lt(two_pow::<N>());
    holds[17] = (c0 + two_pow::<66>()).lt(two_pow::<67>());
    holds[18] = (c1 + two_pow::<66>()).lt(two_pow::<67>());
    holds[19] = a * b == (q_lo + q_hi * TWO_POW_128) * d1 + r;
    for i in 0..20 {
        let expect_violated = ((violated >> i) & 1) == 1;
        assert(holds[i] != expect_violated, "only_fails: witness setup");
    }
}

/// The honest witness for (a, b, d1), limbs included.
fn honest_split(a: Field, b: Field, d1: Field) -> (Field, Field, Field, [Field; 10]) {
    // Safety: test helper; the tests constrain what they use.
    let (q_lo, q_hi, r) = unsafe { hint_mul_div_wide(a, b, d1) };
    // Safety: as above.
    let l = unsafe { hint_wide_limbs(a, b, d1, q_lo, q_hi) };
    (q_lo, q_hi, r, l)
}

global M128: Field = 0x100000000000000000000000000000000;

#[test]
fn honest_split_hints_pass() {
    let (q_lo, q_hi, r, l) = honest_split(M128 - 1, M128 - 1, 3);
    only_fails_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, l, 0);
    constrain_mul_div_wide_split::<128>(
        wit(M128 - 1),
        wit(M128 - 1),
        wit(3),
        wit(q_lo),
        wit(q_hi),
        wit(r),
        wit(l),
    );
    let (q_lo, q_hi, r, l) = honest_split(M128 - 1, M128 - 1, M128 - 2);
    constrain_mul_div_wide_split::<128>(
        wit(M128 - 1),
        wit(M128 - 1),
        wit(M128 - 2),
        wit(q_lo),
        wit(q_hi),
        wit(r),
        wit(l),
    );
    let (q_lo, q_hi, r, l) = honest_split(0, M128 - 1, 1);
    constrain_mul_div_wide_split::<125>(
        wit(0),
        wit(M128 - 1),
        wit(1),
        wit(q_lo),
        wit(q_hi),
        wit(r),
        wit(l),
    );
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_quotient_wrapped_by_p_times_2_pow_128_rejected() {
    // q*d1 + r = 15 + p*2^128 with d1 = 2^127 + 12345: every limb in
    // range, the identity holds mod p and the low 128 bits match; the
    // next 64 bits differ, so only the middle carry rejects it. This is
    // why N = 128 needs two carries: 2^128 alone does not bound q*d1.
    let d1 = 0x80000000000000000000000000003039;
    let q_lo = 0xfc3bc95b2b20f1be2bfcf37b94440b25;
    let q_hi = 0x60c89ce5c263405370a08b6d03028c43;
    let r = 0x20ef129d38568468c7069daf3ac294d2;
    let l = [
        3,
        0,
        5,
        0,
        0x3039,
        0x8000000000000000,
        0x2bfcf37b94440b25,
        0xfc3bc95b2b20f1be,
        0x70a08b6d03028c43,
        0x60c89ce5c2634053,
    ];
    only_fails_split::<128>(3, 5, d1, q_lo, q_hi, r, l, C1);
    constrain_mul_div_wide_split::<128>(3, 5, d1, q_lo, q_hi, r, l);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_quotient_wrapped_by_p_rejected() {
    // 15 + p over d1 = 1 as q = 15 + p (it fits 256 bits): limbs and
    // identity hold; the low 128 bits differ by p mod 2^128, so only
    // the low carry rejects it
    let q_lo = 0x2833e84879b9709143e1f593f0000010;
    let q_hi = 0x30644e72e131a029b85045b68181585d;
    let l = [
        3,
        0,
        5,
        0,
        1,
        0,
        0x43e1f593f0000010,
        0x2833e84879b97091,
        0xb85045b68181585d,
        0x30644e72e131a029,
    ];
    only_fails_split::<128>(3, 5, 1, q_lo, q_hi, 0, l, C0);
    constrain_mul_div_wide_split::<128>(3, 5, 1, q_lo, q_hi, 0, l);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_quotient_wrapped_by_p_times_2_pow_192_rejected() {
    // q*d1 + r = 15 + p*2^192 with d1 = 2^128 - 1: both carries and
    // the identity hold; q needs 318 bits, so q_hi's top limb q3 has
    // 190, and only its 64-bit range rejects it
    let d1 = M128 - 1;
    let q_lo = 0xfc323b4a7181585e589836bb5aeb10ba;
    let q_hi = 0x30644e72e131a029b85045b68181585d589836bb5aeb10ba;
    let r = 0xfc323b4a7181585e589836bb5aeb10c9;
    let l = [
        3,
        0,
        5,
        0,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0x589836bb5aeb10ba,
        0xfc323b4a7181585e,
        0x589836bb5aeb10ba,
        0x30644e72e131a029b85045b68181585d,
    ];
    only_fails_split::<128>(3, 5, d1, q_lo, q_hi, r, l, QHI_HI);
    constrain_mul_div_wide_split::<128>(3, 5, d1, q_lo, q_hi, r, l);
}

#[test(should_fail_with = "mul_div_wide identity")]
fn split_wrong_top_limb_rejected() {
    // q3 + 1 (q off by 2^192) enters neither carry: only the identity
    let (q_lo, q_hi, r, l) = honest_split(M128 - 1, M128 - 1, 3);
    let mut l2 = l;
    l2[9] = l[9] + 1;
    let q_hi2 = q_hi + TWO_POW_64;
    only_fails_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi2, r, l2, S_IDENTITY);
    constrain_mul_div_wide_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi2, r, l2);
}

/// Each limb pair shifted by one unit of 2^64 (lo + 2^64, hi - 1):
/// the reconstruction still holds and lo leaves its range.
fn shifted(l: [Field; 10], pair: u32) -> [Field; 10] {
    let mut s = l;
    s[2 * pair] = l[2 * pair] + TWO_POW_64;
    s[2 * pair + 1] = l[2 * pair + 1] - 1;
    s
}

global SA: Field = 0x70000000000000005; // 5 + 7*2^64
global SB: Field = 0xb0000000000000009; // 9 + 11*2^64
global SD: Field = 0x11000000000000000d; // 13 + 17*2^64

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_shifted_a_limbs_rejected() {
    let (q_lo, q_hi, r, l) = honest_split(SA, SB, SD);
    only_fails_split::<128>(SA, SB, SD, q_lo, q_hi, r, shifted(l, 0), A_LO);
    constrain_mul_div_wide_split::<128>(SA, SB, SD, q_lo, q_hi, r, shifted(l, 0));
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_shifted_b_limbs_rejected() {
    let (q_lo, q_hi, r, l) = honest_split(SA, SB, SD);
    only_fails_split::<128>(SA, SB, SD, q_lo, q_hi, r, shifted(l, 1), B_LO);
    constrain_mul_div_wide_split::<128>(SA, SB, SD, q_lo, q_hi, r, shifted(l, 1));
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_shifted_d_limbs_rejected() {
    let (q_lo, q_hi, r, l) = honest_split(SA, SB, SD);
    only_fails_split::<128>(SA, SB, SD, q_lo, q_hi, r, shifted(l, 2), D_LO);
    constrain_mul_div_wide_split::<128>(SA, SB, SD, q_lo, q_hi, r, shifted(l, 2));
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_shifted_q_lo_limbs_rejected() {
    let (q_lo, q_hi, r, l) = honest_split(M128 - 1, M128 - 1, 3);
    only_fails_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, shifted(l, 3), QLO_LO);
    constrain_mul_div_wide_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, shifted(l, 3));
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_shifted_q_hi_limbs_rejected() {
    let (q_lo, q_hi, r, l) = honest_split(M128 - 1, M128 - 1, 3);
    only_fails_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, shifted(l, 4), QHI_LO);
    constrain_mul_div_wide_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, shifted(l, 4));
}

#[test(should_fail)]
fn split_wrong_operand_limb_rejected() {
    // a1 + 1: a's reconstruction fails (and the carries)
    let (q_lo, q_hi, r, l) = honest_split(M128 - 1, M128 - 1, 3);
    let mut l2 = l;
    l2[1] = l[1] + 1;
    only_fails_split::<128>(
        M128 - 1,
        M128 - 1,
        3,
        q_lo,
        q_hi,
        r,
        l2,
        A_HI + A_RECON + C0 + C1,
    );
    constrain_mul_div_wide_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, l2);
}

#[test(should_fail)]
fn split_wrong_divisor_limb_rejected() {
    // dh + 1: d1's reconstruction fails (and the carries)
    let (q_lo, q_hi, r, l) = honest_split(M128 - 1, M128 - 1, 3);
    let mut l2 = l;
    l2[5] = l[5] + 1;
    only_fails_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, l2, D_RECON + C0 + C1);
    constrain_mul_div_wide_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, l2);
}

#[test(should_fail)]
fn split_wrong_quotient_limb_rejected() {
    // q0 + 1 alone: only q_lo's reconstruction rejects it
    let (q_lo, q_hi, r, l) = honest_split(M128 - 1, M128 - 1, 3);
    let mut l2 = l;
    l2[6] = l[6] + 1;
    only_fails_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, l2, QLO_RECON);
    constrain_mul_div_wide_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, l2);
}

#[test(should_fail)]
fn split_wrong_high_quotient_limb_rejected() {
    // q3 + 1 alone: only q_hi's reconstruction rejects it
    let (q_lo, q_hi, r, l) = honest_split(M128 - 1, M128 - 1, 3);
    let mut l2 = l;
    l2[9] = l[9] + 1;
    only_fails_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, l2, QHI_RECON);
    constrain_mul_div_wide_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, l2);
}

// Operand limbs alone. With the other factor 0 (and q = r = 0) an
// operand's limbs reach neither carry nor the identity, so a wrong
// high limb or reconstruction violates that one constraint and no
// other: each split constraint is load-bearing in a test of its own.

global ZA: Field = 0x80000000000000000000000000003039; // 2^127 + 12345
global ZD: Field = 0x80000000000000000000000000000063; // 2^127 + 99

/// lo moved to `lo`, hi set so the reconstruction still holds in the
/// field: hi = hi + (lo_true - lo)/2^64 has about 254 bits.
fn wrapped_hi(l: [Field; 10], pair: u32, lo: Field) -> [Field; 10] {
    let mut s = l;
    s[2 * pair] = lo;
    s[2 * pair + 1] = l[2 * pair + 1] + (l[2 * pair] - lo) * INV_TWO_POW_64;
    s
}

/// One limb of the pair + 1: the reconstruction fails, the ranges hold.
fn bumped(l: [Field; 10], index: u32) -> [Field; 10] {
    let mut s = l;
    s[index] = l[index] + 1;
    s
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_wrapped_a_high_limb_rejected() {
    // a = 2^127 + 12345 over b = 0, d1 = 1: a0 = 7 and a1 wrapped;
    // only the 64-bit range on a1
    let (q_lo, q_hi, r, l) = honest_split(ZA, 0, 1);
    let l2 = wrapped_hi(l, 0, 7);
    only_fails_split::<128>(ZA, 0, 1, q_lo, q_hi, r, l2, A_HI);
    constrain_mul_div_wide_split::<128>(ZA, 0, 1, q_lo, q_hi, r, l2);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_wrapped_b_high_limb_rejected() {
    let (q_lo, q_hi, r, l) = honest_split(0, ZA, 1);
    let l2 = wrapped_hi(l, 1, 7);
    only_fails_split::<128>(0, ZA, 1, q_lo, q_hi, r, l2, B_HI);
    constrain_mul_div_wide_split::<128>(0, ZA, 1, q_lo, q_hi, r, l2);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_wrapped_divisor_high_limb_rejected() {
    // a = 0 keeps q = r = 0 for d1 = 2^127 + 99: d0 = 5, dh wrapped
    let (q_lo, q_hi, r, l) = honest_split(0, ZA, ZD);
    let l2 = wrapped_hi(l, 2, 5);
    only_fails_split::<128>(0, ZA, ZD, q_lo, q_hi, r, l2, D_HI);
    constrain_mul_div_wide_split::<128>(0, ZA, ZD, q_lo, q_hi, r, l2);
}

#[test(should_fail)]
fn split_wrong_a_limb_alone_rejected() {
    // a1 + 1 over b = 0: only a's reconstruction
    let (q_lo, q_hi, r, l) = honest_split(ZA, 0, 1);
    only_fails_split::<128>(ZA, 0, 1, q_lo, q_hi, r, bumped(l, 1), A_RECON);
    constrain_mul_div_wide_split::<128>(ZA, 0, 1, q_lo, q_hi, r, bumped(l, 1));
}

#[test(should_fail)]
fn split_wrong_b_limb_alone_rejected() {
    let (q_lo, q_hi, r, l) = honest_split(0, ZA, 1);
    only_fails_split::<128>(0, ZA, 1, q_lo, q_hi, r, bumped(l, 3), B_RECON);
    constrain_mul_div_wide_split::<128>(0, ZA, 1, q_lo, q_hi, r, bumped(l, 3));
}

#[test(should_fail)]
fn split_wrong_divisor_limb_alone_rejected() {
    // dh + 1 with a = 0: only d1's reconstruction
    let (q_lo, q_hi, r, l) = honest_split(0, ZA, ZD);
    only_fails_split::<128>(0, ZA, ZD, q_lo, q_hi, r, bumped(l, 5), D_RECON);
    constrain_mul_div_wide_split::<128>(0, ZA, ZD, q_lo, q_hi, r, bumped(l, 5));
}

#[test]
fn split_wrong_limb_witness_setups() {
    // The seven should_fail tests above carry no message to pin (a
    // reconstruction assert has none), so a wrong setup could pass
    // for a rejection; their only_fails checks run here alone.
    let (q_lo, q_hi, r, l) = honest_split(M128 - 1, M128 - 1, 3);
    let mut l2 = l;
    l2[1] = l[1] + 1;
    only_fails_split::<128>(
        M128 - 1,
        M128 - 1,
        3,
        q_lo,
        q_hi,
        r,
        l2,
        A_HI + A_RECON + C0 + C1,
    );
    let mut l3 = l;
    l3[5] = l[5] + 1;
    only_fails_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, l3, D_RECON + C0 + C1);
    let mut l4 = l;
    l4[6] = l[6] + 1;
    only_fails_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, l4, QLO_RECON);
    let mut l5 = l;
    l5[9] = l[9] + 1;
    only_fails_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r, l5, QHI_RECON);
    // the operand limbs alone, over a zero co-factor
    let (q_lo, q_hi, r, l) = honest_split(ZA, 0, 1);
    only_fails_split::<128>(ZA, 0, 1, q_lo, q_hi, r, l, 0);
    constrain_mul_div_wide_split::<128>(
        wit(ZA),
        wit(0),
        wit(1),
        wit(q_lo),
        wit(q_hi),
        wit(r),
        wit(l),
    );
    only_fails_split::<128>(ZA, 0, 1, q_lo, q_hi, r, bumped(l, 1), A_RECON);
    let (q_lo, q_hi, r, l) = honest_split(0, ZA, 1);
    only_fails_split::<128>(0, ZA, 1, q_lo, q_hi, r, l, 0);
    constrain_mul_div_wide_split::<128>(
        wit(0),
        wit(ZA),
        wit(1),
        wit(q_lo),
        wit(q_hi),
        wit(r),
        wit(l),
    );
    only_fails_split::<128>(0, ZA, 1, q_lo, q_hi, r, bumped(l, 3), B_RECON);
    let (q_lo, q_hi, r, l) = honest_split(0, ZA, ZD);
    only_fails_split::<128>(0, ZA, ZD, q_lo, q_hi, r, l, 0);
    only_fails_split::<128>(0, ZA, ZD, q_lo, q_hi, r, bumped(l, 5), D_RECON);
    constrain_mul_div_wide_split::<128>(
        wit(0),
        wit(ZA),
        wit(ZD),
        wit(q_lo),
        wit(q_hi),
        wit(r),
        wit(l),
    );
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_wrapped_low_quotient_rejected() {
    // q_lo = 17/5 in the field with q0 = 0 and q1 = q_lo/2^64: the
    // reconstruction, the carries and the identity hold; only the
    // range on q1
    let q = 17 / 5;
    let l = [17, 0, 1, 0, 5, 0, 0, q * INV_TWO_POW_64, 0, 0];
    only_fails_split::<128>(17, 1, 5, q, 0, 0, l, QLO_HI);
    constrain_mul_div_wide_split::<128>(17, 1, 5, q, 0, 0, l);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_negative_remainder_rejected() {
    let l = [17, 0, 1, 0, 1, 0, 18, 0, 0, 0];
    only_fails_split::<128>(17, 1, 1, 18, 0, P_MINUS_1, l, S_R);
    constrain_mul_div_wide_split::<128>(17, 1, 1, 18, 0, P_MINUS_1, l);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_remainder_past_divisor_rejected() {
    let l = [17, 0, 1, 0, 5, 0, 2, 0, 0, 0];
    only_fails_split::<128>(17, 1, 5, 2, 0, 7, l, S_R_LT_D);
    constrain_mul_div_wide_split::<128>(17, 1, 5, 2, 0, 7, l);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_shifted_witness_at_top_of_range_rejected() {
    // (2^128 - 1)^2 = 2^128*(2^128 - 2) + 1; (q - 1, r + d1) =
    // (2^128 - 1, 2^128 - 1): only r < d1
    let m = M128;
    // Safety: test helper.
    let l = unsafe { hint_wide_limbs(m - 1, m - 1, m - 2, m - 1, 0) };
    only_fails_split::<128>(m - 1, m - 1, m - 2, m - 1, 0, m - 1, l, S_R_LT_D);
    constrain_mul_div_wide_split::<128>(m - 1, m - 1, m - 2, m - 1, 0, m - 1, l);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_wrong_low_quotient_rejected() {
    let (q_lo, q_hi, r, _) = honest_split(M128 - 1, M128 - 1, 3);
    // Safety: test helper; the limbs of the perturbed quotient.
    let l = unsafe { hint_wide_limbs(M128 - 1, M128 - 1, 3, q_lo + 1, q_hi) };
    only_fails_split::<128>(
        M128 - 1,
        M128 - 1,
        3,
        q_lo + 1,
        q_hi,
        r,
        l,
        C0 + C1 + S_IDENTITY,
    );
    constrain_mul_div_wide_split::<128>(M128 - 1, M128 - 1, 3, q_lo + 1, q_hi, r, l);
}

#[test(should_fail_with = "call to assert_max_bit_size")]
fn split_wrong_remainder_rejected() {
    let (q_lo, q_hi, r, l) = honest_split(M128 - 1, M128 - 1, 3);
    only_fails_split::<128>(
        M128 - 1,
        M128 - 1,
        3,
        q_lo,
        q_hi,
        r + 1,
        l,
        C0 + C1 + S_IDENTITY,
    );
    constrain_mul_div_wide_split::<128>(M128 - 1, M128 - 1, 3, q_lo, q_hi, r + 1, l);
}

// The unsplit layout's carry width at the N where its rounding to a
// multiple of 14 bits changes (97/98, 111/112/113) and at its ends.

fn wide_unsplit_honest<let N: u32>() {
    let w = two_pow::<N>() - 1;
    // d1 = 1: q = (2^N - 1)^2, and q_hi = q >> 128 is the largest honest
    // high quotient
    // Safety: honest hint
    let (q_lo, q_hi, r) = unsafe { hint_mul_div_wide(w, w, 1) };
    constrain_mul_div_wide_unsplit::<N>(wit(w), wit(w), wit(1), wit(q_lo), wit(q_hi), wit(r));
    assert_eq(q_lo + q_hi * TWO_POW_128, w * w);
    assert_eq(r, 0);
    // d1 = 2^N - 1: q = 2^N - 1, q_hi = 0
    // Safety: honest hint
    let (q_lo, q_hi, r) = unsafe { hint_mul_div_wide(w, w, w) };
    constrain_mul_div_wide_unsplit::<N>(wit(w), wit(w), wit(w), wit(q_lo), wit(q_hi), wit(r));
    assert_eq((q_lo, q_hi, r), (w, 0, 0));
    // d1 = 2^(N-1)
    let h = two_pow::<N - 1>();
    // Safety: honest hint
    let (q_lo, q_hi, r) = unsafe { hint_mul_div_wide(w, w - 1, h) };
    constrain_mul_div_wide_unsplit::<N>(wit(w), wit(w - 1), wit(h), wit(q_lo), wit(q_hi), wit(r));
    assert_eq((q_lo + q_hi * TWO_POW_128) * h + r, w * (w - 1));
}

#[test]
fn unsplit_carry_widths_at_boundaries() {
    wide_unsplit_honest::<85>();
    wide_unsplit_honest::<97>();
    wide_unsplit_honest::<98>();
    wide_unsplit_honest::<111>();
    wide_unsplit_honest::<112>();
    wide_unsplit_honest::<113>();
    wide_unsplit_honest::<124>();
}

#[test(should_fail)]
fn unsplit_negative_remainder_at_124_bits_rejected() {
    // q_lo + 1 with r - 1, a negative remainder: the RANGE on r fails
    let w = two_pow::<124>() - 1;
    // Safety: wrong-hint test
    let (q_lo, q_hi, r) = unsafe { hint_mul_div_wide(w, w, 1) };
    constrain_mul_div_wide_unsplit::<124>(w, w, 1, q_lo + 1, q_hi, r - 1);
}

#[test(should_fail)]
fn unsplit_low_quotient_past_2_128_at_112_bits_rejected() {
    // move one unit of 2^128 from q_hi into q_lo: q_lo + 2^128 fails its
    // 128-bit RANGE
    let w = two_pow::<112>() - 1;
    // Safety: wrong-hint test
    let (q_lo, q_hi, r) = unsafe { hint_mul_div_wide(w, w, 3) };
    constrain_mul_div_wide_unsplit::<112>(w, w, 3, q_lo + TWO_POW_128, q_hi - 1, r);
}
