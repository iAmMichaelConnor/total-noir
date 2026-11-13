//! Property tests driven by nargo's fuzzer. Each test takes its inputs as
//! arguments, so they reach the library as witnesses and its constraints
//! run on them (the fuzzer executes every test both as ACIR and as
//! Brillig). Each test checks the library against a reference model: an
//! unconstrained function written without the library, on u128, Field or
//! bit-by-bit arithmetic. A test fails when the circuit is unsatisfiable
//! for some input or a value or flag disagrees with the model. The ec
//! test's model is the library's own in-circuit ladder, which uses no
//! black box, against msm_or, which does.
//!
//! Uniform inputs rarely reach the edges (an overflow boundary, a zero
//! divisor, a Field just past the width), so most tests pass each raw
//! input through a shaper driven by a fuzzed selector: the edges of the
//! width, short values, the raw input itself. The shapers are
//! unconstrained, so their outputs are witnesses too.

mod arith;
mod bitwise;
mod bounded_vec;
mod cmp;
mod collections;
mod convert;
mod ctl;
mod ec;
mod encode;
mod range;
mod signed;

global TWO_64: u128 = 0x10000000000000000;

/// 2^n as a Field, n <= 253.
pub(crate) unconstrained fn pow2(n: u32) -> Field {
    let mut r: Field = 1;
    for _ in 0..n {
        r *= 2;
    }
    r
}

/// Whether the canonical value of x is below 2^n.
pub(crate) unconstrained fn fits(x: Field, n: u32) -> bool {
    x.lt(pow2(n))
}

/// x when it is below 2^n, else 0.
pub(crate) unconstrained fn in_or_zero(x: Field, n: u32) -> Field {
    if fits(x, n) {
        x
    } else {
        0
    }
}

/// (v, true) when ok, else (0, false).
pub(crate) unconstrained fn or_zero(ok: bool, v: Field) -> (Field, bool) {
    if ok {
        (v, true)
    } else {
        (0, false)
    }
}

/// The canonical value of x as (hi, lo) halves of 128 bits. The cast
/// keeps the low 128 bits, and x - lo is then an exact multiple of 2^128.
pub(crate) unconstrained fn limbs(x: Field) -> (u128, u128) {
    let lo = x as u128;
    (((x - lo as Field) / pow2(128)) as u128, lo)
}

/// v mod 2^n for n <= 128.
unconstrained fn mod_pow2(v: u128, n: u32) -> u128 {
    if n >= 128 {
        v
    } else {
        v % ((1 as u128) << (n as u128))
    }
}

/// The low n bits of the canonical value of x, n <= 253.
pub(crate) unconstrained fn low_bits(x: Field, n: u32) -> Field {
    let (hi, lo) = limbs(x);
    if n <= 128 {
        mod_pow2(lo, n) as Field
    } else {
        (lo as Field) + (mod_pow2(hi, n - 128) as Field) * pow2(128)
    }
}

/// Bit i of the canonical value of x, i < 254.
pub(crate) unconstrained fn bit(x: Field, i: u32) -> bool {
    let (hi, lo) = limbs(x);
    let (word, j) = if i < 128 { (lo, i) } else { (hi, i - 128) };
    ((word >> (j as u128)) & 1) == 1
}

/// The canonical value of x shifted right by n bits.
pub(crate) unconstrained fn high_bits(x: Field, n: u32) -> Field {
    (x - low_bits(x, n)) / pow2(n)
}

/// a*b as (hi, lo) halves of 128 bits, schoolbook on 64-bit limbs.
pub(crate) unconstrained fn mul_wide(a: u128, b: u128) -> (u128, u128) {
    let (a0, a1, b0, b1) = (a % TWO_64, a / TWO_64, b % TWO_64, b / TWO_64);
    let (p00, p01, p10, p11) = (a0 * b0, a0 * b1, a1 * b0, a1 * b1);
    let mid = p00 / TWO_64 + p01 % TWO_64 + p10 % TWO_64;
    (p11 + p01 / TWO_64 + p10 / TWO_64 + mid / TWO_64, p00 % TWO_64 + (mid % TWO_64) * TWO_64)
}

/// hi*2^128 + lo divided by d != 0: (q_hi, q_lo, r), by long division one
/// bit at a time (the remainder is kept as a Field: 2r + 1 < 2^129).
pub(crate) unconstrained fn div_wide(hi: u128, lo: u128, d: u128) -> (u128, u128, u128) {
    let df = d as Field;
    let mut r: Field = 0;
    let mut q_hi: u128 = 0;
    let mut q_lo: u128 = 0;
    for i in 0..256 {
        let word = if i < 128 { hi } else { lo };
        let bit = (word >> ((127 - i % 128) as u128)) & 1;
        r = r * 2 + bit as Field;
        let take = !r.lt(df);
        if take {
            r -= df;
        }
        if i < 128 {
            q_hi = q_hi * 2 + take as u128;
        } else {
            q_lo = q_lo * 2 + take as u128;
        }
    }
    (q_hi, q_lo, r as u128)
}

/// A bit length in 0..=n: step j of the given number of steps.
unconstrained fn length_of(j: u8, steps: u32, n: u32) -> u32 {
    ((j as u32) * (n + 1)) / steps
}

/// An input for an n-bit Field parameter, chosen by sel: 0, 1, 2^n - 1,
/// 2^n, 2^n + 1, p - 1, a short value (the low bits of x, of a length
/// picked by sel), 2^n - 1 minus a short value, x mod 2^n, or x itself.
pub(crate) unconstrained fn shape(sel: u8, x: Field, n: u32) -> Field {
    let m = pow2(n);
    let short = low_bits(x, length_of(sel / 10, 26, n));
    let k = sel % 10;
    if k == 0 {
        0
    } else if k == 1 {
        1
    } else if k == 2 {
        m - 1
    } else if k == 3 {
        m
    } else if k == 4 {
        m + 1
    } else if k == 5 {
        0 - 1
    } else if k == 6 {
        short
    } else if k == 7 {
        m - 1 - short
    } else if k == 8 {
        low_bits(x, n)
    } else {
        x
    }
}

/// An n-bit unsigned input (n <= 128), as a Field, chosen by sel: 0, 1, 2,
/// 2^n - 1, 2^n - 2, a short value, 2^n - 1 minus a short value, or x
/// itself (x is below 2^n).
pub(crate) unconstrained fn shape_u(sel: u8, x: Field, n: u32) -> Field {
    let m = pow2(n);
    let short = low_bits(x, length_of(sel / 8, 32, n));
    let k = sel % 8;
    if k == 0 {
        0
    } else if k == 1 {
        1
    } else if k == 2 {
        2
    } else if k == 3 {
        m - 1
    } else if k == 4 {
        m - 2
    } else if k == 5 {
        short
    } else if k == 6 {
        m - 1 - short
    } else {
        x
    }
}

/// An n-bit signed input, as its real value (negative values as p - |v|),
/// chosen by sel: MIN, -1, 0, 1, MAX, a short value of either sign, MAX
/// minus a short value, MIN plus a short value, or x itself (x is in
/// range).
pub(crate) unconstrained fn shape_s(sel: u8, x: Field, n: u32) -> Field {
    let h = pow2(n - 1);
    let short = low_bits(x, length_of(sel / 10, 26, n - 1));
    let k = sel % 10;
    if k == 0 {
        0 - h
    } else if k == 1 {
        0 - 1
    } else if k == 2 {
        0
    } else if k == 3 {
        1
    } else if k == 4 {
        h - 1
    } else if k == 5 {
        short
    } else if k == 6 {
        0 - short
    } else if k == 7 {
        h - 1 - short
    } else if k == 8 {
        short - h
    } else {
        x
    }
}

/// Values as exact Fields, for the models: the native integer types,
/// bool and Field.
pub(crate) trait Num {
    /// The value, a negative one as p - |v|.
    fn real(self) -> Field;
    /// The value whose real value is r (r in range).
    fn from_real(r: Field) -> Self;
    /// The least and greatest values, as real values.
    fn bounds() -> (Field, Field);
}

impl Num for u8 {
    fn real(self) -> Field {
        self as Field
    }
    fn from_real(r: Field) -> Self {
        r as u8
    }
    fn bounds() -> (Field, Field) {
        (0, 0xff)
    }
}

impl Num for u16 {
    fn real(self) -> Field {
        self as Field
    }
    fn from_real(r: Field) -> Self {
        r as u16
    }
    fn bounds() -> (Field, Field) {
        (0, 0xffff)
    }
}

impl Num for u32 {
    fn real(self) -> Field {
        self as Field
    }
    fn from_real(r: Field) -> Self {
        r as u32
    }
    fn bounds() -> (Field, Field) {
        (0, 0xffffffff)
    }
}

impl Num for u64 {
    fn real(self) -> Field {
        self as Field
    }
    fn from_real(r: Field) -> Self {
        r as u64
    }
    fn bounds() -> (Field, Field) {
        (0, 0xffffffffffffffff)
    }
}

impl Num for u128 {
    fn real(self) -> Field {
        self as Field
    }
    fn from_real(r: Field) -> Self {
        r as u128
    }
    fn bounds() -> (Field, Field) {
        (0, 0xffffffffffffffffffffffffffffffff)
    }
}

// Signed: the bit pattern read as unsigned, minus 2^N when negative; and
// back through the pattern of r + 2^N.

impl Num for i8 {
    fn real(self) -> Field {
        let p = (self as u8) as Field;
        if self < 0 {
            p - 0x100
        } else {
            p
        }
    }
    fn from_real(r: Field) -> Self {
        ((r + 0x100) as u8) as i8
    }
    fn bounds() -> (Field, Field) {
        (0 - 0x80, 0x7f)
    }
}

impl Num for i16 {
    fn real(self) -> Field {
        let p = (self as u16) as Field;
        if self < 0 {
            p - 0x10000
        } else {
            p
        }
    }
    fn from_real(r: Field) -> Self {
        ((r + 0x10000) as u16) as i16
    }
    fn bounds() -> (Field, Field) {
        (0 - 0x8000, 0x7fff)
    }
}

impl Num for i32 {
    fn real(self) -> Field {
        let p = (self as u32) as Field;
        if self < 0 {
            p - 0x100000000
        } else {
            p
        }
    }
    fn from_real(r: Field) -> Self {
        ((r + 0x100000000) as u32) as i32
    }
    fn bounds() -> (Field, Field) {
        (0 - 0x80000000, 0x7fffffff)
    }
}

impl Num for i64 {
    fn real(self) -> Field {
        let p = (self as u64) as Field;
        if self < 0 {
            p - 0x10000000000000000
        } else {
            p
        }
    }
    fn from_real(r: Field) -> Self {
        ((r + 0x10000000000000000) as u64) as i64
    }
    fn bounds() -> (Field, Field) {
        (0 - 0x8000000000000000, 0x7fffffffffffffff)
    }
}

impl Num for bool {
    fn real(self) -> Field {
        self as Field
    }
    fn from_real(r: Field) -> Self {
        r != 0
    }
    fn bounds() -> (Field, Field) {
        (0, 1)
    }
}

impl Num for Field {
    fn real(self) -> Field {
        self
    }
    fn from_real(r: Field) -> Self {
        r
    }
    fn bounds() -> (Field, Field) {
        (0, 0 - 1)
    }
}

/// An N-bit unsigned input of type T chosen by sel (see shape_u).
pub(crate) unconstrained fn pick_u<T: Num, let N: u32>(sel: u8, x: T) -> T {
    T::from_real(shape_u(sel, x.real(), N))
}

/// An N-bit signed input of type T chosen by sel (see shape_s).
pub(crate) unconstrained fn pick_s<T: Num, let N: u32>(sel: u8, x: T) -> T {
    T::from_real(shape_s(sel, x.real(), N))
}
