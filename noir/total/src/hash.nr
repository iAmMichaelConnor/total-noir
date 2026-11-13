//! Poseidon2 hashing that reproduces Aztec's digests, variable-length
//! SHA-256 and Keccak-256 with a flagged length, and the totality status
//! of the other hash functions std exposes.
//!
//! # Poseidon2 construction
//!
//! The sponge Aztec uses: state width 4, rate 3, capacity 1. The capacity
//! element starts as iv = L * 2^64, where L is the number of absorbed
//! elements. Elements are added into state[0..3] three at a time with a
//! permutation after each full block. A trailing partial block, or the
//! empty input, is added and permuted once more; a length that is a
//! positive multiple of 3 gets no extra permutation. The digest is
//! state[0].
//!
//! Source matched: Aztec's protocol_types crate, crates/types/src/hash.nr
//! (poseidon2_hash, poseidon2_hash_with_separator,
//! poseidon2_hash_subarray, poseidon2_hash_subarray_with_separator). Those
//! call noir-lang/poseidon v0.4.0 poseidon2::Poseidon2::hash(input, len);
//! aztec-nr pins poseidon v0.3.0, whose Poseidon2::hash is the same code.
//! protocol_types' own Poseidon2Sponge (crates/types/src/poseidon2.nr) is
//! the same construction in absorb/squeeze form, and Sponge below follows
//! it. This module re-implements the construction over
//! std::hash::poseidon2_permutation rather than depending on
//! noir-lang/poseidon. The tests pin it to digests taken from those sources:
//! Aztec's TypeScript-generated siloing vectors, an Aztec note-hash
//! vector, and the noir-lang/poseidon test vectors.
//!
//! The Poseidon2Hasher inside std (nargo 1.0.0-rc.3) is pub(crate) and only
//! reachable from comptime code. It is not Aztec-compatible: it always
//! runs a final permutation, so for lengths that are a positive multiple
//! of 3 it gives a different digest. Do not use it as a reference.
//!
//! # Why the Poseidon2 entries are total
//!
//! std::hash::poseidon2_permutation(input: [Field; 4]) is a static_assert
//! on the width (compile time) followed by the #[foreign] black box. In
//! ACIR it is one BlackBoxFuncCall Poseidon2Permutation: its four outputs
//! are fresh witnesses the ACVM computes from any four inputs, and the
//! backend constrains them to the permutation, which holds for every
//! input. It has no range or input-validity condition. The sponge logic
//! around it is additions of field elements and products with constants
//! or with determined bool flags. So p2_hash, p2_hash_sep and Sponge emit
//! only definitions, and p2_hash_var_or and p2_hash_sep_var_or add only the
//! collections::prefix_mask_or gadgets (eq gadgets, hint-satisfiable for
//! every length). None of them emits a RANGE or memory opcode.
//!
//! Unrolled loop indices, numeric generics, and arithmetic or casts to
//! Field on them are compile-time constants and emit no constraint.
//!
//! # Other hash functions in std
//!
//! Every other public hash function in std::hash, with its status. None
//! needs a wrapper; the reason is given per row.
//!
//! | std::hash function | Total as is? |
//! |---|---|
//! | sha256_compression([u32; 16], [u32; 8]) | Yes: one black box; its 32-bit input condition holds by the type |
//! | keccakf1600([u64; 25]) | Yes: one black box; 64-bit inputs by the type |
//! | blake2s::<N>([u8; N]) | Yes: one black box; 8-bit inputs by the type |
//! | blake3::<N>([u8; N]) | Yes for N <= 1024: one black box; its static_assert N <= 1024 is a compile-time check, and bb cannot prove N > 1024 (a proving limit, not an input condition) |
//! | pedersen_hash, pedersen_hash_with_separator ([Field; N]) | Yes: each input becomes a scalar through EmbeddedCurveScalar::from_field (always below the Grumpkin order, since p < q), the generators are compile-time constants on the curve, and the separator must be a compile-time constant (assert_constant, a compile error otherwise); the one MSM black box then sees only inputs its solver accepts. In bb 6.0.0 its bases are those constants, so no input can be placed in relation to the MSM gadget's offset generators (ec::msm_or): an input with no proof would need a discrete-log relation between them and the hashed generators |
//! | pedersen_commitment, pedersen_commitment_with_separator ([Field; N]) | Yes, by the same argument (one MSM on derived generators and from_field scalars) |
//! | derive_generators | Yes: both arguments must be compile-time constants; it emits no constraint |
//! | poseidon2_permutation([Field; 4]) | Yes: used by every Poseidon2 entry here (section above) |
//!
//! The black boxes compute their outputs for every input value and add no
//! RANGE opcode of their own. The trust-boundary hazard is the typing
//! itself: an entry-point parameter of type [u8; N] gets an
//! input-falsifiable 8-bit range check per byte. Take bytes as Field at the
//! boundary and convert each with a flagging conversion (convert.nr)
//! before calling these.
//!
//! # SHA-256 and Keccak-256 over a message
//!
//! sha256 over a message and keccak256 are not in std. They live in the
//! noir-lang/sha256 (v0.3.0) and noir-lang/keccak256 (v0.1.3) libraries.
//! Their fixed-length forms are total as they stand: sha256::digest(msg)
//! and sha256::sha256(msg) call sha256_var(msg, N), whose one assert
//! message_size <= N then holds by construction, and
//! keccak256::keccak256(input, N) with the constant length N meets its
//! assert N >= message_size the same way. So this module does not wrap
//! them; call them with a full array. Their variable-length forms assert
//! on a runtime length: sha256::sha256_var(msg, message_size) asserts
//! message_size <= N, and keccak256(input, message_size) asserts
//! N >= message_size. sha256_var_or and keccak256_var_or here take the
//! length as a Field, flag it, and call the library on a clamped length (0
//! when the flag fails), so the assert always holds. Every other constraint
//! either library emits holds for every byte array once the length is at
//! most N; each entry's doc comment lists them. Bytes past the length
//! reach no constraint.
//!
//! Neither entry runs in co-noir's witness extension
//! (docs/co-noir.md): sha256's block-packing and length hints
//! use integer shifts, and co-noir neither solves nor proves the
//! keccakf1600 black box that keccak256 is built on. With sqrt_or and the
//! ecdsa entries, they are the library's co-noir exceptions.
//!
//! On ok = false every flagged entry here returns the zero value: the
//! Field 0 for the Poseidon2 forms and 32 zero bytes for the byte digests.

use crate::cmp::lte;
use crate::collections::prefix_mask_or;
use crate::core::{eq, select_field, TWO_POW_64};
use crate::ctl::Select;
use std::hash::poseidon2_permutation;

/// Poseidon2 digest of exactly N field elements; equals Aztec's
/// protocol_types poseidon2_hash(input) for every N, including N = 0.
///
/// Unrolled at compile time: N / 3 full blocks, each three additions and
/// one permutation; then the trailing partial block and one more
/// permutation when N % 3 != 0 or N = 0. Emits only permutation black
/// boxes and additions: definitions, no failure source. Cost: ceil(N / 3)
/// permutations, or one for N = 0.
pub fn p2_hash<let N: u32>(input: [Field; N]) -> Field {
    let mut state: [Field; 4] = [0, 0, 0, (N as Field) * TWO_POW_64];
    for c in 0..(N / 3) {
        state[0] += input[3 * c];
        state[1] += input[3 * c + 1];
        state[2] += input[3 * c + 2];
        state = poseidon2_permutation(state);
    }
    let tail = N % 3;
    for i in 0..tail {
        state[i] += input[N - tail + i];
    }
    if (N == 0) | (tail != 0) {
        state = poseidon2_permutation(state);
    }
    state[0]
}

/// Domain-separated Poseidon2: the digest of [sep, input[0], ...,
/// input[N-1]], length N + 1. This is Aztec's convention in
/// protocol_types hash.nr poseidon2_hash_with_separator: the separator is
/// prepended as one more element and counts toward the length in the iv.
/// Pass Aztec's u32 DOM_SEP__ constants as Fields.
///
/// Same constraint set as p2_hash::<N + 1>: definitions only, no failure
/// source, for every input and every separator value. Cost:
/// ceil((N + 1) / 3) permutations.
pub fn p2_hash_sep<let N: u32>(input: [Field; N], sep: Field) -> Field {
    let mut full = [0; N + 1];
    full[0] = sep;
    for i in 0..N {
        full[i + 1] = input[i];
    }
    p2_hash(full)
}

/// Masked absorption core shared by the variable-length entries. mask
/// must be a prefix mask (true then false); the length absorbed is its
/// popcount len1. The result is the Poseidon2 digest of the first len1
/// elements.
///
/// Chunk c covers positions 3c, 3c + 1, 3c + 2. Each chunk adds its
/// masked elements and permutes. The digest is taken from the chunk that
/// holds the last absorbed element (chunk 0 when len1 = 0), selected by
/// f_c = lower_c - upper_c with lower_0 = 1, lower_c = mask[3c] for
/// c >= 1, and upper_c = mask[3c + 3] (0 past the end). For a prefix mask
/// exactly one f_c is 1: the sum telescopes to 1. Chunks before the final
/// one are fully masked in, so their state equals the fixed-length
/// sponge's; the final chunk absorbs the tail and permutes once, as the
/// fixed-length sponge does (a full final chunk takes no extra
/// permutation there either). Chunks after it absorb nothing that
/// reaches the digest.
///
/// Constraints: ceil(M / 3) permutations (at least one) and arithmetic.
/// No failure source: any mask gives a defined digest.
fn p2_hash_masked<let M: u32>(input: [Field; M], mask: [bool; M]) -> Field {
    let mut len1: Field = 0;
    for j in 0..M {
        len1 += mask[j] as Field;
    }
    let mut state: [Field; 4] = [0, 0, 0, len1 * TWO_POW_64];
    let chunks = if M == 0 { 1 } else { (M + 2) / 3 };
    let mut digest: Field = 0;
    for c in 0..chunks {
        for i in 0..3 {
            let j = 3 * c + i;
            if j < M {
                state[i] += (mask[j] as Field) * input[j];
            }
        }
        state = poseidon2_permutation(state);
        let lower: Field = if c == 0 { 1 } else { mask[3 * c] as Field };
        let upper: Field = if 3 * c + 3 < M {
            mask[3 * c + 3] as Field
        } else {
            0
        };
        digest += (lower - upper) * state[0];
    }
    digest
}

/// Poseidon2 digest of the first len elements of input, with the length
/// flagged: returns (digest, ok) with ok = (len <= N).
///
/// len1 = len when ok, else 0. The digest is Aztec's
/// Poseidon2::hash(input, len1), the value of protocol_types
/// poseidon2_hash_subarray(input, len1): iv = len1 * 2^64, elements at
/// positions >= len1 are ignored whatever their values. So on ok = true
/// it equals p2_hash of the first len elements. On ok = false the digest
/// is 0 (the zero value; no Poseidon2 digest of a short input is known to
/// be 0). The length is part of the digest
/// through the iv, so a prover lying about len changes the digest; it
/// never makes the circuit unsatisfiable.
///
/// Constraints: prefix_mask_or::<N> (N + 1 eq gadgets, hint-satisfiable for
/// every Field len, determined) and the masked absorption
/// (definitions), and one select to 0. Total for every input; ok is
/// determined. Cost: N + 1 eq gadgets and ceil(N / 3) permutations (one
/// for N = 0).
pub fn p2_hash_var_or<let N: u32>(input: [Field; N], len: Field) -> (Field, bool) {
    let (mask, ok) = prefix_mask_or::<N>(len);
    (select_field(ok, p2_hash_masked(input, mask), 0), ok)
}

/// Domain-separated variable-length Poseidon2: the digest of [sep]
/// followed by the first len elements of input, with ok = (len <= N).
/// Matches protocol_types poseidon2_hash_subarray_with_separator(input,
/// len, sep), which equals poseidon2_hash_with_separator over the prefix.
///
/// The length mask is computed on len itself, not on len + 1, so a len
/// near p cannot wrap into range. On ok = false the digest is 0.
/// Constraints and totality as p2_hash_var_or. Cost: N + 1 eq gadgets and ceil((N + 1) / 3)
/// permutations.
pub fn p2_hash_sep_var_or<let N: u32>(input: [Field; N], len: Field, sep: Field) -> (Field, bool) {
    let (mask, ok) = prefix_mask_or::<N>(len);
    let mut full = [0; N + 1];
    let mut full_mask = [true; N + 1];
    full[0] = sep;
    for i in 0..N {
        full[i + 1] = input[i];
        full_mask[i + 1] = mask[i];
    }
    (select_field(ok, p2_hash_masked(full, full_mask), 0), ok)
}

/// An incremental Poseidon2 sponge with Aztec's absorb/squeeze behaviour
/// (protocol_types Poseidon2Sponge). POS is the number of cached
/// elements, 0..=3, carried in the type, so every position decision is
/// made at compile time.
///
/// Usage: Sponge::new(iv).absorb(a).absorb_array(xs).squeeze(). With
/// iv = L * 2^64 and L elements absorbed, the digest equals p2_hash of
/// those elements. Each absorb returns a sponge of a different type, so
/// an absorb under a runtime if does not type-check: choose the absorbed
/// value with Select instead, or use p2_hash_var_or for a runtime length.
/// This is what keeps the sponge free of runtime position state (the
/// u32 cache counter of Aztec's sponge becomes a witness under a runtime
/// branch and then costs a permutation per absorb).
///
/// squeeze consumes the sponge and permutes once; there is no squeeze
/// mode and no assert. Squeezing a copy twice gives the same digest.
pub struct Sponge<let POS: u32> {
    state: [Field; 4],
    cache: [Field; 3],
}

impl Sponge<0> {
    /// Empty sponge with capacity element iv. Constants and one input;
    /// no constraint.
    pub fn new(iv: Field) -> Sponge<0> {
        Sponge { state: [0, 0, 0, iv], cache: [0; 3] }
    }
}

impl<let POS: u32> Sponge<POS> {
    /// Absorb one element. When the cache is full (POS = 3) the cache is
    /// added into the state and permuted first. Position logic is
    /// resolved at compile time. Emits at most one permutation and three
    /// additions: definitions, no failure source.
    pub fn absorb(self, x: Field) -> Sponge<POS % 3 + 1> {
        let mut state = self.state;
        let mut cache = self.cache;
        if POS == 3 {
            for i in 0..3 {
                state[i] += cache[i];
            }
            state = poseidon2_permutation(state);
            cache = [x, 0, 0];
        } else {
            cache[POS % 3] = x;
        }
        Sponge { state, cache }
    }

    /// Absorb M elements in order; the same as M calls to absorb. The
    /// result position, written in the type, is POS for M = 0 and
    /// ((POS + M - 1) mod 3) + 1 otherwise, spelled with operations the
    /// type checker evaluates. The loop counter is a compile-time
    /// integer, so no integer witness reaches the circuit. Emits one
    /// permutation per three elements absorbed past a full cache, plus
    /// additions: definitions, no failure source.
    pub fn absorb_array<let M: u32>(
        self,
        xs: [Field; M],
    ) -> Sponge<POS + M + 3 - 3 * ((POS + M + 2) / 3) - 3 * (1 / (POS + M + 1))> {
        let mut state = self.state;
        let mut cache = self.cache;
        let mut pos = POS;
        for k in 0..M {
            if pos == 3 {
                for i in 0..3 {
                    state[i] += cache[i];
                }
                state = poseidon2_permutation(state);
                cache = [xs[k], 0, 0];
                pos = 1;
            } else {
                cache[pos] = xs[k];
                pos += 1;
            }
        }
        Sponge { state, cache }
    }

    /// Add the POS cached elements into the state, permute, and return
    /// state[0]. Emits one permutation and up to three additions:
    /// definitions, no failure source.
    pub fn squeeze(self) -> Field {
        let mut state = self.state;
        for i in 0..3 {
            if i < POS {
                state[i] += self.cache[i];
            }
        }
        poseidon2_permutation(state)[0]
    }
}

/// The flagged byte length shared by sha256_var_or and keccak256_var_or:
/// (len1, ok) with ok = (len <= N), len1 = len when ok, else 0.
///
/// Constraints: the cast len as u32, the compiler's truncation (a hinted
/// quotient and remainder, their range checks and the reconstruction;
/// satisfiable for every Field, and the remainder is determined); one eq
/// gadget, (l32 as Field) == len, true exactly when len < 2^32
/// (hint-satisfiable, determined); the native u32 comparison l32 <= N,
/// total on typed operands; and a u32 select (arithmetic, ctl::Select). A len at or
/// above 2^32 fails the eq, so a len that is N + 1 plus a multiple of
/// 2^32, which truncates into range, still gives ok = false. Hint rule:
/// the compiler's truncation and comparison hints and the eq gadget's
/// inverse. Determined: both flags are, and len1 is a function of len and
/// ok.
///
/// The library length goes through a truncation, not through
/// range::clamp_bits_or: a clamp_bits_or value passed to sha256::sha256_var trips
/// nargo's under-constrained Brillig warning on the library's
/// block-packing hint, which this form does not.
fn byte_len_or<let N: u32>(len: Field) -> (u32, bool) {
    let l32 = len as u32;
    let ok = eq(l32 as Field, len) & lte(l32, N);
    (u32::select(ok, l32, 0), ok)
}

/// SHA-256 of the first len bytes of input, with the length flagged:
/// returns (digest, ok) with ok = (len <= N).
///
/// Calls noir-lang/sha256 v0.3.0 sha256_var(input, len1), with len1 = len
/// when ok and len1 = 0 otherwise. On ok = true the digest is SHA-256 of
/// input[0..len]; bytes at positions >= len do not reach the digest or
/// any constraint. On ok = false it is 32 zero bytes (the library runs
/// on the empty message and its digest is masked).
///
/// Constraints: byte_len_or::<N> (determined, hint-satisfiable for every
/// Field len), then the library's own set on (input, len1), every one of
/// which holds for len1 <= N: assert(len1 <= N), which the clamp
/// guarantees; per 64-byte block, the check of the hinted u32 words
/// against the bytes below min(len1, block end) (the honest hint packs
/// exactly those bytes, and the check pins each word to them); the
/// hinted length limbs checked as 8 * len1 = lo + hi * 2^32 with u32
/// ranges (unique for 8 * len1 < 2^64); reads of the block and state
/// arrays at len1 / 64 <= N / 64, in bounds; the u32 addition of the
/// padding bit, which cannot overflow because the byte at position len1
/// in its word is zero (the block builder zeroes every byte at or past
/// len1); the sha256_compression black boxes; and to_be_bytes on u32
/// state words, which fit in four bytes. Determined: len1 is, and the
/// library pins every hinted word, so the digest is a function of the
/// first len1 bytes and len1. Last, 32 u8 selects on ok (arithmetic).
///
/// The input is typed [u8; N]: at a circuit's entry point that type adds
/// an input-falsifiable 8-bit range check per byte. Take bytes as Field
/// there and convert each with convert::to_u8_or first.
///
/// Not co-noir-safe: the library's block-packing and length hints use
/// integer shifts and bitwise AND, which co-noir's Brillig VM does not
/// run (docs/co-noir.md). The constraints are unaffected.
///
/// Cost: the length flag, plus the library's sha256_var::<N>: N / 64 + 1
/// block packings and at least N / 64 + 1 compressions.
pub fn sha256_var_or<let N: u32>(input: [u8; N], len: Field) -> ([u8; 32], bool) {
    let (len1, ok) = byte_len_or::<N>(len);
    (Select::select(ok, sha256::sha256_var(input, len1), [0; 32]), ok)
}

/// Keccak-256 (the Ethereum variant, padding byte 0x01) of the first len
/// bytes of input, with the length flagged: returns (digest, ok) with
/// ok = (len <= N).
///
/// Calls noir-lang/keccak256 v0.1.3 keccak256(input, len1), with
/// len1 = len when ok and len1 = 0 otherwise. On ok = true the digest is
/// Keccak-256 of input[0..len]; bytes at positions >= len do not reach
/// the digest or any constraint. On ok = false it is 32 zero bytes (the
/// library runs on the empty message and its digest is masked).
///
/// Constraints: byte_len_or::<N> (determined, hint-satisfiable for every
/// Field len), then the library's own set on (input, len1), every one of
/// which holds for len1 <= N: assert(N >= len1), which the clamp
/// guarantees; writes of the padding bytes into the buffer of
/// (N / 136 + 1) * 136 bytes at len1 and at r * 136 - 1, where
/// r = (len1 + 136) / 136 <= N / 136 + 1, both in bounds; u32 arithmetic
/// on len1 + 136, which does not overflow for any N whose arrays compile;
/// assert_max_bit_size::<64> on a sum of eight u8 values weighted by
/// 256^i, below 2^64 by the u8 type; the read of the intermediate state at
/// r - 1 <= N / 136, in bounds; the keccakf1600 black boxes and XOR on
/// u64 lanes (black boxes, total for typed inputs); and to_le_bytes on
/// 64-bit lanes, which fit in eight bytes. The library has no hint of its
/// own; the compiler's hints for u32 division by a constant and for
/// to_le_bytes are satisfiable for every value. Determined: len1 is, and
/// the digest is a function of the first len1 bytes and len1. Last, 32
/// u8 selects on ok (arithmetic).
///
/// The input is typed [u8; N]: at a circuit's entry point that type adds
/// an input-falsifiable 8-bit range check per byte. Take bytes as Field
/// there and convert each with convert::to_u8_or first.
///
/// Not co-noir-safe: its Brillig is clean, but co-noir neither solves nor
/// proves the keccakf1600 black box (docs/co-noir.md).
///
/// Cost: the length flag, plus the library's keccak256::<N>: N / 136 + 1
/// permutations and a dynamic read of the state at the real block count.
pub fn keccak256_var_or<let N: u32>(input: [u8; N], len: Field) -> ([u8; 32], bool) {
    let (len1, ok) = byte_len_or::<N>(len);
    (Select::select(ok, keccak256::keccak256(input, len1), [0; 32]), ok)
}

mod tests {
    use crate::core::TWO_POW_64;
    use super::{p2_hash, p2_hash_sep, p2_hash_sep_var_or, p2_hash_var_or, Sponge};
    use std::hash::poseidon2_permutation;

    global P_MINUS_1: Field = 0 - 1;
    global TWO_POW_128: Field = 0x100000000000000000000000000000000;

    // Aztec v6 domain separators (protocol_types constants.nr).
    global DOM_SEP__NOTE_HASH: Field = 116501019;
    global DOM_SEP__SILOED_NOTE_HASH: Field = 3361878420;
    global DOM_SEP__SILOED_NULLIFIER: Field = 57496191;
    global DOM_SEP__PRIVATE_LOG_FIRST_FIELD: Field = 2769976252;

    /// Reference model: protocol_types Poseidon2Sponge::hash_internal in
    /// its absorb/squeeze form, element by element with a cache counter.
    /// Structurally independent of the chunked and masked code above.
    /// Trap-free: indices are bounded by the loop and the counter.
    unconstrained fn ref_hash<let N: u32>(input: [Field; N], len: u32) -> Field {
        let mut state: [Field; 4] = [0, 0, 0, (len as Field) * TWO_POW_64];
        let mut cache: [Field; 3] = [0; 3];
        let mut cache_size: u32 = 0;
        for i in 0..N {
            if i < len {
                if cache_size == 3 {
                    for k in 0..3 {
                        state[k] += cache[k];
                    }
                    state = poseidon2_permutation(state);
                    cache[0] = input[i];
                    cache_size = 1;
                } else {
                    cache[cache_size] = input[i];
                    cache_size += 1;
                }
            }
        }
        for k in 0..3 {
            if k < cache_size {
                state[k] += cache[k];
            }
        }
        poseidon2_permutation(state)[0]
    }

    fn check_fixed<let N: u32>(input: [Field; N]) {
        // Safety: test-only reference computation.
        let expected = unsafe { ref_hash(input, N) };
        assert_eq(p2_hash(input), expected);
    }

    // Known answers from noir-lang/poseidon v0.4.0 src/tests.nr
    // (Poseidon2::hash), the library Aztec's protocol_types calls.
    #[test]
    fn kat_noir_lang_poseidon_vectors() {
        assert_eq(
            p2_hash([1000]),
            0x16433a80e26a23547e25d61dd95fd5793d1ca2dcd78ae64cd146d3b99a35fa7c,
        );
        assert_eq(
            p2_hash([1000, 2000]),
            0x118d5a5ecb25dafe99eb45cb196604a23d0b7c0cbd0c2be29e0787e59b7a1d8a,
        );
        assert_eq(
            p2_hash([1000, 2000, 3000]),
            0x0f1badcd0d52ced816fb6e6826fdf66ada038135d53cbb993f320ca6529223cd,
        );
    }

    // Known answer from std's own Poseidon2Hasher test (length 5, where
    // std and Aztec agree).
    #[test]
    fn kat_std_vector_length_5() {
        assert_eq(
            p2_hash([1, 2, 3, 4, 5]),
            0x2247be7014a54d17342a7ef677f58d28877780d203860396967f5d0a18d259db,
        );
    }

    // Known answers from Aztec protocol_types hash.nr, generated there by
    // the TypeScript implementation (yarn-project stdlib).
    #[test]
    fn kat_aztec_siloing_vectors() {
        // compute_siloed_nullifier(AztecAddress 123, 456)
        assert_eq(
            p2_hash_sep([123, 456], DOM_SEP__SILOED_NULLIFIER),
            0x169b50336c1f29afdb8a03d955a81e485f5ac7d5f0b8065673d1e407e5877813,
        );
        // compute_siloed_note_hash(AztecAddress 2, 1)
        assert_eq(
            p2_hash_sep([2, 1], DOM_SEP__SILOED_NOTE_HASH),
            0x1986a4bea3eddb1fff917d629a13e10f63f514f401bdd61838c6b475db949169,
        );
        // compute_siloed_private_log_first_field(AztecAddress 123, 456)
        assert_eq(
            p2_hash_sep([123, 456], DOM_SEP__PRIVATE_LOG_FIRST_FIELD),
            0x29480984f7b9257fded523d50addbcfc8d1d33adcf2db73ef3390a8fd5cdffaa,
        );
    }

    // Known answer for the Aztec v6 note hash and nullifier:
    // note_hash(slot 3, owner 0x1122, [0x42], randomness 0x99) =
    // P2(DOM_SEP__NOTE_HASH, slot, packed..., owner, randomness), length 5.
    #[test]
    fn kat_aztec_note_hash() {
        assert_eq(
            p2_hash_sep([3, 0x42, 0x1122, 0x99], DOM_SEP__NOTE_HASH),
            0x0a5e5fc7c279bc18cf34d40b89e636624ddca8c51bc9a009405b4ae33a5ab71a,
        );
    }

    #[test]
    fn p2_hash_matches_reference_lengths_0_to_8() {
        check_fixed([]);
        check_fixed([7]);
        check_fixed([7, 8]);
        check_fixed([7, 8, 9]);
        check_fixed([7, 8, 9, 10]);
        check_fixed([7, 8, 9, 10, 11]);
        check_fixed([7, 8, 9, 10, 11, 12]);
        check_fixed([7, 8, 9, 10, 11, 12, P_MINUS_1]);
        check_fixed([0, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn p2_hash_sep_is_prepend() {
        assert_eq(p2_hash_sep([], 42), p2_hash([42]));
        assert_eq(p2_hash_sep([1, 2, 3], 42), p2_hash([42, 1, 2, 3]));
        assert_eq(p2_hash_sep([1, 2], P_MINUS_1), p2_hash([P_MINUS_1, 1, 2]));
        assert(p2_hash_sep([1, 2], 42) != p2_hash([1, 2]));
    }

    #[test]
    fn p2_hash_var_matches_reference_every_length() {
        let input = [11, 22, 33, 44, 55, 66, P_MINUS_1];
        for l in 0..8 {
            let (h, ok) = p2_hash_var_or(input, l as Field);
            assert(ok);
            // Safety: test-only reference computation.
            let expected = unsafe { ref_hash(input, l) };
            assert_eq(h, expected);
        }
        let six = [1, 2, 3, 4, 5, 6];
        for l in 0..7 {
            let (h, ok) = p2_hash_var_or(six, l as Field);
            assert(ok);
            // Safety: test-only reference computation.
            let expected = unsafe { ref_hash(six, l) };
            assert_eq(h, expected);
        }
    }

    #[test]
    fn p2_hash_var_equals_fixed_prefix() {
        let padded = [1, 2, 3, 4, 99, 99];
        let (h4, ok4) = p2_hash_var_or(padded, 4);
        assert(ok4);
        assert_eq(h4, p2_hash([1, 2, 3, 4]));
        let (h3, ok3) = p2_hash_var_or(padded, 3);
        assert(ok3);
        assert_eq(h3, p2_hash([1, 2, 3]));
        let (h6, ok6) = p2_hash_var_or(padded, 6);
        assert(ok6);
        assert_eq(h6, p2_hash(padded));
        // zero padding does not make lengths collide: the length is in the iv
        let (a, _) = p2_hash_var_or([1, 2, 0], 2);
        let (b, _) = p2_hash_var_or([1, 2, 0], 3);
        assert(a != b);
        let (e, oke) = p2_hash_var_or([], 0);
        assert(oke);
        assert_eq(e, p2_hash([]));
    }

    #[test]
    fn p2_hash_var_length_over_n() {
        let input = [1, 2, 3, 4];
        let bad = [5, 6, 0x10000000000000000, TWO_POW_128, P_MINUS_1];
        for b in 0..5 {
            let (h, ok) = p2_hash_var_or(input, bad[b]);
            assert(!ok);
            assert_eq(h, 0);
        }
        let (h0, ok0) = p2_hash_var_or([], 1);
        assert(!ok0);
        assert_eq(h0, 0);
    }

    #[test]
    fn p2_hash_sep_var_cases() {
        let padded = [1, 2, 3, 0, 0];
        for l in 0..4 {
            let (h, ok) = p2_hash_sep_var_or(padded, l as Field, 42);
            assert(ok);
            let mut prefix = [0; 4];
            prefix[0] = 42;
            for i in 0..3 {
                prefix[i + 1] = padded[i];
            }
            // Safety: test-only reference computation.
            let expected = unsafe { ref_hash(prefix, l + 1) };
            assert_eq(h, expected);
        }
        let (h3, _) = p2_hash_sep_var_or(padded, 3, DOM_SEP__SILOED_NULLIFIER);
        assert_eq(h3, p2_hash_sep([1, 2, 3], DOM_SEP__SILOED_NULLIFIER));
        let (hk, okk) = p2_hash_sep_var_or([123, 456, 0, 0], 2, DOM_SEP__SILOED_NULLIFIER);
        assert(okk);
        assert_eq(hk, 0x169b50336c1f29afdb8a03d955a81e485f5ac7d5f0b8065673d1e407e5877813);
        // len + 1 would wrap to 0 for len = p - 1; the flag must still be false
        let bad = [6, TWO_POW_128, P_MINUS_1];
        for b in 0..3 {
            let (h, ok) = p2_hash_sep_var_or(padded, bad[b], 42);
            assert(!ok);
            assert_eq(h, 0);
        }
    }

    #[test]
    fn sponge_matches_fixed_hash() {
        let xs = [1, 2, 3, 4, 5, 6, 7];
        let iv = 7 * TWO_POW_64;
        let one_by_one = Sponge::new(iv)
            .absorb(1)
            .absorb(2)
            .absorb(3)
            .absorb(4)
            .absorb(5)
            .absorb(6)
            .absorb(7)
            .squeeze();
        assert_eq(one_by_one, p2_hash(xs));
        let split =
            Sponge::new(iv).absorb_array([1, 2]).absorb_array([3, 4, 5, 6]).absorb(7).squeeze();
        assert_eq(split, p2_hash(xs));
        let whole = Sponge::new(iv).absorb_array(xs).squeeze();
        assert_eq(whole, p2_hash(xs));
        let three = Sponge::new(3 * TWO_POW_64).absorb_array([1, 2, 3]).squeeze();
        assert_eq(three, p2_hash([1, 2, 3]));
        assert_eq(Sponge::new(0).squeeze(), p2_hash([]));
    }

    #[test]
    fn sponge_empty_arrays_keep_position() {
        let a = Sponge::new(0).absorb_array([]).absorb(9).squeeze();
        assert_eq(a, Sponge::new(0).absorb(9).squeeze());
        let b = Sponge::new(0).absorb(1).absorb_array([]).absorb(2).squeeze();
        assert_eq(b, Sponge::new(0).absorb(1).absorb(2).squeeze());
        let c = Sponge::new(0).absorb_array([1, 2, 3]).absorb_array([]).absorb(4).squeeze();
        assert_eq(c, Sponge::new(0).absorb(1).absorb(2).absorb(3).absorb(4).squeeze());
    }

    // Aztec's poseidon2_hash_with_separator_bounded_vec uses the sponge
    // this way: iv counts the separator, which is absorbed first.
    #[test]
    fn sponge_with_separator_matches_aztec_vector() {
        let h = Sponge::new(3 * TWO_POW_64)
            .absorb(DOM_SEP__SILOED_NULLIFIER)
            .absorb_array([123, 456])
            .squeeze();
        assert_eq(h, 0x169b50336c1f29afdb8a03d955a81e485f5ac7d5f0b8065673d1e407e5877813);
    }

    // The same code must also run as unconstrained code without traps.
    #[test]
    unconstrained fn entries_run_unconstrained() {
        assert_eq(
            p2_hash([1000, 2000, 3000]),
            0x0f1badcd0d52ced816fb6e6826fdf66ada038135d53cbb993f320ca6529223cd,
        );
        let (h, ok) = p2_hash_var_or([1, 2, 3, 4, 99], 4);
        assert(ok);
        assert_eq(h, p2_hash([1, 2, 3, 4]));
        let (hb, okb) = p2_hash_var_or([1, 2, 3, 4, 99], P_MINUS_1);
        assert(!okb);
        assert_eq(hb, 0);
        let (hs, oks) = p2_hash_sep_var_or([123, 456, 7], 2, DOM_SEP__SILOED_NULLIFIER);
        assert(oks);
        assert_eq(hs, 0x169b50336c1f29afdb8a03d955a81e485f5ac7d5f0b8065673d1e407e5877813);
        let s = Sponge::new(5 * TWO_POW_64).absorb_array([1, 2]).absorb_array([3, 4, 5]).squeeze();
        assert_eq(s, 0x2247be7014a54d17342a7ef677f58d28877780d203860396967f5d0a18d259db);
    }

    // Status evidence for the std black boxes: they execute on boundary
    // values of their typed inputs and give the standard digests.
    #[test]
    fn std_blackboxes_known_answers() {
        // BLAKE2s-256("abc")
        let b2 = std::hash::blake2s("abc".as_bytes());
        assert_eq(b2[0], 0x50);
        assert_eq(b2[1], 0x8c);
        assert_eq(b2[31], 0x82);
        // BLAKE3("abc")
        let b3 = std::hash::blake3("abc".as_bytes());
        assert_eq(b3[0], 0x64);
        assert_eq(b3[1], 0x37);
        assert_eq(b3[31], 0x85);
        // One SHA-256 compression of the padded block for "abc" from the
        // standard IV gives SHA-256("abc").
        let mut block: [u32; 16] = [0; 16];
        block[0] = 0x61626380;
        block[15] = 24;
        let iv: [u32; 8] = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19,
        ];
        let h = std::hash::sha256_compression(block, iv);
        assert_eq(h[0], 0xba7816bf);
        assert_eq(h[7], 0xf20015ad);
        // Keccak-f[1600] of the zero state, first lane.
        let k = std::hash::keccakf1600([0; 25]);
        assert_eq(k[0], 0xf1258f7940e1dde7);
        // All-ones inputs run too.
        let _ = std::hash::blake2s([0xff; 64]);
        let _ = std::hash::keccakf1600([0xffffffffffffffff; 25]);
        let _ = std::hash::sha256_compression([0xffffffff; 16], [0xffffffff; 8]);
    }
}

mod byte_hash_tests {
    use super::{keccak256_var_or, sha256_var_or};

    global P_MINUS_1: Field = 0 - 1;
    global TWO_POW_32: Field = 0x100000000;

    global SHA256_EMPTY: [u8; 32] = [
        0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9,
        0x24, 0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52,
        0xb8, 0x55,
    ];
    global SHA256_ABC: [u8; 32] = [
        0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22,
        0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00,
        0x15, 0xad,
    ];
    global KECCAK256_EMPTY: [u8; 32] = [
        0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c, 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03,
        0xc0, 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b, 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85,
        0xa4, 0x70,
    ];
    global KECCAK256_ABC: [u8; 32] = [
        0x4e, 0x03, 0x65, 0x7a, 0xea, 0x45, 0xa9, 0x4f, 0xc7, 0xd4, 0x7b, 0xa8, 0x26, 0xc8, 0xd6,
        0x67, 0xc0, 0xd1, 0xe6, 0xe3, 0x3a, 0x64, 0xa0, 0x36, 0xec, 0x44, 0xf5, 0x8f, 0xa1, 0x2d,
        0x6c, 0x45,
    ];

    /// "abc" followed by 0xff bytes, which must not reach the digest.
    fn abc_then_ff<let N: u32>() -> [u8; N] {
        let mut a = [0xff; N];
        a[0] = 0x61;
        a[1] = 0x62;
        a[2] = 0x63;
        a
    }

    /// Bytes i * 37 + 11 mod 256: no zero runs, so a dropped or extra
    /// byte changes the digest.
    fn pattern<let N: u32>() -> [u8; N] {
        let mut a = [0; N];
        for i in 0..N {
            a[i] = ((i * 37 + 11) % 256) as u8;
        }
        a
    }

    fn prefix<let L: u32, let N: u32>(a: [u8; N]) -> [u8; L] {
        let mut out = [0; L];
        for i in 0..L {
            out[i] = a[i];
        }
        out
    }

    #[test]
    fn sha256_var_or_known_vectors() {
        let (d, ok) = sha256_var_or(abc_then_ff::<10>(), 3);
        assert(ok);
        assert_eq(d, SHA256_ABC);
        let (d, ok) = sha256_var_or(abc_then_ff::<10>(), 0);
        assert(ok);
        assert_eq(d, SHA256_EMPTY);
        let (d, ok) = sha256_var_or::<0>([], 0);
        assert(ok);
        assert_eq(d, SHA256_EMPTY);
    }

    #[test]
    fn sha256_var_or_out_of_range_lengths_give_zero_bytes() {
        let a = abc_then_ff::<10>();
        for len in [11, 12, TWO_POW_32, TWO_POW_32 + 3, TWO_POW_32 + 11, P_MINUS_1] {
            let (d, ok) = sha256_var_or(a, len);
            assert(!ok);
            assert_eq(d, [0; 32]);
        }
        let (d, ok) = sha256_var_or::<0>([], 1);
        assert(!ok);
        assert_eq(d, [0; 32]);
    }

    // Lengths around the 55/56-byte padding split and the block
    // boundaries, against the library's fixed-length digest of the
    // prefix (a different N, so a different block layout).
    #[test]
    fn sha256_var_matches_the_fixed_length_digest_at_block_boundaries() {
        let a = pattern::<130>();
        let (d, ok) = sha256_var_or(a, 55);
        assert(ok);
        assert_eq(d, sha256::digest(prefix::<55, 130>(a)));
        let (d, _) = sha256_var_or(a, 56);
        assert_eq(d, sha256::digest(prefix::<56, 130>(a)));
        let (d, _) = sha256_var_or(a, 63);
        assert_eq(d, sha256::digest(prefix::<63, 130>(a)));
        let (d, _) = sha256_var_or(a, 64);
        assert_eq(d, sha256::digest(prefix::<64, 130>(a)));
        let (d, _) = sha256_var_or(a, 65);
        assert_eq(d, sha256::digest(prefix::<65, 130>(a)));
        let (d, _) = sha256_var_or(a, 120);
        assert_eq(d, sha256::digest(prefix::<120, 130>(a)));
        let (d, _) = sha256_var_or(a, 128);
        assert_eq(d, sha256::digest(prefix::<128, 130>(a)));
        let (d, ok) = sha256_var_or(a, 130);
        assert(ok);
        assert_eq(d, sha256::digest(a));
    }

    #[test]
    fn sha256_var_ignores_bytes_past_len() {
        let a = pattern::<70>();
        let mut b = a;
        for i in 40..70 {
            b[i] = 0xff - a[i];
        }
        let (da, _) = sha256_var_or(a, 40);
        let (db, _) = sha256_var_or(b, 40);
        assert_eq(da, db);
        let (da, _) = sha256_var_or(a, 41);
        let (db, _) = sha256_var_or(b, 41);
        assert(da != db);
    }

    #[test]
    fn sha256_var_all_ones_full_length() {
        let (d, ok) = sha256_var_or([0xff; 64], 64);
        assert(ok);
        assert_eq(d, sha256::digest([0xff; 64]));
    }

    #[test]
    fn keccak256_var_known_vectors() {
        let (d, ok) = keccak256_var_or(abc_then_ff::<10>(), 3);
        assert(ok);
        assert_eq(d, KECCAK256_ABC);
        let (d, ok) = keccak256_var_or(abc_then_ff::<10>(), 0);
        assert(ok);
        assert_eq(d, KECCAK256_EMPTY);
        let (d, ok) = keccak256_var_or::<0>([], 0);
        assert(ok);
        assert_eq(d, KECCAK256_EMPTY);
    }

    #[test]
    fn keccak256_var_or_out_of_range_lengths_give_zero_bytes() {
        let a = abc_then_ff::<10>();
        for len in [11, 12, TWO_POW_32, TWO_POW_32 + 3, TWO_POW_32 + 11, P_MINUS_1] {
            let (d, ok) = keccak256_var_or(a, len);
            assert(!ok);
            assert_eq(d, [0; 32]);
        }
        let (d, ok) = keccak256_var_or::<0>([], 1);
        assert(!ok);
        assert_eq(d, [0; 32]);
    }

    // Lengths around the 136-byte rate, including 135, where the two
    // padding bytes share one byte (0x81), against the library's digest
    // of the prefix at its own length.
    #[test]
    fn keccak256_var_matches_the_fixed_length_digest_at_block_boundaries() {
        let a = pattern::<274>();
        let (d, ok) = keccak256_var_or(a, 135);
        assert(ok);
        assert_eq(d, keccak256::keccak256(prefix::<135, 274>(a), 135));
        let (d, _) = keccak256_var_or(a, 136);
        assert_eq(d, keccak256::keccak256(prefix::<136, 274>(a), 136));
        let (d, _) = keccak256_var_or(a, 137);
        assert_eq(d, keccak256::keccak256(prefix::<137, 274>(a), 137));
        let (d, _) = keccak256_var_or(a, 271);
        assert_eq(d, keccak256::keccak256(prefix::<271, 274>(a), 271));
        let (d, _) = keccak256_var_or(a, 272);
        assert_eq(d, keccak256::keccak256(prefix::<272, 274>(a), 272));
        let (d, ok) = keccak256_var_or(a, 274);
        assert(ok);
        assert_eq(d, keccak256::keccak256(a, 274));
    }

    #[test]
    fn keccak256_var_ignores_bytes_past_len() {
        let a = pattern::<150>();
        let mut b = a;
        for i in 100..150 {
            b[i] = 0xff - a[i];
        }
        let (da, _) = keccak256_var_or(a, 100);
        let (db, _) = keccak256_var_or(b, 100);
        assert_eq(da, db);
        let (da, _) = keccak256_var_or(a, 101);
        let (db, _) = keccak256_var_or(b, 101);
        assert(da != db);
    }

    #[test]
    fn keccak256_var_all_ones_full_length() {
        let (d, ok) = keccak256_var_or([0xff; 136], 136);
        assert(ok);
        assert_eq(d, keccak256::keccak256([0xff; 136], 136));
    }
}
