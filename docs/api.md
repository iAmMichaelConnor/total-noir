# API reference

Every public entry of `total` and `total_aztec`, by module. Each entry's doc
comment lists the constraints it emits and why its flag is determined;
`nargo doc` in `noir/total` builds the full reference. Limits are in
[limitations.md](limitations.md).

## Conventions

- A public function whose name ends in `_or` returns a tuple whose last
  element is the `ok: bool` flag: `(value, ok)`, or `(q, r, ok)` and similar.
- `::<N>` is a bit width. "Field-domain" entries take arbitrary `Field`
  inputs, flag any that do not fit `N` bits, and so are safe directly on
  untrusted inputs; the traits work on Noir's native integer types.
- On `ok = false` a value is zero (0, `false`, a zeroed array) and an updated
  container is returned unchanged, except: `truncate_or` returns the real low
  bits and dropped part; `wrapping_*_or` and `saturating_*_or` compute on each
  out-of-range input clamped to 0 (`wrapping_add_or::<8>(300, 3)` is
  `(3, false)`); `ec` entries return the point at infinity; and the
  `TotalBoundedVec` updates return an empty vector when the input vector's
  length already exceeds its capacity.
- Each entry's doc comment lists the constraints it emits and why its flag is
  determined; `nargo doc` in `noir/total` builds the full reference.

In the tables, an argument without a type is a `Field`, and `T` is the
operand's own type. The most-used entries are also re-exported at the crate
root (`total::add_or`, `total::eq`, `total::index_or`, `total::Select`,
`total::schnorr_verify`, ...; the list is in
[lib.nr](../noir/total/src/lib.nr)). `total::core` holds the gadgets the modules
are built from (`two_pow`, `limbs`, `select_field`, `is_zero`) and the
constants `TWO_POW_64`, `TWO_POW_128`, `U128_MAX_FIELD` and the
`MUL_DIV_*_MAX_BITS` widths.

## `range`: range flags

| Entry | Gives |
|---|---|
| `fits_bits::<N>(x) -> bool` | Whether `x < 2^N`, for N from 1 to 253. Replaces `assert_max_bit_size`. |
| `clamp_bits_or::<N>(x) -> (Field, bool)` | `(x, true)` if it fits, else `(0, false)`; N from 1 to 253. |
| `fits_u1(x) -> bool`, `fits_u8`, `fits_u16`, `fits_u32`, `fits_u64`, `fits_u128` | Fixed-width shorthands. |

## `convert`: casts and decompositions

| Entry | Gives |
|---|---|
| `to_u8_or(x) -> (u8, bool)` … `to_u128_or` | `Field` to a native unsigned integer, flagged when it does not fit. Replaces typed entry-point parameters. |
| `to_i8_or(x) -> (i8, bool)` … `to_i64_or` | `x` read as an N-bit two's-complement bit pattern, flagged when `x >= 2^N`: `to_i8_or(200)` is `(-56, true)`, and the Field `-1` (that is, `p - 1`) is `(0, false)`. |
| `to_i8_from_signed_or(x) -> (i8, bool)` … `to_i64_from_signed_or` | `x` read as a signed value, a negative `n` encoded as `p - n`: the Field `-1` gives `(-1, true)`; flagged outside `[MIN, MAX]`. |
| `bool_or(x) -> (bool, bool)` | `Field` to `bool`, flagged unless 0 or 1. |
| `from_bool(b: bool) -> Field`, `from_u8(x: u8)` … `from_u128`, `from_i8(x: i8)` … `from_i64`, `from_i8_signed(x: i8)` … `from_i64_signed` | Native to `Field` (always exact). `from_iN` gives the bit pattern (inverse of `to_iN_or`), `from_iN_signed` the signed value (inverse of `to_iN_from_signed_or`). |
| `x.narrow_or()` (`TotalNarrow<T>`), e.g. `let (v, ok): (u8, bool) = x.narrow_or();` | Narrowing, and every sign change between `i8` … `i64` and `u8` … `u128` (same width or not), flagged when the value is not representable. The target type comes from the annotation. |
| `truncate_or::<N>(x) -> (Field, Field, bool)` | `(low N bits, the dropped part, nothing_dropped)`, N from 1 to 253. |
| `to_le_bits_or::<N>(x) -> ([bool; N], bool)`, `to_be_bits_or::<N>`, `to_le_bytes_or::<N>(x) -> ([u8; N], bool)`, `to_be_bytes_or::<N>` | Short decompositions (N up to 253 bits, 31 bytes), flagged when the value does not fit. |
| `sgn0(x) -> bool` | Parity of the canonical value (its low bit). |
| `to_le_bits_total(x) -> [bool; 254]`, `to_be_bits_total`, `to_le_bytes_total(x) -> [u8; 32]`, `to_be_bytes_total` | Full-width canonical decompositions (cannot fail). |
| `from_le_bytes_or(bytes: [u8; 32]) -> (Field, bool)`, `from_be_bytes_or`, `from_le_bits_or(bits: [bool; 254]) -> (Field, bool)`, `from_be_bits_or` | Full-width decoding, flagged when the encoding is at or above the field modulus. |

`convert::PLO` and `convert::PHI` are the low and high 128-bit limbs of the
field modulus.

## `arith`: unsigned and Field arithmetic

| Entry | Gives |
|---|---|
| `TotalArith`: `a.add_or(b) -> (T, bool)`, `sub_or`, `mul_or`, `div_or`, `mod_or`, `a.div_rem_or(b) -> (T, T, bool)` | Flagged `+ - * / %` on `u8` … `u128` (and `i8` … `i64`, see `signed`). |
| `Saturating`: `a.saturating_add(b) -> T`, `saturating_sub`, `saturating_mul` | Saturating forms on `u8` … `u128` (and `i8` … `i64`); no flag. |
| `TotalMulDiv`: `a.mul_div_or(b, d) -> (T, T, bool)`, `a.mul_div_ceil_or(b, d) -> (T, bool)` | `(floor(a·b / d), remainder, ok)` and `ceil(a·b / d)`, on `u8` … `u128` (and `i8` … `i64`) with a full-width intermediate product; flagged on `d = 0` or a result that does not fit. |
| `TotalUnsigned`: `a.widening_mul(b) -> (T, T)`, `a.pow_or(exp: u32) -> (T, bool)`, `a.isqrt() -> T`, `a.abs_diff(b) -> T`, `a.div_ceil_or(d) -> (T, bool)` | On `u8` … `u128`: the product as `(lo, hi)` with `a·b = lo + hi·2^N`, a flagged power (`0^0 = 1`), the integer square root, `\|a - b\|`, and `ceil(a / d)` flagged on `d = 0`. |
| `add_or::<N>(a, b) -> (Field, bool)`, `sub_or::<N>`, `mul_or::<N>` | Field-domain, N up to 128; flagged on overflow or underflow. |
| `wrapping_add_or::<N>(a, b) -> (Field, bool)`, `wrapping_sub_or::<N>`, `wrapping_mul_or::<N>`, `wrapping_neg_or::<N>(a)` | Field-domain; result mod 2^N; `ok` reports only the input ranges. |
| `saturating_add_or::<N>(a, b) -> (Field, bool)`, `saturating_sub_or::<N>`, `saturating_mul_or::<N>` | Field-domain; result clamped to `[0, 2^N - 1]`; `ok` reports only the input ranges. |
| `neg_or::<N>(a) -> (Field, bool)` | Unsigned negation, flagged unless the operand is 0. |
| `div_or::<N>(a, b) -> (Field, bool)`, `mod_or::<N>` | Field-domain quotient and remainder, N up to 128, flagged on a zero divisor. |
| `div_rem_or::<N>(a, b) -> (Field, Field, bool)` | Both from one division: `(q, r, ok)`. |
| `mul_div_or::<N>(a, b, d) -> (Field, Field, bool)` | Field-domain `(floor(a·b / d), a·b mod d, ok)` for N up to 84; the quotient can use 2N bits. |
| `mul_div_to_or::<N, M>(a, b, d) -> (Field, Field, bool)` | The same, also flagged when the quotient is at or above 2^M (M from 1 to 2N). |
| `mul_div_wide_or::<N>(a, b, d) -> (Field, Field, Field, bool)` | `(q_lo, q_hi, r, ok)` for N from 85 to 128, with the quotient `q_lo + q_hi·2^128` in two limbs. |
| `mul_div_wide_to_or::<M>(a, b, d) -> (Field, Field, bool)` | `(q, r, ok)` for 128-bit operands, flagged when the quotient is at or above 2^M (M from 1 to 253). |
| `pow_or::<N, E>(base, exp) -> (Field, bool)` | Power with an E-bit exponent, flagged when the result passes N bits; `0^0 = 1`. |
| `inverse_or(x) -> (Field, bool)`, `field_div_or(a, b)` | Field inverse and division, flagged at zero. Native Field `/` fails at zero. |
| `sqrt_or(x) -> (Field, bool)`, `sqrt_canonical_or(x)` | Field square root, flagged for a non-residue. The prover chooses the sign of `sqrt_or`'s root; the canonical form returns the even root. |

`arith::SQRT_NON_RESIDUE` is the non-residue `sqrt_or` uses.

## `signed`: signed integers

The traits `TotalArith`, `Saturating` and `TotalMulDiv` live in `arith`
(`use total::arith::TotalArith;`); `signed` implements them for `i8` … `i64`
and adds `TotalSigned`.

| Entry | Gives |
|---|---|
| `arith::TotalArith` on `i8` … `i64` | Flagged `+ - * / %`, including the `MIN / -1` and `MIN % -1` cases that native code asserts on. |
| `arith::Saturating` on `i8` … `i64` | Results clamped to `[MIN, MAX]`. |
| `arith::TotalMulDiv` on `i8` … `i64` | `a·b / d` truncated toward zero (remainder with the sign of `a·b`) and its ceiling; flagged on `d = 0` or a quotient that does not fit. |
| `TotalSigned`: `a.neg_or() -> (T, bool)`, `abs_or`, `a.signum() -> T`, `a.div_floor_or(d) -> (T, bool)`, `div_euclid_or`, `rem_euclid_or` | Negation and absolute value flagged at `MIN`; sign; floor and Euclidean division flagged on `d = 0` and `MIN / -1`. |
| `unsigned_abs_i8(x: i8) -> u8` … `unsigned_abs_i64` | Absolute value as the unsigned type (cannot fail). |

## `cmp`: comparison

| Entry | Gives |
|---|---|
| `eq(a: T, b: T) -> bool`, `neq`, `lt`, `lte`, `gt`, `gte` | Comparison flags on `Field` (canonical integer order), `bool`, `u8` … `u128`, `i8` … `i64`. |
| `min(a: T, b: T) -> T`, `max`, `clamp(x: T, lo: T, hi: T) -> T` | On the same types. |
| `is_zero(x) -> bool` | Field zero test. |
| `cmp_bits::<N>(a, b) -> CmpFlags` | Compare two Fields as N-bit integers, N from 1 to 253. `CmpFlags` has the fields `lt`, `eq`, `gt` (all false unless both are in range), `a_ok`, `b_ok`, and the methods `lte()`, `gte()`, `neq()`, `ok()`. |
| `TotalOrd`: `a.total_lt(b) -> bool`, `a.total_eq(b) -> bool` | The trait behind them; it requires `ctl::Select`, so implement both to add a type. |

## `bitwise`: bit operations and shifts

| Entry | Gives |
|---|---|
| `and_bits_or::<N>(a, b) -> (Field, bool)`, `or_bits_or::<N>`, `xor_bits_or::<N>`, `not_bits_or::<N>(a)` | Field-domain bit operations, N up to 128. Native `& \| ^ !` on integer types are already total. |
| `shl_or::<N>(a, s) -> (Field, bool)`, `shr_or::<N>` | Field-domain shifts by a `Field` amount, flagged when the amount is N or more; `shl_or` drops the bits shifted out, as native `<<` does. |
| `shl_exact_or::<N>(a, s) -> (Field, bool)` | Left shift also flagged when a set bit is shifted out. |
| `rotate_left_or::<N>(a, s) -> (Field, bool)`, `rotate_right_or::<N>` | Rotations. |
| `TotalShift`: `a.shl_or(s: T) -> (T, bool)`, `shl_exact_or`, `shr_or` | The same three contracts on `u8` … `u128`; the amount has the operand's type (a `u32` shifts by a `u32`). `shl_or` and `shr_or` replace native `<<` and `>>`. |

## `ctl`: selection and outcomes

| Entry | Gives |
|---|---|
| `Select::select(c: bool, t: T, f: T) -> T` | Constraint-free choice on `Field`, `bool`, `u8` … `u128`, `i8` … `i64`, arrays and tuples of up to four; implement it field by field for your own structs. |
| `Outcome { ok, code }` | An `ok` flag with the code of the first failure: `Outcome::good()`, `.require(flag: bool, code: Field)`, `.and_outcome(other)`, `.guard(new: T, old: T) -> T` (keep `old` unless ok), `.mask_field(x)`, `.mask_array(xs)`. |
| `some_or(opt: Option<T>) -> (T, bool)` | Flagged `Option::unwrap`; zeroed on `None`. |

## `collections`: arrays and `BoundedVec`

Free functions take indices and lengths as `Field`, so any value is flagged.

| Entry | Gives |
|---|---|
| `index_or(arr: [T; N], i) -> (T, bool)`, `set_or(arr: [T; N], i, v: T) -> ([T; N], bool)` | Array read and write with a `Field` index, flagged out of bounds. Linear in the array length. |
| `subarray_or(arr: [T; N], start) -> ([T; M], bool)` | A flagged window; its length M comes from the annotated result type, e.g. `let (w, ok): ([Field; 4], bool) = subarray_or(arr, start);`. |
| `index_flags_or::<N>(i) -> ([bool; N], bool)`, `prefix_mask_or::<N>(len) -> ([bool; N], bool)` | A one-hot index; a length mask. |
| `sum_or::<N, W>(arr: [Field; N]) -> (Field, bool)`, `sum_wide_or::<N, W>` | Sum of W-bit elements (W up to 128), flagged when it passes W bits, or exact without that bound. |
| `first_true_or(flags: [bool; N]) -> (Field, bool)`, `first_index_of_or(arr: [Field; N], x) -> (Field, bool)` | Search, flagged when nothing is found. |
| `any(flags: [bool; N]) -> bool`, `all`, `contains(arr: [T; N], x: T) -> bool`, `count_of(arr, x) -> Field` | Flag folds and equality search on any `Eq` element type (total when `T`'s `Eq` is). |
| `min_of_or::<N, W>(arr: [Field; N]) -> (Field, bool)`, `max_of_or::<N, W>` | Least and greatest of W-bit elements; flagged when empty or an element is out of range. |
| `is_sorted_or::<N, W>(arr: [Field; N]) -> (bool, bool)` | `(sorted, ok)`, W up to 128; `ok` is false when an element is out of range. |
| `sort_or::<N, W>(arr: [Field; N]) -> ([Field; N], bool)` | Total sort of W-bit elements (hinted permutation, checked); O(N^2). std's `sort` on native integers is already total. |

`collections::bounded_vec` (`use total::collections::bounded_vec::{TotalBoundedVec, from_prefix_or};`)
works like std's `BoundedVec` methods, with `u32` indices and lengths:

| Entry | Gives |
|---|---|
| `TotalBoundedVec`: `v.get_or(i: u32) -> (T, bool)`, `v.set_or(i: u32, x: T)`, `v.push_or(x: T)`, `v.set_len_or(len: u32)`, `v.extend_from_array_or(arr: [T; L])`, `v.extend_from_bounded_vec_or(w: BoundedVec<T, L>)`, each `-> (BoundedVec<T, MaxLen>, bool)`; `v.pop_or() -> (BoundedVec<T, MaxLen>, T, bool)`; `v.is_valid() -> bool` | Flagged forms of the `BoundedVec` methods that assert. They return a new vector rather than mutating. |
| `from_parts_or(array: [T; MaxLen], len: u32) -> (BoundedVec<T, MaxLen>, bool)`, `from_prefix_or` | Flagged construction from an array and an untrusted length; `from_parts_or` also flags a nonzero tail, `from_prefix_or` zeroes it. |

## `hash`

| Entry | Gives |
|---|---|
| `p2_hash(input: [Field; N]) -> Field`, `p2_hash_sep(input, sep) -> Field` | Poseidon2, fixed length, plain and domain-separated (Aztec-compatible). |
| `p2_hash_var_or(input: [Field; N], len) -> (Field, bool)`, `p2_hash_sep_var_or(input, len, sep)` | Variable length with a flagged `Field` length; same digest as aztec-nr when the length is in range. |
| `Sponge::new(iv).absorb(x).absorb_array(xs).squeeze() -> Field` | Incremental Poseidon2. `iv` is the capacity element, `L·2^64` for `L` absorbed elements (then the digest equals `p2_hash`). Each `absorb` consumes the sponge and returns one of another type, so chain the calls rather than mutating a variable. |
| `sha256_var_or(input: [u8; N], len) -> ([u8; 32], bool)`, `keccak256_var_or` | SHA-256 and Keccak-256 over a byte array with a flagged `Field` length; the libraries' fixed-length forms and std's other hashes, Pedersen included, are total as they are. |

## `merkle`: Poseidon2 membership

| Entry | Gives |
|---|---|
| `merkle_root_or::<D>(leaf, index, path: [Field; D]) -> (Field, bool)` | The root a leaf and sibling path imply, Aztec's `root_from_sibling_path` with the index flagged below 2^D. D up to 128. |
| `is_member::<D>(leaf, index, path: [Field; D], root) -> bool` | Membership flag against an expected root. |
| `merkle_root_sep_or::<D>(leaf, index, path, sep)`, `is_member_sep::<D>(leaf, index, path, root, sep)` | The same for a tree hashed with another domain separator. |
| `merkle_hash(left, right) -> Field` | Aztec's Merkle node hash, with separator `MERKLE_HASH_SEPARATOR`. |

## `ec`: Grumpkin

| Entry | Gives |
|---|---|
| `Point { x, y, inf: bool }`, `Point::infinity()`, `Point::generator()`, `p.neg()`, `p.to_embedded() -> EmbeddedCurvePoint` | The point type (with `Select` and `Eq`), and conversion to std's form. |
| `decode_or(x, y, inf) -> (Point, bool)`, `decode_xy_or(x, y) -> (Point, bool)` | Flagged decoding of untrusted coordinates. `inf` is a `Field`, flagged unless 0 or 1; `decode_xy_or` takes std's form, where `(0, 0)` is infinity. |
| `on_curve_flag(x, y) -> bool`, `is_well_formed(p: Point) -> bool` | Curve-membership flags, on coordinates and on a `Point`. |
| `add(p: Point, q: Point) -> Point`, `double(p)`, `sub(p, q)`, `p.neg()` | Complete group operations (defined for every pair of points). |
| `mul_or::<MAX_BITS>(p: Point, s) -> (Point, bool)`, `mul_limbs_or(p: Point, lo, hi) -> (Point, bool)`, `scalar_limbs_or(lo, hi) -> (Field, Field, bool)` | Scalar multiplication with a flagged scalar: a `Field` of at most MAX_BITS (1 to 254) bits, or a full scalar as two 128-bit limbs. |
| `msm_or(points: [Point; N], lo: [Field; N], hi: [Field; N]) -> (Point, bool)` | Multi-scalar multiplication over the black box, scalars as limb arrays, with every precondition flagged first and the black box's bases blinded, so bb's MSM gadget has a proof for every input (4.7k gates for one term, 5.3k for two). |

`ec::CURVE_B` is the curve constant -17; `ec::ORDER_LO` and `ec::ORDER_HI` are
the limbs of the group order.

## `encode`: bytes and packing

| Entry | Gives |
|---|---|
| `canonical_le_bytes_flag(bytes: [u8; 32]) -> bool`, `canonical_be_bytes_flag`, `canonical_le_bits_flag(bits: [bool; 254]) -> bool`, `canonical_be_bits_flag` | Whether an encoding is below the field modulus. |
| `u16_to_be_bytes(x: u16) -> [u8; 2]` … `u128_from_le_bytes(b: [u8; 16]) -> u128` | Integer and byte-array conversions in both byte orders (cannot fail). |
| `bytes_to_fields_be(bytes: [u8; N]) -> [Field; N / 31]`, `bytes_to_fields_le(bytes: [u8; N]) -> [Field; (N + 30) / 31]` | 31-byte packing: big-endian chunks with N a multiple of 31 (aztec-nr's convention, checked at compile time), or little-endian chunks with a short final chunk allowed. |
| `fields_to_bytes_be_or(fields: [Field; N]) -> ([u8; 31 * N], bool)`, `fields_to_bytes_le_or`, `chunk_to_be_bytes_or(x) -> ([u8; 31], bool)`, `chunk_to_le_bytes_or` | Unpacking, flagged when a chunk passes 31 bytes. |
| `reverse(arr: [T; N]) -> [T; N]`, `reverse32(arr: [u8; 32])` | Array reversal. |

## `secp`: secp256k1 and secp256r1 points

| Entry | Gives |
|---|---|
| `secp256k1_on_curve(x: [u8; 32], y: [u8; 32]) -> bool`, `secp256r1_on_curve` | Whether 32-byte big-endian coordinates are canonical and on the curve. |

## `schnorr`, `ecdsa`: signatures

| Entry | Gives |
|---|---|
| `schnorr_verify(pk_x, pk_y, sig: [Field; 4], msg) -> bool`, `schnorr_inputs_ok(pk_x, pk_y, sig: [Field; 4]) -> bool` | Schnorr over Grumpkin (noir-lang/schnorr v0.4.0's scheme, computed over `msm_or`), with `sig = [s_lo, s_hi, e_lo, e_hi]`, the Aztec v6 auth-witness layout. A malformed key or signature is `false`, not a failure, and every key has a proof (5.5k gates). |
| `ecdsa_k1_verify(pk_x: [u8; 32], pk_y: [u8; 32], sig: [u8; 64], hash: [u8; 32]) -> bool`, `ecdsa_r1_verify` | ECDSA over secp256k1 and secp256r1 with big-endian coordinates and `sig = r \|\| s`; a public key that is not on the curve is `false`. The std black box runs on the key blinded by an in-circuit multiple of G, so that every key has a proof (63.4k gates on secp256k1 and 66.6k on secp256r1, 1.48x and 1.45x the black box alone). |
| `ecdsa_k1_verify_fields(pk_x: [Field; 32], pk_y: [Field; 32], sig: [Field; 64], hash: [Field; 32]) -> bool`, `ecdsa_r1_verify_fields` | The same on `Field`-typed bytes, each flagged below 256 (70.5k and 73.7k gates). |
| `ecdsa_k1_sig_admissible(sig: [u8; 64]) -> bool`, `ecdsa_r1_sig_admissible` | Whether a signature is outside the input classes the wrappers exclude. |

Typed inputs (`[u8; N]`, `u32`, `bool`, `Point`) at a circuit's entry point
are range checks an input can fail: take `Field` there and convert first,
with `to_u8_or` per byte or the `_fields` and `decode` forms.

## `total_aztec`: aztec-nr v6

> [!CAUTION]
> **`total_aztec` is extremely experimental, more so than the rest of this repository.** The PXE's oracles and aztec-nr were not designed for total circuits, and this package works around them. Several ways remain for a contract or a state to make a private function unprovable (see [Known limitations](limitations.md) and [docs/design.md](design.md)), its guarantees are tied to aztec-nr v6.0.0 exactly, and its API will change. Treat it as a research prototype.

```toml
total_aztec = { tag = "v0.1.0", git = "https://github.com/iAmMichaelConnor/total-noir", directory = "noir/total_aztec" }
aztec = { git = "https://github.com/aztec-labs-eng/aztec-node", tag = "v6.0.0", directory = "noir-projects/aztec-nr/aztec" }
```

Depend on aztec-nr with exactly this `git`, `tag` and `directory`, so that
both packages resolve to one `aztec` crate, and give `total` and
`total_aztec` the same tag, so that both resolve to one `total` crate.

| Entry | Gives |
|---|---|
| `get_note_or(context, owner: Option<AztecAddress>, storage_slot) -> (Note, bool)`, `get_notes_or::<N>(...) -> ([Note; N], [bool; N])` | Note reads that return `found` instead of asserting, one flag per slot for `get_notes_or`; the kernel read request is emitted only under `found`. The PXE answers which notes exist, so `found` is the executor's choice; notes of another type or width at the slot, and a note whose read request the kernel would reject (a pending note is found only in the call that pushed its note hash), are dropped, not fatal. |
| `get_settled_note_from_witness_or(context, note, owner, storage_slot, randomness, note_nonce, leaf_index, sibling_path) -> (Note, bool)` | A settled note read from arguments with no oracle: `found` says the note's unique note hash is on that path below the anchor block's note hash tree root, so it is determined by the arguments and the anchor block. |
| `GetNoteOr`, `GetNotesOr`: `storage.x.get_note_or(owner)`, `storage.x.get_notes_or::<N>(owner)` | The same as methods of an owned `PrivateImmutable`, `PrivateMutable` or `PrivateSet` (without nullifying). |
| `single_private_immutable_get_note_or(context, var) -> (Note, bool)` | The same for a `SinglePrivateImmutable`. |
| `note_hash_exists_at_anchor(context, leaf, leaf_index, sibling_path) -> bool` | Membership flag for a note hash at the anchor block, from a witness the caller passes (no oracle); determined by the arguments and the anchor block. |
| `nullifier_exists_at_anchor(context, inner_nullifier) -> bool`, `contract_is_initialized(context) -> bool`, `public_immutable_is_initialized(context, var) -> bool` | Determined existence flags; `contract_is_initialized` replaces the macro's init check. |
| `record_initializer_args(args)`, `initializer_args_or::<N>(context, initializer) -> InitializerArgs<N>` | The initializer's arguments in a later call of its own transaction, where the initializer's notes cannot be read: a hint the initializer records, `bound` when it hashes to the initialization hash in the address, beside the determined initialisation flag at the anchor block. For a value the contract's state replaces later (an account's first signing key), trust it only while `initialized` is false; the executor chooses the anchor block. |
| `public_immutable_read_or(context, var) -> (T, bool)`, `delayed_public_mutable_read_or(context, var) -> (T, bool)` | A `PublicImmutable`, or a `DelayedPublicMutable`'s current value, read from private with every slot proved at the anchor block: flagged when the value was never set (`PublicImmutable`) or the stored state is one the variable's own functions cannot write (direct storage writes), determined. `T` must have no `bool` member. |
| `key_ok(x, y) -> bool`, `decode_key_or(x, y) -> (Point, bool)`, `refuse_bad_key(x, y, message)`, `set_key_or(var, owner, x, y) -> (MaybeNoteMessage<Note>, bool)`, `KeyNote`, `key_note::KeyFields` | Stored public keys: refuse a bad key where it is written, flag it where it is read. `refuse_bad_key` and `set_key_or` (which also flags an owner other than `msg_sender`) are for the writer's own transaction only; the lint reports them unless the call site carries a marker saying so. A note type implements `KeyFields` to be used with `set_key_or`. |
| `static_call_flagged_or(context, target, selector, args: [Field; A]) -> ([Field; M], bool)`, `call::decode_flagged_or(ret: [Field; M + 1]) -> ([Field; M], bool)` | A static private call whose returns end in a flag Field; the values are zeroed unless it is exactly 1. The callee can still fail the call (its own failures, another return arity); the lint reports the call unless the call site carries a marker naming who chooses the target. |
| `consume_with_nullification_proof_or(context, handoff: NullificationProof<N>, expected_vk_hash, pinned_npk_app_hash, storage_slot, owner) -> ([Field; N], bool)` | A third party consumes an owner's note using the owner's recursive proof of nullification, passed as an argument with the leaf's index and sibling path; `ok` is determined by the arguments and the anchor block. A handoff whose flags hold and whose proof does not verify fails proving (no flag form exists), so the call site carries a marker naming who supplies it. The pin comes from `registered_npk_app_hash(context, owner)` (or `npk_app_hash`) in the owner's own transaction. |

The threat model has two parties. A contract that uses these entries and
passes the lint must stay provable for an honest executor in every state,
including states its own author creates on purpose; and against a dishonest
executor a witness always exists, though an oracle-backed flag (a note's
`found`) is the executor's choice
([docs/design.md](design.md#oracle-data-and-provable-error-codes)).

These are wrappers alongside aztec-nr, not a replacement for it, and a
contract is total only where it uses them. A note read's `found = true` proves
the note was committed at that contract, owner and slot at some point, not
that it is still unspent; `found = false` proves nothing. Note reads find a
note only in a PXE that holds the owner's keys; for anyone else they return
`found = false`: the read does not fail, but it does not read the note either.
[docs/aztec-nr-coverage.md](aztec-nr-coverage.md) surveys how aztec-nr
operations can fail and which of those are covered, and
[docs/design.md](design.md#aztec-what-a-total-private-function-may-use)
states what a total private function may and may not use from aztec-nr v6. `DEV DECISION:` comments
mark each place where an app developer chooses a policy.
