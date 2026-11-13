//! Public state read from private, with flags.
//!
//! # Where aztec-nr v6 fails
//!
//! Function names are aztec-nr v6.0.0's (`aztec/src/...`).
//!
//! - PublicImmutable::read in private fails when the variable was never
//!   initialised: its hint asserts "Trying to read from uninitialized
//!   PublicImmutable" (a Brillig trap), the nullifier read request fails
//!   the kernel, and utils/with_hash.nr's hint check asserts the hint
//!   against the stored hash.
//! - DelayedPublicMutable::get_current_value in private reads through the
//!   same with_hash.nr check: it asserts that the hinted packing hashes to
//!   the stored hash, or is all zeros when the stored hash is 0. Class
//!   code can write any public slot of its own contract directly
//!   (PublicContext::storage_write, or a public function of another type
//!   at the same slot), so a stored hash that disagrees with the stored
//!   values, or values with a zero hash, are reachable states, and in
//!   them the assert has no witness. Its time-horizon arithmetic also
//!   underflows on a stored delay of 0 (u64 subtraction), which only a
//!   direct write can store. Both hold for a PublicImmutable read too.
//! - A typed member decodes inside the hint and again in the circuit: a
//!   bool member asserts {0, 1} (protocol types' Packable for bool), and
//!   an integer member truncates silently.
//! - PublicMutable has no private read, and none is offered: its value
//!   can change between the anchor block and inclusion.
//!
//! # What this module does instead
//!
//! Every slot is read with aztec-nr's public_storage_historical_read, a
//! proof of the slot's value in the anchor block's public data tree (a
//! low-leaf witness from the PXE and its Merkle path: the honest PXE has
//! a witness for every slot, so its asserts are hint-satisfiable in every
//! state). Nothing is hinted, so no assert ties a hint to the stored
//! hash: a stored state the writer's own code could not produce reads as
//! ok = false. ok is a function of the proved slot values alone, so it is
//! determined (relative to the anchor block) in both directions, for the
//! executor and for a requester.
//!
//! The price is one tree proof per packed field plus one for the hash,
//! where aztec-nr proves only the hash.
//!
//! Typed members. ok also requires the stored values to be the canonical
//! packing of the decoded value (T::unpack, then pack, gives them back),
//! so an integer member holding a wider value reads as ok = false. The
//! decode runs only on a consistent state (hash matching), but a bool
//! member's assert cannot be turned into a flag from outside T: with
//! direct writes the class can store 2 with a matching hash. So T must
//! have no bool members (Field and integer members are fine); total-lint
//! reports that assert (a booleanity check on proved data) in every
//! function that reads such a T.
//!
//! Only this contract's own state is read; reading another contract's
//! public value from private has no form here.

use aztec::context::PrivateContext;
use aztec::history::storage::public_storage_historical_read;
use aztec::protocol::{
    abis::block_header::BlockHeader, address::AztecAddress,
    delayed_public_mutable::DelayedPublicMutableValues, hash::poseidon2_hash, traits::Packable,
};
use aztec::state_vars::{
    DELAYED_PUBLIC_MUTABLE_MINIMUM_DELAY, DelayedPublicMutable, PublicImmutable, StateVariable,
};

/// The M public storage slots from storage_slot of address at the block
/// of header, each proved with public_storage_historical_read. Unwritten
/// slots read as 0.
fn read_slots<let M: u32>(
    header: BlockHeader,
    address: AztecAddress,
    storage_slot: Field,
) -> [Field; M] {
    let mut values = [0; M];
    for i in 0..M {
        // total-lint: allow aztec-nr's public data witness checks; the honest PXE has a witness for every slot
        values[i] = public_storage_historical_read(header, storage_slot + i as Field, address);
    }
    values
}

/// values with every field multiplied by keep.
fn masked<let M: u32>(values: [Field; M], keep: bool) -> [Field; M] {
    values.map(|v| (keep as Field) * v)
}

/// Read a PublicImmutable from private as (value, ok). ok is true exactly
/// when, at the anchor block, the stored hash is nonzero, the stored
/// values hash to it, and they are T's canonical packing; on ok = false
/// the value is T::unpack of all zeros. An uninitialised variable, and
/// any state the class wrote directly that initialize could not have
/// written, read as ok = false.
///
/// Constraints: M + 1 public data tree reads (read_slots and the hash
/// slot), then check_public_immutable_or. No hint, no kernel request.
///
/// Determined in both directions, relative to the anchor block.
///
/// T must have no bool member (module header, "Typed members").
pub fn public_immutable_read_or<T, let M: u32>(
    context: &mut PrivateContext,
    var: PublicImmutable<T, &mut PrivateContext>,
) -> (T, bool)
where
    T: Packable<N = M>,
{
    let header = context.get_anchor_block_header();
    let address = context.this_address();
    let slot = var.get_storage_slot();
    let values: [Field; M] = read_slots(header, address, slot);
    // total-lint: allow aztec-nr's public data witness checks; the honest PXE has a witness for every slot
    let stored_hash = public_storage_historical_read(header, slot + M as Field, address);
    check_public_immutable_or(values, stored_hash)
}

/// The flag half of public_immutable_read_or, split out so tests can feed
/// any stored state: (value, ok) with ok = stored_hash != 0 &
/// poseidon2_hash(values) == stored_hash & canonical, where canonical says
/// T::unpack(values).pack() == values.
///
/// Constraints: one Poseidon2 hash, two eq gadgets, the masking products,
/// T::unpack and pack of the masked values with M eq gadgets, then
/// T::unpack of the values masked by ok. No assert of its own; T::unpack
/// is total for Field and integer members (a bool member asserts {0, 1}
/// on a consistent state, module header).
pub fn check_public_immutable_or<T, let M: u32>(values: [Field; M], stored_hash: Field) -> (T, bool)
where
    T: Packable<N = M>,
{
    let consistent = (stored_hash != 0) & (poseidon2_hash(values) == stored_hash);
    let candidate = masked(values, consistent);
    let canonical = T::unpack(candidate).pack() == candidate;
    let ok = consistent & canonical;
    (T::unpack(masked(values, ok)), ok)
}

/// Read a DelayedPublicMutable's current value from private as (value,
/// ok), the total form of aztec-nr's get_current_value. ok is true
/// exactly when the stored state at the anchor block is one the
/// variable's own scheduling functions can produce:
///
/// - consistent: the stored hash is 0 and every value slot is 0 (never
///   written), or the hash is nonzero and the 2M + 1 values hash to it;
/// - canonical: the values are the packing of what they decode to
///   (DelayedPublicMutableValues::unpack, then pack): the timestamps and
///   delays fit their 32-bit fields, the two Option flags are 0 or 1 with
///   a zero delay under none, nothing above bit 143, and T's members are
///   canonical;
/// - delays: each delay the state holds (pre and post, or InitialDelay
///   for none) is at least DELAYED_PUBLIC_MUTABLE_MINIMUM_DELAY, as
///   schedule_delay_change requires.
///
/// On ok = true the value is what get_current_value returns and the
/// transaction's expiration is lowered to the same time horizon; a
/// never-written variable reads as T::unpack of all zeros, as in
/// aztec-nr. On ok = false the value is T::unpack of all zeros and the
/// expiration is not touched.
///
/// Constraints: 2M + 2 public data tree reads; the consistency flags (a
/// Poseidon2 hash, eq gadgets); the decode and re-pack (integer casts the
/// compiler proves, eq gadgets); the delay comparisons; then aztec-nr's
/// time horizon (get_effective_minimum_delay_at, get_time_horizon) and
/// get_current_at on the values masked by ok. Every delay in those is at
/// least the minimum (checked, or InitialDelay on the masked zeros), so
/// their u64 subtractions cannot underflow; timestamps are below 2^32 and
/// the anchor timestamp is a real block's, so the additions cannot
/// overflow. No hint, no kernel request; determined relative to the
/// anchor block.
///
/// What no flag removes: the expiration. A state the writer reaches
/// legitimately leaves at least the delay less one second from the
/// anchor, or less only for a reader anchored just before a scheduled
/// change; a class that writes the slots directly can store a value
/// change scheduled one second after every new block, which leaves every
/// reader's transaction an expiration at its anchor block, so it cannot
/// be included. The transaction stays provable.
///
/// T must have no bool member (module header, "Typed members").
pub fn delayed_public_mutable_read_or<T, let InitialDelay: u64, let M: u32>(
    context: &mut PrivateContext,
    var: DelayedPublicMutable<T, InitialDelay, &mut PrivateContext>,
) -> (T, bool)
where
    T: Packable<N = M> + Eq,
{
    let header = context.get_anchor_block_header();
    let address = context.this_address();
    let slot = var.get_storage_slot();
    let values: [Field; 2 * M + 1] = read_slots(header, address, slot);
    // total-lint: allow aztec-nr's public data witness checks; the honest PXE has a witness for every slot
    let stored_hash = public_storage_historical_read(header, slot + (2 * M + 1) as Field, address);
    let anchor_timestamp = header.timestamp();
    let (value, horizon, ok) = check_delayed_public_mutable_or::<T, InitialDelay, M>(
        values,
        stored_hash,
        anchor_timestamp,
    );
    if ok {
        // total-lint: allow the u64 min in set_expiration_timestamp: the compiler's hints satisfy it for every pair
        context.set_expiration_timestamp(horizon);
    }
    (value, ok)
}

/// The flag half of delayed_public_mutable_read_or, split out so tests
/// can feed any stored state: (value, time horizon, ok). On ok = false
/// the value and horizon are those of the never-written state.
pub fn check_delayed_public_mutable_or<T, let InitialDelay: u64, let M: u32>(
    values: [Field; 2 * M + 1],
    stored_hash: Field,
    anchor_timestamp: u64,
) -> (T, u64, bool)
where
    T: Packable<N = M> + Eq,
{
    let mut all_zero = true;
    for i in 0..2 * M + 1 {
        all_zero &= values[i] == 0;
    }
    let consistent = ((stored_hash == 0) & all_zero)
        | ((stored_hash != 0) & (poseidon2_hash(values) == stored_hash));
    let candidate = masked(values, consistent);
    // total-lint: allow integer casts of proved Fields in the decode: the compiler's quotient and remainder hints satisfy them for every Field
    let decoded: DelayedPublicMutableValues<T, InitialDelay> = Packable::unpack(candidate);
    // total-lint: allow re-pack of decoded values: its 32-bit size asserts hold, every timestamp and delay comes from a u32 cast
    let canonical = decoded.pack() == candidate;
    // total-lint: allow integer casts and comparisons of a proved Field (delays_ok): the compiler's hints satisfy them for every Field
    let ok = consistent & canonical & delays_ok::<InitialDelay>(candidate[0]);
    // total-lint: allow integer casts of proved Fields in the decode: the compiler's quotient and remainder hints satisfy them for every Field
    let safe: DelayedPublicMutableValues<T, InitialDelay> = Packable::unpack(masked(values, ok));
    // total-lint: allow every delay in safe is at least DELAYED_PUBLIC_MUTABLE_MINIMUM_DELAY (delays_ok, or InitialDelay on zeros) and every timestamp below 2^32: no underflow or overflow
    let minimum_delay = safe.sdc.get_effective_minimum_delay_at(anchor_timestamp);
    // total-lint: allow minimum_delay below 2^32 and timestamps below 2^32 against a real anchor timestamp: no underflow or overflow
    let horizon = safe.svc.get_time_horizon(anchor_timestamp, minimum_delay);
    (safe.svc.get_current_at(anchor_timestamp), horizon, ok)
}

/// Flag: each delay in the packed delay field (pre and post, InitialDelay
/// where the Option flag is even) is at least
/// DELAYED_PUBLIC_MUTABLE_MINIMUM_DELAY. The field is cut exactly as
/// protocol types' unpack_delay_change cuts it (svc timestamp, sdc
/// timestamp, post flag, post delay, pre flag, pre delay; subtract the
/// low part, divide by its width). Integer casts and comparisons the
/// compiler proves; no assert.
fn delays_ok<let InitialDelay: u64>(packed: Field) -> bool {
    let two_32 = 0x100000000;
    let two_8 = 0x100;
    let svc_timestamp = packed as u32;
    let mut tmp = (packed - svc_timestamp as Field) / two_32;
    let sdc_timestamp = tmp as u32;
    tmp = (tmp - sdc_timestamp as Field) / two_32;
    let post_flag = tmp as u8;
    tmp = (tmp - post_flag as Field) / two_8;
    let post = tmp as u32;
    tmp = (tmp - post as Field) / two_32;
    let pre_flag = tmp as u8;
    tmp = (tmp - pre_flag as Field) / two_8;
    let pre = tmp as u32;
    let post_delay = if post_flag % 2 != 0 {
        post as u64
    } else {
        InitialDelay
    };
    let pre_delay = if pre_flag % 2 != 0 {
        pre as u64
    } else {
        InitialDelay
    };
    (post_delay >= DELAYED_PUBLIC_MUTABLE_MINIMUM_DELAY)
        & (pre_delay >= DELAYED_PUBLIC_MUTABLE_MINIMUM_DELAY)
}

mod tests {
    use super::{check_delayed_public_mutable_or, check_public_immutable_or};
    use aztec::protocol::{
        delayed_public_mutable::{
            DelayedPublicMutableValues, ScheduledDelayChange, ScheduledValueChange,
        },
        hash::poseidon2_hash,
        traits::Packable,
    };

    /// x as a witness, so a test reaches the constraints instead of being
    /// folded at compile time (the print oracle keeps the call).
    unconstrained fn opaque<T>(x: T) -> T {
        std::print("");
        x
    }

    fn wit<T>(x: T) -> T {
        // Safety: test-only witness construction; no constraint needed.
        unsafe {
            opaque(x)
        }
    }

    fn immutable<T, let M: u32>(values: [Field; M], hash: Field) -> (T, bool)
    where
        T: Packable<N = M>,
    {
        check_public_immutable_or(wit(values), wit(hash))
    }

    #[test]
    fn an_initialised_value_reads() {
        let (v, ok): ([Field; 2], bool) = immutable([3, 4], poseidon2_hash([3, 4]));
        assert_eq((v, ok), ([3, 4], true));
    }

    #[test]
    fn an_unset_value_is_a_flag() {
        let (v, ok): ([Field; 2], bool) = immutable([0, 0], 0);
        assert_eq((v, ok), ([0, 0], false));
    }

    // States only a direct storage write can make, each a flag with the
    // value masked: values with a zero hash (aztec-nr asserts "Non-zero
    // hint for zero hash"), and a nonzero hash the values do not match
    // (aztec-nr asserts "Hint values do not match hash").
    #[test]
    fn directly_written_inconsistent_states_are_flags() {
        let (v, ok): ([Field; 2], bool) = immutable([3, 4], 0);
        assert_eq((v, ok), ([0, 0], false));
        let (v, ok): ([Field; 2], bool) = immutable([3, 5], poseidon2_hash([3, 4]));
        assert_eq((v, ok), ([0, 0], false));
        let (v, ok): ([Field; 2], bool) = immutable([0, 0], poseidon2_hash([3, 4]));
        assert_eq((v, ok), ([0, 0], false));
    }

    #[derive(Eq, Packable)]
    struct ByteValue {
        b: u8,
        f: Field,
    }

    // An integer member holding a wider value, with a matching hash: the
    // decode truncates, the re-pack differs, so it is a flag.
    #[test]
    fn a_non_canonical_integer_member_is_a_flag() {
        let (v, ok): (ByteValue, bool) = immutable([5, 6], poseidon2_hash([5, 6]));
        assert_eq((v, ok), (ByteValue { b: 5, f: 6 }, true));
        let (v, ok): (ByteValue, bool) = immutable([0x105, 6], poseidon2_hash([0x105, 6]));
        assert_eq((v, ok), (ByteValue { b: 0, f: 0 }, false));
    }

    // The restriction on T: a bool member holding 2 with a matching hash
    // (a direct write) makes protocol types' bool unpack assert. total-lint
    // reports that assert in a function that reads such a T.
    #[test(should_fail_with = "bool field must be 0 or 1")]
    fn a_bool_member_holding_two_has_no_witness() {
        let _: (bool, bool) = immutable([2], poseidon2_hash([2]));
    }

    global DELAY: u64 = 86400;
    global ANCHOR: u64 = 1_000_000;

    /// The packing (2 * 1 + 1 fields) aztec-nr writes for a Field value.
    fn packed(
        pre: Field,
        post: Field,
        value_change_at: u64,
        delay_pre: Option<u64>,
        delay_post: Option<u64>,
        delay_change_at: u64,
    ) -> [Field; 3] {
        DelayedPublicMutableValues::<Field, DELAY>::new(
            ScheduledValueChange::new(pre, post, value_change_at),
            ScheduledDelayChange::new(delay_pre, delay_post, delay_change_at),
        )
            .pack()
    }

    fn delayed(values: [Field; 3], hash: Field) -> (Field, u64, bool) {
        check_delayed_public_mutable_or::<Field, DELAY, 1>(wit(values), wit(hash), wit(ANCHOR))
    }

    /// aztec-nr's value and horizon for a state its writer produced.
    fn reference(values: [Field; 3]) -> (Field, u64, bool) {
        let v = DelayedPublicMutableValues::<Field, DELAY>::unpack(values);
        let delay = v.sdc.get_effective_minimum_delay_at(ANCHOR);
        (v.svc.get_current_at(ANCHOR), v.svc.get_time_horizon(ANCHOR, delay), true)
    }

    // aztec-nr's own horizon arithmetic on a directly written zero delay:
    // get_effective_minimum_delay_at subtracts 1 from it.
    #[test(should_fail_with = "attempt to subtract with overflow")]
    fn aztec_nr_horizon_underflows_on_a_zero_delay() {
        let _ = reference(
            wit(
                packed(1, 7, ANCHOR - 10, Option::some(DELAY), Option::some(0), 5),
            ),
        );
    }

    #[test]
    fn a_never_written_variable_reads_as_zero() {
        assert_eq(delayed([0, 0, 0], 0), (0, ANCHOR + DELAY - 1, true));
    }

    // States the writer produces read exactly as aztec-nr reads them: a
    // value changed in the past, a change still scheduled, a delay change
    // pending, a delay change applied.
    #[test]
    fn written_states_read_as_aztec_nr_reads_them() {
        let states = [
            packed(1, 7, ANCHOR - 10, Option::none(), Option::none(), 0),
            packed(1, 7, ANCHOR + 7200, Option::none(), Option::none(), 0),
            packed(
                1,
                7,
                ANCHOR + 7200,
                Option::some(DELAY),
                Option::some(3600),
                ANCHOR + 50,
            ),
            packed(
                1,
                7,
                ANCHOR - 1,
                Option::some(DELAY),
                Option::some(3600),
                ANCHOR - 1,
            ),
        ];
        for s in states {
            assert_eq(delayed(s, poseidon2_hash(s)), reference(s));
        }
    }

    // States only a direct storage write can make. aztec-nr's read has no
    // witness for any of them (its hint check asserts, or its horizon
    // subtracts 1 from a zero delay); here each is ok = false with the
    // never-written value and horizon.
    #[test]
    fn directly_written_delayed_states_are_flags() {
        let none = (0, ANCHOR + DELAY - 1, false);
        let good = packed(1, 7, ANCHOR - 10, Option::none(), Option::none(), 0);
        // a hash that does not match
        assert_eq(delayed(good, poseidon2_hash(good) + 1), none);
        // values with a zero hash
        assert_eq(delayed(good, 0), none);
        // a post delay of 0, applied: aztec-nr computes 0 - 1
        let zero_post = packed(1, 7, ANCHOR - 10, Option::some(DELAY), Option::some(0), 5);
        assert_eq(delayed(zero_post, poseidon2_hash(zero_post)), none);
        // a pre delay of 0 with a change pending: min(0, ..) - 1
        let zero_pre = packed(
            1,
            7,
            ANCHOR - 10,
            Option::some(0),
            Option::some(DELAY),
            ANCHOR + 9,
        );
        assert_eq(delayed(zero_pre, poseidon2_hash(zero_pre)), none);
        // a delay below the one-hour minimum
        let short = packed(1, 7, ANCHOR - 10, Option::some(DELAY), Option::some(59), 5);
        assert_eq(delayed(short, poseidon2_hash(short)), none);
        // non-canonical packings of the delay field: a flag byte of 3, and
        // a bit above the layout
        let mut flag3 = good;
        flag3[0] += 3 * 0x10000000000000000;
        assert_eq(delayed(flag3, poseidon2_hash(flag3)), none);
        let mut high = good;
        high[0] += 0x1000000000000000000000000000000000000;
        assert_eq(delayed(high, poseidon2_hash(high)), none);
    }
}
