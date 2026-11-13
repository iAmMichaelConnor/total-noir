//! TXE tests: the contract's functions executed against a TXE server.
//! Run with `nargo test --oracle-resolver http://127.0.0.1:<port> test::`
//! after `bb aztec_process` on the compiled artifact (README.md).

use crate::ecies;
use crate::enc_key::{ENC_KEY_INITIAL_DELAY, EncKey};
use crate::signing_key::CONSTRUCTOR_SELECTOR;
use crate::TotalAccount;
use aztec::authwit::{
    auth::{compute_authwit_message_hash, IS_VALID_SELECTOR},
    entrypoint::{app::AppPayload, FunctionCall},
};
use aztec::context::{calls::PrivateCall, PrivateContext, PublicContext};
use aztec::keys::getters::get_public_keys;
use aztec::protocol::{
    abis::function_selector::FunctionSelector,
    address::AztecAddress,
    traits::{Deserialize, FromField, Hash, Serialize, ToField},
};
use aztec::state_vars::{DelayedPublicMutable, StateVariable};
use aztec::test::helpers::{
    test_environment::{
        CallPrivateOptions, DeployOptions, PrivateContextOptions, TestEnvironment,
        ViewPrivateOptions,
    },
    txe_oracles,
};
use aztec::transient::TransientArray;
use std::embedded_curve_ops::{EmbeddedCurveScalar, fixed_base_scalar_mul};
use total_aztec::{
    delayed_public_mutable_read_or, initializer_args_or, INITIALIZER_ARGS_SLOT, InitializerArgs,
    record_initializer_args,
};

global SIGN_SK: Field = 0x0a11ce;
global ENC_SK: Field = 0x1d7a0b3c5e9f21a4c6b8d0e2f4a6c8e0b2d4f6a8c0e2b4d6f8a0c2e4b6d8f0a;
global ENC_SK_2: Field = 0x2b0b;
global R: Field = 0x2f1e3d5c7b9a8f6e4d2c1b0a99887766554433221100ffeeddccbbaa998877;
global MSG: [Field; 4] = [0x11, 0x22, 0x33, 0x44];

unconstrained fn pk(sk: Field) -> (Field, Field) {
    let p = fixed_base_scalar_mul(EmbeddedCurveScalar::from_field(sk));
    (p.x, p.y)
}

/// Deploy TotalAccount with keys derived from secret and run its
/// constructor from its own address, so the constructor's key requests
/// are in scope (what TestEnvironment::create_contract_account does for
/// the built-in account). The constructor schedules the key, so the key
/// is not current until the delay passes; this waits it out so that the
/// account has its key.
unconstrained fn deploy_account(
    env: TestEnvironment,
    secret: Field,
    enc_x: Field,
    enc_y: Field,
) -> AztecAddress {
    let b = deploy_account_pending(env, secret, enc_x, enc_y);
    wait_out_delay(env);
    b
}

/// As deploy_account, without waiting: the key is scheduled, not current.
unconstrained fn deploy_account_pending(
    env: TestEnvironment,
    secret: Field,
    enc_x: Field,
    enc_y: Field,
) -> AztecAddress {
    let (sx, sy) = pk(SIGN_SK);
    deploy_account_with(env, secret, sx, sy, enc_x, enc_y)
}

/// Mine a block ENC_KEY_INITIAL_DELAY after the last one, so a value
/// scheduled at the last block's timestamp is current at the next anchor.
unconstrained fn wait_out_delay(env: TestEnvironment) {
    env.mine_block_at(env.last_block_timestamp() + ENC_KEY_INITIAL_DELAY);
}

/// (key, expiration, anchor timestamp) of a private read of the key at
/// block n.
unconstrained fn read_key_at(env: TestEnvironment, b: AztecAddress, n: u32) -> (EncKey, u64, u64) {
    let slot = TotalAccount::storage_layout().enc_pk.slot;
    env.private_context_opts(
        PrivateContextOptions::new().at_contract_address(b).at_anchor_block_number(n),
        |context: &mut PrivateContext| {
            let var = DelayedPublicMutable::<EncKey, ENC_KEY_INITIAL_DELAY, &mut PrivateContext>::new(
                context,
                slot,
            );
            let (key, ok): (EncKey, bool) = delayed_public_mutable_read_or(context, var);
            assert(ok);
            (
                key, context.finish().expiration_timestamp,
                context.get_anchor_block_header().timestamp(),
            )
        },
    )
}

unconstrained fn deploy_account_with(
    env: TestEnvironment,
    secret: Field,
    sx: Field,
    sy: Field,
    enc_x: Field,
    enc_y: Field,
) -> AztecAddress {
    let b = instantiate(secret, sx, sy, enc_x, enc_y);
    construct(env, b, sx, sy, enc_x, enc_y);
    b
}

/// Register a TotalAccount instance whose address commits to these
/// constructor arguments, with keys derived from secret, without running
/// the constructor.
unconstrained fn instantiate(
    secret: Field,
    sx: Field,
    sy: Field,
    enc_x: Field,
    enc_y: Field,
) -> AztecAddress {
    let init = TotalAccount::interface().constructor(sx, sy, enc_x, enc_y);
    txe_oracles::deploy(
        "TotalAccount",
        init.name,
        init.args,
        secret,
        0,
        AztecAddress::zero(),
        0,
    )
        .to_address()
}

/// Run b's constructor from its own address, in a transaction of its own.
unconstrained fn construct(
    env: TestEnvironment,
    b: AztecAddress,
    sx: Field,
    sy: Field,
    enc_x: Field,
    enc_y: Field,
) {
    let init = TotalAccount::interface().constructor(sx, sy, enc_x, enc_y);
    let _: () = env.call_private(b, PrivateCall::new(b, init.selector, init.name, init.args));
}

unconstrained fn assert_masked(r: (Field, Field, [Field; 5], bool)) {
    let (ex, ey, ct, ok) = r;
    assert(!ok);
    assert_eq(ex, 0);
    assert_eq(ey, 0);
    assert_eq(ct, [0; 5]);
}

/// Check that r opens under sk to MSG.
unconstrained fn assert_opens(
    env: TestEnvironment,
    b: AztecAddress,
    sk: Field,
    r: (Field, Field, [Field; 5], bool),
) {
    let (ex, ey, ct, ok) = r;
    assert(ok);
    let (m, opened) = env.execute_utility(TotalAccount::at(b).decrypt_for_owner(sk, ex, ey, ct));
    assert(opened);
    assert_eq(m, MSG);
}

#[test]
unconstrained fn owner_encrypts_and_decrypts() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account(env, 0xb0b, x, y);
    let (ex, ey, ct, ok) = env.call_private(b, TotalAccount::at(b).encrypt_for_owner(MSG, R));
    assert_opens(env, b, ENC_SK, (ex, ey, ct, ok));
    // a corrupted ciphertext does not open
    let mut bad = ct;
    bad[2] += 1;
    let (_, opened_bad) =
        env.execute_utility(TotalAccount::at(b).decrypt_for_owner(ENC_SK, ex, ey, bad));
    assert(!opened_bad);
}

// Another account's call, with only its own scope: the key is public
// state, so the third party reads it and encrypts. This is the production
// path (no access to the account's secrets).
#[test]
unconstrained fn third_party_encrypts() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account(env, 0xb0b, x, y);
    let a = env.create_light_account();
    assert_opens(
        env,
        b,
        ENC_SK,
        env.call_private(a, TotalAccount::at(b).encrypt_for_owner(MSG, R)),
    );
}

// The first key is scheduled by the constructor: until the delay passes
// there is no current key, and a third party's call returns ok = false,
// not a failure. Once it has passed the call encrypts.
#[test]
unconstrained fn a_new_accounts_key_is_current_after_the_delay() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account_pending(env, 0xb0b, x, y);
    let a = env.create_light_account();
    assert_masked(
        env.call_private(a, TotalAccount::at(b).encrypt_for_owner(MSG, R)),
    );
    wait_out_delay(env);
    assert_opens(
        env,
        b,
        ENC_SK,
        env.call_private(a, TotalAccount::at(b).encrypt_for_owner(MSG, R)),
    );
}

// An account that was never constructed: no initialization nullifier and
// no key (the slot reads (0, 0)). The call returns ok = false instead of
// failing, for a third party and for the address itself.
#[test]
unconstrained fn uninitialized_account_gets_a_flag() {
    let mut env = TestEnvironment::new();
    let u = env.deploy("TotalAccount").without_initializer();
    let a = env.create_light_account();
    assert_masked(
        env.call_private(a, TotalAccount::at(u).encrypt_for_owner(MSG, R)),
    );
    assert_masked(
        env.call_private(u, TotalAccount::at(u).encrypt_for_owner(MSG, R)),
    );
}

/// Schedule an arbitrary key in an account's delayed key slot as the
/// contract itself in public, bypassing set_encryption_key's refusal, and
/// wait out the delay so the key is current. This stands for stored state
/// the contract's own writer would refuse: not reachable with this
/// class, planted to show the read path flags it anyway.
unconstrained fn plant_key(env: TestEnvironment, u: AztecAddress, x: Field, y: Field) {
    let slot = TotalAccount::storage_layout().enc_pk.slot;
    env.public_context_at(u, |context: PublicContext| {
        DelayedPublicMutable::<EncKey, ENC_KEY_INITIAL_DELAY, PublicContext>::new(context, slot)
            .schedule_value_change(EncKey { x, y });
    });
    wait_out_delay(env);
}

// Control for the tests below: a planted valid key is read and used.
#[test]
unconstrained fn planted_valid_key_encrypts() {
    let mut env = TestEnvironment::new();
    let u = env.deploy("TotalAccount").without_initializer();
    let a = env.create_light_account();
    let (x, y) = pk(ENC_SK);
    plant_key(env, u, x, y);
    let (ex, ey, ct, ok) = env.call_private(a, TotalAccount::at(u).encrypt_for_owner(MSG, R));
    assert(ok);
    // ecies::open directly: the decrypt_for_owner utility carries aztec-nr's
    // utility initialization check, which this never-constructed account fails.
    let (m, opened) = ecies::open(ENC_SK, ex, ey, ct);
    assert(opened);
    assert_eq(m, MSG);
}

#[test]
unconstrained fn planted_off_curve_key_gets_a_flag() {
    let mut env = TestEnvironment::new();
    let u = env.deploy("TotalAccount").without_initializer();
    let a = env.create_light_account();
    let (x, y) = pk(ENC_SK);
    plant_key(env, u, x, y + 1);
    assert_masked(
        env.call_private(a, TotalAccount::at(u).encrypt_for_owner(MSG, R)),
    );
}

#[test]
unconstrained fn planted_field_max_key_gets_a_flag() {
    let mut env = TestEnvironment::new();
    let u = env.deploy("TotalAccount").without_initializer();
    let a = env.create_light_account();
    plant_key(env, u, -1, -1);
    assert_masked(
        env.call_private(a, TotalAccount::at(u).encrypt_for_owner(MSG, R)),
    );
}

// (0, 0) written explicitly is the same storage as a key never set.
#[test]
unconstrained fn planted_infinity_key_gets_a_flag() {
    let mut env = TestEnvironment::new();
    let u = env.deploy("TotalAccount").without_initializer();
    let a = env.create_light_account();
    let (x, y) = pk(ENC_SK);
    plant_key(env, u, x, y);
    plant_key(env, u, 0, 0);
    assert_masked(
        env.call_private(a, TotalAccount::at(u).encrypt_for_owner(MSG, R)),
    );
}

#[test]
unconstrained fn zero_randomness_gets_a_flag() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account(env, 0xb0b, x, y);
    let a = env.create_light_account();
    assert_masked(
        env.call_private(a, TotalAccount::at(b).encrypt_for_owner(MSG, 0)),
    );
}

// The owner rotates the key with a public call from its own address (in
// production: a public call in a payload signed through the entrypoint).
// Until the delay passes a third party still encrypts to the current
// key; afterwards, to the new one.
#[test]
unconstrained fn owner_rotates_the_key() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account(env, 0xb0b, x, y);
    let a = env.create_light_account();
    let (x2, y2) = pk(ENC_SK_2);
    env.call_public(b, TotalAccount::at(b).set_encryption_key(x2, y2));
    assert_opens(
        env,
        b,
        ENC_SK,
        env.call_private(a, TotalAccount::at(b).encrypt_for_owner(MSG, R)),
    );
    wait_out_delay(env);
    let (ex, ey, ct, ok) = env.call_private(a, TotalAccount::at(b).encrypt_for_owner(MSG, R));
    assert_opens(env, b, ENC_SK_2, (ex, ey, ct, ok));
    let (_, opened_old) =
        env.execute_utility(TotalAccount::at(b).decrypt_for_owner(ENC_SK, ex, ey, ct));
    assert(!opened_old);
}

// The read is the current value at the anchor block, known correct up
// to the expiration it sets: readers anchored before the change takes
// effect see the old key, and those after it the new one.
#[test]
unconstrained fn readers_see_the_key_current_at_their_anchor() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account(env, 0xb0b, x, y);
    let before = env.last_block_number();
    let (x2, y2) = pk(ENC_SK_2);
    env.call_public(b, TotalAccount::at(b).set_encryption_key(x2, y2));
    let pending = env.last_block_number();
    wait_out_delay(env);
    let (at_before, _, _) = read_key_at(env, b, before);
    let (at_pending, _, _) = read_key_at(env, b, pending);
    let (after, _, _) = read_key_at(env, b, env.last_block_number());
    assert_eq(at_before, EncKey { x, y });
    assert_eq(at_pending, EncKey { x, y });
    assert_eq(after, EncKey { x: x2, y: y2 });
}

// With no change pending, a read sets the expiration to anchor + delay -
// 1 second.
#[test]
unconstrained fn a_read_with_nothing_pending_expires_a_delay_later() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account(env, 0xb0b, x, y);
    let (key, expiration, anchor) = read_key_at(env, b, env.last_block_number());
    assert_eq(key, EncKey { x, y });
    assert_eq(expiration, anchor + ENC_KEY_INITIAL_DELAY - 1);
}

// With a key change pending, a read's expiration stops just before the
// change. A reader anchored one second before it gets an expiration equal
// to its anchor's timestamp (only a block sharing that timestamp could
// include the transaction), and one anchored at the change gets the full
// window again: the only short window the owner can cause, and it ends
// at the change.
#[test]
unconstrained fn a_pending_change_shortens_the_expiration_up_to_the_change() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account(env, 0xb0b, x, y);
    let (x2, y2) = pk(ENC_SK_2);
    env.call_public(b, TotalAccount::at(b).set_encryption_key(x2, y2));
    let change = env.last_block_timestamp() + ENC_KEY_INITIAL_DELAY;

    env.mine_block_at(change - 1);
    let (key, expiration, anchor) = read_key_at(env, b, env.last_block_number());
    assert_eq(key, EncKey { x, y });
    assert_eq(anchor, change - 1);
    assert_eq(expiration, change - 1);

    env.mine_block_at(change);
    let (key, expiration, anchor) = read_key_at(env, b, env.last_block_number());
    assert_eq(key, EncKey { x: x2, y: y2 });
    assert_eq(expiration, anchor + ENC_KEY_INITIAL_DELAY - 1);
}

#[test(should_fail_with = "can only be called by the same contract")]
unconstrained fn only_the_account_sets_the_key() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account(env, 0xb0b, x, y);
    let a = env.create_light_account();
    let (x2, y2) = pk(ENC_SK_2);
    env.call_public(a, TotalAccount::at(b).set_encryption_key(x2, y2));
}

#[test(should_fail_with = "encryption key is not a finite curve point")]
unconstrained fn rotation_refuses_an_off_curve_key() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account(env, 0xb0b, x, y);
    env.call_public(b, TotalAccount::at(b).set_encryption_key(x, y + 1));
}

#[test(should_fail_with = "encryption key is not a finite curve point")]
unconstrained fn rotation_refuses_infinity() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account(env, 0xb0b, x, y);
    env.call_public(b, TotalAccount::at(b).set_encryption_key(0, 0));
}

#[test(should_fail_with = "encryption key is not a finite curve point")]
unconstrained fn rotation_refuses_field_max_coordinates() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account(env, 0xb0b, x, y);
    env.call_public(b, TotalAccount::at(b).set_encryption_key(-1, -1));
}

#[test(should_fail_with = "encryption key is not a finite curve point")]
unconstrained fn constructor_refuses_an_off_curve_key() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let _ = deploy_account(env, 0xb0b, x, y + 1);
}

/// An AppPayload whose first call goes to target (zero means no call).
unconstrained fn payload_calling(target: AztecAddress, tx_nonce: Field) -> AppPayload {
    let call = FunctionCall {
        args_hash: 0,
        function_selector: FunctionSelector::from_field(0),
        target_address: target,
        is_public: true,
        hide_msg_sender: false,
        is_static: false,
    }
        .serialize();
    let stride = <FunctionCall as Serialize>::N;
    let mut fields = [0; 5 * <FunctionCall as Serialize>::N + 1];
    for j in 0..stride {
        fields[j] = call[j];
    }
    fields[5 * stride] = tx_nonce;
    AppPayload::deserialize(fields)
}

/// The key TXE signs b's authwits with: the master incoming viewing key
/// of the account keys derived from secret. The keys depend only on the
/// secret, so they are read from a second, uninitialised instance.
unconstrained fn txe_signing_key(mut env: TestEnvironment, secret: Field) -> (Field, Field) {
    let probe = env
        .deploy_opts(DeployOptions::new().with_secret(secret).with_salt(1), "TotalAccount")
        .without_initializer();
    let iv = env.utility_context(|_context| get_public_keys(probe)).ivpk_m.inner;
    (iv.x, iv.y)
}

/// The account's signing key set to the key TXE signs its authwits with.
unconstrained fn deploy_txe_signed_account(env: TestEnvironment, secret: Field) -> AztecAddress {
    let (sx, sy) = txe_signing_key(env, secret);
    let (x, y) = pk(ENC_SK);
    deploy_account_with(env, secret, sx, sy, x, y)
}

#[test]
unconstrained fn entrypoint_accepts_a_signed_payload() {
    let mut env = TestEnvironment::new();
    let b = deploy_txe_signed_account(env, 0xb0b);
    let payload = payload_calling(AztecAddress::zero(), 42);
    let (chain_id, version) =
        env.utility_context(|context| (context.chain_id(), context.version()));
    txe_oracles::add_authwit(
        b,
        compute_authwit_message_hash(b, chain_id, version, payload.hash()),
    );
    let _: () = env.call_private(b, TotalAccount::at(b).entrypoint(payload, 0, false));
}

// A witness TXE signed with the account's viewing key, while the stored
// signing key is a different one: the witness exists, the signature check
// returns false, and the entrypoint's boundary assert fails (it has no
// message; the same flow with the matching key passes above).
#[test(should_fail_with = "Cannot satisfy constraint")]
unconstrained fn entrypoint_refuses_a_wrong_key_signature() {
    let mut env = TestEnvironment::new();
    let (x, y) = pk(ENC_SK);
    let b = deploy_account(env, 0xb0b, x, y);
    let payload = payload_calling(AztecAddress::zero(), 42);
    let (chain_id, version) =
        env.utility_context(|context| (context.chain_id(), context.version()));
    txe_oracles::add_authwit(
        b,
        compute_authwit_message_hash(b, chain_id, version, payload.hash()),
    );
    let _: () = env.call_private(b, TotalAccount::at(b).entrypoint(payload, 0, false));
}

// Two-phase signing key (signing_key.nr). The tests sign with TXE's
// authwit key, so the accounts' constructor signing key is that key
// unless a test says otherwise.

global MULTICALL: str<46> = "../total_account_multicall@multicall/MultiCall";
global INNER: Field = 0x1a2b;

/// initializer_args_or at b, at anchor block n, after stored was recorded
/// as record_initializer_args records it (in the same context, as the
/// constructor does earlier in a self-paid deployment).
unconstrained fn initial_args_after<let K: u32>(
    env: TestEnvironment,
    b: AztecAddress,
    n: u32,
    stored: [Field; K],
) -> InitializerArgs<4> {
    env.private_context_opts(
        PrivateContextOptions::new().at_contract_address(b).at_anchor_block_number(n),
        |context: &mut PrivateContext| {
            record_initializer_args(stored);
            initializer_args_or::<4>(context, CONSTRUCTOR_SELECTOR)
        },
    )
}

/// initializer_args_or at b, at anchor block n, with nothing recorded.
unconstrained fn initial_args_at(
    env: TestEnvironment,
    b: AztecAddress,
    n: u32,
) -> InitializerArgs<4> {
    env.private_context_opts(
        PrivateContextOptions::new().at_contract_address(b).at_anchor_block_number(n),
        |context: &mut PrivateContext| initializer_args_or::<4>(context, CONSTRUCTOR_SELECTOR),
    )
}

/// An account not yet constructed whose constructor signing key is the key
/// TXE signs with: (address, constructor arguments).
unconstrained fn txe_signed_instance(
    env: TestEnvironment,
    secret: Field,
) -> (AztecAddress, [Field; 4]) {
    let (sx, sy) = txe_signing_key(env, secret);
    let (ex, ey) = pk(ENC_SK);
    (instantiate(secret, sx, sy, ex, ey), [sx, sy, ex, ey])
}

/// Sign INNER for consumer a with b's TXE key and run b's private authwit
/// check as a's static call, with b's secrets in scope when owner_scope.
unconstrained fn authwit_check(
    env: TestEnvironment,
    a: AztecAddress,
    b: AztecAddress,
    owner_scope: bool,
) -> Field {
    let (chain_id, version) =
        env.utility_context(|context| (context.chain_id(), context.version()));
    txe_oracles::add_authwit(b, compute_authwit_message_hash(a, chain_id, version, INNER));
    let call = TotalAccount::at(b).verify_private_authwit(INNER);
    if owner_scope {
        env.view_private_opts(a, ViewPrivateOptions::new().with_additional_scopes([b]), call)
    } else {
        env.view_private(a, call)
    }
}

/// A self-paid deployment as aztec.js v6 makes it: one transaction calls
/// b's constructor, then b's entrypoint with a payload TXE signed with
/// b's key (made from MultiCall; see its header). The fee payment method
/// is EXTERNAL: the TXE marks every side effect revertible, so electing
/// the account as fee payer fails there ("fee payer must be elected
/// during the setup phase"). AccountActions::entrypoint checks the
/// signature before it looks at the fee payment method.
unconstrained fn self_paid_deploy(mut env: TestEnvironment, b: AztecAddress, args: [Field; 4]) {
    let payload = payload_calling(AztecAddress::zero(), 42);
    let (chain_id, version) =
        env.utility_context(|context| (context.chain_id(), context.version()));
    txe_oracles::add_authwit(
        b,
        compute_authwit_message_hash(b, chain_id, version, payload.hash()),
    );
    let init = TotalAccount::interface().constructor(args[0], args[1], args[2], args[3]);
    let entry = TotalAccount::at(b).entrypoint(payload, 0, false);
    let m = env.deploy(MULTICALL).without_initializer();
    let mut call_args = [0; 40];
    call_args[0] = b.to_field();
    call_args[1] = init.selector.to_field();
    for i in 0..4 {
        call_args[2 + i] = init.args[i];
    }
    call_args[6] = entry.selector.to_field();
    for i in 0..33 {
        call_args[7 + i] = entry.args[i];
    }
    let selector =
        FunctionSelector::from_signature("call_twice((Field),(u32),[Field;4],(u32),[Field;33])");
    let sender = env.create_light_account();
    let _: () = env.call_private_opts(
        sender,
        CallPrivateOptions::new().with_additional_scopes([b]),
        PrivateCall::new(m, selector, "call_twice", call_args),
    );
}

#[test]
unconstrained fn the_constructor_selector_is_the_initializers() {
    let init = TotalAccount::interface().constructor(1, 2, 3, 4);
    assert_eq(init.selector, CONSTRUCTOR_SELECTOR);
}

// The self-paid deployment: the constructor, then the entrypoint, in one
// transaction. The entrypoint's note read cannot see the key note (a
// pending note of another call) and the initialisation nullifier is not
// in the anchor block's tree, so the key the constructor recorded,
// checked against the address, is the one checked.
#[test]
unconstrained fn a_self_paid_deployment_runs_the_entrypoint_after_the_constructor() {
    let mut env = TestEnvironment::new();
    let (b, args) = txe_signed_instance(env, 0xb0b);
    self_paid_deploy(env, b, args);
    // the deployment initialised the account: from here on the note decides
    let initial = initial_args_at(env, b, env.last_block_number());
    assert(initial.initialized & !initial.bound);
    assert_eq(authwit_check(env, env.create_light_account(), b, true), IS_VALID_SELECTOR);
}

// The same deployment with a constructor key other than the one that
// signed: the key is bound, the signature check is false, and the
// entrypoint's boundary assert (which has no message) fails.
#[test(should_fail_with = "Cannot satisfy constraint")]
unconstrained fn a_self_paid_deployment_signed_by_another_key_is_refused() {
    let mut env = TestEnvironment::new();
    let (sx, sy) = pk(SIGN_SK);
    let (ex, ey) = pk(ENC_SK);
    let b = instantiate(0xb0b, sx, sy, ex, ey);
    self_paid_deploy(env, b, [sx, sy, ex, ey]);
}

// Outside the constructor's transaction an honest PXE has no recorded
// arguments, so a never-constructed account authorises nothing, as before.
#[test(should_fail_with = "Message not authorized by account")]
unconstrained fn without_the_constructor_in_the_transaction_nothing_signs() {
    let mut env = TestEnvironment::new();
    let (b, _) = txe_signed_instance(env, 0xb0b);
    let _ = authwit_check(env, env.create_light_account(), b, false);
}

// After initialisation the key note signs.
#[test]
unconstrained fn after_initialisation_the_note_key_signs() {
    let mut env = TestEnvironment::new();
    let (b, args) = txe_signed_instance(env, 0xb0b);
    construct(env, b, args[0], args[1], args[2], args[3]);
    assert_eq(authwit_check(env, env.create_light_account(), b, true), IS_VALID_SELECTOR);
}

// The phase follows the anchor block. At a fresh anchor after the
// constructor's block the account is initialised, so even the committed
// arguments, bound, no longer decide (signing_key_or takes the note);
// anchored before that block, a transaction still sees the account as not
// initialised and the constructor's key as the one to check (the caveat
// in README.md).
#[test]
unconstrained fn the_phase_is_read_at_the_anchor_block() {
    let mut env = TestEnvironment::new();
    let (b, args) = txe_signed_instance(env, 0xb0b);
    let before = env.last_block_number();
    construct(env, b, args[0], args[1], args[2], args[3]);
    let fresh = initial_args_after(env, b, env.last_block_number(), args);
    assert(fresh.initialized & fresh.bound);
    let old = initial_args_after(env, b, before, args);
    assert(!old.initialized & old.bound);
    assert_eq(old.args, args);
}

// Hints that are not the committed arguments are bound = false with zero
// arguments, and nothing fails.
#[test]
unconstrained fn wrong_initializer_arguments_are_flags() {
    let mut env = TestEnvironment::new();
    let (b, args) = txe_signed_instance(env, 0xb0b);
    let n = env.last_block_number();
    let none = initial_args_at(env, b, n);
    assert(!none.bound & !none.initialized);
    assert_eq(none.args, [0; 4]);
    // another encryption key, another signing key, all zeros
    let other_enc = initial_args_after(env, b, n, [args[0], args[1], args[2], args[3] + 1]);
    assert(!other_enc.bound);
    assert_eq(other_enc.args, [0; 4]);
    let (x, y) = pk(SIGN_SK);
    assert(!initial_args_after(env, b, n, [x, y, args[2], args[3]]).bound);
    assert(!initial_args_after(env, b, n, [0; 4]).bound);
    // the committed arguments
    let right = initial_args_after(env, b, n, args);
    assert(right.bound & !right.initialized);
    assert_eq(right.args, args);
}

// A record of another length (record_initializer_args with another N) is
// bound = false too: the read checks the length before it asks for any
// element.
#[test]
unconstrained fn a_record_of_another_length_is_a_flag() {
    let mut env = TestEnvironment::new();
    let (b, args) = txe_signed_instance(env, 0xb0b);
    let n = env.last_block_number();
    let long = initial_args_after(env, b, n, [args[0], args[1], args[2], args[3], 0]);
    assert(!long.bound);
    assert_eq(long.args, [0; 4]);
    assert(!initial_args_after(env, b, n, [args[0], args[1], args[2]]).bound);
    let empty: [Field; 0] = [];
    assert(!initial_args_after(env, b, n, empty).bound);
}

// What still fails the reader: an element of another width at the slot,
// which only class code writing the slot with the raw transient oracles
// can create (here aztec-nr's TransientArray of two-Field elements, four
// of them, so the length matches). The PXE answers with the stored width
// and the Brillig VM refuses it.
#[test(should_fail_with = "does not match expected size")]
unconstrained fn a_wider_element_written_outside_the_library_fails_the_reader() {
    let mut env = TestEnvironment::new();
    let (b, _) = txe_signed_instance(env, 0xb0b);
    env.private_context_opts(
        PrivateContextOptions::new().at_contract_address(b),
        |context: &mut PrivateContext| {
            let wide = TransientArray::<[Field; 2]>::at(INITIALIZER_ARGS_SLOT);
            for i in 0..4 {
                wide.push([i as Field, 0]);
            }
            let _ = initializer_args_or::<4>(context, CONSTRUCTOR_SELECTOR);
        },
    );
}
