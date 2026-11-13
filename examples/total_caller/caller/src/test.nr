//! TXE tests: A's transaction against a total account and against a
//! griefing one, in the same owner-controlled states. A's user holds only
//! its own scope in every test (no access to B's secrets), as in
//! production. Run with
//! `nargo test --oracle-resolver http://127.0.0.1:<port>`
//! after `bb aztec_process` on all four artifacts (run.sh does both).

use crate::Caller;
use aztec::context::{calls::PrivateCall, PublicContext};
use aztec::protocol::address::AztecAddress;
use aztec::state_vars::{DelayedPublicMutable, StateVariable};
use aztec::test::helpers::{test_environment::TestEnvironment, txe_oracles};
use grief_account::GriefAccount;
use std::embedded_curve_ops::{EmbeddedCurveScalar, fixed_base_scalar_mul};
use std::hash::poseidon2_permutation;
use total_account::{enc_key::{ENC_KEY_INITIAL_DELAY, EncKey}, TotalAccount};

global SIGN_SK: Field = 0x0a11ce;
global ENC_SK: Field = 0x1d7a0b3c5e9f21a4c6b8d0e2f4a6c8e0b2d4f6a8c0e2b4d6f8a0c2e4b6d8f0a;
global ENC_SK_2: Field = 0x2b0b;
global R: Field = 0x2f1e3d5c7b9a8f6e4d2c1b0a99887766554433221100ffeeddccbbaa998877;
global MSG: [Field; 4] = [0x11, 0x22, 0x33, 0x44];

/// TotalAccount's artifact, in the workspace-relative form
/// "<dir>@<package>/<contract>". TXE 6.0.0 mis-resolves the plain
/// "<dir>/<contract>" form (it drops the directory).
global TOTAL_ACCOUNT: str<43> = "../total_account@total_account/TotalAccount";

unconstrained fn pk(sk: Field) -> (Field, Field) {
    let p = fixed_base_scalar_mul(EmbeddedCurveScalar::from_field(sk));
    (p.x, p.y)
}

/// Deploy TotalAccount with its constructor run from its own address (as
/// total_account's tests do). The constructor schedules the key, so this
/// waits out the delay and the account has its key.
unconstrained fn deploy_total(env: TestEnvironment, secret: Field) -> AztecAddress {
    let (sx, sy) = pk(SIGN_SK);
    let (ex, ey) = pk(ENC_SK);
    let init = TotalAccount::interface().constructor(sx, sy, ex, ey);
    let b = txe_oracles::deploy(
        TOTAL_ACCOUNT,
        init.name,
        init.args,
        secret,
        0,
        AztecAddress::zero(),
        0,
    )
        .to_address();
    let _: () = env.call_private(b, PrivateCall::new(b, init.selector, init.name, init.args));
    wait_out_delay(env);
    b
}

/// Mine a block ENC_KEY_INITIAL_DELAY after the last one, so a key
/// scheduled at the last block's timestamp is current at the next anchor.
unconstrained fn wait_out_delay(env: TestEnvironment) {
    env.mine_block_at(env.last_block_timestamp() + ENC_KEY_INITIAL_DELAY);
}

/// Deploy GriefAccount storing (x, y) unchecked, through its public
/// constructor, sent by deployer.
unconstrained fn deploy_grief(
    mut env: TestEnvironment,
    deployer: AztecAddress,
    x: Field,
    y: Field,
) -> AztecAddress {
    env.deploy("@grief_account/GriefAccount").with_public_initializer(
        deployer,
        GriefAccount::interface().constructor(x, y),
    )
}

/// A's user calls Caller.seal_to(b, ...) with its own scope only.
unconstrained fn seal(
    mut env: TestEnvironment,
    user: AztecAddress,
    a: AztecAddress,
    b: AztecAddress,
) -> ([Field; 7], bool) {
    env.call_private(user, Caller::at(a).seal_to(b, MSG, R))
}

unconstrained fn setup() -> (TestEnvironment, AztecAddress, AztecAddress) {
    let mut env = TestEnvironment::new();
    let a = env.deploy("@caller/Caller").without_initializer();
    let user = env.create_light_account();
    (env, a, user)
}

unconstrained fn assert_opens(env: TestEnvironment, b: AztecAddress, sk: Field, out: [Field; 7]) {
    let ct = [out[2], out[3], out[4], out[5], out[6]];
    let (m, opened) =
        env.execute_utility(TotalAccount::at(b).decrypt_for_owner(sk, out[0], out[1], ct));
    assert(opened);
    assert_eq(m, MSG);
}

/// Schedule an arbitrary key in TotalAccount's delayed key slot, as the
/// contract in public, bypassing set_encryption_key's refusal, and wait
/// out the delay. Not reachable with TotalAccount's class (its only
/// writer refuses such keys); planted to show the read path flags it
/// anyway.
unconstrained fn plant_total_key(env: TestEnvironment, b: AztecAddress, x: Field, y: Field) {
    let slot = TotalAccount::storage_layout().enc_pk.slot;
    env.public_context_at(b, |context: PublicContext| {
        DelayedPublicMutable::<EncKey, ENC_KEY_INITIAL_DELAY, PublicContext>::new(context, slot)
            .schedule_value_change(EncKey { x, y });
    });
    wait_out_delay(env);
}

// (a) TotalAccount.

#[test]
unconstrained fn total_account_with_a_good_key_encrypts() {
    let (env, a, user) = setup();
    let b = deploy_total(env, 0xb0b);
    let (out, ok) = seal(env, user, a, b);
    assert(ok);
    assert_opens(env, b, ENC_SK, out);
}

#[test]
unconstrained fn total_account_after_a_rotation_encrypts_to_the_new_key() {
    let (env, a, user) = setup();
    let b = deploy_total(env, 0xb0b);
    let (x2, y2) = pk(ENC_SK_2);
    env.call_public(b, TotalAccount::at(b).set_encryption_key(x2, y2));
    wait_out_delay(env);
    let (out, ok) = seal(env, user, a, b);
    assert(ok);
    assert_opens(env, b, ENC_SK_2, out);
}

// The new key is scheduled, so a call before the delay passes goes to the
// current key and still completes.
#[test]
unconstrained fn total_account_during_a_rotation_encrypts_to_the_current_key() {
    let (env, a, user) = setup();
    let b = deploy_total(env, 0xb0b);
    let (x2, y2) = pk(ENC_SK_2);
    env.call_public(b, TotalAccount::at(b).set_encryption_key(x2, y2));
    let (out, ok) = seal(env, user, a, b);
    assert(ok);
    assert_opens(env, b, ENC_SK, out);
}

#[test]
unconstrained fn total_account_never_constructed_gives_ok_false() {
    let (mut env, a, user) = setup();
    let b = env.deploy(TOTAL_ACCOUNT).without_initializer();
    assert_eq(seal(env, user, a, b), ([0; 7], false));
}

// The owner cannot store a bad key: its own transaction fails, so the
// stored key stays the good one (the test above reads it).
#[test(should_fail_with = "encryption key is not a finite curve point")]
unconstrained fn total_account_refuses_an_off_curve_key_from_its_owner() {
    let (env, _a, _user) = setup();
    let b = deploy_total(env, 0xb0b);
    let (x, y) = pk(ENC_SK);
    env.call_public(b, TotalAccount::at(b).set_encryption_key(x, y + 1));
}

#[test]
unconstrained fn total_account_with_a_planted_off_curve_key_gives_ok_false() {
    let (mut env, a, user) = setup();
    let b = env.deploy(TOTAL_ACCOUNT).without_initializer();
    let (x, y) = pk(ENC_SK);
    plant_total_key(env, b, x, y + 1);
    assert_eq(seal(env, user, a, b), ([0; 7], false));
}

#[test]
unconstrained fn total_account_with_a_planted_field_max_key_gives_ok_false() {
    let (mut env, a, user) = setup();
    let b = env.deploy(TOTAL_ACCOUNT).without_initializer();
    plant_total_key(env, b, -1, -1);
    assert_eq(seal(env, user, a, b), ([0; 7], false));
}

#[test]
unconstrained fn total_account_with_a_planted_infinity_key_gives_ok_false() {
    let (env, a, user) = setup();
    let b = deploy_total(env, 0xb0b);
    plant_total_key(env, b, 0, 0);
    assert_eq(seal(env, user, a, b), ([0; 7], false));
}

// The return arity is part of the interface A trusts: a callee with the
// same selector and a two-Field return fails A's call at the
// returns-preimage oracle (it expects eight Fields), before any of A's
// constraints. A property of the callee's class.
#[test(should_fail_with = "does not match expected size")]
unconstrained fn a_callee_with_another_return_arity_fails_a() {
    let (mut env, a, user) = setup();
    let b = env.deploy("@short_account/ShortAccount").without_initializer();
    let _ = seal(env, user, a, b);
}

// (b) GriefAccount, same states. Every one of these is reachable with
// GriefAccount's class: its constructor stores whatever it is given.

// Control: with a good key the griefing account works, so the failures
// below come from the state, not from the plumbing.
#[test]
unconstrained fn grief_account_with_a_good_key_encrypts() {
    let (env, a, user) = setup();
    let (x, y) = pk(ENC_SK);
    let b = deploy_grief(env, user, x, y);
    let (_, ok) = seal(env, user, a, b);
    assert(ok);
}

#[test(should_fail_with = "Trying to read from uninitialized PublicImmutable")]
unconstrained fn grief_account_never_constructed_fails_a() {
    let (mut env, a, user) = setup();
    let b = env.deploy("@grief_account/GriefAccount").without_initializer();
    let _ = seal(env, user, a, b);
}

#[test(should_fail_with = "is not on curve")]
unconstrained fn grief_account_with_an_off_curve_key_fails_a() {
    let (env, a, user) = setup();
    let (x, y) = pk(ENC_SK);
    let b = deploy_grief(env, user, x, y + 1);
    let _ = seal(env, user, a, b);
}

#[test(should_fail_with = "is not on curve")]
unconstrained fn grief_account_with_a_field_max_key_fails_a() {
    let (env, a, user) = setup();
    let b = deploy_grief(env, user, -1, -1);
    let _ = seal(env, user, a, b);
}

// Not a failure: std's MSM takes (0, 0) and returns infinity, so the
// shared secret's x is 0 and A gets ok = true with a ciphertext anyone
// can open. A confidentiality failure, not griefing.
#[test]
unconstrained fn grief_account_with_an_infinity_key_leaks_the_plaintext() {
    let (env, a, user) = setup();
    let b = deploy_grief(env, user, 0, 0);
    let (out, ok) = seal(env, user, a, b);
    assert(ok);
    // GriefAccount's AE with key 0: the first block is the permutation of
    // [0, E.x, 0, 0], computable by anyone from the public output.
    let s = poseidon2_permutation([0, out[0], 0, 0]);
    assert_eq([out[2] - s[0], out[3] - s[1], out[4] - s[2]], [MSG[0], MSG[1], MSG[2]]);
}
