//! TotalAccount: a Schnorr account contract whose code that other users'
//! transactions run cannot be made to fail by the account's owner.
//!
//! When user A's transaction calls this account's encrypt_for_owner, A's
//! PXE executes this code against state the account's owner B controls
//! (the stored encryption key, or its absence). Every failure B can cause
//! in that function's body becomes ok = false with all-zero outputs: a
//! key never set or not yet current, an off-curve or infinity key, and
//! every curve or encryption step. Inputs A controls (the randomness) are
//! flagged the same way. What stays outside (sync, class upgrades, the
//! expiration window) is listed in total_aztec's lib.nr header.
//!
//! The encryption key is public state in a DelayedPublicMutable, because
//! a third party's PXE never holds the owner's notes (total_aztec's
//! note.nr, "Who can read at all"). The owner's own path (entrypoint) is
//! a signature check that returns a flag, asserted once by aztec-nr's
//! AccountActions. The signing key has two phases (signing_key.nr): the
//! constructor's key, checked against the address, until the account is
//! initialised at the anchor block, then the key note. The first phase
//! lets the entrypoint run in the account's own deployment transaction
//! (a self-paid deployment), where the key note is a pending note of
//! another call that the entrypoint cannot read.

mod ecies;
pub mod enc_key;
mod public_key_note;
pub mod signing_key;
mod test;

use aztec::macros::aztec;

#[aztec]
pub contract TotalAccount {
    use aztec::{
        authwit::{
            account::AccountActions,
            auth::{compute_authwit_message_hash, compute_authwit_nullifier},
            entrypoint::app::AppPayload,
        },
        context::PrivateContext,
        hash::compute_siloed_nullifier,
        macros::{
            functions::{allow_phase_change, external, initializer, noinitcheck, only_self, view},
            storage::storage,
        },
        messages::delivery::MessageDelivery,
        oracle::{
            auth_witness::get_auth_witness,
            get_nullifier_membership_witness::get_low_nullifier_membership_witness,
        },
        protocol::address::AztecAddress,
        state_vars::{DelayedPublicMutable, SinglePrivateImmutable},
    };
    use total::schnorr_verify;
    use total_aztec::{
        delayed_public_mutable_read_or, initializer_args_or, record_initializer_args,
        refuse_bad_key, single_private_immutable_get_note_or,
    };

    use crate::{
        ecies,
        enc_key::{ENC_KEY_INITIAL_DELAY, EncKey},
        public_key_note::PublicKeyNote,
        signing_key::{CONSTRUCTOR_SELECTOR, signing_key_or},
    };

    #[storage]
    struct Storage<Context> {
        signing_public_key: SinglePrivateImmutable<PublicKeyNote, Context>,
        // DEV DECISION: where the encryption key lives. Options: a key note
        // (unreadable by third parties in v6, so every caller but the owner
        // gets ok = false), a PublicImmutable (no rotation), or a
        // DelayedPublicMutable. This code: DelayedPublicMutable; the key and
        // its rotations are public, and a read lowers the reader's
        // expiration (README, "Delay and expiration").
        enc_pk: DelayedPublicMutable<EncKey, ENC_KEY_INITIAL_DELAY, Context>,
    }

    /// Store the signing key and the encryption key.
    ///
    /// Both keys are refused unless they are finite curve points. These
    /// two asserts are input-falsifiable on purpose: they fail the
    /// deployment transaction, whose sender chose the arguments, instead
    /// of storing a key that would make every later signature check or
    /// encryption fail its flag. (The v6 schnorr account stores the
    /// signing key unchecked, so an off-curve key there bricks the
    /// account.) The read paths flag a bad key anyway.
    ///
    /// The encryption key is scheduled in public by set_encryption_key,
    /// enqueued here; it refuses the key again. Refusing it here as well
    /// makes a bad key fail the deployer's proof instead of reverting the
    /// deployment's public part. The key becomes current only after the
    /// initial delay (ENC_KEY_INITIAL_DELAY); until then readers get
    /// ok = false.
    #[external("private")]
    #[initializer]
    fn constructor(
        signing_pub_key_x: Field,
        signing_pub_key_y: Field,
        enc_pk_x: Field,
        enc_pk_y: Field,
    ) {
        // DEV DECISION: key policy at write time. Refuse a bad key (fail the
        // deployment) rather than store it; total_aztec::set_key_or is the
        // flag form that skips the write instead.
        // total-lint: allow write-time refusal: the constructor runs in the deployment transaction, whose sender chose the key
        refuse_bad_key(
            signing_pub_key_x,
            signing_pub_key_y,
            "signing key is not a finite curve point",
        );
        // total-lint: allow write-time refusal: the constructor runs in the deployment transaction, whose sender chose the key
        refuse_bad_key(
            enc_pk_x,
            enc_pk_y,
            "encryption key is not a finite curve point",
        );

        let pub_key_note = PublicKeyNote { x: signing_pub_key_x, y: signing_pub_key_y };
        // The deployer may be another account; tag the note with this
        // account's address so its own PXE discovers it.
        self.storage.signing_public_key.initialize(pub_key_note).deliver(
            MessageDelivery::onchain_unconstrained().with_sender(self.address),
        );
        self.enqueue_self.set_encryption_key(enc_pk_x, enc_pk_y);
        // For the entrypoint later in this transaction (a self-paid
        // deployment), which cannot read the key note just created: a hint
        // it checks against the address (signing_key.nr).
        record_initializer_args([signing_pub_key_x, signing_pub_key_y, enc_pk_x, enc_pk_y]);
    }

    /// Schedule a new encryption key, in public: it takes effect after
    /// the current delay. A change scheduled before the previous one takes
    /// effect replaces it. Owner only: #[only_self] asserts msg_sender ==
    /// this address, so the call must come from this contract: the
    /// constructor, or a public call in a payload signed through this
    /// account's entrypoint. The key is refused unless it is a finite
    /// curve point (off-curve, (0, 0) and coordinates such as (p - 1,
    /// p - 1) all fail key_ok): an input-falsifiable assert in the owner's
    /// own transaction, so the stored key is always a good one or never
    /// set.
    ///
    /// #[noinitcheck]: the constructor enqueues this before the contract
    /// counts as initialised in public, and #[only_self] already limits
    /// the callers to this account.
    #[external("public")]
    #[only_self]
    #[noinitcheck]
    fn set_encryption_key(x: Field, y: Field) {
        // DEV DECISION: refuse at write time (see the constructor), here in
        // public so that the only writer of the key checks it.
        refuse_bad_key(x, y, "encryption key is not a finite curve point");
        self.storage.enc_pk.schedule_value_change(EncKey { x, y });
    }

    /// Encrypt a 4-field plaintext to the owner's encryption key:
    /// (eph_pk_x, eph_pk_y, ciphertext, ok), the ciphertext four elements
    /// and a tag. Callable by any contract; this is the function other
    /// users' transactions execute. randomness must be fresh for every
    /// message (ecies.nr's header).
    ///
    /// No owner-controlled state and no input makes the body fail.
    /// #[noinitcheck] removes the macro's initialisation check. The key is
    /// read with total_aztec's delayed_public_mutable_read_or, which proves
    /// every slot of the variable at the anchor block and flags a stored
    /// state the variable's own functions cannot produce (aztec-nr's
    /// get_current_value asserts on it, and class code writing the slots
    /// directly can produce it), and lowers the transaction's expiration
    /// to the variable's time horizon. A key never set or not yet current
    /// reads as (0, 0), which seal_or refuses as infinity. On ok = false
    /// every returned Field is 0.
    ///
    /// DEV DECISION: no initialisation check. A never-constructed account
    /// reads as "no key"; fold total_aztec::contract_is_initialized into
    /// ok if callers need the distinction.
    #[external("private")]
    #[noinitcheck]
    fn encrypt_for_owner(
        plaintext: [Field; 4],
        randomness: Field,
    ) -> (Field, Field, [Field; 5], bool) {
        let (key, read) = delayed_public_mutable_read_or(self.context, self.storage.enc_pk);
        let sealed = ecies::seal_or(key.x, key.y, read, plaintext, randomness);
        (sealed.eph_pk_x, sealed.eph_pk_y, sealed.ciphertext, sealed.ok)
    }

    /// Owner-side decryption, for the owner's PXE: (plaintext, ok).
    /// Unconstrained and trap-free (ecies::open).
    ///
    /// The encryption secret is an argument, because it is a key of this
    /// example's own scheme, not one the PXE manages. A utility function
    /// runs in the caller's PXE, so the secret stays on the owner's
    /// machine, but it passes through the wallet's call path and any
    /// logging there. aztec-nr v6's PXE-held alternative
    /// (oracle/shared_secret.nr, get_shared_secret) derives an app-siloed
    /// secret from the account's address key, which would replace the
    /// stored key this example exists to show.
    #[external("utility")]
    unconstrained fn decrypt_for_owner(
        enc_sk: Field,
        eph_pk_x: Field,
        eph_pk_y: Field,
        ciphertext: [Field; 5],
    ) -> ([Field; 4], bool) {
        ecies::open(enc_sk, eph_pk_x, eph_pk_y, ciphertext)
    }

    /// The account entrypoint, as in the v6 schnorr account:
    /// AccountActions::entrypoint asserts is_valid_impl's flag once, then
    /// runs the payload. The assert guards the owner's own transaction;
    /// it is not code other users' transactions execute.
    #[external("private")]
    #[noinitcheck]
    #[allow_phase_change]
    fn entrypoint(app_payload: AppPayload, fee_payment_method: u8, cancellable: bool) {
        let actions = AccountActions::init(self.context, is_valid_impl);
        actions.entrypoint(app_payload, fee_payment_method, cancellable);
    }

    /// Private authwit check, as in the v6 schnorr account: the same
    /// total is_valid_impl and one boundary assert inside AccountActions,
    /// which is the authwit protocol's way of saying "not authorized".
    #[external("private")]
    #[noinitcheck]
    #[view]
    fn verify_private_authwit(inner_hash: Field) -> Field {
        let actions = AccountActions::init(self.context, is_valid_impl);
        actions.verify_private_authwit(inner_hash)
    }

    /// Signature check with no failure source of its own, in two phases
    /// (signing_key.nr). The constructor's arguments come from
    /// total_aztec's initializer_args_or (the arguments the constructor
    /// recorded earlier in this transaction, a hint checked against the
    /// address; none or wrong ones are bound = false), with the
    /// initialisation flag at the anchor block. The key note comes from
    /// single_private_immutable_get_note_or (no assert when the PXE has no
    /// note). Until the account is initialised at the anchor block the
    /// constructor's signing key must have signed, afterwards the note's:
    ///
    ///   valid = (!initialized & bound & schnorr(constructor key))
    ///         | (initialized & found & schnorr(note key))
    ///
    /// as one total::schnorr_verify on the selected key (flags an
    /// off-curve or (0, 0) key, non-canonical or out-of-range scalars,
    /// and wrong signatures; its MSM sees only validated, blinded inputs,
    /// so every key has a proof). The auth witness is the prover's: a
    /// wrong one gives false, and a missing one makes the PXE's oracle
    /// throw ("Unknown auth witness"), which fails the owner's own
    /// simulation, as in aztec-nr's v6 accounts. is_valid_impl only runs
    /// in the owner's own transaction, or in the transaction of whoever
    /// holds the owner's authwit, so no other transaction depends on that
    /// oracle.
    #[contract_library_method]
    fn is_valid_impl(context: &mut PrivateContext, outer_hash: Field) -> bool {
        let storage = Storage::init(context);
        let initial = initializer_args_or::<4>(context, CONSTRUCTOR_SELECTOR);
        let (note, found) = single_private_immutable_get_note_or::<PublicKeyNote>(
            context,
            storage.signing_public_key,
        );
        let (x, y, key_may_sign) = signing_key_or(initial, note.x, note.y, found);
        // Safety: the witness only feeds schnorr_verify, which returns
        // false for every witness that is not a valid signature. A missing
        // witness traps in the owner's own PXE (see above).
        let sig: [Field; 4] = unsafe { get_auth_witness(outer_hash) };
        key_may_sign & schnorr_verify(x, y, sig, outer_hash)
    }

    /// Off-chain authwit validity, as in the v6 schnorr account, with the
    /// signature check through schnorr_verify.
    #[external("utility")]
    unconstrained fn lookup_validity(consumer: AztecAddress, inner_hash: Field) -> bool {
        let public_key = self.storage.signing_public_key.view_note();

        let message_hash = compute_authwit_message_hash(
            consumer,
            self.context.chain_id(),
            self.context.version(),
            inner_hash,
        );

        let sig: [Field; 4] = get_auth_witness(message_hash);
        let valid_in_private = schnorr_verify(public_key.x, public_key.y, sig, message_hash);

        // The oracle is the caller's own PXE and this runs off-chain.
        let nullifier = compute_authwit_nullifier(self.address, inner_hash);
        let siloed_nullifier = compute_siloed_nullifier(consumer, nullifier);
        let (low_leaf_preimage, _witness) =
            get_low_nullifier_membership_witness(self.context.block_header(), siloed_nullifier);
        let is_spent = low_leaf_preimage.nullifier == siloed_nullifier;

        !is_spent & valid_in_private
    }
}
