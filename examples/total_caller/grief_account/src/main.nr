//! GriefAccount: an account-like contract with TotalAccount's
//! encrypt_for_owner interface, written the ordinary aztec-nr way, so that
//! its owner can make every caller's transaction fail.
//!
//! Nothing here is exotic. Like TotalAccount it keeps the key in public
//! state, so that callers can read it at all (a key note would be
//! unreadable to them under aztec-nr v6 discovery). The public
//! constructor stores the key without checking it (as the v6 Schnorr
//! account stores its signing key) in a PublicImmutable, the function
//! keeps the macro's initialisation check, reads the key with aztec-nr's
//! PublicImmutable::read, and multiplies by it with std's MSM. Each of
//! those is a failure its owner controls:
//! - never constructed: PublicImmutable::read's hint traps ("Trying to
//!   read from uninitialized PublicImmutable"), and the initialisation
//!   check's and the read's nullifier read requests would fail the
//!   kernel;
//! - an off-curve key, including (p - 1, p - 1): the MSM black box's
//!   witness generation stops ("is not on curve").
//! And one the owner controls that is not a failure but worse: the key
//! (0, 0), std's infinity encoding, passes std's MSM, which returns
//! infinity for the shared secret, so the call completes with ok = true
//! and an AE key of 0: a ciphertext anyone can open.
//!
//! Do not copy this contract. It exists to show the failure total_caller's
//! README describes.

use aztec::macros::aztec;

#[aztec]
pub contract GriefAccount {
    use aztec::{
        macros::{functions::{external, initializer}, storage::storage},
        protocol::traits::Packable,
        state_vars::PublicImmutable,
    };
    use std::embedded_curve_ops::{
        EmbeddedCurvePoint, EmbeddedCurveScalar, fixed_base_scalar_mul, multi_scalar_mul,
    };
    use std::hash::poseidon2_permutation;

    #[derive(Eq, Packable)]
    pub struct EncKey {
        pub x: Field,
        pub y: Field,
    }

    #[storage]
    struct Storage<Context> {
        enc_pk: PublicImmutable<EncKey, Context>,
    }

    /// Stores the key unchecked.
    #[external("public")]
    #[initializer]
    fn constructor(enc_pk_x: Field, enc_pk_y: Field) {
        self.storage.enc_pk.initialize(EncKey { x: enc_pk_x, y: enc_pk_y });
    }

    /// Same signature and return layout as TotalAccount's.
    #[external("private")]
    fn encrypt_for_owner(
        plaintext: [Field; 4],
        randomness: Field,
    ) -> (Field, Field, [Field; 5], bool) {
        let key = self.storage.enc_pk.read();
        let pk = EmbeddedCurvePoint { x: key.x, y: key.y };
        let r = EmbeddedCurveScalar::from_field(randomness);
        let eph = fixed_base_scalar_mul(r);
        let shared = multi_scalar_mul([pk], [r]);
        let mut s = poseidon2_permutation([shared.x, eph.x, 0, 0]);
        let mut ct = [0; 5];
        for i in 0..3 {
            s[i] += plaintext[i];
            ct[i] = s[i];
        }
        s = poseidon2_permutation(s);
        s[0] += plaintext[3];
        ct[3] = s[0];
        ct[4] = poseidon2_permutation(s)[0];
        (eph.x, eph.y, ct, true)
    }
}
