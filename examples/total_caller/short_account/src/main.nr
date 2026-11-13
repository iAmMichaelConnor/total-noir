//! ShortAccount: a callee with encrypt_for_owner's selector (same name and
//! parameter types) but a two-Field return. It shows that the return
//! arity is part of the interface Caller trusts: Caller reads eight
//! Fields, and a callee returning another number fails Caller's call at
//! the returns-preimage oracle, before any constraint of Caller's runs.
//! A property of the callee's class, like every other way its code can
//! fail. Test-only; not an account.

use aztec::macros::aztec;

#[aztec]
pub contract ShortAccount {
    use aztec::macros::functions::external;

    #[external("private")]
    fn encrypt_for_owner(plaintext: [Field; 4], randomness: Field) -> (Field, bool) {
        (plaintext[0] + randomness, true)
    }
}
