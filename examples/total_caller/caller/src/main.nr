//! Caller: contract A, whose function calls a function of an account B
//! that A's user does not control.
//!
//! seal_to(account, plaintext, randomness) asks the account to encrypt
//! four fields to its owner's key, through encrypt_for_owner, and returns
//! the account's output with a flag. A calls B by selector with
//! total_aztec::static_call_flagged_or, so A's own code is total over any
//! eight-Field return; the only way B can fail A's transaction is to fail
//! its own call or return another number of Fields (ShortAccount and its
//! test). Whether B can fail A is decided by B's code: TotalAccount cannot
//! be made to fail by its owner, GriefAccount can (README.md, the tests).

mod test;

use aztec::macros::aztec;

#[aztec]
pub contract Caller {
    use aztec::{
        macros::functions::external,
        protocol::{abis::function_selector::FunctionSelector, address::AztecAddress},
    };
    use total_aztec::static_call_flagged_or;

    /// encrypt_for_owner's selector, from the signature the #[aztec]
    /// macro computes (name and parameter types).
    global ENCRYPT_FOR_OWNER: FunctionSelector =
        comptime { FunctionSelector::from_signature("encrypt_for_owner([Field;4],Field)") };

    /// Ask account to encrypt plaintext to its owner. Returns the
    /// account's (eph_pk_x, eph_pk_y, ciphertext[5]) and ok; on ok = false
    /// the seven Fields are 0. randomness must be fresh for every message
    /// (total_account's ecies.nr). The static call and the flag decoding
    /// are static_call_flagged_or's: ok only when the account's last
    /// return Field is exactly 1.
    #[external("private")]
    fn seal_to(
        account: AztecAddress,
        plaintext: [Field; 4],
        randomness: Field,
    ) -> ([Field; 7], bool) {
        let args = [plaintext[0], plaintext[1], plaintext[2], plaintext[3], randomness];
        // total-lint: allow the call request and the returns preimage check: the callee is the account this function's caller names; a callee that fails or returns another arity than eight Fields fails that caller's own transaction
        let (values, ok) = static_call_flagged_or(self.context, account, ENCRYPT_FOR_OWNER, args);
        (values, ok)
    }
}
