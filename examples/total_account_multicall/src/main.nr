//! MultiCall: a test stand-in for the multicall entrypoint that aztec.js
//! v6 wraps a self-paid account deployment in (DeployAccountMethod with
//! NO_FROM): one transaction calls the account's constructor, then the
//! account's entrypoint with the fee payload. The TXE runs one top-level
//! call per transaction and keeps only that call's arguments, so the two
//! calls are made from this contract, which hands the PXE both argument
//! preimages. Test code only.

use aztec::macros::aztec;

#[aztec]
pub contract MultiCall {
    use aztec::{
        macros::functions::external,
        protocol::{abis::function_selector::FunctionSelector, address::AztecAddress},
    };

    /// Two private calls to account in one transaction: first_selector
    /// with first_args (the constructor), then second_selector with
    /// second_args (the entrypoint: an AppPayload, the fee payment method
    /// and the cancellable flag).
    #[external("private")]
    fn call_twice(
        account: AztecAddress,
        first_selector: FunctionSelector,
        first_args: [Field; 4],
        second_selector: FunctionSelector,
        second_args: [Field; 33],
    ) {
        let _ = self.context.call_private_function(account, first_selector, first_args);
        let _ = self.context.call_private_function(account, second_selector, second_args);
    }
}
