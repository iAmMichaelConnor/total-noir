//! Which key must have signed: the two phases of the signing key.
//!
//! Before the account is initialised at the anchor block, the key the
//! deployer passed to the constructor, read with total_aztec's
//! initializer_args_or: the arguments the constructor recorded (with
//! record_initializer_args) for later calls of its own transaction, a
//! hint checked against the address, whose initialization hash commits
//! to the constructor's arguments. This is
//! what lets the account's entrypoint run in its own deployment
//! transaction, after the constructor: the key note the constructor
//! creates there is a pending note of another call, which no app circuit
//! can read (total_aztec's note.nr). Once the initialisation nullifier is
//! in the anchor block's nullifier tree, the key note, and only the key
//! note.
//!
//! The phase is the initialisation flag, determined relative to the
//! anchor block; the executor chooses the anchor block, so a transaction
//! anchored before the initialisation settled checks the constructor's
//! key (README, "Two-phase signing key").

use aztec::protocol::abis::function_selector::FunctionSelector;
use total_aztec::InitializerArgs;

/// The constructor's selector, which the address's initialization hash
/// commits to (with the hash of its four arguments).
pub global CONSTRUCTOR_SELECTOR: FunctionSelector =
    FunctionSelector::from_signature("constructor(Field,Field,Field,Field)");

/// (x, y, ok): the key the signature is checked against, and whether it
/// may sign. Not initialised at the anchor block: the constructor's
/// signing key (arguments 0 and 1), ok when the hinted arguments are the
/// ones the address commits to. Initialised: the key note, ok when it was
/// found. Selects only; no constraint can fail.
pub fn signing_key_or(
    initial: InitializerArgs<4>,
    note_x: Field,
    note_y: Field,
    found: bool,
) -> (Field, Field, bool) {
    let initialized = initial.initialized;
    let x = if initialized { note_x } else { initial.args[0] };
    let y = if initialized { note_y } else { initial.args[1] };
    let ok = if initialized { found } else { initial.bound };
    (x, y, ok)
}

mod tests {
    use super::signing_key_or;
    use total_aztec::InitializerArgs;

    fn initial(bound: bool, initialized: bool) -> InitializerArgs<4> {
        InitializerArgs { args: [1, 2, 3, 4], bound, initialized }
    }

    #[test]
    fn before_initialisation_the_constructor_key_decides() {
        // the note is ignored whether found or not
        assert_eq(signing_key_or(initial(true, false), 7, 8, false), (1, 2, true));
        assert_eq(signing_key_or(initial(true, false), 7, 8, true), (1, 2, true));
        assert_eq(signing_key_or(initial(false, false), 7, 8, true), (1, 2, false));
    }

    #[test]
    fn after_initialisation_only_the_note_decides() {
        // bound constructor arguments no longer count
        assert_eq(signing_key_or(initial(true, true), 7, 8, true), (7, 8, true));
        assert_eq(signing_key_or(initial(true, true), 7, 8, false), (7, 8, false));
        assert_eq(signing_key_or(initial(false, true), 7, 8, false), (7, 8, false));
    }
}
