//! NullificationExecutor: contract A of the proof-of-nullification
//! pattern. An owner B holds ValueNotes in A's `balances`; an executor
//! E (any, or the one B's proof names) consumes one of B's notes with
//! B's off-line proof (the prove_nullification circuit next to this
//! package), and A pins B's key commitment from B's own registration.
//! Not an application: it shows the two library entries in a real
//! contract and is what the TXE tests and the lint run on.

mod test;
mod owner_vk;

use aztec::macros::aztec;

#[aztec]
pub contract NullificationExecutor {
    use aztec::{
        macros::{functions::{external, only_self}, notes::note, storage::storage},
        protocol::{address::AztecAddress, traits::Packable},
        state_vars::{Map, Owned, PrivateSet, PublicImmutable, StateVariable},
    };
    use total_aztec::{
        consume_with_nullification_proof_or, NullificationProof, public_immutable_read_or,
        registered_npk_app_hash,
    };

    /// The verification-key hash of prove_nullification, poseidon2 over
    /// the 115 fields `bb write_vk -t noir-recursive --output_format json`
    /// lists (equal to that file's `hash`). make_fixture.py --vk (run.sh)
    /// recomputes it and fails if this pin or owner_vk.nr is stale;
    /// --vk --update rewrites both.
    ///
    /// DEV DECISION: which owner circuit A accepts. Options: a vk hash in
    /// code, in storage, or from arguments. This code: in code, because
    /// whoever writes the vk chooses the statement; changing the owner
    /// circuit then means a new contract class.
    pub global OWNER_CIRCUIT_VK_HASH: Field =
        0x03c274020abaae94c4c613bbebd80780d6480f29c7147c6d404a13e0a52885df;

    /// A one-field note; its hash is aztec-nr's #[note] derive, the
    /// formula the owner circuit reproduces.
    #[derive(Eq, Packable)]
    #[note]
    pub struct ValueNote {
        pub value: Field,
    }

    #[storage]
    struct Storage<Context> {
        balances: Owned<PrivateSet<ValueNote, Context>, Context>,
        /// Each owner's npk_app_hash, written once by the owner's own
        /// registration.
        ///
        /// DEV DECISION: where the pin lives. This code: a PublicImmutable
        /// per owner, readable in private without the owner's keys;
        /// registering is therefore public (it shows B uses A). A private
        /// pin would need note delivery to a non-owner, which v6 lacks.
        pins: Map<AztecAddress, PublicImmutable<Field, Context>, Context>,
    }

    /// B's registration, in B's own transaction: commit to B's
    /// kernel-validated app-siloed nullifier hiding key for this
    /// contract.
    #[external("private")]
    fn register() {
        // total-lint: allow the owner's own transaction: msg_sender is the owner's account
        let owner = self.msg_sender();
        // total-lint: allow aztec-nr's key validation request and public-keys check: register runs only in the owner's own transaction, for the owner's own account
        let pin = registered_npk_app_hash(self.context, owner);
        self.enqueue_self._store_pin(owner, pin);
    }

    #[external("public")]
    #[only_self]
    fn _store_pin(owner: AztecAddress, pin: Field) {
        self.storage.pins.at(owner).initialize(pin);
    }

    /// The pin registered for owner (0 when none), for tests and for an
    /// executor checking a registration before asking for a proof.
    #[external("utility")]
    unconstrained fn pin_of(owner: AztecAddress) -> Field {
        let pin = self.storage.pins.at(owner);
        if pin.is_initialized() {
            pin.read()
        } else {
            0
        }
    }

    /// E's call: consume one of owner's notes with the handoff E passes,
    /// returning (value, ok). ok = false when the handoff is withheld (all
    /// zeros), the owner never registered, the handoff's vk is not the
    /// pinned one, the binding does not admit this call (another executor
    /// than this call's msg_sender, or an expiry at or below the anchor
    /// block number), the leaf is not at the handoff's index and path in
    /// the anchor block's note hash tree, the note was already spent
    /// there, or the call is static (a static call may not push the
    /// nullifier). Callable as the first call and through another
    /// contract.
    #[external("private")]
    fn consume(owner: AztecAddress, handoff: NullificationProof<1>) -> (Field, bool) {
        // total-lint: allow aztec-nr's slot != 0 check on the map-derived slot (a Poseidon2 output)
        let (pin, registered) = public_immutable_read_or(self.context, self.storage.pins.at(owner));
        // total-lint: allow the recursive verification, predicated on ok: the handoff is this function's argument, so only its caller can pass a proof that does not verify, failing its own transaction
        let (fields, consumed): ([Field; 1], bool) = consume_with_nullification_proof_or(
            self.context,
            handoff,
            OWNER_CIRCUIT_VK_HASH,
            pin,
            self.storage.balances.get_storage_slot(),
            owner,
        );
        let ok = registered & consumed;
        (fields[0] * (ok as Field), ok)
    }
}
