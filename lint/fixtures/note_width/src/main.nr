// Fixture for total-lint's note-width rule: aztec-nr v6's PXE oracle
// aztec_prv_notifyCreatedNote, declared under its own name, called with a
// packed note one field wider than MAX_NOTE_PACKED_LEN (8) and with one
// exactly that wide. Only the wide calls are note-width sites; every call
// stays an ordinary oracle site. The marker on the third call justifies
// both of its sites.

pub struct AztecAddress {
    inner: Field,
}

#[oracle(aztec_prv_notifyCreatedNote)]
unconstrained fn notify_created_note_oracle<let N: u32>(
    _owner: AztecAddress,
    _storage_slot: Field,
    _randomness: Field,
    _note_type_id: Field,
    _packed_note: [Field; N],
    _note_hash: Field,
    _counter: u32,
) {}

unconstrained fn notify_wide(x: Field) {
    notify_created_note_oracle(AztecAddress { inner: x }, 1, 2, 3, [x; 9], 4, 5);
}

unconstrained fn notify_at_limit(x: Field) {
    notify_created_note_oracle(AztecAddress { inner: x }, 1, 2, 3, [x; 8], 4, 6);
}

unconstrained fn notify_justified(x: Field) {
    notify_created_note_oracle(AztecAddress { inner: x }, 1, 2, 3, [x; 10], 4, 7); // total-lint: allow fixture: no reader in this transaction
}

fn main(x: Field) {
    // Safety: fixture; the calls only notify the PXE and return nothing.
    unsafe {
        notify_wide(x);
        notify_at_limit(x);
        notify_justified(x);
    }
}
