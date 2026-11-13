use aztec::protocol::constants::MAX_TX_LIFETIME;
use aztec::protocol::traits::Packable;

/// DEV DECISION: the delay before an encryption-key change takes effect
/// (seconds, fixed for the account's life). Options: aztec-nr's one-hour
/// minimum up to any longer delay. This code: one day (MAX_TX_LIFETIME),
/// so a key read costs readers no earlier expiration than any private
/// call, at the price of a day's wait for the first key and each rotation.
pub global ENC_KEY_INITIAL_DELAY: u64 = MAX_TX_LIFETIME;

/// The owner's encryption public key (x, y), a Grumpkin point in std's
/// two-coordinate form, as stored in the account's DelayedPublicMutable.
/// Field members only, so packing is the identity and every stored value
/// unpacks (total_aztec::key_note's rules carry over to public state). A
/// slot never written reads as (0, 0), std's infinity encoding, which
/// the read path refuses like any other bad key.
#[derive(Eq, Packable)]
pub struct EncKey {
    pub x: Field,
    pub y: Field,
}
