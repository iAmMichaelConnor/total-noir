use aztec::{macros::notes::note, protocol::traits::Packable};

/// The Schnorr signing public key, stored once at construction in a
/// SinglePrivateImmutable. Same layout as the v6 schnorr account
/// contract's note. The constructor refuses a key that is not a finite
/// curve point, and the verify path flags one anyway.
#[derive(Eq, Packable)]
#[note]
pub struct PublicKeyNote {
    pub x: Field,
    pub y: Field,
}
