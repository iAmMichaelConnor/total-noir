// A total circuit for total-lint: ordinary operations that lower to the
// compiler's own hints, a typed parameter, and one marked full-width
// decomposition. With --allow-entry-ranges the lint exits 0.

fn main(x: Field, i: Field, s: u32, flag: bool) -> pub (bool, u8, u32, [u8; 4], u8, bool) {
    let e = x == 5;
    let a = i as u8;
    let lt = a < 7;
    let m = s & 3;
    let h = s / 2;
    let b: [u8; 4] = (s as Field).to_le_bytes();
    let bytes: [u8; 32] = x.to_le_bytes(); // total-lint: allow a full-width decomposition of x is canonical, so the comparison with the modulus passes
    (e, a, m + h, b, bytes[0], lt & flag)
}
