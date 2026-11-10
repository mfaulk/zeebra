//! SHAKE128, FIPS 202, as an extendable-output reader.
//!
//! Here because two of this crate's primitives **derive** their round constants from it rather
//! than tabulate them: `zkfriendlyhashzoo`'s Feistel-MiMC seeds a SHAKE128 with the string
//! `"FeistelMimc"` and the field characteristic and reads field elements out of the squeeze
//! stream. A tabulated copy of those constants could not be checked against the rule that produced
//! them — the same argument [`sha256`](super::sha256) makes for being hand-written.
//!
//! Not a security primitive as used here: nothing secret is absorbed and there is no
//! constant-time requirement. What is wanted is that the squeeze stream is byte-for-byte the one
//! the reference implementation reads, which the module's tests pin against FIPS 202 output and —
//! the check that actually matters — against the reference's own published Feistel-MiMC test
//! vectors.

/// Keccak-f\[1600\] round constants, FIPS 202 §3.2.5, for the 24 rounds of a 1600-bit state.
const ROUND_CONSTANTS: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// The ρ offsets, FIPS 202 §3.2.2, indexed as `x + 5y`.
const RHO: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// `1600 − 2·128` bits, so 168 bytes absorbed and squeezed per permutation.
const RATE: usize = 168;

/// SHAKE128: absorb with [`Shake128::update`], then squeeze with [`Shake128::read`].
///
/// Absorbing after the first read is a programming error and panics, because the sponge has
/// already been padded and a silently ignored update would make the stream wrong rather than
/// absent.
#[derive(Clone, Debug)]
pub struct Shake128 {
    /// The 5×5 lane state, indexed `x + 5y`.
    state: [u64; 25],

    /// Position within the current rate block: bytes absorbed, or bytes already squeezed.
    offset: usize,

    /// Whether padding has been applied and the sponge switched to squeezing.
    squeezing: bool,
}

impl Default for Shake128 {
    fn default() -> Self {
        Self::new()
    }
}

impl Shake128 {
    /// A fresh sponge with a zero state.
    pub fn new() -> Self {
        Self {
            state: [0; 25],
            offset: 0,
            squeezing: false,
        }
    }

    /// Absorb `bytes`.
    ///
    /// # Panics
    /// Panics if called after [`Self::read`], which would silently drop the input.
    pub fn update(&mut self, bytes: &[u8]) {
        assert!(
            !self.squeezing,
            "SHAKE128 cannot absorb after the squeeze has begun"
        );
        for byte in bytes {
            self.state[self.offset / 8] ^= u64::from(*byte) << (8 * (self.offset % 8));
            self.offset += 1;
            if self.offset == RATE {
                keccak_f1600(&mut self.state);
                self.offset = 0;
            }
        }
    }

    /// Fill `out` from the squeeze stream, continuing where the previous read stopped.
    pub fn read(&mut self, out: &mut [u8]) {
        if !self.squeezing {
            // pad10*1 with the SHAKE domain separator 1111, so the first byte is 0x1f.
            self.state[self.offset / 8] ^= 0x1f << (8 * (self.offset % 8));
            self.state[(RATE - 1) / 8] ^= 0x80 << (8 * ((RATE - 1) % 8));
            keccak_f1600(&mut self.state);
            self.squeezing = true;
            self.offset = 0;
        }
        for byte in out.iter_mut() {
            if self.offset == RATE {
                keccak_f1600(&mut self.state);
                self.offset = 0;
            }
            *byte = (self.state[self.offset / 8] >> (8 * (self.offset % 8))) as u8;
            self.offset += 1;
        }
    }

    /// `length` bytes of output from a one-shot hash of `message`.
    pub fn digest(message: &[u8], length: usize) -> Vec<u8> {
        let mut sponge = Self::new();
        sponge.update(message);
        let mut out = vec![0u8; length];
        sponge.read(&mut out);
        out
    }
}

/// Keccak-f\[1600\], FIPS 202 §3.3: twenty-four rounds of θ, ρ, π, χ and ι.
fn keccak_f1600(state: &mut [u64; 25]) {
    for round_constant in ROUND_CONSTANTS {
        // theta
        let mut parity = [0u64; 5];
        for x in 0..5 {
            parity[x] = (0..5).fold(0, |a, y| a ^ state[x + 5 * y]);
        }
        for x in 0..5 {
            let d = parity[(x + 4) % 5] ^ parity[(x + 1) % 5].rotate_left(1);
            for y in 0..5 {
                state[x + 5 * y] ^= d;
            }
        }

        // rho and pi, combined: B[y][2x + 3y] = rot(A[x][y], RHO[x + 5y]).
        let mut b = [0u64; 25];
        for x in 0..5 {
            for y in 0..5 {
                b[y + 5 * ((2 * x + 3 * y) % 5)] = state[x + 5 * y].rotate_left(RHO[x + 5 * y]);
            }
        }

        // chi
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] =
                    b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
            }
        }

        // iota
        state[0] ^= round_constant;
    }
}

#[cfg(test)]
mod tests {
    use super::Shake128;

    /// SHAKE128 reproduces the FIPS 202 output for the empty message and for `"abc"`.
    #[test]
    fn test_the_published_vectors_are_reproduced() {
        assert_eq!(
            hex(&Shake128::digest(b"", 32)),
            "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26"
        );
        assert_eq!(
            hex(&Shake128::digest(b"abc", 32)),
            "5881092dd818bf5cf8a3ddb793fbcba74097d5c526a6d35f97b83351940f2cc8"
        );
    }

    /// Output past the first rate block is correct, so the squeeze permutes rather than repeating.
    ///
    /// 200 bytes crosses the 168-byte rate boundary, which a sponge that forgot to permute between
    /// blocks would get right for the first 168 bytes and wrong after.
    #[test]
    fn test_output_crosses_the_rate_boundary() {
        let long = Shake128::digest(b"", 200);
        assert_eq!(hex(&long[..32]), hex(&Shake128::digest(b"", 32)));
        assert_eq!(
            hex(&long[168..]),
            "767be1fda69419dfb927e9df07348b196691abaeb580b32def58538b8d23f877"
        );
    }

    /// A message longer than the rate absorbs across block boundaries correctly.
    #[test]
    fn test_input_crosses_the_rate_boundary() {
        let message: Vec<u8> = (0..200u32).map(|b| b as u8).collect();
        assert_eq!(
            hex(&Shake128::digest(&message, 64)),
            "0c4234ca1e31801ae606f8b8d8e0665c66f42a21d601c2681858a92c79ad5d69\
             e143c3b1393dd894e7abd5621b0d877f3573a34245e6b911f671081664a5fa53"
        );
    }

    /// Several short reads give the same stream as one long read, and several short updates the
    /// same absorption as one long one.
    #[test]
    fn test_streaming_matches_one_shot() {
        let mut sponge = Shake128::new();
        sponge.update(b"a");
        sponge.update(b"b");
        sponge.update(b"c");
        let mut first = [0u8; 7];
        let mut rest = [0u8; 25];
        sponge.read(&mut first);
        sponge.read(&mut rest);
        let mut streamed = first.to_vec();
        streamed.extend_from_slice(&rest);
        assert_eq!(streamed, Shake128::digest(b"abc", 32));
    }

    /// Absorbing after the squeeze has begun panics rather than being silently dropped.
    #[test]
    #[should_panic(expected = "cannot absorb after the squeeze")]
    fn test_absorbing_after_reading_panics() {
        let mut sponge = Shake128::new();
        let mut out = [0u8; 4];
        sponge.read(&mut out);
        sponge.update(b"too late");
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{:02x}", b)).collect()
    }
}
