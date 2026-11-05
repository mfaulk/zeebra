//! SHA-256, FIPS 180-4, for pinning the identity of an instance.
//!
//! Hand-written rather than depended upon, for the same reason as [`Json`](crate::grobner::research::Json):
//! the whole of it is ninety lines and a dependency would be the larger thing. It is here because
//! M23's registry has to answer "is this the same mathematical problem?" with a checksum rather
//! than a name — `Provenance::sha256` was a string a shell script computed and no Rust code could
//! check, and a checksum nothing verifies is a comment.
//!
//! Not a security primitive as used here: there is no constant-time requirement, nothing secret is
//! hashed, and the property wanted is only that two different parameter sets do not collide.

use std::fmt::Write as _;

/// FIPS 180-4 §4.2.2: the first thirty-two bits of the fractional parts of the cube roots of the
/// first sixty-four primes.
const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// A streaming SHA-256.
///
/// Streaming rather than one-shot because the things M23 hashes include a polynomial system's
/// canonical form, which there is no reason to materialize as one string first.
#[derive(Clone, Debug)]
pub struct Sha256 {
    /// The eight working variables, §5.3.3.
    state: [u32; 8],

    /// Bytes not yet compressed, fewer than 64.
    buffer: Vec<u8>,

    /// Total message length in bytes, which the padding encodes in bits.
    length: u64,
}

impl Default for Sha256 {
    fn default() -> Self {
        Self::new()
    }
}

impl Sha256 {
    /// A fresh hasher, initialized as §5.3.3.
    pub fn new() -> Self {
        Self {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ],
            buffer: Vec::with_capacity(64),
            length: 0,
        }
    }

    /// Absorb more message.
    pub fn update(&mut self, bytes: &[u8]) {
        self.length = self.length.wrapping_add(bytes.len() as u64);
        let mut rest = bytes;
        if !self.buffer.is_empty() {
            let wanted = 64 - self.buffer.len();
            let take = wanted.min(rest.len());
            self.buffer.extend_from_slice(&rest[..take]);
            rest = &rest[take..];
            if self.buffer.len() == 64 {
                let block: [u8; 64] = self.buffer[..].try_into().expect("exactly 64");
                self.compress(&block);
                self.buffer.clear();
            }
        }
        let mut chunks = rest.chunks_exact(64);
        for block in &mut chunks {
            self.compress(block.try_into().expect("exactly 64"));
        }
        self.buffer.extend_from_slice(chunks.remainder());
    }

    /// Pad, compress the last blocks, and return the digest.
    pub fn finalize(mut self) -> [u8; 32] {
        // §5.1.1: a 1 bit, then zeros, then the length in bits as 64 big-endian bits, to a
        // multiple of 64 bytes. The awkward case is a buffer of 56..=63 bytes, where the length
        // does not fit and a second block is needed — which is the boundary a padding bug hides at.
        let bits = self.length.wrapping_mul(8);
        let mut tail = vec![0x80u8];
        let remainder = (self.buffer.len() + 1) % 64;
        let zeros = (56 + 64 - remainder) % 64;
        tail.extend(std::iter::repeat_n(0u8, zeros));
        tail.extend_from_slice(&bits.to_be_bytes());
        // `update` would add these to the length, so compress them directly.
        let mut block = std::mem::take(&mut self.buffer);
        block.extend_from_slice(&tail);
        debug_assert!(block.len().is_multiple_of(64));
        for chunk in block.chunks_exact(64) {
            self.compress(chunk.try_into().expect("exactly 64"));
        }

        let mut digest = [0u8; 32];
        for (word, out) in self.state.iter().zip(digest.chunks_exact_mut(4)) {
            out.copy_from_slice(&word.to_be_bytes());
        }
        digest
    }

    /// The digest as lowercase hex.
    pub fn hex(self) -> String {
        let digest = self.finalize();
        let mut out = String::with_capacity(64);
        for byte in digest {
            let _ = write!(out, "{:02x}", byte);
        }
        out
    }

    /// §6.2.2 on one 512-bit block.
    fn compress(&mut self, block: &[u8; 64]) {
        let mut w = [0u32; 64];
        for (word, bytes) in w.iter_mut().zip(block.chunks_exact(4)) {
            *word = u32::from_be_bytes(bytes.try_into().expect("exactly 4"));
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = self.state;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choose = (e & f) ^ ((!e) & g);
            let t1 = h
                .wrapping_add(s1)
                .wrapping_add(choose)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(majority);

            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (word, delta) in self.state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *word = word.wrapping_add(delta);
        }
    }
}

/// SHA-256 of `bytes`, as lowercase hex.
pub fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher.hex()
}

#[cfg(test)]
mod tests {
    use super::{sha256_hex, Sha256};

    /// The three FIPS 180-4 example messages hash to their published digests.
    #[test]
    fn test_published_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            sha256_hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }

    /// Message lengths around the padding boundary all hash correctly.
    ///
    /// 55 bytes is the longest message whose padding fits one block, 56 is the shortest that needs
    /// two, and 64 is an exact block — the three lengths a hand-written padding rule gets wrong.
    /// Digests are from an independent implementation (`sha256sum`).
    #[test]
    fn test_padding_boundaries() {
        for (length, expected) in [
            (
                55,
                "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318",
            ),
            (
                56,
                "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a",
            ),
            (
                63,
                "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34",
            ),
            (
                64,
                "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb",
            ),
            (
                65,
                "635361c48bb9eab14198e76ea8ab7f1a41685d6ad62aa9146d301d4f17eb0ae0",
            ),
        ] {
            let message = vec![b'a'; length];
            assert_eq!(sha256_hex(&message), expected, "{} bytes", length);
        }
    }

    /// Updating in arbitrary chunks gives the same digest as one call.
    ///
    /// The property a streaming hasher exists for, and the one that fails if the internal buffer is
    /// mishandled across a block boundary.
    #[test]
    fn test_streaming_matches_one_shot() {
        let message: Vec<u8> = (0..300u32).map(|i| (i % 251) as u8).collect();
        let expected = sha256_hex(&message);
        for chunk in [1usize, 7, 31, 63, 64, 65, 128, 299, 300] {
            let mut hasher = Sha256::new();
            for piece in message.chunks(chunk) {
                hasher.update(piece);
            }
            assert_eq!(hasher.hex(), expected, "chunked by {}", chunk);
        }
    }

    /// One million 'a' hashes to the published digest, which exercises many blocks.
    #[test]
    fn test_long_message() {
        let mut hasher = Sha256::new();
        for _ in 0..1_000 {
            hasher.update(&[b'a'; 1_000]);
        }
        assert_eq!(
            hasher.hex(),
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
        );
    }

    /// A one-bit change in the message changes the digest.
    #[test]
    fn test_digests_separate_near_messages() {
        assert_ne!(
            sha256_hex(b"t=16 R_F=6 R_P=8"),
            sha256_hex(b"t=16 R_F=6 R_P=9")
        );
    }
}
