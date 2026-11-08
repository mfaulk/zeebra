//! Hashing for monomial keys.
//!
//! Monomial-keyed maps are the representation of a sparse multivariate polynomial, so every
//! arithmetic operation hashes once per term. The keys are `[u32; N]` of small exponents and they
//! come from the caller's own polynomial system, never from the network: a caller who can choose
//! the monomials can already choose the ideal, so `SipHash-1-3`'s resistance to chosen keys buys
//! nothing here and costs more per key than the work it guards.

use std::{
    collections::{HashMap, HashSet},
    hash::{BuildHasher, Hasher},
};

use crate::poly::Monomial;

/// A map keyed by monomials, hashed the cheap way. See [`MonomialHasher`].
pub type MonomialMap<const N: usize, V> = HashMap<Monomial<N>, V, BuildMonomialHasher>;

/// A set of monomials, hashed the cheap way. See [`MonomialHasher`].
pub type MonomialSet<const N: usize> = HashSet<Monomial<N>, BuildMonomialHasher>;

/// A multiplicative hash over machine words, for keys that are a handful of integers.
///
/// The construction is the one `rustc` uses for its own interned-key maps: rotate, xor the next
/// word in, multiply by an odd constant.
#[derive(Clone, Copy, Debug, Default)]
pub struct MonomialHasher {
    hash: u64,
}

/// An odd 64-bit constant with a well-mixed bit pattern, from `rustc`'s `FxHasher`.
const HASH_MULTIPLIER: u64 = 0x517c_c1b7_2722_0a95;

impl MonomialHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(5) ^ word).wrapping_mul(HASH_MULTIPLIER);
    }
}

impl Hasher for MonomialHasher {
    /// Eight bytes at a time.
    ///
    /// This is the path a monomial actually takes: `[u32; N]` hashes through the standard library's
    /// `hash_slice` for integers, which hands the whole exponent array over as one byte slice. A
    /// byte-at-a-time loop here turns a 28-byte key into 28 rounds and was measured to be *slower*
    /// than the SipHash it replaced.
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        // `as_chunks` rather than `chunks_exact`: the chunk size is a constant, so the array
        // length is known to the compiler and `from_le_bytes` needs no fallible conversion.
        let (words, tail) = bytes.as_chunks::<8>();
        for word in words {
            self.add(u64::from_le_bytes(*word));
        }
        if !tail.is_empty() {
            let mut padded = [0u8; 8];
            padded[..tail.len()].copy_from_slice(tail);
            self.add(u64::from_le_bytes(padded));
        }
    }

    #[inline]
    fn write_u8(&mut self, value: u8) {
        self.add(value as u64);
    }

    #[inline]
    fn write_u16(&mut self, value: u16) {
        self.add(value as u64);
    }

    #[inline]
    fn write_u32(&mut self, value: u32) {
        self.add(value as u64);
    }

    #[inline]
    fn write_u64(&mut self, value: u64) {
        self.add(value);
    }

    #[inline]
    fn write_usize(&mut self, value: usize) {
        self.add(value as u64);
    }

    /// The accumulator, with its high entropy folded down.
    ///
    /// The fold is not optional. A multiplicative accumulator leaves the *low* bits of the product
    /// depending only on the low bits of the inputs, and `hashbrown` takes the bucket index from
    /// exactly those bits — so returning the accumulator raw makes small exponent vectors collide
    /// in droves. Measured, it doubled the cost of the stage it was meant to cheapen. The finalizer
    /// is `splitmix64`'s: two shifts and a multiply.
    #[inline]
    fn finish(&self) -> u64 {
        let mut hash = self.hash;
        hash ^= hash >> 32;
        hash = hash.wrapping_mul(0xd6e8_feb8_6659_fd93);
        hash ^= hash >> 32;
        hash
    }
}

/// Builds a [`MonomialHasher`].
///
/// Unlike `RandomState` this carries no per-process seed, so the iteration order of a
/// [`MonomialMap`] is a function of its keys alone. Callers that must not depend on iteration
/// order still must not: see `SparseMultiPoly::leading_term`, which sorts.
#[derive(Clone, Copy, Debug, Default)]
pub struct BuildMonomialHasher;

impl BuildHasher for BuildMonomialHasher {
    type Hasher = MonomialHasher;

    #[inline]
    fn build_hasher(&self) -> MonomialHasher {
        MonomialHasher::default()
    }
}

#[cfg(test)]
mod tests {
    use super::{BuildMonomialHasher, MonomialMap, MonomialSet};
    use crate::{
        fields::Zp2147483647 as F,
        grobner::{benchmark_systems::katsura, f4},
        poly::{Monomial, MonomialOrder, MultivariatePolynomial},
    };
    use std::hash::BuildHasher;

    fn hash_of<const N: usize>(monomial: &Monomial<N>) -> u64 {
        BuildMonomialHasher.hash_one(monomial)
    }

    /// The occupied-bucket count and the longest bucket load, for a table sized as `hashbrown`
    /// would size one holding these keys, with the number of buckets a uniform hash would be
    /// expected to occupy.
    ///
    /// The expectation is analytic rather than measured against `RandomState`. SipHash is seeded
    /// per process, so its own bucket count moves from run to run and an assertion against it is a
    /// random assertion: on a 35-monomial support it read 22 buckets against 26 one run and passed
    /// the next.
    fn bucket_profile(hashes: &[u64]) -> (usize, usize, f64) {
        let capacity = (hashes.len() * 8 / 7 + 1).next_power_of_two();
        let mut loads = vec![0usize; capacity];
        for hash in hashes {
            loads[(*hash as usize) & (capacity - 1)] += 1;
        }
        let expected =
            capacity as f64 * (1.0 - (1.0 - 1.0 / capacity as f64).powi(hashes.len() as i32));
        (
            loads.iter().filter(|load| **load > 0).count(),
            loads.iter().copied().max().unwrap_or(0),
            expected,
        )
    }

    /// The deepest bucket tolerated. A uniform hash's worst bucket at these table loads is around
    /// five and has been observed at seven; what this catches is the hash without its finalizer,
    /// whose low bits barely move and which clusters by orders of magnitude, not by a slot.
    const MAX_BUCKET_LOAD: usize = 10;

    /// No full-width collisions, bucket occupancy within a tenth of a uniform hash's expectation,
    /// and no bucket deeper than [`MAX_BUCKET_LOAD`].
    fn assert_spreads_like_a_uniform_hash<const N: usize>(support: &[Monomial<N>], what: &str) {
        let hashes: Vec<u64> = support.iter().map(hash_of).collect();
        assert_eq!(
            hashes
                .iter()
                .copied()
                .collect::<std::collections::HashSet<u64>>()
                .len(),
            support.len(),
            "{what}: full-width hash collision over {} monomials",
            support.len()
        );

        let (occupied, longest, expected) = bucket_profile(&hashes);
        assert!(
            occupied as f64 >= 0.9 * expected,
            "{what}: {occupied} buckets occupied of the {expected:.0} a uniform hash would fill"
        );
        assert!(
            longest <= MAX_BUCKET_LOAD,
            "{what}: longest bucket {longest}, above {MAX_BUCKET_LOAD}"
        );
    }

    /// Real monomial keys at the scale the maps see them: the supports of katsura-4 and katsura-5
    /// Gröbner bases under all three orders, together with the supports of the pairwise products of
    /// each basis — which is what a multiply accumulator is keyed by, and where the keys stop being
    /// a few dozen.
    fn real_support() -> Vec<Monomial<5>> {
        let orders = [
            MonomialOrder::Lexicographic,
            MonomialOrder::GradedLexicographic,
            MonomialOrder::GradedReverseLexicographic,
        ];
        let mut support: Vec<Monomial<5>> = Vec::new();
        for order in orders {
            // katsura-4 embedded in five variables, which is itself a shape the crate meets: a
            // term rarely uses every variable, so trailing zero exponents are the common case.
            let four = f4::<4, F>(&katsura::<4, F>(), order).expect("within limits");
            let embedded: Vec<MultivariatePolynomial<5, F>> = four
                .iter()
                .map(|polynomial| {
                    let terms: Vec<(Monomial<5>, F)> = polynomial
                        .terms()
                        .iter()
                        .map(|(monomial, coefficient)| {
                            let mut exponents = [0u32; 5];
                            exponents[..4].copy_from_slice(monomial.exponents());
                            (Monomial::<5>::new(&exponents), *coefficient)
                        })
                        .collect();
                    MultivariatePolynomial::new(&terms)
                })
                .collect();
            let five = f4::<5, F>(&katsura::<5, F>(), order).expect("within limits");
            for basis in [embedded, five] {
                for (i, left) in basis.iter().enumerate() {
                    support.extend(left.terms().keys().copied());
                    for right in &basis[i..] {
                        support.extend((left * right).terms().keys().copied());
                    }
                }
            }
        }
        support.sort();
        support.dedup();
        support
    }

    /// Equal monomials hash equally, which is the only thing `Hash` actually requires.
    #[test]
    fn test_equal_monomials_hash_equally() {
        for a in 0..8u32 {
            for b in 0..8u32 {
                let monomial = Monomial::<4>::new(&[a, b, (a + b) % 5, 0]);
                let rebuilt = Monomial::<4>::new(monomial.exponents());
                assert_eq!(hash_of(&monomial), hash_of(&rebuilt));
            }
        }
    }

    /// The hash is a function of the key alone: two independently built builders agree, which is
    /// what `RandomState` does not promise and what makes map iteration order reproducible.
    #[test]
    fn test_hash_is_seed_independent() {
        let monomial = Monomial::<6>::new(&[3, 0, 1, 4, 1, 5]);
        let one = BuildMonomialHasher;
        let another = BuildMonomialHasher;
        assert_eq!(one.hash_one(monomial), another.hash_one(monomial));
    }

    /// Exponent order matters: x^2*y and x*y^2 are different keys and hash differently.
    #[test]
    fn test_permuted_exponents_hash_differently() {
        assert_ne!(
            hash_of(&Monomial::<3>::new(&[2, 1, 0])),
            hash_of(&Monomial::<3>::new(&[1, 2, 0]))
        );
        assert_ne!(
            hash_of(&Monomial::<3>::new(&[0, 0, 1])),
            hash_of(&Monomial::<3>::new(&[1, 0, 0]))
        );
    }

    /// A `MonomialMap` round-trips: insert, lookup by an equal-but-rebuilt key, overwrite, remove.
    #[test]
    fn test_monomial_map_round_trips() {
        let mut map: MonomialMap<5, u64> = MonomialMap::default();
        let keys: Vec<Monomial<5>> = (0..64)
            .map(|i| Monomial::new(&[i % 7, i / 7, (i * 3) % 5, 0, i % 2]))
            .collect();
        for (index, key) in keys.iter().enumerate() {
            map.insert(*key, index as u64);
        }
        for (index, key) in keys.iter().enumerate() {
            let rebuilt = Monomial::<5>::new(key.exponents());
            assert_eq!(map.get(&rebuilt), Some(&(index as u64)));
        }
        assert_eq!(map.len(), keys.len());
        map.insert(keys[3], 999);
        assert_eq!(map.len(), keys.len());
        assert_eq!(map.get(&keys[3]), Some(&999));
        assert_eq!(map.remove(&keys[3]), Some(999));
        assert_eq!(map.get(&keys[3]), None);
        assert_eq!(map.len(), keys.len() - 1);
    }

    /// A `MonomialSet` deduplicates equal monomials and keeps distinct ones apart.
    #[test]
    fn test_monomial_set_deduplicates() {
        let mut set: MonomialSet<4> = MonomialSet::default();
        for i in 0..32u32 {
            set.insert(Monomial::new(&[i % 4, i / 4, 0, 1]));
            set.insert(Monomial::new(&[i % 4, i / 4, 0, 1]));
        }
        assert_eq!(set.len(), 32);
        assert!(set.contains(&Monomial::new(&[3, 7, 0, 1])));
        assert!(!set.contains(&Monomial::new(&[3, 7, 1, 1])));
    }

    /// On the support of real Gröbner bases the hash collides on nothing, spreads over buckets as a
    /// uniform hash would, and leaves no deep bucket — and the set holding them keeps every key.
    #[test]
    fn test_no_collisions_on_a_real_support() {
        let support = real_support();
        assert!(
            support.len() > 100,
            "expected a nontrivial support, got {}",
            support.len()
        );

        let distinct: MonomialSet<5> = support.iter().copied().collect();
        assert_eq!(distinct.len(), support.len(), "the set lost a key");

        assert_spreads_like_a_uniform_hash(&support, "katsura-4 and katsura-5 bases");
    }

    /// The same, over the exponent shapes the crate uses: the dense simplex of total degree <= d,
    /// for arities from 2 to 12, which is where a weak-avalanche hash loses.
    #[test]
    fn test_bucket_spread_on_dense_simplices() {
        fn check<const N: usize>(degree: u32) {
            let mut exponents = [0u32; N];
            let mut support: Vec<Monomial<N>> = Vec::new();
            fill_simplex::<N>(0, degree, &mut exponents, &mut support);
            assert_spreads_like_a_uniform_hash(
                &support,
                &format!("degree-{degree} simplex in {N}"),
            );
        }

        fn fill_simplex<const N: usize>(
            index: usize,
            remaining: u32,
            exponents: &mut [u32; N],
            support: &mut Vec<Monomial<N>>,
        ) {
            if index == N {
                support.push(Monomial::new(exponents));
                return;
            }
            for e in 0..=remaining {
                exponents[index] = e;
                fill_simplex::<N>(index + 1, remaining - e, exponents, support);
            }
            exponents[index] = 0;
        }

        check::<2>(40);
        check::<3>(14);
        check::<4>(9);
        check::<6>(6);
        check::<8>(4);
        check::<12>(3);
    }
}
