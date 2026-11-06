//! A Finite Field (I)FFT domain.
//!
//! The Fast Fourier Transform is a "divide-and-conquer" algorithm that decomposes a Fourier transform
//! of size n = n_1 * n_2 into smaller Fourier transforms of size n_1 and n_2. These can also be
//! decomposed recursively if n_1 and n_2 are composite, and the FFT is fastest when the size
//! n is the product of small prime factors. The simplest case, assumed here, is when the size
//! is a power of 2.

use crate::{fft::evens_and_odds, fields::batch_inverse, powers_of, FiniteField};
use std::{
    fmt::{Display, Formatter},
    ops::Index,
};

/// Why an element does not generate an FFT domain of the requested size.
///
/// Facts about the field and the requested size rather than programmer errors, so
/// [`FFTDomain::try_from_generator`] returns them instead of aborting.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DomainError {
    /// Only power-of-two sizes are supported; see the module comment.
    SizeNotPowerOfTwo { size: usize },

    /// `g^size != 1`, so the powers of `g` do not close up after `size` of them.
    NotAnNthRoot { size: usize },

    /// `g^size = 1` but the order of `g` is a proper divisor of `size`, so its powers repeat.
    NotPrimitive { size: usize },
}

impl Display for DomainError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SizeNotPowerOfTwo { size } => {
                write!(f, "an FFT domain of size {size} is not a power of two")
            }
            Self::NotAnNthRoot { size } => {
                write!(f, "the generator is not a {size}-th root of unity")
            }
            Self::NotPrimitive { size } => write!(
                f,
                "the generator's order is a proper divisor of {size}, so its powers repeat"
            ),
        }
    }
}

impl std::error::Error for DomainError {}

/// An (I)FFT domain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FFTDomain<F: FiniteField> {
    /// Powers of the generator: 1, g, g^2, ...
    powers: Vec<F>,
}

impl<F: FiniteField> FFTDomain<F> {
    /// An FFT domain.
    ///
    /// # Arguments
    /// * `powers` - Powers of the generator `g` : 1, g, g^2, ...
    pub fn new(powers: Vec<F>) -> Self {
        assert!(powers.len().is_power_of_two());
        // assert_eq!(powers[0], F::one(), "First element must be 1");
        // assert!(powers.len() > 1, "Domain must have at least 2 elements");
        Self { powers }
    }

    /// An FFT domain of `size` points, the powers of a primitive `size`-th root of unity.
    ///
    /// Whether a given element has the requested order is a fact about the field, so the three
    /// ways this can fail are [`DomainError`] values rather than panics.
    ///
    /// The order has to be *exactly* `size`: an element merely satisfying `g^n = 1` whose order
    /// is a proper divisor of n produces a point sequence that repeats, and a transform over
    /// repeated points is not invertible.
    ///
    /// # Arguments
    /// * `generator` - A primitive `size`-th root of unity.
    /// * `size` - The number of elements `n` in the domain.
    pub fn try_from_generator(generator: F, size: usize) -> Result<Self, DomainError> {
        if !size.is_power_of_two() {
            return Err(DomainError::SizeNotPowerOfTwo { size });
        }
        if generator.pow(size as u128) != F::one() {
            return Err(DomainError::NotAnNthRoot { size });
        }
        // For a power-of-two n the order is exactly n unless `g^(n/2) = 1`, so this needs no
        // factorization. The size-one domain is the powers of 1, where n / 2 would be zero.
        if size > 1 && generator.pow((size / 2) as u128) == F::one() {
            return Err(DomainError::NotPrimitive { size });
        }

        Ok(Self {
            powers: powers_of(&generator, size),
        })
    }

    /// An FFT domain of `size` points, panicking if `generator` does not generate one.
    ///
    /// A convenience over [`Self::try_from_generator`].
    ///
    /// # Panics
    /// Panics with the [`DomainError`] the fallible form returns.
    pub fn from_generator(generator: F, size: usize) -> Self {
        Self::try_from_generator(generator, size).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Generator `g` of the domain.
    pub fn generator(&self) -> &F {
        &self.powers[1]
    }

    /// Number of elements in the domain.
    pub fn size(&self) -> usize {
        self.powers.len()
    }

    /// Powers of the generator: 1, g, g^2, ...
    pub fn powers(&self) -> &[F] {
        &self.powers
    }

    /// Split the domain into even and odd powers of the generator.
    pub fn split(&self) -> (FFTDomain<F>, FFTDomain<F>) {
        let (evens, odds) = evens_and_odds(self.powers());
        (FFTDomain::new(evens), FFTDomain::new(odds))
    }

    /// Inverse powers 1, g^{-1}, g^{-2}, ...
    ///
    /// One inversion for the whole domain rather than one per element, by Montgomery's trick —
    /// see [`batch_inverse`]. Every power of a root of unity is a unit, so no element is skipped.
    ///
    /// Not `from_generator(self.generator().inverse(), self.size())`, which is what this used to
    /// hold as commented-out code. A domain is not required to be a power sequence starting at
    /// one: [`Self::split`] produces the odd powers `g, g^3, g^5, ...`, whose `generator()` is
    /// `g^3` and whose inverses are *not* the powers of `g^-3`. That form would also panic on such
    /// a domain, since `(g^3)^(n/2)` is `-1` rather than one.
    pub fn inverse(&self) -> FFTDomain<F> {
        FFTDomain::new(batch_inverse(self.powers()))
    }

    /// Returns an iterator over the elements of this domain.
    pub fn iter(&self) -> impl Iterator<Item = &F> {
        self.powers.iter()
    }
}

impl<F: FiniteField> Index<usize> for FFTDomain<F> {
    type Output = F;

    fn index(&self, index: usize) -> &Self::Output {
        &self.powers[index]
    }
}

impl<F: FiniteField> Display for FFTDomain<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "FFTDomain(generator: {}, size: {})",
            self.powers[1],
            self.powers.len()
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::PrimeFieldElement64,
        identities::{One, Zero},
        powers_of, DomainError, FFTDomain, FiniteField, KnownOrder,
    };
    use rand::{prelude::StdRng, SeedableRng};

    #[test]
    // Should create an FFT domain as the powers of the given nth root of unity.
    fn test_from_generator() {
        type F = PrimeFieldElement64<65537>; // Proth prime, 2^16 + 1
        let mut rng = StdRng::seed_from_u64(3889);
        let n: usize = 32;
        let generator = F::root_of_unity(n as u64, &mut rng);
        let domain: FFTDomain<F> = FFTDomain::from_generator(generator, n);
        assert_eq!(*domain.generator(), generator);
        assert_eq!(domain.size(), n);
        for (i, w_i) in domain.powers.iter().enumerate() {
            assert_eq!(*w_i, generator.pow(i as u128));
        }
    }

    #[test]
    #[should_panic]
    // Should fail if the generator is not an nth root of unity.
    fn test_generator_must_be_nth_root_of_unity() {
        type Zp = PrimeFieldElement64<541>; // // 540 = 2^2 × 3^3 × 5
        let g = Zp::new(13); // Not a primitive root.
        assert_ne!(g.pow(540), Zp::one());
        let _domain = FFTDomain::from_generator(g, 540);
    }

    /// A size that is not a power of two is an error value, naming the size.
    #[test]
    fn test_a_size_that_is_not_a_power_of_two_is_an_error() {
        type F = PrimeFieldElement64<65537>;
        // The size is rejected before the generator is looked at: 3 does not divide 65536, so
        // this field has no element of order three to offer.
        assert_eq!(
            FFTDomain::try_from_generator(F::one(), 3),
            Err(DomainError::SizeNotPowerOfTwo { size: 3 })
        );
    }

    /// A generator that is not an nth root of unity is an error value rather than a panic.
    #[test]
    fn test_a_generator_that_is_not_an_nth_root_is_an_error() {
        type F = PrimeFieldElement64<65537>;
        // 2 has order 32 in this field, so it is not a 16th root of unity.
        let g = F::new(2);
        assert!(!g.pow(16).is_one());
        assert_eq!(
            FFTDomain::try_from_generator(g, 16),
            Err(DomainError::NotAnNthRoot { size: 16 })
        );
    }

    /// A primitive nth root of the requested order is accepted.
    #[test]
    fn test_a_primitive_root_builds_a_domain() {
        type F = PrimeFieldElement64<65537>;
        let mut rng = StdRng::seed_from_u64(7);
        let n = 16;
        let g = F::root_of_unity(n as u64, &mut rng);
        let domain = FFTDomain::try_from_generator(g, n).expect("a primitive 16th root");
        assert_eq!(domain.size(), n);
    }

    /// An nth root of unity whose order is a proper divisor of n is refused, not silently used.
    ///
    /// `g^8` satisfies `x^16 = 1` but has order 2, so its powers repeat and the domain would hold
    /// two distinct points under sixteen indices — which is the failure the old `pow(size) == 1`
    /// assertion let through.
    #[test]
    fn test_a_root_of_too_small_an_order_is_refused() {
        type F = PrimeFieldElement64<65537>;
        let mut rng = StdRng::seed_from_u64(11);
        let g = F::root_of_unity(16, &mut rng);
        let not_primitive = g.pow(8);
        assert!(not_primitive.pow(16).is_one());
        assert_eq!(
            FFTDomain::try_from_generator(not_primitive, 16),
            Err(DomainError::NotPrimitive { size: 16 })
        );
    }

    /// The one-element domain is the powers of 1, which is a primitive first root of unity.
    #[test]
    fn test_the_one_element_domain_is_accepted() {
        type F = PrimeFieldElement64<65537>;
        let domain = FFTDomain::try_from_generator(F::one(), 1).expect("1 is a first root");
        assert_eq!(domain.size(), 1);
    }

    #[test]
    // Should compute the inverse powers 1, g^{-1}, g^{-2}, .... of the generator g.
    fn test_inverse() {
        type F = PrimeFieldElement64<65537>; // Proth prime, 2^16 + 1
        let mut rng = StdRng::seed_from_u64(3889);
        let n: usize = 32;
        let g = F::root_of_unity(n as u64, &mut rng);
        let domain: FFTDomain<F> = FFTDomain::from_generator(g, n);
        let inverse = domain.inverse();
        let expected_powers = powers_of(&g.inverse(), n);
        assert_eq!(inverse.powers, expected_powers);
    }

    /// A split domain inverts elementwise, though it is not a power sequence starting at one.
    ///
    /// The case that rules out `from_generator(generator().inverse(), size())`: the odd powers
    /// `g, g^3, g^5, ...` have `generator() == g^3`, whose powers are a different set, and
    /// `from_generator` would reject `g^3` outright because `(g^3)^(n/2) = -1`.
    #[test]
    fn test_inverse_of_a_split_domain() {
        type F = PrimeFieldElement64<65537>;
        let mut rng = StdRng::seed_from_u64(104729);
        let n: usize = 32;
        let g = F::root_of_unity(n as u64, &mut rng);
        let domain: FFTDomain<F> = FFTDomain::from_generator(g, n);
        let (evens, odds) = domain.split();

        for part in [&evens, &odds] {
            let inverted = part.inverse();
            assert_eq!(inverted.size(), part.size());
            for (w_i, inverse) in part.iter().zip(inverted.iter()) {
                assert_eq!(*inverse, w_i.inverse(), "domain element {w_i}");
                assert!((*w_i * *inverse).is_one());
            }
        }

        // The odd part really is not a power sequence from one, so the cheaper form is unavailable.
        assert_ne!(odds[0], F::one());
        assert_eq!(odds.generator().pow((n / 2) as u128), F::zero() - F::one());
    }

    #[test]
    // Should split the domain into even and odd powers of the generator.
    fn test_split() {
        type F = PrimeFieldElement64<65537>; // Proth prime, 2^16 + 1
        let mut rng = StdRng::seed_from_u64(3889);
        let n: usize = 32;
        let g = F::root_of_unity(n as u64, &mut rng);
        let domain: FFTDomain<F> = FFTDomain::from_generator(g, n);
        let (evens, odds) = domain.split();
        assert_eq!(evens.size(), n / 2);
        assert_eq!(odds.size(), n / 2);
        for (i, w_i) in evens.iter().enumerate() {
            assert_eq!(*w_i, g.pow((2 * i) as u128));
        }
        for (i, w_i) in odds.iter().enumerate() {
            assert_eq!(*w_i, g.pow((2 * i + 1) as u128));
        }
    }
}
