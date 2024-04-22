//! A Finite Field (I)FFT domain.
//!
//! The Fast Fourier Transform is a "divide-and-conquer" algorithm that decomposes a Fourier transform
//! of size n = n_1 * n_2 into smaller Fourier transforms of size n_1 and n_2. These can also be
//! decomposed recursively if n_1 and n_2 are composite, and the FFT is fastest when the size
//! n is the product of small prime factors. The simplest case, assumed here, is when the size
//! is a power of 2.

use crate::{fft::evens_and_odds, powers_of, FiniteField};
use std::{
    fmt::{Display, Formatter},
    ops::Index,
};

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

    /// Create an FFT domain from an n^th root of unity.
    ///
    /// # Arguments
    /// * `generator` - An n^th root of unity.
    /// * `size` - The number of elements `n` in the domain.
    pub fn from_generator(generator: F, size: usize) -> Self {
        assert!(size.is_power_of_two());
        assert_eq!(
            generator.pow(size as u128),
            F::one(),
            "Generator {} must be an {}th root of unity",
            generator,
            size,
        );
        let powers = powers_of(&generator, size);
        Self { powers }
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
    pub fn inverse(&self) -> FFTDomain<F> {
        let inverse_powers: Vec<_> = self.powers().iter().map(|w_i| w_i.inverse()).collect();
        FFTDomain::new(inverse_powers)
        // let inverse_generator = self.generator().inverse();
        // FFTDomain::from_generator(inverse_generator, self.size())
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
    use crate::{fields::PrimeFieldElement64, identities::One, powers_of, FFTDomain, FiniteField};
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
        // TODO: does the generator need to be a *primitive* nth root of unity?
        type Zp = PrimeFieldElement64<541>; // // 540 = 2^2 × 3^3 × 5
        let g = Zp::new(13); // Not a primitive root.
        assert_ne!(g.pow(540), Zp::one());
        let _domain = FFTDomain::from_generator(g, 540);
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
