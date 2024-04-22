//! Finding generators of a cyclic group.
//!
//! Given a cyclic group G of order n, find an element a \in G of order n, called a generator.
//! There is no known efficient algorithm for finding a generator, but it can be done practically
//! using a probabilistic algorithm when the prime factorization of n is given.
//!
//! # References
//! * A Computational Introduction to Number Theory and Algebra, 11.1
//! * Handbook of Applied Cryptography, 4.6

use crate::integers::{
    big_uint::{BigUInt, ONE},
    prime_factors::factoring::from_prime_factorization,
};
use rand::{CryptoRng, RngCore};

/// Find a generator for the cyclic group of order n, given the prime-power factorization of n.
///
/// p - 1 = n = \prod_i q_i ^{e_i}
///
/// # Arguments
/// * `prime_factors` - The primes q_i
/// * `powers` - The power e_i of the prime factor q_i.
pub fn find_generator<R: RngCore + CryptoRng>(
    prime_factors: &[BigUInt],
    powers: &[u128],
    rng: &mut R,
) -> BigUInt {
    assert_eq!(prime_factors.len(), powers.len());

    // See A Computational Introduction to Number Theory and Algebra, 11.1
    let n = from_prime_factorization(prime_factors, powers);
    let p = &n + &ONE;

    let mut gamma = BigUInt::one();
    for (q_i, e) in prime_factors.iter().zip(powers.iter()) {
        let mut alpha = BigUInt::zero();
        let mut beta = BigUInt::one();

        while beta.is_one() {
            alpha = BigUInt::sample_inclusive(&ONE, &n, rng);
            beta = alpha.pow_mod_p(&(&n / q_i), &p);
        }

        let gamma_i = alpha.pow_mod_p(&(&n / &q_i.pow_mod_p(&BigUInt::new_from_u128(*e), &p)), &p);
        gamma = (&gamma * &gamma_i) % &p;
    }

    gamma
}

#[cfg(test)]
mod tests {
    use crate::integers::{
        big_uint::BigUInt,
        prime_factors::{factoring::factor, generator::find_generator, SMALL_PRIMES},
    };
    use rand::{prelude::StdRng, CryptoRng, RngCore, SeedableRng};
    use std::collections::HashSet;

    // Find a generator for Z_p^*
    fn test_generator_zp<R: RngCore + CryptoRng>(p: u64, rng: &mut R) {
        let (prime_factors, powers) = factor(&BigUInt::new_from_u64(p - 1), rng);
        let g = find_generator(&prime_factors, &powers, rng);
        println!("g: {}", &g);

        let mut group_elements: HashSet<BigUInt> = Default::default();
        for i in 1..p {
            group_elements.insert(BigUInt::new_from_u64(i));
        }

        // g must be a group element.
        assert!(group_elements.contains(&g));
        group_elements.remove(&g);

        // Compute the powers of g: g^2, g^3, ... , g^{p-1}
        let mut gi = g.clone();
        for _i in 2..p {
            gi = (gi * &g) % &BigUInt::new_from_u64(p);
            assert!(group_elements.contains(&gi));
            group_elements.remove(&gi);
        }

        // All group elements should have been generated.
        assert_eq!(group_elements.len(), 0);
    }

    #[test]
    // Find generator for the cyclic group Z_7^*
    fn test_find_generator() {
        let mut rng = StdRng::seed_from_u64(909090);

        // Spot checks.
        test_generator_zp(2, &mut rng);
        test_generator_zp(3, &mut rng);
        test_generator_zp(5, &mut rng);
        test_generator_zp(1307, &mut rng);
        test_generator_zp(14153, &mut rng);
        test_generator_zp(43411, &mut rng);

        for p in &SMALL_PRIMES[0..500] {
            test_generator_zp(*p, &mut rng);
        }
    }
}
