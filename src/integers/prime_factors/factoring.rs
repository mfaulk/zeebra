//! Integer factorization.

use crate::integers::{
    big_integers::big_uint::{BigUInt, ZERO},
    prime_factors::{pollard_rho::pollards_rho_factorize, SMALL_PRIMES},
};
use rand::{CryptoRng, RngCore};

/// Factor an integer into the product of prime powers, x = \prod_i p_i^{e_i}
pub fn factor<R: RngCore + CryptoRng>(x: &BigUInt, rng: &mut R) -> (Vec<BigUInt>, Vec<u128>) {
    let mut x = x.clone();
    let mut prime_factors: Vec<BigUInt> = Default::default();
    let mut powers: Vec<u128> = Default::default();

    // Trial division by small primes. Good for numbers up to ~ 2^16.
    for p in SMALL_PRIMES.into_iter().map(BigUInt::new_from_u64) {
        if x.is_one() {
            // x has been fully factored.
            return (prime_factors, powers);
        }

        if &x % &p == *ZERO {
            // p is a prime factor.
            let mut power: u128 = 1;
            x = &x / &p;

            // Remove additional multiples of p.
            while x >= p && &x % &p == *ZERO {
                x = &x / &p;
                power += 1;
            }

            prime_factors.push(p);
            powers.push(power);
        }
    }

    // Use Pollard's rho method to find additional factors.
    let (p, e) = pollards_rho_factorize(&x, rng);
    prime_factors.extend_from_slice(&p);
    powers.extend_from_slice(&e);

    // TODO: Finally, apply a general-purpose algorithm (e.g. quadratic sieve, general number field sieve, etc).

    (prime_factors, powers)
}

/// Compute n from its prime factorization n = \prod_i p_i^{e_i}.
///
/// # Arguments
/// * `prime_factors` - The primes p_i
/// * `powers` - The power e_i of the prime factor p_i.
pub fn from_prime_factorization(prime_factors: &[BigUInt], powers: &[u128]) -> BigUInt {
    assert_eq!(prime_factors.len(), powers.len());
    let mut n = BigUInt::one();
    for (p, e) in prime_factors.iter().zip(powers.iter()) {
        n = n * &p.pow(&BigUInt::new_from_u128(*e));
    }
    n
}

#[cfg(test)]
mod tests {
    use crate::integers::{
        big_integers::big_uint::BigUInt,
        prime_factors::{factoring::factor, miller_rabin::is_prime},
    };
    use rand::{prelude::StdRng, SeedableRng};

    #[test]
    #[ignore] // Slow test
    fn test_factorization_122234025357862370736689285321110574726() {
        let mut rng = StdRng::seed_from_u64(383);
        // 2 * 1747 * 1377882830479031 * 25389662319625554359
        let n = BigUInt::from_dec_str("122234025357862370736689285321110574726").unwrap();
        let (primes, powers) = factor(&n, &mut rng);
        let expected_primes: Vec<BigUInt> = vec![
            BigUInt::new_from_u64(2),
            BigUInt::new_from_u64(1747),
            BigUInt::new_from_u64(1377882830479031),
            BigUInt::from_dec_str("25389662319625554359").unwrap(),
        ];
        // 1180591620717411303424

        let expected_powers = vec![1, 1, 1, 1];
        assert_eq!(primes, expected_primes);
        assert_eq!(powers, expected_powers);
    }

    #[test]
    // Prime factors must be in increasing order.
    fn test_factorization_is_in_increasing_order() {
        // sage: factor(1239879817230798)
        // 2 * 3 * 241 * 857454922013
        let mut rng = StdRng::seed_from_u64(383);
        let n = BigUInt::from_dec_str("1239879817230798").unwrap();
        let (primes, powers) = factor(&n, &mut rng);
        assert_eq!(
            primes,
            vec![
                BigUInt::new_from_u64(2),
                BigUInt::new_from_u64(3),
                BigUInt::new_from_u64(241),
                BigUInt::from_dec_str("857454922013").unwrap()
            ]
        );
        assert_eq!(powers, vec![1, 1, 1, 1]);
    }

    #[test]
    // The prime-powers representation must equal the original number.
    fn test_factorization_recovers_original_number() {
        let mut rng = StdRng::seed_from_u64(3993);
        for _i in 0..9 {
            let x = BigUInt::sample_inclusive(
                &BigUInt::zero(),
                &BigUInt::from_dec_str("10000000000").unwrap(),
                &mut rng,
            );
            if !is_prime(&x, 3, &mut rng) {
                let (_primes, _powers) = factor(&x, &mut rng);
            }
        }
    }

    #[test]
    // Should correctly factorize products of "small primes" and their powers.
    fn test_factorization_of_small_primes_2() {
        let mut rng = StdRng::seed_from_u64(3883);
        let n = BigUInt::new_from_u64(2);
        let (primes, powers) = factor(&n, &mut rng);
        assert_eq!(primes, vec![BigUInt::new_from_u64(2)]);
        assert_eq!(powers, vec![1]);
    }

    #[test]
    // Should correctly factorize products of "small primes" and their powers.
    fn test_factorization_of_small_primes_4409() {
        let mut rng = StdRng::seed_from_u64(3883);
        let n = BigUInt::new_from_u64(4409);
        let (primes, powers) = factor(&n, &mut rng);
        assert_eq!(primes, vec![BigUInt::new_from_u64(4409)]);
        assert_eq!(powers, vec![1]);
    }

    #[test]
    // Should correctly factorize products of "small primes" and their powers.
    fn test_factorization_of_small_primes_14() {
        let mut rng = StdRng::seed_from_u64(3883);
        let n = BigUInt::new_from_u64(14);
        let (primes, powers) = factor(&n, &mut rng);
        let expected_primes: Vec<BigUInt> =
            vec![2, 7].into_iter().map(BigUInt::new_from_u64).collect();
        let expected_powers = vec![1, 1];
        assert_eq!(primes, expected_primes);
        assert_eq!(powers, expected_powers);
    }

    #[test]
    // Should correctly factorize products of "small primes" and their powers.
    fn test_factorization_of_small_primes_98() {
        let mut rng = StdRng::seed_from_u64(3883);
        let n = BigUInt::new_from_u64(98);
        let (primes, powers) = factor(&n, &mut rng);
        let expected_primes: Vec<BigUInt> =
            vec![2, 7].into_iter().map(BigUInt::new_from_u64).collect();
        let expected_powers = vec![1, 2];
        assert_eq!(primes, expected_primes);
        assert_eq!(powers, expected_powers);
    }

    #[test]
    // Should correctly factorize products of "small primes" and their powers.
    fn test_factorization_of_small_primes_1290159361801237() {
        let mut rng = StdRng::seed_from_u64(3883);
        let n = BigUInt::new_from_u64(1290159361801237); // 4409^3 * 15053
        let (primes, powers) = factor(&n, &mut rng);
        let expected_primes: Vec<BigUInt> = vec![4409, 15053]
            .into_iter()
            .map(BigUInt::new_from_u64)
            .collect();
        let expected_powers = vec![3, 1];
        assert_eq!(primes, expected_primes);
        assert_eq!(powers, expected_powers);
    }

    #[test]
    #[ignore] // Slow test
    fn test_factorization_25519() {
        let mut rng = StdRng::seed_from_u64(3883);
        // 2^255 - 19
        let n = BigUInt::from_dec_str(
            "53919893334301279589334030174039261347274288845081144962207220498413",
        )
        .unwrap();

        let (primes, powers) = factor(&n, &mut rng);
        let expected_primes: Vec<BigUInt> = vec![
            BigUInt::new_from_u64(17),
            BigUInt::new_from_u64(1187),
            BigUInt::new_from_u64(14411),
            BigUInt::new_from_u64(718943873),
            BigUInt::from_dec_str("257905307077116855891360591658724367533687172297949").unwrap(),
        ];
        let expected_powers = vec![1, 1, 1, 1, 1];
        assert_eq!(primes, expected_primes);
        assert_eq!(powers, expected_powers);
    }
}
