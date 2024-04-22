//! Pollard's Rho algorithm for integer factorization.
//!
//! Pick k numbers x_1, ..., x_k uniformly at random between 2 and n.
//! Ask if GCD( x_i - x_j, n) > 1. If yes, then the GCD is a factor of n.
//! Pollard's rho algorithm is sort of like a fancy version of trial division, where instead of
//! looking for an exact factor of n, we look for a number x with a non-trivial GCD with n.
//! The rho algorithm makes use of the birthday paradox to reduce the number of samples we need in
//! order to find a GCD with n: instead of sampling a sequence of values {x_i} and testing
//! GCD( x_i , n ), it tests GCD( x_i - x_j , n). This reduces the number of values {x_i} that we
//! need to sample from n^{1/2} to n^{1/4}.
//!  
//! Unfortunately, n^{1/4} could be a lot of samples to keep in memory. To avoid this, we can use a
//! pseudo-random function to compute the values (i.e., instead of storing them and looking them up).
//! This mostly works, but there is a chance that the pseudo-randomly chosen sequence will repeat
//! itself and fall into infinite looping. The "fix" here is to use a cycle detection algorithm
//! (e.g. Floyd's "tortoise and hare" algorithm) and terminate the algorithm if a loop is detected.

use crate::integers::{
    big_integers::big_uint::{BigUInt, ONE},
    prime_factors::miller_rabin::is_prime,
};
use rand::{CryptoRng, RngCore};
use std::collections::BTreeMap;

// Number of Miller-Rabin iterations.
const NUM_ITERATIONS_MR: usize = 5;

/// Pollard's rho algorithm for integer factorization.
///
/// # Arguments
/// * `n` - A composite integer that is not a prime power.
/// * `x_0` - The initial point.
///
/// This is a probabilistic algorithm. If successful, returns a non-trivial factor (not necessarily prime).
/// If not successful, the algorithm should be retried with a different initial point.
pub fn pollards_rho(n: &BigUInt, x_0: &BigUInt) -> Result<BigUInt, ()> {
    println!("pollards rho, n: {}, x_0: {}", n, x_0);
    // Defines the pseudo-random sequence x_{i+1} = x_i^2 + 1 (mod n)
    fn f(x: &BigUInt, n: &BigUInt) -> BigUInt {
        (x * x + &BigUInt::one()) % n
    }

    let mut x_i = x_0.clone();
    let mut y_i = x_0.clone();

    loop {
        x_i = f(&x_i, n);
        y_i = f(&f(&y_i, n), n);
        // | x_i - y_i |
        let absolute_difference = if x_i > y_i { &x_i - &y_i } else { &y_i - &x_i };
        let factor = n.gcd(&absolute_difference);
        if factor == *ONE {
            continue;
        } else if factor == *n {
            // Fail. This is an indirect way of saying that a cycle has been detected, i.e.,
            // x_i - y_i = 0, and so GCD(0,n) = n.
            return Err(());
        } else {
            return Ok(factor);
        }
    }
}

/// Prime-powers factorization by repeated Pollard rho.
pub fn pollards_rho_factorize<R: RngCore + CryptoRng>(
    n: &BigUInt,
    rng: &mut R,
) -> (Vec<BigUInt>, Vec<u128>) {
    if is_prime(n, NUM_ITERATIONS_MR, rng) {
        return (vec![n.clone()], vec![1]);
    }
    let mut composite_factors: Vec<BigUInt> = vec![n.clone()];

    // Map from prime factor p to its exponent.
    let mut prime_factors: BTreeMap<BigUInt, u128> = Default::default();

    let mut loop_count: usize = 0;
    while !composite_factors.is_empty() && loop_count < 1000 {
        loop_count += 1;
        let n = composite_factors.pop().unwrap();
        let x_0 = BigUInt::new_from_u64(rng.next_u64());
        if let Ok(f) = pollards_rho(&n, &x_0) {
            let remainder = n / &f;
            if is_prime(&f, NUM_ITERATIONS_MR, rng) {
                *prime_factors.entry(f).or_insert(0) += 1;
            } else {
                composite_factors.push(f);
            }

            if is_prime(&remainder, NUM_ITERATIONS_MR, rng) {
                *prime_factors.entry(remainder).or_insert(0) += 1;
            } else {
                composite_factors.push(remainder);
            }
        } else {
            // Else, failed to find a factor from the initial point. Put n back, and try again.
            composite_factors.push(n);
        }
    }
    // BTreeMap returns these in order, sorted by prime factor.
    prime_factors.into_iter().unzip()
}

#[cfg(test)]
mod tests {
    use crate::integers::{
        big_integers::big_uint::BigUInt,
        prime_factors::pollard_rho::{pollards_rho, pollards_rho_factorize},
    };
    use rand::{prelude::StdRng, SeedableRng};

    #[test]
    fn test_pollards_rho() {
        // Depending on the initial point, the algorithm should return Some(1931), Some(7573), or None.
        // let n = U256::from(14623463); // 1931 * 7573 = 14623463
        let n = BigUInt::new_from_u64(14623463); // 1931 * 7573 = 14623463
        assert_eq!(
            pollards_rho(&n, &BigUInt::new_from_u64(2)).unwrap(),
            BigUInt::new_from_u64(1931)
        );

        assert_eq!(
            pollards_rho(&n, &BigUInt::new_from_u64(14)).unwrap(),
            BigUInt::new_from_u64(7573)
        );

        // This should happen infrequently.
        assert!(pollards_rho(&n, &BigUInt::new_from_u64(115)).is_err());
    }

    #[test]
    // Initial point is a number whose square exceeds 256-bits.
    fn test_pollards_rho_doesnt_overflow() {
        // sage: 2 * (2^226 - 5)
        let x_0 = BigUInt::from_dec_str(
            "215679573337205118357336120696157045389097155380324579848828881993718",
        )
        .unwrap();

        let n = BigUInt::new_from_u64(14623463); // 1931 * 7573 = 14623463
        assert_eq!(pollards_rho(&n, &x_0).unwrap(), BigUInt::new_from_u64(1931));
    }

    #[test]
    // Should return ([n], [1]) if n is prime.
    fn test_pollard_rho_factorize_n_is_prime() {
        let mut rng = StdRng::seed_from_u64(99283);
        for prime in [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 104729].iter() {
            let n = BigUInt::new_from_u64(*prime);
            let (primes, exponents) = pollards_rho_factorize(&n, &mut rng);
            assert_eq!(primes, vec![n]);
            assert_eq!(exponents, vec![1]);
        }
    }

    #[test]
    // Should return a full factorization of 1931 * 7573.
    fn test_pollard_rho_factorize_14623463() {
        let mut rng = StdRng::seed_from_u64(99283);
        let n = BigUInt::new_from_u64(14623463); // 1931 * 7573 = 14623463
        let (primes, exponents) = pollards_rho_factorize(&n, &mut rng);
        assert_eq!(
            primes,
            vec![BigUInt::new_from_u64(1931), BigUInt::new_from_u64(7573)]
        );
        assert_eq!(exponents, vec![1, 1])
    }

    #[test]
    // Should return a full factorization of 47 * 1931^3 * 7573.
    fn test_pollard_rho_factorize_2562787730409121() {
        let mut rng = StdRng::seed_from_u64(87993);
        let n = BigUInt::new_from_u64(2562787730409121); // 47 * 1931^3 * 7573
        let (primes, exponents) = pollards_rho_factorize(&n, &mut rng);
        assert_eq!(
            primes,
            vec![
                BigUInt::new_from_u64(47),
                BigUInt::new_from_u64(1931),
                BigUInt::new_from_u64(7573)
            ]
        );
        assert_eq!(exponents, vec![1, 3, 1]);
    }
}
