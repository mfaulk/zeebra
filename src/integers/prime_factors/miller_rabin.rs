//! Miller-Rabin primality testing.
//!
//! Miller-Rabin is a randomized primality test that can distinguish primes from composites with
//! high probability. Deterministic primality tests exist (i.e., Agrawal-Kayal-Saxena), but they are
//! too slow in practice.
//!
//! Fermat's little theorem:
//! If p is a prime and x is a positive integer that is not divisible by p, then
//!    x^{p-1} mod p = 1
//!
//! The Miller-Rabin test is based on the observation that if n > 1 is an odd integer, then the
//! quantity (n - 1) = 2^e * k, where e \geq 1 and k is odd. If n is prime, then Fermat's little theorem
//! gives us that x^{2^e*k} - 1 \equiv 0 (mod n). We can then repeatedly factor the difference of
//! squares until we reach an expression like:
//!
//! ( x^k - 1 )( x^k + 1 )( x^{2k}+1 )( x^{4k}+1 ) ... ( x^{2^{e-1}k} +1 ) \equiv 0 (mod n).
//!
//! That is, when n is prime, one of the above factors must be 0 mod n:
//!
//!  x^k \eqiv 1 (mod n) or x^{2^{i}k} \eqiv - 1 (mod n), for i \in {0,1, ..., e-1}
//!
//! The Miller-Rabin test proceeds by choosing a random a \in  {1,...,n-1} and evaluating the
//! congruences a^k \eqiv 1 (mod n) and a^{2^{i}k} \eqiv -1 (mod n), for i \in {0,1, ..., e-1}.
//! If **all** of the congruences fail, then we say that a is a Miller-Rabin witness that n is composite.
//! If **any** of the congruences hold, then a is a non-witness and n is a "probable prime". If we
//! do not find a witness in t trials, we conclude that n is prime with probability at least 1 - (1/4)^t.

use crate::integers::{
    big_integers::big_uint::{BigUInt, ONE, TWO, ZERO},
    prime_factors::SMALL_PRIMES,
};
use rand::{CryptoRng, RngCore};

/// Performs multiple iterations of the Miller-Rabin test.
///
/// # Arguments
/// * `n` - An integer.
/// * `n_iterations` - number of iterations of the Miller-Rabin test.
/// * `rng` -
///
/// Returns true if n is a "probable" prime, or false if n has been shown to be composite.
pub fn is_prime<R: RngCore + CryptoRng>(n: &BigUInt, n_iterations: usize, rng: &mut R) -> bool {
    if n.is_zero() || n.is_one() {
        return false;
    }
    if *n == *TWO {
        return true;
    }

    if (n % &BigUInt::new_from_u64(2)).is_zero() {
        // n is an even integer greater than 2.
        return false;
    }

    // TODO: Multiple iterations can be parallelized.
    for i in 0..n_iterations {
        let a = if n < &BigUInt::new_from_u64(10000) {
            // Choose a random value 'a' in [1,...,n-2].
            BigUInt::sample_inclusive(&ONE, &(n - &TWO), rng)
        } else {
            // Heuristically, these work and are faster to compute with than larger integers.
            BigUInt::new_from_u64(SMALL_PRIMES[i + 1])
        };

        // Choose a random value 'a' in [1,...,n-2].
        // let a = BigUInt::sample_inclusive(&ONE, &(n - &TWO), rng);
        if miller_rabin_is_composite(n, &a) {
            return false;
        }
    }

    // n is prime with probability at least 1 - (1/4)^t, where t is num_iterations.
    true
}

/// Miller-Rabin test for compositeness.
///
/// # Arguments
/// * `n` - An odd integer n > 2.
/// * `a` - A possible witness value in [1..n-2].
///
/// Returns true if `a` is a witness for the compositeness of n. Returning false
/// indicates that n may be either prime or composite.
fn miller_rabin_is_composite(n: &BigUInt, a: &BigUInt) -> bool {
    println!("miller-rabin n: {}, a: {}", n, a);
    assert!(*n > *TWO); // n > 2
    assert_eq!(n % &BigUInt::new_from_u64(2), BigUInt::one()); // n must be odd.

    // factor (n-1) = 2^e * k
    let (e, k): (u128, BigUInt) = {
        let mut k = n - &ONE;
        let mut e: u128 = 0;
        while &k % &TWO == *ZERO {
            e += 1;
            k = k / &TWO
        }
        (e, k)
    };
    // By assumption, n is an odd integer greater than 2, so (n-1) >= 2 is an even integer.
    assert!(e > 0);
    assert!(!k.is_zero());

    // If **any** of the congruences hold, then `a` is a non-witness and n is a "probable prime".

    // a^k
    println!("a: {}, e: {}, k: {}", a, e, k);
    let a_k = a.pow_mod_p(&k, n);

    // a^k \eqiv? 1 (mod n)
    if &a_k % n == *ONE {
        // a is a non-witness, and n is a probable prime.
        return false;
    }

    // a^{2^{i}k} \equiv? -1 (mod n) for i in {0, 1, ... e-1}
    let mut temp = a_k;
    for _i in 0..=(e - 1) {
        if (&temp + &ONE) % n == *ZERO {
            // a is a non-witness, and n is a probable prime.
            return false;
        }
        temp = temp.pow(&TWO) % n;
    }

    // **All** congruences failed, so `a` is a Miller-Rabin witness that n is composite.
    true
}

#[cfg(test)]
mod tests {
    use crate::integers::{big_integers::big_uint::BigUInt, prime_factors::miller_rabin::is_prime};
    use rand::{prelude::StdRng, SeedableRng};

    #[test]
    // Miller-Rabin should always categorize a prime as a "probable prime".
    fn test_miller_rabin_primes() {
        let mut rng = StdRng::seed_from_u64(188);
        let primes: Vec<BigUInt> = vec![
            BigUInt::new_from_u64(3),
            BigUInt::new_from_u64(13),
            BigUInt::new_from_u64(709),
            BigUInt::new_from_u64(3109),
            BigUInt::new_from_u64(92237),                // 4*23059 + 1
            BigUInt::new_from_u64(18446744073709551557), // 2^64 - 59
            BigUInt::from_dec_str("340282366920938463463374607431768211297").unwrap(), // 2^128 - 159
        ];

        let n_iterations = 10;
        for n in &primes {
            println!("n: {}", n);
            assert!(is_prime(n, n_iterations, &mut rng));
        }
    }

    #[test]
    // Miller-Rabin should classify a composite as "composite" with high probability, but may
    // classify it as "probable prime".
    fn test_miller_rabin_composites() {
        let mut rng = StdRng::seed_from_u64(1313);
        let composites: Vec<BigUInt> = vec![
            // Even values are trivial to check.
            BigUInt::new_from_u64(4),
            BigUInt::new_from_u64(6),
            BigUInt::new_from_u64(12),
            BigUInt::new_from_u64(4096),
            // Odd composites.
            BigUInt::new_from_u64(9),
            BigUInt::new_from_u64(25),
            BigUInt::new_from_u64(35),
            BigUInt::new_from_u64(49),
            BigUInt::new_from_u64(81),
            BigUInt::new_from_u64(125),
            BigUInt::new_from_u64(6125),
            BigUInt::new_from_u64(16807),       // 7^5
            BigUInt::new_from_u64(117649),      // 7^6
            BigUInt::new_from_u64(823543),      // 7^7,
            BigUInt::new_from_u64(96889010407), // 7^13
            BigUInt::from_dec_str(
                "100974195868289511092701256356196637398170423693954944610595703125",
            )
            .unwrap(), // 5^93
        ];

        let n_iterations = 10;
        for n in &composites {
            assert!(!is_prime(n, n_iterations, &mut rng));
        }
    }

    // Try the pseudo-primes or Carmichael numbers?
}
