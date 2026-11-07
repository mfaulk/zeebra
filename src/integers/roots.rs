//! Integer roots and the perfect-power test.
//!
//! Both are prerequisites rather than endpoints: [`BigUInt::isqrt`] bounds trial division, and
//! [`perfect_power`] is what keeps a factoring driver from spending Pollard rho's whole budget on
//! an `n = m^k` whose only factors are `m`'s.

use crate::integers::{
    big_integers::big_uint::{BigUInt, ONE},
    highest_set_bit,
    prime_factors::SMALL_PRIMES,
};

impl BigUInt {
    /// The integer square root: the largest `r` with `r^2 <= self`.
    pub fn isqrt(&self) -> BigUInt {
        self.nth_root(2)
    }

    /// The integer `k`-th root: the largest `r` with `r^k <= self`.
    ///
    /// Newton's iteration from an initial estimate above the root, where it is monotone decreasing
    /// and so terminates at the floor.
    ///
    /// # Panics
    /// Panics for `k = 0`, which has no root to return: `r^0` is one for every `r`.
    pub fn nth_root(&self, k: u32) -> BigUInt {
        assert!(k > 0, "the zeroth root is not defined");
        if k == 1 || self.is_zero() || self.is_one() {
            return self.clone();
        }

        // 2^ceil(bits/k) raised to the k-th power is at least 2^bits, which exceeds self, so the
        // iteration starts strictly above the root — the side on which it decreases monotonically.
        let bits = highest_set_bit(self.as_le_words()).expect("self is nonzero") + 1;
        let mut estimate = &BigUInt::one() << bits.div_ceil(k as usize);

        let k_minus_one = BigUInt::new_from_u64(k as u64 - 1);
        let k_big = BigUInt::new_from_u64(k as u64);
        loop {
            // next = ((k-1) * estimate + self / estimate^(k-1)) / k
            let next = (&k_minus_one * &estimate + self / &estimate.pow(&k_minus_one)) / &k_big;
            if next >= estimate {
                return estimate;
            }
            estimate = next;
        }
    }
}

/// `n` written as `m^k` with the largest possible `k`, or `None` if `n` is not a perfect power.
///
/// The returned base is never itself a perfect power, because the exponent is maximal. Zero and
/// one are not perfect powers here: every `k` would answer for them, so no answer is informative.
///
/// Only prime exponents are tested, which loses nothing — `n = m^(ab)` is `(m^a)^b` — and the
/// recursion on the base recovers the composite exponent.
pub fn perfect_power(n: &BigUInt) -> Option<(BigUInt, u32)> {
    // m >= 2 bounds the exponent by log2(n), so anything below 2^2 has no room for one.
    let bits = highest_set_bit(n.as_le_words())? + 1;
    if *n < BigUInt::new_from_u64(4) {
        return None;
    }

    for &prime in SMALL_PRIMES.iter() {
        // A base of at least two needs 2^prime <= n, so the exponent cannot exceed log2(n).
        if prime as usize >= bits {
            break;
        }
        let exponent = prime as u32;
        let root = n.nth_root(exponent);
        if root.pow(&BigUInt::new_from_u64(prime)) == *n {
            // The base may be a perfect power in turn: 2^6 is found as 8^2 by the k = 2 pass, and
            // 8 is 2^3, so the maximal exponent is the product.
            return match perfect_power(&root) {
                Some((base, inner)) => Some((base, exponent * inner)),
                None => Some((root, exponent)),
            };
        }
        // A root of one means the exponent has outrun n, which cannot happen below log2(n).
        debug_assert!(root > *ONE);
    }
    None
}

#[cfg(test)]
mod tests {
    use crate::integers::{big_integers::big_uint::BigUInt, roots::perfect_power};
    use proptest::proptest;

    fn big(value: u64) -> BigUInt {
        BigUInt::new_from_u64(value)
    }

    /// `isqrt` is the floor of the square root on small values, including the non-squares.
    #[test]
    fn test_isqrt_small_values() {
        for n in 0u64..100 {
            let root = big(n).isqrt();
            assert_eq!(root, big((n as f64).sqrt().floor() as u64), "isqrt({n})");
        }
    }

    /// `isqrt` is exact on perfect squares, including ones wider than a machine word.
    #[test]
    fn test_isqrt_of_a_perfect_square() {
        assert_eq!(big(1 << 62).isqrt(), big(1 << 31));
        let large = BigUInt::from_dec_str("123456789012345678901234567890").unwrap();
        assert_eq!((&large * &large).isqrt(), large);
    }

    /// `isqrt` returns the floor at both neighbours of a perfect square, which is where an
    /// off-by-one in the iteration's termination would show.
    #[test]
    fn test_isqrt_either_side_of_a_square() {
        let root = BigUInt::from_dec_str("98765432109876543210").unwrap();
        let square = &root * &root;
        assert_eq!((&square - &BigUInt::one()).isqrt(), &root - &BigUInt::one());
        assert_eq!(square.isqrt(), root);
        assert_eq!((&square + &BigUInt::one()).isqrt(), root);
    }

    /// `nth_root` is the floor of the k-th root, exact on k-th powers and truncating otherwise.
    #[test]
    fn test_nth_root() {
        assert_eq!(big(27).nth_root(3), big(3));
        assert_eq!(big(26).nth_root(3), big(2));
        assert_eq!(big(28).nth_root(3), big(3));
        assert_eq!(big(1023).nth_root(10), big(1));
        assert_eq!(big(1024).nth_root(10), big(2));
        assert_eq!(big(3).pow(&big(40)).nth_root(40), big(3));
    }

    /// The first root is the value, and zero and one are their own roots for every k.
    #[test]
    fn test_nth_root_degenerate_arguments() {
        let n = BigUInt::from_dec_str("1234567890123456789").unwrap();
        assert_eq!(n.nth_root(1), n);
        assert_eq!(BigUInt::zero().nth_root(7), BigUInt::zero());
        assert_eq!(BigUInt::one().nth_root(7), BigUInt::one());
    }

    /// The zeroth root is rejected rather than answered arbitrarily.
    #[test]
    #[should_panic(expected = "zeroth root")]
    fn test_nth_root_rejects_a_zero_exponent() {
        let _ = big(8).nth_root(0);
    }

    /// `perfect_power` reports the base and the exponent of a prime power.
    #[test]
    fn test_perfect_power_of_a_prime_power() {
        assert_eq!(perfect_power(&big(9)), Some((big(3), 2)));
        assert_eq!(perfect_power(&big(125)), Some((big(5), 3)));
        assert_eq!(perfect_power(&big(1 << 61)), Some((big(2), 61)));
    }

    /// The exponent returned is the maximal one, so the base is not itself a perfect power.
    #[test]
    fn test_perfect_power_returns_the_maximal_exponent() {
        // 64 = 8^2 = 4^3 = 2^6; only the last has a base that is not a perfect power.
        assert_eq!(perfect_power(&big(64)), Some((big(2), 6)));
        // 6^4, found through the k = 2 pass as 36^2.
        assert_eq!(perfect_power(&big(1296)), Some((big(6), 4)));
    }

    /// A composite base is reported as itself, not factored.
    #[test]
    fn test_perfect_power_with_a_composite_base() {
        assert_eq!(perfect_power(&big(36)), Some((big(6), 2)));
        let base = BigUInt::from_dec_str("1000003000033").unwrap();
        let power = base.pow(&big(3));
        assert_eq!(perfect_power(&power), Some((base, 3)));
    }

    /// Values that are not perfect powers, including the ones with no room for an exponent.
    #[test]
    fn test_not_a_perfect_power() {
        for n in [0, 1, 2, 3, 5, 6, 7, 10, 12, 1000003] {
            assert_eq!(perfect_power(&big(n)), None, "perfect_power({n})");
        }
    }

    proptest! {
        #[test]
        /// r = isqrt(n) satisfies r^2 <= n < (r+1)^2.
        fn isqrt_brackets_the_square_root(n: u128) {
            let n = BigUInt::new_from_u128(n);
            let root = n.isqrt();
            let next = &root + &BigUInt::one();
            assert!(&root * &root <= n);
            assert!(n < &next * &next);
        }

        #[test]
        /// r = nth_root(n, k) satisfies r^k <= n < (r+1)^k.
        fn nth_root_brackets_the_root(n: u128, k in 1u32..=12) {
            let n = BigUInt::new_from_u128(n);
            let exponent = BigUInt::new_from_u64(k as u64);
            let root = n.nth_root(k);
            let next = &root + &BigUInt::one();
            assert!(root.pow(&exponent) <= n);
            assert!(n < next.pow(&exponent));
        }

        #[test]
        /// Whenever `perfect_power` answers, the answer multiplies back out to n and the base is
        /// at least two; whenever it declines, no exponent above one would have worked.
        fn perfect_power_agrees_with_an_exhaustive_search(n in 4u64..100_000) {
            let n = BigUInt::new_from_u64(n);
            match perfect_power(&n) {
                Some((base, exponent)) => {
                    assert!(base >= BigUInt::new_from_u64(2));
                    assert_eq!(base.pow(&BigUInt::new_from_u64(exponent as u64)), n);
                }
                None => {
                    for k in 2u32..=17 {
                        let root = n.nth_root(k);
                        assert_ne!(root.pow(&BigUInt::new_from_u64(k as u64)), n, "n = {n} is a {k}-th power");
                    }
                }
            }
        }
    }
}
