//! Greatest common divisor of two integers.

/// Greatest common divisor of two integers.
pub fn gcd_u64(a: u64, b: u64) -> u64 {
    gcd_u128(a as u128, b as u128) as u64
}

/// Greatest common divisor of two integers.
pub fn gcd_u128(a: u128, b: u128) -> u128 {
    let mut a = a;
    let mut b = b;
    if a == 0 {
        return b;
    }
    while b != 0 {
        // If a = qb + r, then gcd(a,b) = gcd(b,r)
        let temp = b;
        b = a % &b;
        a = temp;
    }
    a
}

/// The inverse of `a` modulo `m`, or `None` if `gcd(a, m) != 1`.
///
/// The returned value is the representative in `0..m`.
///
/// The Bézout coefficient is carried as a magnitude plus a sign rather than as a signed integer.
/// Its magnitudes obey `|s_{i+1}| = q_i |s_i| + |s_{i-1}|` with the sign alternating, and the
/// largest of them is `m / gcd(a, m)`, so every intermediate fits in a `u128` for every modulus a
/// `u128` can express. The textbook `i128` recurrence would overflow once `m > 2^127`.
pub fn mod_inverse_u128(a: u128, m: u128) -> Option<u128> {
    // Nothing is invertible modulo zero: a*x = 1 has no solution over the integers unless a = 1,
    // and there is no residue to return.
    if m == 0 {
        return None;
    }

    let (mut r_prev, mut r) = (a % m, m);
    let (mut s_prev, mut s) = (1u128, 0u128);
    let mut s_prev_is_negative = false;
    while r != 0 {
        let q = r_prev / r;
        (r_prev, r) = (r, r_prev - q * r);
        (s_prev, s) = (s, s_prev + q * s);
        s_prev_is_negative = !s_prev_is_negative;
    }

    // `r_prev` is gcd(a, m), and `s_prev` the coefficient of `a` in s*a + t*m = gcd.
    if r_prev != 1 {
        return None;
    }
    Some(if s_prev_is_negative {
        (m - s_prev % m) % m
    } else {
        s_prev % m
    })
}

#[cfg(test)]
mod tests {
    use proptest::proptest;

    use crate::integers::{gcd_u128, mod_inverse_u128};

    #[test]
    /// A known inverse: 3 * 5 = 15 = 1 (mod 7).
    fn test_mod_inverse_of_a_small_value() {
        assert_eq!(mod_inverse_u128(3, 7), Some(5));
    }

    #[test]
    /// A value sharing a factor with the modulus has no inverse.
    fn test_mod_inverse_rejects_a_common_factor() {
        assert_eq!(mod_inverse_u128(4, 6), None);
        assert_eq!(mod_inverse_u128(0, 6), None);
    }

    #[test]
    /// Modulo one, every value is congruent to zero, which is its own inverse.
    fn test_mod_inverse_modulo_one() {
        assert_eq!(mod_inverse_u128(0, 1), Some(0));
        assert_eq!(mod_inverse_u128(7, 1), Some(0));
    }

    #[test]
    /// There is no inverse modulo zero.
    fn test_mod_inverse_modulo_zero() {
        assert_eq!(mod_inverse_u128(1, 0), None);
    }

    #[test]
    /// A modulus at the top of the `u128` range, where a signed recurrence would overflow:
    /// 3 * (2^128 - 1)/3 = 2^128 - 1 = 1 (mod 2^128 - 2).
    fn test_mod_inverse_with_a_modulus_near_the_top_of_the_range() {
        let m = u128::MAX - 1; // 2^128 - 2
        let expected = 113427455640312821154458202477256070485; // (2^128 - 1) / 3
        assert_eq!(mod_inverse_u128(3, m), Some(expected));
    }

    proptest! {
        #[test]
        /// Whenever `mod_inverse_u128` returns an inverse, it is one: a * a^-1 = 1 (mod m).
        /// Inputs stay in `u64` so the check itself can multiply without overflowing.
        fn mod_inverse_is_a_multiplicative_inverse(a: u64, m: u64) {
            let (a, m) = (a as u128, m.max(1) as u128);
            match mod_inverse_u128(a, m) {
                Some(inverse) => {
                    assert_eq!(gcd_u128(a, m), 1);
                    assert_eq!((a % m) * inverse % m, 1 % m);
                }
                None => assert_ne!(gcd_u128(a, m), 1),
            }
        }
    }

    #[test]
    /// gcd(0, 0) = 0
    fn test_gcd_of_zero_and_zero() {
        assert_eq!(gcd_u128(0, 0), 0);
    }

    proptest! {
        #[test]
        /// gcd(a, b) divides a and b.
        fn gcd_divides_a_and_b(a: u128, b: u128) {
            let gcd = gcd_u128(a, b);
            assert!(a % gcd == 0);
            assert!(b % gcd == 0);
        }

        #[test]
        /// gcd(0, a) = gcd(a, 0) = a
        fn test_gcd_with_zero(a: u128) {
            assert_eq!(gcd_u128(0, a), a);
            assert_eq!(gcd_u128(a, 0), a);
        }

        #[test]
        /// gcd(1, a) = gcd(a, 1) = 1
        fn test_gcd_with_one(a: u128) {
            assert_eq!(gcd_u128(1, a), 1);
            assert_eq!(gcd_u128(a, 1), 1);
        }

        #[test]
        /// gcd(a, b) = gcd(b, a)
        fn test_gcd_is_symmetric(a: u128, b: u128) {
            assert_eq!(gcd_u128(a, b), gcd_u128(b, a));
        }
    }
}
