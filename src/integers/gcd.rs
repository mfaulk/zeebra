//! Greatest common divisor of two integers.

/// Greatest common divisor of two integers.
pub fn gcd_u64(a: u64, b: u64) -> u64 {
    gcd_u128(a as u128, b as u128) as u64
}

/// Greatest common divisor of two integers.
pub fn gcd_u128(a: u128, b: u128) -> u128 {
    let mut a = a.clone();
    let mut b = b.clone();
    if a == 0 {
        return b;
    }
    while b != 0 {
        // If a = qb + r, then gcd(a,b) = gcd(b,r)
        let temp = b.clone();
        b = a % &b;
        a = temp;
    }
    a
}

#[cfg(test)]
mod tests {
    use proptest::proptest;

    use crate::integers::gcd_u128;

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
