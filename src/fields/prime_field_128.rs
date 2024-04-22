//! Prime-order finite field.
//!
//! For each prime p, the finite field F_p is defined to be the quotient ring Z/pZ.

use std::{
    fmt::{Display, Formatter},
    ops,
};

use proptest::{
    arbitrary::Arbitrary,
    prelude::{any, BoxedStrategy, Strategy},
};
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};

use crate::{FiniteField, identities::{One, Zero}, impl_add_variants, impl_div_variants, impl_mul_variants, impl_sub_variants, integers::{big_uint::BigUInt, factor, find_generator, U256, utils::u128_from_parts}, Ring};

#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq, Deserialize, Serialize)]
/// Element of a prime field with prime modulus P.
pub struct PrimeFieldElement128<const P: u128> {
    /// The element's representative integer in [0,p-1]
    pub value: u128,
}

impl<const P: u128> PrimeFieldElement128<P> {
    /// A new field element.
    ///
    /// # Arguments
    /// * `value` - The field element's value, in [0, p-1].
    pub fn new(value: u128) -> Self {
        Self { value: value % P }
    }
}

impl<const P: u128> Zero for PrimeFieldElement128<P> {
    const ZERO: Self = Self { value: 0 };
}

impl<const P: u128> One for PrimeFieldElement128<P> {
    const ONE: Self = Self { value: 1 };
}

impl<const P: u128> Ring for PrimeFieldElement128<P> {}

impl<const P: u128> FiniteField for PrimeFieldElement128<P> {
    fn new(val: u64) -> Self {
        Self {
            value: val as u128 % P,
        }
    }

    fn from_str(value: &str) -> Result<Self, ()> {
        let parsed = BigUInt::from_dec_str(value).map_err(|_| ())?;
        let modulus = BigUInt::new_from_u128(P);
        let residue = parsed % &modulus;
        let words = residue.as_le_words();
        assert!(words.len() <= 2);
        let value = u128_from_parts(*words.first().unwrap_or(&0), *words.get(1).unwrap_or(&0));

        Ok(Self { value })
    }
    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        // Sample a value uniformly in 0..P by rejection sampling.
        let mask_low: u64;
        let mask_high: u64;
        let num_zero_bits = P.leading_zeros();
        if num_zero_bits <= 64 {
            mask_high = u64::MAX.checked_shr(num_zero_bits).unwrap_or(0);
            mask_low = u64::MAX;
        } else {
            mask_high = 0;
            mask_low = u64::MAX.checked_shr(num_zero_bits).unwrap_or(0);
        }

        loop {
            let rand_low = (rng.next_u64() & mask_low) as u128;
            let rand_high = (rng.next_u64() & mask_high) as u128;
            let val = (rand_high << 64) + rand_low;
            if val <= P {
                return Self::new(val);
            }
        }
    }

    fn primitive_element<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        // See Algorithm 4.80 of Handbook of Applied Cryptography.
        let n = BigUInt::new_from_u128(P - 1);
        let (prime_factors, powers) = factor(&n, rng);
        let generator = find_generator(&prime_factors, &powers, rng);
        // Convert generator to an integer in [0,P).
        assert!(generator <= n);
        let words = generator.as_le_words();
        let low: u64 = words.first().cloned().unwrap_or(0);
        let hi: u64 = words.get(1).cloned().unwrap_or(0);
        Self {
            value: u128_from_parts(low, hi),
        }
    }

    fn root_of_unity<R: RngCore + CryptoRng>(n: u64, rng: &mut R) -> Self {
        // n must divide the group order.
        let group_order = Self::order() - 1;
        assert_eq!(group_order % n as u128, 0);

        let x = Self::primitive_element(rng);
        x.pow(group_order / n as u128)
    }

    fn order() -> u128 {
        P
    }

    fn characteristic() -> u128 {
        P
    }
}

/// impl Display
impl<const P: u128> Display for PrimeFieldElement128<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

// Borrowed + Borrowed
impl<const P: u128> ops::Add for &PrimeFieldElement128<P> {
    type Output = PrimeFieldElement128<P>;

    fn add(self, rhs: Self) -> Self::Output {
        let sum = U256::new_from_u128(self.value) + U256::new_from_u128(rhs.value);
        let value = (sum % U256::new_from_u128(P)).as_u128();
        PrimeFieldElement128 { value }
    }
}

impl_add_variants!([const P: u128], PrimeFieldElement128<P>);

// Borrowed * Borrowed
impl<const P: u128> ops::Mul<&PrimeFieldElement128<P>> for &PrimeFieldElement128<P> {
    type Output = PrimeFieldElement128<P>;

    fn mul(self, rhs: &PrimeFieldElement128<P>) -> Self::Output {
        let prod = U256::new_from_u128(self.value) * U256::new_from_u128(rhs.value);
        let value = (prod % U256::new_from_u128(P)).as_u128();
        Self::Output { value }
    }
}

impl_mul_variants!([const P: u128], PrimeFieldElement128<P>);

// Borrowed - Borrowed
impl<const P: u128> ops::Sub<Self> for &PrimeFieldElement128<P> {
    type Output = PrimeFieldElement128<P>;

    fn sub(self, rhs: Self) -> Self::Output {
        let value = if self.value > rhs.value {
            let difference = U256::new_from_u128(self.value) - U256::new_from_u128(rhs.value);
            (difference % U256::new_from_u128(P)).as_u128()
        } else {
            // a - b mod p = a + (P -b) mod P
            (self + (PrimeFieldElement128::new(P - rhs.value))).value
        };
        Self::Output { value }
    }
}

impl_sub_variants!([const P: u128], PrimeFieldElement128<P>);

impl<const P: u128> ops::Neg for PrimeFieldElement128<P> {
    type Output = PrimeFieldElement128<P>;

    fn neg(self) -> Self::Output {
        Self::zero() - self
    }
}

/// impl Neg
impl<const P: u128> ops::Neg for &PrimeFieldElement128<P> {
    type Output = PrimeFieldElement128<P>;

    fn neg(self) -> Self::Output {
        PrimeFieldElement128::zero() - self
    }
}

// Borrowed / Borrowed
impl<const P: u128> ops::Div<Self> for &PrimeFieldElement128<P> {
    type Output = PrimeFieldElement128<P>;

    fn div(self, rhs: Self) -> Self::Output {
        // Division is multiplication by the inverse modulo p.
        self * rhs.inverse()
    }
}

impl_div_variants!([const P: u128], PrimeFieldElement128<P>);

/// impl Arbitrary
impl<const P: u128> Arbitrary for PrimeFieldElement128<P> {
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        any::<u128>().prop_map(Self::new).boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use proptest::{prelude::any, proptest};
    use rand::{prelude::StdRng, SeedableRng, thread_rng};

    use crate::{
        fields::{PrimeFieldElement128, Zp221360928884514619393, Zp541},
        FiniteField, One, Zero,
    };

    #[test]
    // The default value should be zero.
    fn test_default_is_zero() {
        type F = PrimeFieldElement128<5807>;
        assert_eq!(F::default(), F::zero());
    }

    // TODO: 'new' rejects non-prime modulus.

    // TODO: 'new' rejects a value outside of [0, p-1].

    #[test]
    // Should parse a decimal string mod P.
    fn test_from_str() {
        type Zp = PrimeFieldElement128<5807>;
        for x in 0..10000 {
            assert_eq!(Zp::new(x), Zp::from_str(&x.to_string()).unwrap());
        }
    }

    #[test]
    // random should not panic
    fn test_random_doesnt_panic() {
        let mut rng = thread_rng();
        for _i in 0..1000 {
            let _element = PrimeFieldElement128::<61>::random(&mut rng);
        }
    }

    #[ignore]
    #[test]
    // random() should sample a field element uniformly at random.
    fn test_random_distribution() {
        // Randomly sampled values should not be statistically differentiable from a sequence of
        // truly random values sampled from Uniform[0,P). Perform something like Chi-squared test.
        unimplemented!()
    }

    proptest! {
        #[test]
        // A non-zero element times its inverse is one.
        fn test_element_times_inverse_is_one(e in any::<PrimeFieldElement128<541>>()){
            if e == PrimeFieldElement128::<541>::zero() {
                return Ok(());
            }
            let inverse = e.inverse();
            assert_eq!(e * inverse, PrimeFieldElement128::<541>::one());
        }
    }

    #[test]
    #[should_panic]
    // Zero does not have a multiplicative inverse.
    fn test_inverse_of_zero() {
        type Zp = PrimeFieldElement128<7>;
        let element = Zp::new(0);
        let _inverse = element.inverse();
    }

    #[test]
    fn test_add() {
        type Zp = PrimeFieldElement128<7>;
        assert_eq!(Zp::new(3) + Zp::new(2), Zp::new(5)); // 3 + 2 mod 7 = 5
        assert_eq!(Zp::new(3) + Zp::new(6), Zp::new(2)); // 3 + 6 mod 7 = 2
    }

    proptest! {

        #[test]
        fn test_addition_is_commutative(
            a in any::<Zp221360928884514619393>(),
            b in any::<Zp221360928884514619393>()
        ){
            assert_eq!(a + b, b + a);
        }

        #[test]
        fn test_addiion_is_modulo_p(
            a in any::<Zp221360928884514619393>(),
            b in any::<Zp221360928884514619393>()
        ){
            let sum = a + b;
            assert!(sum.value < 221360928884514619393);
        }
    }

    #[test]
    // Add large values so the sum exceeds u64::MAX
    fn test_add_exceeds_max() {
        // 2^128 - 159 = 340282366920938463463374607431768211297 is the largest 128-bit prime.
        const P: u128 = 340282366920938463463374607431768211297;
        let a = PrimeFieldElement128::<P>::new(1 << 127);
        let b = PrimeFieldElement128::<P>::new(1 << 127);
        assert_eq!(a + b, PrimeFieldElement128::new(159)); // sage: 2^128 % (2^128 - 159)
    }

    #[test]
    // Spot-check subtraction
    fn test_sub() {
        type Zp = PrimeFieldElement128<7>;
        let a = Zp::new(3);
        let b = Zp::new(2);
        assert_eq!(a - a, Zp::new(0)); // 3 - 3 mod 7
        assert_eq!(a - b, Zp::new(1)); // 3 - 2 mod 7
        assert_eq!(b - a, Zp::new(6)); // 2 - 3 mod 7
    }

    #[test]
    // Spot-check multiplication.
    fn test_mul() {
        type Zp = PrimeFieldElement128<7>;
        assert_eq!(Zp::new(3) * Zp::new(2), Zp::new(6)); // 3 * 2 mod 7 = 6
        assert_eq!(Zp::new(3) * Zp::new(6), Zp::new(4)); // 3 * 6 mod 7 = 4
    }

    #[test]
    // Multiply large values so the prod exceeds u64::MAX
    fn test_mul_large_values() {
        // 2^128 - 159 = 340282366920938463463374607431768211297 is the largest 128-bit prime.
        const P: u128 = 340282366920938463463374607431768211297;

        let a = PrimeFieldElement128::<P>::new(1 << 122);
        let b = PrimeFieldElement128::<P>::new(1 << 116);

        // sage: p = 2^128 - 159
        // sage: (2^122 * 2^116) % p
        let expected: u128 = 206393800126759398234087229086498816;
        assert_eq!(a * b, PrimeFieldElement128::new(expected));
    }

    proptest! {
        #[test]
        fn test_multiplication_is_commutative(
            a in any::<Zp221360928884514619393>(),
            b in any::<Zp221360928884514619393>()
        ){
            assert_eq!(a * b, b * a);
        }
    }

    #[test]
    // pow() should correctly compute powers.
    fn test_pow() {
        // Mersenne prime 2^31 - 1 = 2147483647.
        const P: u128 = 2147483647;
        let a = PrimeFieldElement128::<P>::new(827376);
        assert_eq!(a.pow(1), a);
        assert_eq!(a.pow(2).value, 1651245630);
        assert_eq!(a.pow(7).value, 1787801728);
        assert_eq!(a.pow(43).value, 263804505);
        assert_eq!(a.pow(196).value, 1889125610);
    }

    #[test]
    // Spot-check division
    fn test_div() {
        type Zp = PrimeFieldElement128<7>;
        assert_eq!(Zp::new(6) / Zp::new(2), Zp::new(3)); // 6 / 2 mod 7 = 3
        assert_eq!(Zp::new(2) / Zp::new(6), Zp::new(5)); // 2 / 6 mod 7 = 5
    }

    #[test]
    #[should_panic]
    // Dividing by zero panics.
    fn test_div_by_zero_panics() {
        // 2^31 - 1 = 2147483647 is a nice prime.
        const P: u128 = 2147483647;
        let a = PrimeFieldElement128::<P>::new(6);
        let _x = a / PrimeFieldElement128::<P>::zero();
    }

    #[test]
    // Powers of a primitive element generate all non-zero elements of the field.
    fn test_primitive_element() {
        const P: u128 = 73;
        type Zp = PrimeFieldElement128<P>;
        let mut rng = StdRng::seed_from_u64(141234);
        let alpha = Zp::primitive_element(&mut rng);
        let nonzero_elements: HashSet<Zp> = (1..P).into_iter().map(Zp::new).collect();
        assert!(nonzero_elements.contains(&alpha));

        let mut generated_elements: HashSet<Zp> = Default::default();
        // \alpha^x, x \in {0, 1, ..., P-2}
        for i in 0..=(P - 2) {
            generated_elements.insert(alpha.pow(i));
        }
        assert_eq!(generated_elements, nonzero_elements);
    }

    #[test]
    // Should not return the trivial root.
    fn test_root_of_unity_is_not_one() {
        let mut rng = StdRng::seed_from_u64(88283746);
        type Zp = Zp541;
        // 540 = 2^2 × 3^3 × 5
        for _i in 1..100 {
            assert_ne!(Zp::root_of_unity(2, &mut rng), Zp::one());
            assert_ne!(Zp::root_of_unity(3, &mut rng), Zp::one());
            assert_ne!(Zp::root_of_unity(5, &mut rng), Zp::one());
        }
    }

    #[test]
    // Should return an nth root of unity, r^n = 1.
    fn test_root_of_unity() {
        let mut rng = StdRng::seed_from_u64(88283746);
        type Zp = Zp541;
        // 540 = 2^2 × 3^3 × 5
        for _i in 1..100 {
            let r_2 = Zp::root_of_unity(2, &mut rng);
            assert_eq!(r_2.pow(2), Zp::one());

            let r_3 = Zp::root_of_unity(3, &mut rng);
            assert_eq!(r_3.pow(3), Zp::one());

            let r_5 = Zp::root_of_unity(5, &mut rng);
            assert_eq!(r_5.pow(5), Zp::one());
        }
    }

    #[test]
    // Should return a **primitive** nth root of unity.
    fn test_root_of_unity_is_primitive() {
        // This can be tested exhaustively for small n. Is there a better way?
        let mut rng = StdRng::seed_from_u64(65537);
        type Zp = Zp221360928884514619393; // Proth prime 3*2^66 + 1
        for exp in [4, 13] {
            let n = 2u64.pow(exp);
            let r = Zp::root_of_unity(n, &mut rng);
            // r^n = 1, but r^k != 1 for any k < n.
            for k in 1..n {
                assert_ne!(r.pow(k as u128), Zp::one());
            }
        }
    }
}
