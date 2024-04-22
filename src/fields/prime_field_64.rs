//! Prime-order finite field.
//!
//! For each prime p, the finite field F_p is defined to be the quotient ring Z/pZ.

use std::{
    fmt::{Display, Formatter},
    ops,
};

use proptest::prelude::{any, Arbitrary, BoxedStrategy, Strategy};
use rand::{CryptoRng, Rng, RngCore};
use serde::{Deserialize, Serialize};

use crate::{FiniteField, identities::{One, Zero}, impl_add_variants, impl_div_variants, impl_mul_variants, impl_sub_variants, integers::{big_uint::BigUInt, factor, find_generator}, Ring};

#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq, Deserialize, Serialize)]
/// Element of a prime field with prime modulus P.
pub struct PrimeFieldElement64<const P: u64> {
    /// The element's representative integer in [0,p-1]
    pub value: u64,
}

impl<const P: u64> Zero for PrimeFieldElement64<P> {
    const ZERO: Self = Self { value: 0 };
}

impl<const P: u64> One for PrimeFieldElement64<P> {
    const ONE: Self = Self { value: 1 };
}

impl<const P: u64> Ring for PrimeFieldElement64<P> {}

impl<const P: u64> FiniteField for PrimeFieldElement64<P> {
    fn new(val: u64) -> Self {
        Self { value: val % P }
    }

    fn from_str(value: &str) -> Result<Self, ()> {
        let parsed = BigUInt::from_dec_str(value).map_err(|_| ())?;
        let modulus = BigUInt::new_from_u64(P);
        let residue = parsed % &modulus;
        let words = residue.as_le_words();
        assert!(words.len() <= 1);

        Ok(Self {
            value: *words.first().unwrap_or(&0),
        })
    }

    fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        let value = rng.gen_range(0..P);
        Self::new(value)
    }

    fn primitive_element<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        // See Algorithm 4.80 of Handbook of Applied Cryptography.
        let n = BigUInt::new_from_u64(P - 1);
        let (prime_factors, powers) = factor(&n, rng);
        let generator = find_generator(&prime_factors, &powers, rng);
        // Convert generator to an integer in [0,P).
        assert!(generator <= n);
        let value = generator.as_le_words()[0];
        Self { value }
    }

    fn root_of_unity<R: RngCore + CryptoRng>(n: u64, rng: &mut R) -> Self {
        // n must divide the group order.
        let group_order = Self::order() - 1;
        assert_eq!(group_order % n as u128, 0, "n must divide the group order.");

        let x = Self::primitive_element(rng);
        x.pow(group_order / n as u128)
    }

    fn order() -> u128 {
        P as u128
    }

    fn characteristic() -> u128 {
        P as u128
    }
}

/// Display
impl<const P: u64> Display for PrimeFieldElement64<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

/// Borrowed + Borrowed
impl<const P: u64> ops::Add<&PrimeFieldElement64<P>> for &PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn add(self, rhs: &PrimeFieldElement64<P>) -> Self::Output {
        let sum = self.value as u128 + rhs.value as u128;
        let value = (sum % P as u128) as u64;
        PrimeFieldElement64 { value }
    }
}

impl_add_variants!([const P: u64], PrimeFieldElement64<P>);

/// Borrowed * Borrowed
impl<const P: u64> ops::Mul<&PrimeFieldElement64<P>> for &PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn mul(self, rhs: &PrimeFieldElement64<P>) -> Self::Output {
        let prod = self.value as u128 * rhs.value as u128;
        let value = (prod % P as u128) as u64;
        Self::Output { value }
    }
}

impl_mul_variants!([const P: u64], PrimeFieldElement64<P>);

/// Borrowed - Borrowed
impl<const P: u64> ops::Sub for &PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn sub(self, rhs: Self) -> Self::Output {
        let difference = self.value as i128 - rhs.value as i128;
        let value = difference.wrapping_rem_euclid(P as i128) as u64;
        Self::Output { value }
    }
}

impl_sub_variants!([const P: u64], PrimeFieldElement64<P>);

impl<const P: u64> ops::Neg for PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn neg(self) -> Self::Output {
        Self::zero() - self
    }
}

impl<const P: u64> ops::Neg for &PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn neg(self) -> Self::Output {
        PrimeFieldElement64::zero() - self
    }
}

/// Borrowed / Borrowed
impl<const P: u64> ops::Div<Self> for &PrimeFieldElement64<P> {
    type Output = PrimeFieldElement64<P>;

    fn div(self, rhs: Self) -> Self::Output {
        // Division is multiplication by the inverse modulo p.
        self * rhs.inverse()
    }
}

impl_div_variants!([const P: u64], PrimeFieldElement64<P>);

/// impl Arbitrary
impl<const P: u64> Arbitrary for PrimeFieldElement64<P> {
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        any::<u64>().prop_map(Self::new).boxed()
    }

    type Strategy = BoxedStrategy<Self>;
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use proptest::{arbitrary::Arbitrary, proptest};
    use rand::{prelude::StdRng, SeedableRng, thread_rng};

    use crate::{
        fields::{
            PrimeFieldElement64, Zp1091, Zp18446744073709551557, Zp2147483647, Zp541, Zp65537, Zp7,
        },
        FiniteField,
        identities::{One, Zero},
    };

    #[test]
    // The default value should be zero.
    fn test_default_is_zero() {
        type F = PrimeFieldElement64<5807>;
        assert_eq!(F::default(), F::zero());
    }

    #[test]
    // Should parse a decimal string mod P.
    fn test_from_str() {
        type Zp = Zp1091;
        for x in 0..10000 {
            assert_eq!(Zp::new(x), Zp::from_str(&x.to_string()).unwrap());
        }
    }

    #[test]
    // random should not panic.
    fn test_random_does_not_panic() {
        let mut rng = thread_rng();
        for _i in 0..1000 {
            let _element = PrimeFieldElement64::<61>::random(&mut rng);
        }
    }

    #[ignore]
    #[test]
    // random() should sample a field element uniformly at random.
    fn test_random_distribution() {
        unimplemented!()
    }

    // A non-zero element times its inverse must be 1.
    fn element_times_inverse_is_one<F: FiniteField>(element: &F) {
        if element.is_zero() {
            return;
        }
        let inverse = element.inverse();
        assert_eq!(*element * inverse, F::one());
    }

    proptest! {
        #[test]
        fn test_inverse_p_7(element in Zp7::arbitrary()) {
            element_times_inverse_is_one(&element);
        }

        #[test]
        fn test_inverse_p_541(element in Zp541::arbitrary()) {
            element_times_inverse_is_one(&element);
        }
    }

    #[test]
    #[should_panic]
    // Zero does not have a multiplicative inverse.
    fn test_inverse_of_zero() {
        type Zp = PrimeFieldElement64<7>;
        let element = Zp::new(0);
        let _inverse = element.inverse();
    }

    fn addition_is_commutative<F: FiniteField>(a: F, b: F) {
        assert_eq!(a + b, b + a);
    }

    proptest! {

        #[test]
        fn test_addition_is_commutative_p_7(a in Zp7::arbitrary(), b in Zp7::arbitrary()) {
            addition_is_commutative(a, b);
        }

        #[test]
        fn test_addition_is_commutative_p_18446744073709551557(a in Zp18446744073709551557::arbitrary(), b in Zp18446744073709551557::arbitrary()) {
            addition_is_commutative(a, b);
        }
    }

    proptest! {
        #[test]
        fn test_addition_is_modulo_p(a in Zp65537::arbitrary(), b in Zp65537::arbitrary()) {
            let sum = a + b;
            assert!(sum.value < 65537);
        }
    }

    #[test]
    // Spot-check that subtraction produces correct values.
    fn test_sub() {
        type Zp = PrimeFieldElement64<7>;
        let a = Zp::new(3);
        let b = Zp::new(2);

        assert_eq!(a - a, Zp::new(0)); // 3 - 3 mod 7
        assert_eq!(a - b, Zp::new(1)); // 3 - 2 mod 7
        assert_eq!(b - a, Zp::new(6)); // 2 - 3 mod 7
    }

    #[test]
    // Spot-check that multiplication produces correct values.
    fn test_mul() {
        type Zp = PrimeFieldElement64<7>;
        let a = Zp::new(3);
        let b = Zp::new(2);

        assert_eq!(a * b, Zp::new(6)); // 3 * 2 mod 7

        let c = Zp::new(6);
        assert_eq!(a * c, Zp::new(4)); // 3 * 6 mod 7
    }

    #[test]
    // Multiply large values so the prod exceeds u64::MAX
    fn test_mul_large_values() {
        const P: u64 = (1u64 << 61) + 20 * (1u64 << 32) + 1; // 2^61 + 20*2^32 + 1
        type Zp = PrimeFieldElement64<P>;
        let a = Zp::new(2u64.pow(50));
        // a * a = 1758668848648192 = 2^100 (mod p)
        assert_eq!(a * a, Zp::new(1758668848648192));
    }

    fn multiplication_is_commutative<F: FiniteField>(a: F, b: F) {
        assert_eq!(a * b, b * a);
    }

    proptest! {
        #[test]
        fn test_multiplication_is_commutative_p_7(a in Zp7::arbitrary(), b in Zp7::arbitrary()) {
            multiplication_is_commutative(a, b);
        }

        #[test]
        fn test_multiplication_is_commutative_p_18446744073709551557(a in Zp18446744073709551557::arbitrary(), b in Zp18446744073709551557::arbitrary()) {
            multiplication_is_commutative(a, b);
        }
    }

    proptest! {
        #[test]
        fn test_multiplication_is_modulo_p(a in Zp65537::arbitrary(), b in Zp65537::arbitrary()) {
            let prod = a * b;
            assert!(prod.value < 65537);
        }
    }

    #[test]
    // x^0 = 1
    fn test_pow_zero() {
        type Zp = PrimeFieldElement64<2147483647>;
        let mut rng = StdRng::seed_from_u64(333378);
        let x = Zp::random(&mut rng);
        assert_eq!(x.pow(0), Zp::one());
    }

    #[test]
    // Spot-check that pow() correctly compute powers.
    fn test_pow() {
        type Zp = Zp2147483647;

        let a = Zp::new(827376);
        assert_eq!(a.pow(1), a);
        assert_eq!(a.pow(2).value, 1651245630);
        assert_eq!(a.pow(7).value, 1787801728);
        assert_eq!(a.pow(43).value, 263804505);
        assert_eq!(a.pow(196).value, 1889125610);
    }

    #[test]
    // Spot-check that division produces correct values.
    fn test_div() {
        type Zp = PrimeFieldElement64<7>;
        let a = Zp::new(6);
        let b = Zp::new(2);
        assert_eq!(a / b, Zp::new(3)); // 6 / 2 mod 7
        assert_eq!(b / a, Zp::new(5)); // 2 / 6 mod 7
    }

    #[test]
    #[should_panic]
    // Dividing by zero should panic.
    fn test_div_by_zero_panics() {
        type Zp = Zp2147483647;
        let a = Zp::new(6);
        let _boom = a / Zp::zero();
    }

    #[test]
    // Powers of the primitive element generate all non-zero elements of the field.
    fn test_primitive_element() {
        const P: u64 = 73;
        type Zp = PrimeFieldElement64<P>;
        let mut rng = StdRng::seed_from_u64(87878);
        let alpha = Zp::primitive_element(&mut rng);
        let nonzero_elements: HashSet<Zp> = (1..P).into_iter().map(Zp::new).collect();
        assert!(nonzero_elements.contains(&alpha));

        let mut generated_elements: HashSet<Zp> = Default::default();
        // \alpha^x, x \in {0, 1, ..., P-2}
        for i in 0..=(P - 2) {
            generated_elements.insert(alpha.pow(i as u128));
        }
        assert_eq!(generated_elements, nonzero_elements);
    }

    #[test]
    // Should not return the trivial root.
    fn test_root_of_unity_is_not_one() {
        let mut rng = StdRng::seed_from_u64(88283746);
        type Zp = PrimeFieldElement64<541>;
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
        type Zp = PrimeFieldElement64<541>;
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

    #[ignore]
    #[test]
    // Should return a **primitive** nth root of unity.
    fn test_root_of_unity_is_primitive() {
        // r^n = 1, but r^k != 1 for any k < n.
        todo!()
    }
}
