//! `c * p` for every concrete field type, which is where the orphan rule forces this to live.
//!
//! The mathematics writes `c·p`, and until now the crate had to write `p * c` or `m.scale(&c)` —
//! `impl<F: FiniteField> Mul<DensePolynomial<F>> for F` does not compile, because `F` is a type
//! parameter and the `Self` type of that impl is therefore not local.
//!
//! The way round it is a **concrete local type** in the `Self` position. One invocation per field
//! element *struct* rather than per field, because `PrimeFieldElement64<P>` is local for every `P`:
//! six invocations below cover every prime, every binary modulus and every extension the crate
//! names, including ones nobody has written an alias for yet.
//!
//! This module is impls and nothing else. It is here rather than beside the fields because it
//! mentions `linalg` and `poly`, and rather than beside the containers because there are four of
//! them and the list of fields belongs in one place — `test_the_field_list_covers_every_field_type`
//! is what keeps that list honest as fields are added.

use crate::{
    fields::{
        BinaryFieldElement, ExtensionFieldElement, IrreduciblePolynomial, PrimeFieldElement256,
        PrimeFieldElement32, PrimeFieldElement64, PrimeModulus256,
    },
    impl_left_scalar_mul,
};

impl_left_scalar_mul!([const P: u32], PrimeFieldElement32<P>);
impl_left_scalar_mul!([const P: u64], PrimeFieldElement64<P>);
impl_left_scalar_mul!([M: PrimeModulus256], PrimeFieldElement256<M>);
impl_left_scalar_mul!([const P: u64], BinaryFieldElement<P>);
impl_left_scalar_mul!(
    [const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>],
    ExtensionFieldElement<P, N, M>
);

/// `PrimeFieldElement128` is deprecated by #163 but still public, so it keeps the operators.
///
/// The module exists only to scope `allow(deprecated)` over the expansion: a lint attribute on a
/// macro invocation is inert, and the expansion names the deprecated type sixteen times.
#[allow(deprecated)]
mod deprecated_prime_field_128 {
    use crate::{fields::PrimeFieldElement128, impl_left_scalar_mul};

    impl_left_scalar_mul!([const P: u128], PrimeFieldElement128<P>);
}

#[cfg(test)]
mod tests {
    // Zp221360928884514619393 is deprecated by #163; the coverage test still has to name it.
    #[allow(deprecated)]
    use crate::{
        fields::{Bn254Fr, Gf13Pow4, Gf256, KoalaBear, Zp13, Zp221360928884514619393},
        linalg::{Matrix, Vector},
        FiniteField, Monomial, MultivariatePolynomial, UnivariatePolynomial,
    };

    /// `c * p` agrees with `p * c` for a univariate polynomial, in all four ownership spellings.
    #[test]
    fn test_left_and_right_scalar_multiplication_agree_on_a_univariate_polynomial() {
        type F = Zp13;
        let p = UnivariatePolynomial::<F>::new(&[F::new(1), F::new(2), F::new(3)]);
        let c = F::new(5);
        let expected = &p * &c;
        assert_eq!(&c * &p, expected);
        assert_eq!(&c * p.clone(), expected);
        assert_eq!(c * &p, expected);
        assert_eq!(c * p, expected);
    }

    /// `c * p` agrees with `p * c` for a multivariate polynomial, in all four ownership spellings.
    ///
    /// Covers the right-hand operator too, which `SparseMultiPoly` had in neither direction.
    #[test]
    fn test_left_and_right_scalar_multiplication_agree_on_a_multivariate_polynomial() {
        type F = KoalaBear;
        let p = MultivariatePolynomial::<3, F>::new(&[
            (Monomial::new(&[2, 0, 1]), F::new(7)),
            (Monomial::new(&[0, 1, 0]), F::new(11)),
        ]);
        let c = F::new(5);
        let expected = p.scale(&c);
        assert_eq!(&p * &c, expected);
        assert_eq!(&p * c, expected);
        assert_eq!(p.clone() * &c, expected);
        assert_eq!(p.clone() * c, expected);
        assert_eq!(&c * &p, expected);
        assert_eq!(&c * p.clone(), expected);
        assert_eq!(c * &p, expected);
        assert_eq!(c * p, expected);
    }

    /// `c * m` and `c * v` agree with the right-hand spellings, over a matrix and a vector.
    #[test]
    fn test_left_and_right_scalar_multiplication_agree_on_a_matrix_and_a_vector() {
        type F = Zp13;
        let m = Matrix::<F>::new(2, 2, &[F::new(1), F::new(2), F::new(3), F::new(4)]);
        let c = F::new(5);
        let expected = &m * &c;
        assert_eq!(&c * &m, expected);
        assert_eq!(&c * m.clone(), expected);
        assert_eq!(c * &m, expected);
        assert_eq!(c * m.clone(), expected);
        assert_eq!(m.clone() * &c, expected);
        assert_eq!(m * c, expected);

        let v = Vector::<F>::new(&[F::new(1), F::new(2), F::new(3)]);
        let expected = &v * &c;
        assert_eq!(&c * &v, expected);
        assert_eq!(&c * v.clone(), expected);
        assert_eq!(c * &v, expected);
        assert_eq!(c * v.clone(), expected);
        assert_eq!(v.clone() * &c, expected);
        assert_eq!(v * c, expected);
    }

    /// Every field element struct the crate defines has the left-hand operators.
    ///
    /// **The test that keeps the list in this module honest.** The impls are per *struct*, so a
    /// new field reached through an existing struct — another prime, another binary modulus — is
    /// covered with no edit, and only a new struct needs one. This body does not compile if an
    /// invocation is missing, which is the whole check; the field aliases are chosen one per
    /// struct, with `Gf13Pow4` standing for `ExtensionFieldElement` and `Bn254Fr` for
    /// `PrimeFieldElement256`.
    #[test]
    #[allow(deprecated)] // PrimeFieldElement128 is still a struct the crate defines.
    fn test_the_field_list_covers_every_field_type() {
        fn covered<F>()
        where
            F: FiniteField,
            F: std::ops::Mul<UnivariatePolynomial<F>, Output = UnivariatePolynomial<F>>,
            F: std::ops::Mul<MultivariatePolynomial<2, F>, Output = MultivariatePolynomial<2, F>>,
            F: std::ops::Mul<Matrix<F>, Output = Matrix<F>>,
            F: std::ops::Mul<Vector<F>, Output = Vector<F>>,
        {
            let p = UnivariatePolynomial::<F>::new(&[F::one(), F::one()]);
            assert_eq!(F::one() * p.clone(), p);
        }

        covered::<KoalaBear>(); // PrimeFieldElement32
        covered::<Zp13>(); // PrimeFieldElement64
        covered::<Zp221360928884514619393>(); // PrimeFieldElement128
        covered::<Bn254Fr>(); // PrimeFieldElement256
        covered::<Gf256>(); // BinaryFieldElement
        covered::<Gf13Pow4>(); // ExtensionFieldElement
    }
}
