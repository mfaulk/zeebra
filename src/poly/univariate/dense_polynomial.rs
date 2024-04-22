//! A univariate polynomial whose coefficients are from a finite field `F`.

use std::fmt::{Display, Formatter};

use proptest::{
    arbitrary::{any, Arbitrary},
    collection::vec,
    prelude::{BoxedStrategy, Strategy},
};
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};

use crate::{
    poly::univariate::{
        div_with_remainder::div_with_remainder, trim,
        univariate_parser::parse_univariate_polynomial, Polynomial,
    },
    FiniteField,
};

/// A Polynomial over a finite field `F`.
#[derive(Clone, Debug, Default, Eq, PartialEq, Deserialize, Serialize)]
pub struct DensePolynomial<F: FiniteField> {
    /// coefficients[i] = a_i
    #[serde(bound = "F: FiniteField")]
    pub coefficients: Vec<F>,
}

impl<F: FiniteField> DensePolynomial<F> {
    /// A polynomial with the given coefficients.
    pub fn new(coefficients: &[F]) -> Self {
        let mut coefficients = coefficients.to_vec();
        trim(&mut coefficients);
        Self { coefficients }
    }

    /// A polynomial with the given zeros.
    pub fn from_zeros(zeros: &[F]) -> Self {
        // \prod (x - x_i)
        zeros
            .iter()
            .fold(Self::one(), |p, x| p * Self::new(&[x.neg(), F::one()]))
    }
}

impl<F: FiniteField> Polynomial<F> for DensePolynomial<F> {
    fn lift(c: &F) -> Self {
        Self::new(&[*c])
    }

    fn coefficients(&self) -> &[F] {
        &self.coefficients
    }

    fn degree(&self) -> u32 {
        // Coefficients must not contain trailing (i.e., high-order) zeros.
        if self.coefficients.len() > 1 {
            assert!(*self.coefficients.last().unwrap() != F::zero());
        }

        // TODO: the zero polynomial's degree is undefined, but here it is zero.
        (self.coefficients.len() - 1) as u32
    }

    fn eval(&self, x: &F) -> F {
        // Horner's rule P(x) = a_0 + x(a_1 + x(a_2 + ... + xa_{n-1}))
        let mut result = F::zero();
        for (i, a_i) in self.coefficients.iter().enumerate().rev() {
            if i == 0 {
                result += *a_i;
            } else {
                result = *x * (*a_i + result);
            }
        }
        result
    }

    fn zero() -> Self {
        Self {
            coefficients: vec![F::zero()],
        }
    }

    fn is_zero(&self) -> bool {
        self.coefficients.is_empty()
            || self.coefficients.len() == 1 && self.coefficients[0] == F::zero()
    }

    fn one() -> Self {
        Self {
            coefficients: vec![F::one()],
        }
    }

    fn is_one(&self) -> bool {
        self.coefficients.len() == 1 && self.coefficients[0].is_one()
    }

    /// A random polynomial of degree `d`.
    fn rand<R: RngCore + CryptoRng>(d: u64, rng: &mut R) -> Self {
        let coefficients: Vec<_> = (0..=d)
            .map(|i| {
                if i == d {
                    let mut c_i = F::random(rng);
                    // The degree-d term must have non-zero coefficient.
                    while c_i.is_zero() {
                        c_i = F::random(rng);
                    }
                    c_i
                } else {
                    F::random(rng)
                }
            })
            .collect();
        // By construction, coefficients does not contain high-order zeros.
        Self { coefficients }
    }

    fn scale(&self, c: &F) -> Self {
        let coefficients: Vec<F> = self
            .coefficients
            .iter()
            .map(|coefficient| *c * coefficient)
            .collect();

        Self::new(&coefficients)
    }

    fn shift(&self, k: &F) -> Self {
        let x_plus_k = DensePolynomial::new(&[*k, F::one()]);
        self.compose(&x_plus_k)
    }

    fn pow(&self, b: u32) -> Self {
        if self.is_zero() {
            if b == 0 {
                // 0^0 = 1.
                return Self::one();
            }
            return Self::zero();
        }

        if b == 0 {
            return Self::one();
        }

        // Exponentiation by squaring.
        if b == 1 {
            self.clone()
        } else if b % 2 == 0 {
            // b is even: a^b = a^(b/2) * a^(b/2)
            let y = self.pow(b / 2);
            &y * &y
        } else {
            // b is odd: a^b = a * a^(b-1)
            self * self.pow(b - 1)
        }
    }

    fn compose(&self, p: &Self) -> Self {
        let mut result = Self::zero();
        for (power, coefficient) in self.coefficients.iter().enumerate() {
            result = result + p.pow(power as u32) * coefficient;
        }
        result
    }

    fn div(&self, divisor: &Self) -> (Self, Self) {
        div_with_remainder(self, divisor)
    }
}

/// TryFrom<&str>
impl<F: FiniteField> TryFrom<&str> for DensePolynomial<F> {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        println!("{}", value);
        // TODO: return an informative error.
        parse_univariate_polynomial(value).map_err(|_| ())
    }
}

/// Display
impl<F: FiniteField> Display for DensePolynomial<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut term_strings: Vec<String> = Vec::new();
        for (i, c) in self.coefficients.iter().enumerate() {
            if c.is_zero() {
                continue;
            }
            let coefficient: String = c.to_string();
            let power: String = if i == 1 {
                // x^1 is just x.
                "x".to_string()
            } else {
                format!("x^{}", i)
            };

            format!("x^{}", i);

            if i == 0 {
                // c * x^0 is just c.
                term_strings.push(coefficient);
            } else if c.is_one() {
                // 1 * x^i is just x^i.
                term_strings.push(power);
            } else {
                // c*x^i
                term_strings.push([coefficient, power].join("*"));
            }
        }

        if term_strings.is_empty() {
            write!(f, "0")
        } else {
            write!(f, "{}", term_strings.join(" + "))
        }
    }
}

// impl Arbitrary
impl<F: FiniteField + 'static> Arbitrary for DensePolynomial<F> {
    type Parameters = usize; // degree

    // Generate a random polynomial of the given degree.
    fn arbitrary_with(degree: Self::Parameters) -> Self::Strategy {
        vec(any::<F>(), degree + 1)
            .prop_filter("nonzero leading coefficient", |coefficients| {
                !coefficients.last().unwrap().is_zero()
            })
            .prop_map(|coefficients| Self::new(&coefficients))
            .boxed()
    }

    type Strategy = BoxedStrategy<DensePolynomial<F>>;
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use rand::{prelude::StdRng, SeedableRng};

    use crate::{
        fields::{PrimeFieldElement64, Zp541},
        identities::Zero,
        poly::univariate::{dense_polynomial::DensePolynomial, Polynomial},
        FiniteField,
    };

    fn get_elements(values: Vec<u64>) -> Vec<PrimeFieldElement64<13>> {
        values
            .iter()
            .map(|v| PrimeFieldElement64::new(*v))
            .collect()
    }

    #[test]
    // The zero polynomial should contain a single coefficient a_0 = 0.
    fn test_zero_polynomial() {
        type F = PrimeFieldElement64<7>;
        let p = DensePolynomial::<F>::new(&[]);
        assert_eq!(p.coefficients, [F::zero()])
    }

    #[test]
    #[ignore]
    // Should produce the lowest-degree polynomial with the given zeros.
    fn test_from_zeros() {
        todo!()
    }

    #[test]
    fn test_rand() {
        type F = PrimeFieldElement64<13>;
        let mut rng = StdRng::seed_from_u64(0);
        for d in 0..73 {
            let poly = DensePolynomial::<F>::rand(d, &mut rng);
            assert_eq!(poly.coefficients.len(), (d + 1) as usize);
            assert_ne!(*poly.coefficients.last().unwrap(), F::zero()) // leading coefficient is non-zero.
        }
    }

    #[test]
    fn test_eval() {
        // 1 + 2x + 3x^2 + 4x^3
        let coefficients = get_elements(vec![1, 2, 3, 4]);
        let poly = DensePolynomial::new(&coefficients);

        // a(0) = 1
        assert_eq!(
            poly.eval(&PrimeFieldElement64::new(0)),
            PrimeFieldElement64::new(1)
        );

        // a(3) = 1 + 6 + 27 + 108 mod 13 = 12
        assert_eq!(
            poly.eval(&PrimeFieldElement64::new(3)),
            PrimeFieldElement64::new(12)
        );

        // a(8) = (1 + 2*8 + 3*8^2 + 4 * 8^3) mod 13 = 8
        assert_eq!(
            poly.eval(&PrimeFieldElement64::new(8)),
            PrimeFieldElement64::new(8)
        );
    }

    #[test]
    fn test_scale_spot_check() {
        type F = PrimeFieldElement64<541>;
        let c = F::new(5);
        let p = DensePolynomial::new(&[F::new(3), F::zero(), F::new(16), F::new(44)]);

        let expected = DensePolynomial::new(&[F::new(15), F::zero(), F::new(80), F::new(220)]);
        assert_eq!(p * c, expected)
    }

    #[test]
    fn test_shift_by_zero() {
        type F = PrimeFieldElement64<541>;
        type P = DensePolynomial<F>;
        let p = P::try_from("3 + 16x^2 + 44x^3").unwrap();
        let shifted = p.shift(&F::zero());
        // p(x + 0) = p(x)
        assert_eq!(p, shifted);
    }

    #[test]
    // Should symbolically compute p^n.
    fn test_pow_spot_check() {
        type F = PrimeFieldElement64<541>;
        type P = DensePolynomial<F>;

        // 3 + 16x^2 + 44x^3
        let p = P::try_from("3 + 16x^2 + 44x^3").unwrap();

        // p^0 = 1
        assert_eq!(p.pow(0), DensePolynomial::<F>::one());

        // p^1 = p
        assert_eq!(p.pow(1), p);

        // sage: sage.misc.banner.version()
        // 'SageMath version 9.5, Release Date: 2022-01-30'
        //
        // sage: R.<x>=GF(541)[]
        // sage: p = 3 + 16*x^2 + 44*x^3
        // sage: p^2
        // 313*x^6 + 326*x^5 + 256*x^4 + 264*x^3 + 96*x^2 + 9
        // sage: p^3
        // 247*x^9 + 417*x^8 + 250*x^7 + 421*x^6 + 229*x^5 + 140*x^4 + 106*x^3 + 432*x^2 + 27

        let p2 = P::try_from("313*x^6 + 326*x^5 + 256*x^4 + 264*x^3 + 96*x^2 + 9").unwrap();

        assert_eq!(p.pow(2), p2);

        let p3 = P::try_from(
            "247*x^9 + 417*x^8 + 250*x^7 + 421*x^6 + 229*x^5 + 140*x^4 + 106*x^3 + 432*x^2 + 27",
        )
        .unwrap();

        assert_eq!(p.pow(3), p3);
    }

    #[test]
    // Should symbolically compute f(g(x)).
    fn test_compose() {
        type F = PrimeFieldElement64<541>;
        type P = DensePolynomial<F>;

        let f = P::try_from("x^2").unwrap();
        let g = P::try_from("9 + 2x + x^3").unwrap();

        // Composing the zero polynomial with anything gives the zero polynomial.
        assert_eq!(P::zero().compose(&f), P::zero());
        assert_eq!(P::zero().compose(&g), P::zero());

        // Composing a polynomial with the zero polynomial yields a constant or zero.
        assert_eq!(f.compose(&P::zero()), P::zero());
        assert_eq!(g.compose(&P::zero()), P::try_from("9").unwrap());

        // Composing the one polynomial with anything gives the one polynomial.
        assert_eq!(P::one().compose(&f), P::one());
        assert_eq!(P::one().compose(&g), P::one());

        // Composing anything with the one polynomial gives the sum of coefficients.
        assert_eq!(f.compose(&P::one()), P::lift(&F::new(1)));
        assert_eq!(g.compose(&P::one()), P::lift(&F::new(12)));

        // sage: sage.misc.banner.version()
        // 'SageMath version 9.5, Release Date: 2022-01-30'
        //
        // sage: R.<x>=GF(541)[]
        // sage: f = x^2
        // sage: g =  9 + 2*x + x^3
        // sage: f(g)
        // x^6 + 4*x^4 + 18*x^3 + 4*x^2 + 36*x + 81
        // sage: g(f)
        // x^6 + 2*x^2 + 9

        // f(g(x))
        assert_eq!(
            f.compose(&g),
            P::try_from("x^6 + 4x^4 + 18x^3 + 4x^2 + 36x + 81").unwrap()
        );

        // g(f(x))
        assert_eq!(g.compose(&f), P::try_from("x^6 + 2x^2 + 9").unwrap())
    }

    // Serializing then deserializing should yield the same polynomial.
    fn serialize_then_deserialize<F: FiniteField>(p: DensePolynomial<F>) {
        let bytes = bincode::serialize(&p).unwrap();
        let recovered: DensePolynomial<F> = bincode::deserialize(&bytes).unwrap();
        assert_eq!(p, recovered);
    }

    proptest! {
        #[test]
        fn test_ser_de(poly in ((0..=100usize).prop_flat_map(|d| any_with::<DensePolynomial<Zp541>>(d)))) {
            serialize_then_deserialize(poly);
        }
    }

    #[test]
    // Display / to_string() should produce a Sage-friendly string.
    fn test_display() {
        type F = PrimeFieldElement64<541>;
        type P = DensePolynomial<F>;

        assert_eq!(P::try_from("0").unwrap().to_string(), "0");
        assert_eq!(P::try_from("1").unwrap().to_string(), "1");
        assert_eq!(P::try_from("33").unwrap().to_string(), "33");

        assert_eq!(P::try_from("x").unwrap().to_string(), "x");
        assert_eq!(P::try_from("x^2").unwrap().to_string(), "x^2");
        assert_eq!(P::try_from("y^3").unwrap().to_string(), "x^3");

        assert_eq!(P::try_from("3*x").unwrap().to_string(), "3*x");
        assert_eq!(P::try_from("11*x^2").unwrap().to_string(), "11*x^2");
        // The display variable is always "x"
        assert_eq!(P::try_from("5*y^3").unwrap().to_string(), "5*x^3");

        assert_eq!(P::try_from("1+3*x").unwrap().to_string(), "1 + 3*x");
        assert_eq!(P::try_from("x+11*x^2").unwrap().to_string(), "x + 11*x^2");
        assert_eq!(
            P::try_from("9 + x + 2*x^2 + 5*y^3").unwrap().to_string(),
            "9 + x + 2*x^2 + 5*x^3"
        );
    }
}
