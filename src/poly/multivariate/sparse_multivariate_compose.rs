//! Symbolic composition of a multivariate polynomial with one polynomial per variable.

use std::collections::HashMap;

use crate::{
    poly::{
        multivariate::sparse_multivariate_polynomial::SparseMultiPoly, Polynomial,
        UnivariatePolynomial,
    },
    FiniteField, Monomial,
};

impl<const N: usize, F: FiniteField> SparseMultiPoly<N, F> {
    /// The univariate polynomial `p`, read as a polynomial in variable `index` alone.
    ///
    /// # Panics
    /// Panics if `index` is not a variable of this ring.
    pub fn from_univariate(index: usize, p: &UnivariatePolynomial<F>) -> Self {
        assert!(
            index < N,
            "index {} is not one of the {} variables",
            index,
            N
        );
        let terms: Vec<(Monomial<N>, F)> = p
            .coefficients()
            .iter()
            .enumerate()
            .map(|(exponent, c)| (Monomial::univariate(index, exponent as u32), *c))
            .collect();
        // Through `new`, which drops the zero coefficients a dense representation carries.
        Self::new(&terms)
    }

    /// Substitute `substitutions[i]` for `x_i`, in every variable simultaneously.
    ///
    /// The general composition: each variable may be replaced by a polynomial in all N variables,
    /// so this is substitution into the ring rather than a change of one coordinate. Simultaneous,
    /// not sequential — `substitutions[i]`'s own occurrences of `x_j` are not themselves
    /// substituted.
    pub fn compose(&self, substitutions: &[Self; N]) -> Self {
        let mut powers: Vec<PowerTable<N, F>> = substitutions.iter().map(PowerTable::new).collect();

        let mut composed = Self::zero();
        for (monomial, coefficient) in self.terms.iter() {
            // The coefficient is nonzero by the canonical invariant, so this is never the zero
            // polynomial and the product below starts from a real term.
            let mut product = Self::from(*coefficient);
            for (i, exponent) in monomial.exponents().iter().enumerate() {
                if *exponent == 0 {
                    continue;
                }
                // A substitution can be the zero polynomial, or a product can cancel entirely;
                // multiplying further factors into it cannot bring it back.
                if product.is_zero() {
                    break;
                }
                product = &product * powers[i].power(*exponent);
            }
            composed += product;
        }
        composed
    }

    /// Substitute `substitutions[i](x_i)` for `x_i`.
    ///
    /// The case the callers want: a Poseidon round is an S-box `x -> x^d` per state word followed
    /// by an affine layer, which is exactly a multivariate polynomial composed with one univariate
    /// polynomial per variable. Each `x_i` is replaced by a polynomial in `x_i` alone, so unlike
    /// [`Self::compose`] no variable can leak into another's image.
    pub fn compose_univariate(&self, substitutions: &[UnivariatePolynomial<F>; N]) -> Self {
        let lifted: [Self; N] =
            std::array::from_fn(|i| Self::from_univariate(i, &substitutions[i]));
        self.compose(&lifted)
    }
}

/// Powers of one substituted polynomial, computed on demand and shared across terms.
///
/// A monomial needs `substitutions[i]^(e_i)`, and composition's cost is dominated by forming those
/// powers: degree grows multiplicatively, so a single power can be larger than the whole input.
/// Exponents repeat across a polynomial's terms — every term of a homogeneous polynomial in one
/// variable shares one — so the powers are memoized by exponent and built by repeated squaring.
/// A distinct exponent `e` then costs O(log e) multiplications rather than `e - 1`, and a repeated
/// one costs none.
struct PowerTable<'a, const N: usize, F: FiniteField> {
    base: &'a SparseMultiPoly<N, F>,
    powers: HashMap<u32, SparseMultiPoly<N, F>>,
}

impl<'a, const N: usize, F: FiniteField> PowerTable<'a, N, F> {
    fn new(base: &'a SparseMultiPoly<N, F>) -> Self {
        Self {
            base,
            powers: HashMap::new(),
        }
    }

    /// `base^exponent`, computing and storing it if it is not already known.
    fn power(&mut self, exponent: u32) -> &SparseMultiPoly<N, F> {
        if !self.powers.contains_key(&exponent) {
            let value = match exponent {
                0 => SparseMultiPoly::one(),
                1 => self.base.clone(),
                e => {
                    // Cloned so that the recursive borrow of `self` ends before the insert below.
                    let half = self.power(e / 2).clone();
                    let squared = &half * &half;
                    if e % 2 == 0 {
                        squared
                    } else {
                        &squared * self.base
                    }
                }
            };
            self.powers.insert(exponent, value);
        }
        &self.powers[&exponent]
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::Zp13,
        poly::{
            multivariate::sparse_multivariate_polynomial::SparseMultiPoly, Polynomial,
            UnivariatePolynomial,
        },
        FiniteField, Monomial, Zero,
    };

    type F = Zp13;

    /// `compose_univariate` agrees with substituting each `g_i` by hand and expanding.
    #[test]
    fn test_compose_univariate_matches_hand_expansion() {
        let vars = ["x", "y"];
        // p = x^2*y + 3x + 2, with x -> x + 1 and y -> y^2.
        let p: SparseMultiPoly<2, F> = SparseMultiPoly::parse("x^2*y + 3*x + 2", vars).unwrap();
        let g0 = UnivariatePolynomial::new(&[F::new(1), F::new(1)]);
        let g1 = UnivariatePolynomial::new(&[F::new(0), F::new(0), F::new(1)]);

        // (x+1)^2*y^2 + 3(x+1) + 2 = x^2*y^2 + 2*x*y^2 + y^2 + 3*x + 5
        let expected: SparseMultiPoly<2, F> =
            SparseMultiPoly::parse("x^2*y^2 + 2*x*y^2 + y^2 + 3*x + 5", vars).unwrap();
        assert_eq!(p.compose_univariate(&[g0, g1]), expected);
    }

    /// Composing with `x_i -> x_i` returns the polynomial unchanged.
    #[test]
    fn test_compose_with_the_identity_is_the_identity() {
        let vars = ["x", "y"];
        let p: SparseMultiPoly<2, F> =
            SparseMultiPoly::parse("4*x^3*y + x*y + 7*y^2 + 11", vars).unwrap();
        let x = UnivariatePolynomial::new(&[F::new(0), F::new(1)]);
        assert_eq!(p.compose_univariate(&[x.clone(), x.clone()]), p);

        // And the same substitution written as multivariate polynomials.
        let identity: [SparseMultiPoly<2, F>; 2] = [
            SparseMultiPoly::from(Monomial::univariate(0, 1)),
            SparseMultiPoly::from(Monomial::univariate(1, 1)),
        ];
        assert_eq!(p.compose(&identity), p);
    }

    /// Composing with constants collapses to the polynomial's value at those constants.
    #[test]
    fn test_compose_with_constants_collapses_to_evaluation() {
        let vars = ["x", "y"];
        let p: SparseMultiPoly<2, F> =
            SparseMultiPoly::parse("x^2*y + 3*x*y^2 + 2*y + 5", vars).unwrap();
        let (a, b) = (F::new(4), F::new(9));
        let composed = p.compose_univariate(&[
            UnivariatePolynomial::new(&[a]),
            UnivariatePolynomial::new(&[b]),
        ]);

        assert!(composed.is_constant());
        assert_eq!(composed.eval(&[F::zero(), F::zero()]), p.eval(&[a, b]));
    }

    /// A constant substitution for one variable only agrees with `substitute`.
    #[test]
    fn test_compose_agrees_with_substitute_on_one_variable() {
        let vars = ["x", "y"];
        let p: SparseMultiPoly<2, F> =
            SparseMultiPoly::parse("x^2*y + 3*x + 2*y + 5", vars).unwrap();
        let identity_y = UnivariatePolynomial::new(&[F::new(0), F::new(1)]);
        let composed = p.compose_univariate(&[UnivariatePolynomial::new(&[F::new(2)]), identity_y]);
        assert_eq!(composed, p.substitute(0, F::new(2)));
    }

    /// The composed degree is the monomial's exponents weighted by the substituted degrees.
    #[test]
    fn test_compose_degree_is_multiplicative() {
        // p = x^3*y^2, a single monomial, so nothing can cancel.
        let p: SparseMultiPoly<2, F> = SparseMultiPoly::new(&[(Monomial::new(&[3, 2]), F::new(1))]);
        // deg(g0) = 2, deg(g1) = 3, so deg(p(g0, g1)) = 3*2 + 2*3 = 12.
        let g0 = UnivariatePolynomial::new(&[F::new(1), F::new(1), F::new(1)]);
        let g1 = UnivariatePolynomial::new(&[F::new(0), F::new(1), F::new(0), F::new(1)]);
        assert_eq!(p.compose_univariate(&[g0, g1]).degree(), 12);
    }

    /// Terms that cancel during composition are dropped, not kept with a zero coefficient.
    #[test]
    fn test_compose_drops_cancelled_terms() {
        let vars = ["x", "y"];
        // (x - 1)^2 + (x - 1) = x^2 - x: the constant term cancels.
        let p: SparseMultiPoly<2, F> = SparseMultiPoly::parse("x^2 + x", vars).unwrap();
        let shifted = UnivariatePolynomial::new(&[F::new(12), F::new(1)]);
        let identity_y = UnivariatePolynomial::new(&[F::new(0), F::new(1)]);
        let composed = p.compose_univariate(&[shifted, identity_y.clone()]);

        let expected: SparseMultiPoly<2, F> = SparseMultiPoly::parse("x^2 - x", vars).unwrap();
        assert_eq!(composed, expected);
        assert_eq!(composed.terms().len(), 2);
        assert!(composed.terms().values().all(|c| !c.is_zero()));

        // Everything can cancel: x^2 - x at x = 1 is 0, and the zero polynomial holds no terms.
        let q: SparseMultiPoly<2, F> = SparseMultiPoly::parse("x^2 - x", vars).unwrap();
        let one = UnivariatePolynomial::new(&[F::new(1)]);
        let collapsed = q.compose_univariate(&[one, identity_y]);
        assert!(collapsed.is_zero(), "expected zero, got {}", collapsed);
        assert!(collapsed.terms().is_empty());
    }

    /// Cross-variable cancellation under a general substitution is also canonical.
    #[test]
    fn test_compose_multivariate_cancellation_is_canonical() {
        let vars = ["x", "y"];
        // (x_0 - x_1) with both variables sent to x_0 is the zero polynomial.
        let p: SparseMultiPoly<2, F> = SparseMultiPoly::parse("x - y", vars).unwrap();
        let x0: SparseMultiPoly<2, F> = SparseMultiPoly::from(Monomial::univariate(0, 1));
        let composed = p.compose(&[x0.clone(), x0]);
        assert!(composed.is_zero(), "expected zero, got {}", composed);
        assert!(composed.terms().is_empty());
    }

    /// A general multivariate substitution expands as the ring operations would.
    #[test]
    fn test_compose_general_multivariate_matches_hand_expansion() {
        let vars = ["x", "y"];
        // x*y with x -> x + y and y -> x - y is x^2 - y^2.
        let p: SparseMultiPoly<2, F> = SparseMultiPoly::parse("x*y", vars).unwrap();
        let sum: SparseMultiPoly<2, F> = SparseMultiPoly::parse("x + y", vars).unwrap();
        let difference: SparseMultiPoly<2, F> = SparseMultiPoly::parse("x - y", vars).unwrap();
        let expected: SparseMultiPoly<2, F> = SparseMultiPoly::parse("x^2 - y^2", vars).unwrap();
        assert_eq!(p.compose(&[sum, difference]), expected);
    }

    /// Composing the zero polynomial gives zero, whatever is substituted.
    #[test]
    fn test_compose_of_the_zero_polynomial_is_zero() {
        let zero: SparseMultiPoly<3, F> = SparseMultiPoly::zero();
        let g = UnivariatePolynomial::new(&[F::new(5), F::new(7)]);
        let composed = zero.compose_univariate(&[g.clone(), g.clone(), g]);
        assert!(composed.is_zero());
        assert!(composed.terms().is_empty());
    }

    /// Substituting the zero polynomial for a variable kills every term that used it.
    #[test]
    fn test_compose_with_zero_substitution() {
        let vars = ["x", "y"];
        let p: SparseMultiPoly<2, F> = SparseMultiPoly::parse("x*y + y + 3", vars).unwrap();
        let identity_x = UnivariatePolynomial::new(&[F::new(0), F::new(1)]);
        let composed = p.compose_univariate(&[identity_x, UnivariatePolynomial::zero()]);
        let expected: SparseMultiPoly<2, F> = SparseMultiPoly::from(F::new(3));
        assert_eq!(composed, expected);
    }

    /// `from_univariate` places a univariate polynomial's coefficients on one variable.
    #[test]
    fn test_from_univariate() {
        let vars = ["x", "y"];
        // 2*t^3 + t + 5 on variable 1.
        let g = UnivariatePolynomial::new(&[F::new(5), F::new(1), F::new(0), F::new(2)]);
        let lifted: SparseMultiPoly<2, F> = SparseMultiPoly::from_univariate(1, &g);
        let expected: SparseMultiPoly<2, F> =
            SparseMultiPoly::parse("2*y^3 + y + 5", vars).unwrap();
        assert_eq!(lifted, expected);

        // The zero polynomial lifts to the zero polynomial, with no terms.
        let zero: SparseMultiPoly<2, F> =
            SparseMultiPoly::from_univariate(0, &UnivariatePolynomial::zero());
        assert!(zero.terms().is_empty());
    }

    mod over_every_field {
        use crate::{
            poly::{
                multivariate::sparse_multivariate_polynomial::SparseMultiPoly, Polynomial,
                UnivariatePolynomial,
            },
            FiniteField, Monomial,
        };
        use rand::{prelude::StdRng, Rng, SeedableRng};

        /// A polynomial with `num_terms` drawn monomials of small exponent and drawn coefficients.
        ///
        /// Written out rather than reached through `Arbitrary`, whose strategy is boxed and so
        /// requires `F: 'static` — a bound the generic body `for_each_field!` writes cannot state.
        fn random_poly<const N: usize, F: FiniteField, R: Rng + rand::CryptoRng>(
            num_terms: usize,
            rng: &mut R,
        ) -> SparseMultiPoly<N, F> {
            let terms: Vec<(Monomial<N>, F)> = (0..num_terms)
                .map(|_| {
                    let mut exponents = [0u32; N];
                    for e in exponents.iter_mut() {
                        *e = rng.gen_range(0..4);
                    }
                    (Monomial::new(&exponents), F::random(rng))
                })
                .collect();
            SparseMultiPoly::new(&terms)
        }

        /// Composition agrees with evaluating the substitutions first, at drawn points.
        pub(super) fn assert_compose_agrees_with_evaluation<const N: usize, F: FiniteField>() {
            let mut rng = StdRng::seed_from_u64(0xc0c0_05e1);
            for _ in 0..16 {
                let p = random_poly::<N, F, _>(5, &mut rng);
                let substitutions: [UnivariatePolynomial<F>; N] =
                    std::array::from_fn(|_| UnivariatePolynomial::rand(2, &mut rng));
                let composed = p.compose_univariate(&substitutions);

                // No operation may leave a zero coefficient in the map.
                assert!(
                    composed.terms().values().all(|c| !c.is_zero()),
                    "composition retained a zero coefficient"
                );

                for _ in 0..8 {
                    let point: [F; N] = std::array::from_fn(|_| F::random(&mut rng));
                    let substituted: Vec<F> = substitutions
                        .iter()
                        .zip(point.iter())
                        .map(|(g, x)| g.eval(x))
                        .collect();
                    assert_eq!(
                        composed.eval(&point),
                        p.eval(&substituted),
                        "p = {}, composed = {}",
                        p,
                        composed
                    );
                }
            }
        }

        /// The general composition agrees with evaluating the substitutions first.
        pub(super) fn assert_multivariate_compose_agrees_with_evaluation<
            const N: usize,
            F: FiniteField,
        >() {
            let mut rng = StdRng::seed_from_u64(0x9e11_7a4d);
            for _ in 0..16 {
                let p = random_poly::<N, F, _>(5, &mut rng);
                let substitutions: [SparseMultiPoly<N, F>; N] =
                    std::array::from_fn(|_| random_poly::<N, F, _>(3, &mut rng));
                let composed = p.compose(&substitutions);
                assert!(
                    composed.terms().values().all(|c| !c.is_zero()),
                    "composition retained a zero coefficient"
                );

                for _ in 0..8 {
                    let point: [F; N] = std::array::from_fn(|_| F::random(&mut rng));
                    let substituted: Vec<F> =
                        substitutions.iter().map(|g| g.eval(&point)).collect();
                    assert_eq!(composed.eval(&point), p.eval(&substituted));
                }
            }
        }

        /// Composing with the identity is the identity, and with constants is evaluation.
        pub(super) fn assert_compose_endpoints<const N: usize, F: FiniteField>() {
            let mut rng = StdRng::seed_from_u64(0x1de7_1147);
            let identity: [UnivariatePolynomial<F>; N] =
                std::array::from_fn(|_| UnivariatePolynomial::new(&[F::zero(), F::one()]));
            for _ in 0..16 {
                let p = random_poly::<N, F, _>(5, &mut rng);
                assert_eq!(p.compose_univariate(&identity), p);

                let constants: [F; N] = std::array::from_fn(|_| F::random(&mut rng));
                let lifted: [UnivariatePolynomial<F>; N] =
                    std::array::from_fn(|i| UnivariatePolynomial::new(&[constants[i]]));
                let collapsed = p.compose_univariate(&lifted);
                assert!(collapsed.is_constant());
                assert_eq!(collapsed.eval(&constants), p.eval(&constants));
            }
        }
    }

    // Univariate composition agrees with evaluating the substitutions first, over every field.
    for_each_field!(
        fn univariate_composition_agrees_with_evaluation<F>() {
            over_every_field::assert_compose_agrees_with_evaluation::<1, F>();
            over_every_field::assert_compose_agrees_with_evaluation::<2, F>();
            over_every_field::assert_compose_agrees_with_evaluation::<3, F>();
        }
    );

    // General composition agrees with evaluating the substitutions first, over every field.
    for_each_field!(
        fn multivariate_composition_agrees_with_evaluation<F>() {
            over_every_field::assert_multivariate_compose_agrees_with_evaluation::<2, F>();
            over_every_field::assert_multivariate_compose_agrees_with_evaluation::<3, F>();
        }
    );

    // The identity and constant substitutions behave, over every field.
    for_each_field!(
        fn composition_endpoints_hold<F>() {
            over_every_field::assert_compose_endpoints::<1, F>();
            over_every_field::assert_compose_endpoints::<2, F>();
            over_every_field::assert_compose_endpoints::<3, F>();
        }
    );
}
