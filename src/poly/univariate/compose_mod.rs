//! Modular composition, `f(g) mod h`.
//!
//! Brent–Kung baby-step/giant-step: with `m ≈ sqrt(deg h)`, write `f = Σ_j F_j(x) · x^{mj}` with
//! every `F_j` of degree below `m`. The baby steps `1, g, …, g^{m-1} mod h` are the rows of an
//! `m × n` matrix, the coefficients of the `F_j` are the rows of a `k × m` matrix, and one matrix
//! product evaluates every `F_j(g) mod h` at once. Horner in `g^m` then joins the `k` blocks. That
//! trades `deg f` modular multiplications for about `2·sqrt(n)` of them plus one dense `k × m × n`
//! matrix product, which is what makes it the inner step of a Frobenius iteration
//! `x^{q^{d+1}} = x^{q^d} ∘ x^q mod h`: one composition instead of `log2 q` modular squarings.
//!
//! The inner argument is fixed across a Frobenius iteration, so [`ModularComposer`] keeps the baby
//! steps and pays for them once.
//!
//! # References
//! * R. P. Brent and H. T. Kung, *Fast algorithms for manipulating formal power series*, J. ACM 25
//!   (1978), Algorithm 2.1.
//! * von zur Gathen and Gerhard, *Modern Computer Algebra*, §12.2.

use crate::{
    linalg::Matrix,
    poly::univariate::{Polynomial, UnivariatePolynomial},
    FiniteField,
};

/// `f(g) mod h`, by Brent–Kung.
///
/// # Panics
/// Panics if `h` is the zero polynomial.
pub fn compose_mod<F: FiniteField>(
    f: &UnivariatePolynomial<F>,
    g: &UnivariatePolynomial<F>,
    h: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    // sqrt(deg f + 1) balances the baby steps against the giant steps for this one f; the matrix
    // product costs (deg f + 1) · deg h multiply-adds whatever the block.
    ModularComposer::with_block(g, h, block_for(f.coefficients().len())).compose(f)
}

/// `f(g) mod h`, by Horner's rule reducing after every step.
///
/// `deg f` modular multiplications. The reference [`compose_mod`] is checked against, and the
/// cheaper of the two when `f` is short.
///
/// # Panics
/// Panics if `h` is the zero polynomial.
pub fn compose_mod_horner<F: FiniteField>(
    f: &UnivariatePolynomial<F>,
    g: &UnivariatePolynomial<F>,
    h: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    assert_nonzero(h);
    let g = g % h;
    let mut result = UnivariatePolynomial::zero();
    for c in f.coefficients().iter().rev() {
        result = &(&(&result * &g) + &UnivariatePolynomial::new(&[*c])) % h;
    }
    result
}

/// Brent–Kung composition with a fixed inner argument `g` and modulus `h`.
///
/// Construction costs `m` modular multiplications for `m = ceil(sqrt(deg h))`. Each
/// [`compose`](Self::compose) then costs one `k × m` by `m × deg h` matrix product and `k − 1`
/// modular multiplications, for `k = ceil((deg f + 1) / m)`.
#[derive(Clone, Debug)]
pub struct ModularComposer<F: FiniteField> {
    modulus: UnivariatePolynomial<F>,
    /// Row `i` is `g^i mod h`, padded to `deg h` coefficients.
    baby_steps: Matrix<F>,
    /// `g^m mod h`.
    giant_step: UnivariatePolynomial<F>,
}

impl<F: FiniteField> ModularComposer<F> {
    /// Precompute the baby steps of `g` modulo `h`.
    ///
    /// # Panics
    /// Panics if `h` is the zero polynomial.
    pub fn new(g: &UnivariatePolynomial<F>, h: &UnivariatePolynomial<F>) -> Self {
        assert_nonzero(h);
        Self::with_block(g, h, block_for(h.degree() as usize))
    }

    fn with_block(g: &UnivariatePolynomial<F>, h: &UnivariatePolynomial<F>, block: usize) -> Self {
        assert_nonzero(h);
        let n = h.degree() as usize;
        let g = g % h;

        // Reducing 1 matters only when h is a constant, where F[x]/(h) is the zero ring.
        let mut power = &UnivariatePolynomial::one() % h;
        let mut elements = Vec::with_capacity(block * n);
        for _ in 0..block {
            push_padded(&mut elements, &power, n);
            power = &(&power * &g) % h;
        }
        Self {
            modulus: h.clone(),
            baby_steps: Matrix::new(block, n, &elements),
            giant_step: power,
        }
    }

    /// The modulus `h`.
    pub fn modulus(&self) -> &UnivariatePolynomial<F> {
        &self.modulus
    }

    /// `f(g) mod h`.
    pub fn compose(&self, f: &UnivariatePolynomial<F>) -> UnivariatePolynomial<F> {
        let n = self.baby_steps.num_columns();
        if f.is_zero() || n == 0 {
            return UnivariatePolynomial::zero();
        }
        let block = self.baby_steps.num_rows();
        let coefficients = f.coefficients();
        let blocks = coefficients.len().div_ceil(block);

        let mut chunks = Vec::with_capacity(blocks * block);
        for j in 0..blocks {
            let end = ((j + 1) * block).min(coefficients.len());
            chunks.extend_from_slice(&coefficients[j * block..end]);
            chunks.resize((j + 1) * block, F::ZERO);
        }
        // Row j of the product is F_j(g) mod h, every block evaluated by one matrix product.
        let evaluated = &Matrix::new(blocks, block, &chunks) * &self.baby_steps;
        let row = |j: usize| UnivariatePolynomial::new(&evaluated.elements()[j * n..(j + 1) * n]);

        let mut result = row(blocks - 1);
        for j in (0..blocks - 1).rev() {
            result = &(&(&result * &self.giant_step) % &self.modulus) + &row(j);
        }
        result
    }
}

/// `ceil(sqrt(len))`, at least one.
fn block_for(len: usize) -> usize {
    let mut m = (len as f64).sqrt() as usize;
    while m * m < len {
        m += 1;
    }
    m.max(1)
}

fn push_padded<F: FiniteField>(out: &mut Vec<F>, p: &UnivariatePolynomial<F>, n: usize) {
    let start = out.len();
    if !p.is_zero() {
        out.extend_from_slice(p.coefficients());
    }
    out.resize(start + n, F::ZERO);
}

fn assert_nonzero<F: FiniteField>(h: &UnivariatePolynomial<F>) {
    assert!(!h.is_zero(), "the modulus must be a nonzero polynomial");
}

#[cfg(test)]
mod tests {
    use rand::{rngs::StdRng, SeedableRng};

    use super::{compose_mod, compose_mod_horner, ModularComposer};
    use crate::{
        fields::{Bn254Fr, Gf13Pow4, Gf256, KoalaBear, Zp18446744069414584321, Zp7},
        poly::univariate::{pow_mod, Polynomial, UnivariatePolynomial},
        FiniteField, KnownOrder,
    };

    fn poly<F: FiniteField>(coefficients: &[u64]) -> UnivariatePolynomial<F> {
        UnivariatePolynomial::new(&coefficients.iter().map(|c| F::new(*c)).collect::<Vec<_>>())
    }

    fn random<F: FiniteField>(degree: u64, rng: &mut StdRng) -> UnivariatePolynomial<F> {
        UnivariatePolynomial::rand(degree, rng)
    }

    /// `f(g) mod h` with no reduction until the end, sharing no code with either route.
    fn unreduced<F: FiniteField>(
        f: &UnivariatePolynomial<F>,
        g: &UnivariatePolynomial<F>,
        h: &UnivariatePolynomial<F>,
    ) -> UnivariatePolynomial<F> {
        let mut sum = UnivariatePolynomial::zero();
        for (i, c) in f.coefficients().iter().enumerate() {
            sum = &sum + &g.pow(i as u32).scale(c);
        }
        &sum % h
    }

    /// Brent–Kung and Horner agree on random operands of every relative size over one field.
    fn check_routes_agree<F: FiniteField>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        for h_degree in [1u64, 2, 3, 5, 8, 17, 40] {
            let h = random::<F>(h_degree, &mut rng);
            for f_degree in [0u64, 1, 2, 7, h_degree, 2 * h_degree + 3] {
                for g_degree in [0u64, 1, h_degree.saturating_sub(1), h_degree, h_degree + 4] {
                    let f = random::<F>(f_degree, &mut rng);
                    let g = random::<F>(g_degree, &mut rng);
                    assert_eq!(
                        compose_mod(&f, &g, &h),
                        compose_mod_horner(&f, &g, &h),
                        "deg f {f_degree} deg g {g_degree} deg h {h_degree}"
                    );
                }
            }
        }
    }

    /// Horner agrees with composing outright and reducing once, on sizes where that is cheap.
    #[test]
    fn test_horner_agrees_with_unreduced_composition() {
        let mut rng = StdRng::seed_from_u64(1);
        for _ in 0..40 {
            let h = random::<Zp7>(4, &mut rng);
            let f = random::<Zp7>(6, &mut rng);
            let g = random::<Zp7>(5, &mut rng);
            assert_eq!(compose_mod_horner(&f, &g, &h), unreduced(&f, &g, &h));
        }
    }

    /// Brent–Kung agrees with Horner over a narrow prime field.
    #[test]
    fn test_compose_mod_agrees_with_horner_narrow() {
        check_routes_agree::<Zp7>(2);
        check_routes_agree::<KoalaBear>(3);
    }

    /// Brent–Kung agrees with Horner over a 64-bit prime field.
    #[test]
    fn test_compose_mod_agrees_with_horner_64_bit() {
        check_routes_agree::<Zp18446744069414584321>(4);
    }

    /// Brent–Kung agrees with Horner over a 254-bit prime field.
    #[test]
    fn test_compose_mod_agrees_with_horner_wide() {
        check_routes_agree::<Bn254Fr>(5);
    }

    /// Brent–Kung agrees with Horner over extension fields of odd and even characteristic.
    #[test]
    fn test_compose_mod_agrees_with_horner_extension_fields() {
        check_routes_agree::<Gf256>(6);
        check_routes_agree::<Gf13Pow4>(7);
    }

    /// A constant `f` composes to itself, and the zero `f` to zero.
    #[test]
    fn test_constant_and_zero_outer_polynomial() {
        let g = poly::<KoalaBear>(&[3, 1, 4, 1, 5]);
        let h = poly::<KoalaBear>(&[2, 7, 1, 8]);
        let c = poly::<KoalaBear>(&[9]);
        assert_eq!(compose_mod(&c, &g, &h), c);
        let zero = UnivariatePolynomial::<KoalaBear>::zero();
        assert_eq!(compose_mod(&zero, &g, &h), zero);
        assert_eq!(compose_mod_horner(&zero, &g, &h), zero);
    }

    /// A constant `g` evaluates `f` there, and the zero `g` leaves the constant term.
    #[test]
    fn test_constant_and_zero_inner_polynomial() {
        let f = poly::<KoalaBear>(&[1, 2, 3, 4]);
        let h = poly::<KoalaBear>(&[5, 0, 0, 1]);
        let g = poly::<KoalaBear>(&[6]);
        let value = f.eval(&KoalaBear::new(6));
        assert_eq!(compose_mod(&f, &g, &h), UnivariatePolynomial::new(&[value]));
        let zero = UnivariatePolynomial::<KoalaBear>::zero();
        assert_eq!(compose_mod(&f, &zero, &h), poly::<KoalaBear>(&[1]));
    }

    /// An inner argument of degree at least `deg h` gives the same result as its reduction.
    #[test]
    fn test_inner_argument_is_reduced_first() {
        let mut rng = StdRng::seed_from_u64(8);
        let h = random::<KoalaBear>(9, &mut rng);
        let f = random::<KoalaBear>(20, &mut rng);
        let g = random::<KoalaBear>(30, &mut rng);
        assert_eq!(compose_mod(&f, &g, &h), compose_mod(&f, &(&g % &h), &h));
    }

    /// Modulo a linear `x - r`, the result is the constant `f(g(r))`.
    #[test]
    fn test_linear_modulus_evaluates_at_its_root() {
        let mut rng = StdRng::seed_from_u64(9);
        let r = KoalaBear::new(12345);
        let h = UnivariatePolynomial::new(&[KoalaBear::new(0) - r, KoalaBear::new(1)]);
        let f = random::<KoalaBear>(11, &mut rng);
        let g = random::<KoalaBear>(6, &mut rng);
        let expected = UnivariatePolynomial::new(&[f.eval(&g.eval(&r))]);
        assert_eq!(compose_mod(&f, &g, &h), expected);
    }

    /// A nonzero constant modulus is the zero ring, where everything is zero.
    #[test]
    fn test_constant_modulus_gives_zero() {
        let f = poly::<KoalaBear>(&[1, 2, 3]);
        let g = poly::<KoalaBear>(&[4, 5]);
        let h = poly::<KoalaBear>(&[7]);
        assert!(compose_mod(&f, &g, &h).is_zero());
        assert!(compose_mod_horner(&f, &g, &h).is_zero());
    }

    /// The zero modulus is rejected rather than divided by.
    #[test]
    #[should_panic(expected = "nonzero")]
    fn test_zero_modulus_panics() {
        let f = poly::<KoalaBear>(&[1, 2]);
        compose_mod(&f, &f, &UnivariatePolynomial::zero());
    }

    /// One composer serves many outer polynomials, each matching a fresh composition.
    #[test]
    fn test_composer_is_reusable() {
        let mut rng = StdRng::seed_from_u64(10);
        let h = random::<Zp18446744069414584321>(50, &mut rng);
        let g = random::<Zp18446744069414584321>(49, &mut rng);
        let composer = ModularComposer::new(&g, &h);
        for f_degree in [0u64, 3, 49, 50, 151] {
            let f = random::<Zp18446744069414584321>(f_degree, &mut rng);
            assert_eq!(composer.compose(&f), compose_mod_horner(&f, &g, &h));
        }
    }

    /// Composing `x^q` with itself is `x^{q^2}`, the identity the Frobenius iteration rests on.
    #[test]
    fn test_frobenius_by_composition_matches_pow_mod() {
        fn check<F: KnownOrder>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            let h = random::<F>(31, &mut rng);
            let x = poly::<F>(&[0, 1]);
            let xq = pow_mod::pow_mod_limbs(&x, F::order_limbs(), &h);
            let xq2 = pow_mod::pow_mod_limbs(&xq, F::order_limbs(), &h);
            assert_eq!(compose_mod(&xq, &xq, &h), xq2);
        }
        check::<KoalaBear>(11);
        check::<Bn254Fr>(12);
        check::<Gf256>(13);
    }
}
