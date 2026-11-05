//! A resultant, by Sylvester determinant and interpolation: elimination that is not a Gröbner
//! basis.
//!
//! M23-E's bounded spike. The question is narrow — on **one** small CICO instance, does
//! structure-aware elimination beat general F4, and is the univariate polynomial it produces
//! manageable? — and so is this: two polynomials, two variables, one eliminated.
//!
//! # Why the determinant and not a Euclidean algorithm
//!
//! `Res_y(f, g)` is `det Syl(f, g)`, a determinant of a matrix whose entries are polynomials in
//! the surviving variable. Evaluating that matrix at a point and taking a scalar determinant
//! commutes with evaluation **always**, because a determinant is a polynomial in the entries. So
//! the resultant is recovered by interpolating scalar determinants, and the construction needs no
//! case analysis.
//!
//! A subresultant or Euclidean approach would be asymptotically better and would need exactly the
//! case analysis this avoids: specializing `f` at a point where its leading coefficient in `y`
//! vanishes drops its degree, and the specialized resultant is then **not** the specialization of
//! the resultant. That is the classic trap, and at the sizes M23-E measures — a Sylvester matrix
//! of order at most a few dozen over a 31-bit prime — it buys nothing worth the risk.
//!
//! # What the resultant does and does not give
//!
//! `Res_y(f, g)(a) = 0` is **necessary** for a common root with `x = a`, not sufficient: the
//! resultant vanishes whenever the two specialized polynomials share a root in an *extension*, and
//! it also vanishes when both leading coefficients vanish. So every root of the resultant is a
//! candidate and each candidate must be checked — here, by running the permutation. Nothing in
//! this module decides that a candidate is a solution.

use std::fmt::{Display, Formatter};

use crate::{
    grobner::research::poseidon::{CicoInstance, PoseidonError},
    linalg::Matrix,
    poly::{lagrange_interpolate, Monomial, Polynomial, UnivariatePolynomial},
    FiniteField, KnownOrder, MultivariatePolynomial,
};

/// The constrained output words of a CICO instance, as polynomials in its first two free inputs.
///
/// **This is the elimination.** Every S-box output of a Poseidon permutation is a polynomial in the
/// inputs — the round function is a straight-line program, so there is nothing to solve for, only
/// to evaluate — and fixing all but two free inputs leaves `k` polynomials in two variables. The
/// 46-equation, 46-variable system M23-B measured becomes two polynomials of degree `3^rounds`.
///
/// That is the trade the S-box-per-variable formulation declines to make: it holds every equation
/// at degree `alpha` and pays one variable per S-box, which is the right call when many inputs are
/// free and the wrong one when two are.
///
/// # Errors
/// [`PoseidonError::WrongStateWidth`] unless `fixed` has `t − k − 2` entries, and whatever the
/// permutation reports.
pub fn cico_bivariate<F: KnownOrder>(
    instance: &CicoInstance<F>,
    fixed: &[F],
) -> Result<Vec<MultivariatePolynomial<2, F>>, PoseidonError> {
    let poseidon = &instance.poseidon;
    let t = poseidon.parameters.t;
    let k = instance.k;
    let free = instance.free_inputs();
    if free < 2 || fixed.len() + 2 != free {
        return Err(PoseidonError::WrongStateWidth {
            expected: free.saturating_sub(2),
            found: fixed.len(),
        });
    }

    let constant = |c: F| -> MultivariatePolynomial<2, F> {
        MultivariatePolynomial::new(&[(Monomial::new(&[0, 0]), c)])
    };
    let variable = |index: usize| -> MultivariatePolynomial<2, F> {
        let mut exponents = [0u32; 2];
        exponents[index] = 1;
        MultivariatePolynomial::new(&[(Monomial::new(&exponents), F::one())])
    };
    let power = |p: &MultivariatePolynomial<2, F>, alpha: u32| -> MultivariatePolynomial<2, F> {
        let mut result = p.clone();
        for _ in 1..alpha {
            result = &result * p;
        }
        result
    };
    let mds = |state: &[MultivariatePolynomial<2, F>]| -> Vec<MultivariatePolynomial<2, F>> {
        poseidon
            .mds
            .iter()
            .map(|row| {
                row.iter()
                    .zip(state)
                    .fold(MultivariatePolynomial::zero(), |acc, (m, word)| {
                        acc + word.scale(m)
                    })
            })
            .collect()
    };

    // The input state: the instance's constrained prefix, the two unknowns, then the fixed values.
    let mut state: Vec<MultivariatePolynomial<2, F>> = Vec::with_capacity(t);
    for i in 0..k {
        state.push(constant(instance.constants[i]));
    }
    state.push(variable(0));
    state.push(variable(1));
    for value in fixed {
        state.push(constant(*value));
    }
    debug_assert_eq!(state.len(), t);

    // The CICO verifier applies the MDS before the first round, as `permutation_plus_linear` does.
    state = mds(&state);

    let alpha = poseidon.parameters.alpha;
    let half = poseidon.parameters.r_f / 2;
    let mut round = 0;
    for _ in 0..half {
        add_constants(&mut state, &poseidon.round_constants[round], &constant);
        for word in state.iter_mut() {
            *word = power(word, alpha);
        }
        state = mds(&state);
        round += 1;
    }
    for _ in 0..poseidon.parameters.r_p {
        add_constants(&mut state, &poseidon.round_constants[round], &constant);
        state[0] = power(&state[0], alpha);
        state = mds(&state);
        round += 1;
    }
    for _ in 0..half {
        add_constants(&mut state, &poseidon.round_constants[round], &constant);
        for word in state.iter_mut() {
            *word = power(word, alpha);
        }
        state = mds(&state);
        round += 1;
    }

    // The constrained words, with their targets subtracted: a common root of these is a solution.
    Ok((0..k)
        .map(|i| &state[i] - &constant(instance.constants[k + i]))
        .collect())
}

/// Add one round's constants to a symbolic state.
fn add_constants<F: FiniteField>(
    state: &mut [MultivariatePolynomial<2, F>],
    constants: &[F],
    constant: &impl Fn(F) -> MultivariatePolynomial<2, F>,
) {
    for (word, c) in state.iter_mut().zip(constants) {
        *word = &*word + &constant(*c);
    }
}

/// Why a resultant could not be formed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResultantError {
    /// One of the inputs does not involve the eliminated variable.
    ///
    /// The Sylvester matrix of a polynomial of degree zero in `y` is empty, and the resultant is
    /// then a power of that polynomial rather than anything this function should silently return.
    NoDegreeInEliminatedVariable {
        /// Which argument, 0 or 1.
        argument: usize,
    },

    /// The field is too small to interpolate a polynomial of the resultant's degree bound.
    ///
    /// Interpolation needs `bound + 1` distinct points, so a field with fewer elements cannot
    /// determine the answer. Not a concern for KoalaBear; checked because it is silent if not.
    FieldTooSmall {
        /// Points needed.
        needed: usize,
    },
}

impl Display for ResultantError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoDegreeInEliminatedVariable { argument } => write!(
                f,
                "argument {} has degree zero in the eliminated variable",
                argument
            ),
            Self::FieldTooSmall { needed } => {
                write!(f, "interpolation needs {} distinct points", needed)
            }
        }
    }
}

impl std::error::Error for ResultantError {}

/// `f` as a polynomial in `x_eliminate` with coefficients in `F[x_keep]`.
///
/// Index `i` of the result is the coefficient of `x_eliminate^i`, as a univariate polynomial in
/// `x_keep`. Any term involving a third variable is a programming error here and is rejected by
/// the caller's dimension — this is a bivariate routine.
fn coefficients_in<F: FiniteField>(
    f: &MultivariatePolynomial<2, F>,
    eliminate: usize,
) -> Vec<UnivariatePolynomial<F>> {
    let keep = 1 - eliminate;
    let degree = f
        .terms()
        .keys()
        .map(|monomial| monomial.exponents()[eliminate])
        .max()
        .unwrap_or(0) as usize;

    let mut columns = vec![Vec::<F>::new(); degree + 1];
    for (monomial, coefficient) in f.terms() {
        let exponents = monomial.exponents();
        let power = exponents[eliminate] as usize;
        let other = exponents[keep] as usize;
        let column = &mut columns[power];
        if column.len() <= other {
            column.resize(other + 1, F::zero());
        }
        column[other] += *coefficient;
    }
    columns
        .into_iter()
        .map(|coefficients| {
            if coefficients.is_empty() {
                <UnivariatePolynomial<F> as Polynomial<F>>::zero()
            } else {
                UnivariatePolynomial::new(&coefficients)
            }
        })
        .collect()
}

/// `Res_{x_eliminate}(f, g)`, as a polynomial in the surviving variable.
///
/// Computed as `det Syl(f, g)` by interpolating scalar determinants — see the module docs for why
/// that and not a Euclidean algorithm.
///
/// # Errors
/// [`ResultantError`].
pub fn bivariate_resultant<F: FiniteField>(
    f: &MultivariatePolynomial<2, F>,
    g: &MultivariatePolynomial<2, F>,
    eliminate: usize,
) -> Result<UnivariatePolynomial<F>, ResultantError> {
    let fc = coefficients_in(f, eliminate);
    let gc = coefficients_in(g, eliminate);
    let m = fc.len() - 1;
    let n = gc.len() - 1;
    if m == 0 {
        return Err(ResultantError::NoDegreeInEliminatedVariable { argument: 0 });
    }
    if n == 0 {
        return Err(ResultantError::NoDegreeInEliminatedVariable { argument: 1 });
    }

    // The resultant's degree in the surviving variable is at most `n·deg(f) + m·deg(g)`: the
    // Sylvester matrix has `n` rows of `f`'s coefficients and `m` of `g`'s, and a determinant is a
    // sum of products taking one entry from each row.
    let f_degree = fc.iter().map(|c| c.degree() as usize).max().unwrap_or(0);
    let g_degree = gc.iter().map(|c| c.degree() as usize).max().unwrap_or(0);
    let bound = n * f_degree + m * g_degree;
    let points = bound + 1;

    let mut samples: Vec<(F, F)> = Vec::with_capacity(points);
    for i in 0..points {
        let at = F::new(i as u64);
        // `F::new` is taken modulo the order, so for a field smaller than `points` the sample
        // points would collide and the interpolation would be of the wrong polynomial.
        if i > 0 && at.is_zero() {
            return Err(ResultantError::FieldTooSmall { needed: points });
        }
        samples.push((at, sylvester_determinant(&fc, &gc, at)));
    }
    Ok(lagrange_interpolate(samples))
}

/// `det Syl(f, g)` with the surviving variable set to `at`.
///
/// The Sylvester matrix of `f` of degree `m` and `g` of degree `n` is `(m + n)` square: `n` rows
/// of `f`'s coefficients, each shifted one place right of the last, then `m` rows of `g`'s.
fn sylvester_determinant<F: FiniteField>(
    fc: &[UnivariatePolynomial<F>],
    gc: &[UnivariatePolynomial<F>],
    at: F,
) -> F {
    let m = fc.len() - 1;
    let n = gc.len() - 1;
    let size = m + n;

    // Highest power first, which is the usual layout.
    let f_row: Vec<F> = (0..=m).rev().map(|i| fc[i].eval(&at)).collect();
    let g_row: Vec<F> = (0..=n).rev().map(|i| gc[i].eval(&at)).collect();

    let mut elements = vec![F::zero(); size * size];
    for row in 0..n {
        for (offset, value) in f_row.iter().enumerate() {
            elements[row * size + row + offset] = *value;
        }
    }
    for row in 0..m {
        for (offset, value) in g_row.iter().enumerate() {
            elements[(n + row) * size + row + offset] = *value;
        }
    }
    Matrix::new(size, size, &elements)
        .determinant()
        .expect("a square matrix has a determinant")
}

/// The two polynomials `f` and `g` evaluated at `(keep, eliminate) = (a, b)`.
///
/// A convenience for checking a candidate: the resultant's roots are necessary conditions, so
/// something has to test them.
pub fn evaluate_bivariate<F: FiniteField>(f: &MultivariatePolynomial<2, F>, a: F, b: F) -> F {
    f.eval(&[a, b])
}

#[cfg(test)]
mod tests {
    use super::{bivariate_resultant, cico_bivariate, ResultantError};
    use crate::{
        fields::{PrimeFieldElement64, Zp13},
        poly::{Polynomial, UnivariatePolynomial},
        FiniteField, MultivariatePolynomial, Zero,
    };

    type F = Zp13;
    const VARS: [&str; 2] = ["x", "y"];

    fn parse(text: &str) -> MultivariatePolynomial<2, F> {
        MultivariatePolynomial::parse(text, VARS).expect("a bivariate polynomial")
    }

    /// `Res_y(y - a, y - b) = a - b` up to sign: the textbook case, checked against a hand value.
    ///
    /// With `f = y - x` and `g = y - 2`, eliminating `y` leaves `x - 2` up to sign — the resultant
    /// vanishes exactly where the two share a root.
    #[test]
    fn test_a_linear_pair() {
        let f = parse("y - x");
        let g = parse("y - 2");
        let resultant = bivariate_resultant(&f, &g, 1).expect("both involve y");
        assert_eq!(resultant.degree(), 1);
        // 2 - x or x - 2, depending on the row order; either vanishes only at x = 2.
        assert!(resultant.eval(&F::new(2)).is_zero());
        for other in [0u64, 1, 3, 7, 12] {
            assert!(!resultant.eval(&F::new(other)).is_zero(), "{}", other);
        }
    }

    /// The resultant of a system whose common roots are known vanishes at exactly those roots.
    ///
    /// `f = y^2 - x` and `g = y - x` share roots where `x^2 = x`, i.e. `x ∈ {0, 1}`, so the
    /// resultant must be `x^2 - x` up to a unit — degree 2, vanishing at 0 and 1 and nowhere else.
    #[test]
    fn test_a_quadratic_pair() {
        let f = parse("y^2 - x");
        let g = parse("y - x");
        let resultant = bivariate_resultant(&f, &g, 1).expect("both involve y");
        assert_eq!(resultant.degree(), 2);
        for root in [0u64, 1] {
            assert!(resultant.eval(&F::new(root)).is_zero(), "{}", root);
        }
        for other in 2u64..13 {
            assert!(!resultant.eval(&F::new(other)).is_zero(), "{}", other);
        }
    }

    /// A pair with no common root has a resultant with no root, and it is not the zero polynomial.
    #[test]
    fn test_no_common_root() {
        // y^2 + 1 and y^2 + 2 differ by a constant, so they share no root anywhere.
        let f = parse("y^2 + 1");
        let g = parse("y^2 + 2");
        let resultant = bivariate_resultant(&f, &g, 1).expect("both involve y");
        assert!(
            !resultant.is_zero(),
            "the resultant of a coprime pair is nonzero"
        );
        assert_eq!(resultant.degree(), 0, "there is no x in either input");
        for x in 0u64..13 {
            assert!(!resultant.eval(&F::new(x)).is_zero());
        }
    }

    /// A common factor makes the resultant vanish identically.
    #[test]
    fn test_a_common_factor_gives_the_zero_resultant() {
        let f = parse("y^2 - x^2");
        let g = parse("y^3 - x^2*y");
        // Both are divisible by y - x, so they share a root for *every* x.
        let resultant = bivariate_resultant(&f, &g, 1).expect("both involve y");
        assert!(resultant.is_zero(), "{:?}", resultant);
    }

    /// Eliminating the other variable is a different polynomial, and both are correct.
    #[test]
    fn test_either_variable_can_be_eliminated() {
        let f = parse("x*y - 1");
        let g = parse("x + y - 3");
        // Common roots: x + 1/x = 3, i.e. x^2 - 3x + 1 = 0. Over GF(13) that is x ∈ {4, 12}:
        // 16 - 12 + 1 = 5 ≠ 0 mod 13... so check by substitution instead of by assertion.
        let in_x = bivariate_resultant(&f, &g, 1).expect("both involve y");
        let in_y = bivariate_resultant(&f, &g, 0).expect("both involve x");
        assert_eq!(in_x.degree(), 2);
        assert_eq!(in_y.degree(), 2);
        // The system is symmetric in x and y, so the two eliminations agree up to a unit.
        for at in 0u64..13 {
            let a = in_x.eval(&F::new(at));
            let b = in_y.eval(&F::new(at));
            assert_eq!(a.is_zero(), b.is_zero(), "at {}", at);
        }
        // And every root is a genuine first coordinate: y is then determined by g.
        for at in 0u64..13 {
            let x = F::new(at);
            if in_x.eval(&x).is_zero() {
                let y = F::new(3) - x;
                assert!(
                    f.eval(&[x, y]).is_zero() && g.eval(&[x, y]).is_zero(),
                    "x = {} should extend to a common root",
                    x
                );
            }
        }
    }

    /// Specializing at a point where a leading coefficient vanishes is handled.
    ///
    /// The trap a Euclidean implementation has to special-case: at `x = 0` the leading coefficient
    /// of `f` in `y` vanishes, so `f(0, y)` has lower degree than `f`. The determinant
    /// construction does not care — it evaluates the *matrix*, whose determinant is the resultant
    /// by definition — and the test is that the interpolated polynomial is still right at 0.
    #[test]
    fn test_a_vanishing_leading_coefficient() {
        let f = parse("x*y^2 + y + 1");
        let g = parse("y - x");
        let resultant = bivariate_resultant(&f, &g, 1).expect("both involve y");
        // Substituting y = x into f gives x^3 + x + 1, whose roots are the common ones.
        let expected = UnivariatePolynomial::new(&[F::new(1), F::new(1), F::zero(), F::new(1)]);
        for at in 0u64..13 {
            let x = F::new(at);
            assert_eq!(
                resultant.eval(&x).is_zero(),
                expected.eval(&x).is_zero(),
                "at {}",
                at
            );
        }
        // x = 0: f(0, y) = y + 1 and g(0, y) = y share no root, and the resultant agrees.
        assert!(!resultant.eval(&F::zero()).is_zero());
    }

    /// A polynomial free of the eliminated variable is refused by argument number.
    #[test]
    fn test_degree_zero_is_refused() {
        let f = parse("x^2 + 1");
        let g = parse("y - x");
        assert_eq!(
            bivariate_resultant(&f, &g, 1),
            Err(ResultantError::NoDegreeInEliminatedVariable { argument: 0 })
        );
        assert_eq!(
            bivariate_resultant(&g, &f, 1),
            Err(ResultantError::NoDegreeInEliminatedVariable { argument: 1 })
        );
    }

    /// The field has to be large enough to interpolate the bound.
    #[test]
    fn test_a_field_too_small_to_interpolate() {
        type Tiny = PrimeFieldElement64<5>;
        let f = MultivariatePolynomial::<2, Tiny>::parse("x^3*y^2 + y + 1", VARS).expect("parses");
        let g =
            MultivariatePolynomial::<2, Tiny>::parse("x^3*y^2 + 2*y + 1", VARS).expect("parses");
        // The bound is 2·3 + 2·3 = 12 and GF(5) has five elements.
        assert_eq!(
            bivariate_resultant(&f, &g, 1),
            Err(ResultantError::FieldTooSmall { needed: 13 })
        );
    }

    /// The registered `t = 16` slice, end to end: evaluate, eliminate, solve, verify.
    ///
    /// The spike's whole claim in one test. `cico_bivariate` turns the 46-variable system into two
    /// polynomials of degree `3^2 = 9`; their resultant has degree 81, exactly the Bézout bound;
    /// its roots extend to points that the **permutation** accepts. Nothing about this test trusts
    /// the resultant — `is_solution` runs the real permutation on the recovered inputs.
    #[test]
    fn test_the_registered_full_width_slice_end_to_end() {
        use rand::{prelude::StdRng, SeedableRng};

        use crate::{
            fields::PrimeFieldElement64,
            grobner::research::{challenge, Specialization, KOALABEAR_PRIME},
            roots,
        };

        type Koala = PrimeFieldElement64<KOALABEAR_PRIME>;

        let manifest = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
        let instance = manifest.cico_instance::<Koala>().expect("builds");
        let free = instance.free_inputs();

        // The slice M23-B and M23-C measured, from the same seeded stream.
        let variables: Vec<usize> = (2..free).collect();
        let specialization =
            Specialization::<46, Koala>::seeded(&variables, 1).expect("distinct indices");
        let fixed: Vec<Koala> = (2..free)
            .map(|i| specialization.value_of(i).expect("fixed"))
            .collect();

        let outputs = cico_bivariate(&instance, &fixed).expect("two free inputs remain");
        assert_eq!(outputs.len(), 2, "k = 2 constrained words");
        for output in &outputs {
            assert_eq!(output.degree(), 9, "two rounds of a cubic S-box");
        }

        let resultant =
            bivariate_resultant(&outputs[0], &outputs[1], 1).expect("both involve the second");
        assert_eq!(resultant.degree(), 81, "9 x 9, the Bézout bound exactly");

        // Every root is a candidate for the first unknown; the second comes from the first
        // polynomial and is checked against the second. Three of them survive and verify.
        let mut verified = 0;
        for first in roots(&resultant, &mut StdRng::seed_from_u64(7)) {
            let specialized: Vec<Koala> = (0..=9)
                .map(|power| {
                    outputs[0]
                        .terms()
                        .iter()
                        .filter(|(monomial, _)| monomial.exponents()[1] as usize == power)
                        .map(|(monomial, c)| *c * first.pow(monomial.exponents()[0] as u128))
                        .fold(Koala::zero(), |acc, term| acc + term)
                })
                .collect();
            for second in roots(
                &UnivariatePolynomial::new(&specialized),
                &mut StdRng::seed_from_u64(11),
            ) {
                let mut inputs = vec![first, second];
                inputs.extend_from_slice(&fixed);
                if instance.is_solution(&inputs).expect("the right width") {
                    verified += 1;
                }
            }
        }
        assert_eq!(
            verified, 3,
            "the seed-1 slice has three base-field solutions, and the permutation accepts all of \
             them"
        );
    }

    /// Over a large field, a degree-9 pair gives a resultant of the Bézout degree.
    ///
    /// The shape M23-E's CICO instance has: two polynomials of degree 9 in two unknowns, whose
    /// resultant is bounded by 81. This checks the bound is attained by a generic-looking pair, so
    /// a *smaller* degree on the real instance is a fact about Poseidon and not about this code.
    #[test]
    fn test_the_bezout_degree_is_attained() {
        type Big = PrimeFieldElement64<2_130_706_433>;
        let f = MultivariatePolynomial::<2, Big>::parse("x^9 + y^9 + x*y + 1", VARS).expect("ok");
        let g = MultivariatePolynomial::<2, Big>::parse("x^9 - y^9 + x + 7", VARS).expect("ok");
        let resultant = bivariate_resultant(&f, &g, 1).expect("both involve y");
        assert_eq!(resultant.degree(), 81, "9 x 9 = 81, and it is reached");
    }
}
