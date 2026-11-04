//! Shape position: when the lex basis can be read off one variable's Krylov sequence.
//!
//! **A feasibility study with a verified prototype, not a production converter.** M18-4's research
//! spike, and §8 of `docs/MILESTONE-FGLM-SCALABILITY.md` has the measurements and the go/no-go.
//!
//! # The idea
//! Classical FGLM walks the monomials in lex order, asks of each whether its class is in the span
//! of those accepted, and emits a relation when it is not. The walk is why it keeps every accepted
//! quotient vector: a candidate's class is `x_i` times an accepted one.
//!
//! If a single variable `t` *generates* the quotient algebra — if `1, t, ..., t^{D-1}` is a basis of
//! `A`, which is what **shape position** means — none of that is needed. The lex basis is then
//!
//! ```text
//! p(t) = 0,   x_0 - h_0(t) = 0,   ...,   x_{N-2} - h_{N-2}(t) = 0
//! ```
//!
//! and every one of those `N` polynomials is one linear solve against the same `D x D` matrix,
//! whose columns are the powers of `t`. There is no frontier, no monomial ordering question, and
//! nothing to retain but the echelon form itself — the Krylov vectors are consumed as they are
//! produced, so the accepted-vector block classical FGLM carries does not exist here.
//!
//! # What this is not
//! It is not sparse FGLM. Faugère and Mou's algorithms replace the dense dependence test with a
//! *scalar* Krylov sequence `l(t^k)` of length `2D` for a linear form `l`, and recover the minimal
//! polynomial from it by Berlekamp–Massey in `O(D)` memory. That is where the asymptotic win is,
//! and Zeebra has no Berlekamp–Massey. This prototype keeps the dense echelon form, so it is
//! `O(D^2)` memory like the classical algorithm — just a smaller constant and a simpler shape.
//! §8.5 of the milestone document is the recommendation that follows.
//!
//! # Nothing probabilistic is exposed
//! [`shape_lex_basis`] verifies its own output before returning it, deterministically. See there.
//!
//! # References
//! * Faugère, J.-C., Mou, C. (2017). *Sparse FGLM algorithms.* J. Symbolic Computation 80,
//!   538–569.

use std::fmt::{Display, Formatter};

use crate::{
    grobner::fglm::{incremental_span::Dependence, IncrementalSpan, QuotientAlgebra},
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

/// What a variable's Krylov sequence showed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ShapeReport {
    /// The variable whose powers were taken.
    pub variable: usize,

    /// `D = dim_F(R/I)`.
    pub dimension: usize,

    /// The degree of `t`'s minimal polynomial over `F`, i.e. the first `k` with `t^k` dependent on
    /// `1, ..., t^{k-1}`.
    ///
    /// At most the dimension always, and equal to it exactly when `t` generates the algebra.
    pub minimal_polynomial_degree: usize,
}

impl ShapeReport {
    /// Whether this variable generates the quotient algebra.
    ///
    /// **An algebraic test, not a count of solutions.** `1, t, ..., t^{D-1}` being independent is
    /// what is checked; how many points the variety has over the base field has nothing to do with
    /// it, and a nonradical ideal can be in shape position — `<x - 1, (y - 1)^2>` is.
    pub fn is_separating(&self) -> bool {
        self.minimal_polynomial_degree == self.dimension
    }
}

/// Why a shape-form conversion could not be produced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ShapeError {
    /// The variable does not generate the quotient algebra, so there is no shape form in it.
    NotSeparating {
        /// The variable tried.
        variable: usize,
        /// The degree its powers reached before becoming dependent.
        minimal_degree: usize,
        /// `D`, which that degree would have to equal.
        dimension: usize,
    },

    /// The produced polynomials did not verify, so they were not returned.
    ///
    /// **Should be unreachable**, and is an error rather than a `debug_assert` precisely because
    /// this is a prototype: a route that is new is a route whose output has to be checked, and a
    /// check that only runs in debug builds is not a check. Reaching this is a bug in this module.
    Unverified {
        /// Which polynomial, and why.
        detail: String,
    },
}

impl Display for ShapeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotSeparating {
                variable,
                minimal_degree,
                dimension,
            } => write!(
                f,
                "x_{} has a minimal polynomial of degree {} in a quotient of dimension {}, so it \
                 does not generate the algebra",
                variable, minimal_degree, dimension
            ),
            Self::Unverified { detail } => {
                write!(f, "the shape basis did not verify: {}", detail)
            }
        }
    }
}

impl std::error::Error for ShapeError {}

/// The echelon form of `1, t, ..., t^{k-1}` for the largest independent `k`, that `k`, and `t^k`.
///
/// The span is returned ready to answer "what is this class in terms of the powers of `t`", which
/// is the only question the shape form asks. The Krylov vectors themselves are **not** returned
/// and are not retained: each is produced from the previous by one operator application and
/// consumed immediately, so this holds one `D`-vector at a time beyond the echelon form. That is
/// the block classical FGLM cannot do without and this route never allocates.
///
/// The one power that *is* returned is the first dependent one, `t^k`. The sweep has it in hand
/// when it stops, and recomputing it afterwards would be `D` more operator applications — which,
/// measured, was most of what made this route slower than the classical walk.
fn krylov_span<const N: usize, F: FiniteField>(
    algebra: &QuotientAlgebra<N, F>,
    variable: usize,
) -> (IncrementalSpan<F>, usize, Vec<F>) {
    let dimension = algebra.dimension();
    let mut span = IncrementalSpan::new(dimension);
    let mut power = algebra.one();

    for _ in 0..dimension {
        match span.reduce(&power) {
            Dependence::Independent {
                residue,
                combination,
            } => span.insert(residue, combination),
            // `t^k` is a combination of lower powers, so the minimal polynomial has degree `k` and
            // no higher power can be independent either.
            Dependence::Dependent { .. } => break,
        }
        power = algebra.multiply_by_variable(variable, &power);
    }

    let degree = span.accepted();
    (span, degree, power)
}

/// Whether a variable generates the quotient algebra, and the degree of its minimal polynomial.
///
/// `D` applications of `T_variable` and `D` reductions against a growing echelon form.
///
/// # Panics
/// If `variable` is not below `N`.
pub fn shape_report<const N: usize, F: FiniteField>(
    algebra: &QuotientAlgebra<N, F>,
    variable: usize,
) -> ShapeReport {
    assert!(variable < N, "variable {} of {}", variable, N);
    let (_, degree, _) = krylov_span(algebra, variable);
    ShapeReport {
        variable,
        dimension: algebra.dimension(),
        minimal_polynomial_degree: degree,
    }
}

/// Every variable that generates the quotient algebra, ascending.
///
/// Empty when none does, which is the case the shape form does not cover. Costs `N` Krylov sweeps,
/// so it is a diagnostic rather than something to call before a conversion — [`shape_lex_basis`]
/// needs the *last* variable specifically and reports on that one alone.
pub fn separating_variables<const N: usize, F: FiniteField>(
    algebra: &QuotientAlgebra<N, F>,
) -> Vec<usize> {
    (0..N)
        .filter(|variable| shape_report(algebra, *variable).is_separating())
        .collect()
}

/// The reduced lex Gröbner basis in shape form, or why there is none.
///
/// Uses `t = x_{N-1}`, the lex-*last* variable, and no other: lex eliminates the earlier variables,
/// so `x_i - h_i(t)` is a lex basis element only when `t` is last. A different variable can perfectly
/// well generate the algebra — [`separating_variables`] reports which do — without the shape form
/// in it being a *lex* basis.
///
/// # The output is verified before it is returned
/// Two facts, and together they are a complete proof that the result is the reduced lex basis:
///
/// 1. **Every polynomial is in `I`.** Checked by evaluating it at the multiplication operators and
///    requiring the zero vector — `f` is in `I` exactly when its class in `A` is zero. This is the
///    part a linear solve could get wrong, and it is checked rather than argued.
/// 2. **The leading monomials are `t^D` and `x_0, ..., x_{N-2}`.** True by construction, and the
///    standard monomials of the ideal they generate are exactly `1, t, ..., t^{D-1}` — `D` of them.
///
/// A set of polynomials in `I` whose leading monomials generate a monomial ideal with the *same*
/// finite quotient dimension as `LT(I)` generates `LT(I)` itself, because one monomial ideal
/// contained in another with equal quotient dimensions is equal to it. So the set is a Gröbner
/// basis; and each element is monic with no term divisible by another's leading monomial, so it is
/// the reduced one.
///
/// **Nothing here is probabilistic**, so there is no certified-versus-conjectural distinction to
/// expose. A caller gets the basis or an error.
///
/// # Why the check is not `normal_form`
/// Reducing these polynomials modulo the *grevlex* source basis would be the obvious check and is
/// the wrong one: `p(t)` has degree `D` in a single variable, which under grevlex is as far from
/// the staircase as a monomial gets. Tried, it did not finish on cyclic-6 within ten minutes —
/// avoiding exactly that reduction is why one converts bases at all. Evaluating at the operators
/// is `D` operator applications per relation and is independent of the echelon form that produced
/// the coefficients, so it is both cheaper and a real second opinion. The unit tests additionally
/// reduce modulo the source basis on small systems, where it is affordable.
///
/// # Errors
/// [`ShapeError::NotSeparating`] if `x_{N-1}` does not generate the algebra, and
/// [`ShapeError::Unverified`] if a produced polynomial is not in the ideal — which would be a bug
/// in this module.
pub fn shape_lex_basis<const N: usize, F: FiniteField>(
    algebra: &QuotientAlgebra<N, F>,
) -> Result<Vec<MultivariatePolynomial<N, F>>, ShapeError> {
    let dimension = algebra.dimension();
    let last = N - 1;

    // The unit ideal: the quotient is the zero space, every variable trivially generates it, and
    // the lex basis is `{1}`. Returned here because the Krylov sweep below has nothing to sweep.
    if dimension == 0 {
        return Ok(vec![MultivariatePolynomial::new(&[(
            Monomial::one(),
            F::one(),
        )])]);
    }

    let (mut span, degree, power) = krylov_span(algebra, last);
    if degree != dimension {
        return Err(ShapeError::NotSeparating {
            variable: last,
            minimal_degree: degree,
            dimension,
        });
    }

    let mut basis: Vec<MultivariatePolynomial<N, F>> = Vec::with_capacity(N);

    // `p(t) = t^D - sum_k c_k t^k`. The span has accepted `1 .. t^{D-1}`, so the class of `t^D`
    // must be dependent on them — the space has no room for anything else. `power` is that class,
    // carried out of the sweep rather than recomputed.
    let coefficients = match span.reduce(&power) {
        Dependence::Dependent { coefficients } => coefficients,
        Dependence::Independent { .. } => {
            return Err(ShapeError::Unverified {
                detail: format!(
                    "t^{} is independent of {} powers in a {}-dimensional algebra",
                    dimension, dimension, dimension
                ),
            })
        }
    };
    basis.push(univariate_relation(
        Monomial::univariate(last, dimension as u32),
        last,
        &coefficients,
    ));

    // `x_i - h_i(t)` for every other variable. The class of `x_i` is `T_i` applied to the class of
    // 1, which is one operator application rather than a reduction.
    for variable in 0..last {
        let class = algebra.multiply_by_variable(variable, &algebra.one());
        let coefficients = match span.reduce(&class) {
            Dependence::Dependent { coefficients } => coefficients,
            Dependence::Independent { .. } => {
                return Err(ShapeError::Unverified {
                    detail: format!(
                        "x_{} is independent of a basis of the whole algebra",
                        variable
                    ),
                })
            }
        };
        basis.push(univariate_relation(
            Monomial::univariate(variable, 1),
            last,
            &coefficients,
        ));
    }

    // Fact 1 of the two above. Fact 2 holds by construction and is argued, not computed.
    for polynomial in &basis {
        if !vanishes_in_algebra(algebra, polynomial, last) {
            return Err(ShapeError::Unverified {
                detail: format!("{} is not in the ideal", polynomial),
            });
        }
    }

    // Descending by lex leading monomial, the convention both Gröbner engines return.
    basis.sort_by(|a, b| {
        MonomialOrder::Lexicographic.cmp(
            &b.leading_monomial(MonomialOrder::Lexicographic),
            &a.leading_monomial(MonomialOrder::Lexicographic),
        )
    });
    Ok(basis)
}

/// Whether a shape relation's class in the quotient algebra is zero, i.e. whether it is in `I`.
///
/// Evaluates the polynomial at the operators rather than reducing it: every term is `c * t^k` or
/// the single leading `x_i`, so one sweep up the powers of `t` accumulates all of them in `D`
/// operator applications. Independent of the echelon form that produced the coefficients, which is
/// what makes it a check rather than a restatement.
///
/// # Panics
/// If a term is neither a power of `t` nor a single other variable, which the construction above
/// cannot produce.
fn vanishes_in_algebra<const N: usize, F: FiniteField>(
    algebra: &QuotientAlgebra<N, F>,
    polynomial: &MultivariatePolynomial<N, F>,
    t: usize,
) -> bool {
    let dimension = algebra.dimension();
    let mut total = vec![F::zero(); dimension];

    // The terms that are not powers of `t`: at most the one leading `x_i`.
    let mut powers: Vec<(usize, F)> = Vec::new();
    for (monomial, coefficient) in polynomial.terms() {
        let exponents = monomial.exponents();
        let other: Vec<usize> = (0..N).filter(|i| *i != t && exponents[*i] != 0).collect();
        match other.as_slice() {
            [] => powers.push((exponents[t] as usize, *coefficient)),
            [variable] => {
                assert_eq!(
                    exponents[*variable], 1,
                    "a shape relation's non-leading terms are powers of t"
                );
                assert_eq!(exponents[t], 0, "a shape relation has no mixed term");
                let class = algebra.multiply_by_variable(*variable, &algebra.one());
                for (slot, value) in total.iter_mut().zip(&class) {
                    *slot += *coefficient * *value;
                }
            }
            _ => panic!("a shape relation has no term in two variables"),
        }
    }

    // One sweep up the powers of `t`, accumulating every term that needs each.
    let highest = powers.iter().map(|(k, _)| *k).max().unwrap_or(0);
    let mut power = algebra.one();
    for k in 0..=highest {
        for (_, coefficient) in powers.iter().filter(|(exponent, _)| *exponent == k) {
            for (slot, value) in total.iter_mut().zip(&power) {
                *slot += *coefficient * *value;
            }
        }
        if k < highest {
            power = algebra.multiply_by_variable(t, &power);
        }
    }

    total.iter().all(|value| value.is_zero())
}

/// `leading - sum_k coefficients[k] * t^k`, monic in `leading`.
fn univariate_relation<const N: usize, F: FiniteField>(
    leading: Monomial<N>,
    t: usize,
    coefficients: &[F],
) -> MultivariatePolynomial<N, F> {
    let mut terms: Vec<(Monomial<N>, F)> = Vec::with_capacity(coefficients.len() + 1);
    terms.push((leading, F::one()));
    for (k, coefficient) in coefficients.iter().enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        terms.push((Monomial::univariate(t, k as u32), F::zero() - *coefficient));
    }
    MultivariatePolynomial::new(&terms)
}

#[cfg(test)]
mod tests {
    use super::{separating_variables, shape_lex_basis, shape_report, ShapeError};
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura, planted},
            f4,
            fglm::{fglm_to_lex, FglmOptions, QuotientAlgebra},
        },
        FiniteField, MonomialOrder, MultivariatePolynomial,
    };

    type F = Zp2147483647;

    const SOURCE: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    fn algebra_of<const N: usize>(
        system: &[MultivariatePolynomial<N, F>],
    ) -> QuotientAlgebra<N, F> {
        let basis = f4(system, SOURCE).expect("within limits");
        QuotientAlgebra::new(&basis, SOURCE, &FglmOptions::unbounded()).expect("finite")
    }

    fn parse<const N: usize>(
        system: &[&str],
        variables: [&str; N],
    ) -> Vec<MultivariatePolynomial<N, F>> {
        system
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, variables).unwrap())
            .collect()
    }

    /// Where the shape form exists, it is the same basis classical FGLM produces.
    ///
    /// Not "a" lex basis: the reduced lex basis is unique, so agreement is an equality of values
    /// and the two routes cannot both be right and different.
    #[test]
    fn test_the_shape_basis_is_the_lex_basis() {
        fn check<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
            let algebra = algebra_of(system);
            let expected = fglm_to_lex(algebra.source_basis(), SOURCE).expect("convertible");

            match shape_lex_basis(&algebra) {
                Ok(shape) => assert_eq!(
                    shape, expected,
                    "{}: the shape basis disagrees with classical FGLM",
                    name
                ),
                Err(ShapeError::NotSeparating { .. }) => {}
                Err(e) => panic!("{}: {}", name, e),
            }
        }

        for system in [
            &["x^2 - y", "y^3 - 1"][..],
            &["x + y", "x*y - 1"][..],
            &["x^3 - 1", "y - x^2"][..],
            &["x^2 - 2*x + 1", "y - x"][..],
            &["x^4 - x", "y^2 - x"][..],
            &["x^2", "y^2"][..],
            &["x^2 + 1", "y^2 + 1"][..],
        ] {
            check(system[0], &parse(system, ["x", "y"]));
        }

        check("katsura-3", &katsura::<3, F>());
        check("katsura-4", &katsura::<4, F>());
        check("katsura-5", &katsura::<5, F>());
        check("cyclic-3", &cyclic::<3, F>());
        check("cyclic-5", &cyclic::<5, F>());
        let point: Vec<F> = [3u64, 5, 7, 11].iter().map(|v| F::new(*v)).collect();
        check("planted-4", &planted::<4, F>(&point));
    }

    /// A system that is not in shape position is rejected, with the degree that fell short.
    ///
    /// `<x^2 - 1, y^2 - 1, z - 1>` has dimension four and `z` is the constant 1 in the quotient, so
    /// the powers of `z` span one dimension. Rejection is the correct answer, not a failure.
    #[test]
    fn test_a_system_not_in_shape_position_is_rejected() {
        let algebra = algebra_of(&parse(&["x^2 - 1", "y^2 - 1", "z - 1"], ["x", "y", "z"]));
        assert_eq!(algebra.dimension(), 4);

        match shape_lex_basis(&algebra) {
            Err(ShapeError::NotSeparating {
                variable,
                minimal_degree,
                dimension,
            }) => {
                assert_eq!(variable, 2);
                assert_eq!(minimal_degree, 1, "z is the constant 1 in this quotient");
                assert_eq!(dimension, 4);
            }
            other => panic!("expected a rejection, got {:?}", other.is_ok()),
        }
    }

    /// Shape position is decided algebraically, not from the number of solutions.
    ///
    /// `<x - 1, (y - 1)^2>` has one point over the base field and quotient dimension two, and `y`
    /// does generate the algebra — so the shape form exists for a **nonradical** ideal with fewer
    /// points than dimensions. A test that counted solutions would get this wrong.
    #[test]
    fn test_a_nonradical_ideal_can_be_in_shape_position() {
        let algebra = algebra_of(&parse(&["x - 1", "y^2 - 2*y + 1"], ["x", "y"]));
        assert_eq!(algebra.dimension(), 2);

        let report = shape_report(&algebra, 1);
        assert!(report.is_separating(), "y should generate this algebra");
        assert_eq!(report.minimal_polynomial_degree, 2);

        let shape = shape_lex_basis(&algebra).expect("in shape position");
        assert_eq!(
            shape,
            fglm_to_lex(algebra.source_basis(), SOURCE).expect("convertible")
        );
    }

    /// The minimal-polynomial degree never exceeds the dimension, and the report is consistent.
    #[test]
    fn test_the_minimal_degree_is_bounded_by_the_dimension() {
        fn check<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
            let algebra = algebra_of(system);
            for variable in 0..N {
                let report = shape_report(&algebra, variable);
                assert_eq!(report.variable, variable);
                assert_eq!(report.dimension, algebra.dimension());
                assert!(
                    report.minimal_polynomial_degree <= report.dimension,
                    "{}: x_{} has minimal degree {} in dimension {}",
                    name,
                    variable,
                    report.minimal_polynomial_degree,
                    report.dimension
                );
                assert_eq!(
                    report.is_separating(),
                    report.minimal_polynomial_degree == report.dimension
                );
            }
        }

        check("katsura-4", &katsura::<4, F>());
        check("cyclic-5", &cyclic::<5, F>());
        check(
            "x^2-1, y^2-1, z-1",
            &parse(&["x^2 - 1", "y^2 - 1", "z - 1"], ["x", "y", "z"]),
        );
    }

    /// `separating_variables` lists exactly the variables whose report says so.
    #[test]
    fn test_separating_variables_agrees_with_the_reports() {
        let algebra = algebra_of(&katsura::<4, F>());
        let listed = separating_variables(&algebra);
        let expected: Vec<usize> = (0..4)
            .filter(|v| shape_report(&algebra, *v).is_separating())
            .collect();
        assert_eq!(listed, expected);
    }

    /// The unit ideal converts to `{1}`, as classical FGLM does.
    #[test]
    fn test_the_unit_ideal_converts_to_one() {
        let algebra = algebra_of(&parse(&["x", "x - 1"], ["x", "y"]));
        assert_eq!(algebra.dimension(), 0);
        assert_eq!(
            shape_lex_basis(&algebra).expect("the unit ideal"),
            fglm_to_lex(algebra.source_basis(), SOURCE).expect("convertible")
        );
    }

    /// The shape basis is in the ideal and is reduced, checked independently of the construction.
    ///
    /// The verification inside `shape_lex_basis` is a precondition of it returning at all; this
    /// re-checks the properties from outside, so a bug in that verification would not hide a bug in
    /// the construction.
    #[test]
    fn test_the_shape_basis_is_reduced_and_lies_in_the_ideal() {
        const LEX: MonomialOrder = MonomialOrder::Lexicographic;

        fn check<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
            let algebra = algebra_of(system);
            let Ok(basis) = shape_lex_basis(&algebra) else {
                return;
            };

            assert_eq!(basis.len(), N, "{}: a shape basis has N elements", name);
            for polynomial in &basis {
                assert!(
                    polynomial
                        .normal_form(algebra.source_basis(), SOURCE)
                        .is_zero(),
                    "{}: {} is not in the ideal",
                    name,
                    polynomial
                );
            }

            // Reduced: no non-leading term of any element is divisible by any element's leading
            // monomial.
            let leading: Vec<_> = basis.iter().map(|p| p.leading_monomial(LEX)).collect();
            for polynomial in &basis {
                let own = polynomial.leading_monomial(LEX);
                for monomial in polynomial.terms().keys() {
                    if *monomial == own {
                        continue;
                    }
                    for lead in &leading {
                        assert!(
                            monomial.checked_div(lead).is_none(),
                            "{}: {} is divisible by the leading monomial {}",
                            name,
                            monomial,
                            lead
                        );
                    }
                }
            }
        }

        check("katsura-4", &katsura::<4, F>());
        check("cyclic-5", &cyclic::<5, F>());
        check("x^2-y, y^3-1", &parse(&["x^2 - y", "y^3 - 1"], ["x", "y"]));
    }
}
