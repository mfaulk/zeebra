//! Solving a zero-dimensional polynomial system over its base field, under explicit budgets.
//!
//! Separate from [`solve`](super::solve) rather than replacing it. That function handles
//! positive-dimensional systems by enumerating the field, which is the only way to list a solution
//! set that grows with the field, and it panics when the field is too large for that to be
//! possible. These entry points refuse such systems outright and in exchange never enumerate, never
//! panic on an ordinary input, and report every failure as a `Result`.
//!
//! # No variable is ever free, and that is a theorem
//!
//! `solve`'s field enumeration exists because a variable can be left unconstrained by the basis.
//! For a **zero-dimensional** ideal that cannot happen, which is what lets this module drop the
//! enumeration entirely:
//!
//! Zero-dimensionality gives `x_k^d` in `LT(I)` for some `d >= 1`, so some basis element `g` has
//! `LM(g) = x_k^d` — a pure power of `x_k`, since the leading monomials generate `LT(I)` and a
//! pure power in that monomial ideal must be divisible by one of them. Under lex every monomial of
//! `g` is at most `x_k^d`, and a monomial at most `x_k^d` has exponent zero in `x_0 .. x_{k-1}`:
//! otherwise lex would compare that earlier variable first and make it larger. So `g` lies in
//! `F[x_k, ..., x_{N-1}]`, and substituting the already-assigned `x_{k+1} .. x_{N-1}` leaves a
//! polynomial in `x_k` alone. Its `x_k^d` coefficient is `g`'s leading coefficient, which is 1
//! because the basis is reduced, and substitution cannot touch it. So the constraint is a univariate
//! polynomial of degree exactly `d >= 1`.
//!
//! Hence `candidate_values` never returns `None` here, there is no field-order limit, and
//! `MAX_FIELD_ORDER` has no analogue in this module.
//!
//! # References
//! * Cox, Little, O'Shea, *Ideals, Varieties, and Algorithms*, Ch. 2 §2.2 and Ch. 5, for the
//!   finiteness theorem and the elimination property of lex.

use std::fmt::{Display, Formatter};

use rand::{CryptoRng, RngCore};

use crate::{
    grobner::{
        f4_with_options,
        fglm::{classify_ideal, fglm_to_lex_with_options, FglmError, FglmOptions, FglmStatistics},
        solve::{candidate_values, is_nonzero_constant},
        F4Error, F4Options,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

/// Which route to the lexicographic basis solving needs.
///
/// Explicit rather than chosen for you. §10.2 of `docs/MILESTONE-FGLM-SOLVING.md` measures both:
/// conversion wins by 7.4x on cyclic-6 and is the only route at all on katsura-7, and loses by 65x
/// on planted-8. No heuristic yet distinguishes those in advance, and one that guessed would be
/// worse than a choice the caller makes knowingly.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum SolveStrategy {
    /// Compute the lex basis directly with F4. Faster on most systems, and the default.
    #[default]
    DirectLexF4,

    /// Compute a grevlex basis with F4 and convert it with FGLM.
    ///
    /// Slower on most systems and the only route on some: katsura-7's lex basis is beyond F4's
    /// default limits while its grevlex basis takes 30 ms.
    GrevlexF4ThenFglm,
}

/// Budgets and strategy for the zero-dimensional solvers.
///
/// Not `Copy`, because `F4Options` is not.
#[derive(Clone, Debug, Default)]
pub struct SolveOptions {
    pub strategy: SolveStrategy,

    /// Limits for the Gröbner basis computation.
    pub f4: F4Options,

    /// Limits for the conversion, used only by [`SolveStrategy::GrevlexF4ThenFglm`].
    pub fglm: FglmOptions,

    /// Candidate values tried across the whole search before it gives up. `None` for no limit.
    ///
    /// A zero-dimensional system's search tree is finite, so this is for a caller with a latency
    /// budget rather than for termination.
    pub max_branches: Option<usize>,

    /// Distinct solutions to find before giving up. `None` for no limit.
    ///
    /// Exceeding it is an error and not a truncated list: a list that looks complete and is not is
    /// worse than a failure. Ignored by [`solve_one`], which stops at one by construction.
    pub max_solutions: Option<usize>,
}

impl SolveOptions {
    /// The given strategy, with every other field at its default.
    pub fn with_strategy(strategy: SolveStrategy) -> Self {
        Self {
            strategy,
            ..Self::default()
        }
    }
}

/// What a zero-dimensional solve did.
///
/// The figures `docs/MILESTONE-FGLM-SOLVING.md` §10.3 reports, so a caller can reproduce them
/// without an instrumented build. `branches` is the one that is otherwise invisible: it is what
/// [`SolveOptions::max_branches`] is enforced on, and the difference between finding one solution
/// and finding all of them shows up here before it shows up in the clock.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SolveStatistics {
    /// Elements of the lexicographic basis the search ran on.
    pub lex_basis_elements: usize,

    /// Candidate assignments tried, across the whole search.
    pub branches: usize,

    /// Distinct solutions returned.
    pub solutions: usize,

    /// What the conversion did, or `None` under [`SolveStrategy::DirectLexF4`].
    pub fglm: Option<FglmStatistics>,
}

/// Why a zero-dimensional solve stopped without an answer.
///
/// Note what is **not** here: having no solution over the base field. That is `Ok(None)` from
/// [`solve_one`] and an empty vector from [`solve_zero_dimensional`], because it is an answer. A
/// system can be zero-dimensional, have a quotient algebra of positive dimension, and still have
/// no points in `F` — `x^2 + 1` over GF(3) has quotient dimension two and no roots.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SolveError {
    /// The system is not zero-dimensional. Use [`solve`](super::solve) for those, which enumerates
    /// the field and is bounded by the field's order rather than by the solution count.
    PositiveDimensional,

    /// The Gröbner basis computation crossed one of its limits.
    Grobner(F4Error),

    /// The conversion crossed one of its limits.
    Fglm(FglmError),

    /// The search tried `limit` candidate assignments without exhausting the tree.
    TooManyBranches { limit: usize },

    /// More distinct solutions exist than the caller allowed.
    ///
    /// Carries only the limit, and no partial list: the solutions found so far are a prefix of an
    /// unknown whole, and returning them would be indistinguishable from completeness.
    TooManySolutions { limit: usize },
}

impl Display for SolveError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PositiveDimensional => write!(
                f,
                "the system is not zero-dimensional, so its solution set is not finite"
            ),
            Self::Grobner(e) => write!(f, "the Gröbner basis could not be computed: {}", e),
            Self::Fglm(e) => write!(f, "the basis could not be converted to lex: {}", e),
            Self::TooManyBranches { limit } => write!(
                f,
                "the search did not finish within {} candidate assignments",
                limit
            ),
            Self::TooManySolutions { limit } => {
                write!(f, "there are more than the {} solutions allowed", limit)
            }
        }
    }
}

impl std::error::Error for SolveError {}

impl From<F4Error> for SolveError {
    fn from(e: F4Error) -> Self {
        Self::Grobner(e)
    }
}

impl From<FglmError> for SolveError {
    /// A plain wrap, with no special case for `FglmError::PositiveDimensional`.
    ///
    /// There was one, and it was dead: `lex_basis` classifies the source basis itself before
    /// converting, so the conversion is never reached with a positive-dimensional ideal and never
    /// reports one. Both strategies therefore produce `SolveError::PositiveDimensional` from the
    /// same place.
    fn from(e: FglmError) -> Self {
        Self::Fglm(e)
    }
}

/// One solution of `system` over `F`, or `Ok(None)` if it has none.
///
/// Stops at the first complete point rather than enumerating the solution set, backtracking when a
/// partial assignment cannot be completed.
///
/// # Errors
/// [`SolveError::PositiveDimensional`] if the system is not zero-dimensional, or a resource variant
/// if a limit in [`SolveOptions::default`] is crossed. Having no solution is `Ok(None)`.
pub fn solve_one<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
) -> Result<Option<[F; N]>, SolveError> {
    solve_one_with_options(system, rng, &SolveOptions::default()).map(|(found, _)| found)
}

/// As [`solve_one`], under the given strategy and budgets, additionally reporting the work done.
#[allow(clippy::type_complexity)]
pub fn solve_one_with_options<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
    options: &SolveOptions,
) -> Result<(Option<[F; N]>, SolveStatistics), SolveError> {
    let (basis, fglm) = lex_basis(system, options)?;
    let (found, mut statistics) = search(&basis, system, Stop::AtFirst, options, rng)?;
    statistics.fglm = fglm;
    Ok((found.into_iter().next(), statistics))
}

/// Every distinct solution of `system` over `F`.
///
/// The order is unspecified. Distinctness is automatic rather than enforced: each level of the
/// search tries distinct roots, so two complete assignments differ in at least one coordinate.
///
/// # Errors
/// As [`solve_one`], plus [`SolveError::TooManySolutions`]. The result is never a truncated list.
pub fn solve_zero_dimensional<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
) -> Result<Vec<[F; N]>, SolveError> {
    solve_zero_dimensional_with_options(system, rng, &SolveOptions::default())
        .map(|(found, _)| found)
}

/// As [`solve_zero_dimensional`], under the given strategy and budgets.
pub fn solve_zero_dimensional_with_options<
    const N: usize,
    F: FiniteField,
    R: RngCore + CryptoRng,
>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
    options: &SolveOptions,
) -> Result<(Vec<[F; N]>, SolveStatistics), SolveError> {
    let (basis, fglm) = lex_basis(system, options)?;
    let (found, mut statistics) = search(&basis, system, Stop::AtEvery, options, rng)?;
    statistics.fglm = fglm;
    Ok((found, statistics))
}

/// The lexicographic Gröbner basis of a zero-dimensional system, by the chosen route.
///
/// Zero-dimensionality is decided from whichever basis the strategy computes first, which is the
/// grevlex one where there is a choice: classification is a question about leading monomials and
/// costs the same under any order, so it is asked of the cheaper basis.
#[allow(clippy::type_complexity)]
fn lex_basis<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    options: &SolveOptions,
) -> Result<(Vec<MultivariatePolynomial<N, F>>, Option<FglmStatistics>), SolveError> {
    match options.strategy {
        SolveStrategy::DirectLexF4 => {
            let lex = MonomialOrder::Lexicographic;
            let (basis, _) = f4_with_options(system, lex, &options.f4)?;
            if !classify_ideal(&basis, lex).is_finite_dimensional() {
                return Err(SolveError::PositiveDimensional);
            }
            Ok((basis, None))
        }
        SolveStrategy::GrevlexF4ThenFglm => {
            let source_order = MonomialOrder::GradedReverseLexicographic;
            let (source, _) = f4_with_options(system, source_order, &options.f4)?;
            // `fglm_to_lex_with_options` classifies too, but doing it here means a
            // positive-dimensional system costs no quotient-algebra construction and reports the
            // same variant it would under the other strategy.
            if !classify_ideal(&source, source_order).is_finite_dimensional() {
                return Err(SolveError::PositiveDimensional);
            }
            let (basis, statistics) =
                fglm_to_lex_with_options(&source, source_order, &options.fglm)?;
            Ok((basis, Some(statistics)))
        }
    }
}

/// Whether the search stops at the first solution or collects them all.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Stop {
    AtFirst,
    AtEvery,
}

/// What the search has spent, and what it is allowed to spend.
struct Budget {
    branches: usize,
    max_branches: Option<usize>,
    max_solutions: Option<usize>,
}

impl Budget {
    /// Charge one candidate assignment.
    fn charge_branch(&mut self) -> Result<(), SolveError> {
        self.branches += 1;
        match self.max_branches {
            Some(limit) if self.branches > limit => Err(SolveError::TooManyBranches { limit }),
            _ => Ok(()),
        }
    }
}

/// Assign variables from the last backwards, collecting the points that satisfy the whole basis.
fn search<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
    basis: &[MultivariatePolynomial<N, F>],
    system: &[MultivariatePolynomial<N, F>],
    stop: Stop,
    options: &SolveOptions,
    rng: &mut R,
) -> Result<(Vec<[F; N]>, SolveStatistics), SolveError> {
    let mut statistics = SolveStatistics {
        lex_basis_elements: basis.len(),
        ..SolveStatistics::default()
    };

    // The unit ideal: the system is inconsistent, so there is nothing to search.
    if basis.iter().any(is_nonzero_constant) {
        return Ok((Vec::new(), statistics));
    }

    let mut budget = Budget {
        branches: 0,
        max_branches: options.max_branches,
        // Irrelevant when stopping at the first solution: the search unwinds on its own.
        max_solutions: match stop {
            Stop::AtFirst => None,
            Stop::AtEvery => options.max_solutions,
        },
    };
    let mut solutions = Vec::new();
    let mut assignment = [F::zero(); N];

    extend(
        basis,
        N,
        &mut assignment,
        &mut solutions,
        stop,
        &mut budget,
        rng,
    )?;

    // Every returned point is checked against the polynomials the caller passed, not against the
    // basis derived from them. A basis is only as good as the computation that produced it.
    for point in &solutions {
        for p in system {
            assert!(
                p.eval(point).is_zero(),
                "{:?} does not satisfy {}, which the solver was asked about",
                point,
                p
            );
        }
    }

    statistics.branches = budget.branches;
    statistics.solutions = solutions.len();
    Ok((solutions, statistics))
}

/// One level of the back-substitution.
///
/// `basis` always has the already-assigned variables substituted in, so at the deepest level every
/// polynomial is a constant.
fn extend<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
    basis: &[MultivariatePolynomial<N, F>],
    remaining: usize,
    assignment: &mut [F; N],
    solutions: &mut Vec<[F; N]>,
    stop: Stop,
    budget: &mut Budget,
    rng: &mut R,
) -> Result<(), SolveError> {
    // Enough is enough. Checked on entry so that every level above unwinds as soon as the
    // deepest one succeeds, which is what makes this stop at the first point rather than find it
    // first and then keep going.
    if stop == Stop::AtFirst && !solutions.is_empty() {
        return Ok(());
    }

    if remaining == 0 {
        if basis.iter().all(|p| p.is_zero()) {
            solutions.push(*assignment);
            if let Some(limit) = budget.max_solutions {
                if solutions.len() > limit {
                    return Err(SolveError::TooManySolutions { limit });
                }
            }
        }
        return Ok(());
    }

    let index = remaining - 1;
    let candidates = candidate_values(basis, index, rng).unwrap_or_else(|| {
        panic!(
            "variable {} is unconstrained in a zero-dimensional ideal, which the elimination \
             property of lex forbids — see this module's header for the argument",
            index
        )
    });

    for value in candidates {
        if stop == Stop::AtFirst && !solutions.is_empty() {
            return Ok(());
        }
        budget.charge_branch()?;
        assignment[index] = value;
        let substituted: Vec<MultivariatePolynomial<N, F>> =
            basis.iter().map(|p| p.substitute(index, value)).collect();

        // A nonzero constant says this partial assignment already contradicts the system, so the
        // whole subtree below it is dead.
        //
        // **This never fired on any system in the test corpus**, and nor did the all-zero check
        // at the leaf. `candidate_values` keeps only the values satisfying *every* constraint
        // univariate in the current variable, which subsumes most of what these would catch, and
        // a dead branch dies instead by having no candidate roots at all.
        //
        // Both are kept rather than removed, because the argument that they are unreachable is
        // not airtight. A basis polynomial such as `x*y - 1` degenerates to the nonzero constant
        // `-1` if `y` is ever assigned zero, and `y` cannot be assigned zero only because a
        // candidate value is always a coordinate of a genuine solution over the algebraic
        // closure — which holds for a reduced lex basis of a zero-dimensional ideal but is not
        // proved here. A cheap check that bounds the damage from a mistake in that reasoning is
        // worth more than the lines it costs.
        if substituted.iter().any(is_nonzero_constant) {
            continue;
        }

        extend(
            &substituted,
            index,
            assignment,
            solutions,
            stop,
            budget,
            rng,
        )?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rand::{prelude::StdRng, SeedableRng};

    use rand::{CryptoRng, RngCore};

    use super::{
        solve_one, solve_one_with_options, solve_zero_dimensional,
        solve_zero_dimensional_with_options, SolveError, SolveOptions, SolveStrategy,
    };
    use crate::{
        fields::{PrimeFieldElement64, Zp2147483647},
        grobner::{
            benchmark_systems::{cyclic, katsura, planted},
            fglm::FglmError,
            solve,
        },
        FiniteField, MultivariatePolynomial, One, Zero,
    };

    type F = Zp2147483647;

    const STRATEGIES: [SolveStrategy; 2] =
        [SolveStrategy::DirectLexF4, SolveStrategy::GrevlexF4ThenFglm];

    /// `solve_one_with_options`, discarding the statistics. Most tests do not read them.
    fn one<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
        system: &[MultivariatePolynomial<N, F>],
        rng: &mut R,
        options: &SolveOptions,
    ) -> Result<Option<[F; N]>, SolveError> {
        solve_one_with_options(system, rng, options).map(|(found, _)| found)
    }

    /// `solve_zero_dimensional_with_options`, discarding the statistics.
    fn all<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
        system: &[MultivariatePolynomial<N, F>],
        rng: &mut R,
        options: &SolveOptions,
    ) -> Result<Vec<[F; N]>, SolveError> {
        solve_zero_dimensional_with_options(system, rng, options).map(|(found, _)| found)
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

    /// Every point of F^N at which the system vanishes, found by trying all of them.
    ///
    /// Independent of everything under test: no Gröbner basis, no conversion, no pruning. Only
    /// affordable for a small field and few variables, and the strongest oracle available there.
    fn by_exhaustive_search<const N: usize, const P: u64>(
        system: &[MultivariatePolynomial<N, PrimeFieldElement64<P>>],
    ) -> HashSet<[PrimeFieldElement64<P>; N]> {
        type E<const P: u64> = PrimeFieldElement64<P>;
        let elements: Vec<E<P>> = (0..P).map(E::<P>::new).collect();
        let mut found = HashSet::new();
        let mut point = [E::<P>::zero(); N];

        fn walk<const N: usize, const P: u64>(
            system: &[MultivariatePolynomial<N, PrimeFieldElement64<P>>],
            elements: &[PrimeFieldElement64<P>],
            remaining: usize,
            point: &mut [PrimeFieldElement64<P>; N],
            found: &mut HashSet<[PrimeFieldElement64<P>; N]>,
        ) {
            if remaining == 0 {
                if system.iter().all(|p| p.eval(point).is_zero()) {
                    found.insert(*point);
                }
                return;
            }
            let index = remaining - 1;
            for value in elements {
                point[index] = *value;
                walk(system, elements, index, point, found);
            }
        }
        walk(system, &elements, N, &mut point, &mut found);
        found
    }

    /// Both strategies find every solution that exhaustive search finds, over two small fields.
    ///
    /// The headline correctness test. It is also where the two strategies are checked against each
    /// other: a reduced lex basis is unique, so they must agree, and any disagreement is a bug in
    /// the conversion rather than a difference of method.
    #[test]
    fn test_all_solutions_agree_with_exhaustive_search() {
        fn check<const P: u64>(seed: u64) {
            type E<const P: u64> = PrimeFieldElement64<P>;
            let systems: Vec<Vec<&str>> = vec![
                vec!["x - 1", "y - 1"],
                vec!["x + y", "x*y - 1"],
                vec!["x^2 + y^2 - 1", "x - y"],
                vec!["x^2", "y^2"],
                vec!["x^3 - 1", "y - x^2"],
                vec!["x^2 + 1", "y"],
                vec!["x^2 - 1", "y^2 - 1"],
                vec!["x^4 - x", "y^2 - x"],
                vec!["x^2 - 2*x + 1", "y - x"],
            ];
            let mut rng = StdRng::seed_from_u64(seed);

            for system in &systems {
                let f: Vec<MultivariatePolynomial<2, E<P>>> = system
                    .iter()
                    .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
                    .collect();
                let expected = by_exhaustive_search::<2, P>(&f);

                for strategy in STRATEGIES {
                    let options = SolveOptions::with_strategy(strategy);
                    let found: HashSet<_> = all(&f, &mut rng, &options)
                        .unwrap_or_else(|e| {
                            panic!("{:?} over GF({}) with {:?}: {}", system, P, strategy, e)
                        })
                        .into_iter()
                        .collect();
                    assert_eq!(
                        found, expected,
                        "{:?} over GF({}) with {:?}",
                        system, P, strategy
                    );
                }
            }
        }
        check::<5>(1);
        check::<7>(2);
        check::<13>(3);
    }

    /// `solve_one` returns a point exactly when `solve_zero_dimensional` returns a non-empty set,
    /// and that point is one of them.
    #[test]
    fn test_one_solution_is_consistent_with_all_of_them() {
        let mut rng = StdRng::seed_from_u64(11);
        let systems: Vec<Vec<&str>> = vec![
            vec!["x^2 - 1", "y^2 - 1"],
            vec!["x^2 + 1", "y"],
            vec!["x", "x - 1"],
            vec!["x^3 - 1", "y - x^2"],
            vec!["x^2", "y^2"],
        ];

        for system in &systems {
            let f = parse(system, ["x", "y"]);
            let all = solve_zero_dimensional(&f, &mut rng).expect("zero-dimensional");
            let one = solve_one(&f, &mut rng).expect("zero-dimensional");

            assert_eq!(
                one.is_some(),
                !all.is_empty(),
                "{:?}: solve_one and solve_zero_dimensional disagree about solvability",
                system
            );
            if let Some(point) = one {
                assert!(
                    all.contains(&point),
                    "{:?}: {:?} is not a solution",
                    system,
                    point
                );
            }
        }
    }

    /// A system with no base-field solution is `Ok(None)`, not an error.
    ///
    /// `x^2 + 1` over GF(3) is zero-dimensional with quotient dimension two — it has roots in an
    /// extension — and no point in GF(3). Distinguishing that from resource exhaustion is the
    /// whole purpose of the return type.
    #[test]
    fn test_no_base_field_solution_is_not_an_error() {
        type Gf3 = PrimeFieldElement64<3>;
        let mut rng = StdRng::seed_from_u64(13);
        let f: Vec<MultivariatePolynomial<2, Gf3>> = ["x^2 + 1", "y"]
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
            .collect();

        for strategy in STRATEGIES {
            let options = SolveOptions::with_strategy(strategy);
            assert_eq!(
                one(&f, &mut rng, &options).expect("zero-dimensional"),
                None,
                "{:?}",
                strategy
            );
            assert!(all(&f, &mut rng, &options)
                .expect("zero-dimensional")
                .is_empty());
        }
    }

    /// The same system over GF(5), where the roots do lie in the base field.
    #[test]
    fn test_the_same_system_over_a_field_that_contains_its_roots() {
        type Gf5 = PrimeFieldElement64<5>;
        let mut rng = StdRng::seed_from_u64(17);
        let f: Vec<MultivariatePolynomial<2, Gf5>> = ["x^2 + 1", "y"]
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
            .collect();

        let found = solve_zero_dimensional(&f, &mut rng).expect("zero-dimensional");
        assert_eq!(found.len(), 2, "x^2 = -1 has two roots in GF(5)");
        for point in &found {
            assert_eq!(point[0] * point[0], Gf5::zero() - Gf5::one());
            assert!(point[1].is_zero());
        }
    }

    /// The unit ideal has no solutions, and that is `Ok` rather than an error.
    #[test]
    fn test_the_unit_ideal_has_no_solutions() {
        let mut rng = StdRng::seed_from_u64(19);
        let f = parse(&["x", "x - 1"], ["x", "y"]);
        for strategy in STRATEGIES {
            let options = SolveOptions::with_strategy(strategy);
            assert_eq!(one(&f, &mut rng, &options).unwrap(), None);
            assert!(all(&f, &mut rng, &options).unwrap().is_empty());
        }
    }

    /// A positive-dimensional system is refused by both strategies, with the same variant.
    ///
    /// `solve` handles these by enumerating the field; these entry points do not, and say so
    /// rather than returning something that looks like an answer.
    #[test]
    fn test_positive_dimensional_systems_are_refused() {
        let mut rng = StdRng::seed_from_u64(23);
        for strategy in STRATEGIES {
            let options = SolveOptions::with_strategy(strategy);

            let curve = parse(&["x*y - 1"], ["x", "y"]);
            assert_eq!(
                one(&curve, &mut rng, &options).unwrap_err(),
                SolveError::PositiveDimensional,
                "{:?}",
                strategy
            );

            let line = parse(&["x - y"], ["x", "y"]);
            assert_eq!(
                all(&line, &mut rng, &options).unwrap_err(),
                SolveError::PositiveDimensional
            );

            let cyclic_4 = cyclic::<4, F>();
            assert_eq!(
                one(&cyclic_4, &mut rng, &options).unwrap_err(),
                SolveError::PositiveDimensional
            );
        }
    }

    /// An empty system constrains nothing, so it is positive-dimensional and refused.
    ///
    /// `solve` answers this with every point of F^N, which is a different and also correct
    /// answer to a different question.
    #[test]
    fn test_an_empty_system_is_refused() {
        let mut rng = StdRng::seed_from_u64(29);
        let empty: Vec<MultivariatePolynomial<2, F>> = Vec::new();
        assert_eq!(
            solve_one(&empty, &mut rng).unwrap_err(),
            SolveError::PositiveDimensional
        );

        let zeros: Vec<MultivariatePolynomial<2, F>> = vec![MultivariatePolynomial::zero()];
        assert_eq!(
            solve_zero_dimensional(&zeros, &mut rng).unwrap_err(),
            SolveError::PositiveDimensional
        );
    }

    /// The search backtracks: a candidate root that cannot be extended is abandoned.
    ///
    /// Over GF(5), `<y^2 - 1, x^2 - (y + 1)>` gives y two candidates. At y = 1 the next constraint
    /// is `x^2 = 2`, which has no root in GF(5), so that whole branch dies; at y = -1 it is
    /// `x^2 = 0`, giving x = 0. So the solver must try both values of y and accept only one — and
    /// which it tries first depends on `roots`, so it has to handle either order.
    #[test]
    fn test_the_search_backtracks_past_a_dead_branch() {
        type Gf5 = PrimeFieldElement64<5>;
        let f: Vec<MultivariatePolynomial<2, Gf5>> = ["y^2 - 1", "x^2 - y - 1"]
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
            .collect();

        let expected = by_exhaustive_search::<2, 5>(&f);
        assert_eq!(expected.len(), 1, "the premise of the test");

        // Several seeds, since the order `roots` returns candidates in is not specified.
        for seed in 0..8u64 {
            let mut rng = StdRng::seed_from_u64(seed);
            let one = solve_one(&f, &mut rng).expect("zero-dimensional");
            assert_eq!(
                one,
                expected.iter().copied().next(),
                "seed {} did not reach the only solution",
                seed
            );
        }
    }

    /// The planted point is recovered, in four, six and eight variables.
    #[test]
    fn test_the_planted_point_is_recovered() {
        let mut rng = StdRng::seed_from_u64(31);

        macro_rules! check {
            ($n:literal) => {{
                let point: Vec<F> = (0..$n).map(|i| F::new(2 * i as u64 + 3)).collect();
                let expected: [F; $n] = point.clone().try_into().unwrap();
                let system = planted::<$n, F>(&point);

                for strategy in STRATEGIES {
                    let options = SolveOptions::with_strategy(strategy);
                    let all = all(&system, &mut rng, &options)
                        .unwrap_or_else(|e| panic!("planted-{} with {:?}: {}", $n, strategy, e));
                    assert!(
                        all.contains(&expected),
                        "planted-{} with {:?}: the planted point is not among {} solutions",
                        $n,
                        strategy,
                        all.len()
                    );
                    // And one solution is found without enumerating them all.
                    let one = one(&system, &mut rng, &options)
                        .unwrap()
                        .expect("a solution exists");
                    for p in &system {
                        assert!(
                            p.eval(&one).is_zero(),
                            "planted-{}: {} is not satisfied",
                            $n,
                            p
                        );
                    }
                }
            }};
        }

        check!(4);
        check!(6);
        check!(8);
    }

    /// The benchmark corpus solves, by both routes, with the same answers.
    #[test]
    fn test_the_benchmark_corpus_solves_the_same_way_by_both_routes() {
        let mut rng = StdRng::seed_from_u64(37);

        macro_rules! check {
            ($system:expr, $name:literal) => {{
                let system = $system;
                let direct = all(
                    &system,
                    &mut rng,
                    &SolveOptions::with_strategy(SolveStrategy::DirectLexF4),
                )
                .unwrap_or_else(|e| panic!("{} direct: {}", $name, e));
                let converted = all(
                    &system,
                    &mut rng,
                    &SolveOptions::with_strategy(SolveStrategy::GrevlexF4ThenFglm),
                )
                .unwrap_or_else(|e| panic!("{} converted: {}", $name, e));

                let a: HashSet<_> = direct.into_iter().collect();
                let b: HashSet<_> = converted.into_iter().collect();
                assert_eq!(a, b, "{}: the two strategies disagree", $name);
            }};
        }

        check!(cyclic::<3, F>(), "cyclic-3");
        check!(katsura::<3, F>(), "katsura-3");
        check!(katsura::<4, F>(), "katsura-4");
        check!(katsura::<5, F>(), "katsura-5");
    }

    /// Solving over a field far too large to enumerate.
    ///
    /// The property that distinguishes these entry points from `solve`: no variable is ever free
    /// for a zero-dimensional ideal, so the field's size never enters the search. `solve` has a
    /// `MAX_FIELD_ORDER` of 2^20 for the positive-dimensional case; this field is two thousand
    /// times larger and the question does not arise.
    #[test]
    fn test_solving_over_a_field_too_large_to_enumerate() {
        let mut rng = StdRng::seed_from_u64(41);
        let f = parse(&["x^2 - 4", "y - x"], ["x", "y"]);

        let found: HashSet<_> = solve_zero_dimensional(&f, &mut rng)
            .expect("zero-dimensional")
            .into_iter()
            .collect();
        let minus_two = F::zero() - F::new(2);
        assert_eq!(
            found,
            HashSet::from([[F::new(2), F::new(2)], [minus_two, minus_two]])
        );
    }

    /// The legacy `solve` and the new solver agree on zero-dimensional systems.
    ///
    /// `solve` is unchanged by this milestone, and this is what says so from the outside.
    #[test]
    fn test_the_legacy_solver_agrees_on_zero_dimensional_systems() {
        type Gf7 = PrimeFieldElement64<7>;
        let mut rng = StdRng::seed_from_u64(43);
        let systems: Vec<Vec<&str>> = vec![
            vec!["x - 1", "y - 2"],
            vec!["x + y", "x*y - 1"],
            vec!["x^2", "y^2"],
            vec!["x^3 - 1", "y - x^2"],
            vec!["x^2 + 1", "y"],
        ];

        for system in &systems {
            let f: Vec<MultivariatePolynomial<2, Gf7>> = system
                .iter()
                .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
                .collect();
            let legacy: HashSet<_> = solve(&f, &mut rng).into_iter().collect();
            let new: HashSet<_> = solve_zero_dimensional(&f, &mut rng)
                .expect("zero-dimensional")
                .into_iter()
                .collect();
            assert_eq!(legacy, new, "{:?}", system);
        }
    }

    /// A branch budget below what the search needs is a structured error.
    #[test]
    fn test_the_branch_budget_is_enforced() {
        let mut rng = StdRng::seed_from_u64(47);
        let f = parse(&["x^3 - 1", "y^3 - 1"], ["x", "y"]);

        let mut options = SolveOptions {
            max_branches: Some(1),
            ..SolveOptions::default()
        };
        assert_eq!(
            all(&f, &mut rng, &options).unwrap_err(),
            SolveError::TooManyBranches { limit: 1 }
        );

        // A budget of zero forbids the first candidate, rather than being rejected as invalid.
        options.max_branches = Some(0);
        assert_eq!(
            one(&f, &mut rng, &options).unwrap_err(),
            SolveError::TooManyBranches { limit: 0 }
        );

        // And a generous budget succeeds.
        options.max_branches = Some(1000);
        assert!(all(&f, &mut rng, &options).is_ok());
    }

    /// A solution budget below the true count is an error, not a truncated list.
    #[test]
    fn test_the_solution_budget_is_enforced() {
        let mut rng = StdRng::seed_from_u64(53);
        // Nine solutions: three cube roots of one for each variable.
        let f = parse(&["x^3 - 1", "y^3 - 1"], ["x", "y"]);
        assert_eq!(
            solve_zero_dimensional(&f, &mut rng)
                .expect("zero-dimensional")
                .len(),
            9
        );

        let mut options = SolveOptions::default();
        for limit in 0..9 {
            options.max_solutions = Some(limit);
            assert_eq!(
                all(&f, &mut rng, &options).unwrap_err(),
                SolveError::TooManySolutions { limit },
                "a limit of {} should have been exceeded",
                limit
            );
        }
        options.max_solutions = Some(9);
        assert_eq!(
            all(&f, &mut rng, &options)
                .expect("exactly at the limit")
                .len(),
            9
        );

        // `solve_one` ignores the limit, since it stops at one by construction.
        options.max_solutions = Some(0);
        assert!(one(&f, &mut rng, &options)
            .expect("the limit does not apply")
            .is_some());
    }

    /// `solve_one` stops early: it explores far fewer branches than finding every solution does.
    ///
    /// The point of having a separate entry point rather than taking the first of all solutions.
    /// Measured through the branch budget, which is the only observable the search exposes: a
    /// budget that is ample for one solution but not for nine.
    #[test]
    fn test_finding_one_solution_explores_fewer_branches() {
        let mut rng = StdRng::seed_from_u64(59);
        let f = parse(&["x^3 - 1", "y^3 - 1"], ["x", "y"]);

        let options = SolveOptions {
            max_branches: Some(4),
            ..SolveOptions::default()
        };

        assert!(one(&f, &mut rng, &options)
            .expect("one solution is within four branches")
            .is_some());
        assert_eq!(
            all(&f, &mut rng, &options).unwrap_err(),
            SolveError::TooManyBranches { limit: 4 },
            "all nine solutions should not fit in four branches"
        );
    }

    /// Neither strategy dominates: each has a system the other cannot solve.
    ///
    /// This is why the choice is the caller's and why no heuristic makes it. The conversion is the
    /// only route to katsura-7, whose lex basis crosses F4's live-nonzero limit. planted-14 goes
    /// the other way: its quotient dimension is 4^7 = 16384, past what the conversion will build,
    /// while its lex basis is trivial and the direct route solves it in milliseconds.
    ///
    /// katsura-7 is left to `examples/solve_one.rs` because it costs 80 ms in release and far more
    /// in debug. The direction that is cheap to assert is the one below.
    #[test]
    fn test_neither_strategy_dominates() {
        let mut rng = StdRng::seed_from_u64(67);
        let point: Vec<F> = (0..14).map(|i| F::new(2 * i as u64 + 3)).collect();
        let system = planted::<14, F>(&point);

        // The conversion refuses: 16384 standard monomials against a limit of 4096.
        let converted = one(
            &system,
            &mut rng,
            &SolveOptions::with_strategy(SolveStrategy::GrevlexF4ThenFglm),
        );
        assert_eq!(
            converted.unwrap_err(),
            SolveError::Fglm(FglmError::QuotientDimensionExceeded { limit: 4096 }),
            "planted-14 should outgrow the conversion"
        );

        // The direct route solves it, and the planted point is the answer.
        let expected: [F; 14] = point.clone().try_into().unwrap();
        let found = one(
            &system,
            &mut rng,
            &SolveOptions::with_strategy(SolveStrategy::DirectLexF4),
        )
        .expect("the direct route handles it")
        .expect("a solution exists");
        for p in &system {
            assert!(p.eval(&found).is_zero(), "{} is not satisfied", p);
        }
        // Not asserted to *be* the planted point: the system has many solutions and which one
        // `solve_one` reaches is unspecified. That the planted one is among them is checked by
        // `test_the_planted_point_is_recovered`.
        let _ = expected;
    }

    /// A conversion budget below what the system needs surfaces as `SolveError::Fglm`.
    ///
    /// The cheap version of the test above: the same refusal, forced with options rather than by
    /// finding a system large enough to trigger it.
    #[test]
    fn test_a_conversion_limit_is_reported_as_such() {
        let mut rng = StdRng::seed_from_u64(71);
        let system = katsura::<5, F>();

        let mut options = SolveOptions::with_strategy(SolveStrategy::GrevlexF4ThenFglm);
        options.fglm.max_quotient_dimension = 8;
        assert_eq!(
            one(&system, &mut rng, &options).unwrap_err(),
            SolveError::Fglm(FglmError::QuotientDimensionExceeded { limit: 8 })
        );

        // The direct route is unaffected by a conversion limit, since it does not convert.
        let mut options = SolveOptions::with_strategy(SolveStrategy::DirectLexF4);
        options.fglm.max_quotient_dimension = 8;
        assert!(one(&system, &mut rng, &options).is_ok());
    }

    /// An F4 budget below what the basis needs surfaces as `SolveError::Grobner`.
    #[test]
    fn test_a_grobner_limit_is_reported_as_such() {
        let mut rng = StdRng::seed_from_u64(73);
        let system = katsura::<5, F>();

        let mut options = SolveOptions::default();
        options.f4.max_matrix_rows = 2;
        assert!(matches!(
            one(&system, &mut rng, &options).unwrap_err(),
            SolveError::Grobner(_)
        ));
    }

    /// The statistics account for the work, and show what the clock only implies.
    ///
    /// `<x^3 - 1, y^3 - 1>` has nine solutions and a search tree of 3 + 9 = 12 candidate
    /// assignments: three roots for y, and three for x under each. Finding one solution charges
    /// two branches — one value of y, one of x — so the ratio is six, before any timing is
    /// involved.
    #[test]
    fn test_the_statistics_account_for_the_search() {
        let mut rng = StdRng::seed_from_u64(79);
        let f = parse(&["x^3 - 1", "y^3 - 1"], ["x", "y"]);
        let options = SolveOptions::default();

        let (every, all_statistics) =
            solve_zero_dimensional_with_options(&f, &mut rng, &options).expect("zero-dimensional");
        assert_eq!(all_statistics.solutions, every.len());
        assert_eq!(all_statistics.solutions, 9);
        assert_eq!(all_statistics.branches, 12);
        assert_eq!(all_statistics.lex_basis_elements, f.len());
        // The direct strategy converts nothing, so there is nothing to report.
        assert_eq!(all_statistics.fglm, None);

        let (first, one_statistics) =
            solve_one_with_options(&f, &mut rng, &options).expect("zero-dimensional");
        assert!(first.is_some());
        assert_eq!(one_statistics.solutions, 1);
        assert_eq!(
            one_statistics.branches, 2,
            "one solution costs one value of each variable"
        );
    }

    /// Under the conversion strategy the statistics carry the quotient dimension and its cost.
    #[test]
    fn test_the_statistics_report_the_conversion() {
        let mut rng = StdRng::seed_from_u64(83);
        let options = SolveOptions::with_strategy(SolveStrategy::GrevlexF4ThenFglm);

        let (_, statistics) =
            solve_zero_dimensional_with_options(&katsura::<5, F>(), &mut rng, &options)
                .expect("zero-dimensional");

        let fglm = statistics.fglm.expect("the conversion ran");
        assert_eq!(fglm.quotient_dimension, 16, "katsura-5 has D = 2^4");
        assert_eq!(fglm.candidates_independent, 16);
        assert_eq!(fglm.candidates_dependent, statistics.lex_basis_elements);
        assert!(fglm.operator_entries > 0);
        assert!(fglm.span_row_operations > 0);

        // The storage estimate is the operators plus the dependence test, and nothing else.
        assert_eq!(
            fglm.estimated_bytes(),
            fglm.operator_entries * 16 + 2 * 16 * 16 * 8
        );
    }

    /// Returned solutions are distinct, with no deduplication step.
    ///
    /// Each level of the search tries distinct roots, so two complete assignments differ in at
    /// least one coordinate. Checked on a system with many solutions rather than argued.
    #[test]
    fn test_the_solutions_are_distinct() {
        let mut rng = StdRng::seed_from_u64(61);
        let f = parse(&["x^5 - x", "y^5 - y"], ["x", "y"]);
        let all = solve_zero_dimensional(&f, &mut rng).expect("zero-dimensional");
        let distinct: HashSet<_> = all.iter().copied().collect();
        assert_eq!(all.len(), distinct.len(), "{:?} contains a repeat", all);
    }
}
