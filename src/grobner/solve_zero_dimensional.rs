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
        f4_reported,
        fglm::{classify_ideal, fglm_to_lex_with_options, FglmError, FglmOptions, FglmStatistics},
        solve::{candidate_values, is_nonzero_constant},
        F4Error, F4Options, F4Statistics, StopKind,
    },
    FiniteField, KnownOrder, MonomialOrder, MultivariatePolynomial,
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
///
/// Not `Copy` since M21-C, because [`F4Statistics`] is not — the same reason
/// [`SolveOptions`] is not.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SolveStatistics {
    /// Elements of the lexicographic basis the search ran on.
    pub lex_basis_elements: usize,

    /// Candidate assignments tried, across the whole search.
    pub branches: usize,

    /// Distinct solutions returned.
    pub solutions: usize,

    /// The lexicographic basis contained a nonzero constant, so `1` is in the ideal.
    ///
    /// The distinction that was otherwise lost. An inconsistent system and a zero-dimensional one
    /// with no point over `F` both return no solutions, and they are different mathematical facts;
    /// this is which of the two happened. [`SolveOutcome`] is the typed form.
    pub inconsistent: bool,

    /// What the Gröbner basis computation did.
    ///
    /// `None` only if it was never reached. Both routes compute one — under
    /// [`SolveStrategy::GrevlexF4ThenFglm`] this is the *source* basis, under
    /// [`SolveStrategy::DirectLexF4`] it is the lex basis itself.
    ///
    /// Carried since M21-C. It was computed and discarded before, which left a caller unable to
    /// say what either route cost and left `examples/solve_baseline.rs` re-running the whole
    /// pipeline to find out.
    pub f4: Option<F4Statistics>,

    /// What the conversion did, or `None` under [`SolveStrategy::DirectLexF4`].
    pub fglm: Option<FglmStatistics>,

    /// What the dimension diagnosis cost, or `None` if none was needed.
    ///
    /// Present only on a [`SolveStrategy::DirectLexF4`] attempt whose F4 run crossed a resource
    /// limit: there is then no lex basis to classify, so the route computes a *grevlex* one to
    /// find out whether the ideal was positive-dimensional all along (#376). Separate from
    /// [`Self::f4`] rather than folded into it, because the two are different computations under
    /// different orders and a sum would report a batch count no single basis ever had.
    pub diagnosis: Option<F4Statistics>,
}

impl SolveStatistics {
    /// Estimated bytes the largest stage held at once.
    ///
    /// The **maximum** of the Gröbner stage's estimate and the conversion's, not their sum: F4's
    /// matrices are dropped before the conversion allocates anything, so the two peaks are not
    /// live together and adding them would overstate the high-water mark.
    ///
    /// An *estimate*, of the representation only. It omits what
    /// [`F4Options::max_live_bytes`](crate::grobner::F4Options::max_live_bytes) omits — the
    /// monomial-to-column map, the basis's term vectors, the backend's dense buffer, allocator
    /// overhead — and it omits the back-substitution search entirely. For the measured figure use
    /// [`peak_resident_bytes`](crate::util::peak_resident_bytes); on katsura-7 under lex the two
    /// differ by 4.1x, and §1.2 of `docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md` is why.
    pub fn estimated_peak_bytes(&self) -> usize {
        let grobner = self.f4.as_ref().map_or(0, |s| s.max_estimated_bytes);
        let conversion = self.fglm.as_ref().map_or(0, |s| s.estimated_bytes());
        // The diagnosis is a third stage under the same rule: it starts after the failed lex
        // attempt's matrices are freed, so it enters the maximum and not a sum.
        let diagnosis = self.diagnosis.as_ref().map_or(0, |s| s.max_estimated_bytes);
        grobner.max(conversion).max(diagnosis)
    }
}

/// What a solve attempt established, as distinct mathematical facts.
///
/// [`solve_one`] returns `Option<[F; N]>`, which collapses two of these: an inconsistent system
/// and a zero-dimensional one with no point over `F` are both `None`. They are different answers
/// to a cryptanalytic question — the first says the equations contradict each other, the second
/// says the variety is nonempty over an extension and has no base-field point — so
/// [`solve_one_with_outcome`] returns this instead.
///
/// **Every variant is an answer.** A crossed budget is a [`SolveError`] and can never appear here,
/// which is the invariant that keeps a resource failure from being read as "no solution".
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SolveOutcome<const N: usize, F: FiniteField> {
    /// A point, already verified against the original generators.
    Point([F; N]),

    /// The ideal is zero-dimensional and has no point over the base field.
    ///
    /// `x^2 + 1` over GF(3) is the small case: quotient dimension two, no roots.
    NoBaseFieldPoint,

    /// `1` is in the ideal, so the system has no solution over any extension either.
    Inconsistent,
}

impl<const N: usize, F: FiniteField> SolveOutcome<N, F> {
    /// The point, if there is one. The bridge to [`solve_one`]'s older return type.
    pub fn point(&self) -> Option<[F; N]> {
        match self {
            Self::Point(p) => Some(*p),
            _ => None,
        }
    }
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
    ///
    /// Reported by both strategies, and since #376 from a grevlex basis computed for the purpose
    /// when the direct route's own lex basis never materialized — see [`explain_lex_failure`].
    /// Nothing a budget can be raised to will help; for a system over a small field the usual
    /// remedy is [`with_field_equations`](super::with_field_equations).
    PositiveDimensional,

    /// The Gröbner basis computation crossed one of its limits.
    Grobner(F4Error),

    /// The conversion crossed one of its limits.
    Fglm(FglmError),

    /// The conversion was **not attempted**: a computed quotient dimension put it out of budget.
    ///
    /// Distinct from `Fglm(FglmError::SpanStorageExceeded)`, which means the conversion ran and
    /// crossed the limit. Here nothing was spent on it at all — the source basis exists and its
    /// quotient basis was enumerated, and that was enough to know the conversion could not fit. A
    /// predicted crossing reported as a real one would misattribute the cost.
    ///
    /// Produced only by the policy layer; the explicit strategies never predict.
    ConversionInfeasible {
        /// `D`, counted rather than estimated.
        dimension: usize,
        /// What the dense blocks would need, in the unit of the budget that bound.
        needed: usize,
        /// That budget's value.
        limit: usize,
        /// Which budget bound: `"span cells"` or `"span bytes"`.
        ///
        /// Named, because the two are different quantities over a wide field — a cell is 8 bytes
        /// over a 64-bit prime field and 32 over BN254 — and quoting one budget's value against
        /// the other's requirement would be wrong by that factor.
        budget: &'static str,
    },

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
            Self::ConversionInfeasible {
                dimension,
                needed,
                limit,
                budget,
            } => write!(
                f,
                "conversion was not attempted: quotient dimension {} needs {} {}, over the limit \
                 of {}",
                dimension, needed, budget, limit
            ),
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

impl SolveError {
    /// Whether this failure is about resources rather than about the ideal.
    ///
    /// The distinction a fallback turns on. [`Self::PositiveDimensional`] is a property of the
    /// ideal, so the other route would refuse it identically and trying is pure waste; an
    /// unsatisfiable `F4Options` is a caller error with the same property. Everything else is a
    /// budget, and a different route may fit a different one.
    pub fn is_resource_failure(&self) -> bool {
        !matches!(
            self,
            Self::PositiveDimensional
                | Self::Grobner(F4Error::InvalidOptions { .. })
                // Predicted infeasibility is not a spent budget. It is a *reason to switch*, which
                // the planner acts on directly, so it must not also license a retry of the route
                // that was just ruled out.
                | Self::ConversionInfeasible { .. }
        )
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
    /// reports one. The conversion is on the grevlex route only, and that route always has a basis
    /// to classify; the direct route reaches the same variant through [`explain_lex_failure`] when
    /// it has none.
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
pub fn solve_one<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
) -> Result<Option<[F; N]>, SolveError> {
    solve_one_with_options(system, rng, &SolveOptions::default()).map(|(found, _)| found)
}

/// As [`solve_one`], under the given strategy and budgets, additionally reporting the work done.
#[allow(clippy::type_complexity)]
pub fn solve_one_with_options<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
    options: &SolveOptions,
) -> Result<(Option<[F; N]>, SolveStatistics), SolveError> {
    solve_one_with_outcome(system, rng, options)
        .map(|(outcome, statistics)| (outcome.point(), statistics))
}

/// As [`solve_one_with_options`], distinguishing the two reasons there might be no point.
///
/// The entry point M21-C added, and the one to prefer when the *answer* matters rather than only
/// the point: `Ok(None)` cannot say whether the equations contradicted each other or merely had no
/// base-field solution, and [`SolveOutcome`] can. Nothing else differs — the same route, the same
/// budgets, the same statistics, and the same verification of the returned point against the
/// original generators.
///
/// # Errors
/// As [`solve_one`]. A crossed budget is an error here too, and **never** a `NoBaseFieldPoint`.
#[allow(clippy::type_complexity)]
pub fn solve_one_with_outcome<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
    options: &SolveOptions,
) -> Result<(SolveOutcome<N, F>, SolveStatistics), SolveError> {
    let (outcome, statistics) = solve_one_reported(system, rng, options);
    outcome.map(|outcome| (outcome, statistics))
}

/// As [`solve_one_with_outcome`], returning the statistics even when the attempt fails.
///
/// The diagnostic entry point, and the analogue of
/// [`f4_reported`](crate::grobner::f4_reported) one level up. A route that fails has still done
/// work, and which work it did is the question a planner has to answer before it decides whether
/// to try the other one:
///
/// - a positive-dimensional system has a **complete** Gröbner basis behind the refusal: under
///   [`SolveStrategy::GrevlexF4ThenFglm`] it is `statistics.f4`, and under
///   [`SolveStrategy::DirectLexF4`] whose lex attempt crossed a budget it is the grevlex basis in
///   `statistics.diagnosis`, with `statistics.f4` describing the attempt that failed;
/// - a conversion that crosses its span budget has a complete *source* basis behind it, so
///   `statistics.f4` is present and `statistics.fglm` is not;
/// - an F4 computation that crosses a budget has no basis at all, and `statistics.f4` still says
///   how many batches it got through and how large the matrices became.
///
/// `solve_one_with_outcome` discards exactly that, because a `SolveError` cannot carry it: the
/// error type is `Copy`, every caller matches on it exhaustively, and putting work inside a failure
/// would conflate the two. Hence a tuple.
///
/// **Statistics are never an answer.** The outcome is in the `Result`, so a crossed budget has no
/// `SolveOutcome` to be mistaken for one.
#[allow(clippy::type_complexity)]
pub fn solve_one_reported<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
    options: &SolveOptions,
) -> (Result<SolveOutcome<N, F>, SolveError>, SolveStatistics) {
    let mut statistics = SolveStatistics::default();
    let outcome = solve_one_into(system, rng, options, &mut statistics);
    (outcome, statistics)
}

/// One solve, accumulating into a caller-owned `statistics`.
fn solve_one_into<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
    options: &SolveOptions,
    statistics: &mut SolveStatistics,
) -> Result<SolveOutcome<N, F>, SolveError> {
    let basis = lex_basis(system, options, statistics)?;
    solve_from_lex_basis_into(&basis, system, options, statistics, rng)
}

/// One point of `system`, from a lexicographic Gröbner basis already in hand.
///
/// The back-substitution half of [`solve_one_with_outcome`], split out so that a caller which
/// reached the lex basis by its own route — a planner weighing the two, a specialization that
/// solved a reduced system — runs the same search rather than a second copy of it.
///
/// `basis` must be a Gröbner basis of `system` under
/// [`MonomialOrder::Lexicographic`]. That is a precondition and is not checked, because checking it
/// means recomputing the basis; what *is* checked is zero-dimensionality, so a basis of the wrong
/// shape is refused rather than reaching the search's internal invariant.
///
/// The point is verified against `system` — the original generators, not `basis` — before it is
/// returned, exactly as the ordinary entry points do.
///
/// # Errors
/// [`SolveError::PositiveDimensional`] if `basis` does not generate a zero-dimensional ideal, or a
/// resource variant if a search limit in `options` is crossed.
pub fn solve_from_lex_basis<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    basis: &[MultivariatePolynomial<N, F>],
    system: &[MultivariatePolynomial<N, F>],
    options: &SolveOptions,
    rng: &mut R,
) -> Result<(SolveOutcome<N, F>, SolveStatistics), SolveError> {
    let mut statistics = SolveStatistics::default();
    let outcome = solve_from_lex_basis_into(basis, system, options, &mut statistics, rng);
    outcome.map(|outcome| (outcome, statistics))
}

/// [`solve_from_lex_basis`], accumulating into a caller-owned `statistics`.
fn solve_from_lex_basis_into<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    basis: &[MultivariatePolynomial<N, F>],
    system: &[MultivariatePolynomial<N, F>],
    options: &SolveOptions,
    statistics: &mut SolveStatistics,
    rng: &mut R,
) -> Result<SolveOutcome<N, F>, SolveError> {
    // The unit ideal is zero-dimensional and `classify_ideal` says so, so this check does not
    // reject an inconsistent system; `search` reports that one as `Inconsistent` below.
    if !classify_ideal(basis, MonomialOrder::Lexicographic).is_finite_dimensional() {
        return Err(SolveError::PositiveDimensional);
    }
    let found = search(basis, system, Stop::AtFirst, options, statistics, rng)?;

    Ok(match found.into_iter().next() {
        Some(point) => SolveOutcome::Point(point),
        // `search` has already set `inconsistent` from the basis, so this reads a fact rather than
        // re-deriving one.
        None if statistics.inconsistent => SolveOutcome::Inconsistent,
        None => SolveOutcome::NoBaseFieldPoint,
    })
}

/// Every distinct solution of `system` over `F`.
///
/// The order is unspecified. Distinctness is automatic rather than enforced: each level of the
/// search tries distinct roots, so two complete assignments differ in at least one coordinate.
///
/// # Errors
/// As [`solve_one`], plus [`SolveError::TooManySolutions`]. The result is never a truncated list.
pub fn solve_zero_dimensional<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
) -> Result<Vec<[F; N]>, SolveError> {
    solve_zero_dimensional_with_options(system, rng, &SolveOptions::default())
        .map(|(found, _)| found)
}

/// As [`solve_zero_dimensional`], under the given strategy and budgets.
pub fn solve_zero_dimensional_with_options<
    const N: usize,
    F: KnownOrder,
    R: RngCore + CryptoRng,
>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
    options: &SolveOptions,
) -> Result<(Vec<[F; N]>, SolveStatistics), SolveError> {
    let mut statistics = SolveStatistics::default();
    let basis = lex_basis(system, options, &mut statistics)?;
    let found = search(&basis, system, Stop::AtEvery, options, &mut statistics, rng)?;
    Ok((found, statistics))
}

/// The lexicographic Gröbner basis of a zero-dimensional system, by the chosen route.
///
/// Zero-dimensionality is decided from whichever basis the strategy computes first, which is the
/// grevlex one where there is a choice: classification is a question about leading monomials and
/// costs the same under any order, so it is asked of the cheaper basis.
///
/// `statistics` is filled in as each stage completes, **including when a later stage refuses**: a
/// positive-dimensional classification and a crossed span budget both sit behind a Gröbner basis
/// that really was computed, and discarding its counters would make the two failures look free.
fn lex_basis<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    options: &SolveOptions,
    statistics: &mut SolveStatistics,
) -> Result<Vec<MultivariatePolynomial<N, F>>, SolveError> {
    let order = match options.strategy {
        SolveStrategy::DirectLexF4 => MonomialOrder::Lexicographic,
        SolveStrategy::GrevlexF4ThenFglm => MonomialOrder::GradedReverseLexicographic,
    };

    // `f4_reported` rather than `f4_with_options`, so that a crossed F4 budget still says how many
    // batches it managed and how large the matrices became.
    let (basis, f4) = f4_reported(system, order, &options.f4);
    statistics.f4 = Some(f4);
    let basis = match basis {
        Ok(basis) => basis,
        Err(e) => {
            // A crossed lex budget leaves nothing to classify, so the route cannot tell a system
            // too large for the budget from one whose lex basis the search could never use. Only
            // the direct route needs asking: the other one already has a grevlex basis or failed
            // to get one.
            let diagnose = options.strategy == SolveStrategy::DirectLexF4;
            let (error, diagnosis) = explain_lex_failure(system, e, &options.f4, diagnose);
            statistics.diagnosis = diagnosis;
            return Err(error);
        }
    };

    // Classified from whichever basis the route computed first, which is the grevlex one where
    // there is a choice: classification is a question about leading monomials and costs the same
    // under any order, so it is asked of the cheaper basis. Doing it here rather than inside the
    // conversion also means a positive-dimensional system costs no quotient algebra and reports
    // the same variant under either route.
    if !classify_ideal(&basis, order).is_finite_dimensional() {
        return Err(SolveError::PositiveDimensional);
    }

    match options.strategy {
        SolveStrategy::DirectLexF4 => Ok(basis),
        SolveStrategy::GrevlexF4ThenFglm => {
            let (lex, fglm) = fglm_to_lex_with_options(&basis, order, &options.fglm)?;
            statistics.fglm = Some(fglm);
            Ok(lex)
        }
    }
}

/// What a crossed F4 budget under lex really means, and what finding out cost.
///
/// The fix for #376. A direct-lex attempt that crosses a resource limit has no basis to classify,
/// so a positive-dimensional ideal and a system merely too large for the budget arrive as the same
/// `F4Error` — and the resource reading is the actively harmful one, since raising
/// `max_matrix_columns` cannot produce a lex basis the search can use. A **grevlex** basis settles
/// it: classification is a question about leading monomials and is the same under any order, and
/// degrevlex keeps the matrices small on much of what lex elimination blows up on.
///
/// # It cannot relabel a genuine resource failure
///
/// [`SolveError::PositiveDimensional`] is returned only from a **complete** grevlex basis whose
/// leading monomials omit a pure power of some variable, which is a proof about the ideal and not
/// an inference from the failure. A grevlex run that crosses the budget too, or one that completes
/// and is zero-dimensional, leaves `error` exactly as it was.
///
/// # What it costs, and when it is declined
///
/// At most one more basis computation, under the same [`F4Options`] the caller already consented
/// to, and only on a path that has already failed. Declined when `diagnose` is false, and when the
/// crossed limit was not a resource one:
///
/// - [`StopKind::Time`] — a caller who bounded wall clock would have it silently doubled, and that
///   budget is the one resource a second computation cannot help spending;
/// - [`StopKind::Caller`] — unsatisfiable options would refuse the grevlex run identically;
/// - [`StopKind::Certification`] — a basis that failed its own check is a defect, not a dimension.
pub(crate) fn explain_lex_failure<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    error: F4Error,
    options: &F4Options,
    diagnose: bool,
) -> (SolveError, Option<F4Statistics>) {
    if !diagnose || error.stop_kind() != StopKind::Resource {
        return (SolveError::Grobner(error), None);
    }

    let grevlex = MonomialOrder::GradedReverseLexicographic;
    let (basis, statistics) = f4_reported(system, grevlex, options);
    let positive_dimensional =
        basis.is_ok_and(|basis| !classify_ideal(&basis, grevlex).is_finite_dimensional());

    let error = if positive_dimensional {
        SolveError::PositiveDimensional
    } else {
        SolveError::Grobner(error)
    };
    (error, Some(statistics))
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
fn search<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    basis: &[MultivariatePolynomial<N, F>],
    system: &[MultivariatePolynomial<N, F>],
    stop: Stop,
    options: &SolveOptions,
    statistics: &mut SolveStatistics,
    rng: &mut R,
) -> Result<Vec<[F; N]>, SolveError> {
    statistics.lex_basis_elements = basis.len();

    // The unit ideal: the system is inconsistent, so there is nothing to search. Recorded as
    // well as acted on, because "no solutions because 1 is in the ideal" and "no solutions in this
    // field" are different answers and the caller cannot otherwise tell them apart.
    if basis.iter().any(is_nonzero_constant) {
        statistics.inconsistent = true;
        return Ok(Vec::new());
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
    Ok(solutions)
}

/// One level of the back-substitution.
///
/// `basis` always has the already-assigned variables substituted in, so at the deepest level every
/// polynomial is a constant.
fn extend<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
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
    use std::{collections::HashSet, mem::size_of, time::Duration};

    use rand::{prelude::StdRng, SeedableRng};

    use rand::{CryptoRng, RngCore};

    use super::{
        solve_one, solve_one_reported, solve_one_with_options, solve_zero_dimensional,
        solve_zero_dimensional_with_options, SolveError, SolveOptions, SolveStrategy,
    };
    use crate::{
        fields::{PrimeFieldElement64, Zp2147483647},
        grobner::{
            benchmark_systems::{cyclic, katsura, planted},
            f4_with_options,
            fglm::{classify_ideal, FglmError},
            solve, F4Error, F4Options,
        },
        FiniteField, KnownOrder, MonomialOrder, MultivariatePolynomial, One, Zero,
    };

    type F = Zp2147483647;

    const STRATEGIES: [SolveStrategy; 2] =
        [SolveStrategy::DirectLexF4, SolveStrategy::GrevlexF4ThenFglm];

    /// `solve_one_with_options`, discarding the statistics. Most tests do not read them.
    fn one<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
        system: &[MultivariatePolynomial<N, F>],
        rng: &mut R,
        options: &SolveOptions,
    ) -> Result<Option<[F; N]>, SolveError> {
        solve_one_with_options(system, rng, options).map(|(found, _)| found)
    }

    /// `solve_zero_dimensional_with_options`, discarding the statistics.
    fn all<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
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

    /// A positive-dimensional ideal whose lex basis is out of budget is still named as such.
    ///
    /// #376: the direct route has no basis to classify when F4 under lex crosses a budget, so it
    /// used to blame the budget for a property of the ideal. katsura-6 less one equation is the
    /// small instance — its lex matrices pass 1000 columns, its grevlex basis does not.
    #[test]
    fn test_a_positive_dimensional_ideal_is_not_blamed_on_the_matrix_budget() {
        let mut system = katsura::<6, F>();
        system.pop();
        let f4 = F4Options {
            max_matrix_rows: 1000,
            max_matrix_columns: 1000,
            ..Default::default()
        };

        // The premise: lex is out of reach at this budget and grevlex is not.
        assert!(f4_with_options(&system, MonomialOrder::Lexicographic, &f4).is_err());

        for strategy in STRATEGIES {
            let options = SolveOptions {
                f4: f4.clone(),
                ..SolveOptions::with_strategy(strategy)
            };
            let (outcome, statistics) =
                solve_one_reported(&system, &mut StdRng::seed_from_u64(31), &options);
            assert_eq!(
                outcome.unwrap_err(),
                SolveError::PositiveDimensional,
                "{:?}",
                strategy
            );
            // The grevlex route classifies its own basis; the direct one needs a diagnosis.
            assert_eq!(
                statistics.diagnosis.is_some(),
                strategy == SolveStrategy::DirectLexF4,
                "{:?}",
                strategy
            );
        }
    }

    /// A zero-dimensional ideal that really is out of budget keeps its resource failure.
    ///
    /// The other direction of #376, and the one a wrong diagnosis would corrupt. cyclic-6 is
    /// zero-dimensional and its grevlex basis fits where its lex basis does not, so the diagnosis
    /// runs, completes, and must leave the original error standing.
    #[test]
    fn test_a_real_resource_failure_is_not_relabelled_as_positive_dimensional() {
        let system = cyclic::<6, F>();
        let f4 = F4Options {
            max_matrix_rows: 1000,
            max_matrix_columns: 1000,
            ..Default::default()
        };

        // The premise: the diagnosis gets a complete grevlex basis, and it is zero-dimensional.
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        let (source, _) = f4_with_options(&system, grevlex, &f4).expect("grevlex fits this budget");
        assert!(classify_ideal(&source, grevlex).is_finite_dimensional());

        let options = SolveOptions {
            f4,
            ..SolveOptions::with_strategy(SolveStrategy::DirectLexF4)
        };
        let (outcome, statistics) =
            solve_one_reported(&system, &mut StdRng::seed_from_u64(37), &options);
        let error = outcome.unwrap_err();
        assert!(
            matches!(error, SolveError::Grobner(_)) && error.is_resource_failure(),
            "{}",
            error
        );
        assert!(statistics.diagnosis.is_some(), "the diagnosis still ran");
    }

    /// A route that ran out of *time* is not diagnosed, because diagnosing costs more time.
    ///
    /// The one resource whose budget a second basis computation would silently double. The system
    /// is positive-dimensional, so the diagnosis would have fired on any other crossed limit.
    #[test]
    fn test_a_crossed_time_budget_is_not_spent_again_on_a_diagnosis() {
        let mut system = katsura::<6, F>();
        system.pop();
        let options = SolveOptions {
            f4: F4Options {
                max_wall_time: Some(Duration::from_nanos(1)),
                ..Default::default()
            },
            ..SolveOptions::with_strategy(SolveStrategy::DirectLexF4)
        };

        let (outcome, statistics) =
            solve_one_reported(&system, &mut StdRng::seed_from_u64(41), &options);
        assert!(
            matches!(
                outcome.unwrap_err(),
                SolveError::Grobner(F4Error::TimeBudgetExceeded { .. })
            ),
            "one batch always overruns a nanosecond"
        );
        assert!(
            statistics.diagnosis.is_none(),
            "no second basis was started"
        );
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

        // The storage estimate is the operators' own bytes plus every dense block the dependence
        // machinery needs at full rank: the span's two *triangular* blocks — a row leading at
        // `pivot` stores `D - pivot` coordinates and a row at `r` stores `r + 1` combination
        // coefficients — and the retained accepted vectors. M17 counted two square blocks and
        // priced the operators at a flat 16 bytes an entry, which was wrong in three ways — the
        // operators have a column spine, neither of the span's blocks is square, and the accepted
        // vectors were missing entirely.
        assert_eq!(fglm.memory.span_cells, 16 * 17);
        assert_eq!(fglm.memory.accepted_vector_cells, 16 * 16);
        assert_eq!(
            fglm.estimated_bytes(),
            fglm.memory.operator_bytes
                + (fglm.memory.span_cells + fglm.memory.accepted_vector_cells) * size_of::<F>()
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

#[cfg(test)]
mod outcome_tests {
    //! M21-C: the typed outcome, the carried diagnostics, and the invariant between them.

    use rand::{prelude::StdRng, SeedableRng};

    use super::{
        solve_one, solve_one_reported, solve_one_with_outcome, SolveError, SolveOptions,
        SolveOutcome, SolveStrategy,
    };
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura, planted},
            F4Options, FglmOptions,
        },
        FiniteField, MultivariatePolynomial, Zero,
    };

    type F = Zp2147483647;

    const STRATEGIES: [SolveStrategy; 2] =
        [SolveStrategy::DirectLexF4, SolveStrategy::GrevlexF4ThenFglm];

    fn parse<const N: usize>(
        strings: &[&str],
        vars: [&str; N],
    ) -> Vec<MultivariatePolynomial<N, F>> {
        strings
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, vars).expect("parses"))
            .collect()
    }

    fn solve<const N: usize>(
        system: &[MultivariatePolynomial<N, F>],
        strategy: SolveStrategy,
    ) -> Result<SolveOutcome<N, F>, SolveError> {
        let mut rng = StdRng::seed_from_u64(7);
        solve_one_with_outcome(system, &mut rng, &SolveOptions::with_strategy(strategy))
            .map(|(outcome, _)| outcome)
    }

    /// An inconsistent system and one with no base-field point reach *different* outcomes.
    ///
    /// Both are `Ok(None)` from `solve_one`, which is the conflation M21-C exists to close. The
    /// second system is zero-dimensional with quotient dimension two: 2^31 - 1 is 3 mod 4, so -1
    /// is not a square and `x^2 + 1` has no root in the field.
    #[test]
    fn test_inconsistency_is_distinguished_from_having_no_base_field_point() {
        let inconsistent = parse(&["x - 1", "x - 2"], ["x", "y"]);
        let no_point = parse(&["x^2 + 1", "y"], ["x", "y"]);

        for strategy in STRATEGIES {
            assert_eq!(
                solve(&inconsistent, strategy).expect("within limits"),
                SolveOutcome::Inconsistent,
                "{:?}",
                strategy
            );
            assert_eq!(
                solve(&no_point, strategy).expect("within limits"),
                SolveOutcome::NoBaseFieldPoint,
                "{:?}",
                strategy
            );
        }

        // And the older entry point still collapses them, which is why it is not the one to use
        // when the answer matters.
        let mut rng = StdRng::seed_from_u64(7);
        assert_eq!(solve_one(&inconsistent, &mut rng), Ok(None));
        let mut rng = StdRng::seed_from_u64(7);
        assert_eq!(solve_one(&no_point, &mut rng), Ok(None));
    }

    /// A found point comes back as `Point`, and agrees with what `solve_one` returns.
    #[test]
    fn test_a_point_is_reported_and_agrees_with_solve_one() {
        let point: Vec<F> = (0..6).map(|i| F::new(2 * i as u64 + 3)).collect();
        let system = planted::<6, F>(&point);

        for strategy in STRATEGIES {
            let outcome = solve(&system, strategy).expect("within limits");
            let found = outcome.point().expect("a point exists");
            for p in &system {
                assert!(p.eval(&found).is_zero(), "{} is not satisfied", p);
            }
        }
    }

    /// A positive-dimensional system is an error, not an outcome.
    ///
    /// The route does not apply; that is a statement about the ideal and not an answer about its
    /// points, so it cannot be a `SolveOutcome` variant.
    #[test]
    fn test_positive_dimensional_is_not_an_outcome() {
        for strategy in STRATEGIES {
            assert_eq!(
                solve(&cyclic::<4, F>(), strategy),
                Err(SolveError::PositiveDimensional)
            );
        }
    }

    /// A crossed budget is an error and **never** a no-solution outcome. M21-C's key invariant.
    ///
    /// The failure mode a retrying planner would otherwise introduce: an exhausted attempt read as
    /// "there is no solution". Every budget in `SolveOptions` is exercised against a system that
    /// does have a point, so any `NoBaseFieldPoint` or `Inconsistent` here would be a wrong answer
    /// rather than a missing one.
    #[test]
    fn test_a_crossed_budget_is_never_a_no_solution_answer() {
        let point: Vec<F> = (0..6).map(|i| F::new(2 * i as u64 + 3)).collect();
        let solvable = planted::<6, F>(&point);

        let budgets = [
            SolveOptions {
                f4: F4Options {
                    max_live_nonzeros: 1,
                    ..F4Options::default()
                },
                ..SolveOptions::default()
            },
            SolveOptions {
                f4: F4Options {
                    max_live_bytes: 16,
                    ..F4Options::default()
                },
                ..SolveOptions::default()
            },
            SolveOptions {
                f4: F4Options {
                    max_matrix_rows: 1,
                    ..F4Options::default()
                },
                ..SolveOptions::default()
            },
            SolveOptions {
                max_branches: Some(1),
                ..SolveOptions::default()
            },
            SolveOptions {
                strategy: SolveStrategy::GrevlexF4ThenFglm,
                fglm: FglmOptions {
                    max_quotient_dimension: 1,
                    ..FglmOptions::default()
                },
                ..SolveOptions::default()
            },
            SolveOptions {
                strategy: SolveStrategy::GrevlexF4ThenFglm,
                fglm: FglmOptions {
                    max_span_bytes: 8,
                    ..FglmOptions::default()
                },
                ..SolveOptions::default()
            },
        ];

        for options in budgets {
            let mut rng = StdRng::seed_from_u64(7);
            let result = solve_one_with_outcome(&solvable, &mut rng, &options);
            match result {
                Err(_) => {}
                Ok((SolveOutcome::Point(_), _)) => {}
                Ok((outcome, _)) => panic!(
                    "{:?} under {:?} turned an exhausted budget into an answer",
                    outcome, options.strategy
                ),
            }
        }
    }

    /// A failed attempt still reports the work it did, which is what a planner has to charge for.
    ///
    /// Three failures with three different amounts of completed work behind them. All three are
    /// `Err` from `solve_one_with_outcome`, which discards every counter; `solve_one_reported`
    /// keeps them, and the difference between the three is the whole reason M21-D can account for
    /// discarded work at all.
    #[test]
    fn test_a_failed_attempt_keeps_its_diagnostics() {
        // 1. Positive-dimensional. The basis behind the refusal is complete.
        let mut rng = StdRng::seed_from_u64(3);
        let (outcome, statistics) =
            solve_one_reported(&cyclic::<4, F>(), &mut rng, &SolveOptions::default());
        assert_eq!(outcome, Err(SolveError::PositiveDimensional));
        let f4 = statistics.f4.as_ref().expect("a basis really was computed");
        assert!(
            f4.batches > 0 && f4.max_matrix_rows > 0,
            "a positive-dimensional refusal is not free and must not look free"
        );
        assert_eq!(statistics.fglm, None, "the conversion was never reached");

        // 2. The conversion crosses its budget. The *source* basis behind it is complete.
        let point: Vec<F> = (0..6).map(|i| F::new(2 * i as u64 + 3)).collect();
        let mut rng = StdRng::seed_from_u64(3);
        let (outcome, statistics) = solve_one_reported(
            &planted::<6, F>(&point),
            &mut rng,
            &SolveOptions {
                strategy: SolveStrategy::GrevlexF4ThenFglm,
                fglm: FglmOptions {
                    max_quotient_dimension: 1,
                    ..FglmOptions::default()
                },
                ..SolveOptions::default()
            },
        );
        assert!(matches!(outcome, Err(SolveError::Fglm(_))));
        assert!(statistics.f4.is_some(), "the source basis was computed");
        assert_eq!(statistics.fglm, None, "and the conversion did not finish");

        // 3. F4 itself crosses a budget. No basis at all, but the batches it managed are reported.
        let mut rng = StdRng::seed_from_u64(3);
        let (outcome, statistics) = solve_one_reported(
            &katsura::<6, F>(),
            &mut rng,
            &SolveOptions {
                f4: F4Options {
                    max_batches: Some(2),
                    ..F4Options::default()
                },
                ..SolveOptions::default()
            },
        );
        assert!(matches!(
            outcome,
            Err(SolveError::Grobner(
                crate::grobner::F4Error::TooManyBatches { limit: 2 }
            ))
        ));
        let f4 = statistics
            .f4
            .as_ref()
            .expect("the attempt is still described");
        assert_eq!(f4.batches, 2);
        assert!(f4.max_live_nonzeros > 0);

        // And in every case the statistics are not an answer: there is no outcome to misread.
        assert!(!statistics.inconsistent);
        assert_eq!(statistics.solutions, 0);
    }

    /// `solve_one_with_outcome` is `solve_one_reported` with the statistics dropped on failure.
    #[test]
    fn test_the_reported_and_unreported_entry_points_agree() {
        let point: Vec<F> = (0..6).map(|i| F::new(2 * i as u64 + 3)).collect();
        for system in [planted::<6, F>(&point), katsura::<6, F>()] {
            for strategy in STRATEGIES {
                let options = SolveOptions::with_strategy(strategy);
                let (reported, reported_statistics) =
                    solve_one_reported(&system, &mut StdRng::seed_from_u64(5), &options);
                let direct =
                    solve_one_with_outcome(&system, &mut StdRng::seed_from_u64(5), &options);
                assert_eq!(
                    reported.map(|o| (o, reported_statistics)),
                    direct,
                    "{:?}",
                    strategy
                );
            }
        }
    }

    /// The Gröbner stage's statistics reach the caller, on both routes.
    #[test]
    fn test_the_grobner_statistics_are_carried() {
        let mut rng = StdRng::seed_from_u64(7);
        let (_, direct) = solve_one_with_outcome(
            &katsura::<5, F>(),
            &mut rng,
            &SolveOptions::with_strategy(SolveStrategy::DirectLexF4),
        )
        .expect("within limits");
        let f4 = direct
            .f4
            .as_ref()
            .expect("the direct route computes a basis");
        assert!(f4.batches > 0);
        assert!(f4.max_matrix_rows > 0);
        assert_eq!(f4.bytes_per_entry, 16);
        assert_eq!(direct.fglm, None, "the direct route converts nothing");
        assert_eq!(direct.estimated_peak_bytes(), f4.max_estimated_bytes);

        let mut rng = StdRng::seed_from_u64(7);
        let (_, converted) = solve_one_with_outcome(
            &katsura::<5, F>(),
            &mut rng,
            &SolveOptions::with_strategy(SolveStrategy::GrevlexF4ThenFglm),
        )
        .expect("within limits");
        let source = converted
            .f4
            .as_ref()
            .expect("the source basis is computed too");
        let conversion = converted.fglm.expect("and converted");
        assert!(source.batches > 0);
        assert!(conversion.quotient_dimension > 0);
        // The maximum of the two stages, not their sum: F4's matrices are gone before the
        // conversion allocates.
        assert_eq!(
            converted.estimated_peak_bytes(),
            source.max_estimated_bytes.max(conversion.estimated_bytes())
        );
    }

    /// `solve_one` is exactly the point of `solve_one_with_outcome`, with nothing else changed.
    #[test]
    fn test_the_two_entry_points_agree() {
        let point: Vec<F> = (0..6).map(|i| F::new(2 * i as u64 + 3)).collect();
        // Each arity separately, since `N` is a const generic and the systems do not share one.
        agree(&planted::<6, F>(&point));
        agree(&katsura::<6, F>());
        agree(&cyclic::<5, F>());
    }

    /// `solve_one` and `solve_one_with_outcome` return the same point, under both routes.
    fn agree<const N: usize>(system: &[MultivariatePolynomial<N, F>]) {
        for strategy in STRATEGIES {
            let options = SolveOptions::with_strategy(strategy);
            let mut rng = StdRng::seed_from_u64(11);
            let old = solve_one(system, &mut StdRng::seed_from_u64(11));
            let new = solve_one_with_outcome(system, &mut rng, &options).map(|(o, _)| o.point());
            assert_eq!(old, new, "{:?}", strategy);
        }
    }
}
