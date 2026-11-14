//! A resultant, by Sylvester determinant and interpolation: elimination that is not a Gröbner
//! basis.
//!
//! Two polynomials, two variables, one eliminated: `Res_y(f, g)` is a univariate polynomial in the
//! surviving variable whose roots contain the `x`-coordinate of every common root. It was written
//! (M23-E) to test whether structure-aware elimination beats general F4 on small two-variable
//! slices of larger systems, and it is general: nothing here knows where `f` and `g` came from.
//!
//! # Two kernels for one scalar, and why the second one now exists
//!
//! `Res_y(f, g)` is `det Syl(f, g)`, a determinant of a matrix whose entries are polynomials in
//! the surviving variable. Evaluating that matrix at a point and taking a scalar determinant
//! commutes with evaluation **always**, because a determinant is a polynomial in the entries. So
//! the resultant is recovered by interpolating scalar determinants, and that construction needs no
//! case analysis. It is [`DeterminantKernel::Dense`], and it remains the default.
//!
//! M23-E deliberately stopped there, on the grounds that a Euclidean approach "would be
//! asymptotically better and would need exactly the case analysis this avoids … at the sizes M23-E
//! measures — a Sylvester matrix of order at most a few dozen over a 31-bit prime — it buys nothing
//! worth the risk." **That judgement was right for the sizes it was made at and is wrong for the
//! sizes now in scope**, which is why [`DeterminantKernel::Euclidean`] was added under #350.
//!
//! What changed is the order, not the algorithm. Scoping moved from order 18 to **order 1 458**,
//! taking the operation-count gap from 48x to 3 888x and the stage from milliseconds to 67% of a row
//! that would not run. Driving `f mod g` down the remainder sequence costs `O(n²)` where the
//! determinant costs `O(n³)`, and at order 1 458 that measures **1 692x** — 1.343 ms against
//! 2.272 s on one pinned core (`docs/research/structured-sylvester.md` §5.5).
//!
//! The case analysis M23-E declined to write is real, and it is in
//! `formal_sylvester_determinant`. Specializing `f` at a point where its leading coefficient in
//! `y` vanishes drops its degree, and the specialized resultant is then **not** the specialization
//! of the resultant: the Sylvester order stays fixed at the generic degrees while the actual degrees
//! fall, and the two differ by a factor that is not even the same on both sides. Three corrections
//! cover it, and differential tests assert agreement with the dense kernel at every point of a
//! small field rather than trusting the derivation.
//!
//! **Neither kernel is more correct than the other, and the fast one is not trusted on that
//! claim.** Both are kept, the default is unchanged so figures taken before this existed still
//! reproduce, and `agrees_off_domain` validates against the *dense* kernel whatever the route used —
//! a fast kernel checked against itself is not checked.
//!
//! # What the resultant does and does not give
//!
//! `Res_y(f, g)(a) = 0` is **necessary** for a common root with `x = a`, not sufficient: the
//! resultant vanishes whenever the two specialized polynomials share a root in an *extension*, and
//! it also vanishes when both leading coefficients vanish. So every root of the resultant is a
//! candidate and each candidate must be checked against the system it came from. Nothing in
//! this module decides that a candidate is a solution.
//!
//! # Where the samples are taken, and why it turns out not to matter
//!
//! [`bivariate_resultant`] samples at consecutive field elements and interpolates with
//! `lagrange_interpolate`. [`bivariate_resultant_ntt`] takes the *same* determinants on a
//! power-of-two multiplicative subgroup instead, so the recovery is one inverse NTT; it is the
//! same resultant of the same two polynomials, only the abscissae differ, and it falls back to the
//! reference route on a field whose two-adicity admits no large enough subgroup.
//!
//! **The subgroup route loses on this problem shape, and the reason is structural rather than an
//! implementation detail.** A degree-`d` bivariate pair needs about `2d²` samples of an order-`2d`
//! determinant, so the determinants cost `d^5` while a quadratic Lagrange interpolation costs
//! `d^4`: the interpolation cannot dominate again. Forcing the sample count up to the next power
//! of two therefore buys an `O(n log n)` recovery at the price of extra `O(d^3)` determinants,
//! and at `d = 81` the padding from 13 123 to 16 384 samples costs more than the whole Lagrange
//! solve it removes. Both are kept — see `docs/research/resultant-elimination.md` §6.
//!
//! # Concurrency, and why the answer cannot depend on it
//!
//! Once the interpolation is quadratic the determinants are the whole cost — 99% of the four-round
//! row, §6.4 — and they are independent: each is one evaluation of one matrix at one field element,
//! sharing nothing. [`ResultantOptions::concurrency`] spreads them over worker threads and
//! **defaults to 1**, so every figure recorded before this existed reproduces unchanged.
//!
//! The determinants are written **into their own index** rather than collected in completion order.
//! The interpolation that consumes them is a function of the sample *sequence*, so a resultant whose
//! coefficients depended on thread scheduling would not be reproducible — and a
//! figure that is not reproducible is not a figure. See `sample_determinants` for why a static
//! split is the right shape here where the differential sweep's dynamic handout was not.

use std::{
    fmt::{Display, Formatter},
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, SeedableRng};

use crate::{
    interpolate,
    linalg::Matrix,
    poly::{
        lagrange_interpolate, resultant_from_coefficients, Monomial, Polynomial,
        UnivariatePolynomial,
    },
    FFTDomain, FiniteField, KnownOrder, MultivariatePolynomial,
};

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

/// How a resultant is evaluated, as distinct from which resultant it is.
///
/// Nothing here changes the answer. One knob is how many threads evaluate the independent
/// Sylvester determinants, and it defaults to **1** so that a figure taken without it is
/// reproduced exactly; the other is how many points outside the sample set
/// [`bivariate_resultant_predicted`] checks its answer at before returning it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ResultantOptions {
    /// Worker threads over which the determinants are spread. At least 1.
    pub concurrency: usize,

    /// Points outside the sample set checked against a direct Sylvester determinant. At least 1.
    ///
    /// Only [`bivariate_resultant_predicted`] reads this: the other routes sample against a
    /// *proven* bound and have nothing to validate. The checks are spread over the same
    /// `concurrency` workers as the interpolation's samples, so raising the worker count shortens
    /// them too — at six rounds a serial check was 3% of the row.
    pub off_domain_checks: usize,

    /// Which kernel evaluates each scalar resultant. Defaults to [`DeterminantKernel::Dense`].
    ///
    /// This one does not change the answer either — the kernels agree at every point, including the
    /// specialization points, and differential tests assert it. It changes only what the evaluation
    /// costs, from `O(n³)` to `O(n²)` in the Sylvester order.
    pub kernel: DeterminantKernel,
}

impl Default for ResultantOptions {
    fn default() -> Self {
        Self {
            concurrency: 1,
            off_domain_checks: Self::DEFAULT_OFF_DOMAIN_CHECKS,
            kernel: DeterminantKernel::Dense,
        }
    }
}

impl ResultantOptions {
    /// Off-domain checks taken unless the caller says otherwise: what the four-round rows used.
    pub const DEFAULT_OFF_DOMAIN_CHECKS: usize = 8;

    /// `concurrency` workers.
    ///
    /// # Panics
    /// If `concurrency` is zero. Clamping it to one silently would turn a mis-parsed flag into a
    /// single-threaded run reported as a parallel one, which is exactly the misreading the
    /// scoreboard's `concurrency` field exists to prevent.
    pub fn with_concurrency(concurrency: usize) -> Self {
        assert!(concurrency >= 1, "a resultant needs at least one worker");
        Self {
            concurrency,
            ..Self::default()
        }
    }

    /// The same options validating at `checks` points outside the sample set.
    ///
    /// # Panics
    /// If `checks` is zero. An unvalidated prediction is not a result, and the same argument
    /// applies as for a mis-parsed concurrency: silently accepting none would report an
    /// unvalidated answer in the shape of a validated one.
    pub fn with_off_domain_checks(mut self, checks: usize) -> Self {
        assert!(
            checks >= 1,
            "a predicted sample count must be validated off the domain"
        );
        self.off_domain_checks = checks;
        self
    }

    /// The same options evaluating each scalar resultant by `kernel`.
    pub fn with_kernel(mut self, kernel: DeterminantKernel) -> Self {
        self.kernel = kernel;
        self
    }
}

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
pub fn bivariate_resultant<F: FiniteField + Send + Sync>(
    f: &MultivariatePolynomial<2, F>,
    g: &MultivariatePolynomial<2, F>,
    eliminate: usize,
) -> Result<UnivariatePolynomial<F>, ResultantError> {
    bivariate_resultant_reference(f, g, eliminate).map(|(resultant, _)| resultant)
}

/// The reference route's abscissae: `0, 1, 2, ...`, `points` of them.
///
/// # Errors
/// [`ResultantError::FieldTooSmall`] if the field has fewer than `points` elements.
fn consecutive_abscissae<F: FiniteField>(points: usize) -> Result<Vec<F>, ResultantError> {
    let mut at: Vec<F> = Vec::with_capacity(points);
    for i in 0..points {
        let x = F::new(i as u64);
        // `F::new` is taken modulo the order, so for a field smaller than `points` the sample
        // points would collide and the interpolation would be of the wrong polynomial.
        if i > 0 && x.is_zero() {
            return Err(ResultantError::FieldTooSmall { needed: points });
        }
        at.push(x);
    }
    Ok(at)
}

/// One Sylvester determinant per entry of `at`, in that order, over `concurrency` workers.
///
/// **Index, not completion order.** The output is pre-sized and split into contiguous blocks, so
/// each slot is written by exactly one worker from exactly one abscissa. The returned sequence is
/// therefore a function of `at` alone and not of which worker finished first — which is what makes
/// the interpolation that consumes it reproducible.
///
/// The blocks are **static**, unlike the dynamic index handout
/// [`run_sweep`](crate::grobner::differential::run_sweep) uses. That sweep hands out one index at a
/// time because a generated system's cost spans orders of magnitude; here every sample is a
/// determinant of the *same* order evaluated at a different point, so the blocks are equal work by
/// construction and a shared counter would only add contention.
fn sample_determinants<F: FiniteField + Send + Sync>(
    fc: &[UnivariatePolynomial<F>],
    gc: &[UnivariatePolynomial<F>],
    at: &[F],
    concurrency: usize,
    kernel: DeterminantKernel,
) -> Vec<F> {
    let mut values = vec![F::zero(); at.len()];
    if concurrency <= 1 {
        specialize_block(fc, gc, at, kernel, &mut values);
        return values;
    }

    // `div_ceil` so the blocks cover the whole range; a short tail means fewer threads than
    // requested, never more, and never a sample left unevaluated.
    let block = at.len().div_ceil(concurrency).max(1);
    std::thread::scope(|scope| {
        for (chunk, abscissae) in values.chunks_mut(block).zip(at.chunks(block)) {
            scope.spawn(move || specialize_block(fc, gc, abscissae, kernel, chunk));
        }
    });
    values
}

/// Where the interpolation samples live.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResultantRoute {
    /// The multiplicative subgroup of order `2^log_size`, recovered by one inverse NTT.
    Ntt {
        /// `log2` of the domain size.
        log_size: u32,
    },

    /// `points` consecutive field elements `0, 1, 2, ...`, recovered by Lagrange interpolation.
    ///
    /// The reference route, used when the field has no power-of-two subgroup large enough. It is
    /// cubic in `points`, which is why it is not the default where a subgroup exists.
    Lagrange {
        /// Number of samples, one more than the degree bound.
        points: usize,
    },
}

/// What one resultant cost, by stage.
#[derive(Clone, Copy, Debug)]
pub struct ResultantStages {
    /// Where the samples were taken.
    pub route: ResultantRoute,
    /// The proven bound `n·deg_x(f) + m·deg_x(g)` on the resultant's degree.
    pub degree_bound: usize,
    /// Order of the Sylvester matrix, `deg_y(f) + deg_y(g)`.
    pub matrix_order: usize,
    /// Sylvester determinants evaluated.
    pub samples: usize,
    /// Worker threads the determinants were spread over. 1 for an uncontended figure.
    pub concurrency: usize,
    /// Time spent evaluating those determinants.
    pub sampling: Duration,
    /// Time spent recovering the polynomial from them.
    pub interpolation: Duration,
    /// Which degree the sample count was sized against.
    pub degree_source: DegreeSource,
    /// Points outside the sample set checked against a direct Sylvester determinant.
    pub off_domain_checks: usize,
    /// Time spent on those checks, and on a predicted attempt the checks refused.
    ///
    /// Disjoint from [`Self::sampling`] and [`Self::interpolation`], and the three together are the
    /// elimination's wall clock — [`Self::elapsed`]. Anything that also charges this to a later
    /// stage counts it twice, which is what inflated the six-round totals before M25.
    pub validation: Duration,
}

impl ResultantStages {
    /// The elimination's wall clock: determinants, recovery and validation, each counted **once**.
    ///
    /// The single definition of what one elimination cost, so that a caller filing a stage cost and
    /// a caller printing a total cannot disagree. The three fields are measured in disjoint windows
    /// inside the route, so this is a lower bound on the route's own elapsed time and never an
    /// over-count — `tests` pins both halves of that against an outer timer.
    pub fn elapsed(&self) -> Duration {
        self.sampling + self.interpolation + self.validation
    }
}

/// Which degree the sample count was sized against, and whether a prediction survived validation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DegreeSource {
    /// The proven bound `n·deg_x(f) + m·deg_x(g)`, which needs no validation to be trusted.
    Proven,

    /// The caller's predicted degree, and the recovered polynomial agreed with a direct determinant
    /// at points outside the interpolation domain.
    PredictionHeld {
        /// The predicted degree the sample count came from.
        degree: usize,
    },

    /// The prediction was refused off the domain, so the proven bound produced the answer.
    ///
    /// A falsification of the prediction on that input, and worth more than the samples it would
    /// have saved.
    PredictionFalsified {
        /// The predicted degree that did not hold.
        degree: usize,
    },
}

/// The interpolation route for a resultant of degree at most `degree_bound` over `F`.
///
/// The smallest power-of-two subgroup with more than `degree_bound` elements, when the field's
/// two-adicity admits one: `degree_bound + 1` samples determine a polynomial of degree at most
/// `degree_bound`, and a domain of that size or larger is therefore exact. Fields whose
/// two-adicity is too small — Mersenne-31's is 1 — get the reference route rather than a domain
/// that does not exist.
pub fn interpolation_route<F: KnownOrder>(degree_bound: usize) -> ResultantRoute {
    let points = degree_bound + 1;
    let log_size = points.next_power_of_two().trailing_zeros();
    if log_size <= F::two_adicity() {
        ResultantRoute::Ntt { log_size }
    } else {
        ResultantRoute::Lagrange { points }
    }
}

/// The Sylvester matrix's coefficient rows and the resultant's proven degree bound.
///
/// # Errors
/// [`ResultantError::NoDegreeInEliminatedVariable`].
#[allow(clippy::type_complexity)]
fn sylvester_setup<F: FiniteField>(
    f: &MultivariatePolynomial<2, F>,
    g: &MultivariatePolynomial<2, F>,
    eliminate: usize,
) -> Result<
    (
        Vec<UnivariatePolynomial<F>>,
        Vec<UnivariatePolynomial<F>>,
        usize,
    ),
    ResultantError,
> {
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

    // The resultant's degree in the surviving variable is at most `n·deg_x(f) + m·deg_x(g)`: the
    // Sylvester matrix has `n` rows of `f`'s coefficients and `m` of `g`'s, and a determinant is a
    // sum of products taking one entry from each row.
    let f_degree = fc.iter().map(|c| c.degree() as usize).max().unwrap_or(0);
    let g_degree = gc.iter().map(|c| c.degree() as usize).max().unwrap_or(0);
    Ok((fc, gc, n * f_degree + m * g_degree))
}

/// `Res_{x_eliminate}(f, g)` by the reference route, with its two stages timed apart.
///
/// The A/B partner of [`bivariate_resultant_ntt`]: same answer as [`bivariate_resultant`], which
/// is a thin wrapper over this, but reporting the determinant evaluations and the Lagrange
/// interpolation separately so the two routes can be compared stage by stage rather than only on a
/// total.
///
/// Single-threaded. [`bivariate_resultant_reference_with`] takes the concurrency.
///
/// # Errors
/// [`ResultantError`].
pub fn bivariate_resultant_reference<F: FiniteField + Send + Sync>(
    f: &MultivariatePolynomial<2, F>,
    g: &MultivariatePolynomial<2, F>,
    eliminate: usize,
) -> Result<(UnivariatePolynomial<F>, ResultantStages), ResultantError> {
    bivariate_resultant_reference_with(f, g, eliminate, ResultantOptions::default())
}

/// [`bivariate_resultant_reference`] with the determinants spread over `options.concurrency`
/// workers.
///
/// The recovered polynomial does not depend on the concurrency — the samples are indexed, not
/// collected — and `tests` pins that at 1, 8 and 32.
///
/// # Errors
/// [`ResultantError`].
pub fn bivariate_resultant_reference_with<F: FiniteField + Send + Sync>(
    f: &MultivariatePolynomial<2, F>,
    g: &MultivariatePolynomial<2, F>,
    eliminate: usize,
    options: ResultantOptions,
) -> Result<(UnivariatePolynomial<F>, ResultantStages), ResultantError> {
    let (fc, gc, degree_bound) = sylvester_setup(f, g, eliminate)?;
    let points = degree_bound + 1;
    let abscissae = consecutive_abscissae::<F>(points)?;

    let at = Instant::now();
    let values = sample_determinants(&fc, &gc, &abscissae, options.concurrency, options.kernel);
    let sampling = at.elapsed();

    let at = Instant::now();
    let resultant = lagrange_interpolate(abscissae.into_iter().zip(values).collect::<Vec<_>>());
    let interpolation = at.elapsed();

    Ok((
        resultant,
        ResultantStages {
            route: ResultantRoute::Lagrange { points },
            degree_bound,
            matrix_order: fc.len() + gc.len() - 2,
            samples: points,
            concurrency: options.concurrency,
            degree_source: DegreeSource::Proven,
            off_domain_checks: 0,
            validation: Duration::ZERO,
            sampling,
            interpolation,
        },
    ))
}

/// `Res_{x_eliminate}(f, g)` from `predicted_degree + 1` samples, **validated**.
///
/// The proven bound `n·deg_x(f) + m·deg_x(g)` is of Bézout size, and structured inputs often have a
/// resultant far below it, so sizing the sample set against a caller's prediction is the largest
/// saving on this route: 730 determinants instead of 13 123 on one measured four-round
/// permutation slice. The prediction is experimental, so this function does not
/// trust it — the recovered polynomial is checked against a direct Sylvester determinant at
/// `options.off_domain_checks` points the interpolation never sampled, and on disagreement the
/// **proven** path produces the answer instead, with [`DegreeSource::PredictionFalsified`]
/// recording that the formula did not hold on this input.
///
/// Samples at consecutive field elements and recovers by `lagrange_interpolate`. The predicted
/// count is not a power of two — 730 on that row — and rounding it up to an NTT domain would give
/// back a third of the saving to buy a recovery that `resultant-elimination.md` §6.4 shows cannot
/// matter at any round count.
///
/// # Errors
/// [`ResultantError`].
pub fn bivariate_resultant_predicted<F: FiniteField + Send + Sync>(
    f: &MultivariatePolynomial<2, F>,
    g: &MultivariatePolynomial<2, F>,
    eliminate: usize,
    predicted_degree: usize,
    options: ResultantOptions,
) -> Result<(UnivariatePolynomial<F>, ResultantStages), ResultantError> {
    let (fc, gc, degree_bound) = sylvester_setup(f, g, eliminate)?;
    // A prediction no smaller than the proven bound saves nothing and needs no validating.
    if predicted_degree >= degree_bound {
        return bivariate_resultant_reference_with(f, g, eliminate, options);
    }
    let points = predicted_degree + 1;
    let abscissae = consecutive_abscissae::<F>(points)?;

    let at = Instant::now();
    let values = sample_determinants(&fc, &gc, &abscissae, options.concurrency, options.kernel);
    let sampling = at.elapsed();

    let at = Instant::now();
    let candidate = lagrange_interpolate(abscissae.into_iter().zip(values).collect::<Vec<_>>());
    let interpolation = at.elapsed();

    let at = Instant::now();
    let held = agrees_off_domain(
        &fc,
        &gc,
        &candidate,
        points,
        options.off_domain_checks,
        options.concurrency,
    )?;
    let validation = at.elapsed();

    if held {
        return Ok((
            candidate,
            ResultantStages {
                route: ResultantRoute::Lagrange { points },
                degree_bound,
                matrix_order: fc.len() + gc.len() - 2,
                samples: points,
                concurrency: options.concurrency,
                sampling,
                interpolation,
                degree_source: DegreeSource::PredictionHeld {
                    degree: predicted_degree,
                },
                off_domain_checks: options.off_domain_checks,
                validation,
            },
        ));
    }

    let (resultant, mut stages) = bivariate_resultant_reference_with(f, g, eliminate, options)?;
    stages.degree_source = DegreeSource::PredictionFalsified {
        degree: predicted_degree,
    };
    stages.off_domain_checks = options.off_domain_checks;
    // The refused attempt is charged to this row: it is wall clock the row spent.
    stages.validation = validation + sampling + interpolation;
    Ok((resultant, stages))
}

/// `checks` distinct abscissae outside the sample set `0, 1, …, points − 1`.
///
/// Pure in `(points, checks)` and in the fixed seed, and in particular **independent of the
/// candidate and of the concurrency**: the points can therefore be drawn before any determinant is
/// evaluated, which is what lets the validation ride the same parallel sample loop as the
/// interpolation instead of a serial loop of its own.
///
/// Distinctness is explicit rather than left to the field's size. Over KoalaBear a repeat among
/// eight draws has probability about `8²/2^32`, so this changes no run on record — but the
/// probability bound in `resultant-elimination.md` is an argument about `checks` *independent*
/// points, and a silently repeated point would weaken the bound without changing the count.
///
/// # Errors
/// [`ResultantError::FieldTooSmall`] if the field cannot supply `checks` points outside the sample
/// set.
fn off_domain_abscissae<F: FiniteField>(
    points: usize,
    checks: usize,
) -> Result<Vec<F>, ResultantError> {
    let mut rng = StdRng::seed_from_u64(0x00ff_d01a);
    let in_sample_set = |x: &F| (0..points as u64).any(|i| *x == F::new(i));

    let mut at: Vec<F> = Vec::with_capacity(checks);
    let mut drawn = 0usize;
    while at.len() < checks {
        if drawn > 8 * checks + 64 {
            return Err(ResultantError::FieldTooSmall {
                needed: points + checks,
            });
        }
        let x = F::random(&mut rng);
        drawn += 1;
        if in_sample_set(&x) || at.contains(&x) {
            continue;
        }
        at.push(x);
    }
    Ok(at)
}

/// Whether `candidate` agrees with `det Syl(f, g)` at `checks` points outside the sample set.
///
/// The samples are `0, 1, …, points − 1`; a point drawn from outside that set was never
/// interpolated through, so agreement there is evidence about the construction rather than a
/// restatement of it. The draws are from a fixed seed, which keeps a run reproducible.
///
/// **This is a probabilistic consistency check and not a proof of a polynomial identity.** What it
/// establishes is that a candidate of degree below `points` agreeing with the determinant at
/// `checks` further points is wrong with probability at most `(2d²/p)^checks` over the draws — see
/// `resultant-elimination.md` §6.9. The *proven*-bound routes need no such argument, because there
/// a polynomial of degree at most the bound agreeing on `bound + 1` points is the resultant
/// outright; the predicted count buys its sample saving at the price of this being evidence rather
/// than a certificate.
///
/// The determinants go through [`sample_determinants`] at `concurrency` workers, the same indexed
/// path the interpolation's samples take, and **every** check is evaluated before any is compared.
/// A short-circuit on the first disagreement would make the verdict depend on which worker got
/// there first in a falsifying case; evaluating all of them costs `checks` determinants on the path
/// that is about to pay for a whole proven-bound fallback anyway.
///
/// # Errors
/// [`ResultantError::FieldTooSmall`] if the field cannot supply `checks` points outside the sample
/// set.
fn agrees_off_domain<F: FiniteField + Send + Sync>(
    fc: &[UnivariatePolynomial<F>],
    gc: &[UnivariatePolynomial<F>],
    candidate: &UnivariatePolynomial<F>,
    points: usize,
    checks: usize,
    concurrency: usize,
) -> Result<bool, ResultantError> {
    let at = off_domain_abscissae::<F>(points, checks)?;
    // Deliberately DENSE regardless of the route's kernel: a fast kernel checked against
    // itself is not checked. This makes every predicted run a differential test of the remainder
    // sequence against the determinant, and eight dense evaluations are negligible against a row.
    let direct = sample_determinants(fc, gc, &at, concurrency, DeterminantKernel::Dense);
    Ok(at
        .iter()
        .zip(&direct)
        .all(|(x, determinant)| candidate.eval(x) == *determinant))
}

/// `Res_{x_eliminate}(f, g)`, interpolated on a power-of-two subgroup, with stage costs.
///
/// Same resultant as [`bivariate_resultant`] — the determinant of the same Sylvester matrix in the
/// same variable — recovered from samples on a multiplicative subgroup instead of at consecutive
/// field elements, so the interpolation is one inverse NTT rather than a Lagrange solve.
/// [`interpolation_route`] picks the domain and falls back to
/// [`bivariate_resultant_reference`] when the field's two-adicity admits none.
///
/// The domain is sized against the **proven** bound `n·deg_x(f) + m·deg_x(g)`, not against the
/// smaller degree a structured input may turn out to have. That costs samples: for one measured
/// four-round permutation slice the bound is 13 122, so 13 123 samples would do and the domain is `2^14 = 16 384`. Since a
/// determinant costs far more than a point of interpolation at these sizes, the padding is the
/// dominant term of the comparison between the two routes — see `resultant-elimination.md` §6.
///
/// Single-threaded. [`bivariate_resultant_ntt_with`] takes the concurrency.
///
/// # Errors
/// [`ResultantError`].
pub fn bivariate_resultant_ntt<F: KnownOrder + Send + Sync>(
    f: &MultivariatePolynomial<2, F>,
    g: &MultivariatePolynomial<2, F>,
    eliminate: usize,
) -> Result<(UnivariatePolynomial<F>, ResultantStages), ResultantError> {
    bivariate_resultant_ntt_with(f, g, eliminate, ResultantOptions::default())
}

/// [`bivariate_resultant_ntt`] with the determinants spread over `options.concurrency` workers.
///
/// # Errors
/// [`ResultantError`].
pub fn bivariate_resultant_ntt_with<F: KnownOrder + Send + Sync>(
    f: &MultivariatePolynomial<2, F>,
    g: &MultivariatePolynomial<2, F>,
    eliminate: usize,
    options: ResultantOptions,
) -> Result<(UnivariatePolynomial<F>, ResultantStages), ResultantError> {
    let (fc, gc, degree_bound) = sylvester_setup(f, g, eliminate)?;
    let log_size = match interpolation_route::<F>(degree_bound) {
        ResultantRoute::Ntt { log_size } => log_size,
        ResultantRoute::Lagrange { .. } => {
            return bivariate_resultant_reference_with(f, g, eliminate, options)
        }
    };

    // Any primitive `2^log_size`-th root of unity serves: the recovered polynomial is the unique
    // one of degree below the domain size agreeing with the determinant on the subgroup, so it
    // does not depend on which generator enumerates it. The seed is fixed to keep the run
    // reproducible.
    let size = 1usize << log_size;
    let generator = F::two_adic_root_of_unity(log_size, &mut StdRng::seed_from_u64(0x5e5a17a27));
    let domain = FFTDomain::from_generator(generator, size);

    let at = Instant::now();
    let values = sample_determinants(
        &fc,
        &gc,
        domain.powers(),
        options.concurrency,
        options.kernel,
    );
    let sampling = at.elapsed();

    let at = Instant::now();
    let resultant = interpolate(&values, &domain);
    let interpolation = at.elapsed();

    Ok((
        resultant,
        ResultantStages {
            route: ResultantRoute::Ntt { log_size },
            degree_bound,
            matrix_order: fc.len() + gc.len() - 2,
            samples: size,
            concurrency: options.concurrency,
            degree_source: DegreeSource::Proven,
            off_domain_checks: 0,
            validation: Duration::ZERO,
            sampling,
            interpolation,
        },
    ))
}

/// `det Syl(f, g)` in `x_eliminate`, with the surviving variable set to `at`.
///
/// The independent check on an interpolated resultant: one scalar determinant, sharing no code
/// with the interpolation. Evaluating it at a point *outside* the interpolation domain tests the
/// recovered polynomial against the definition rather than against its own samples.
///
/// # Errors
/// [`ResultantError::NoDegreeInEliminatedVariable`].
pub fn sylvester_determinant_at<F: FiniteField>(
    f: &MultivariatePolynomial<2, F>,
    g: &MultivariatePolynomial<2, F>,
    eliminate: usize,
    at: F,
) -> Result<F, ResultantError> {
    let fc = coefficients_in(f, eliminate);
    let gc = coefficients_in(g, eliminate);
    if fc.len() == 1 {
        return Err(ResultantError::NoDegreeInEliminatedVariable { argument: 0 });
    }
    if gc.len() == 1 {
        return Err(ResultantError::NoDegreeInEliminatedVariable { argument: 1 });
    }
    Ok(sylvester_determinant(&fc, &gc, at))
}

/// Specializes a fixed coefficient vector at a run of sample points, one column at a time.
///
/// #598. `fc` and `gc` are built once per row and fixed for the whole sweep, so evaluating every
/// coefficient at every sample by Horner is a multipoint evaluation done the slowest possible way
/// — #412 measured it at about two thirds of the per-determinant cost.
///
/// # Forward differences, and why not the transform
///
/// #598 prices a transform route at ~40x on this term. It needs the sample set to be a
/// multiplicative subgroup, and the module comment above records that the subgroup route **loses
/// on this problem shape**: padding 13 123 samples to 16 384 costs more determinants than the
/// Lagrange solve it removes. The route that runs samples at *consecutive* field elements, and on
/// an arithmetic progression the available trick is forward differences.
///
/// `t[k]` holds the k-th forward difference at the current point; the value is `t[0]` and a step is
/// `t[k] += t[k+1]` ascending, because `D^k p(x + h) = D^k p(x) + D^(k+1) p(x)`. The top difference
/// of a degree-`e` polynomial is constant, so a step costs `e` **additions** where Horner costs `e`
/// multiply-adds. The operation count is unchanged; only the operation gets cheaper, which is why
/// this was measured before it was written: `examples/specialization_batch.rs` puts it at
/// **2.7x-4.5x** across three fields at degrees 243 and 729.
///
/// # Why this holds no buffer
///
/// Materializing the whole `2(d + 1) x S` specialization would be about 690 MB at `rf4-rp2` over
/// an 8-byte field and 2.8 GB over BN254 `Fr`. A difference table is `O(d^2)` in total - about
/// 4 MB at `d = 729` - and yields one sample's column per step, so this drops into the existing
/// per-sample loop rather than replacing it with a batch.
struct Specializer<'a, F: FiniteField> {
    polynomials: &'a [UnivariatePolynomial<F>],

    /// The sample points, in the order they will be asked for.
    at: &'a [F],

    /// Difference tables, one per polynomial, or empty when that polynomial stays on Horner.
    ///
    /// Empty for every polynomial when the points are not an arithmetic progression - the subgroup
    /// route's domain is geometric, and the off-domain validation points are random - so a
    /// non-progression sample set reproduces the pre-#598 behaviour exactly.
    tables: Vec<Vec<F>>,

    /// How many columns have been produced.
    produced: usize,
}

impl<'a, F: FiniteField> Specializer<'a, F> {
    /// Prepare to walk `at`, using differences if `at` is an arithmetic progression.
    fn new(polynomials: &'a [UnivariatePolynomial<F>], at: &'a [F]) -> Self {
        let tables = if Self::is_progression(at) {
            polynomials
                .iter()
                .map(|c| Self::difference_table(c, at))
                .collect()
        } else {
            Vec::new()
        };
        Self {
            polynomials,
            at,
            tables,
            produced: 0,
        }
    }

    /// Whether `at` is `x0, x0 + h, x0 + 2h, ...` for a single non-zero `h`.
    ///
    /// Checked rather than assumed from the route: one [`sample_determinants`] serves the
    /// consecutive route, the subgroup route and the random off-domain points, and differencing a
    /// geometric or random set would be silently wrong rather than merely slow.
    fn is_progression(at: &[F]) -> bool {
        if at.len() < 3 {
            return false;
        }
        let step = at[1] - at[0];
        if step.is_zero() {
            return false;
        }
        at.windows(2).all(|pair| pair[1] - pair[0] == step)
    }

    /// `t[k] = D^k p(at[0])`, or empty when `at` is too short for the table to be built.
    fn difference_table(p: &UnivariatePolynomial<F>, at: &[F]) -> Vec<F> {
        let e = p.degree() as usize;
        if at.len() < e + 1 {
            return Vec::new();
        }
        let mut row: Vec<F> = at[..=e].iter().map(|x| p.eval(x)).collect();
        // Repeated in-place differencing; descending `i` so each read of `row[i - 1]` precedes its
        // overwrite. After pass `k`, `row[k]` is the k-th difference at `at[0]`.
        for k in 0..=e {
            for i in (k + 1..=e).rev() {
                row[i] = row[i] - row[i - 1];
            }
        }
        row
    }

    /// The next sample's coefficient vector, written into `out`.
    ///
    /// # Panics
    /// If called more times than there are sample points.
    fn next_into(&mut self, out: &mut Vec<F>) {
        let index = self.produced;
        assert!(
            index < self.at.len(),
            "asked for column {} of a {}-point sweep",
            index,
            self.at.len()
        );
        out.clear();
        if self.tables.is_empty() {
            out.extend(self.polynomials.iter().map(|c| c.eval(&self.at[index])));
            self.produced += 1;
            return;
        }
        for (column, table) in self.tables.iter_mut().enumerate() {
            if table.is_empty() {
                out.push(self.polynomials[column].eval(&self.at[index]));
                continue;
            }
            // Read before advancing: the table is at position `index` on entry.
            out.push(table[0]);
            for k in 0..table.len() - 1 {
                table[k] = table[k] + table[k + 1];
            }
        }
        self.produced += 1;
    }
}

/// One contiguous block of samples, specialized by [`Specializer`] and reduced by the kernel.
///
/// The block is what carries the difference tables, which is why this exists rather than the loop
/// being inline: a worker's block is a sub-progression of the sweep's progression - same step, a
/// later start - so each worker builds its own tables and the result is unchanged by how the blocks
/// were cut. A block too short to build a table falls back to Horner per point, which is the
/// pre-#598 behaviour and is also what a non-progression sample set gets.
///
/// Two buffers, reused across the whole block rather than allocated per sample. That is the other
/// half of what #598 removes: the old route allocated two `Vec`s per determinant.
fn specialize_block<F: FiniteField>(
    fc: &[UnivariatePolynomial<F>],
    gc: &[UnivariatePolynomial<F>],
    at: &[F],
    kernel: DeterminantKernel,
    out: &mut [F],
) {
    debug_assert_eq!(at.len(), out.len());
    let mut f_specializer = Specializer::new(fc, at);
    let mut g_specializer = Specializer::new(gc, at);
    let mut a: Vec<F> = Vec::with_capacity(fc.len());
    let mut b: Vec<F> = Vec::with_capacity(gc.len());
    for slot in out.iter_mut() {
        f_specializer.next_into(&mut a);
        g_specializer.next_into(&mut b);
        *slot = determinant_of(&a, &b, kernel);
    }
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
    let a: Vec<F> = fc.iter().map(|c| c.eval(&at)).collect();
    let b: Vec<F> = gc.iter().map(|c| c.eval(&at)).collect();
    sylvester_determinant_of(&a, &b)
}

/// [`sylvester_determinant`] on coefficients already specialized at the point.
///
/// Split out by #598 so the specialization can be walked by [`Specializer`] across the sweep
/// instead of recomputed per point. The arithmetic below is unchanged, which is what makes the
/// batched route bit-identical rather than merely equivalent.
fn sylvester_determinant_of<F: FiniteField>(a: &[F], b: &[F]) -> F {
    let m = a.len() - 1;
    let n = b.len() - 1;
    let size = m + n;

    // Highest power first, which is the usual layout.
    let f_row: Vec<F> = (0..=m).rev().map(|i| a[i]).collect();
    let g_row: Vec<F> = (0..=n).rev().map(|i| b[i]).collect();

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

/// `det Syl(f, g)` with the surviving variable set to `at`, by the remainder sequence.
///
/// The same scalar [`sylvester_determinant`] returns, for the same inputs, at `O(n²)` rather than
/// `O(n³)` in the Sylvester order.
///
/// **Test-only since #598.** The sweep no longer specializes per point — [`Specializer`] walks the
/// progression instead — so this and [`determinant_at`] survive as the per-point reference the
/// batched route is differentially tested against. That is the same discipline [`DeterminantKernel`]
/// and [`ResultantRoute`] are kept under: a figure is only a comparison if the thing it is compared
/// against is still runnable.
#[cfg(test)]
fn sylvester_resultant_euclid<F: FiniteField>(
    fc: &[UnivariatePolynomial<F>],
    gc: &[UnivariatePolynomial<F>],
    at: F,
) -> F {
    let a: Vec<F> = fc.iter().map(|c| c.eval(&at)).collect();
    let b: Vec<F> = gc.iter().map(|c| c.eval(&at)).collect();
    resultant_from_coefficients(&a, &b)
}

/// One scalar resultant from coefficients already specialized at the point.
///
/// The specialization trap of `docs/research/structured-sylvester.md` §5.3 is handled downstream by
/// `formal_determinant`, on these very slices - so batching the *production* of `a` and `b` cannot
/// disturb it. That is the safety argument for #598: the batched route hands the kernels the same
/// vectors, with the same lengths encoding the same formal degrees, bit for bit.
fn determinant_of<F: FiniteField>(a: &[F], b: &[F], kernel: DeterminantKernel) -> F {
    match kernel {
        DeterminantKernel::Dense => sylvester_determinant_of(a, b),
        DeterminantKernel::Euclidean => resultant_from_coefficients(a, b),
    }
}

/// Which kernel evaluates one scalar resultant at one point.
///
/// Both are kept rather than one replacing the other, for the same reason both interpolation routes
/// are: a figure is only a comparison if the thing it is compared against is still runnable. The
/// two agree at every point including the specialization points, which is asserted by differential
/// tests rather than assumed.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum DeterminantKernel {
    /// `det Syl(f, g)` by dense LU on the `(m + n)`-square matrix. `O(n³)` per evaluation.
    ///
    /// The default, so that a figure taken before the remainder sequence existed is reproduced
    /// exactly by a run that does not ask for anything else.
    #[default]
    Dense,

    /// `Res(f, g)` down the polynomial remainder sequence. `O(n²)` per evaluation.
    Euclidean,
}

impl Display for DeterminantKernel {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Dense => write!(formatter, "dense"),
            Self::Euclidean => write!(formatter, "euclidean"),
        }
    }
}

/// One scalar resultant at one point, by the named kernel.
///
/// **Test-only since #598**; see [`sylvester_resultant_euclid`].
#[cfg(test)]
fn determinant_at<F: FiniteField>(
    fc: &[UnivariatePolynomial<F>],
    gc: &[UnivariatePolynomial<F>],
    at: F,
    kernel: DeterminantKernel,
) -> F {
    match kernel {
        DeterminantKernel::Dense => sylvester_determinant(fc, gc, at),
        DeterminantKernel::Euclidean => sylvester_resultant_euclid(fc, gc, at),
    }
}

/// A bivariate polynomial with the given degree in each variable and random coefficients.
///
/// The top coefficient in both variables is forced nonzero so that the Sylvester matrix really has
/// the order the degrees claim — which is the whole point when the pair exists to put a determinant
/// of a *named* order under a timer.
pub fn random_bivariate<F: FiniteField, R: rand::RngCore + rand::CryptoRng>(
    degree_x: u32,
    degree_y: u32,
    rng: &mut R,
) -> MultivariatePolynomial<2, F> {
    let mut terms: Vec<(Monomial<2>, F)> = Vec::new();
    for i in 0..=degree_x {
        for j in 0..=degree_y {
            let mut c = F::random(rng);
            if i == degree_x && j == degree_y && c.is_zero() {
                c = F::one();
            }
            if !c.is_zero() {
                terms.push((Monomial::new(&[i, j]), c));
            }
        }
    }
    MultivariatePolynomial::new(&terms)
}

/// What one batch of Sylvester determinants cost.
///
/// The unit a cost model is calibrated in. `examples/determinant_sweep.rs` takes one of these per
/// matrix order and fits [`fit_power_law`] to the per-determinant cost; the matrix footprint is
/// carried alongside the time because the deviation from a single power law is a cache effect and
/// the footprint is what decides which level of the hierarchy a given order lands in.
#[derive(Clone, Copy, Debug)]
pub struct DeterminantBatch {
    /// Order of the Sylvester matrix, `deg_y(f) + deg_y(g)`.
    pub matrix_order: usize,
    /// Determinants evaluated.
    pub determinants: usize,
    /// Worker threads they were spread over.
    pub concurrency: usize,
    /// Bytes one dense `(m+n)²` matrix of field elements occupies.
    ///
    /// The *matrix*, not the live set: `crout_lu_pivoting` allocates `L`, `U` and `P` beside a
    /// clone of it, so a worker's working set is about four times this.
    ///
    /// Reported for both kernels and meaningful only for [`DeterminantKernel::Dense`]: the
    /// remainder sequence never forms the matrix, and holds two coefficient vectors instead.
    pub matrix_bytes: usize,
    /// Wall clock for the whole batch, excluding the one-off coefficient extraction.
    pub elapsed: Duration,
    /// Which kernel produced it.
    ///
    /// Recorded because the two differ by orders of magnitude at the same `matrix_order`, so a
    /// batch without its kernel is a number that cannot be compared with another.
    pub kernel: DeterminantKernel,
}

impl DeterminantBatch {
    /// Wall clock per determinant: what a batch of this width costs an operator.
    pub fn wall_per_determinant(&self) -> f64 {
        self.elapsed.as_secs_f64() / self.determinants.max(1) as f64
    }

    /// Core-time per determinant: wall clock times workers, which is the figure that extrapolates.
    ///
    /// Comparing *this* across worker counts is what separates a parallel-efficiency loss from a
    /// per-determinant cost that genuinely grew — see `resultant-elimination.md` §6.6.
    pub fn core_per_determinant(&self) -> f64 {
        self.wall_per_determinant() * self.concurrency as f64
    }
}

/// `at.len()` Sylvester determinants of `f` and `g`, timed, over `concurrency` workers.
///
/// The measurement entry point for the determinant kernel, sharing the sample loop
/// `sample_determinants` with every resultant route so that what is timed here is what a row
/// pays. The coefficient extraction is done once and is **not** inside the timer: it is per-row
/// work, not per-determinant work.
///
/// # Errors
/// [`ResultantError::NoDegreeInEliminatedVariable`].
pub fn time_sylvester_determinants<F: FiniteField + Send + Sync>(
    f: &MultivariatePolynomial<2, F>,
    g: &MultivariatePolynomial<2, F>,
    eliminate: usize,
    at: &[F],
    concurrency: usize,
    kernel: DeterminantKernel,
) -> Result<(Vec<F>, DeterminantBatch), ResultantError> {
    let (fc, gc, _) = sylvester_setup(f, g, eliminate)?;
    let matrix_order = fc.len() + gc.len() - 2;

    let started = Instant::now();
    let values = sample_determinants(&fc, &gc, at, concurrency, kernel);
    let elapsed = started.elapsed();

    Ok((
        values,
        DeterminantBatch {
            matrix_order,
            determinants: at.len(),
            concurrency,
            matrix_bytes: matrix_order * matrix_order * std::mem::size_of::<F>(),
            elapsed,
            kernel,
        },
    ))
}

/// A least-squares power law `y = a · x^b`, fitted in log–log space.
///
/// Reported with its residuals rather than with a correlation coefficient: a cost model is used to
/// *refuse runs*, so what matters is how wrong it is at the largest order measured and not how well
/// it describes the cloud on average.
#[derive(Clone, Debug)]
pub struct PowerLawFit {
    /// The exponent `b`.
    pub exponent: f64,
    /// The prefactor `a`.
    pub prefactor: f64,
    /// Relative residual `fitted / measured − 1` at each input point, in input order.
    pub residuals: Vec<f64>,
    /// Standard error of `exponent`. Zero when there are too few points to estimate one.
    pub exponent_stderr: f64,
}

impl PowerLawFit {
    /// The fitted value at `x`.
    pub fn at(&self, x: f64) -> f64 {
        self.prefactor * x.powf(self.exponent)
    }

    /// The largest relative residual in absolute value: the fit's worst case over its own data.
    pub fn worst_residual(&self) -> f64 {
        self.residuals.iter().fold(0.0f64, |w, r| w.max(r.abs()))
    }
}

/// Ordinary least squares on `(ln x, ln y)`.
///
/// `None` unless there are at least two points with finite positive coordinates and at least two
/// distinct abscissae — a single point admits any exponent, and an exponent that the data does not
/// constrain must not be returned as if it were measured. A non-finite coordinate is refused rather
/// than propagated, since a NaN exponent would be printed as a fit.
pub fn fit_power_law(points: &[(f64, f64)]) -> Option<PowerLawFit> {
    let usable = |v: f64| v.is_finite() && v > 0.0;
    if points.iter().any(|(x, y)| !usable(*x) || !usable(*y)) {
        return None;
    }
    let n = points.len();
    if n < 2 {
        return None;
    }
    let logs: Vec<(f64, f64)> = points.iter().map(|(x, y)| (x.ln(), y.ln())).collect();
    let mean_x = logs.iter().map(|(x, _)| *x).sum::<f64>() / n as f64;
    let mean_y = logs.iter().map(|(_, y)| *y).sum::<f64>() / n as f64;
    let sxx: f64 = logs.iter().map(|(x, _)| (x - mean_x).powi(2)).sum();
    if sxx <= 0.0 {
        return None;
    }
    let sxy: f64 = logs
        .iter()
        .map(|(x, y)| (x - mean_x) * (y - mean_y))
        .sum::<f64>();
    let exponent = sxy / sxx;
    let prefactor = (mean_y - exponent * mean_x).exp();

    let residuals: Vec<f64> = points
        .iter()
        .map(|(x, y)| prefactor * x.powf(exponent) / y - 1.0)
        .collect();
    // The slope's standard error from the log–log residuals. Two points fit a line exactly, so
    // there is no spread to estimate from and the honest answer is zero rather than a NaN.
    let exponent_stderr = if n > 2 {
        let sse: f64 = logs
            .iter()
            .map(|(x, y)| (y - (mean_y + exponent * (x - mean_x))).powi(2))
            .sum();
        (sse / (n - 2) as f64 / sxx).sqrt()
    } else {
        0.0
    };

    Some(PowerLawFit {
        exponent,
        prefactor,
        residuals,
        exponent_stderr,
    })
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
    use super::{
        bivariate_resultant, bivariate_resultant_ntt, bivariate_resultant_ntt_with,
        bivariate_resultant_predicted, bivariate_resultant_reference_with, determinant_at,
        interpolation_route, sample_determinants, sylvester_determinant_at, DegreeSource,
        DeterminantKernel, ResultantError, ResultantOptions, ResultantRoute, Specializer,
    };
    use crate::{
        fields::{Mersenne31, PrimeFieldElement64, Zp13},
        identities::One,
        poly::{Polynomial, UnivariatePolynomial},
        FiniteField, MultivariatePolynomial, Zero,
    };

    type F = Zp13;
    /// KoalaBear, `2^31 - 2^24 + 1`, at 64-bit storage: a 31-bit prime with two-adicity 24.
    type Koala = PrimeFieldElement64<2_130_706_433>;
    const VARS: [&str; 2] = ["x", "y"];

    fn parse(text: &str) -> MultivariatePolynomial<2, F> {
        MultivariatePolynomial::parse(text, VARS).expect("a bivariate polynomial")
    }

    /// A bivariate pair over KoalaBear, at the degrees the caller names.
    fn random_bivariate<R: rand::RngCore + rand::CryptoRng>(
        degree_x: u32,
        degree_y: u32,
        rng: &mut R,
    ) -> MultivariatePolynomial<2, Koala> {
        super::random_bivariate::<Koala, R>(degree_x, degree_y, rng)
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

    /// An interpolation sized against too small a degree is refused by the off-domain check.
    ///
    /// The guard that makes an unproven formula usable: claiming degree 7 for a resultant of
    /// degree 32 recovers a wrong polynomial, the check catches it, and the proven bound is used.
    #[test]
    fn test_a_truncated_interpolation_is_caught_off_the_domain() {
        use rand::{prelude::StdRng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(0x7c0bb1e);
        let f = random_bivariate(4, 4, &mut rng);
        let g = random_bivariate(4, 4, &mut rng);
        let proven = bivariate_resultant(&f, &g, 1).expect("both involve y");
        let (recovered, stages) =
            bivariate_resultant_predicted(&f, &g, 1, 7, ResultantOptions::default())
                .expect("both involve y");
        assert_eq!(
            stages.degree_source,
            DegreeSource::PredictionFalsified { degree: 7 },
            "degree 7 cannot pin a degree-32 resultant"
        );
        assert_eq!(stages.samples, stages.degree_bound + 1, "the proven count");
        assert_eq!(recovered, proven, "the fallback returns the real resultant");
    }

    /// A prediction no smaller than the proven bound takes the proven path and saves nothing.
    #[test]
    fn test_a_prediction_above_the_proven_bound_takes_the_proven_path() {
        let f = MultivariatePolynomial::<2, Koala>::parse("x^2*y^2 + y + 1", VARS).expect("parses");
        let g = MultivariatePolynomial::<2, Koala>::parse("x*y^2 + 3*y + x", VARS).expect("parses");
        let (resultant, stages) =
            bivariate_resultant_predicted(&f, &g, 1, 1_000, ResultantOptions::default())
                .expect("both involve y");
        assert_eq!(stages.degree_source, DegreeSource::Proven);
        assert_eq!(stages.samples, stages.degree_bound + 1);
        assert_eq!(resultant, bivariate_resultant(&f, &g, 1).expect("ok"));
    }

    /// The off-domain validation cannot be switched off: asking for none panics.
    #[test]
    #[should_panic(expected = "validated off the domain")]
    fn test_the_off_domain_validation_is_not_optional() {
        let _ = ResultantOptions::default().with_off_domain_checks(0);
    }

    /// A predicted-count resultant is identical at concurrency 1, 8 and 32.
    ///
    /// The samples are indexed rather than collected, so the recovered coefficients cannot depend
    /// on which worker finished first — and the predicted route must inherit that, not only the
    /// proven one.
    #[test]
    fn test_the_predicted_route_is_identical_at_every_concurrency() {
        use rand::{prelude::StdRng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(0x180);
        let f = random_bivariate(4, 4, &mut rng);
        let g = random_bivariate(4, 4, &mut rng);
        let (single, stages) =
            bivariate_resultant_predicted(&f, &g, 1, 24, ResultantOptions::default())
                .expect("both involve y");
        for workers in [8usize, 32] {
            let (concurrent, cstages) = bivariate_resultant_predicted(
                &f,
                &g,
                1,
                24,
                ResultantOptions::with_concurrency(workers),
            )
            .expect("both involve y");
            assert_eq!(concurrent, single, "{workers} workers");
            assert_eq!(cstages.samples, stages.samples);
            assert_eq!(cstages.degree_source, stages.degree_source);
            assert_eq!(cstages.concurrency, workers);
        }
    }

    /// The off-domain validation runs on the **parallel** determinant path too, both ways.
    ///
    /// The hazard of composing a guard with a rewritten loop is that it stops executing silently.
    /// `PredictionHeld` is only reachable after the check passes and `PredictionFalsified` only
    /// after it fails, so observing both at concurrency 1, 8 and 32 shows the guard still decides
    /// after the checks themselves were spread over workers — and the recovered polynomial is
    /// compared across the three, because a verdict that agreed while the answer drifted would be
    /// worse than a verdict that flipped.
    #[test]
    fn test_the_off_domain_validation_runs_on_the_parallel_path() {
        use rand::{prelude::StdRng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(0x0ffd);
        let f = random_bivariate(4, 4, &mut rng);
        let g = random_bivariate(4, 4, &mut rng);
        let truth = bivariate_resultant(&f, &g, 1).expect("ok");
        // The true resultant has degree 4·4 + 4·4 = 32.
        for workers in [1usize, 8, 32] {
            let options = ResultantOptions::with_concurrency(workers);
            let (_, held) =
                bivariate_resultant_predicted(&f, &g, 1, 32, options).expect("both involve y");
            assert_eq!(
                held.degree_source,
                DegreeSource::Proven,
                "degree 32 is the proven bound itself at {workers} workers"
            );

            let (recovered, falsified) =
                bivariate_resultant_predicted(&f, &g, 1, 11, options).expect("both involve y");
            assert_eq!(
                falsified.degree_source,
                DegreeSource::PredictionFalsified { degree: 11 },
                "the check must still refuse a short count at {workers} workers"
            );
            assert_eq!(
                falsified.off_domain_checks,
                ResultantOptions::DEFAULT_OFF_DOMAIN_CHECKS,
                "and must have taken its checks"
            );
            assert_eq!(
                recovered, truth,
                "the fallback is the real resultant at {workers} workers"
            );
        }
    }

    /// The off-domain points are deterministic, distinct, and outside the sample set.
    #[test]
    fn test_the_off_domain_points_are_distinct_and_outside_the_sample_set() {
        let at = super::off_domain_abscissae::<Koala>(82, 8).expect("a 31-bit field has room");
        assert_eq!(at.len(), 8, "exactly the checks asked for");
        for x in &at {
            assert!(
                !(0..82u64).any(|i| *x == Koala::new(i)),
                "{x} is in the sample set"
            );
        }
        for (i, x) in at.iter().enumerate() {
            assert!(
                !at[i + 1..].contains(x),
                "{x} was drawn twice, which is not eight independent points"
            );
        }
        assert_eq!(
            at,
            super::off_domain_abscissae::<Koala>(82, 8).expect("again"),
            "the fixed seed makes the draw reproducible"
        );
    }

    /// A field with no room outside the sample set is reported, not looped on forever.
    #[test]
    fn test_the_off_domain_draw_refuses_a_field_with_no_room() {
        // Zp13's thirteen elements are all inside a sample set of twelve points but one.
        let error = super::off_domain_abscissae::<F>(12, 8).expect_err("no room for eight");
        assert_eq!(error, ResultantError::FieldTooSmall { needed: 20 });
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

    /// The subgroup route returns the same polynomial as Lagrange on randomized pairs.
    #[test]
    fn test_the_subgroup_route_agrees_with_lagrange_on_random_pairs() {
        use rand::{prelude::StdRng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(20261105);
        for degree_x in 1..=4u32 {
            for degree_y in 1..=4u32 {
                for _ in 0..4 {
                    let f = random_bivariate(degree_x, degree_y, &mut rng);
                    let g = random_bivariate(degree_x, degree_y, &mut rng);
                    let reference = bivariate_resultant(&f, &g, 1).expect("both involve y");
                    let (fast, stages) =
                        bivariate_resultant_ntt(&f, &g, 1).expect("both involve y");
                    assert!(
                        matches!(stages.route, ResultantRoute::Ntt { .. }),
                        "KoalaBear has a subgroup for {degree_x}/{degree_y}"
                    );
                    assert_eq!(fast, reference, "degrees {degree_x}, {degree_y}");
                }
            }
        }
    }

    /// Eliminating the other variable also agrees between the two routes.
    #[test]
    fn test_the_subgroup_route_agrees_when_the_first_variable_is_eliminated() {
        use rand::{prelude::StdRng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(7);
        for _ in 0..8 {
            let f = random_bivariate(3, 2, &mut rng);
            let g = random_bivariate(2, 3, &mut rng);
            let reference = bivariate_resultant(&f, &g, 0).expect("both involve x");
            let (fast, _) = bivariate_resultant_ntt(&f, &g, 0).expect("both involve x");
            assert_eq!(fast, reference);
        }
    }

    /// A common factor gives the identically zero resultant on the subgroup route too.
    #[test]
    fn test_the_subgroup_route_on_a_zero_resultant() {
        let f = MultivariatePolynomial::<2, Koala>::parse("y^2 - x^2", VARS).expect("parses");
        let g = MultivariatePolynomial::<2, Koala>::parse("y^3 - x^2*y", VARS).expect("parses");
        let (resultant, _) = bivariate_resultant_ntt(&f, &g, 1).expect("both involve y");
        assert!(resultant.is_zero());
        assert_eq!(resultant, bivariate_resultant(&f, &g, 1).expect("ok"));
    }

    /// With no surviving variable in either input the resultant is a nonzero constant.
    #[test]
    fn test_the_subgroup_route_on_a_constant_resultant() {
        let f = MultivariatePolynomial::<2, Koala>::parse("y^2 + 1", VARS).expect("parses");
        let g = MultivariatePolynomial::<2, Koala>::parse("y^2 + 2", VARS).expect("parses");
        let (resultant, stages) = bivariate_resultant_ntt(&f, &g, 1).expect("both involve y");
        assert_eq!(stages.degree_bound, 0, "no x in either input");
        assert_eq!(resultant.degree(), 0);
        assert!(!resultant.is_zero());
        assert_eq!(resultant, bivariate_resultant(&f, &g, 1).expect("ok"));
    }

    /// An input of degree zero in the surviving variable is handled by the subgroup route.
    #[test]
    fn test_the_subgroup_route_with_one_input_of_degree_zero_in_x() {
        let f = MultivariatePolynomial::<2, Koala>::parse("y^2 + y + 1", VARS).expect("parses");
        let g = MultivariatePolynomial::<2, Koala>::parse("y - x", VARS).expect("parses");
        let (resultant, _) = bivariate_resultant_ntt(&f, &g, 1).expect("both involve y");
        assert_eq!(resultant, bivariate_resultant(&f, &g, 1).expect("ok"));
        // Substituting y = x into f gives x^2 + x + 1, whose roots are the common ones.
        for at in 0u64..32 {
            let x = Koala::new(at);
            let expected = x * x + x + Koala::one();
            assert_eq!(resultant.eval(&x).is_zero(), expected.is_zero(), "at {at}");
        }
    }

    /// A vanishing leading coefficient is still recovered, though zero is not in the subgroup.
    ///
    /// The multiplicative subgroup never contains 0, so unlike the reference route this one never
    /// samples the point where `f`'s leading coefficient in `y` vanishes — and the interpolated
    /// polynomial is nonetheless correct there.
    #[test]
    fn test_the_subgroup_route_with_a_vanishing_leading_coefficient() {
        let f = MultivariatePolynomial::<2, Koala>::parse("x*y^2 + y + 1", VARS).expect("parses");
        let g = MultivariatePolynomial::<2, Koala>::parse("y - x", VARS).expect("parses");
        let (resultant, _) = bivariate_resultant_ntt(&f, &g, 1).expect("both involve y");
        assert_eq!(resultant, bivariate_resultant(&f, &g, 1).expect("ok"));
        assert_eq!(
            resultant.eval(&Koala::zero()),
            sylvester_determinant_at(&f, &g, 1, Koala::zero()).expect("both involve y")
        );
    }

    /// An input free of the eliminated variable is refused by the subgroup route by argument.
    #[test]
    fn test_the_subgroup_route_refuses_degree_zero_in_the_eliminated_variable() {
        let f = MultivariatePolynomial::<2, Koala>::parse("x^2 + 1", VARS).expect("parses");
        let g = MultivariatePolynomial::<2, Koala>::parse("y - x", VARS).expect("parses");
        assert_eq!(
            bivariate_resultant_ntt(&f, &g, 1).err(),
            Some(ResultantError::NoDegreeInEliminatedVariable { argument: 0 })
        );
        assert_eq!(
            bivariate_resultant_ntt(&g, &f, 1).err(),
            Some(ResultantError::NoDegreeInEliminatedVariable { argument: 1 })
        );
    }

    /// A field whose two-adicity is too small dispatches to the reference route, not to garbage.
    ///
    /// Mersenne-31 has two-adicity 1, so no power-of-two subgroup above size two exists at all.
    #[test]
    fn test_a_field_without_a_large_enough_subgroup_dispatches_to_lagrange() {
        let f = MultivariatePolynomial::<2, Mersenne31>::parse("x^2*y^2 + y + 1", VARS)
            .expect("parses");
        let g = MultivariatePolynomial::<2, Mersenne31>::parse("x*y^2 + 3*y + x", VARS)
            .expect("parses");
        let (resultant, stages) = bivariate_resultant_ntt(&f, &g, 1).expect("both involve y");
        assert_eq!(
            stages.route,
            ResultantRoute::Lagrange {
                points: stages.degree_bound + 1
            }
        );
        assert_eq!(resultant, bivariate_resultant(&f, &g, 1).expect("ok"));
    }

    /// The domain chosen for the four-round shape is 2^14, which covers the proven bound 13 123.
    #[test]
    fn test_the_domain_covers_the_degree_bound() {
        // Two polynomials of degree 81 in each variable: the bound is 81·81 + 81·81 = 13 122.
        let bound = 2 * 81 * 81;
        assert_eq!(bound, 13_122);
        assert_eq!(
            interpolation_route::<Koala>(bound),
            ResultantRoute::Ntt { log_size: 14 }
        );
        // `> bound` rather than `>= bound + 1`: the domain must hold more points than the bound,
        // which is what makes the interpolation exact.
        assert!(1usize << 14 > bound, "16 384 > 13 122");
        // Exactly at a power of two the domain is that power, and one above it doubles.
        assert_eq!(
            interpolation_route::<Koala>(255),
            ResultantRoute::Ntt { log_size: 8 }
        );
        assert_eq!(
            interpolation_route::<Koala>(256),
            ResultantRoute::Ntt { log_size: 9 }
        );
        // Beyond KoalaBear's two-adicity of 24 there is no domain and the reference is used.
        assert_eq!(
            interpolation_route::<Koala>(1 << 24),
            ResultantRoute::Lagrange {
                points: (1 << 24) + 1
            }
        );
        // Mersenne-31's two-adicity is 1, so only a bound of 0 or 1 has a domain.
        assert_eq!(
            interpolation_route::<Mersenne31>(1),
            ResultantRoute::Ntt { log_size: 1 }
        );
        assert_eq!(
            interpolation_route::<Mersenne31>(2),
            ResultantRoute::Lagrange { points: 3 }
        );
    }

    /// The recovered resultant agrees with the determinant at points outside the domain.
    ///
    /// The independent check the four-round run uses: the subgroup is the set of `2^k`-th roots of
    /// unity, so any element whose order is odd — 0 included — lies outside it.
    #[test]
    fn test_the_recovered_resultant_agrees_off_the_interpolation_domain() {
        use rand::{prelude::StdRng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(99);
        let f = random_bivariate(4, 4, &mut rng);
        let g = random_bivariate(4, 4, &mut rng);
        let (resultant, stages) = bivariate_resultant_ntt(&f, &g, 1).expect("both involve y");
        let ResultantRoute::Ntt { log_size } = stages.route else {
            panic!("KoalaBear has a subgroup here");
        };
        let domain_size = 1u128 << log_size;
        let mut checked = 0;
        for at in 0u64..64 {
            let x = Koala::new(at);
            // In the subgroup exactly when x^{2^k} = 1; skip those, they are the samples.
            if x.pow(domain_size).is_one() {
                continue;
            }
            assert_eq!(
                resultant.eval(&x),
                sylvester_determinant_at(&f, &g, 1, x).expect("both involve y"),
                "at {at}"
            );
            checked += 1;
        }
        assert!(checked > 0, "some point lies outside the domain");
    }

    /// The concurrency the determinants are spread over cannot be zero.
    #[test]
    #[should_panic(expected = "at least one worker")]
    fn test_zero_workers_is_refused() {
        let _ = ResultantOptions::with_concurrency(0);
    }

    /// Both routes return byte-identical coefficients at concurrency 1, 8 and 32.
    ///
    /// The determinism the whole parallel path rests on. The samples are written into their own
    /// index rather than collected as they finish, so the interpolation sees the same sequence at
    /// every worker count — and a coefficient that moved would mean the index bookkeeping is
    /// wrong, not that the hardware is noisy.
    #[test]
    fn test_the_resultant_does_not_depend_on_the_concurrency() {
        use rand::{prelude::StdRng, SeedableRng};

        const WORKERS: [usize; 3] = [1, 8, 32];
        let mut rng = StdRng::seed_from_u64(0x180);
        for (degree_x, degree_y) in [(4u32, 4u32), (5, 3), (3, 5)] {
            let f = random_bivariate(degree_x, degree_y, &mut rng);
            let g = random_bivariate(degree_x, degree_y, &mut rng);
            let mut subgroup = None;
            let mut lagrange = None;
            for workers in WORKERS {
                let options = ResultantOptions::with_concurrency(workers);
                let (ntt, stages) =
                    bivariate_resultant_ntt_with(&f, &g, 1, options).expect("both involve y");
                assert_eq!(stages.concurrency, workers, "the stages report the workers");
                let (reference, _) =
                    bivariate_resultant_reference_with(&f, &g, 1, options).expect("both involve y");
                assert_eq!(ntt, reference, "the two routes agree at {workers} workers");
                match (&subgroup, &lagrange) {
                    (None, None) => {
                        subgroup = Some(ntt);
                        lagrange = Some(reference);
                    }
                    (Some(first_ntt), Some(first_reference)) => {
                        assert_eq!(&ntt, first_ntt, "subgroup route at {workers} workers");
                        assert_eq!(
                            &reference, first_reference,
                            "reference route at {workers} workers"
                        );
                    }
                    _ => unreachable!("both are set together"),
                }
            }
        }
    }

    /// More workers than samples leaves no sample unevaluated.
    ///
    /// The tail block of the static split is shorter than the rest, and a sample dropped there
    /// would interpolate a *different* polynomial rather than fail — so the small-domain case is
    /// checked against the single-threaded answer directly.
    #[test]
    fn test_more_workers_than_samples_still_evaluates_every_sample() {
        let f = MultivariatePolynomial::<2, Koala>::parse("x*y^2 + y + 1", VARS).expect("parses");
        let g = MultivariatePolynomial::<2, Koala>::parse("y - x", VARS).expect("parses");
        let (sequential, stages) = bivariate_resultant_ntt(&f, &g, 1).expect("both involve y");
        assert!(stages.samples < 32, "fewer samples than workers");
        for workers in [2usize, 7, 32, 64] {
            let (parallel, _) = bivariate_resultant_ntt_with(
                &f,
                &g,
                1,
                ResultantOptions::with_concurrency(workers),
            )
            .expect("both involve y");
            assert_eq!(parallel, sequential, "{workers} workers");
        }
    }

    /// A fit to exact cubic data recovers exponent 3 with zero residuals.
    #[test]
    fn test_the_power_law_fit_recovers_an_exact_cubic() {
        let points: Vec<(f64, f64)> = [18.0, 162.0, 486.0, 1458.0]
            .into_iter()
            .map(|order: f64| (order, 7.0 * order.powi(3)))
            .collect();
        let fit = super::fit_power_law(&points).expect("four positive points");
        assert!((fit.exponent - 3.0).abs() < 1e-9, "{}", fit.exponent);
        assert!((fit.prefactor - 7.0).abs() < 1e-6, "{}", fit.prefactor);
        assert!(fit.worst_residual() < 1e-9, "{}", fit.worst_residual());
        assert_eq!(fit.residuals.len(), 4, "one residual per input point");
    }

    /// Curved log-log data is reported with a per-point residual rather than as a clean fit.
    #[test]
    fn test_the_power_law_fit_reports_residuals_on_curved_data() {
        // Sub-cubic at the bottom, super-cubic at the top: the shape the three determinant timings
        // on record have. A rising local slope is *convex* in log-log, so a single straight line
        // through it over-predicts the middle and under-predicts both ends — and no single
        // exponent can describe it.
        let points = [(18.0, 8.5e-6), (162.0, 2.868e-3), (1458.0, 2.70)];
        let fit = super::fit_power_law(&points).expect("three positive points");
        assert!(fit.worst_residual() > 0.05, "{}", fit.worst_residual());
        assert!(fit.exponent_stderr > 0.0, "three points estimate a spread");
        assert!(
            fit.residuals[1] > 0.0,
            "the middle is over-predicted: {:?}",
            fit.residuals
        );
        assert!(
            fit.residuals[0] < 0.0 && fit.residuals[2] < 0.0,
            "and both ends under-predicted: {:?}",
            fit.residuals
        );
    }

    /// A fit needs two distinct positive abscissae, and refuses rather than inventing an exponent.
    #[test]
    fn test_the_power_law_fit_refuses_data_it_cannot_constrain() {
        assert!(super::fit_power_law(&[]).is_none(), "no points");
        assert!(super::fit_power_law(&[(162.0, 1.0)]).is_none(), "one point");
        assert!(
            super::fit_power_law(&[(162.0, 1.0), (162.0, 2.0)]).is_none(),
            "one distinct abscissa"
        );
        assert!(
            super::fit_power_law(&[(0.0, 1.0), (162.0, 2.0)]).is_none(),
            "a logarithm of zero"
        );
    }

    /// A timed batch reports the order, the count, the footprint, and the values themselves.
    #[test]
    fn test_a_timed_determinant_batch_reports_its_shape() {
        use rand::{prelude::StdRng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(0xd00d);
        let f = random_bivariate(1, 9, &mut rng);
        let g = random_bivariate(1, 9, &mut rng);
        let at: Vec<Koala> = (1..=12u64).map(Koala::new).collect();
        let (values, batch) =
            super::time_sylvester_determinants(&f, &g, 1, &at, 1, DeterminantKernel::Dense)
                .expect("both involve y");
        assert_eq!(batch.matrix_order, 18, "9 + 9");
        assert_eq!(batch.determinants, 12);
        assert_eq!(batch.concurrency, 1);
        assert_eq!(
            batch.matrix_bytes,
            18 * 18 * std::mem::size_of::<Koala>(),
            "the dense matrix one worker builds"
        );
        assert!(batch.core_per_determinant() >= batch.wall_per_determinant());
        assert_eq!(
            batch.kernel,
            DeterminantKernel::Dense,
            "the kernel is recorded"
        );
        for (value, x) in values.iter().zip(&at) {
            assert_eq!(
                *value,
                sylvester_determinant_at(&f, &g, 1, *x).expect("both involve y"),
                "the batch evaluates the same determinant the single-point entry does"
            );
        }
    }

    /// The timed batch gives the same determinants at every concurrency, in the same index order.
    #[test]
    fn test_a_timed_determinant_batch_does_not_depend_on_the_concurrency() {
        use rand::{prelude::StdRng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(0xd00e);
        let f = random_bivariate(1, 5, &mut rng);
        let g = random_bivariate(1, 5, &mut rng);
        let at: Vec<Koala> = (1..=40u64).map(Koala::new).collect();
        // Both kernels, because the indexed hand-out is shared and neither may depend on width.
        for kernel in [DeterminantKernel::Dense, DeterminantKernel::Euclidean] {
            let (serial, _) =
                super::time_sylvester_determinants(&f, &g, 1, &at, 1, kernel).expect("ok");
            for workers in [8usize, 32] {
                let (parallel, batch) =
                    super::time_sylvester_determinants(&f, &g, 1, &at, workers, kernel)
                        .expect("ok");
                assert_eq!(parallel, serial, "{kernel} at {workers} workers");
                assert_eq!(batch.concurrency, workers);
                assert_eq!(batch.kernel, kernel);
            }
        }
    }

    /// Both resultant kernels agree at every point of the field, including the specialization
    /// points where a leading coefficient in the eliminated variable vanishes.
    #[test]
    fn euclidean_and_dense_kernels_agree_at_every_point_of_the_field() {
        // f's leading coefficient in y is x, which vanishes at exactly x = 0.
        let f = parse("x*y^2 + 3*y + x + 1");
        let g = parse("2*y^2 + x*y + 5");
        let fc = super::coefficients_in(&f, 1);
        let gc = super::coefficients_in(&g, 1);

        let mut saw_specialization = false;
        for i in 0..13u64 {
            let at = F::new(i);
            let dense = super::sylvester_determinant(&fc, &gc, at);
            let euclid = super::sylvester_resultant_euclid(&fc, &gc, at);
            assert_eq!(dense, euclid, "at x = {i}");
            if fc[fc.len() - 1].eval(&at).is_zero() {
                saw_specialization = true;
            }
        }
        // The test is only meaningful if the sweep actually hit a dropped degree.
        assert!(saw_specialization, "no specialization point in the sweep");
    }

    /// Over a large field the two kernels agree on random pairs at random points.
    #[test]
    fn euclidean_and_dense_kernels_agree_on_random_pairs() {
        let mut rng = rand::rngs::OsRng;
        for degree in 1..=4u32 {
            let f = random_bivariate(degree, degree, &mut rng);
            let g = random_bivariate(degree, degree, &mut rng);
            let fc = super::coefficients_in(&f, 1);
            let gc = super::coefficients_in(&g, 1);
            for i in 0..8u64 {
                let at = Koala::new(i * 7 + 1);
                assert_eq!(
                    super::sylvester_determinant(&fc, &gc, at),
                    super::sylvester_resultant_euclid(&fc, &gc, at),
                    "degree {degree}, at {i}"
                );
            }
        }
    }

    /// A run of coefficient polynomials shaped like a CICO row's: `fc[j]` of degree `degree - j`.
    fn coefficient_run<G: FiniteField>(degree: usize, seed: u64) -> Vec<UnivariatePolynomial<G>> {
        use rand::{prelude::StdRng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(seed);
        (0..=degree)
            .map(|j| UnivariatePolynomial::<G>::rand((degree - j) as u64, &mut rng))
            .collect()
    }

    /// The batched specialization is **bit-identical** to Horner at every sample.
    ///
    /// This is the test #598 rests on. `formal_determinant` does degree-sensitive case analysis on
    /// the specialized slices — the specialization trap of `structured-sylvester.md` §5.3 — so the
    /// batched route is safe exactly because it hands the kernels the same vectors, not merely
    /// equivalent ones.
    #[test]
    fn test_the_batched_specialization_matches_horner_elementwise() {
        type G = PrimeFieldElement64<2_147_483_647>;
        for degree in [0usize, 1, 2, 3, 7, 12] {
            let fc = coefficient_run::<G>(degree, 0x0598_0100 + degree as u64);
            for points in [1usize, 2, 3, 5, 40] {
                let at: Vec<G> = (0..points as u64).map(G::new).collect();
                let mut specializer = Specializer::new(&fc, &at);
                let mut column: Vec<G> = Vec::new();
                for x in &at {
                    specializer.next_into(&mut column);
                    let expected: Vec<G> = fc.iter().map(|c| c.eval(x)).collect();
                    assert_eq!(
                        column, expected,
                        "degree {}, {} points, at {}",
                        degree, points, x
                    );
                }
            }
        }
    }

    /// The same over a progression whose step is not one, and one that starts away from zero.
    #[test]
    fn test_the_batched_specialization_handles_any_progression() {
        type G = PrimeFieldElement64<2_147_483_647>;
        let fc = coefficient_run::<G>(6, 0x0598_0101);
        for (start, step) in [(0u64, 1u64), (5, 1), (0, 3), (100, 7)] {
            let at: Vec<G> = (0..32).map(|i| G::new(start + i * step)).collect();
            let mut specializer = Specializer::new(&fc, &at);
            let mut column: Vec<G> = Vec::new();
            for x in &at {
                specializer.next_into(&mut column);
                let expected: Vec<G> = fc.iter().map(|c| c.eval(x)).collect();
                assert_eq!(column, expected, "start {}, step {}", start, step);
            }
        }
    }

    /// A sample set that is not a progression falls back to Horner and is still exact.
    ///
    /// The subgroup route's domain is geometric and the off-domain validation points are random,
    /// so this is not a hypothetical: differencing either would be silently wrong.
    #[test]
    fn test_a_non_progression_sample_set_falls_back() {
        type G = PrimeFieldElement64<2_147_483_647>;
        let fc = coefficient_run::<G>(5, 0x0598_0102);

        // Geometric, as the subgroup route produces.
        let base = G::new(7);
        let geometric: Vec<G> = (0..24u32).map(|i| base.pow(i as u128)).collect();
        assert!(!Specializer::is_progression(&geometric));

        // Scattered, as the off-domain validation points are.
        let scattered: Vec<G> = [3u64, 17, 2, 99, 40, 11, 8]
            .iter()
            .map(|v| G::new(*v))
            .collect();
        assert!(!Specializer::is_progression(&scattered));

        for at in [geometric, scattered] {
            let mut specializer = Specializer::new(&fc, &at);
            let mut column: Vec<G> = Vec::new();
            for x in &at {
                specializer.next_into(&mut column);
                let expected: Vec<G> = fc.iter().map(|c| c.eval(x)).collect();
                assert_eq!(column, expected);
            }
        }
    }

    /// What counts as a progression, including the cases that must not.
    #[test]
    fn test_progression_detection() {
        type G = PrimeFieldElement64<2_147_483_647>;
        let of = |v: &[u64]| -> Vec<G> { v.iter().map(|x| G::new(*x)).collect() };
        assert!(Specializer::is_progression(&of(&[0, 1, 2, 3])));
        assert!(Specializer::is_progression(&of(&[10, 13, 16])));
        // A constant run has step zero, which no difference table can walk.
        assert!(!Specializer::is_progression(&of(&[4, 4, 4, 4])));
        // Too short to establish a step.
        assert!(!Specializer::is_progression(&of(&[0, 1])));
        assert!(!Specializer::is_progression(&of(&[0])));
        assert!(!Specializer::is_progression(&of(&[])));
        // A broken step anywhere disqualifies the whole run.
        assert!(!Specializer::is_progression(&of(&[0, 1, 2, 4])));
    }

    /// `sample_determinants` is unchanged by #598, at every concurrency and on both kernels.
    ///
    /// The blocks now carry difference tables, so a worker's block is a sub-progression with a
    /// later start — which is why the output has to be asserted independent of how the blocks were
    /// cut, not merely correct at concurrency one.
    #[test]
    fn test_the_sweep_is_unchanged_by_batching_and_by_block_count() {
        type G = PrimeFieldElement64<2_147_483_647>;
        let fc = coefficient_run::<G>(4, 0x0598_0103);
        let gc = coefficient_run::<G>(3, 0x0598_0104);
        let at: Vec<G> = (0..37u64).map(G::new).collect();

        for kernel in [DeterminantKernel::Dense, DeterminantKernel::Euclidean] {
            // The per-point reference, which is what the sweep did before #598.
            let expected: Vec<G> = at
                .iter()
                .map(|x| determinant_at(&fc, &gc, *x, kernel))
                .collect();
            for concurrency in [1usize, 2, 3, 4, 8, 37, 64] {
                let actual = sample_determinants(&fc, &gc, &at, concurrency, kernel);
                assert_eq!(
                    actual, expected,
                    "{:?} kernel at concurrency {}",
                    kernel, concurrency
                );
            }
        }
    }

    /// A block shorter than a polynomial's degree cannot hold a table, and falls back per point.
    ///
    /// Reached by asking for more workers than the progression has room for: at concurrency 37 over
    /// 37 points every block is a single sample, which is below every table's length.
    #[test]
    fn test_blocks_too_short_for_a_table_still_agree() {
        type G = PrimeFieldElement64<2_147_483_647>;
        let fc = coefficient_run::<G>(9, 0x0598_0105);
        let gc = coefficient_run::<G>(9, 0x0598_0106);
        let at: Vec<G> = (0..12u64).map(G::new).collect();
        let expected: Vec<G> = at
            .iter()
            .map(|x| determinant_at(&fc, &gc, *x, DeterminantKernel::Euclidean))
            .collect();
        for concurrency in [1usize, 6, 12, 24] {
            assert_eq!(
                sample_determinants(&fc, &gc, &at, concurrency, DeterminantKernel::Euclidean),
                expected,
                "concurrency {}",
                concurrency
            );
        }
    }
}

#[cfg(test)]
mod extraction_cost_509 {
    use super::{coefficients_in, sylvester_determinant, sylvester_determinant_at};
    use crate::{fields::PrimeFieldElement64, FiniteField};
    use rand::SeedableRng;
    use std::time::Instant;

    type Koala = PrimeFieldElement64<2_130_706_433>;

    /// Prints the per-call price of the two `coefficients_in` extractions against the determinant.
    #[test]
    #[ignore = "a timing probe for #509, not a check"]
    fn probe_extraction_cost() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(509);
        for degree_y in [20u32, 81] {
            let f = super::random_bivariate::<Koala, _>(81, degree_y, &mut rng);
            let g = super::random_bivariate::<Koala, _>(81, degree_y, &mut rng);
            let at = <Koala as FiniteField>::new(7);
            let reps = 200;
            let mut best_extract = f64::MAX;
            let mut best_det = f64::MAX;
            let mut best_at = f64::MAX;
            for _ in 0..5 {
                let start = Instant::now();
                for _ in 0..reps {
                    std::hint::black_box(coefficients_in(std::hint::black_box(&f), 1));
                    std::hint::black_box(coefficients_in(std::hint::black_box(&g), 1));
                }
                best_extract = best_extract.min(start.elapsed().as_secs_f64() / reps as f64);
                let (fc, gc) = (coefficients_in(&f, 1), coefficients_in(&g, 1));
                let start = Instant::now();
                for _ in 0..reps / 10 {
                    std::hint::black_box(sylvester_determinant(&fc, &gc, at));
                }
                best_det = best_det.min(start.elapsed().as_secs_f64() / (reps / 10) as f64);
                let start = Instant::now();
                for _ in 0..reps / 10 {
                    std::hint::black_box(sylvester_determinant_at(&f, &g, 1, at).unwrap());
                }
                best_at = best_at.min(start.elapsed().as_secs_f64() / (reps / 10) as f64);
            }
            println!(
                "order={} terms={}+{} extract={:.4} ms det={:.4} ms det_at={:.4} ms",
                2 * degree_y,
                f.terms().len(),
                g.terms().len(),
                best_extract * 1e3,
                best_det * 1e3,
                best_at * 1e3
            );
        }
    }
}
