//! The opt-in entry point (#905): a pre-solve dispatch between the shipping F4 and the signature
//! engine. The rule reads only the input's size, degrees and density, the caller's worker cap and
//! the field's width, never an instance name or digest, so it costs one pass over the generators'
//! terms; it never hands a solve over midway (plan §4.2).
//!
//! The rule is asymmetric on purpose. Sending an input to the shipping F4 that the signature
//! engine would have won costs only the saving; sending Cyclic-7 the other way cost 4.6× (#904).
//! So the signature engine is taken only where every measured row favoured it.
//! `docs/research/m31-sigf4-dispatch.md` records the evidence for the M31 thresholds and
//! `docs/research/m32-adaptive-dispatch.md` for the worker-aware ones (#927).

use std::{
    ops::RangeInclusive,
    time::{Duration, Instant},
};

use super::{engine, SigF4Error, SigF4Options, SigF4Statistics};
use crate::{
    grobner::{
        f4::{f4_reported, F4Error, F4Options},
        planning::monomials_up_to_degree,
    },
    poly::MonomialOrder,
    FiniteField, MultivariatePolynomial,
};

/// Fewer variables than this go to the shipping F4: such a solve is process startup on both
/// engines (katsura-4 runs 6 ms on every arm), and at 16 workers the signature engine's per-batch
/// thread team cost it 8% there (`docs/research/m31-baseline.md` §3.1).
pub const SIGNATURE_MIN_VARIABLES: usize = 6;

/// The widest spread of nonlinear generator degrees the signature engine is given. Cyclic-n
/// (degrees 2, …, n) outgrows its reduced basis 15–90× in signature elements and ran 2–37× slower
/// serially; every row with nonlinear degrees within one of each other ran faster.
pub const SIGNATURE_MAX_DEGREE_SPREAD: u64 = 1;

/// From this many workers a quadratic input in [`SIGNATURE_CROSSOVER_VARIABLES`] goes to the
/// shipping F4. On MQ10 the shipping F4 scales 4.1–4.5× from one to 16 workers and the signature
/// engine 1.25×, its symbolic stage being serial; they cross at four.
pub const SIGNATURE_CROSSOVER_WORKERS: usize = 4;

/// The variable counts of quadratic inputs the worker crossover applies to. **Fitted to MQ10
/// alone** (#927): katsura-9 (9 variables) and katsura-11 and MQ11 (11) won at every worker
/// count, and no density, term count or degree feature separates MQ10 (95 terms, density 0.16)
/// from them. The band only ever moves an input to the shipping F4, so a miss loses the saving and
/// is never slower than the shipping F4 (`docs/research/m32-adaptive-dispatch.md`).
pub const SIGNATURE_CROSSOVER_VARIABLES: RangeInclusive<usize> = 10..=10;

/// Signature inputs in fewer variables than this run on at most [`SIGNATURE_SMALL_TEAM`] workers:
/// noon-7, noon-8 and katsura-9 ran 2–8% slower at 16 workers than at four.
pub const SIGNATURE_SMALL_TEAM_VARIABLES: usize = 10;

/// The team a small signature input runs on.
pub const SIGNATURE_SMALL_TEAM: usize = 4;

/// Which engine the entry point ran, and why.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum SignatureRoute {
    /// The signature engine, on [`SignatureDispatch::workers`] threads.
    Signature,
    /// The shipping F4, with exactly the caller's options.
    Shipping(ShippingReason),
}

/// Why the entry point ran the shipping F4.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ShippingReason {
    /// Fewer than [`SIGNATURE_MIN_VARIABLES`] variables appear.
    Small,
    /// No generator is nonlinear: there is no signature work to save.
    Linear,
    /// The nonlinear degrees spread wider than [`SIGNATURE_MAX_DEGREE_SPREAD`].
    DegreeSpread,
    /// A quadratic input in [`SIGNATURE_CROSSOVER_VARIABLES`] with at least
    /// [`SIGNATURE_CROSSOVER_WORKERS`] workers, where the shipping F4's parallel elimination
    /// outruns the signature engine's serial symbolic stage.
    WorkerCrossover,
    /// The signature engine crossed one of its own size limits, which its signature basis and
    /// matrices can reach before the shipping F4's would, and the shipping F4 was run instead with
    /// the wall budget that remained.
    Fallback(F4Error),
}

/// How the signature engine finishes each batch's elimination.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cascade {
    /// Design 2's serial cascade pass.
    Serial,
    /// #904's prereduce + claim cascade on the team.
    Parallel,
}

/// The features the rule read. Computed before any solve.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DispatchFeatures {
    /// Variables that appear in some generator.
    pub variables: usize,
    /// Nonzero generators.
    pub generators: usize,
    /// Least total degree over the nonlinear generators; 0 when there are none.
    pub min_nonlinear_degree: u64,
    pub max_degree: u64,
    /// Nonzero terms over the nonzero generators.
    pub terms: usize,
    /// Monomials of degree at most each nonzero generator's degree in `variables` variables,
    /// summed: the terms a fully dense input would have.
    pub monomials: u64,
    /// The caller's worker cap: the larger of the forward and symbolic caps in `F4Options`.
    pub workers: usize,
    /// Bits in the field element's in-memory representation.
    pub field_bits: u32,
}

impl DispatchFeatures {
    /// `terms / monomials`; zero without a nonzero generator.
    pub fn density(&self) -> f64 {
        if self.monomials == 0 {
            0.0
        } else {
            self.terms as f64 / self.monomials as f64
        }
    }
}

/// What [`f4_signature_reported`] decided, and what deciding cost: the engine, the cascade and the
/// team, each separately.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignatureDispatch {
    pub route: SignatureRoute,
    /// The signature engine's cascade; `None` when the shipping F4 was chosen before any solve. A
    /// size fallback keeps the cascade the signature engine ran with.
    pub cascade: Option<Cascade>,
    /// Workers the chosen engine was allowed: on the signature route the team, never more than
    /// [`DispatchFeatures::workers`]; on the shipping route the caller's cap, unchanged.
    pub workers: usize,
    pub features: DispatchFeatures,
    /// Wall time spent computing the features and the decisions.
    pub dispatch: Duration,
}

/// The decisions [`f4_signature`] takes for these generators under `options`, without solving.
///
/// # Errors
/// [`SigF4Error::Unsupported`] for every non-graded order (`Lexicographic`, `Weighted`, `Block`).
pub fn signature_route<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> Result<SignatureDispatch, SigF4Error> {
    // The worker cap first, off the clock: an `Auto` cap reads the process's CPU count once per
    // process (about 100 µs of cgroup files, #752). M31's entry point paid it too, after its
    // clock, and the shipping F4 pays it on its first batch; it is not the rule's cost.
    let workers = caller_workers(options);
    let started = Instant::now();
    engine::graded(order)?;
    let mut used = [false; N];
    let mut degrees = Vec::with_capacity(generators.len());
    let mut features = DispatchFeatures {
        workers,
        field_bits: u32::try_from(8 * std::mem::size_of::<F>()).unwrap_or(u32::MAX),
        ..DispatchFeatures::default()
    };
    for p in generators.iter().filter(|p| !p.is_zero()) {
        features.generators += 1;
        features.terms += p.terms().len();
        for m in p.terms().keys() {
            for (seen, &e) in used.iter_mut().zip(m.exponents()) {
                *seen |= e > 0;
            }
        }
        let degree = p.degree();
        degrees.push(degree);
        features.max_degree = features.max_degree.max(degree);
        if degree > 1
            && (features.min_nonlinear_degree == 0 || degree < features.min_nonlinear_degree)
        {
            features.min_nonlinear_degree = degree;
        }
    }
    features.variables = used.iter().filter(|&&u| u).count();
    features.monomials = degrees
        .iter()
        .map(|&d| monomials_up_to_degree(features.variables, d))
        .fold(0, u64::saturating_add);
    let route = if features.min_nonlinear_degree == 0 {
        SignatureRoute::Shipping(ShippingReason::Linear)
    } else if features.variables < SIGNATURE_MIN_VARIABLES {
        SignatureRoute::Shipping(ShippingReason::Small)
    } else if features.max_degree - features.min_nonlinear_degree > SIGNATURE_MAX_DEGREE_SPREAD {
        SignatureRoute::Shipping(ShippingReason::DegreeSpread)
    } else if features.workers >= SIGNATURE_CROSSOVER_WORKERS
        && features.max_degree == 2
        && SIGNATURE_CROSSOVER_VARIABLES.contains(&features.variables)
    {
        SignatureRoute::Shipping(ShippingReason::WorkerCrossover)
    } else {
        SignatureRoute::Signature
    };
    let (cascade, workers) = if route == SignatureRoute::Signature {
        let team = if features.variables < SIGNATURE_SMALL_TEAM_VARIABLES {
            features.workers.min(SIGNATURE_SMALL_TEAM)
        } else {
            features.workers
        };
        let cascade = if team > 1 {
            Cascade::Parallel
        } else {
            Cascade::Serial
        };
        (Some(cascade), team)
    } else {
        (None, features.workers)
    };
    Ok(SignatureDispatch {
        route,
        cascade,
        workers,
        features,
        dispatch: started.elapsed(),
    })
}

/// The reduced Gröbner basis under a graded `order`, by the signature engine where the pre-solve
/// dispatch expects it to win and by the shipping F4 elsewhere. The output is the same reduced
/// basis [`crate::grobner::f4_with_options`] returns, coefficient for coefficient.
///
/// From `options` the signature engine takes the wall, basis-size, matrix and live-byte budgets,
/// [`F4Options::certify`] with [`F4Options::max_certify_time`], and a team of at most the larger
/// of the `parallel_forward` and `parallel_symbolic` caps, never more; more than one worker runs
/// its parallel cascade. The shipping route uses `options` unchanged.
///
/// # Performance caveat
/// The dispatch thresholds were fitted to the M31/M32 development corpus, eleven rows in five
/// families. Dense quadratic inputs go to the shipping F4 from four workers up only to at most ten
/// variables, a bound fitted to MQ10 against MQ11 alone (#927); other families are not covered.
/// Measure your own systems before preferring this entry point; [`f4_signature_reported`] reports
/// which route ran, on how many workers.
///
/// ```
/// use zeebra::{
///     fields::Zp32003,
///     grobner::{benchmark_systems::katsura, f4_signature, f4_with_options, F4Options},
///     MonomialOrder,
/// };
///
/// let system = katsura::<7, Zp32003>();
/// let order = MonomialOrder::GradedReverseLexicographic;
/// let options = F4Options::default();
/// let basis = f4_signature(&system, order, &options).unwrap();
/// assert_eq!(basis, f4_with_options(&system, order, &options).unwrap().0);
/// ```
///
/// # Errors
/// [`SigF4Error::Unsupported`] for a non-graded order, whatever the dispatch would choose;
/// [`SigF4Error::Budget`] for a crossed budget, a certification stop or a certification failure,
/// in the shipping F4's terms.
pub fn f4_signature<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error> {
    f4_signature_reported(generators, order, options).0
}

/// As [`f4_signature`], with the decisions taken and the dispatch's cost.
///
/// When the dispatch refuses the order, the report's route is [`SignatureRoute::Signature`]
/// with default features, no cascade and no workers: no engine ran.
pub fn f4_signature_reported<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> (
    Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error>,
    SignatureDispatch,
) {
    let started = Instant::now();
    let mut report = match signature_route(generators, order, options) {
        Ok(report) => report,
        Err(refusal) => {
            let report = SignatureDispatch {
                route: SignatureRoute::Signature,
                cascade: None,
                workers: 0,
                features: DispatchFeatures::default(),
                dispatch: started.elapsed(),
            };
            return (Err(refusal), report);
        }
    };
    if report.route != SignatureRoute::Signature {
        return (shipping(generators, order, options), report);
    }
    let mut statistics = SigF4Statistics::default();
    let result = engine::run(
        generators,
        order,
        &signature_options(options, report.workers),
        &mut statistics,
    );
    match result {
        Err(SigF4Error::Budget(limit)) if is_signature_size_limit(&limit) => {
            let remaining = options
                .max_wall_time
                .map(|budget| budget.saturating_sub(started.elapsed()));
            let fallback = F4Options {
                max_wall_time: remaining,
                ..options.clone()
            };
            report.route = SignatureRoute::Shipping(ShippingReason::Fallback(limit));
            (shipping(generators, order, &fallback), report)
        }
        result => (result, report),
    }
}

/// The larger of the forward and symbolic worker caps in `options`.
fn caller_workers(options: &F4Options) -> usize {
    options
        .parallel_forward
        .max_workers()
        .max(options.parallel_symbolic.workers())
}

/// The signature engine's budgets, read from the shipping F4's options, on `workers` threads.
fn signature_options(options: &F4Options, workers: usize) -> SigF4Options {
    SigF4Options {
        max_wall_time: options.max_wall_time,
        max_basis_elements: options.max_basis_elements,
        max_matrix_rows: options.max_matrix_rows,
        max_matrix_columns: options.max_matrix_columns,
        certify: options.certify,
        max_certify_time: options.max_certify_time,
        workers,
        parallel_cascade: workers > 1,
        max_live_bytes: Some(options.max_live_bytes),
        ..SigF4Options::default()
    }
}

/// Limits on quantities the signature engine holds more of than the shipping F4 does: its
/// signature basis outgrows the reduced one, and its batches are its own.
fn is_signature_size_limit(error: &F4Error) -> bool {
    matches!(
        error,
        F4Error::TooManyBasisElements { .. }
            | F4Error::TooManyRows { .. }
            | F4Error::TooManyColumns { .. }
            | F4Error::TooManyLiveBytes { .. }
    )
}

fn shipping<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error> {
    f4_reported(generators, order, options)
        .0
        .map_err(SigF4Error::Budget)
}

#[cfg(test)]
mod tests;
