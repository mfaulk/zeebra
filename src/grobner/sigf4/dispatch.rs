//! The opt-in entry point (#905): a pre-solve dispatch between the shipping F4 and the signature
//! engine. The rule reads only the input's size and degrees, never an instance name or digest, so
//! it costs one pass over the generators' terms; it never hands a solve over midway (plan §4.2).
//!
//! The rule is asymmetric on purpose. Sending an input to the shipping F4 that the signature
//! engine would have won costs only the saving; sending Cyclic-7 the other way cost 4.6× (#904).
//! So the signature engine is taken only where every measured row favoured it, and
//! `docs/research/m31-sigf4-dispatch.md` records the evidence for each threshold.

use std::time::{Duration, Instant};

use super::{engine, SigF4Error, SigF4Options, SigF4Statistics};
use crate::{
    grobner::f4::{f4_reported, F4Error, F4Options},
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

/// Which engine the entry point ran, and why.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum SignatureRoute {
    /// The signature engine, on the workers `F4Options` allows.
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
    /// The signature engine crossed one of its own size limits, which its signature basis and
    /// matrices can reach before the shipping F4's would, and the shipping F4 was run instead with
    /// the wall budget that remained.
    Fallback(F4Error),
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
}

/// What [`f4_signature_reported`] decided, and what deciding cost.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignatureDispatch {
    pub route: SignatureRoute,
    pub features: DispatchFeatures,
    /// Wall time spent computing the features and the route.
    pub dispatch: Duration,
}

/// The route [`f4_signature`] takes for these generators, and the features it read.
///
/// # Errors
/// [`SigF4Error::Unsupported`] for every non-graded order (`Lexicographic`, `Weighted`, `Block`).
pub fn signature_route<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Result<(SignatureRoute, DispatchFeatures), SigF4Error> {
    engine::graded(order)?;
    let mut used = [false; N];
    let mut features = DispatchFeatures::default();
    for p in generators.iter().filter(|p| !p.is_zero()) {
        features.generators += 1;
        for m in p.terms().keys() {
            for (seen, &e) in used.iter_mut().zip(m.exponents()) {
                *seen |= e > 0;
            }
        }
        let degree = p.degree();
        features.max_degree = features.max_degree.max(degree);
        if degree > 1
            && (features.min_nonlinear_degree == 0 || degree < features.min_nonlinear_degree)
        {
            features.min_nonlinear_degree = degree;
        }
    }
    features.variables = used.iter().filter(|&&u| u).count();
    let route = if features.min_nonlinear_degree == 0 {
        SignatureRoute::Shipping(ShippingReason::Linear)
    } else if features.variables < SIGNATURE_MIN_VARIABLES {
        SignatureRoute::Shipping(ShippingReason::Small)
    } else if features.max_degree - features.min_nonlinear_degree > SIGNATURE_MAX_DEGREE_SPREAD {
        SignatureRoute::Shipping(ShippingReason::DegreeSpread)
    } else {
        SignatureRoute::Signature
    };
    Ok((route, features))
}

/// The reduced Gröbner basis under a graded `order`, by the signature engine where the pre-solve
/// dispatch expects it to win and by the shipping F4 elsewhere. The output is the same reduced
/// basis [`crate::grobner::f4_with_options`] returns, coefficient for coefficient.
///
/// From `options` the signature engine takes the wall, basis-size, matrix and live-byte budgets,
/// [`F4Options::certify`] with [`F4Options::max_certify_time`], and its worker count from
/// `parallel_forward` and `parallel_symbolic`; more than one worker runs its parallel cascade. The
/// shipping route uses `options` unchanged.
///
/// # Performance caveat
/// The dispatch thresholds were fitted to M31's corpus. Two held-out rows favoured the signature
/// route, but other families are not covered. Dense random quadratic systems pass the rule yet ran
/// 1.6–1.75× *slower* than [`crate::grobner::f4_with_options`] at 16 workers (MQ10, #927),
/// because the signature engine's symbolic stage is serial. Measure your own systems before
/// preferring this entry point; [`f4_signature_reported`] reports which route ran.
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

/// As [`f4_signature`], with the route taken and the dispatch's cost.
///
/// When the dispatch refuses the order, the report's route is [`SignatureRoute::Signature`]
/// with default features: no engine ran.
pub fn f4_signature_reported<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> (
    Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error>,
    SignatureDispatch,
) {
    let started = Instant::now();
    let decided = signature_route(generators, order);
    let dispatch = started.elapsed();
    let (route, features) = match decided {
        Ok(decided) => decided,
        Err(refusal) => {
            let report = SignatureDispatch {
                route: SignatureRoute::Signature,
                features: DispatchFeatures::default(),
                dispatch,
            };
            return (Err(refusal), report);
        }
    };
    let mut report = SignatureDispatch {
        route,
        features,
        dispatch,
    };
    if report.route != SignatureRoute::Signature {
        return (shipping(generators, order, options), report);
    }
    let mut statistics = SigF4Statistics::default();
    let result = engine::run(
        generators,
        order,
        &signature_options(options),
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

/// The signature engine's budgets and workers, read from the shipping F4's options.
pub(super) fn signature_options(options: &F4Options) -> SigF4Options {
    let workers = options
        .parallel_forward
        .max_workers()
        .max(options.parallel_symbolic.workers());
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
