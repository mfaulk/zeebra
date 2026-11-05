//! Faugère's F4 algorithm for computing a Gröbner basis.
//!
//! Buchberger reduces one S-polynomial at a time and throws most of that work away: on katsura-5
//! under grevlex, 39 of 49 reductions produce zero. F4 instead takes a whole batch of critical
//! pairs, works out symbolically which polynomial multiples the batch's reductions could possibly
//! need, lays them out as the rows of one sparse matrix over a finite field, and reduces the lot
//! by Gaussian elimination. The cancellations Buchberger pays full price to rediscover become row
//! operations shared across the batch.
//!
//! The pipeline is one module per stage:
//!
//! - [`symbolic`] turns a batch of pairs into a set of rows closed under reduction.
//! - [`macaulay`] lays those rows out as a sparse matrix with monomials for columns.
//! - [`crate::linalg::sparse`] reduces it.
//! - [`reduction`] extracts the rows whose leading monomial is new.
//!
//! [`super::buchberger`] is unchanged and remains the correctness oracle.
//!
//! See Faugère, J.-C. (1999), *A new efficient algorithm for computing Gröbner bases (F4)*,
//! Journal of Pure and Applied Algebra 139, 61-88, and `docs/MILESTONE-F4.md` for the invariants
//! this implementation is built on.

pub mod macaulay;
pub mod observer;
pub mod options;
pub mod reduction;
pub mod statistics;
pub mod structured;
pub mod symbolic;

#[cfg(test)]
mod tests;

pub use macaulay::{BuildBudgetExceeded, MacaulayMatrix};
pub use observer::{trace_batches, BatchObserver, BatchTrace, TracedBatch};
pub use options::{F4Error, F4Options, ReducerSelection, ReductionStrategy};
pub use reduction::{reduce_batch, reduce_batch_in, BatchOutcome};
pub use statistics::{BatchStatistics, F4Statistics, StageClock, StageTimings};
pub use symbolic::{
    symbolic_preprocessing, symbolic_preprocessing_with, symbolic_preprocessing_within, CacheMode,
    MonicBasis, MonicElement, Preprocessed, PreprocessedRow, ReducerCache, RowBudgetExceeded,
    RowKind, SymbolicCounts,
};

use crate::{
    grobner::{
        buchberger::reduce_grobner_basis,
        pairs::{CriterionCounts, PairQueue},
    },
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

/// The reduced Gröbner basis for the given polynomials, with respect to the given monomial order.
///
/// The same contract as [`super::buchberger`]: zero generators are ignored, duplicates are
/// dropped, the empty basis is returned for the zero ideal, `{1}` for an inconsistent system, and
/// the result is sorted by leading monomial in descending order. A reduced Gröbner basis is unique
/// for a given ideal and order, so the two functions return exactly the same thing.
///
/// # Errors
/// Returns an [`F4Error`] if a matrix or its elimination exceeds a limit in [`F4Options::default`].
/// A successful return is always a complete basis; nothing partial is ever returned as though it
/// were finished.
pub fn f4<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Result<Vec<MultivariatePolynomial<N, F>>, F4Error> {
    f4_with_options(generators, order, &F4Options::default()).map(|(basis, _)| basis)
}

/// As [`f4`], under the given limits, additionally reporting the work performed.
pub fn f4_with_options<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> Result<(Vec<MultivariatePolynomial<N, F>>, F4Statistics), F4Error> {
    f4_observed(generators, order, options, &mut observer::Ignore)
}

/// As [`f4_with_options`], returning the statistics accumulated even when a limit is crossed.
///
/// The diagnostic entry point, for a caller that has to say *what the computation did* before it
/// ran out of room — how many batches it got through, how large the matrices became, how badly
/// they filled in. `f4` and `f4_with_options` discard exactly that on the error path, and a
/// resource failure is the case where it matters most.
///
/// **A crossed budget still cannot be mistaken for a finished one**: the basis lives inside the
/// `Result`, so an incomplete computation has no basis to hand back. The statistics beside it
/// describe work, never an answer.
///
/// ```
/// use zeebra::{fields::Zp13, grobner::{f4_reported, F4Options}, MonomialOrder, MultivariatePolynomial};
///
/// let system = vec![MultivariatePolynomial::<2, Zp13>::parse("x^2 - y", ["x", "y"]).unwrap()];
/// let budget = F4Options { max_live_bytes: 16, ..F4Options::default() };
/// let (result, statistics) = f4_reported(&system, MonomialOrder::Lexicographic, &budget);
/// // The field's entry size is known even when nothing was built.
/// assert_eq!(statistics.bytes_per_entry, 16);
/// assert!(result.is_ok() || statistics.batches == 0);
/// ```
pub fn f4_reported<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> (
    Result<Vec<MultivariatePolynomial<N, F>>, F4Error>,
    F4Statistics,
) {
    let mut statistics = new_statistics::<F>();
    let basis = f4_into(
        generators,
        order,
        options,
        &mut observer::Ignore,
        &mut statistics,
    );
    (basis, statistics)
}

/// As [`f4_with_options`], notifying `observer` of each batch before it is reduced.
///
/// The instrumentation entry point. Generic over the observer rather than taking a trait object,
/// so that [`observer::Ignore`] — which every ordinary call uses — compiles to nothing. See
/// [`observer`] for why measuring stages on real batches needs this rather than a reimplemented
/// main loop.
///
/// # Errors
/// As [`f4_with_options`].
pub fn f4_observed<const N: usize, F: FiniteField, O: BatchObserver<N, F>>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
    observer: &mut O,
) -> Result<(Vec<MultivariatePolynomial<N, F>>, F4Statistics), F4Error> {
    let mut statistics = new_statistics::<F>();
    let basis = f4_into(generators, order, options, observer, &mut statistics)?;
    Ok((basis, statistics))
}

/// An accumulator that already knows the field's entry size.
///
/// Set before anything else, so that a computation which returns early — the zero ideal, an
/// unsatisfiable option, a budget crossed in the first batch — still reports it rather than zero.
fn new_statistics<F: FiniteField>() -> F4Statistics {
    F4Statistics {
        bytes_per_entry: F4Options::bytes_per_entry::<F>(),
        ..F4Statistics::default()
    }
}

/// The main loop, accumulating into a caller-owned `statistics`.
///
/// A `&mut` parameter rather than a return value for one reason: the counters have to survive the
/// error path, and a function that returns them can only do so by returning them *in* the error,
/// which would put work and failure in one type and make every existing `match` on `F4Error`
/// stop compiling.
fn f4_into<const N: usize, F: FiniteField, O: BatchObserver<N, F>>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
    observer: &mut O,
    statistics: &mut F4Statistics,
) -> Result<Vec<MultivariatePolynomial<N, F>>, F4Error> {
    let total_clock = StageClock::new(options.measure_stages);

    // A batch of no pairs makes no progress, so a zero limit is unsatisfiable rather than merely
    // strict. Rejected here, which is also what keeps `PairQueue::select_batch`'s precondition
    // from being reachable through this function.
    if options.max_pairs_per_batch == Some(0) {
        return Err(F4Error::InvalidOptions {
            reason: "max_pairs_per_batch of zero would select no pairs and make no progress",
        });
    }

    // A zero generator contributes nothing to the ideal, and would otherwise reach
    // `leading_coefficient().inverse()` with a zero coefficient. Duplicates are dropped too, so
    // they cannot produce pairs with themselves. Identical to Buchberger's handling, deliberately.
    let mut basis: Vec<MultivariatePolynomial<N, F>> = Vec::new();
    for p in generators.iter().filter(|p| !p.is_zero()) {
        let monic = p.scale(&p.leading_coefficient(order).inverse());
        if !basis.contains(&monic) {
            basis.push(monic);
        }
    }
    if basis.is_empty() {
        return Ok(Vec::new());
    }

    // The limit is on the basis, so it applies to the generators the caller supplied and not only
    // to what F4 appends. Checking it solely after an append let a system whose initial basis
    // already exceeded the limit return successfully, provided no candidate was ever produced —
    // `<x, y>` under a limit of one has its only pair eliminated by the product criterion, so
    // nothing is appended and nothing was checked.
    check_basis_size(basis.len(), options)?;

    let mut monic = MonicBasis::new(&basis, order);

    // The leading monomials, maintained alongside the basis. Pair handling needs them and nothing
    // else, and taking them from a polynomial is a scan of its whole term map — which the pair
    // queue would otherwise repeat once per pair created.
    let mut leads: Vec<Monomial<N>> = monic.leading_monomials().collect();

    let mut criteria_counts = CriterionCounts::default();
    let mut pending = PairQueue::seeded_from_leads(&leads, &options.criteria, &mut criteria_counts);
    let mut cache = ReducerCache::new(options.reducer_cache);

    // Terminates because each batch either consumes pairs without adding any, or produces a
    // candidate whose leading monomial is outside the leading-term ideal of the current basis —
    // which therefore grows strictly. An ascending chain of monomial ideals stabilizes, by
    // Dickson's lemma, so only finitely many candidates are ever produced.
    while !pending.is_empty() {
        let selected = pending.select_batch(options.max_pairs_per_batch);
        statistics.pairs_considered += selected.len();
        for pair in &selected {
            statistics.max_pair_degree = statistics.max_pair_degree.max(pair.degree);
        }

        // The pair criteria, applied before anything is built. A pair a criterion discards is one
        // whose S-polynomial is guaranteed to reduce to zero modulo relations the computation
        // already has, so there is no reason to put its rows in a matrix.
        let batch = pending.filter_batch(selected, &leads, &options.criteria, &mut criteria_counts);
        if batch.is_empty() {
            continue;
        }
        statistics.pairs_reduced += batch.len();

        // Checked here rather than at the top of the loop, so the limit counts matrices actually
        // built. A pass whose every pair is eliminated by a criterion builds nothing and must not
        // consume a batch's worth of budget.
        if let Some(limit) = options.max_batches {
            if statistics.batches >= limit {
                return Err(F4Error::TooManyBatches { limit });
            }
        }

        observer.batch(&monic, &batch);

        let outcome = reduce_batch_in(&monic, &batch, order, options, &mut cache)?;
        statistics.record(&outcome.statistics);

        for candidate in outcome.candidates {
            statistics.max_terms = statistics.max_terms.max(candidate.terms().len());
            let added = basis.len();
            // Already monic: elimination normalized every pivot to one.
            monic.push(&candidate, order);
            leads.push(monic.element(added).leading_monomial);
            basis.push(candidate);
            statistics.elements_added += 1;

            check_basis_size(basis.len(), options)?;

            // Only the pairs involving the new element are new.
            pending.push_pairs_from_leads(&leads, added, &options.criteria, &mut criteria_counts);
        }
    }

    statistics.criteria = criteria_counts;
    statistics.pairs_eliminated_by_product_criterion = criteria_counts.product;

    // Timed separately: on katsura-6 under lex it is the majority of the computation, which no
    // per-batch counter would have revealed — 59 matrices and a six-element answer, with the cost
    // in the reduction between them.
    let mut interreduction_clock = StageClock::new(options.measure_stages);
    let reduced = reduce_grobner_basis(&basis, order);
    statistics.stages.interreduction = interreduction_clock.lap();

    // Read last, so that everything is inside the total. What the stages do not account for is
    // pair selection and basis bookkeeping, which is what `stage_coverage` reports.
    statistics.total = total_clock.elapsed();

    Ok(reduced)
}

/// Reject a basis larger than `options` allows.
fn check_basis_size(elements: usize, options: &F4Options) -> Result<(), F4Error> {
    match options.max_basis_elements {
        Some(limit) if elements > limit => Err(F4Error::TooManyBasisElements { elements, limit }),
        _ => Ok(()),
    }
}
