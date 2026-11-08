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

pub mod budget;
pub mod certify;
pub mod degrees;
pub mod hilbert_driven;
pub(crate) mod interreduce;
pub mod macaulay;
pub mod observer;
pub mod options;
pub mod reduction;
pub mod statistics;
pub mod structured;
pub mod symbolic;

#[cfg(test)]
mod tests;

pub use budget::{Allowance, BudgetApproach, BudgetLine, BudgetReport};
pub use certify::{certify_f4_output, certify_submitted_basis, CertificationReport, Provenance};
pub use degrees::{DegreeProfile, DegreeStatistics};
pub use hilbert_driven::{HilbertSelection, SelectionLimits};
pub use macaulay::{BuildBudgetExceeded, MacaulayMatrix};
pub use observer::{trace_batches, BatchObserver, BatchTrace, TracedBatch};
pub use options::{
    F4Error, F4Options, InterreductionRoute, ReducerSelection, ReductionStrategy, StopKind,
};
pub use reduction::{reduce_batch, reduce_batch_in, BatchOutcome};
pub use statistics::{
    BatchStatistics, F4Statistics, HilbertCounts, MatrixInterreduction, MatrixRefusal, StageClock,
    StageTimings,
};
pub use symbolic::{
    symbolic_preprocessing, symbolic_preprocessing_with, symbolic_preprocessing_within, CacheMode,
    MonicBasis, MonicElement, Preprocessed, PreprocessedRow, ReducerCache, RowBudgetExceeded,
    RowKind, SymbolicCounts,
};

use std::time::Instant;

use crate::{
    grobner::{
        buchberger::{
            minimal_basis_for_interreduction, reduce_grobner_basis_counted,
            reduce_grobner_basis_measured, reduce_grobner_basis_until, InterreductionReport,
        },
        f4::interreduce::{
            interreduce_by_matrix, MatrixInterreductionAborted, MatrixInterreductionRefused,
        },
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

/// [`f4_observed`] and [`f4_reported`] at once: an observer, and statistics even on refusal.
///
/// The combination exists for a computation that is **expected not to finish**. A frontier run
/// needs the statistics from a crossed budget, which [`f4_observed`] discards with its `Err`, and
/// it needs per-batch notification so that an external supervisor can say how far the computation
/// had got if it had to be abandoned outright.
///
/// For a wall clock, prefer [`F4Options::max_wall_time`]: a cooperative stop **returns**, so the
/// statistics come back through this function's second element and the observer is not the only
/// account of the state. An external supervisor remains the right backstop for a single batch that
/// outlasts the budget, which no per-batch check can interrupt.
///
/// # Errors
/// As [`f4_with_options`], with the work done before the refusal in the statistics.
pub fn f4_observed_reported<const N: usize, F: FiniteField, O: BatchObserver<N, F>>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
    observer: &mut O,
) -> (
    Result<Vec<MultivariatePolynomial<N, F>>, F4Error>,
    F4Statistics,
) {
    let mut statistics = new_statistics::<F>();
    let basis = f4_into(generators, order, options, observer, &mut statistics);
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

    // `Some` only when a time budget was asked for. An `Option<Instant>` rather than an always-on
    // clock because the shipping path must contain no timing at all: `None` means the per-batch
    // check below reads nothing. Separate from `total_clock`, whose activation is tied to stage
    // measurement and which a caller may therefore have left off.
    let wall_clock = options.max_wall_time.map(|_| Instant::now());

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

    // How many terms each element has, which a pair cannot carry and a length-ranking schedule
    // needs. Maintained alongside `leads`, and append-only for the reason given on
    // `PairQueue::push_term_count`.
    let term_counts: Vec<usize> = (0..monic.len())
        .map(|index| monic.element(index).terms.len())
        .collect();

    // Terms across the whole basis, maintained rather than rescanned: the basis is stored twice
    // while the loop runs and three times during interreduction, and a term costs several times
    // what a matrix entry does, so this is the figure that says how much of a run's memory the
    // entry budget cannot see. Incremental because the shipping path must not pay for an O(|G|)
    // scan per batch.
    let mut basis_terms: usize = term_counts.iter().sum();

    let mut criteria_counts = CriterionCounts::default();
    let mut pending = PairQueue::seeded_from_leads_ranked(
        &leads,
        &term_counts,
        &options.criteria,
        options.schedule,
        order,
        &mut criteria_counts,
    );
    let mut cache = ReducerCache::new(options.reducer_cache);

    // The Hilbert prediction, computed once from the generators' degrees. A failure to compute it
    // is not fatal: the strategy becomes inert, which is counted, because a run whose cap was never
    // computed is not the same result as a run whose cap did not bite.
    let limits = if options.hilbert.is_active() {
        match SelectionLimits::new(generators, options.hilbert.slack()) {
            Ok(limits) => {
                statistics.hilbert.degree_of_regularity = limits.degree_of_regularity();
                Some(limits)
            }
            Err(_) => {
                statistics.hilbert.predictions_unavailable += 1;
                None
            }
        }
    } else {
        None
    };

    // Terminates because each batch either consumes pairs without adding any, or produces a
    // candidate whose leading monomial is outside the leading-term ideal of the current basis —
    // which therefore grows strictly. An ascending chain of monomial ideals stabilizes, by
    // Dickson's lemma, so only finitely many candidates are ever produced.
    //
    // `has_work` rather than `!is_empty`: a selection strategy may have deferred pairs out of the
    // pending set, and a computation with deferred pairs left is not finished. Promoting them is
    // what makes such a strategy complete — see [`hilbert_driven`].
    // The previous batch's selection degree, and whether it produced a relation below it. Both are
    // needed to attribute a drop in degree: a drop can also follow an ordinary batch, since a new
    // element of the batch's own degree can pair low with an old one.
    let mut previous_degree: Option<u64> = None;
    let mut previous_had_mutant = false;

    while pending.has_work() {
        if pending.is_empty() {
            statistics.hilbert.pairs_promoted += pending.promote_deferred();
            continue;
        }

        // The cap this batch is selected under: the caller's, and the prediction's where one
        // applies. The smaller of the two, so neither can be escaped by the other.
        let next_degree = pending.next_degree();
        let predicted_cap = limits
            .as_ref()
            .filter(|_| options.hilbert.limits())
            .and_then(|limits| {
                let degree = next_degree?;
                match limits.cap(degree, &leads) {
                    Some(cap) => Some(cap),
                    None => {
                        statistics.hilbert.predictions_unavailable += 1;
                        None
                    }
                }
            });
        let cap = match (options.max_pairs_per_batch, predicted_cap) {
            (Some(caller), Some(predicted)) => Some(caller.min(predicted)),
            (caller, None) => caller,
            (None, predicted) => predicted,
        };

        // Pairs available *at this degree*, not in the whole queue: a batch is formed from one
        // degree, so charging the cap with withholding pairs at a higher degree — which it was
        // never offered and which no cap could have taken — would overstate it severalfold.
        //
        // Counted **only when a cap could have bound**. `pending_at_degree` is a scan of the whole
        // heap, so computing it unconditionally would put O(pending) per batch on the default path,
        // where `hilbert` is `Off` and the result is unused. The default path should not pay for an
        // experimental counter, and should not rely on the optimizer to notice.
        let available = match (predicted_cap, next_degree) {
            (Some(_), Some(degree)) => pending.pending_at_degree(degree),
            _ => 0,
        };
        let selected = pending.select_batch(cap);
        if predicted_cap.is_some_and(|cap| cap < available) {
            statistics.hilbert.degrees_limited += 1;
            statistics.hilbert.pairs_withheld += available - selected.len();
        }
        statistics.pairs_considered += selected.len();
        for pair in &selected {
            statistics.max_pair_degree = statistics.max_pair_degree.max(pair.degree);
        }

        // One degree per batch: `select_batch` takes the pairs of the lowest degree available and
        // stops at the first pair above it. Read before filtering, so that a batch every criterion
        // discards is still filed under the degree it was selected at.
        let degree = selected.first().map_or(0, |pair| pair.degree);
        let considered = selected.len();

        // Did the schedule go *down*? F4 always selects the lowest pending degree, so a relation
        // that created lower-degree pairs is acted on at the very next batch — this records the
        // times that happened rather than arguing that it must. Counted before the criteria, since
        // the degree was selected whether or not a matrix follows.
        if let Some(previous) = previous_degree {
            if degree < previous {
                statistics.degree_regressions += 1;
                statistics.max_degree_drop = statistics.max_degree_drop.max(previous - degree);
                if previous_had_mutant {
                    statistics.regressions_after_mutants += 1;
                }
            }
        }
        previous_degree = Some(degree);
        previous_had_mutant = false;

        // The prediction's quota for this degree, recorded against what the degree yields. Taken
        // before the batch is reduced, since the basis grows during it.
        let quota = limits
            .as_ref()
            .and_then(|limits| limits.predicted_new_elements(degree, &leads));

        // The pair criteria, applied before anything is built. A pair a criterion discards is one
        // whose S-polynomial is guaranteed to reduce to zero modulo relations the computation
        // already has, so there is no reason to put its rows in a matrix.
        let batch = pending.filter_batch(selected, &leads, &options.criteria, &mut criteria_counts);
        if options.profile_degrees {
            statistics
                .degrees
                .record_selection(degree, considered, considered - batch.len());
        }
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

        // The cooperative time check, beside the batch limit and for the same reason: a budget
        // crossed between batches leaves the statistics describing whole batches. `wall_clock` is
        // `Some` only when a budget was asked for, so the default path reads no clock at all —
        // which is why this is not folded into `total_clock`, whose own activation is tied to
        // stage measurement.
        //
        // `statistics.batches > 0` is the one condition, and it is the point of the whole
        // mechanism rather than a guard against an edge case: #284 exists because a time-bounded
        // run reported no matrix statistics at all, and a stop before the first matrix would
        // reproduce that with a different error. One batch is therefore always reduced, so the
        // report is never empty. A budget too small to admit a single batch is not satisfiable by
        // any faster code, only by a smaller problem.
        if let (Some(clock), Some(budget)) = (wall_clock.as_ref(), options.max_wall_time) {
            let elapsed = clock.elapsed();
            if statistics.batches > 0 && elapsed >= budget {
                return Err(F4Error::TimeBudgetExceeded {
                    degree,
                    elapsed_millis: elapsed.as_millis().min(u128::from(u64::MAX)) as u64,
                    budget_millis: budget.as_millis().min(u128::from(u64::MAX)) as u64,
                });
            }
        }

        // The structures no budget bounds, sampled once per batch. Every figure here is a field
        // read or a maintained running total, so this is not a scan; see
        // `F4Statistics::peak_pair_queue` for why the pair queue in particular has to be reported
        // separately from the matrix.
        statistics.peak_pair_queue = statistics.peak_pair_queue.max(&pending.footprint());
        statistics.peak_basis_elements = statistics.peak_basis_elements.max(basis.len());
        statistics.peak_basis_terms = statistics.peak_basis_terms.max(basis_terms);

        // Once per batch, after the basis and the queue have both been mutated by the previous
        // iteration and before this one reads them. Recomputes every cached field rather than
        // trusting it; see `MonicBasis::check`. Debug-only, so release pays nothing.
        #[cfg(debug_assertions)]
        {
            monic.check();
            pending.check(&leads);
        }

        observer.batch(&monic, &batch);

        let outcome = reduce_batch_in(&monic, &batch, order, options, &mut cache)?;
        statistics.record(&outcome.statistics);
        // Beside `record`, which is what increments `batches`, so the sequence and the count stay
        // the same length by construction rather than by agreement.
        statistics.record_step_degree(degree);
        if options.profile_degrees {
            statistics.degrees.record(degree, &outcome.statistics);
        }
        if let Some(quota) = quota {
            statistics.hilbert.predicted_new_elements += quota;
            statistics.hilbert.observed_new_elements += outcome.statistics.candidates;
        }
        if outcome.statistics.candidates_below_batch_degree > 0 {
            statistics.batches_with_mutants += 1;
            previous_had_mutant = true;
            if let Some(lowest) = outcome.statistics.min_candidate_degree {
                statistics.max_mutant_degree_gap = statistics
                    .max_mutant_degree_gap
                    .max(degree.saturating_sub(lowest));
            }
        }

        // Having taken this degree's predicted quota, set the rest of it aside and move on. The
        // pairs are promoted back before the loop can end, so this reorders work and never skips
        // it — see [`hilbert_driven`] for why that is the only form of the idea the measurements
        // support.
        if options.hilbert.defers() && predicted_cap.is_some() {
            statistics.hilbert.pairs_deferred += pending.defer_degree(degree);
        }

        for candidate in outcome.candidates {
            statistics.max_terms = statistics.max_terms.max(candidate.terms().len());
            let added = basis.len();
            // Already monic: elimination normalized every pivot to one.
            monic.push(&candidate, order);
            leads.push(monic.element(added).leading_monomial);
            pending.push_term_count(monic.element(added).terms.len());
            basis_terms += monic.element(added).terms.len();
            basis.push(candidate);
            statistics.elements_added += 1;

            check_basis_size(basis.len(), options)?;

            // Only the pairs involving the new element are new.
            pending.push_pairs_from_leads(&leads, added, &options.criteria, &mut criteria_counts);
        }

        // Sampled again here, and this is the sample that matters: the one above is taken after
        // `select_batch` drained a degree, which is a local *minimum* of the heap. The pairs of
        // this batch's new elements have just been pushed, so this is the high-water mark.
        statistics.peak_pair_queue = statistics.peak_pair_queue.max(&pending.footprint());
    }

    statistics.criteria = criteria_counts;
    statistics.pairs_eliminated_by_product_criterion = criteria_counts.product;

    // The basis is largest when the loop ends, and the last batch's appends came after the last
    // per-batch sample. Taken before interreduction, which is where the basis is held three times
    // over.
    statistics.peak_basis_elements = statistics.peak_basis_elements.max(basis.len());
    statistics.peak_basis_terms = statistics.peak_basis_terms.max(basis_terms);

    // Timed separately: on katsura-6 under lex it is the majority of the computation, which no
    // per-batch counter would have revealed — 59 matrices and a six-element answer, with the cost
    // in the reduction between them.
    // The wall clock is checked **inside** this stage, not only in the batch loop above. #349
    // measured interreduction at 80.4% of `mq-random-10`, so a budget honored at every batch could
    // previously be overrun by four fifths of the computation (#395).
    // Everything the loop needed is dead here, and interreduction is where the basis peaks. Until
    // #304 the basis was live in **three** forms at this point: `basis`, `monic`, and the scaled
    // copy `minimize_grobner_basis` built. `monic`, `leads` and `pending` are dropped explicitly
    // rather than left to the end of the function, and `basis` is **moved** into the stage, so one
    // copy reaches it instead of three.
    drop(pending);
    drop(monic);
    drop(leads);
    drop(term_counts);

    let mut interreduction_clock = StageClock::new(options.measure_stages);
    let should_stop = || match (wall_clock.as_ref(), options.max_wall_time) {
        (Some(clock), Some(budget)) => clock.elapsed() >= budget,
        _ => false,
    };
    // The measured variant is the same code behind a const-generic flag, so the split and the
    // operation counters cannot drift from the path that runs when nothing is being measured.
    let mut report = InterreductionReport::default();
    let interreduction = if options.interreduction.builds_a_matrix(order) {
        // One matrix, not 247 divisions. The budgets are the batch loop's, so a basis whose
        // closure is too wide falls back rather than exceeding a limit the rest of the
        // computation obeyed — and the fallback is recorded, because a timing from a run that
        // fell back is a timing about the division route.
        let minimal = minimal_basis_for_interreduction(basis, order);
        // `minimal` is **moved** in, and handed back by `Refused` if a budget crosses, so the
        // fallback costs no clone. #304/#437 took this stage from three live copies of the basis
        // to one, and a fallback written with `minimal.clone()` would put a second one back for
        // the whole matrix pass.
        match interreduce_by_matrix(
            minimal,
            order,
            options.max_matrix_rows,
            options.max_matrix_columns,
            options.live_entry_allowance::<F>(),
            should_stop,
        ) {
            Ok((reduced, matrix)) => {
                statistics.interreduction_matrix = Some(MatrixInterreduction {
                    rows: matrix.rows,
                    columns: matrix.columns,
                    nonzeros: matrix.nonzeros,
                    peak_nonzeros: matrix.peak_nonzeros,
                    peak_entry_capacity: matrix.peak_entry_capacity,
                    elements: matrix.elements,
                    fell_back: false,
                    refused_by: None,
                });
                report.elements = matrix.elements;
                Ok(reduced)
            }
            Err(MatrixInterreductionAborted::Refused(reason, minimal, refused)) => {
                statistics.interreduction_matrix = Some(MatrixInterreduction {
                    // The shape as far as it was established before the refusal, so a `fell_back`
                    // row says *what* was refused. Zero throughout when the closure or the
                    // construction is what crossed, since there was no matrix to describe.
                    rows: refused.rows,
                    columns: refused.columns,
                    nonzeros: refused.nonzeros,
                    peak_nonzeros: refused.peak_nonzeros,
                    peak_entry_capacity: refused.peak_entry_capacity,
                    elements: minimal.len(),
                    fell_back: true,
                    refused_by: Some(match reason {
                        MatrixInterreductionRefused::Rows { limit } => {
                            MatrixRefusal::Rows { limit }
                        }
                        MatrixInterreductionRefused::Columns { limit } => {
                            MatrixRefusal::Columns { limit }
                        }
                        MatrixInterreductionRefused::Nonzeros { nonzeros } => {
                            MatrixRefusal::Nonzeros { nonzeros }
                        }
                        MatrixInterreductionRefused::LiveEntries { nonzeros } => {
                            MatrixRefusal::LiveEntries { nonzeros }
                        }
                    }),
                });
                // The division route always terminates inside the memory the old default used, so
                // a refusal is a fallback rather than a failure. It takes its own stop predicate,
                // at its own per-element granularity.
                reduce_grobner_basis_until(minimal, order, || {
                    match (wall_clock.as_ref(), options.max_wall_time) {
                        (Some(clock), Some(budget)) => clock.elapsed() >= budget,
                        _ => false,
                    }
                })
            }
            Err(MatrixInterreductionAborted::Stopped(stopped)) => Err(stopped),
        }
    } else if options.count_interreduction {
        reduce_grobner_basis_counted(basis, order, should_stop, &mut report)
    } else if options.measure_stages {
        reduce_grobner_basis_measured(basis, order, should_stop, &mut report)
    } else {
        reduce_grobner_basis_until(basis, order, should_stop)
    };
    statistics.stages.interreduction = interreduction_clock.lap();
    // The stage clock is the authority on the total; the report refines it. They are measured by
    // different instruments over the same code, so they agree to clock granularity rather than
    // exactly, and the invariant asserted in tests is over the report's own two halves.
    statistics.stages.interreduction_minimize = report.minimize;
    statistics.stages.interreduction_reduce = report.reduce;
    // Two instruments over the same code: the stage clock brackets the call, the report times the
    // two halves inside it. The clock therefore reads at least the report's total and not much
    // more, and a split that drifted from the total it refines would be worse than no split.
    debug_assert!(
        !(options.measure_stages || options.count_interreduction)
            || report.total() <= statistics.stages.interreduction,
        "the interreduction split ({:?}) cannot exceed the stage clock ({:?})",
        report.total(),
        statistics.stages.interreduction
    );
    debug_assert!(
        !(options.measure_stages || options.count_interreduction)
            || report.elements == 0
            || (0.0..=1.0).contains(&report.reduce_share()),
        "a share is a fraction"
    );
    statistics.interreduction = report.counts;
    statistics.interreduction_elements = report.elements;
    let reduced = match interreduction {
        Ok(reduced) => reduced,
        Err(stopped) => {
            // The stage time is recorded above before returning, so a stopped run still accounts
            // for where it spent the budget — which is the point of a cooperative stop.
            let elapsed = wall_clock
                .as_ref()
                .map(Instant::elapsed)
                .unwrap_or_default();
            return Err(F4Error::InterreductionTimeBudgetExceeded {
                elements_reduced: stopped.elements_reduced,
                elements: stopped.elements,
                elapsed_millis: elapsed.as_millis().min(u128::from(u64::MAX)) as u64,
                budget_millis: options
                    .max_wall_time
                    .unwrap_or_default()
                    .as_millis()
                    .min(u128::from(u64::MAX)) as u64,
            });
        }
    };

    // The independent check, when asked for. It is not what makes the computation complete — no
    // strategy here discards a pair on heuristic grounds, and the deferred set is drained by the
    // loop's own termination test — but a correctness claim that cannot fail is not a check, and
    // the plan's §8.5 needs its cost reported separately from the work it is checking.
    if options.certify {
        // `certify_f4_output` and not the submitted-basis entry point: this *is* F4's output,
        // run on these generators, so the derivation invariant holds and `is_complete` means what
        // it says. A caller certifying a basis from elsewhere gets the weaker conclusion.
        let report = certify::certify_f4_output(generators, &reduced, order);
        statistics.certification = Some(report);
        if let Some(reason) = report.first_failure() {
            // Deliberately before `statistics.total` is set: a refusal has no total, and the
            // diagnostic entry point still carries everything above.
            return Err(F4Error::CertificationFailed { reason });
        }
    }

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
