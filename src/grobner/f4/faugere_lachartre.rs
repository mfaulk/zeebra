//! A structured batch in Faugère–Lachartre order (#816): every pair row swept against the whole
//! reducer block, then `D'` eliminated alone on the columns no reducer leads.
//!
//! `D'` is renumbered onto its own columns before its elimination so that dense scans, and the
//! `Dense` backend's buffer, span only those columns; the rows are mapped back afterwards, so the
//! matrix the caller extracts candidates from is indexed as it was built. Reducer rows are never
//! written.
//!
//! Under [`ParallelForward`] both passes may run on workers through the field's
//! [`concurrent::Dispatch`], each behind the same gate as the forward order's pass. A pass whose
//! workers' reservation does not fit falls back to its serial kernel; the sweep leaves rows the
//! serial sweep finishes identically, and the concurrent echelon leaves `D'` untouched. An echelon
//! refused on the live-entry budget after its workers started instead keeps their finished rows
//! and reduces only the rest serially, falling back from scratch only if that is refused too.

use super::{
    candidate,
    macaulay::MacaulayMatrix,
    options::ParallelForward,
    parallel,
    statistics::{ParallelForwardStatistics, StageClock, StageTimings},
    structured::BlockOutcome,
};
use crate::{
    linalg::{
        concurrent,
        echelon::{row_echelon_with, sweep_rows_against_pivots, Backend},
        sparse::{EliminationStatistics, SparseMatrix, SparseRow},
    },
    FiniteField,
};
use std::sync::atomic::AtomicBool;

/// Which concurrent kernel a pass asks for.
#[derive(Clone, Copy)]
enum Pass {
    Sweep,
    Echelon,
}

/// Rows `[split..]` of `matrix` through `pass` on workers, or `None` for the serial kernel.
///
/// `None` after a refusal is recorded as a fallback; a worker panic propagates, as for the
/// forward order.
#[allow(clippy::too_many_arguments)]
fn on_workers<F: FiniteField>(
    pass: Pass,
    setting: ParallelForward,
    backend: Backend,
    matrix: &mut SparseMatrix<F>,
    split: usize,
    allowance: usize,
    measure: bool,
    record: &mut ParallelForwardStatistics,
) -> Option<concurrent::Report> {
    let lower = &matrix.rows()[split..];
    let lower_nonzeros = lower.iter().map(SparseRow::nonzeros).sum();
    let (dispatch, mut config) =
        parallel::gate::<F>(setting, backend, lower.len(), lower_nonzeros, allowance)?;
    config.measure_work = measure;
    let cancel = AtomicBool::new(false);
    let result = match pass {
        Pass::Sweep => dispatch
            .sweep(matrix, split, &config, &cancel)
            .map(concurrent::Outcome::Reduced),
        Pass::Echelon => dispatch.reduce_retaining(matrix, split, &config, &cancel),
    };
    match result {
        Ok(concurrent::Outcome::Reduced(report)) => {
            record.batches = 1;
            record.max_workers = record.max_workers.max(config.workers);
            record.lost_publications += report.failed_publications;
            record.workspace_bytes = record.workspace_bytes.max(report.workspace_bytes);
            if measure {
                record.record_pass(&report, config.workers);
            }
            Some(report)
        }
        // As for the forward order (#1068): a `D'` pass refused after its workers started keeps
        // their finished rows and reduces the rest serially, unless that continuation is refused
        // too, in which case `D'` is restored and the caller's serial kernel redoes it.
        Ok(concurrent::Outcome::Retained(partial)) => {
            record.fallback_batches = 1;
            let retained = partial.completed.len();
            let report =
                concurrent::continue_serially(matrix, split, partial, backend, allowance).ok()?;
            record.retained_batches = 1;
            record.retained_rows += retained;
            record.max_workers = record.max_workers.max(config.workers);
            record.lost_publications += report.failed_publications;
            record.workspace_bytes = record.workspace_bytes.max(report.workspace_bytes);
            if measure {
                record.record_pass(&report, config.workers);
            }
            Some(report)
        }
        Err(concurrent::Error::Entries { .. } | concurrent::Error::Workspace { .. }) => {
            record.fallback_batches = 1;
            None
        }
        Err(concurrent::Error::WorkerPanicked) => panic!("a Faugère–Lachartre worker panicked"),
        Err(error) => {
            unreachable!("structured batch rejected by concurrent elimination: {error:?}")
        }
    }
}

/// Eliminate a batch in Faugère–Lachartre order.
///
/// `candidate_columns[c]` says whether a pivot in original column `c` is a candidate; under
/// `reduce`, exactly the candidate rows are then cleared of every other pivot column, the contract
/// [`candidate::finish`] keeps for the forward order. The sweep and the echelon of `D'` are charged
/// to `stages.forward`, split as `stages.fl_sweep` and `stages.fl_echelon`, the candidate pass to
/// `stages.backward`. `setting` may put either pass
/// on workers, recorded in `record`.
///
/// # Errors
/// The live entry count, reducer rows included, that crossed `allowance`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn eliminate<const N: usize, F: FiniteField>(
    backend: Backend,
    setting: ParallelForward,
    matrix: &mut MacaulayMatrix<N, F>,
    candidate_columns: &[bool],
    reduce: bool,
    allowance: usize,
    clock: &mut StageClock,
    stages: &mut StageTimings,
    record: &mut ParallelForwardStatistics,
) -> Result<(BlockOutcome, candidate::Report), usize> {
    let split = matrix.partition_reducers_first();
    debug_assert_eq!(
        super::structured::check_reducer_block(matrix.matrix(), split),
        Ok(())
    );
    let measure = clock.measuring();
    let mut statistics = match on_workers(
        Pass::Sweep,
        setting,
        backend,
        matrix.matrix_mut(),
        split,
        allowance,
        measure,
        record,
    ) {
        Some(report) => {
            record.reserved_entries = record.reserved_entries.max(report.peak_reserved_entries);
            report.statistics
        }
        None => sweep_rows_against_pivots(matrix.matrix_mut(), split, allowance)?,
    };
    stages.fl_sweep = clock.lap();

    let columns = matrix.num_columns();
    let mut reducer_led = vec![false; columns];
    let mut upper = 0usize;
    for row in &matrix.matrix().rows()[..split] {
        if let Some(lead) = row.leading_column() {
            reducer_led[lead] = true;
        }
        upper += row.nonzeros();
    }
    let mut compact = vec![usize::MAX; columns];
    let mut original = Vec::new();
    for (column, led) in reducer_led.iter().enumerate() {
        if !led {
            compact[column] = original.len();
            original.push(column);
        }
    }
    // The renumbering is monotone, so sorted rows stay sorted.
    let lower: Vec<SparseRow<F>> = matrix.matrix_mut().rows_mut()[split..]
        .iter_mut()
        .map(|row| {
            let row = std::mem::take(row);
            let entries = row
                .entries()
                .iter()
                .map(|&(column, value)| {
                    debug_assert_ne!(compact[column], usize::MAX, "a reducer column survived");
                    (compact[column], value)
                })
                .collect();
            SparseRow::from_sorted_unchecked(entries)
        })
        .collect();
    let mut residual = SparseMatrix::new(original.len(), lower);

    // `D'` is budgeted with the reducer block still resident beside it.
    let within = allowance.saturating_sub(upper);
    let lift = |live: usize| live.saturating_add(upper);
    let mut inner: EliminationStatistics = match on_workers(
        Pass::Echelon,
        setting,
        backend,
        &mut residual,
        0,
        within,
        measure,
        record,
    ) {
        Some(report) => {
            record.reserved_entries = record
                .reserved_entries
                .max(lift(report.peak_reserved_entries));
            report.statistics
        }
        None => row_echelon_with(backend, &mut residual, within).map_err(lift)?,
    };
    stages.fl_echelon = clock.lap();
    stages.forward = stages.fl_sweep + stages.fl_echelon;

    let mut report = candidate::Report::default();
    let mut back_substituted_rows = None;
    if reduce {
        let selected: Vec<bool> = original
            .iter()
            .map(|&column| candidate_columns[column])
            .collect();
        let has_candidates = residual
            .rows()
            .iter()
            .any(|row| row.leading_column().is_some_and(|c| selected[c]));
        let (visits, finished) = if !has_candidates {
            (0, candidate::Report::default())
        } else if candidate::workspace_bytes::<F>(residual.num_columns())
            .is_some_and(|bytes| bytes <= candidate::WORKSPACE_LIMIT)
        {
            candidate::finish(
                &mut residual,
                &selected,
                within,
                candidate::WORKSPACE_LIMIT,
                &mut inner,
            )
            .map_err(lift)?
        } else {
            candidate::full(&mut residual, within, 0, &mut inner).map_err(lift)?
        };
        back_substituted_rows = Some(visits);
        report = finished;
    }

    for (slot, row) in matrix.matrix_mut().rows_mut()[split..]
        .iter_mut()
        .zip(residual.rows())
    {
        let entries = row
            .entries()
            .iter()
            .map(|&(column, value)| (original[column], value))
            .collect();
        *slot = SparseRow::from_sorted_unchecked(entries);
    }

    statistics.rank += inner.rank;
    statistics.zero_rows = matrix.num_rows() - statistics.rank;
    statistics.row_operations += inner.row_operations;
    statistics.pivot_inversions += inner.pivot_inversions;
    statistics.peak_nonzeros = statistics.peak_nonzeros.max(lift(inner.peak_nonzeros));
    statistics.final_nonzeros = lift(inner.final_nonzeros);
    debug_assert_eq!(statistics.final_nonzeros, matrix.nonzeros());
    Ok((
        BlockOutcome {
            statistics,
            free_pivots: split,
            back_substituted_rows,
        },
        report,
    ))
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::{Bn254Fr, Gf256, Zp13, Zp2, Zp2147483647, Zp32003},
        grobner::{
            benchmark_systems::{cyclic, katsura},
            f4::{f4_reported, BatchOrder, F4Error, F4Options, ParallelForward},
        },
        linalg::Backend,
        FiniteField, MonomialOrder, MultivariatePolynomial,
    };

    fn agree<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
        options: &F4Options,
    ) {
        let forward = F4Options {
            batch_order: BatchOrder::Forward,
            ..options.clone()
        };
        let fl = F4Options {
            batch_order: BatchOrder::FaugereLachartre,
            ..options.clone()
        };
        let (expected, _) = f4_reported(system, order, &forward);
        let (actual, _) = f4_reported(system, order, &fl);
        assert_eq!(actual.unwrap(), expected.unwrap(), "{order:?} {options:?}");
    }

    // Whole F4 runs in either batch order reach the same reduced basis, over every field width,
    // order, backend, row form and forward-worker setting.
    #[test]
    fn both_orders_reach_the_same_basis() {
        fn check<F: FiniteField>() {
            for order in [
                MonomialOrder::GradedReverseLexicographic,
                MonomialOrder::Lexicographic,
            ] {
                for elimination in [Backend::Sparse, Backend::Dense, Backend::Adaptive] {
                    for reduce_batch_rows in [true, false] {
                        let options = F4Options {
                            elimination,
                            reduce_batch_rows,
                            ..F4Options::default()
                        };
                        agree(&katsura::<5, F>(), order, &options);
                        agree(&cyclic::<5, F>(), order, &options);
                    }
                }
            }
        }
        check::<Zp13>();
        check::<Zp2>();
        check::<Zp32003>();
        check::<Zp2147483647>();
        check::<Bn254Fr>();
        check::<Gf256>();
    }

    // A larger computation, whose batches have many reducer and pair rows.
    #[test]
    fn both_orders_reach_the_same_katsura_7() {
        agree(
            &katsura::<7, Zp32003>(),
            MonomialOrder::GradedReverseLexicographic,
            &F4Options::default(),
        );
    }

    // Forced workers run the sweep and `D'` on threads and reach serial forward's basis at every
    // thread count, over every field width that offers a concurrent handle.
    #[test]
    fn parallel_fl_reproduces_the_serial_basis() {
        fn check<F: FiniteField>() {
            for order in [
                MonomialOrder::GradedReverseLexicographic,
                MonomialOrder::Lexicographic,
            ] {
                let serial = F4Options {
                    parallel_forward: ParallelForward::Serial,
                    ..F4Options::default()
                };
                for workers in [1, 2, 4, 16] {
                    let options = F4Options {
                        parallel_forward: ParallelForward::Forced { workers },
                        ..F4Options::default()
                    };
                    for system in [katsura::<5, F>(), cyclic::<5, F>()] {
                        let fl = F4Options {
                            batch_order: BatchOrder::FaugereLachartre,
                            ..options.clone()
                        };
                        let (expected, _) = f4_reported(&system, order, &serial);
                        let (actual, statistics) = f4_reported(&system, order, &fl);
                        assert_eq!(actual.unwrap(), expected.unwrap(), "{order:?} {workers}");
                        let parallel = statistics.parallel_forward;
                        assert!(
                            parallel.batches > 0,
                            "{order:?} {workers}: nothing dispatched"
                        );
                        assert!(parallel.max_workers <= workers);
                        assert_eq!(parallel.fallback_batches, 0);
                    }
                }
            }
        }
        check::<Zp13>();
        check::<Zp32003>();
        check::<Zp2147483647>();
        check::<Bn254Fr>();
        check::<Gf256>();
    }

    // Sixteen forced workers on a batch large enough for them to race for `D'` pivots.
    #[test]
    fn parallel_fl_reproduces_katsura_7() {
        let system = katsura::<7, Zp32003>();
        let order = MonomialOrder::GradedReverseLexicographic;
        let (expected, _) = f4_reported(&system, order, &F4Options::default());
        for parallel_forward in [
            ParallelForward::Forced { workers: 16 },
            ParallelForward::Auto { max_workers: 16 },
        ] {
            let options = F4Options {
                batch_order: BatchOrder::FaugereLachartre,
                parallel_forward,
                ..F4Options::default()
            };
            let (actual, statistics) = f4_reported(&system, order, &options);
            assert_eq!(actual.unwrap(), *expected.as_ref().unwrap());
            if matches!(parallel_forward, ParallelForward::Forced { .. }) {
                assert!(statistics.parallel_forward.batches > 0);
                assert!(statistics.parallel_forward.reserved_entries > 0);
            }
        }
    }

    // Measured FL batches split `forward` exactly into the reducer sweep and the `D'` echelon
    // (#918), serially and on workers; the forward order leaves both refinements zero.
    #[test]
    fn the_fl_forward_clock_splits_into_sweep_and_echelon() {
        use std::time::Duration;
        let system = katsura::<6, Zp32003>();
        let order = MonomialOrder::GradedReverseLexicographic;
        for parallel_forward in [
            ParallelForward::Serial,
            ParallelForward::Forced { workers: 4 },
        ] {
            let at = |batch_order| F4Options {
                batch_order,
                parallel_forward,
                measure_stages: true,
                ..F4Options::default()
            };
            let (_, fl) = f4_reported(&system, order, &at(BatchOrder::FaugereLachartre));
            let stages = fl.stages;
            assert!(stages.fl_sweep > Duration::ZERO && stages.fl_echelon > Duration::ZERO);
            assert_eq!(stages.fl_sweep + stages.fl_echelon, stages.forward);
            let (_, forward) = f4_reported(&system, order, &at(BatchOrder::Forward));
            assert!(forward.stages.forward > Duration::ZERO);
            assert_eq!(
                forward.stages.fl_sweep + forward.stages.fl_echelon,
                Duration::ZERO
            );
        }
    }

    // A field with no concurrent handle runs the FL order serially under any setting.
    #[test]
    fn parallel_fl_without_a_handle_stays_serial() {
        use crate::fields::Gf13Pow4;
        let options = F4Options {
            batch_order: BatchOrder::FaugereLachartre,
            parallel_forward: ParallelForward::Forced { workers: 4 },
            ..F4Options::default()
        };
        let system = katsura::<4, Gf13Pow4>();
        let order = MonomialOrder::GradedReverseLexicographic;
        let (expected, _) = f4_reported(&system, order, &F4Options::default());
        let (actual, statistics) = f4_reported(&system, order, &options);
        assert_eq!(actual.unwrap(), expected.unwrap());
        assert_eq!(statistics.parallel_forward.batches, 0);
    }

    // A budget the serial FL route fits but the workers' reservation does not falls back, not refuses.
    #[test]
    fn parallel_fl_falls_back_under_a_tight_budget() {
        let system = katsura::<6, Zp32003>();
        let order = MonomialOrder::GradedReverseLexicographic;
        let at = |parallel_forward, entries: usize| F4Options {
            batch_order: BatchOrder::FaugereLachartre,
            parallel_forward,
            ..F4Options::default().with_live_entries::<Zp32003>(entries)
        };
        let (_, serial) = f4_reported(
            &system,
            order,
            &at(ParallelForward::Serial, usize::MAX / 64),
        );
        let peak = serial.max_live_nonzeros;
        let (basis, statistics) = f4_reported(
            &system,
            order,
            &at(ParallelForward::Forced { workers: 16 }, peak),
        );
        let (expected, _) = f4_reported(&system, order, &F4Options::default());
        assert_eq!(basis.unwrap(), expected.unwrap());
        assert!(statistics.parallel_forward.fallback_batches > 0);
    }

    /// Run `system` in FL order on `workers` forced workers at budgets from half its unbounded
    /// peak up to it, asserting the default basis wherever the budget is admitted, and return how
    /// many admitted runs carried retained `D'` rows into the serial kernel.
    fn retaining_budgets<const N: usize>(
        system: &[MultivariatePolynomial<N, Zp32003>],
        workers: usize,
    ) -> usize {
        let order = MonomialOrder::GradedReverseLexicographic;
        let forced = |entries: usize| F4Options {
            batch_order: BatchOrder::FaugereLachartre,
            parallel_forward: ParallelForward::Forced { workers },
            ..F4Options::default().with_live_entries::<Zp32003>(entries)
        };
        let expected = f4_reported(system, order, &F4Options::default()).0.unwrap();
        let (_, unbounded) = f4_reported(system, order, &forced(usize::MAX / 64));
        let top = unbounded
            .max_live_nonzeros
            .max(unbounded.parallel_forward.reserved_entries);
        let mut retained = 0;
        for budget in (top / 2..=top).step_by((top / 400).max(1)) {
            let (basis, statistics) = f4_reported(system, order, &forced(budget));
            let parallel = statistics.parallel_forward;
            assert!(
                parallel.retained_batches <= parallel.fallback_batches,
                "{workers} workers at {budget}: {parallel:?}"
            );
            // A budget below what the serial route needs is refused outright.
            let Ok(basis) = basis else { continue };
            assert_eq!(basis, expected, "{workers} workers at {budget}");
            retained += usize::from(parallel.retained_rows > 0);
        }
        retained
    }

    // A `D'` pass the budget refuses partway keeps the rows its workers finished and still returns
    // the serial basis (#1086). Where a refusal lands after a row has finished depends on how the
    // workers' ledger charges them (#1085): one worker on Katsura-6 is only ever refused before its
    // first row once replaced inputs are released. So the budgets are scanned rather than fixed,
    // over a one-worker run, whose refusals are deterministic, and four-worker runs, which reach
    // many more; the test asserts the same basis at every admitted budget and that some budget
    // retained rows.
    #[test]
    fn a_refused_d_prime_pass_keeps_its_finished_rows() {
        let retained = retaining_budgets(&cyclic::<6, Zp32003>(), 1)
            + retaining_budgets(&cyclic::<6, Zp32003>(), 4)
            + retaining_budgets(&katsura::<6, Zp32003>(), 4);
        assert!(
            retained > 0,
            "no budget refused a D' pass after it finished a row"
        );
    }

    // The route's reported peak is its budget boundary: admitted at the peak, refused one below.
    #[test]
    fn the_reported_peak_is_the_budget_boundary() {
        let system = katsura::<6, Zp32003>();
        let order = MonomialOrder::GradedReverseLexicographic;
        let at = |entries: usize| F4Options {
            batch_order: BatchOrder::FaugereLachartre,
            parallel_forward: crate::grobner::f4::ParallelForward::Serial,
            ..F4Options::default().with_live_entries::<Zp32003>(entries)
        };
        let (basis, statistics) = f4_reported(&system, order, &at(usize::MAX / 64));
        basis.unwrap();
        let peak = statistics.max_live_nonzeros;
        assert!(peak > 0);
        let (admitted, _) = f4_reported(&system, order, &at(peak));
        admitted.unwrap();
        let (refused, _) = f4_reported(&system, order, &at(peak - 1));
        assert!(
            matches!(refused, Err(F4Error::TooManyNonzeros { .. })),
            "{refused:?}"
        );
    }
}
