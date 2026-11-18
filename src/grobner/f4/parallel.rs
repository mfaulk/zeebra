//! A batch's forward elimination on worker threads, when the gate and the field allow it (#752).

use super::{
    macaulay::MacaulayMatrix,
    options::ParallelForward,
    statistics::ParallelForwardStatistics,
    structured::{BlockOutcome, BlockPlan},
    symbolic::RowKind,
};
use crate::{
    linalg::{
        concurrent,
        sparse::{EliminationStatistics, SparseMatrix},
        Backend,
    },
    FiniteField,
};
use std::sync::atomic::AtomicBool;

/// Dense rows and publication slots across all workers; past it the batch stays serial.
const WORKSPACE_LIMIT: usize = 64 * 1024 * 1024;

/// The reducer-block forward pass on workers, or `None` for the caller's serial kernel.
///
/// `None` leaves the matrix's rows untouched, though possibly partitioned reducers-first, which
/// the serial plan does itself. A worker panic propagates; the serial kernel would have met the
/// same arithmetic.
pub(crate) fn forward<const N: usize, F: FiniteField>(
    setting: ParallelForward,
    plan: BlockPlan,
    backend: Backend,
    matrix: &mut MacaulayMatrix<N, F>,
    allowance: usize,
    statistics: &mut ParallelForwardStatistics,
) -> Option<BlockOutcome> {
    if setting == ParallelForward::Serial
        || plan != BlockPlan::ReducersFirstBlock
        || backend != Backend::Adaptive
    {
        return None;
    }
    // Read the gate's inputs off the row kinds, so a batch the gate leaves serial pays one pass
    // over the rows and no permutation.
    let (lower_rows, lower_nonzeros) = matrix
        .row_origins()
        .iter()
        .zip(matrix.matrix().rows())
        .filter(|(origin, _)| origin.kind != RowKind::Reducer)
        .fold((0, 0), |(rows, nonzeros), (_, row)| {
            (rows + 1, nonzeros + row.nonzeros())
        });
    let (dispatch, config) = gate::<F>(setting, backend, lower_rows, lower_nonzeros, allowance)?;
    let workers = config.workers;
    let split = matrix.partition_reducers_first();
    debug_assert_eq!(
        super::structured::check_reducer_block(matrix.matrix(), split),
        Ok(())
    );
    match dispatch.reduce(matrix.matrix_mut(), split, &config, &AtomicBool::new(false)) {
        Ok(report) => {
            *statistics = ParallelForwardStatistics {
                batches: 1,
                fallback_batches: 0,
                max_workers: workers,
                lost_publications: report.failed_publications,
                reserved_entries: report.peak_reserved_entries,
                workspace_bytes: report.workspace_bytes,
            };
            Some(BlockOutcome {
                statistics: report.statistics,
                free_pivots: split,
                back_substituted_rows: None,
            })
        }
        Err(concurrent::Error::Entries { .. } | concurrent::Error::Workspace { .. }) => {
            statistics.fallback_batches = 1;
            None
        }
        Err(concurrent::Error::WorkerPanicked) => panic!("a forward-elimination worker panicked"),
        Err(error) => {
            unreachable!("structured batch rejected by concurrent elimination: {error:?}")
        }
    }
}

/// A batch's candidate finishing on worker threads (#845): the visits, the report and the worker
/// count, or `None`, with the matrix untouched, for the caller's serial kernel.
///
/// Gated like the forward pass, with the selected targets as the rows and their entries as the
/// work.
pub(crate) fn finish<F: FiniteField>(
    setting: ParallelForward,
    backend: Backend,
    matrix: &mut SparseMatrix<F>,
    selected: &[bool],
    allowance: usize,
    statistics: &mut EliminationStatistics,
) -> Option<(usize, super::candidate::Report, usize)> {
    let (targets, entries) = matrix
        .rows()
        .iter()
        .filter(|row| row.leading_column().is_some_and(|column| selected[column]))
        .fold((0, 0), |(rows, entries), row| {
            (rows + 1, entries + row.nonzeros())
        });
    let (_, config) = gate::<F>(setting, backend, targets, entries, allowance)?;
    let (visits, report) = super::candidate::finish_parallel(
        matrix,
        selected,
        allowance,
        super::candidate::WORKSPACE_LIMIT,
        config.workers,
        statistics,
    )?;
    Some((visits, report, config.workers))
}

/// The handle and configuration for a block of `lower_rows` rows and `lower_nonzeros` entries to
/// go to workers, or `None` when the setting, the backend, the field or the gate keeps it serial.
///
/// Shared by the forward order and both passes of the Faugère–Lachartre order, so all three
/// answer to one gate. `Forced { workers: 1 }` still takes the concurrent kernel: the one-thread
/// control that separates algorithm from threading.
pub(crate) fn gate<F: FiniteField>(
    setting: ParallelForward,
    backend: Backend,
    lower_rows: usize,
    lower_nonzeros: usize,
    allowance: usize,
) -> Option<(concurrent::Dispatch<F>, concurrent::Config)> {
    if setting == ParallelForward::Serial || backend != Backend::Adaptive {
        return None;
    }
    let dispatch = F::concurrent_elimination()?;
    let workers = setting.workers(lower_rows, lower_nonzeros);
    if workers <= 1 && !matches!(setting, ParallelForward::Forced { .. }) {
        return None;
    }
    Some((
        dispatch,
        concurrent::Config {
            workers,
            schedule: concurrent::Schedule::Dynamic,
            max_entries: allowance,
            max_workspace_bytes: WORKSPACE_LIMIT,
            measure_work: false,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        fields::{Bn254Fr, Gf13Pow4, Gf256, Zp13, Zp18446744073709551263, Zp2147483647, Zp32003},
        grobner::{
            benchmark_systems::{cyclic, katsura},
            f4::{f4_reported, F4Error, F4Options},
        },
        MonomialOrder, MultivariatePolynomial,
    };

    fn serial() -> F4Options {
        F4Options {
            parallel_forward: ParallelForward::Serial,
            ..F4Options::default()
        }
    }

    fn forced(workers: usize) -> F4Options {
        F4Options {
            parallel_forward: ParallelForward::Forced { workers },
            ..F4Options::default()
        }
    }

    fn agree<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
        options: &F4Options,
    ) -> ParallelForwardStatistics {
        let (expected, _) = f4_reported(system, order, &serial());
        let (parallel, statistics) = f4_reported(system, order, options);
        assert_eq!(parallel.unwrap(), expected.unwrap());
        statistics.parallel_forward
    }

    // Forced workers give the serial reduced basis over every field width and every plain order.
    #[test]
    fn forced_workers_reproduce_the_serial_basis() {
        fn check<F: FiniteField>() {
            for order in [
                MonomialOrder::GradedReverseLexicographic,
                MonomialOrder::Lexicographic,
                MonomialOrder::GradedLexicographic,
            ] {
                for workers in [1, 2, 3, 8] {
                    let k = agree(&katsura::<5, F>(), order, &forced(workers));
                    let c = agree(&cyclic::<5, F>(), order, &forced(workers));
                    assert!(
                        k.batches > 0 && c.batches > 0,
                        "{order:?} dispatched nothing"
                    );
                    assert!(k.max_workers <= workers && c.max_workers <= workers);
                }
            }
        }
        check::<Zp13>();
        check::<Zp32003>();
        check::<Zp2147483647>();
        check::<Zp18446744073709551263>();
        check::<Bn254Fr>();
        check::<Gf256>();
    }

    // Forced workers finish candidates on threads and still return the serial reduced basis.
    #[test]
    fn forced_workers_finish_candidates_to_the_serial_basis() {
        fn check<F: FiniteField>() {
            same(&katsura::<6, F>());
            same(&cyclic::<5, F>());
        }
        fn same<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>]) {
            let order = MonomialOrder::GradedReverseLexicographic;
            let (expected, serial_statistics) = f4_reported(system, order, &serial());
            let expected = expected.unwrap();
            assert_eq!(serial_statistics.candidate_reduction.parallel_batches, 0);
            for workers in [1, 2, 4, 16] {
                let (basis, statistics) = f4_reported(system, order, &forced(workers));
                assert_eq!(basis.unwrap(), expected);
                // Forced forward elimination changes the echelon rows finishing starts from, so
                // its counters are compared at the kernel (`candidate`'s tests), not here.
                let finish = statistics.candidate_reduction;
                assert!(
                    finish.parallel_batches > 0,
                    "{workers} workers: none parallel"
                );
                assert!(finish.max_workers <= workers);
                assert_eq!(finish.fallback_batches, 0);
            }
        }
        check::<Zp32003>();
        check::<Zp18446744073709551263>();
        check::<Gf256>();
    }

    // Forced dispatch on a larger computation, where workers genuinely race for pivots.
    #[test]
    fn forced_workers_reproduce_katsura_7() {
        let statistics = agree(
            &katsura::<7, Zp32003>(),
            MonomialOrder::GradedReverseLexicographic,
            &forced(16),
        );
        assert!(statistics.batches > 0);
        assert_eq!(statistics.fallback_batches, 0);
        assert!(statistics.reserved_entries > 0 && statistics.workspace_bytes > 0);
    }

    // A field that provides no concurrent handle is computed serially under any setting.
    #[test]
    fn a_field_without_a_handle_stays_serial() {
        assert!(Gf13Pow4::concurrent_elimination().is_none());
        let statistics = agree(
            &katsura::<4, Gf13Pow4>(),
            MonomialOrder::GradedReverseLexicographic,
            &forced(4),
        );
        assert_eq!(statistics, ParallelForwardStatistics::default());
    }

    // Serial, a non-adaptive backend and the unstructured plan never dispatch.
    #[test]
    fn ineligible_settings_stay_serial() {
        let system = katsura::<5, Zp32003>();
        let order = MonomialOrder::GradedReverseLexicographic;
        for options in [
            serial(),
            F4Options {
                elimination: Backend::Sparse,
                ..forced(4)
            },
            F4Options {
                reduction: crate::grobner::f4::ReductionStrategy::Unstructured,
                ..forced(4)
            },
        ] {
            assert_eq!(
                agree(&system, order, &options),
                ParallelForwardStatistics::default()
            );
        }
    }

    // The automatic gate leaves small batches serial, so small controls pay no dispatch.
    #[test]
    fn auto_leaves_small_computations_serial() {
        let options = F4Options {
            parallel_forward: ParallelForward::Auto { max_workers: 64 },
            ..F4Options::default()
        };
        let statistics = agree(
            &cyclic::<5, Zp32003>(),
            MonomialOrder::GradedReverseLexicographic,
            &options,
        );
        assert_eq!(statistics.batches, 0);
    }

    // A budget the serial kernel fits but the workers' reservation does not falls back, not refuses.
    #[test]
    fn a_tight_budget_falls_back_to_serial_admission() {
        let system = katsura::<6, Zp32003>();
        let order = MonomialOrder::GradedReverseLexicographic;
        let (_, baseline) = f4_reported(&system, order, &serial());
        let peak = baseline.max_live_nonzeros;
        let tight = |entries| forced(16).with_live_entries::<Zp32003>(entries);
        let statistics = agree(&system, order, &tight(peak));
        assert!(statistics.fallback_batches > 0, "{statistics:?}");
        // Below the serial peak both routes refuse with the same error.
        let (refused, _) = f4_reported(&system, order, &tight(peak - 1));
        let (expected, _) = f4_reported(
            &system,
            order,
            &serial().with_live_entries::<Zp32003>(peak - 1),
        );
        assert!(matches!(refused, Err(F4Error::TooManyNonzeros { .. })));
        assert_eq!(refused.unwrap_err(), expected.unwrap_err());
    }

    // A batch the gate leaves serial is returned unpermuted, so declining costs no row movement.
    #[test]
    fn a_declined_batch_is_left_in_place() {
        struct Capture(Vec<MacaulayMatrix<5, Zp32003>>);
        impl crate::grobner::f4::BatchObserver<5, Zp32003> for Capture {
            fn batch(
                &mut self,
                _: &crate::grobner::f4::MonicBasis<5, Zp32003>,
                _: &[crate::grobner::CriticalPair<5>],
            ) {
            }
            fn matrix(&mut self, matrix: &MacaulayMatrix<5, Zp32003>) {
                self.0.push(matrix.clone());
            }
        }
        let mut capture = Capture(Vec::new());
        crate::grobner::f4::f4_observed(
            &cyclic::<5, Zp32003>(),
            MonomialOrder::GradedReverseLexicographic,
            &F4Options::default(),
            &mut capture,
        )
        .unwrap();
        // At least one batch must be one that partitioning would reorder, or this proves nothing.
        assert!(capture.0.iter().any(|matrix| {
            let mut partitioned = matrix.clone();
            partitioned.partition_reducers_first();
            partitioned.row_origins() != matrix.row_origins()
        }));
        for mut matrix in capture.0 {
            let before = matrix.clone();
            let mut statistics = ParallelForwardStatistics::default();
            let outcome = forward(
                ParallelForward::Auto { max_workers: 16 },
                BlockPlan::ReducersFirstBlock,
                Backend::Adaptive,
                &mut matrix,
                usize::MAX,
                &mut statistics,
            );
            assert!(outcome.is_none());
            assert_eq!(matrix.row_origins(), before.row_origins());
            assert_eq!(matrix.matrix(), before.matrix());
            assert_eq!(statistics, ParallelForwardStatistics::default());
        }
    }

    // Worker counts follow the setting and never exceed the lower rows to reduce.
    #[test]
    fn worker_counts_respect_the_setting() {
        assert_eq!(ParallelForward::Serial.workers(1000, 10_000_000), 1);
        assert_eq!(ParallelForward::Forced { workers: 8 }.workers(3, 0), 3);
        assert_eq!(ParallelForward::Forced { workers: 0 }.workers(3, 0), 1);
        let auto = ParallelForward::Auto { max_workers: 4 };
        assert_eq!(
            auto.workers(10_000, ParallelForward::MIN_LOWER_NONZEROS - 1),
            1
        );
        assert_eq!(auto.workers(10_000, usize::MAX / 2), 4);
        assert!(ParallelForward::Auto { max_workers: 0 }.workers(10_000, usize::MAX / 2) >= 1);
    }

    /// `max_workers` is the largest count any batch shape can get, and never zero.
    #[test]
    fn max_workers_bounds_every_batch() {
        assert_eq!(ParallelForward::Serial.max_workers(), 1);
        assert_eq!(ParallelForward::Forced { workers: 8 }.max_workers(), 8);
        assert_eq!(ParallelForward::Forced { workers: 0 }.max_workers(), 1);
        assert_eq!(ParallelForward::Auto { max_workers: 4 }.max_workers(), 4);
        assert!(ParallelForward::Auto { max_workers: 0 }.max_workers() >= 1);
    }
}
