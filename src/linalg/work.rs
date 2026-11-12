//! Passive, thread-local research counters; disabled scopes retain no solver state.

use std::cell::RefCell;

use crate::util::Json;

/// Logical entry operations, not CPU instructions or physical memory traffic.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PhaseWork {
    pub pivot_applications: usize,
    pub coefficient_products: usize,
    /// Unique affected target entries consumed by merges; repeated comparison loads are not counted.
    pub sparse_target_entries: usize,
    pub sparse_prefix_preserved: usize,
    pub sparse_merge_output_entries: usize,
    pub sparse_copyback_entries: usize,
    pub dense_load_entries: usize,
    pub dense_scan_cells: usize,
    pub dense_gather_cells: usize,
    pub dense_gather_entries: usize,
    pub normalized_cells: usize,
    pub reducer_target_operations: usize,
    pub pair_target_operations: usize,
    pub rows_loaded: usize,
    pub rows_zero: usize,
}

impl PhaseWork {
    pub fn json(&self) -> Json {
        Json::object([
            ("pivot_applications", Json::size(self.pivot_applications)),
            (
                "coefficient_products",
                Json::size(self.coefficient_products),
            ),
            (
                "sparse_target_entries",
                Json::size(self.sparse_target_entries),
            ),
            (
                "sparse_prefix_preserved",
                Json::size(self.sparse_prefix_preserved),
            ),
            (
                "sparse_merge_output_entries",
                Json::size(self.sparse_merge_output_entries),
            ),
            (
                "sparse_copyback_entries",
                Json::size(self.sparse_copyback_entries),
            ),
            ("dense_load_entries", Json::size(self.dense_load_entries)),
            ("dense_scan_cells", Json::size(self.dense_scan_cells)),
            ("dense_gather_cells", Json::size(self.dense_gather_cells)),
            (
                "dense_gather_entries",
                Json::size(self.dense_gather_entries),
            ),
            ("normalized_cells", Json::size(self.normalized_cells)),
            (
                "reducer_target_operations",
                Json::size(self.reducer_target_operations),
            ),
            (
                "pair_target_operations",
                Json::size(self.pair_target_operations),
            ),
            ("rows_loaded", Json::size(self.rows_loaded)),
            ("rows_zero", Json::size(self.rows_zero)),
        ])
    }
}

/// One matrix's live payload/capacity peaks exclude basis, monomial tables and allocator overhead.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MatrixWork {
    pub degree: u64,
    pub pairs: usize,
    pub rows: usize,
    pub columns: usize,
    pub reducer_rows: usize,
    pub initial_entries: usize,
    pub rank: usize,
    pub zero_rows: usize,
    pub final_entries: usize,
    pub peak_mathematical_entries: usize,
    pub peak_sparse_live_entries: usize,
    pub peak_sparse_capacity_entries: usize,
    pub dense_capacity_bytes: usize,
    pub sparse_entry_bytes: usize,
    pub auxiliary_capacity_bytes: usize,
    pub forward: PhaseWork,
    pub backward: PhaseWork,
}

impl MatrixWork {
    pub fn json(&self) -> Json {
        Json::object([
            ("degree", Json::int(self.degree)),
            ("pairs", Json::size(self.pairs)),
            ("rows", Json::size(self.rows)),
            ("columns", Json::size(self.columns)),
            ("reducer_rows", Json::size(self.reducer_rows)),
            ("initial_entries", Json::size(self.initial_entries)),
            ("rank", Json::size(self.rank)),
            ("zero_rows", Json::size(self.zero_rows)),
            ("final_entries", Json::size(self.final_entries)),
            (
                "peak_mathematical_entries",
                Json::size(self.peak_mathematical_entries),
            ),
            (
                "peak_sparse_live_entries",
                Json::size(self.peak_sparse_live_entries),
            ),
            (
                "peak_sparse_capacity_entries",
                Json::size(self.peak_sparse_capacity_entries),
            ),
            (
                "dense_capacity_bytes",
                Json::size(self.dense_capacity_bytes),
            ),
            ("sparse_entry_bytes", Json::size(self.sparse_entry_bytes)),
            (
                "auxiliary_capacity_bytes",
                Json::size(self.auxiliary_capacity_bytes),
            ),
            ("forward", self.forward.json()),
            ("backward", self.backward.json()),
        ])
    }
}

/// Measurements remain separate from backend-invariant elimination statistics.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct WorkReport {
    pub batches: Vec<MatrixWork>,
    pub outside_batch: MatrixWork,
}

impl WorkReport {
    pub fn json(&self) -> Json {
        Json::object([
            ("schema", Json::int(1)),
            (
                "coverage",
                Json::string(
                    "Sparse and Adaptive elimination; DenseRows arithmetic is not observed",
                ),
            ),
            (
                "batches",
                Json::Array(self.batches.iter().map(MatrixWork::json).collect()),
            ),
            ("outside_batch", self.outside_batch.json()),
        ])
    }
}

#[derive(Default)]
struct State {
    report: WorkReport,
    batch: Option<usize>,
    backward: bool,
    target: Option<usize>,
    structured: bool,
    resident: usize,
    allocated: usize,
}

thread_local! {
    static ACTIVE: RefCell<Option<State>> = const { RefCell::new(None) };
}

/// Observe this thread only; nested scopes are rejected and a panic restores the disabled state.
pub fn measure<T>(f: impl FnOnce() -> T) -> (T, WorkReport) {
    ACTIVE.with(|active| {
        let mut state = active.borrow_mut();
        assert!(state.is_none(), "work measurement scopes cannot nest");
        *state = Some(State::default());
    });
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            ACTIVE.with(|active| *active.borrow_mut() = None);
        }
    }
    let reset = Reset;
    let result = f();
    let report = ACTIVE.with(|active| active.borrow_mut().take().unwrap().report);
    drop(reset);
    (result, report)
}

fn update(f: impl FnOnce(&mut MatrixWork, bool, Option<bool>)) {
    ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let Some(state) = active.as_mut() else {
            return;
        };
        let matrix = match state.batch {
            Some(index) => &mut state.report.batches[index],
            None => &mut state.report.outside_batch,
        };
        let reducer = if state.structured && state.batch.is_some() {
            state.target.map(|index| index < matrix.reducer_rows)
        } else {
            None
        };
        f(matrix, state.backward, reducer);
    });
}

pub(crate) fn begin_batch(matrix: MatrixWork, structured: bool) {
    ACTIVE.with(|active| {
        if let Some(state) = active.borrow_mut().as_mut() {
            assert!(state.batch.is_none());
            state.batch = Some(state.report.batches.len());
            state.report.batches.push(matrix);
            state.structured = structured;
            state.backward = false;
            state.target = None;
        }
    });
}

pub(crate) fn finish_batch(statistics: &super::sparse::EliminationStatistics) {
    update(|matrix, _, _| {
        matrix.rank = statistics.rank;
        matrix.zero_rows = statistics.zero_rows;
        matrix.final_entries = statistics.final_nonzeros;
        matrix.peak_mathematical_entries = statistics.peak_nonzeros;
    });
    ACTIVE.with(|active| {
        if let Some(state) = active.borrow_mut().as_mut() {
            state.batch = None;
            state.backward = false;
            state.target = None;
        }
    });
}

pub(crate) fn enabled() -> bool {
    ACTIVE.with(|active| active.borrow().is_some())
}

pub(crate) fn target(index: usize) {
    ACTIVE.with(|active| {
        if let Some(state) = active.borrow_mut().as_mut() {
            state.target = Some(index);
        }
    });
}

pub(crate) struct Backward(bool);
impl Drop for Backward {
    fn drop(&mut self) {
        ACTIVE.with(|active| {
            if let Some(state) = active.borrow_mut().as_mut() {
                state.backward = self.0;
            }
        });
    }
}

pub(crate) fn backward() -> Backward {
    let previous = ACTIVE.with(|active| {
        active.borrow_mut().as_mut().is_some_and(|state| {
            let previous = state.backward;
            state.backward = true;
            previous
        })
    });
    Backward(previous)
}

pub(crate) fn counters(f: impl FnOnce(&mut PhaseWork)) {
    update(|matrix, backward, _| {
        f(if backward {
            &mut matrix.backward
        } else {
            &mut matrix.forward
        })
    });
}

pub(crate) fn pivot(products: usize) {
    update(|matrix, backward, reducer| {
        let work = if backward {
            &mut matrix.backward
        } else {
            &mut matrix.forward
        };
        work.pivot_applications += 1;
        work.coefficient_products += products;
        if let Some(reducer) = reducer {
            work.reducer_target_operations += usize::from(reducer);
            work.pair_target_operations += usize::from(!reducer);
        }
    });
}

pub(crate) fn memory(
    live: usize,
    capacity: usize,
    dense_bytes: usize,
    auxiliary_bytes: usize,
    entry_bytes: usize,
) {
    update(|matrix, _, _| {
        matrix.peak_sparse_live_entries = matrix.peak_sparse_live_entries.max(live);
        matrix.peak_sparse_capacity_entries = matrix.peak_sparse_capacity_entries.max(capacity);
        matrix.dense_capacity_bytes = matrix.dense_capacity_bytes.max(dense_bytes);
        matrix.auxiliary_capacity_bytes = matrix.auxiliary_capacity_bytes.max(auxiliary_bytes);
        matrix.sparse_entry_bytes = entry_bytes;
    });
}

pub(crate) fn outside_summary(
    statistics: &super::sparse::EliminationStatistics,
    rows: usize,
    columns: usize,
) {
    ACTIVE.with(|active| {
        if let Some(state) = active.borrow_mut().as_mut() {
            if state.batch.is_none() {
                let matrix = &mut state.report.outside_batch;
                matrix.rows = rows;
                matrix.columns = columns;
                matrix.initial_entries = statistics.initial_nonzeros;
                matrix.rank = statistics.rank;
                matrix.zero_rows = statistics.zero_rows;
                matrix.final_entries = statistics.final_nonzeros;
                matrix.peak_mathematical_entries = statistics.peak_nonzeros;
            }
        }
    });
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::Zp13,
        linalg::{
            sparse::{reduced_row_echelon, SparseMatrix, SparseRow},
            work::measure,
        },
        One,
    };

    // A three-row echelon fixture prices two back substitutions and leaves its RREF unchanged.
    #[test]
    fn exact_sparse_work_does_not_change_rref() {
        let rows = vec![
            SparseRow::<Zp13>::new(&[(0, Zp13::ONE), (2, Zp13::ONE)]),
            SparseRow::new(&[(1, Zp13::ONE), (2, Zp13::ONE)]),
            SparseRow::new(&[(2, Zp13::ONE), (3, Zp13::ONE)]),
        ];
        let mut control = SparseMatrix::new(4, rows);
        let mut observed = control.clone();
        let expected = reduced_row_echelon(&mut control);
        let (actual, work) = measure(|| reduced_row_echelon(&mut observed));
        assert_eq!(actual, expected);
        assert_eq!(control, observed);
        assert_eq!(work.outside_batch.backward.pivot_applications, 2);
        assert_eq!(work.outside_batch.backward.coefficient_products, 4);
        assert_eq!(work.outside_batch.backward.sparse_target_entries, 2);
        assert_eq!(work.outside_batch.backward.sparse_prefix_preserved, 2);
        assert_eq!(work.outside_batch.backward.sparse_merge_output_entries, 2);
        assert_eq!(work.outside_batch.peak_sparse_live_entries, 7);
        assert!(work.outside_batch.peak_sparse_capacity_entries >= 7);
    }

    // A duplicate dense-accumulator row performs one two-coefficient subtraction and contributes no rank.
    #[test]
    fn exact_accumulator_work_counts_products_and_scans() {
        use crate::linalg::{row_echelon_with, Backend};
        let original = SparseRow::<Zp13>::new(&[(0, Zp13::ONE), (1, Zp13::ONE)]);
        let mut matrix = SparseMatrix::new(2, vec![original; 2]);
        let (result, work) =
            measure(|| row_echelon_with(Backend::Adaptive, &mut matrix, usize::MAX).unwrap());
        assert_eq!(result.rank, 1);
        assert_eq!(result.zero_rows, 1);
        let phase = work.outside_batch.forward;
        assert_eq!(phase.pivot_applications, 1);
        assert_eq!(phase.coefficient_products, 2);
        assert_eq!(phase.dense_load_entries, 4);
        assert_eq!(phase.dense_scan_cells, 2);
        assert_eq!(phase.dense_gather_cells, 2);
        assert_eq!(phase.dense_gather_entries, 2);
        assert_eq!(phase.rows_loaded, 2);
        assert_eq!(phase.rows_zero, 1);
        assert_eq!(work.outside_batch.dense_capacity_bytes, 16);
        assert_eq!(work.outside_batch.peak_sparse_live_entries, 6);
    }

    // Passive full-F4 observation preserves the basis and reconciles batch pivot applications with existing counters.
    #[test]
    fn f4_observation_preserves_trajectory_and_batch_work() {
        use crate::{
            grobner::{f4_with_options, F4Options},
            MonomialOrder, MultivariatePolynomial,
        };
        let names = ["x", "y", "z"];
        let system: Vec<MultivariatePolynomial<3, Zp13>> = ["x^2 + y", "x*y + z", "z^2 + x"]
            .iter()
            .map(|text| MultivariatePolynomial::parse(text, names).unwrap())
            .collect();
        let order = MonomialOrder::GradedReverseLexicographic;
        let options = F4Options::default();
        let (basis, statistics) = f4_with_options(&system, order, &options).unwrap();
        let ((observed_basis, observed), report) =
            measure(|| f4_with_options(&system, order, &options).unwrap());
        assert_eq!(basis, observed_basis);
        assert_eq!(statistics.row_operations, observed.row_operations);
        assert_eq!(statistics.step_degrees, observed.step_degrees);
        assert_eq!(report.batches.len(), statistics.batches);
        assert_eq!(
            report
                .batches
                .iter()
                .map(|batch| batch.forward.pivot_applications + batch.backward.pivot_applications)
                .sum::<usize>(),
            statistics.row_operations
        );
        for batch in report.batches {
            assert_eq!(
                batch.backward.pivot_applications,
                batch.backward.reducer_target_operations + batch.backward.pair_target_operations
            );
            assert!(batch.peak_sparse_capacity_entries >= batch.initial_entries);
        }
    }

    // An unwinding measurement restores the disabled state and does not contaminate the next scope.
    #[test]
    fn panic_restores_measurement_scope() {
        let result = std::panic::catch_unwind(|| measure(|| panic!("intentional")));
        assert!(result.is_err());
        assert!(!super::enabled());
        let (_, work) = measure(|| ());
        assert_eq!(work, super::WorkReport::default());
    }
}

// Row-local storage is sampled before copyback while both the old target and merge output live.
pub(crate) fn row_context(resident: usize, allocated: usize) {
    ACTIVE.with(|active| {
        if let Some(state) = active.borrow_mut().as_mut() {
            state.resident = resident;
            state.allocated = allocated;
        }
    });
}

pub(crate) fn sparse_storage(live: usize, capacity: usize, entry_bytes: usize) {
    let (resident, allocated) = ACTIVE.with(|active| {
        active
            .borrow()
            .as_ref()
            .map_or((0, 0), |state| (state.resident, state.allocated))
    });
    memory(resident + live, allocated + capacity, 0, 0, entry_bytes);
}
