//! Passive, thread-local research counters; disabled scopes retain no solver state.

use std::cell::RefCell;
use std::time::Instant;

use crate::util::Json;

/// Serial row timings and dependencies describe the control trajectory, not a parallel schedule.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DiscoveryRow {
    pub row: usize,
    pub completed: bool,
    pub elapsed_ns: u64,
    pub first_claim_column: Option<usize>,
    pub pivot_column: Option<usize>,
    pub inherited_products: usize,
    pub discovered_products: usize,
    pub dependencies: Vec<usize>,
}

impl DiscoveryRow {
    fn json(&self) -> Json {
        let column = |value: Option<usize>| value.map_or(Json::Null, Json::size);
        Json::object([
            ("row", Json::size(self.row)),
            ("completed", Json::Bool(self.completed)),
            ("elapsed_ns", Json::int(self.elapsed_ns)),
            ("first_claim_column", column(self.first_claim_column)),
            ("pivot_column", column(self.pivot_column)),
            ("inherited_products", Json::size(self.inherited_products)),
            ("discovered_products", Json::size(self.discovered_products)),
            (
                "dependencies",
                Json::Array(self.dependencies.iter().copied().map(Json::size).collect()),
            ),
        ])
    }
}

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
    pub discovery: Vec<DiscoveryRow>,
    /// False for an interrupted/refused matrix; zero summary counts then mean unavailable.
    pub completed: bool,
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
            (
                "discovery",
                Json::Array(self.discovery.iter().map(DiscoveryRow::json).collect()),
            ),
            ("completed", Json::Bool(self.completed)),
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
    discovery: bool,
    discovery_row: Option<DiscoveryRow>,
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

/// Add per-row clocks and dependency observations to the normal serial work scope.
pub fn measure_discovery<T>(f: impl FnOnce() -> T) -> (T, WorkReport) {
    measure(|| {
        ACTIVE.with(|active| active.borrow_mut().as_mut().unwrap().discovery = true);
        f()
    })
}

pub(crate) struct DiscoveryScope(Option<Instant>);

impl Drop for DiscoveryScope {
    fn drop(&mut self) {
        if let Some(started) = self.0 {
            let row = ACTIVE.with(|active| {
                active
                    .borrow_mut()
                    .as_mut()
                    .and_then(|state| state.discovery_row.take())
            });
            if let Some(mut row) = row {
                row.elapsed_ns = started.elapsed().as_nanos().min(u64::MAX as u128) as u64;
                update(|matrix, _, _| matrix.discovery.push(row));
            }
        }
    }
}

pub(crate) fn discovery_row(row: usize) -> DiscoveryScope {
    DiscoveryScope(ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let state = active.as_mut()?;
        if !state.discovery {
            return None;
        }
        assert!(state.discovery_row.is_none());
        state.discovery_row = Some(DiscoveryRow {
            row,
            ..Default::default()
        });
        Some(Instant::now())
    }))
}

pub(crate) fn discovery_pivot(column: usize, pivot: Option<usize>, first: usize, products: usize) {
    ACTIVE.with(|active| {
        if let Some(row) = active
            .borrow_mut()
            .as_mut()
            .and_then(|state| state.discovery_row.as_mut())
        {
            match pivot {
                Some(index) if index < first => row.inherited_products += products,
                other => {
                    row.first_claim_column.get_or_insert(column);
                    if let Some(index) = other {
                        row.discovered_products += products;
                        row.dependencies.push(index);
                    }
                }
            }
        }
    });
}

pub(crate) fn discovery_finish(column: Option<usize>) {
    ACTIVE.with(|active| {
        if let Some(row) = active
            .borrow_mut()
            .as_mut()
            .and_then(|state| state.discovery_row.as_mut())
        {
            row.completed = true;
            row.pivot_column = column;
        }
    });
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

pub(crate) struct BatchScope(Option<usize>);

impl Drop for BatchScope {
    fn drop(&mut self) {
        ACTIVE.with(|active| {
            if let Some(state) = active.borrow_mut().as_mut() {
                if self.0.is_some() && state.batch == self.0 {
                    state.batch = None;
                    state.backward = false;
                    state.target = None;
                }
            }
        });
    }
}

pub(crate) fn begin_batch(matrix: MatrixWork, structured: bool) -> BatchScope {
    let index = ACTIVE.with(|active| {
        if let Some(state) = active.borrow_mut().as_mut() {
            assert!(state.batch.is_none());
            state.batch = Some(state.report.batches.len());
            state.report.batches.push(matrix);
            state.structured = structured;
            state.backward = false;
            state.target = None;
            state.batch
        } else {
            None
        }
    });
    BatchScope(index)
}

pub(crate) fn finish_batch(statistics: &super::sparse::EliminationStatistics) {
    update(|matrix, _, _| {
        matrix.completed = true;
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
                matrix.completed = true;
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

    // Discovery tracing separates inherited work, new-pivot dependencies and zero residuals without changing rows.
    #[test]
    fn discovery_records_row_dependencies() {
        use crate::linalg::{reduce_rows_against_pivots_with, Backend};
        let rows = vec![
            SparseRow::<Zp13>::new(&[(0, Zp13::ONE), (3, Zp13::ONE)]),
            SparseRow::new(&[(1, Zp13::ONE), (2, Zp13::ONE)]),
            SparseRow::new(&[(0, Zp13::ONE), (1, Zp13::ONE)]),
            SparseRow::new(&[(1, Zp13::ONE), (2, Zp13::ONE)]),
        ];
        let mut control = SparseMatrix::new(4, rows);
        let mut observed = control.clone();
        let expected =
            reduce_rows_against_pivots_with(Backend::Adaptive, &mut control, 1, usize::MAX)
                .unwrap();
        let (actual, report) = super::measure_discovery(|| {
            reduce_rows_against_pivots_with(Backend::Adaptive, &mut observed, 1, usize::MAX)
                .unwrap()
        });
        assert_eq!(actual, expected);
        assert_eq!(observed, control);
        let rows = report.outside_batch.discovery;
        assert_eq!(rows.len(), 3);
        assert!(rows.iter().all(|row| row.completed));
        assert_eq!(rows[0].pivot_column, Some(1));
        assert_eq!(rows[1].inherited_products, 2);
        assert_eq!(rows[1].discovered_products, 2);
        assert_eq!(rows[1].dependencies, vec![1]);
        assert_eq!(rows[1].pivot_column, Some(2));
        assert_eq!(rows[2].dependencies, vec![1]);
        assert_eq!(rows[2].pivot_column, None);
        assert_eq!(rows[2].first_claim_column, Some(1));
    }

    // Discovery refusal records an incomplete row and unwinding leaves the next scope clean.
    #[test]
    fn discovery_refusal_and_panic_cleanup() {
        use crate::linalg::{reduce_rows_against_pivots_with, Backend};
        let mut matrix = SparseMatrix::new(
            4,
            vec![
                SparseRow::<Zp13>::new(&[(0, Zp13::ONE), (1, Zp13::ONE), (2, Zp13::ONE)]),
                SparseRow::new(&[(0, Zp13::ONE), (3, Zp13::ONE)]),
            ],
        );
        let (result, report) = super::measure_discovery(|| {
            reduce_rows_against_pivots_with(Backend::Adaptive, &mut matrix, 1, 5)
        });
        assert!(result.is_err());
        assert_eq!(report.outside_batch.discovery.len(), 1);
        assert!(!report.outside_batch.discovery[0].completed);
        assert!(
            std::panic::catch_unwind(|| super::measure_discovery(|| panic!("intentional")))
                .is_err()
        );
        assert_eq!(measure(|| ()).1, super::WorkReport::default());
    }

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

    // An elimination-budget refusal does not leave a failed batch active during a later solve in the same scope.
    #[test]
    fn refused_batch_does_not_contaminate_later_solve() {
        use crate::{
            grobner::{f4_with_options, F4Options},
            MonomialOrder, MultivariatePolynomial,
        };
        let names = ["x", "y", "z"];
        let system: Vec<MultivariatePolynomial<3, Zp13>> = ["x^2+y^2", "x^2+x*z+y*z+z^2"]
            .iter()
            .map(|text| MultivariatePolynomial::parse(text, names).unwrap())
            .collect();
        let order = MonomialOrder::GradedReverseLexicographic;
        let bounded = F4Options {
            max_live_nonzeros: 6,
            ..F4Options::default()
        };
        let expected = f4_with_options(&system, order, &F4Options::default())
            .unwrap()
            .0;
        let (basis, report) = measure(|| {
            assert!(f4_with_options(&system, order, &bounded).is_err());
            f4_with_options(&system, order, &F4Options::default())
                .unwrap()
                .0
        });
        assert_eq!(basis, expected);
        assert_eq!(report.batches.len(), 2);
        assert!(!report.batches[0].completed);
        assert!(report.batches[1].completed);
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
