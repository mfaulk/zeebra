use crate::{
    fields::ConcurrentJob,
    linalg::{
        sparse::{EliminationStatistics, SparseMatrix, SparseRow},
        DenseAccumulator,
    },
    FiniteField,
};
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Debug, Default, PartialEq, Eq)]
pub struct Report {
    pub targets: usize,
    pub products: usize,
    pub workspace_bytes: usize,
    pub reserved_entries: usize,
    pub peak_capacity_entries: usize,
    pub fell_back: bool,
}

pub const WORKSPACE_LIMIT: usize = 64 * 1024 * 1024;

pub(crate) fn workspace_bytes<F>(columns: usize) -> Option<usize> {
    columns.checked_mul(
        std::mem::size_of::<F>() + std::mem::size_of::<usize>() + std::mem::size_of::<bool>(),
    )
}

pub(crate) fn full<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    max_entries: usize,
    mask_bytes: usize,
    statistics: &mut EliminationStatistics,
) -> Result<(usize, Report), usize> {
    #[cfg(feature = "research-work")]
    crate::linalg::work::memory(
        matrix.nonzeros(),
        matrix.entry_capacity(),
        0,
        mask_bytes,
        std::mem::size_of::<(usize, F)>(),
    );
    let visits =
        crate::linalg::sparse::back_substitute_pivots_within(matrix, max_entries, statistics)?;
    Ok((
        visits,
        Report {
            fell_back: true,
            workspace_bytes: mask_bytes,
            ..Report::default()
        },
    ))
}

/// Finish precisely the requested pivot rows; public matrix RREF keeps its full-row contract.
/// Later echelon pivots stay immutable because targets run in increasing leading column.
/// A checked whole-pass reservation precedes mutation; insufficient temporary space selects
/// the original full-RREF pass, with its original admission and error semantics.
pub fn finish<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    selected_columns: &[bool],
    max_entries: usize,
    max_workspace: usize,
    statistics: &mut EliminationStatistics,
) -> Result<(usize, Report), usize> {
    #[cfg(feature = "research-work")]
    use std::mem::size_of;
    debug_assert_eq!(selected_columns.len(), matrix.num_columns());
    let columns = matrix.num_columns();
    let selected = |row: &SparseRow<F>| row.leading_column().is_some_and(|c| selected_columns[c]);
    let targets = matrix.rows().iter().filter(|row| selected(row)).count();
    if targets == 0 {
        return Ok((0, Report::default()));
    }
    // Every selected replacement fits in its suffix. Sum all possible positive growth,
    // then reserve one additional dense row while retained originals are still present.
    let reservation = matrix
        .rows()
        .iter()
        .filter(|row| selected(row))
        .try_fold(matrix.nonzeros(), |bound, row| {
            let suffix = columns - row.leading_column().unwrap();
            bound.checked_add(suffix.saturating_sub(row.nonzeros()))
        })
        .and_then(|bound| bound.checked_add(columns));
    let workspace = workspace_bytes::<F>(columns);
    if reservation.is_none_or(|n| n > max_entries) || workspace.is_none_or(|n| n > max_workspace) {
        return full(matrix, max_entries, selected_columns.len(), statistics);
    }
    let mut report = Report {
        workspace_bytes: workspace.unwrap(),
        reserved_entries: reservation.unwrap(),
        peak_capacity_entries: matrix.entry_capacity(),
        ..Report::default()
    };
    let mut pivots = vec![usize::MAX; columns];
    for (index, row) in matrix.rows().iter().enumerate() {
        if let Some(lead) = row.leading_column() {
            debug_assert_eq!(row.leading_coefficient(), Some(F::ONE));
            debug_assert_eq!(pivots[lead], usize::MAX);
            pivots[lead] = index;
        }
    }
    let mut cells = vec![F::ZERO; columns];
    let mut resident = matrix.nonzeros();
    let mut capacity = matrix.entry_capacity();
    #[cfg(feature = "research-work")]
    let _phase = crate::linalg::work::backward();
    for lead in 0..columns {
        let index = pivots[lead];
        if index == usize::MAX || !selected_columns[lead] {
            continue;
        }
        let original = matrix.row(index);
        let original_len = original.nonzeros();
        let original_capacity = original.capacity();
        let mut live = original_len;
        for &(c, value) in original.entries() {
            cells[c] = value;
        }
        #[cfg(feature = "research-work")]
        crate::linalg::work::target(index);
        for column in lead + 1..columns {
            let factor = cells[column];
            let source = pivots[column];
            if source == usize::MAX || factor.is_zero() {
                continue;
            }
            let pivot = matrix.row(source);
            report.products = report.products.saturating_add(pivot.nonzeros());
            #[cfg(feature = "research-work")]
            crate::linalg::work::pivot(pivot.nonzeros());
            for &(c, value) in pivot.entries() {
                let before = cells[c];
                let after = before - factor * value;
                cells[c] = after;
                live += usize::from(before.is_zero());
                live -= usize::from(after.is_zero());
            }
            statistics.row_operations += 1;
            // The retained original is a temporary copy, not an additional mathematical row.
            statistics.peak_nonzeros = statistics.peak_nonzeros.max(resident - original_len + live);
        }
        let mut output = Vec::with_capacity(live);
        for (column, cell) in cells.iter_mut().enumerate().skip(lead) {
            let value = std::mem::replace(cell, F::ZERO);
            if !value.is_zero() {
                output.push((column, value));
            }
        }
        debug_assert_eq!(output.len(), live);
        report.targets += 1;
        report.peak_capacity_entries = report
            .peak_capacity_entries
            .max(capacity.saturating_add(output.capacity()));
        #[cfg(feature = "research-work")]
        {
            crate::linalg::work::counters(|w| {
                w.rows_loaded += 1;
                w.dense_load_entries += original_len;
                w.dense_scan_cells += columns - lead - 1;
                w.dense_gather_cells += columns - lead;
                w.dense_gather_entries += live;
            });
            crate::linalg::work::memory(
                resident - original_len + live,
                capacity.saturating_add(output.capacity()),
                columns * size_of::<F>(),
                columns * (size_of::<usize>() + size_of::<bool>()),
                size_of::<(usize, F)>(),
            );
        }
        capacity = capacity - original_capacity + output.capacity();
        resident = resident - original_len + live;
        matrix.rows_mut()[index] = SparseRow::from_sorted_unchecked(output);
    }
    statistics.final_nonzeros = resident;
    Ok((report.targets, report))
}

/// [`finish`] with its targets reduced on `workers` threads (#845), or `None`, before any row
/// changes, when the field cannot share rows across threads or the reservation does not fit.
/// The caller then runs [`finish`].
///
/// A target reads only pivots right of its lead, and in [`finish`]'s increasing-lead order those
/// are still unfinished when it runs. So every target is a function of the input alone and the
/// targets are independent. They run in waves of consecutive leads, each wave's results written
/// back only after the whole wave has read, which keeps every read an input row: rows, products,
/// row operations and `peak_nonzeros` are [`finish`]'s exactly, at every worker count.
///
/// A wave holds its targets' inputs beside their results until it is written back. The waves are
/// cut so that retention stays under a sixteenth of the resident entries (or one dense row per
/// worker, if larger), and the reservation is [`finish`]'s plus that retention plus one dense row
/// per further worker.
pub(crate) fn finish_parallel<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    selected_columns: &[bool],
    max_entries: usize,
    max_workspace: usize,
    workers: usize,
    statistics: &mut EliminationStatistics,
) -> Option<(usize, Report)> {
    debug_assert_eq!(selected_columns.len(), matrix.num_columns());
    F::concurrent_elimination()?;
    let columns = matrix.num_columns();
    let workers = workers.max(1);
    let mut pivots = vec![usize::MAX; columns];
    for (index, row) in matrix.rows().iter().enumerate() {
        if let Some(lead) = row.leading_column() {
            debug_assert_eq!(row.leading_coefficient(), Some(F::ONE));
            pivots[lead] = index;
        }
    }
    let targets: Vec<usize> = (0..columns)
        .filter(|&lead| selected_columns[lead] && pivots[lead] != usize::MAX)
        .map(|lead| pivots[lead])
        .collect();
    if targets.is_empty() {
        return Some((0, Report::default()));
    }
    let retention_cap = (matrix.nonzeros() / 16).max(columns.saturating_mul(workers));
    let mut waves = vec![0];
    let mut retained = 0usize;
    let mut max_retained = 0usize;
    for (position, &index) in targets.iter().enumerate() {
        let entries = matrix.row(index).nonzeros();
        if retained > 0 && retained.saturating_add(entries) > retention_cap {
            waves.push(position);
            retained = 0;
        }
        retained = retained.saturating_add(entries);
        max_retained = max_retained.max(retained);
    }
    waves.push(targets.len());
    let reservation = targets
        .iter()
        .try_fold(matrix.nonzeros(), |bound, &index| {
            let row = matrix.row(index);
            let suffix = columns - row.leading_column().unwrap();
            bound.checked_add(suffix.saturating_sub(row.nonzeros()))
        })
        .and_then(|bound| bound.checked_add(columns.checked_mul(workers)?))
        .and_then(|bound| bound.checked_add(max_retained));
    let workspace = columns
        .checked_mul(std::mem::size_of::<F>())
        .and_then(|row| row.checked_mul(workers))
        .and_then(|rows| rows.checked_add(columns.checked_mul(std::mem::size_of::<usize>())?));
    if reservation.is_none_or(|n| n > max_entries) || workspace.is_none_or(|n| n > max_workspace) {
        return None;
    }
    let mut report = Report {
        workspace_bytes: workspace.unwrap(),
        reserved_entries: reservation.unwrap(),
        peak_capacity_entries: matrix.entry_capacity(),
        ..Report::default()
    };
    let mut resident = matrix.nonzeros();
    let mut capacity = matrix.entry_capacity();
    for wave in waves.windows(2) {
        let wave = &targets[wave[0]..wave[1]];
        let job = Wave {
            matrix: &*matrix,
            pivots: &pivots,
            targets: wave,
            workers,
        };
        let Ok(finished) = F::run_concurrent(job) else {
            unreachable!("a field with concurrent elimination runs concurrent jobs")
        };
        let held: usize = finished.iter().map(|f| f.row.capacity()).sum();
        report.peak_capacity_entries = report
            .peak_capacity_entries
            .max(capacity.saturating_add(held));
        for (&index, finished) in wave.iter().zip(finished) {
            let original = matrix.row(index);
            let (original_len, original_capacity) = (original.nonzeros(), original.capacity());
            if finished.operations > 0 {
                statistics.peak_nonzeros = statistics
                    .peak_nonzeros
                    .max(resident - original_len + finished.peak);
            }
            statistics.row_operations += finished.operations;
            report.products = report.products.saturating_add(finished.products);
            report.targets += 1;
            resident = resident - original_len + finished.row.nonzeros();
            capacity = capacity - original_capacity + finished.row.capacity();
            matrix.rows_mut()[index] = finished.row;
        }
    }
    statistics.final_nonzeros = resident;
    Some((report.targets, report))
}

/// One target's finished row and what reducing it cost.
struct Finished<F: FiniteField> {
    row: SparseRow<F>,
    operations: usize,
    products: usize,
    peak: usize,
}

/// A wave of [`finish_parallel`]'s targets, reduced against the unchanged matrix.
struct Wave<'a, F: FiniteField> {
    matrix: &'a SparseMatrix<F>,
    pivots: &'a [usize],
    targets: &'a [usize],
    workers: usize,
}

impl<F: FiniteField> Wave<'_, F> {
    fn reduce(&self, accumulator: &mut DenseAccumulator<F>, index: usize) -> Finished<F> {
        let row = self.matrix.row(index);
        let lead = row.leading_column().unwrap();
        accumulator.load(row);
        let (operations, products, peak) = accumulator.sweep_with_peak(|column| {
            let source = self.pivots[column];
            (column != lead && source != usize::MAX).then(|| self.matrix.row(source))
        });
        Finished {
            row: accumulator.take(),
            operations,
            products,
            peak,
        }
    }
}

impl<F: FiniteField> ConcurrentJob<F> for Wave<'_, F> {
    type Output = Vec<Finished<F>>;

    fn run(self) -> Self::Output
    where
        F: Send + Sync,
    {
        let columns = self.matrix.num_columns();
        let workers = self.workers.min(self.targets.len());
        if workers <= 1 {
            let mut accumulator = DenseAccumulator::new(columns);
            return self
                .targets
                .iter()
                .map(|&index| self.reduce(&mut accumulator, index))
                .collect();
        }
        // Targets differ widely in cost (a lower lead has a longer suffix), so each is claimed
        // singly.
        let next = AtomicUsize::new(0);
        let mut slots: Vec<Option<Finished<F>>> = Vec::new();
        slots.resize_with(self.targets.len(), || None);
        let (wave, next) = (&self, &next);
        let parts = crate::util::team::run(workers, |_| {
            let mut accumulator = DenseAccumulator::new(columns);
            let mut done = Vec::new();
            loop {
                let position = next.fetch_add(1, Ordering::Relaxed);
                let Some(&index) = wave.targets.get(position) else {
                    break done;
                };
                done.push((position, wave.reduce(&mut accumulator, index)));
            }
        })
        .into_iter()
        .map(|outcome| outcome.unwrap_or_else(|_| panic!("a candidate-finishing worker panicked")))
        .collect::<Vec<_>>();
        for (position, finished) in parts.into_iter().flatten() {
            slots[position] = Some(finished);
        }
        slots.into_iter().map(Option::unwrap).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        fields::{Bn254Fr, Gf256, Zp13, Zp18446744069414584321, Zp2},
        linalg::sparse::{back_substitute_pivots_within, row_echelon, SparseRow},
        One,
    };

    fn input<F: FiniteField>() -> SparseMatrix<F> {
        SparseMatrix::new(
            5,
            vec![
                SparseRow::new(&[(0, F::ONE), (1, F::ONE), (3, F::ONE)]),
                SparseRow::new(&[(1, F::ONE), (2, F::ONE)]),
                SparseRow::new(&[(2, F::ONE), (4, F::ONE)]),
                SparseRow::new(&[(3, F::ONE), (4, F::ONE)]),
                SparseRow::zero(),
            ],
        )
    }

    fn subsets<F: FiniteField>() {
        for bits in 0..64 {
            let mut matrix = input::<F>();
            if bits >= 32 {
                matrix.rows_mut().reverse();
            }
            let mut stats = row_echelon(&mut matrix);
            let original = matrix.clone();
            let mut full = matrix.clone();
            back_substitute_pivots_within(&mut full, usize::MAX, &mut stats.clone()).unwrap();
            let selected: Vec<_> = (0..5).map(|i| bits & (1 << i) != 0).collect();
            let (_, report) =
                finish(&mut matrix, &selected, usize::MAX, usize::MAX, &mut stats).unwrap();
            assert!(!report.fell_back);
            for (i, row) in original.rows().iter().enumerate() {
                let expected = if row.leading_column().is_some_and(|c| selected[c]) {
                    full.rows()
                        .iter()
                        .find(|r| r.leading_column() == row.leading_column())
                        .unwrap()
                } else {
                    row
                };
                assert_eq!(matrix.row(i), expected);
            }
            assert_eq!(stats.final_nonzeros, matrix.nonzeros());
        }
    }

    // Selection-mask admission checks total workspace and overflow without allocating an oversized matrix.
    #[test]
    fn workspace_preflight_precedes_selection_allocation() {
        let width =
            WORKSPACE_LIMIT / (std::mem::size_of::<Bn254Fr>() + std::mem::size_of::<usize>() + 1);
        assert!(workspace_bytes::<Bn254Fr>(width).unwrap() <= WORKSPACE_LIMIT);
        assert!(workspace_bytes::<Bn254Fr>(width + 1).unwrap() > WORKSPACE_LIMIT);
        assert_eq!(workspace_bytes::<Bn254Fr>(usize::MAX), None);
        assert_eq!(workspace_bytes::<Bn254Fr>(0), Some(0));
    }

    // Every selected subset matches full RREF over prime, binary, extension and wide fields.
    #[test]
    fn selected_rows_are_exact_across_fields() {
        subsets::<Zp13>();
        subsets::<Zp2>();
        subsets::<Gf256>();
        subsets::<Zp18446744069414584321>();
        subsets::<Bn254Fr>();
    }

    // No selected rows need neither dense workspace nor an extra entry reservation.
    #[test]
    fn empty_selection_needs_no_workspace() {
        let mut m = input::<Zp13>();
        let original = m.clone();
        let mut stats = row_echelon(&mut m);
        let allowance = m.nonzeros();
        let (_, r) = finish(&mut m, &[false; 5], allowance, 0, &mut stats).unwrap();
        assert_eq!(m, original);
        assert_eq!(r, Report::default());
    }

    // Insufficient conservative reservation falls back before mutation and preserves full-RREF admission.
    #[test]
    fn tight_allowance_uses_original_full_rref() {
        let mut m = input::<Zp13>();
        let mut stats = row_echelon(&mut m);
        let mut full = m.clone();
        let mut expected_stats = stats.clone();
        back_substitute_pivots_within(&mut full, 100, &mut expected_stats).unwrap();
        let (_, report) = finish(&mut m, &[true; 5], 100, 0, &mut stats).unwrap();
        assert!(report.fell_back);
        assert_eq!(m, full);
        assert_eq!(stats, expected_stats);
    }

    // An entry allowance that admitted full RREF still admits it after selective preflight refuses.
    #[test]
    fn entry_reservation_fallback_preserves_admission_and_errors() {
        for allowance in 0..40 {
            let mut matrix = input::<Zp13>();
            let mut stats = row_echelon(&mut matrix);
            let mut full = matrix.clone();
            let mut expected_stats = stats.clone();
            let expected = back_substitute_pivots_within(&mut full, allowance, &mut expected_stats);
            let actual = finish(&mut matrix, &[true; 5], allowance, usize::MAX, &mut stats);
            if let Ok((_, r)) = &actual {
                if r.fell_back {
                    assert_eq!(matrix, full);
                    assert_eq!(stats, expected_stats);
                }
                assert!(expected.is_ok());
            } else {
                assert_eq!(actual.unwrap_err(), expected.unwrap_err());
            }
        }
    }

    // Positive replacement growth is reserved for the entire pass before any target changes.
    #[test]
    fn later_target_growth_falls_back_before_mutation() {
        let mut matrix = SparseMatrix::new(
            6,
            vec![
                SparseRow::new(&[(0, Zp13::ONE), (2, Zp13::ONE)]),
                SparseRow::new(&[(1, Zp13::ONE), (2, Zp13::ONE)]),
                SparseRow::new(&[
                    (2, Zp13::ONE),
                    (3, Zp13::ONE),
                    (4, Zp13::ONE),
                    (5, Zp13::ONE),
                ]),
            ],
        );
        let mut stats = row_echelon(&mut matrix);
        let mut full = matrix.clone();
        back_substitute_pivots_within(&mut full, 20, &mut stats.clone()).unwrap();
        let (_, r) = finish(&mut matrix, &[true; 6], 20, usize::MAX, &mut stats).unwrap();
        assert!(r.fell_back);
        assert_eq!(matrix, full);
    }

    /// A random echelon matrix of `rows` rows over `columns` columns, with monic pivots.
    fn random_echelon<F: FiniteField>(seed: u64, rows: usize, columns: usize) -> SparseMatrix<F> {
        let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
        let mut next = move || {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            state >> 33
        };
        let input = (0..rows)
            .map(|_| {
                let mut entries = Vec::new();
                for c in 0..columns {
                    let value = <F as FiniteField>::new(1 + next() % 11);
                    if next() % 3 == 0 && !value.is_zero() {
                        entries.push((c, value));
                    }
                }
                SparseRow::new(&entries)
            })
            .collect();
        let mut matrix = SparseMatrix::new(columns, input);
        row_echelon(&mut matrix);
        matrix
    }

    // Parallel finishing reproduces the serial kernel's rows and counters at every worker count.
    #[test]
    fn parallel_finish_matches_serial_finish() {
        fn check<F: FiniteField + Send + Sync>() {
            for seed in 0..24 {
                let columns = 4 + seed as usize % 37;
                let matrix = random_echelon::<F>(seed, 3 + seed as usize % 29, columns);
                let selected: Vec<_> = (0..columns)
                    .map(|c| !(c * 7 + seed as usize).is_multiple_of(3))
                    .collect();
                let mut expected = matrix.clone();
                let mut expected_stats = EliminationStatistics::default();
                let (visits, serial) = finish(
                    &mut expected,
                    &selected,
                    usize::MAX,
                    usize::MAX,
                    &mut expected_stats,
                )
                .unwrap();
                for workers in [1, 2, 4, 16] {
                    let mut actual = matrix.clone();
                    let mut stats = EliminationStatistics::default();
                    let (targets, report) = finish_parallel(
                        &mut actual,
                        &selected,
                        usize::MAX,
                        usize::MAX,
                        workers,
                        &mut stats,
                    )
                    .unwrap();
                    assert_eq!(actual, expected, "seed {seed}, {workers} workers");
                    assert_eq!(targets, visits);
                    assert_eq!(report.targets, serial.targets);
                    assert_eq!(report.products, serial.products);
                    assert_eq!(stats, expected_stats, "seed {seed}, {workers} workers");
                    assert!(!report.fell_back);
                    assert!(report.reserved_entries >= serial.reserved_entries);
                    assert!(report.peak_capacity_entries >= serial.peak_capacity_entries);
                }
            }
        }
        check::<Zp13>();
        check::<Gf256>();
        check::<Zp18446744069414584321>();
        check::<Bn254Fr>();
    }

    // A parallel reservation that cannot fit declines before any row changes.
    #[test]
    fn parallel_finish_declines_a_tight_allowance() {
        let matrix = random_echelon::<Zp13>(3, 12, 20);
        let selected = vec![true; 20];
        let mut serial = matrix.clone();
        let (_, report) = finish(
            &mut serial,
            &selected,
            usize::MAX,
            usize::MAX,
            &mut EliminationStatistics::default(),
        )
        .unwrap();
        assert!(report.targets > 1);
        let mut actual = matrix.clone();
        let declined = finish_parallel(
            &mut actual,
            &selected,
            report.reserved_entries,
            usize::MAX,
            4,
            &mut EliminationStatistics::default(),
        );
        assert!(declined.is_none());
        assert_eq!(actual, matrix);
    }

    // Scratch reservations stay separate from mathematical nonzeros and are never the final count.
    #[test]
    fn reserved_entries_are_not_mathematical_nonzeros() {
        let mut m = input::<Zp13>();
        let mut stats = row_echelon(&mut m);
        let (_, report) = finish(
            &mut m,
            &[true, false, false, false, false],
            1000,
            1000,
            &mut stats,
        )
        .unwrap();
        assert!(report.reserved_entries > stats.peak_nonzeros);
        assert_eq!(report.targets, 1);
        assert_eq!(stats.final_nonzeros, m.nonzeros());
    }
}
