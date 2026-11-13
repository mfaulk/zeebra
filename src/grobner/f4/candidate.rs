use crate::{
    linalg::sparse::{EliminationStatistics, SparseMatrix},
    FiniteField,
};

#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct Report {
    pub targets: usize,
    pub products: usize,
    pub workspace_bytes: usize,
    pub reserved_entries: usize,
    pub peak_capacity_entries: usize,
    pub fell_back: bool,
}

pub(crate) const WORKSPACE_LIMIT: usize = 64 * 1024 * 1024;

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
pub(crate) fn finish<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    selected_columns: &[bool],
    max_entries: usize,
    max_workspace: usize,
    statistics: &mut EliminationStatistics,
) -> Result<(usize, Report), usize> {
    use crate::linalg::sparse::SparseRow;
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
