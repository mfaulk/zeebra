use crate::{
    linalg::sparse::{EliminationStatistics, SparseMatrix},
    FiniteField,
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Report {
    pub targets: usize,
    pub products: usize,
    pub scans: usize,
    pub loads: usize,
    pub gathers: usize,
    pub workspace_bytes: usize,
    pub peak_entries: usize,
    pub peak_capacity_entries: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    InvalidEchelon,
    Selection,
    Workspace,
    Entries(usize),
}

/// Reduce only selected rows of a normalized echelon matrix, preserving every other row.
///
/// Targets run by increasing leading column, so every later pivot is still the original
/// echelon row. Left-to-right substitution terminates and yields the unique RREF target.
/// This research entry does not promise that the whole matrix becomes RREF.
///
/// Workspace bounds dense cells and the column index. The entry limit additionally charges
/// the retained original target plus its live dense copy; it can refuse earlier than full RREF.
/// On refusal earlier targets may be reduced, but the current target is unchanged.
///
/// # Errors
/// Rejects mismatched selections, nonmonic/duplicate pivots, workspace overflow or entry limits.
pub fn reduce<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    selected: &[bool],
    max_entries: usize,
    max_workspace_bytes: usize,
    statistics: &mut EliminationStatistics,
) -> Result<Report, Error> {
    use crate::linalg::{sparse::SparseRow, work};
    let _phase = work::backward();
    if selected.len() != matrix.num_rows() {
        return Err(Error::Selection);
    }
    let columns = matrix.num_columns();
    let workspace = columns
        .checked_mul(std::mem::size_of::<F>() + std::mem::size_of::<usize>())
        .filter(|bytes| *bytes <= max_workspace_bytes)
        .ok_or(Error::Workspace)?;
    let mut pivot = vec![usize::MAX; columns];
    for (index, row) in matrix.rows().iter().enumerate() {
        if let Some(c) = row.leading_column() {
            if row.leading_coefficient() != Some(F::ONE) || pivot[c] != usize::MAX {
                return Err(Error::InvalidEchelon);
            }
            pivot[c] = index;
        }
    }
    let mut resident = matrix.nonzeros();
    if resident > max_entries {
        return Err(Error::Entries(resident));
    }
    let mut capacity = matrix.entry_capacity();
    let mut report = Report {
        workspace_bytes: workspace,
        peak_entries: resident,
        peak_capacity_entries: capacity,
        ..Report::default()
    };
    let mut cells = vec![F::ZERO; columns];
    for lead in 0..columns {
        let index = pivot[lead];
        if index == usize::MAX || !selected[index] {
            continue;
        }
        work::target(index);
        let original = matrix.row(index);
        let original_len = original.nonzeros();
        let original_capacity = original.capacity();
        let mut live = original_len;
        let peak = resident + live;
        if peak > max_entries {
            return Err(Error::Entries(peak));
        }
        report.targets += 1;
        report.loads += live;
        report.peak_entries = report.peak_entries.max(peak);
        for &(column, value) in original.entries() {
            cells[column] = value;
        }
        for column in lead + 1..columns {
            let factor = cells[column];
            let source = pivot[column];
            if source == usize::MAX || factor.is_zero() {
                continue;
            }
            let row = matrix.row(source);
            report.products += row.nonzeros();
            work::pivot(row.nonzeros());
            for &(c, value) in row.entries() {
                let before = cells[c];
                let after = before - factor * value;
                cells[c] = after;
                live += usize::from(before.is_zero());
                live -= usize::from(after.is_zero());
            }
            statistics.row_operations += 1;
            let peak = resident + live;
            report.peak_entries = report.peak_entries.max(peak);
            statistics.peak_nonzeros = statistics.peak_nonzeros.max(peak);
            if peak > max_entries {
                return Err(Error::Entries(peak));
            }
        }
        report.scans += columns - lead - 1;
        let mut output = Vec::with_capacity(live);
        for (column, cell) in cells.iter_mut().enumerate().skip(lead) {
            let value = std::mem::replace(cell, F::ZERO);
            if !value.is_zero() {
                output.push((column, value));
            }
        }
        debug_assert_eq!(output.len(), live);
        report.peak_capacity_entries = report
            .peak_capacity_entries
            .max(capacity + output.capacity());
        capacity = capacity - original_capacity + output.capacity();
        report.gathers += live;
        work::counters(|w| {
            w.rows_loaded += 1;
            w.dense_load_entries += original_len;
            w.dense_scan_cells += columns - lead - 1;
            w.dense_gather_cells += columns - lead;
            w.dense_gather_entries += live;
        });
        resident = resident - original_len + live;
        matrix.rows_mut()[index] = SparseRow::from_sorted_unchecked(output);
        statistics.final_nonzeros = resident;
    }
    statistics.peak_nonzeros = statistics.peak_nonzeros.max(report.peak_entries);
    statistics.final_nonzeros = resident;
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        fields::{Bn254Fr, Gf256, Zp13, Zp18446744069414584321, Zp2},
        linalg::sparse::{back_substitute_pivots_within, row_echelon, SparseRow},
    };

    fn matrix<F: FiniteField>() -> SparseMatrix<F> {
        let rows = [
            vec![(0, 1), (1, 2), (3, 1)],
            vec![(1, 1), (2, 1)],
            vec![(2, 1), (4, 1)],
            vec![(3, 1), (4, 2)],
            vec![],
        ];
        SparseMatrix::new(
            5,
            rows.into_iter()
                .map(|row| {
                    SparseRow::new(
                        &row.into_iter()
                            .map(|(c, n)| (c, if n == 1 { F::ONE } else { F::ONE + F::ONE }))
                            .collect::<Vec<_>>(),
                    )
                })
                .collect(),
        )
    }

    fn subsets<F: FiniteField>() {
        for bits in 0..32 {
            let mut input = matrix::<F>();
            let mut stats = row_echelon(&mut input);
            let original = input.clone();
            let mut full = input.clone();
            back_substitute_pivots_within(&mut full, usize::MAX, &mut stats.clone()).unwrap();
            let selected: Vec<_> = (0..5).map(|i| bits & (1 << i) != 0).collect();
            reduce(&mut input, &selected, usize::MAX, usize::MAX, &mut stats).unwrap();
            for (i, selected) in selected.into_iter().enumerate() {
                let expected = if selected {
                    full.rows()
                        .iter()
                        .find(|r| r.leading_column() == original.row(i).leading_column())
                        .unwrap()
                } else {
                    original.row(i)
                };
                assert_eq!(input.row(i), expected);
            }
            assert_eq!(stats.final_nonzeros, input.nonzeros());
        }
    }

    // Every selected subset equals full RREF while unselected rows retain their echelon tails.
    #[test]
    fn subsets_match_rref_across_fields() {
        subsets::<Zp13>();
        subsets::<Zp2>();
        subsets::<Zp18446744069414584321>();
        subsets::<Bn254Fr>();
        subsets::<Gf256>();
    }

    // Duplicate pivots, nonmonic rows and mismatched selections are rejected before mutation.
    #[test]
    fn invalid_inputs_are_unchanged() {
        let row = SparseRow::from_sorted(vec![(0, Zp13::new(2))]).unwrap();
        for rows in [vec![row], vec![SparseRow::new(&[(0, Zp13::new(1))]); 2]] {
            let mut m = SparseMatrix::new(1, rows);
            let original = m.clone();
            assert_eq!(
                reduce(
                    &mut m,
                    &vec![true; original.num_rows()],
                    100,
                    100,
                    &mut EliminationStatistics::default()
                ),
                Err(Error::InvalidEchelon)
            );
            assert_eq!(m, original);
        }
        let mut m = matrix::<Zp13>();
        assert_eq!(
            reduce(&mut m, &[], 100, 100, &mut EliminationStatistics::default()),
            Err(Error::Selection)
        );
    }

    // Workspace refusal precedes mutation and a later invocation can reuse the matrix.
    #[test]
    fn workspace_refusal_is_reusable() {
        let mut m = matrix::<Zp13>();
        let original = m.clone();
        let mut stats = row_echelon(&mut m);
        assert_eq!(
            reduce(&mut m, &[true; 5], 100, 0, &mut stats),
            Err(Error::Workspace)
        );
        assert_eq!(m, original);
        reduce(&mut m, &[true; 5], 100, usize::MAX, &mut stats).unwrap();
    }

    // An entry refusal preserves the current row and cannot leak scratch into a retry.
    #[test]
    fn entry_refusal_is_reusable() {
        let mut m = matrix::<Zp13>();
        let mut stats = row_echelon(&mut m);
        let original = m.clone();
        assert!(matches!(
            reduce(
                &mut m,
                &[true; 5],
                original.nonzeros(),
                usize::MAX,
                &mut stats
            ),
            Err(Error::Entries(_))
        ));
        assert_eq!(m, original);
        reduce(&mut m, &[true; 5], 100, usize::MAX, &mut stats).unwrap();
    }

    // Fill-in can exceed the allowance mid-subtraction without losing the current target.
    #[test]
    fn mid_operation_refusal_preserves_target() {
        let mut m = SparseMatrix::new(
            5,
            vec![
                SparseRow::new(&[(0, Zp13::new(1)), (1, Zp13::new(1))]),
                SparseRow::new(&[
                    (1, Zp13::new(1)),
                    (2, Zp13::new(1)),
                    (3, Zp13::new(1)),
                    (4, Zp13::new(1)),
                ]),
            ],
        );
        let original = m.clone();
        let mut stats = row_echelon(&mut m);
        assert_eq!(
            reduce(&mut m, &[true, false], 8, 1024, &mut stats),
            Err(Error::Entries(10))
        );
        assert_eq!(m, original);
        reduce(&mut m, &[true, false], 100, 1024, &mut stats).unwrap();
        assert_eq!(m.row(0).nonzeros(), 4);
    }

    // Dependent and empty rows with varied fill produce exact selected RREF rows after forward elimination.
    #[test]
    fn randomized_rank_deficient_inputs() {
        use rand::{rngs::StdRng, Rng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(269);
        for _ in 0..64 {
            let mut rows: Vec<_> = (0..6)
                .map(|_| {
                    SparseRow::new(
                        &(0..9)
                            .map(|c| (c, Zp13::new(rng.gen_range(0..13))))
                            .collect::<Vec<_>>(),
                    )
                })
                .collect();
            rows.push(rows[0].clone());
            rows.push(SparseRow::zero());
            let mut m = SparseMatrix::new(9, rows);
            let mut stats = row_echelon(&mut m);
            let original = m.clone();
            let mut full = m.clone();
            back_substitute_pivots_within(&mut full, usize::MAX, &mut stats.clone()).unwrap();
            let selected: Vec<_> = (0..m.num_rows()).map(|_| rng.gen()).collect();
            reduce(&mut m, &selected, usize::MAX, usize::MAX, &mut stats).unwrap();
            for (index, chosen) in selected.into_iter().enumerate() {
                let expected = if chosen {
                    full.rows()
                        .iter()
                        .find(|r| r.leading_column() == original.row(index).leading_column())
                        .unwrap()
                } else {
                    original.row(index)
                };
                assert_eq!(m.row(index), expected);
            }
        }
    }

    // Empty and zero-only matrices perform no arithmetic or allocation-sized workspace.
    #[test]
    fn empty_inputs_complete() {
        let mut m = SparseMatrix::<Zp13>::zero(0, 0);
        assert_eq!(
            reduce(&mut m, &[], 0, 0, &mut EliminationStatistics::default()).unwrap(),
            Report::default()
        );
    }
}
