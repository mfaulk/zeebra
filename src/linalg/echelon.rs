//! The elimination interface F4 calls, and the backends that implement it.
//!
//! Two functions, and the choice of representation is a parameter rather than a call site. That
//! separation exists so that a caller which knows something about the *structure* of its matrix —
//! which rows are already pivots, which are the work — and a backend which knows something about
//! its *density* can be developed independently of each other.
//!
//! [`Backend::Sparse`] is the implementation from the preceding milestone and the reference every
//! other backend is checked against. The remaining variants are declared here so that the option
//! surface is complete before the implementations exist; each currently delegates to the sparse
//! path, which is documented per variant rather than left to be discovered.
//!
//! `linalg` does not depend on `grobner`, and does not learn to. [`Backend`] is this module's own
//! type; F4 holds one in its options.

use std::collections::HashMap;

use crate::{
    linalg::sparse::{row_echelon_within, EliminationStatistics, SparseMatrix, SparseRow},
    FiniteField,
};

/// Which representation an elimination uses.
///
/// The mathematical result does not depend on this choice: every backend produces the same rank
/// and the same row space, and leaves every nonzero row with a distinct leading column and a unit
/// pivot. Only the cost differs.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Backend {
    /// Sorted-vector sparse rows throughout. The measured baseline.
    #[default]
    Sparse,

    /// Dense rows throughout.
    ///
    /// Currently the sparse path. A dense row echelon with this module's contract — the same
    /// leftmost-first pivot rule, the same unit-pivot normalization, one inverse per pivot — is
    /// what makes a sparse/dense comparison mean anything, and is the first deliverable of the
    /// linear-algebra workstream.
    Dense,

    /// Chosen per matrix, or per row, from the density actually observed.
    ///
    /// Currently the sparse path. A policy keyed on *global* density would be keyed on the wrong
    /// quantity: an F4 matrix with thousands of columns can hold a few nearly dense rows and still
    /// be a fraction of a percent dense overall.
    Adaptive,
}

/// Reduce `matrix` to row echelon form in place, and report the work done.
///
/// Every nonzero row of the result has a unit leading coefficient and a leading column distinct
/// from every other row's, and every row processed after a column acquired its pivot is zero in
/// that column. Rows keep their arrival order.
///
/// # Errors
/// The count that crossed `max_nonzeros`, if more than that many nonzero entries were ever live at
/// once. `matrix` is then partially reduced and must not be read.
pub fn row_echelon_with<F: FiniteField>(
    backend: Backend,
    matrix: &mut SparseMatrix<F>,
    max_nonzeros: usize,
) -> Result<EliminationStatistics, usize> {
    match backend {
        Backend::Sparse | Backend::Dense | Backend::Adaptive => {
            row_echelon_within(matrix, max_nonzeros)
        }
    }
}

/// Reduce rows `[split..]` against the pivots of rows `[..split]`, then echelonize them.
///
/// The upper rows are treated as a set of pivots that is already established: they are left
/// exactly where they are, are not normalized, and are not reduced against one another. Only the
/// lower rows are rewritten. A caller that built its upper block so as to already be in echelon
/// form therefore pays nothing to rediscover it, and nothing in fill-in for reducing it against
/// itself.
///
/// After the call the whole matrix is in row echelon form in the sense above: every nonzero row
/// has a distinct leading column, and the lower rows have unit pivots. The row space is unchanged.
///
/// `split == 0` is a full echelon of every row; `split == num_rows` establishes the pivot map and
/// does nothing else. Both are useful and both are tested.
///
/// # Panics
/// If `split` exceeds the row count, if two of the upper rows lead with the same column, or if an
/// upper row's leading coefficient is not one. Those are the preconditions, and a caller that
/// violates them would otherwise get a wrong answer rather than a failure.
///
/// # Errors
/// As [`row_echelon_with`].
pub fn reduce_rows_against_pivots_with<F: FiniteField>(
    backend: Backend,
    matrix: &mut SparseMatrix<F>,
    split: usize,
    max_nonzeros: usize,
) -> Result<EliminationStatistics, usize> {
    match backend {
        Backend::Sparse | Backend::Dense | Backend::Adaptive => {
            sparse_reduce_rows_against_pivots(matrix, split, max_nonzeros)
        }
    }
}

/// [`reduce_rows_against_pivots_with`] over sorted-vector sparse rows.
fn sparse_reduce_rows_against_pivots<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    split: usize,
    max_nonzeros: usize,
) -> Result<EliminationStatistics, usize> {
    assert!(
        split <= matrix.num_rows(),
        "a split of {} in a matrix of {} rows",
        split,
        matrix.num_rows()
    );

    let initial_nonzeros = matrix.nonzeros();
    let mut statistics = EliminationStatistics {
        initial_nonzeros,
        peak_nonzeros: initial_nonzeros,
        ..Default::default()
    };
    if initial_nonzeros > max_nonzeros {
        return Err(initial_nonzeros);
    }

    // The pivots the caller supplied. Checked rather than trusted: a duplicated leading column
    // would silently drop one of the two relations, which is the kind of wrong answer that looks
    // like a correct one.
    let mut pivot_of_column: HashMap<usize, usize> = HashMap::with_capacity(split);
    for index in 0..split {
        let Some(column) = matrix.row(index).leading_column() else {
            statistics.zero_rows += 1;
            continue;
        };
        assert_eq!(
            matrix.row(index).leading_coefficient(),
            Some(F::ONE),
            "pivot row {} is not normalized",
            index
        );
        if let Some(previous) = pivot_of_column.insert(column, index) {
            panic!(
                "pivot rows {} and {} both lead with column {}",
                previous, index, column
            );
        }
        statistics.rank += 1;
    }

    // Nonzero entries held by the rows still in the matrix; the row being worked on is taken out.
    let mut resident = initial_nonzeros;
    let mut scratch: Vec<(usize, F)> = Vec::new();

    for index in split..matrix.num_rows() {
        let mut row = std::mem::take(&mut matrix.rows_mut()[index]);
        resident -= row.nonzeros();

        while let Some(column) = row.leading_column() {
            match pivot_of_column.get(&column) {
                Some(&pivot_index) => {
                    // Every pivot's leading coefficient is one, so the factor that clears this
                    // column is this row's own leading coefficient.
                    let factor = row
                        .leading_coefficient()
                        .expect("a row with a leading column has a leading coefficient");
                    let pivot: &SparseRow<F> = matrix.row(pivot_index);
                    row.subtract_scaled(pivot, &factor, &mut scratch);
                    statistics.row_operations += 1;
                    let live = resident + row.nonzeros();
                    statistics.peak_nonzeros = statistics.peak_nonzeros.max(live);
                    if live > max_nonzeros {
                        return Err(live);
                    }
                }
                None => {
                    if row.normalize() {
                        statistics.pivot_inversions += 1;
                    }
                    pivot_of_column.insert(column, index);
                    statistics.rank += 1;
                    break;
                }
            }
        }

        if row.is_zero() {
            statistics.zero_rows += 1;
        }
        resident += row.nonzeros();
        statistics.peak_nonzeros = statistics.peak_nonzeros.max(resident);
        matrix.rows_mut()[index] = row;
    }

    statistics.final_nonzeros = resident;
    debug_assert_eq!(statistics.final_nonzeros, matrix.nonzeros());
    debug_assert_eq!(statistics.rank, matrix.nonzero_rows());
    debug_assert_eq!(statistics.rank + statistics.zero_rows, matrix.num_rows());
    Ok(statistics)
}

#[cfg(test)]
mod tests {
    use super::{reduce_rows_against_pivots_with, row_echelon_with, Backend};
    use crate::{
        fields::{Zp13, Zp2147483647, Zp7},
        linalg::sparse::{row_echelon, SparseMatrix, SparseRow},
        FiniteField,
    };
    use rand::{prelude::StdRng, Rng, SeedableRng};

    const BACKENDS: [Backend; 3] = [Backend::Sparse, Backend::Dense, Backend::Adaptive];

    type F = Zp13;

    fn matrix_of(rows: &[&[(usize, u64)]], num_columns: usize) -> SparseMatrix<F> {
        let rows: Vec<SparseRow<F>> = rows
            .iter()
            .map(|entries| {
                SparseRow::new(
                    &entries
                        .iter()
                        .map(|(column, value)| (*column, F::new(*value)))
                        .collect::<Vec<_>>(),
                )
            })
            .collect();
        SparseMatrix::new(num_columns, rows)
    }

    /// A deterministic sparse matrix, for the comparisons that need many shapes.
    fn random_matrix<G: FiniteField>(
        rows: usize,
        columns: usize,
        density: f64,
        seed: u64,
    ) -> SparseMatrix<G> {
        let mut rng = StdRng::seed_from_u64(seed);
        let rows: Vec<SparseRow<G>> = (0..rows)
            .map(|_| {
                let mut entries: Vec<(usize, G)> = Vec::new();
                for column in 0..columns {
                    if rng.gen_bool(density) {
                        entries.push((column, G::random(&mut rng)));
                    }
                }
                SparseRow::new(&entries)
            })
            .collect();
        SparseMatrix::new(columns, rows)
    }

    /// Every backend currently computes the same echelon form as the sparse implementation.
    ///
    /// This is the property that makes `Backend` safe to add variants to before they are
    /// implemented, and it is the property each new backend has to keep.
    #[test]
    fn test_every_backend_agrees_with_the_sparse_echelon() {
        for (rows, columns, density) in [(8, 12, 0.3), (16, 8, 0.5), (24, 24, 0.1), (5, 40, 0.6)] {
            for seed in 0..4 {
                let original: SparseMatrix<F> = random_matrix(rows, columns, density, seed);
                let mut expected = original.clone();
                let reference = row_echelon(&mut expected);

                for backend in BACKENDS {
                    let mut actual = original.clone();
                    let statistics = row_echelon_with(backend, &mut actual, usize::MAX)
                        .expect("unbounded cannot fail");
                    assert_eq!(actual, expected, "{:?} disagreed on the matrix", backend);
                    assert_eq!(statistics, reference, "{:?} disagreed on the work", backend);
                }
            }
        }
    }

    /// Splitting at zero is a full echelon, and the result matches the unsplit one exactly.
    #[test]
    fn test_split_at_zero_is_a_full_echelon() {
        for backend in BACKENDS {
            let original: SparseMatrix<F> = random_matrix(12, 16, 0.3, 11);
            let mut expected = original.clone();
            let reference = row_echelon(&mut expected);

            let mut actual = original.clone();
            let statistics = reduce_rows_against_pivots_with(backend, &mut actual, 0, usize::MAX)
                .expect("unbounded cannot fail");
            assert_eq!(actual, expected, "{:?}", backend);
            assert_eq!(statistics, reference, "{:?}", backend);
        }
    }

    /// Splitting at the row count establishes the pivot map and rewrites nothing.
    #[test]
    fn test_split_at_the_row_count_changes_nothing() {
        for backend in BACKENDS {
            // Already echelon: distinct leading columns, unit pivots.
            let original = matrix_of(&[&[(0, 1), (2, 5)], &[(1, 1), (3, 7)], &[(4, 1)]], 5);
            let mut actual = original.clone();
            let split = actual.num_rows();
            let statistics =
                reduce_rows_against_pivots_with(backend, &mut actual, split, usize::MAX)
                    .expect("unbounded cannot fail");

            assert_eq!(actual, original, "{:?}: rows were rewritten", backend);
            assert_eq!(statistics.rank, 3, "{:?}", backend);
            assert_eq!(statistics.row_operations, 0, "{:?}", backend);
            assert_eq!(statistics.zero_rows, 0, "{:?}", backend);
        }
    }

    /// An upper block that is already echelon makes the split and the unsplit paths identical.
    ///
    /// This is the fact a structured F4 elimination rests on: when the rows that are going to be
    /// pivots are put first and already have distinct leading columns, a full echelon performs no
    /// row operation on them either — so the two paths agree, and the split one skips the scan
    /// that discovers what it was already told.
    #[test]
    fn test_an_echelon_upper_block_makes_the_two_paths_agree() {
        for backend in BACKENDS {
            // Rows 0..3 have distinct leading columns 0, 1, 2 and unit pivots.
            let original = matrix_of(
                &[
                    &[(0, 1), (3, 4), (5, 2)],
                    &[(1, 1), (3, 9), (4, 1)],
                    &[(2, 1), (5, 6)],
                    // The work: these lead in columns the pivots own.
                    &[(0, 3), (1, 2), (4, 7)],
                    &[(1, 5), (2, 8), (5, 11)],
                    &[(0, 2), (3, 1)],
                ],
                6,
            );

            let mut split_path = original.clone();
            let split_statistics =
                reduce_rows_against_pivots_with(backend, &mut split_path, 3, usize::MAX)
                    .expect("unbounded cannot fail");

            let mut full_path = original.clone();
            let full_statistics = row_echelon(&mut full_path);

            assert_eq!(split_path, full_path, "{:?}", backend);
            assert_eq!(split_statistics, full_statistics, "{:?}", backend);
        }
    }

    /// The row space and the rank are what the contract promises, over several fields.
    #[test]
    fn test_rank_and_row_space_agree_with_a_full_echelon() {
        fn check<G: FiniteField>(seed: u64) {
            for (rows, columns, density, split) in [
                (10, 14, 0.3, 4),
                (20, 10, 0.4, 7),
                (16, 32, 0.2, 1),
                (9, 9, 0.5, 8),
            ] {
                let original: SparseMatrix<G> = random_matrix(rows, columns, density, seed);

                // Put the matrix's own first `split` echelon rows on top, so the precondition
                // holds, then compare against a full echelon of the same arrangement.
                let mut prepared = original.clone();
                let _ = row_echelon(&mut prepared);
                prepared.sort_rows_by_leading_column();

                let mut split_path = prepared.clone();
                let split_statistics = reduce_rows_against_pivots_with(
                    Backend::Sparse,
                    &mut split_path,
                    split.min(prepared.num_rows()),
                    usize::MAX,
                )
                .expect("unbounded cannot fail");

                let mut full_path = prepared.clone();
                let full_statistics = row_echelon(&mut full_path);

                assert_eq!(split_statistics.rank, full_statistics.rank);
                assert_eq!(split_path, full_path);
            }
        }
        check::<Zp7>(3);
        check::<Zp13>(4);
        check::<Zp2147483647>(5);
    }

    /// The entry budget refuses the work rather than reporting it afterwards.
    #[test]
    fn test_the_budget_is_enforced() {
        let original: SparseMatrix<F> = random_matrix(24, 24, 0.5, 2);
        let initial = original.nonzeros();

        for backend in BACKENDS {
            let mut matrix = original.clone();
            assert_eq!(
                row_echelon_with(backend, &mut matrix, initial - 1),
                Err(initial),
                "{:?}: a budget below the input should fail immediately",
                backend
            );

            let mut matrix = original.clone();
            assert_eq!(
                reduce_rows_against_pivots_with(backend, &mut matrix, 0, initial - 1),
                Err(initial),
                "{:?}",
                backend
            );
        }
    }

    /// A split beyond the row count is a programming error, not a silently clamped one.
    #[test]
    #[should_panic(expected = "a split of 5 in a matrix of 3 rows")]
    fn test_a_split_beyond_the_row_count_panics() {
        let mut matrix = matrix_of(&[&[(0, 1)], &[(1, 1)], &[(2, 1)]], 3);
        let _ = reduce_rows_against_pivots_with(Backend::Sparse, &mut matrix, 5, usize::MAX);
    }

    /// Two upper rows leading with the same column violate the precondition and are rejected.
    #[test]
    #[should_panic(expected = "both lead with column 0")]
    fn test_duplicate_upper_pivots_panic() {
        let mut matrix = matrix_of(&[&[(0, 1), (1, 2)], &[(0, 1), (2, 3)]], 3);
        let _ = reduce_rows_against_pivots_with(Backend::Sparse, &mut matrix, 2, usize::MAX);
    }

    /// An unnormalized upper pivot violates the precondition and is rejected.
    #[test]
    #[should_panic(expected = "pivot row 0 is not normalized")]
    fn test_an_unnormalized_upper_pivot_panics() {
        let mut matrix = matrix_of(&[&[(0, 3), (1, 2)], &[(1, 1)]], 3);
        let _ = reduce_rows_against_pivots_with(Backend::Sparse, &mut matrix, 1, usize::MAX);
    }

    /// Zero rows in the upper block are counted, not mistaken for pivots.
    #[test]
    fn test_zero_rows_in_the_upper_block() {
        // Upper block: a pivot in column 0, an empty row, a pivot in column 1. The lower row is
        // their sum, so it reduces to zero and contributes no pivot of its own.
        let mut matrix = matrix_of(
            &[&[(0, 1), (2, 4)], &[], &[(1, 1)], &[(0, 1), (1, 4), (2, 4)]],
            3,
        );
        let statistics =
            reduce_rows_against_pivots_with(Backend::Sparse, &mut matrix, 3, usize::MAX)
                .expect("unbounded cannot fail");
        assert_eq!(statistics.rank, 2, "the empty upper row is not a pivot");
        assert_eq!(
            statistics.zero_rows, 2,
            "the empty upper row and the dependent lower row"
        );
        assert_eq!(
            statistics.rank + statistics.zero_rows,
            matrix.num_rows(),
            "every row is either a pivot or zero"
        );
    }
}
