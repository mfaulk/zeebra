//! Deterministic Gaussian elimination on a sparse finite-field matrix.
//!
//! Rows are taken in index order; each is reduced against the pivots already established, and
//! becomes the pivot for its own leading column if that column has none. Over a finite field there
//! is no numerical stability to pivot for, so the choice can be the leftmost nonzero column and
//! the first row to reach it — which makes the result a function of the input alone.
//!
//! See Sec 2.10 of Ideals, Varieties, and Algorithms by Cox, Little, and O'Shea for the role this
//! plays in F4, and Faugère (1999) for the algorithm that calls it.

use crate::{
    linalg::{
        sparse::{matrix::SparseMatrix, row::SparseRow},
        PivotIndex,
    },
    FiniteField,
};

/// Counters describing the work an elimination performed.
///
/// Reported because the cost of a sparse elimination is not predictable from its dimensions: a
/// matrix that is one percent dense to begin with may be far denser by the time it is reduced, and
/// `peak_nonzeros` against `initial_nonzeros` is what says whether that happened.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct EliminationStatistics {
    /// The number of pivots found, which is the rank of the matrix.
    pub rank: usize,

    /// Rows that reduced to zero, i.e. the linear dependencies among the input rows.
    pub zero_rows: usize,

    /// Nonzero entries in the input.
    pub initial_nonzeros: usize,

    /// Nonzero entries in the result.
    pub final_nonzeros: usize,

    /// The largest number of nonzero entries live at any point during the elimination.
    pub peak_nonzeros: usize,

    /// Row operations performed, i.e. subtractions of a scaled pivot row from another row.
    pub row_operations: usize,

    /// Modular inverses computed to normalize a pivot to one.
    ///
    /// Counted separately from row operations because an inverse is a modular exponentiation of
    /// about log2(q) multiplications, far more than the row operation it enables. A row whose
    /// pivot is already one — the common case in F4, whose rows come from monic basis elements —
    /// costs none.
    pub pivot_inversions: usize,
}

/// Reduce `matrix` to row echelon form in place, and report the work done.
///
/// Every nonzero row of the result has a unit leading coefficient and a leading column distinct
/// from every other row's, and every row processed after a column acquired its pivot is zero in
/// that column. Rows keep their arrival order; [`SparseMatrix::sort_rows_by_leading_column`] turns
/// that into the staircase shape if a caller needs it. F4 does not: it reads each row's leading
/// column, not the matrix's shape.
///
/// Entries above a pivot are left alone. [`reduced_row_echelon`] removes them, at the cost of a
/// second pass that F4's candidate extraction has no use for.
pub fn row_echelon<F: FiniteField>(matrix: &mut SparseMatrix<F>) -> EliminationStatistics {
    row_echelon_within(matrix, usize::MAX)
        .expect("an unbounded elimination cannot exceed its budget")
}

/// As [`row_echelon`], but abandoned if more than `max_nonzeros` entries are ever live at once.
///
/// Elimination can make a matrix far denser than the one it was handed, and how much denser is not
/// predictable from the input. A budget turns running out of memory into a return value: the
/// `Err` carries the count that crossed the limit, and `matrix` is left partially reduced and
/// should not be read.
///
/// The budget is checked after every row operation, so the overshoot is bounded by one row rather
/// than by the whole matrix.
pub fn row_echelon_within<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    max_nonzeros: usize,
) -> Result<EliminationStatistics, usize> {
    let initial_nonzeros = matrix.nonzeros();
    let mut statistics = EliminationStatistics {
        initial_nonzeros,
        peak_nonzeros: initial_nonzeros,
        ..Default::default()
    };
    if initial_nonzeros > max_nonzeros {
        return Err(initial_nonzeros);
    }

    // Nonzero entries held by the rows left in the matrix. The row being worked on is taken out of
    // the matrix, so its own entries are added back in when the peak is sampled.
    let mut resident = statistics.initial_nonzeros;

    // Which row is the pivot for a given column, indexed by the column. Never iterated, so no
    // storage order can reach the result.
    let mut pivot_of_column = PivotIndex::new(matrix.num_columns(), matrix.num_rows());
    let mut scratch: Vec<(usize, F)> = Vec::new();

    for index in 0..matrix.num_rows() {
        // Taken out so that the pivot rows, which are still in the matrix, can be read while this
        // one is written. A pivot's index is always one already processed, so never this one.
        let mut row = std::mem::take(&mut matrix.rows_mut()[index]);
        resident -= row.nonzeros();

        while let Some(column) = row.leading_column() {
            match pivot_of_column.pivot_of(column) {
                Some(pivot_index) => {
                    // The pivot's leading coefficient is one, so the factor that clears this
                    // column is this row's leading coefficient itself.
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

/// Reduce `matrix` to reduced row echelon form in place, and report the work done.
///
/// As [`row_echelon`], and then each pivot column is eliminated from every other row, so that a
/// pivot column holds a single nonzero entry. Pivots are processed right to left, so that by the
/// time a pivot row is used to clear its own column it has already been cleared of every pivot
/// column to its right — which is what makes one pass enough.
///
/// The reported statistics cover both passes. The result is canonical: reduced row echelon form is
/// unique up to the order of the rows, and the rows are sorted by leading column.
pub fn reduced_row_echelon<F: FiniteField>(matrix: &mut SparseMatrix<F>) -> EliminationStatistics {
    reduced_row_echelon_counting_rows(matrix).0
}

/// [`reduced_row_echelon`], also reporting how many rows the back-substitution pass examined.
///
/// The count is what the output-sensitivity test weighs against the entries the pivot columns
/// actually hold; it is not part of the public contract, which is why it is not an
/// [`EliminationStatistics`] field.
fn reduced_row_echelon_counting_rows<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
) -> (EliminationStatistics, usize) {
    let mut statistics = row_echelon(matrix);
    let mut scratch: Vec<(usize, F)> = Vec::new();
    let mut resident = statistics.final_nonzeros;
    let mut rows_examined = 0usize;

    // Pivot columns, right to left. The sort stays: the rows are visited in row order, and what
    // the pass needs is column order, so the sort is what converts the one into the other rather
    // than a guard against the pivot index's storage order. Collecting from the rows rather than
    // from the index keeps the two facts independent.
    let mut pivots: Vec<(usize, usize)> = (0..matrix.num_rows())
        .filter_map(|index| matrix.row(index).leading_column().map(|c| (c, index)))
        .collect();
    pivots.sort_unstable();

    for &(column, pivot_index) in pivots.iter().rev() {
        for index in 0..matrix.num_rows() {
            if index == pivot_index {
                continue;
            }
            rows_examined += 1;
            let factor = matrix.row(index).coefficient(column);
            if factor.is_zero() {
                continue;
            }
            let mut row = std::mem::take(&mut matrix.rows_mut()[index]);
            resident -= row.nonzeros();
            row.subtract_scaled(matrix.row(pivot_index), &factor, &mut scratch);
            statistics.row_operations += 1;
            resident += row.nonzeros();
            statistics.peak_nonzeros = statistics.peak_nonzeros.max(resident);
            matrix.rows_mut()[index] = row;
        }
    }

    matrix.sort_rows_by_leading_column();
    statistics.final_nonzeros = resident;
    debug_assert_eq!(statistics.final_nonzeros, matrix.nonzeros());
    (statistics, rows_examined)
}

#[cfg(test)]
mod tests {
    use super::{
        reduced_row_echelon, reduced_row_echelon_counting_rows, row_echelon, row_echelon_within,
        EliminationStatistics,
    };
    use crate::{
        fields::{Zp13, Zp2147483647, Zp541, Zp7},
        linalg::{gauss_jordan_elimination, sparse::SparseMatrix, sparse::SparseRow, Matrix},
        FiniteField, One, Zero,
    };
    use rand::{prelude::StdRng, Rng, SeedableRng};

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

    /// Every nonzero row of an echelon form is monic and owns its leading column exclusively.
    fn assert_is_row_echelon<G: FiniteField>(matrix: &SparseMatrix<G>) {
        let mut seen: Vec<usize> = Vec::new();
        for row in matrix.rows() {
            let Some(column) = row.leading_column() else {
                continue;
            };
            assert_eq!(
                row.leading_coefficient(),
                Some(G::ONE),
                "pivot in column {} is not one",
                column
            );
            assert!(
                !seen.contains(&column),
                "column {} holds two pivots",
                column
            );
            seen.push(column);
        }
        // A pivot column is zero in every row below its pivot. After sorting, "below" is "later".
        let mut sorted = matrix.clone();
        sorted.sort_rows_by_leading_column();
        for (i, row) in sorted.rows().iter().enumerate() {
            let Some(column) = row.leading_column() else {
                continue;
            };
            for lower in &sorted.rows()[(i + 1)..] {
                assert!(
                    lower.coefficient(column).is_zero(),
                    "column {} is nonzero below its pivot",
                    column
                );
            }
        }
    }

    /// The zero matrix is its own echelon form, with rank zero.
    #[test]
    fn test_all_zero_matrix() {
        let mut matrix = SparseMatrix::<F>::zero(3, 4);
        let statistics = row_echelon(&mut matrix);
        assert_eq!(
            statistics,
            EliminationStatistics {
                rank: 0,
                zero_rows: 3,
                initial_nonzeros: 0,
                final_nonzeros: 0,
                peak_nonzeros: 0,
                row_operations: 0,
                pivot_inversions: 0,
            }
        );
        assert_eq!(matrix, SparseMatrix::zero(3, 4));
    }

    /// A matrix with no rows or no columns reduces trivially.
    #[test]
    fn test_degenerate_dimensions() {
        for (rows, columns) in [(0usize, 0usize), (0, 5), (3, 0)] {
            let mut matrix = SparseMatrix::<F>::zero(rows, columns);
            let statistics = row_echelon(&mut matrix);
            assert_eq!(statistics.rank, 0, "{}x{}", rows, columns);
            assert_eq!(statistics.zero_rows, rows, "{}x{}", rows, columns);
        }
    }

    /// The identity matrix is already reduced, and needs no inverses.
    #[test]
    fn test_identity_is_a_fixed_point() {
        let dense = Matrix::<F>::identity(5);
        let mut matrix = SparseMatrix::from_dense(&dense);
        let statistics = row_echelon(&mut matrix);
        assert_eq!(statistics.rank, 5);
        assert_eq!(statistics.row_operations, 0);
        assert_eq!(statistics.pivot_inversions, 0, "pivots are already one");
        assert_eq!(matrix.to_dense(), dense);
    }

    /// A diagonal matrix needs one inverse per non-unit pivot and no row operations.
    #[test]
    fn test_diagonal_matrix() {
        let dense = Matrix::<F>::from_diag(&[F::new(2), F::ONE, F::new(5)]);
        let mut matrix = SparseMatrix::from_dense(&dense);
        let statistics = row_echelon(&mut matrix);
        assert_eq!(statistics.rank, 3);
        assert_eq!(statistics.row_operations, 0);
        assert_eq!(statistics.pivot_inversions, 2, "one pivot was already one");
        assert_eq!(matrix.to_dense(), Matrix::identity(3));
    }

    /// Duplicate rows are a rank-one dependency, and the duplicate reduces to zero.
    #[test]
    fn test_duplicate_rows_reduce_to_zero() {
        let mut matrix = matrix_of(
            &[&[(0, 1), (2, 3)], &[(0, 1), (2, 3)], &[(0, 2), (2, 6)]],
            3,
        );
        let statistics = row_echelon(&mut matrix);
        assert_eq!(statistics.rank, 1);
        assert_eq!(statistics.zero_rows, 2);
        assert_is_row_echelon(&matrix);
    }

    /// A linear dependency among distinct rows is found, not just an exact duplicate.
    #[test]
    fn test_linear_dependency_is_detected() {
        // r2 = r0 + r1, so the rank is two.
        let mut matrix = matrix_of(
            &[
                &[(0, 1), (1, 2)],
                &[(1, 3), (2, 4)],
                &[(0, 1), (1, 5), (2, 4)],
            ],
            3,
        );
        let statistics = row_echelon(&mut matrix);
        assert_eq!(statistics.rank, 2);
        assert_eq!(statistics.zero_rows, 1);
        assert_is_row_echelon(&matrix);
    }

    /// Rows with disjoint supports are already independent and need no row operations.
    #[test]
    fn test_disjoint_supports_need_no_work() {
        let mut matrix = matrix_of(&[&[(0, 1)], &[(5, 1)], &[(9, 1)]], 10);
        let statistics = row_echelon(&mut matrix);
        assert_eq!(statistics.rank, 3);
        assert_eq!(statistics.row_operations, 0);
        assert_eq!(statistics.initial_nonzeros, 3);
        assert_eq!(statistics.final_nonzeros, 3);
        assert_eq!(statistics.peak_nonzeros, 3);
    }

    /// A column with no entry simply has no pivot, and later columns still do.
    #[test]
    fn test_zero_column_has_no_pivot() {
        // Column 1 is empty throughout.
        let mut matrix = matrix_of(&[&[(0, 1), (2, 2)], &[(2, 3)]], 3);
        row_echelon(&mut matrix);
        assert_is_row_echelon(&matrix);
        let leading: Vec<Option<usize>> = matrix
            .rows()
            .iter()
            .map(|row| row.leading_column())
            .collect();
        assert_eq!(leading, vec![Some(0), Some(2)]);
    }

    /// More rows than columns forces dependencies; more columns than rows leaves free columns.
    #[test]
    fn test_rectangular_matrices() {
        // 4 rows, 2 columns: rank at most two.
        let mut tall = matrix_of(
            &[&[(0, 1), (1, 1)], &[(0, 1)], &[(1, 1)], &[(0, 3), (1, 7)]],
            2,
        );
        let statistics = row_echelon(&mut tall);
        assert_eq!(statistics.rank, 2);
        assert_eq!(statistics.zero_rows, 2);
        assert_is_row_echelon(&tall);

        // 2 rows, 5 columns: rank two, three free columns.
        let mut wide = matrix_of(&[&[(0, 2), (4, 1)], &[(1, 3), (3, 5)]], 5);
        let statistics = row_echelon(&mut wide);
        assert_eq!(statistics.rank, 2);
        assert_eq!(statistics.zero_rows, 0);
        assert_is_row_echelon(&wide);
    }

    /// Elimination fills in: the result can hold far more entries than the input.
    ///
    /// The first row is dense and every other row has two entries sharing column zero, so
    /// clearing column zero copies the dense row's tail into each of them: a two-entry row becomes
    /// a fourteen-entry row. This is the case that makes a sparse representation lose to a dense
    /// one, so the statistics have to show it rather than report the input's sparsity.
    #[test]
    fn test_fill_in_is_measured() {
        let width = 16;
        let mut rows: Vec<SparseRow<F>> = vec![SparseRow::new(
            &(0..width).map(|c| (c, F::ONE)).collect::<Vec<_>>(),
        )];
        rows.extend((1..width).map(|i| SparseRow::new(&[(0, F::ONE), (i, F::ONE)])));

        let mut matrix = SparseMatrix::new(width, rows);
        let initial = matrix.nonzeros();
        assert_eq!(initial, width + 2 * (width - 1));

        let statistics = row_echelon(&mut matrix);
        assert_eq!(statistics.initial_nonzeros, initial);
        assert!(
            statistics.peak_nonzeros > statistics.initial_nonzeros,
            "expected fill-in, got {:?}",
            statistics
        );
        assert!(
            statistics.peak_nonzeros >= statistics.final_nonzeros,
            "the peak cannot be below the final count: {:?}",
            statistics
        );
        assert_is_row_echelon(&matrix);
    }

    /// The reduced form agrees with the dense Gauss-Jordan implementation, entry for entry.
    ///
    /// The dense implementation is independently tested against Sage, so it is the oracle here.
    /// Reduced row echelon form is unique for a given row space, so this is an equality and not
    /// merely a consistency check.
    fn assert_agrees_with_dense<G: FiniteField>(matrix: &SparseMatrix<G>) {
        let dense_reduced = gauss_jordan_elimination(&matrix.to_dense());

        let mut sparse = matrix.clone();
        let statistics = reduced_row_echelon(&mut sparse);

        assert_eq!(
            sparse.to_dense(),
            dense_reduced,
            "sparse and dense reduced forms differ"
        );
        assert_eq!(
            statistics.rank,
            matrix.to_dense().rank(),
            "rank disagrees with the dense implementation"
        );
    }

    /// Hand-written cases, including rank-deficient and rectangular ones, agree with dense.
    #[test]
    fn test_agrees_with_dense_on_hand_written_cases() {
        type Case<'a> = (Vec<&'a [(usize, u64)]>, usize);
        let cases: Vec<Case> = vec![
            (vec![&[(0, 1)]], 1),
            (vec![&[(0, 1), (1, 2), (2, 3)]], 3),
            (vec![&[(0, 1), (1, 2)], &[(0, 3), (1, 4)]], 2),
            // Singular.
            (vec![&[(0, 1), (1, 2)], &[(0, 2), (1, 4)]], 2),
            // The Sage example from the dense tests, over GF(13) instead.
            (
                vec![
                    &[(0, 1), (1, 2), (2, 3)],
                    &[(0, 4), (1, 5), (2, 6)],
                    &[(0, 7), (1, 8), (2, 9)],
                ],
                3,
            ),
            // A zero row in the middle.
            (vec![&[(0, 1), (2, 1)], &[], &[(1, 1)]], 3),
            // Pivot not in the first column of the first row.
            (vec![&[(2, 5)], &[(0, 1), (2, 1)]], 3),
            // Wide and tall.
            (vec![&[(0, 1), (4, 7)], &[(2, 3)]], 6),
            (vec![&[(0, 1)], &[(0, 2)], &[(0, 3)], &[(0, 4)]], 1),
        ];

        for (rows, columns) in cases {
            let matrix = matrix_of(&rows, columns);
            assert_agrees_with_dense(&matrix);
        }
    }

    /// Random sparse matrices agree with dense elimination over several fields and densities.
    #[test]
    fn test_agrees_with_dense_on_random_matrices() {
        fn check<G: FiniteField>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            for (rows, columns) in [(4usize, 4usize), (6, 4), (4, 6), (8, 8), (12, 7)] {
                for density in [0.1f64, 0.3, 0.6, 1.0] {
                    let sparse_rows: Vec<SparseRow<G>> = (0..rows)
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
                    assert_agrees_with_dense(&SparseMatrix::new(columns, sparse_rows));
                }
            }
        }

        // A characteristic small enough that random coefficients collide often, a middling one,
        // and the 31-bit prime the benchmarks use.
        check::<Zp7>(1);
        check::<Zp13>(2);
        check::<Zp541>(3);
        check::<Zp2147483647>(4);
    }

    /// Reducing an already reduced matrix changes nothing.
    #[test]
    fn test_reduced_row_echelon_is_idempotent() {
        let mut matrix = matrix_of(
            &[
                &[(0, 2), (1, 4), (2, 6)],
                &[(0, 1), (1, 3), (2, 5)],
                &[(0, 7), (1, 8), (2, 9)],
            ],
            3,
        );
        reduced_row_echelon(&mut matrix);
        let once = matrix.clone();
        reduced_row_echelon(&mut matrix);
        assert_eq!(matrix, once);
    }

    /// In reduced form, a pivot column holds exactly one nonzero entry.
    #[test]
    fn test_reduced_form_isolates_pivot_columns() {
        let mut matrix = matrix_of(
            &[
                &[(0, 1), (1, 1), (3, 2)],
                &[(1, 1), (2, 1)],
                &[(0, 1), (2, 5), (3, 1)],
            ],
            4,
        );
        reduced_row_echelon(&mut matrix);

        for row in matrix.rows() {
            let Some(pivot) = row.leading_column() else {
                continue;
            };
            let occupied = matrix
                .rows()
                .iter()
                .filter(|other| !other.coefficient(pivot).is_zero())
                .count();
            assert_eq!(occupied, 1, "pivot column {} is not isolated", pivot);
        }
    }

    /// The back-substitution pass as it stood before the column index: every row probed for every
    /// pivot column.
    ///
    /// The oracle for the differential test below, kept as a transcription of the original so that
    /// "the two agree" is a statement about the optimization rather than about a reimplementation.
    /// Returns the same statistics plus the rows it examined, which is `rank * (num_rows - 1)` by
    /// construction and is the figure the indexed pass has to beat.
    fn probing_reduced_row_echelon<G: FiniteField>(
        matrix: &mut SparseMatrix<G>,
    ) -> (EliminationStatistics, usize) {
        let mut statistics = row_echelon(matrix);
        let mut scratch: Vec<(usize, G)> = Vec::new();
        let mut resident = statistics.final_nonzeros;
        let mut rows_examined = 0usize;

        let mut pivots: Vec<(usize, usize)> = (0..matrix.num_rows())
            .filter_map(|index| matrix.row(index).leading_column().map(|c| (c, index)))
            .collect();
        pivots.sort_unstable();

        for &(column, pivot_index) in pivots.iter().rev() {
            for index in 0..matrix.num_rows() {
                if index == pivot_index {
                    continue;
                }
                rows_examined += 1;
                let factor = matrix.row(index).coefficient(column);
                if factor.is_zero() {
                    continue;
                }
                let mut row = std::mem::take(&mut matrix.rows_mut()[index]);
                resident -= row.nonzeros();
                row.subtract_scaled(matrix.row(pivot_index), &factor, &mut scratch);
                statistics.row_operations += 1;
                resident += row.nonzeros();
                statistics.peak_nonzeros = statistics.peak_nonzeros.max(resident);
                matrix.rows_mut()[index] = row;
            }
        }

        matrix.sort_rows_by_leading_column();
        statistics.final_nonzeros = resident;
        (statistics, rows_examined)
    }

    /// The pivot columns of an echelon form, and the `(column, row)` incidences they hold.
    fn pivot_column_incidences<G: FiniteField>(matrix: &SparseMatrix<G>) -> (usize, usize) {
        let mut pivot_columns: Vec<usize> = matrix
            .rows()
            .iter()
            .filter_map(|row| row.leading_column())
            .collect();
        pivot_columns.sort_unstable();
        let incidences = matrix
            .rows()
            .iter()
            .map(|row| {
                row.entries()
                    .iter()
                    .filter(|(column, _)| pivot_columns.binary_search(column).is_ok())
                    .count()
            })
            .sum();
        (pivot_columns.len(), incidences)
    }

    /// Reduced forms pin to known matrices: rank deficiency, interleaved zero rows, duplicate
    /// leading columns, a free column, and entries on both sides of a pivot.
    #[test]
    fn test_reduced_row_echelon_pins_known_forms() {
        // Every row a multiple of (1, 2), with an empty row in the middle: rank one, three zero
        // rows, and three input rows leading with the same column.
        let mut rank_one = matrix_of(&[&[(0, 1), (1, 2)], &[(0, 2), (1, 4)], &[], &[(0, 3), (1, 6)]], 2);
        reduced_row_echelon(&mut rank_one);
        assert_eq!(
            rank_one,
            matrix_of(&[&[(0, 1), (1, 2)], &[], &[], &[]], 2),
            "rank-deficient form"
        );

        // x1 + x2, x0 + x2, x0 + x1 over GF(13): the determinant is 2, so the form is the identity.
        // Every row holds an entry in a pivot column other than its own, on both sides of it.
        let mut full_rank = matrix_of(&[&[(1, 1), (2, 1)], &[(0, 1), (2, 1)], &[(0, 1), (1, 1)]], 3);
        reduced_row_echelon(&mut full_rank);
        assert_eq!(
            full_rank,
            matrix_of(&[&[(0, 1)], &[(1, 1)], &[(2, 1)]], 3),
            "full-rank form"
        );

        // Column 1 is free, and column 3's pivot sits to the right of two rows that hold it.
        let mut with_free_column = matrix_of(
            &[
                &[(0, 1), (1, 2), (3, 3)],
                &[(0, 2), (1, 4), (3, 1)],
                &[(2, 1), (3, 5)],
            ],
            4,
        );
        reduced_row_echelon(&mut with_free_column);
        assert_eq!(
            with_free_column,
            matrix_of(&[&[(0, 1), (1, 2)], &[(2, 1)], &[(3, 1)]], 4),
            "form with a free column"
        );
    }

    /// Clearing a pivot column changes no column to its left, and no pivot column's entry set
    /// changes before the right-to-left pass reaches it.
    ///
    /// This is the invariant that lets the column index be built once instead of maintained: a
    /// pivot row's entries all lie at or right of its own leading column, so subtracting it cannot
    /// reach further left. The test performs the pass itself so it can look between the pivots.
    #[test]
    fn test_clearing_a_pivot_column_leaves_columns_to_its_left_alone() {
        // Fill-in heavy: a dense row plus rows sharing column zero, so clearing pivots rewrites
        // most of the matrix rather than nothing.
        let width = 24;
        let mut rng = StdRng::seed_from_u64(168);
        let mut rows: Vec<SparseRow<F>> = vec![SparseRow::new(
            &(0..width).map(|c| (c, F::new(1 + c as u64 % 12))).collect::<Vec<_>>(),
        )];
        rows.extend((0..width).map(|_| {
            let mut entries: Vec<(usize, F)> = Vec::new();
            for column in 0..width {
                if rng.gen_bool(0.35) {
                    entries.push((column, F::random(&mut rng)));
                }
            }
            SparseRow::new(&entries)
        }));
        let mut matrix = SparseMatrix::new(width, rows);
        row_echelon(&mut matrix);

        let mut pivots: Vec<(usize, usize)> = (0..matrix.num_rows())
            .filter_map(|index| matrix.row(index).leading_column().map(|c| (c, index)))
            .collect();
        pivots.sort_unstable();
        assert!(pivots.len() > 1, "the case needs several pivots");

        let rows_holding = |matrix: &SparseMatrix<F>, column: usize| -> Vec<usize> {
            (0..matrix.num_rows())
                .filter(|&index| !matrix.row(index).coefficient(column).is_zero())
                .collect()
        };
        let entries_left_of = |matrix: &SparseMatrix<F>, column: usize| -> Vec<Vec<(usize, F)>> {
            matrix
                .rows()
                .iter()
                .map(|row| {
                    row.entries()
                        .iter()
                        .copied()
                        .filter(|(c, _)| *c < column)
                        .collect()
                })
                .collect()
        };

        // The entry sets as the echelon pass left them, before any back-substitution.
        let initial: Vec<Vec<usize>> = pivots
            .iter()
            .map(|&(column, _)| rows_holding(&matrix, column))
            .collect();

        let mut scratch: Vec<(usize, F)> = Vec::new();
        let mut cleared_something = false;
        for (slot, &(column, pivot_index)) in pivots.iter().enumerate().rev() {
            assert_eq!(
                rows_holding(&matrix, column),
                initial[slot],
                "pivot column {} gained or lost an entry before the pass reached it",
                column
            );
            let left_before = entries_left_of(&matrix, column);

            for index in 0..matrix.num_rows() {
                if index == pivot_index {
                    continue;
                }
                let factor = matrix.row(index).coefficient(column);
                if factor.is_zero() {
                    continue;
                }
                cleared_something = true;
                let mut row = std::mem::take(&mut matrix.rows_mut()[index]);
                row.subtract_scaled(matrix.row(pivot_index), &factor, &mut scratch);
                matrix.rows_mut()[index] = row;
            }

            assert_eq!(
                entries_left_of(&matrix, column),
                left_before,
                "clearing column {} changed a column to its left",
                column
            );
        }
        assert!(cleared_something, "the case cleared no pivot column at all");
    }

    /// Back-substitution examines only the rows that hold a pivot-column entry, not every row.
    ///
    /// A block-diagonal matrix: full rank, but each pivot column holds entries in at most two
    /// rows, so the pass has a few hundred rows to examine rather than `rank * (num_rows - 1)`.
    #[test]
    fn test_back_substitution_is_output_sensitive() {
        let blocks = 64;
        let width = 2 * blocks;
        let rows: Vec<SparseRow<F>> = (0..blocks)
            .flat_map(|block| {
                let (a, b) = (2 * block, 2 * block + 1);
                [
                    SparseRow::new(&[(a, F::new(1)), (b, F::new(2))]),
                    SparseRow::new(&[(a, F::new(3)), (b, F::new(4))]),
                ]
            })
            .collect();
        let matrix = SparseMatrix::new(width, rows);

        // The incidences present once the echelon pass is done, which is the pass's input.
        let mut echelon = matrix.clone();
        row_echelon(&mut echelon);
        let (rank, incidences) = pivot_column_incidences(&echelon);
        assert_eq!(rank, width, "the blocks are all nonsingular");

        let mut indexed = matrix.clone();
        let (_, examined) = reduced_row_echelon_counting_rows(&mut indexed);

        // Every pivot column's own pivot row is skipped, so the bound is exact.
        assert_eq!(
            examined,
            incidences - rank,
            "the pass examined rows it had no entry for"
        );

        let mut probed = matrix.clone();
        let (_, probed_examined) = probing_reduced_row_echelon(&mut probed);
        assert_eq!(probed_examined, rank * (matrix.num_rows() - 1));
        assert!(
            examined * 8 < probed_examined,
            "examined {} rows against the probing pass's {}",
            examined,
            probed_examined
        );
    }

    /// The indexed pass reproduces the probing pass exactly — matrix and statistics — across
    /// densities, shapes, and characteristics.
    #[test]
    fn test_column_index_matches_the_probing_pass_on_random_matrices() {
        fn check<G: FiniteField>(seed: u64) {
            let mut rng = StdRng::seed_from_u64(seed);
            for (rows, columns) in [
                (1usize, 1usize),
                (8, 8),
                (16, 9),
                (9, 16),
                (24, 24),
                (32, 11),
            ] {
                for density in [0.0f64, 0.02, 0.1, 0.3, 0.6, 1.0] {
                    let sparse_rows: Vec<SparseRow<G>> = (0..rows)
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
                    let matrix = SparseMatrix::new(columns, sparse_rows);

                    let mut indexed = matrix.clone();
                    let indexed_statistics = reduced_row_echelon(&mut indexed);
                    let mut probed = matrix.clone();
                    let (probed_statistics, _) = probing_reduced_row_echelon(&mut probed);

                    assert_eq!(
                        indexed, probed,
                        "{}x{} at {} differ as matrices",
                        rows, columns, density
                    );
                    assert_eq!(
                        indexed_statistics, probed_statistics,
                        "{}x{} at {} differ in statistics",
                        rows, columns, density
                    );
                }
            }
        }

        check::<Zp7>(1681);
        check::<Zp13>(1682);
        check::<Zp541>(1683);
        check::<Zp2147483647>(1684);
    }

    /// Elimination preserves the row space, certified by the transformation it performs.
    ///
    /// The matrix is augmented with an identity block, so each reduced row carries the combination
    /// of original rows that produced it. Multiplying that combination back out must reproduce the
    /// row, which shows the reduced rows lie in the original row space; equal ranks then give
    /// equality of the two spaces.
    #[test]
    fn test_row_space_is_preserved() {
        let rows: Vec<&[(usize, u64)]> = vec![
            &[(0, 1), (1, 2), (2, 3)],
            &[(0, 4), (1, 5), (2, 6)],
            &[(0, 7), (1, 8), (2, 9)],
            &[(0, 1), (2, 1)],
        ];
        let original = matrix_of(&rows, 3);

        // [ A | I ], so columns 3.. record the row operations applied.
        let augmented_rows: Vec<SparseRow<F>> = original
            .rows()
            .iter()
            .enumerate()
            .map(|(index, row)| {
                let mut entries: Vec<(usize, F)> = row.entries().to_vec();
                entries.push((3 + index, F::ONE));
                SparseRow::from_sorted_unchecked(entries)
            })
            .collect();
        let mut augmented = SparseMatrix::new(3 + original.num_rows(), augmented_rows);
        reduced_row_echelon(&mut augmented);

        for row in augmented.rows() {
            // Split the row back into its matrix part and its certificate.
            let left: Vec<(usize, F)> = row
                .entries()
                .iter()
                .filter(|(column, _)| *column < 3)
                .copied()
                .collect();
            let combination: Vec<(usize, F)> = row
                .entries()
                .iter()
                .filter(|(column, _)| *column >= 3)
                .map(|(column, coefficient)| (column - 3, *coefficient))
                .collect();

            // Sum of coefficient * original row, which must equal the reduced row.
            let mut rebuilt: Vec<(usize, F)> = Vec::new();
            for (index, coefficient) in &combination {
                for (column, entry) in original.row(*index).entries() {
                    rebuilt.push((*column, *coefficient * *entry));
                }
            }
            assert_eq!(
                SparseRow::new(&rebuilt),
                SparseRow::from_sorted_unchecked(left),
                "a reduced row is not the combination of originals its certificate claims"
            );
        }
    }

    /// Elimination is deterministic: identical input gives an identical result, every run.
    #[test]
    fn test_elimination_is_deterministic() {
        let mut rng = StdRng::seed_from_u64(11);
        let rows: Vec<SparseRow<F>> = (0..10)
            .map(|_| {
                let mut entries: Vec<(usize, F)> = Vec::new();
                for column in 0..12 {
                    if rng.gen_bool(0.4) {
                        entries.push((column, F::random(&mut rng)));
                    }
                }
                SparseRow::new(&entries)
            })
            .collect();
        let matrix = SparseMatrix::new(12, rows);

        let mut first = matrix.clone();
        let first_statistics = row_echelon(&mut first);
        for _ in 0..8 {
            let mut again = matrix.clone();
            let statistics = row_echelon(&mut again);
            assert_eq!(again, first);
            assert_eq!(statistics, first_statistics);
        }
    }

    /// A budget large enough to cover the peak behaves exactly as the unbounded elimination.
    #[test]
    fn test_budget_that_is_never_reached() {
        let mut bounded = matrix_of(
            &[
                &[(0, 1), (1, 2), (2, 3)],
                &[(0, 4), (1, 5), (2, 6)],
                &[(0, 7), (1, 8), (2, 9)],
            ],
            3,
        );
        let mut unbounded = bounded.clone();

        let statistics = row_echelon_within(&mut bounded, 1000).expect("budget not reached");
        assert_eq!(statistics, row_echelon(&mut unbounded));
        assert_eq!(bounded, unbounded);
    }

    /// A budget below the peak abandons the elimination and reports the count that crossed it.
    #[test]
    fn test_budget_that_is_exceeded() {
        // The fill-in matrix: a dense first row makes each two-entry row fourteen entries.
        let width = 16;
        let mut rows: Vec<SparseRow<F>> = vec![SparseRow::new(
            &(0..width).map(|c| (c, F::ONE)).collect::<Vec<_>>(),
        )];
        rows.extend((1..width).map(|i| SparseRow::new(&[(0, F::ONE), (i, F::ONE)])));
        let matrix = SparseMatrix::new(width, rows);

        let unbounded = row_echelon(&mut matrix.clone());
        assert!(unbounded.peak_nonzeros > matrix.nonzeros());

        // A budget just under the peak must stop, and report at least the budget.
        let mut bounded = matrix.clone();
        let observed = row_echelon_within(&mut bounded, unbounded.peak_nonzeros - 1)
            .expect_err("the budget should have been exceeded");
        assert!(
            observed > unbounded.peak_nonzeros - 1,
            "reported {} for a budget of {}",
            observed,
            unbounded.peak_nonzeros - 1
        );

        // A budget below even the input is rejected before any work is done.
        let mut tiny = matrix.clone();
        assert_eq!(
            row_echelon_within(&mut tiny, matrix.nonzeros() - 1),
            Err(matrix.nonzeros())
        );
        assert_eq!(tiny, matrix, "no work should have been done");
    }

    /// Rank is computed over the field in question, not over the integers.
    ///
    /// The diagonal (1, 7, 13) has full rank over the integers, rank two over GF(7) and over
    /// GF(13) — a different row vanishing in each — and full rank over GF(541). A test over one
    /// field alone would not distinguish arithmetic that ignored the modulus.
    #[test]
    fn test_rank_depends_on_the_characteristic() {
        fn rank_over<G: FiniteField>() -> usize {
            let mut matrix =
                SparseMatrix::from_dense(&Matrix::from_diag(&[G::ONE, G::new(7), G::new(13)]));
            row_echelon(&mut matrix).rank
        }

        assert_eq!(rank_over::<Zp7>(), 2, "7 vanishes over GF(7)");
        assert_eq!(rank_over::<Zp13>(), 2, "13 vanishes over GF(13)");
        assert_eq!(rank_over::<Zp541>(), 3);
        assert_eq!(rank_over::<Zp2147483647>(), 3);
    }
}
