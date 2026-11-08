//! The elimination interface F4 calls, and the backends that implement it.
//!
//! Two functions, and the choice of representation is a parameter rather than a call site. That
//! separation exists so that a caller which knows something about the *structure* of its matrix —
//! which rows are already pivots, which are the work — and a backend which knows something about
//! its *density* can be developed independently of each other.
//!
//! [`Backend::Sparse`] is the implementation from the preceding milestone and the reference every
//! other backend is checked against. Every backend runs the *same* algorithm — leftmost nonzero
//! column, first row to reach it, unit pivot, one inverse per pivot — so all three agree on the
//! resulting matrix and on every counter in [`EliminationStatistics`], and a comparison between
//! them measures storage and nothing else.
//!
//! `linalg` does not depend on `grobner`, and does not learn to. [`Backend`] is this module's own
//! type; F4 holds one in its options.
//!
//! **Black-box methods — Wiedemann, block Wiedemann, Krylov — are a recorded won't-do here**, not a
//! cost question: the output of this elimination *is* the transformed matrix and its rank defect,
//! so there is no vector to solve for. `docs/research/wiedemann-krylov.md` §1 has the argument and
//! the measurements; do not re-derive it.

use crate::{
    linalg::{
        dense::{
            accumulated_reduce_rows_against_pivots, accumulated_row_echelon,
            dense_reduce_rows_against_pivots, dense_row_echelon,
        },
        sparse::{row_echelon_within, EliminationStatistics, SparseMatrix, SparseRow},
        PivotIndex,
    },
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

    /// Dense rows throughout: the matrix is densified, eliminated, and sparsified again.
    ///
    /// Exists so that a sparse/dense comparison measures storage rather than algorithm. It also
    /// allocates `num_rows * num_columns` cells whatever the entry budget says, which is the one
    /// respect in which the two backends are not comparable — the budget counts entries, not
    /// bytes, and a dense backend's bytes are a property of the shape alone.
    Dense,

    /// Sparse rows, reduced through a dense accumulator.
    ///
    /// The matrix stays sparse and only the row being reduced is made dense, so a row operation
    /// costs the *pivot's* support rather than a sorted merge over both rows, and the buffer is one
    /// row wide for the whole elimination. The mixed representation is what "adaptive" names here:
    /// the choice is per role — pivot or work — rather than per matrix.
    ///
    /// Deliberately not keyed on a measured density, global or otherwise. §7.4 of
    /// `docs/MILESTONE-F4-OPTIMIZATION.md` reports the distributions: on every instance measured,
    /// no row and no 64x64 block ever exceeds 50% occupancy, so there is no threshold for a
    /// density-keyed policy to find and a policy keyed on *global* density would be keyed on the
    /// wrong quantity besides.
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
        Backend::Sparse => row_echelon_within(matrix, max_nonzeros),
        Backend::Dense => dense_row_echelon(matrix, max_nonzeros),
        Backend::Adaptive => accumulated_row_echelon(matrix, max_nonzeros),
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

    // Validated once, here, rather than once per backend: the preconditions are the interface's,
    // not a representation's, and a second copy of them is a second chance to drift.
    let mut pivot_of_column = upper_block_pivots(matrix, split, &mut statistics);

    match backend {
        Backend::Sparse => sparse_reduce_rows_against_pivots(
            matrix,
            split,
            &mut pivot_of_column,
            &mut statistics,
            max_nonzeros,
        )?,
        Backend::Dense => dense_reduce_rows_against_pivots(
            matrix,
            split,
            &mut pivot_of_column,
            &mut statistics,
            max_nonzeros,
        )?,
        Backend::Adaptive => accumulated_reduce_rows_against_pivots(
            matrix,
            split,
            &mut pivot_of_column,
            &mut statistics,
            max_nonzeros,
        )?,
    }

    debug_assert_eq!(statistics.final_nonzeros, matrix.nonzeros());
    debug_assert_eq!(statistics.rank, matrix.nonzero_rows());
    debug_assert_eq!(statistics.rank + statistics.zero_rows, matrix.num_rows());
    Ok(statistics)
}

/// The pivot map rows `[..split]` declare, with the preconditions enforced.
///
/// Checked rather than trusted: a duplicated leading column would silently drop one of the two
/// relations, which is the kind of wrong answer that looks like a correct one.
///
/// # Panics
/// If two upper rows lead with the same column, or if an upper row is not normalized.
fn upper_block_pivots<F: FiniteField>(
    matrix: &SparseMatrix<F>,
    split: usize,
    statistics: &mut EliminationStatistics,
) -> PivotIndex {
    let mut pivot_of_column = PivotIndex::new(matrix.num_columns(), matrix.num_rows());
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
    pivot_of_column
}

/// [`reduce_rows_against_pivots_with`] over sorted-vector sparse rows.
fn sparse_reduce_rows_against_pivots<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    split: usize,
    pivot_of_column: &mut PivotIndex,
    statistics: &mut EliminationStatistics,
    max_nonzeros: usize,
) -> Result<(), usize> {
    // Nonzero entries held by the rows still in the matrix; the row being worked on is taken out.
    let mut resident = statistics.initial_nonzeros;
    let mut scratch: Vec<(usize, F)> = Vec::new();

    for index in split..matrix.num_rows() {
        let mut row = std::mem::take(&mut matrix.rows_mut()[index]);
        resident -= row.nonzeros();

        while let Some(column) = row.leading_column() {
            match pivot_of_column.pivot_of(column) {
                Some(pivot_index) => {
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
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{reduce_rows_against_pivots_with, row_echelon_with, Backend};
    use crate::{
        fields::{Gf256, Zp13, Zp18446744073709551557, Zp2, Zp2147483647, Zp541, Zp7},
        linalg::sparse::{
            reduced_row_echelon, row_echelon, EliminationStatistics, SparseMatrix, SparseRow,
        },
        FiniteField, One,
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

    /// The shapes a sparse/dense comparison has to cover, named so a failure says which one.
    ///
    /// Rectangular both ways, square, singular, rank-deficient by duplication, nearly empty,
    /// completely full, and the fill-in case where a dense first row turns every two-entry row
    /// into a full one — which is the shape that is supposed to favour dense storage.
    fn comparison_cases<G: FiniteField>() -> Vec<(String, SparseMatrix<G>)> {
        let mut cases: Vec<(String, SparseMatrix<G>)> = Vec::new();

        for (rows, columns, density) in [
            (12usize, 12usize, 0.3f64), // square
            (24, 8, 0.4),               // tall
            (8, 40, 0.3),               // wide
            (16, 16, 0.02),             // sparse
            (10, 10, 1.0),              // dense
        ] {
            cases.push((
                format!("{}x{} at {}", rows, columns, density),
                random_matrix(rows, columns, density, 17),
            ));
        }

        // Singular: a square matrix whose last row is the sum of the first two.
        let mut rows: Vec<SparseRow<G>> = vec![
            SparseRow::new(&[(0, G::new(1)), (1, G::new(2)), (2, G::new(3))]),
            SparseRow::new(&[(0, G::new(4)), (1, G::new(5)), (2, G::new(6))]),
            SparseRow::new(&[(0, G::new(5)), (1, G::new(7)), (2, G::new(9))]),
        ];
        cases.push(("singular".to_string(), SparseMatrix::new(3, rows)));

        // Rank-deficient by duplication: every row a multiple of the first.
        rows = (1..=6)
            .map(|k| SparseRow::new(&[(0, G::new(k)), (3, G::new(2 * k))]))
            .collect();
        cases.push(("rank one".to_string(), SparseMatrix::new(4, rows)));

        // Fill-in heavy: a dense first row, then rows of two entries sharing column zero.
        let width = 24;
        rows = vec![SparseRow::new(
            &(0..width).map(|c| (c, G::new(1))).collect::<Vec<_>>(),
        )];
        rows.extend((1..width).map(|i| SparseRow::new(&[(0, G::new(1)), (i, G::new(1))])));
        cases.push(("fill-in".to_string(), SparseMatrix::new(width, rows)));

        // Degenerate shapes, which have caught off-by-ones in both representations.
        cases.push(("no rows".to_string(), SparseMatrix::zero(0, 7)));
        cases.push(("no columns".to_string(), SparseMatrix::zero(5, 0)));
        cases.push(("all zero".to_string(), SparseMatrix::zero(4, 6)));

        // One column: every row competes for the single pivot, so all but one reduce to zero.
        cases.push((
            "single column".to_string(),
            SparseMatrix::new(
                1,
                (1..=5)
                    .map(|k| SparseRow::new(&[(0, G::new(k))]))
                    .collect::<Vec<_>>(),
            ),
        ));

        cases
    }

    /// Every backend reproduces the sparse echelon and the dense rank, over five fields.
    ///
    /// Not merely the same rank and row space: the same pivot rule and the same normalization make
    /// the resulting matrix a function of the input alone, so a disagreement anywhere means one
    /// backend is running a different algorithm rather than a different representation.
    #[test]
    fn test_every_backend_agrees_on_every_shape_and_field() {
        fn check<G: FiniteField>(field: &str) {
            for (label, original) in comparison_cases::<G>() {
                let mut expected = original.clone();
                let reference = row_echelon(&mut expected);

                if original.num_rows() > 0 && original.num_columns() > 0 {
                    assert_eq!(
                        reference.rank,
                        original.to_dense().rank(),
                        "{}/{}: rank disagrees with the dense implementation",
                        field,
                        label
                    );
                }

                for backend in BACKENDS {
                    let mut actual = original.clone();
                    let statistics = row_echelon_with(backend, &mut actual, usize::MAX)
                        .expect("unbounded cannot fail");
                    assert_eq!(actual, expected, "{}/{}/{:?}", field, label, backend);
                    assert_eq!(statistics, reference, "{}/{}/{:?}", field, label, backend);
                }
            }
        }

        check::<Zp7>("GF(7)");
        check::<Zp13>("GF(13)");
        check::<Zp541>("GF(541)");
        check::<Zp2147483647>("GF(2^31-1)");
        check::<Zp18446744073709551557>("GF(2^64-59)");
        // Characteristic two, which until #218 nothing in `src/linalg/` reached: `Zp2`, `Gf256`
        // and `BinaryFieldElement` appeared nowhere under it, so of the three backends only
        // `Adaptive` had ever run at this characteristic — and only indirectly, because
        // `F4Options::default()` selects it. Two shapes of even characteristic, because they are
        // different code: `Zp2` keeps the wide-remainder path, since `2^32` is not invertible
        // modulo an even number, while `Gf256` is carry-less multiplication with a Barrett
        // reduction.
        //
        // The pivot rule is what makes this worth checking rather than assuming. Every nonzero
        // coefficient over `GF(2)` is one, so normalization never divides and `pivot_inversions`
        // stays zero; and `a + a = 0` makes cancellation far more frequent, which is the path on
        // which the backends maintain their nonzero counters separately.
        check::<Zp2>("GF(2)");
        check::<Gf256>("GF(2^8)");
    }

    /// Every backend's echelon rows lie in the original row space, certified by an identity block.
    ///
    /// `[A | I]` is eliminated, so each resulting row carries the combination of original rows that
    /// produced it. Multiplying that combination back out must reproduce the row, which puts the
    /// result inside the original row space; equal ranks then make the two spaces equal.
    #[test]
    fn test_every_backend_preserves_the_row_space() {
        let original: SparseMatrix<F> = random_matrix(9, 11, 0.4, 23);
        let width = original.num_columns();

        let augmented_rows: Vec<SparseRow<F>> = original
            .rows()
            .iter()
            .enumerate()
            .map(|(index, row)| {
                let mut entries: Vec<(usize, F)> = row.entries().to_vec();
                entries.push((width + index, F::ONE));
                SparseRow::from_sorted_unchecked(entries)
            })
            .collect();
        let augmented = SparseMatrix::new(width + original.num_rows(), augmented_rows);

        let reference_rank = {
            let mut matrix = original.clone();
            row_echelon(&mut matrix).rank
        };

        for backend in BACKENDS {
            let mut reduced = augmented.clone();
            let statistics =
                row_echelon_with(backend, &mut reduced, usize::MAX).expect("unbounded cannot fail");
            // The identity block makes every augmented row independent, so the rank is the row
            // count; the rank of the matrix part is what the certificate is checked against.
            assert_eq!(
                statistics.rank,
                original.num_rows(),
                "{:?}: an augmented row cannot vanish",
                backend
            );

            let mut nonzero_left = 0;
            for row in reduced.rows() {
                let left: Vec<(usize, F)> = row
                    .entries()
                    .iter()
                    .filter(|(column, _)| *column < width)
                    .copied()
                    .collect();
                let combination: Vec<(usize, F)> = row
                    .entries()
                    .iter()
                    .filter(|(column, _)| *column >= width)
                    .map(|(column, coefficient)| (column - width, *coefficient))
                    .collect();

                let mut rebuilt: Vec<(usize, F)> = Vec::new();
                for (index, coefficient) in &combination {
                    for (column, entry) in original.row(*index).entries() {
                        rebuilt.push((*column, *coefficient * *entry));
                    }
                }
                assert_eq!(
                    SparseRow::new(&rebuilt),
                    SparseRow::from_sorted_unchecked(left.clone()),
                    "{:?}: a row is not the combination its certificate claims",
                    backend
                );
                if !left.is_empty() {
                    nonzero_left += 1;
                }
            }
            assert_eq!(
                nonzero_left, reference_rank,
                "{:?}: the row space has a different dimension",
                backend
            );
        }
    }

    /// Every backend honours the split contract at zero, at the row count, and in between.
    ///
    /// The upper rows must be untouched, the lower rows reduced against them and normalized, and
    /// the whole result equal to a full echelon of the same arrangement — which is the strongest
    /// form of "the row space is unchanged" available, since the pivot rule makes the echelon form
    /// a function of the input.
    #[test]
    fn test_every_backend_honours_the_split_contract() {
        fn check<G: FiniteField>(field: &str) {
            for (rows, columns, density) in
                [(14usize, 18usize, 0.3f64), (20, 9, 0.5), (11, 11, 0.2)]
            {
                // An echelon arrangement, so that any prefix satisfies the precondition.
                let mut prepared: SparseMatrix<G> = random_matrix(rows, columns, density, 29);
                let _ = row_echelon(&mut prepared);
                prepared.sort_rows_by_leading_column();

                let mut full = prepared.clone();
                let expected_statistics = row_echelon(&mut full);

                for split in [0, prepared.num_rows() / 2, prepared.num_rows()] {
                    for backend in BACKENDS {
                        let mut actual = prepared.clone();
                        let statistics = reduce_rows_against_pivots_with(
                            backend,
                            &mut actual,
                            split,
                            usize::MAX,
                        )
                        .expect("unbounded cannot fail");

                        // The upper rows are left exactly where they were.
                        for index in 0..split {
                            assert_eq!(
                                actual.row(index),
                                prepared.row(index),
                                "{}/{:?}: upper row {} was rewritten at split {}",
                                field,
                                backend,
                                index,
                                split
                            );
                        }
                        assert_eq!(
                            actual, full,
                            "{}/{:?}: split {} disagrees with a full echelon",
                            field, backend, split
                        );
                        assert_eq!(
                            statistics, expected_statistics,
                            "{}/{:?}: split {} disagrees on the work",
                            field, backend, split
                        );
                    }
                }
            }
        }

        check::<Zp7>("GF(7)");
        check::<Zp13>("GF(13)");
        check::<Zp541>("GF(541)");
        check::<Zp2147483647>("GF(2^31-1)");
        check::<Zp18446744073709551557>("GF(2^64-59)");
        // The split contract at characteristic two as well (#218): an upper block whose pivots are
        // all one is exactly the case where "normalized" is free, so a backend could skip a step
        // and still look correct over an odd field.
        check::<Zp2>("GF(2)");
        check::<Gf256>("GF(2^8)");
    }

    /// Each backend is deterministic, and the adaptive one agrees with both fixed backends.
    ///
    /// Elimination over a finite field has no numerical stability to pivot for, so a backend that
    /// answered differently on a second run would be reading something other than its input.
    #[test]
    fn test_every_backend_is_deterministic() {
        let original: SparseMatrix<F> = random_matrix(18, 22, 0.35, 31);

        let mut results = Vec::new();
        for backend in BACKENDS {
            let mut first = original.clone();
            let first_statistics =
                row_echelon_with(backend, &mut first, usize::MAX).expect("unbounded cannot fail");
            for _ in 0..8 {
                let mut again = original.clone();
                let statistics = row_echelon_with(backend, &mut again, usize::MAX)
                    .expect("unbounded cannot fail");
                assert_eq!(again, first, "{:?} is not deterministic", backend);
                assert_eq!(
                    statistics, first_statistics,
                    "{:?} is not deterministic",
                    backend
                );
            }
            results.push((first, first_statistics));
        }

        for (index, backend) in BACKENDS.iter().enumerate().skip(1) {
            assert_eq!(results[index].0, results[0].0, "{:?}", backend);
            assert_eq!(results[index].1, results[0].1, "{:?}", backend);
        }
    }

    /// Every backend abandons the elimination when fill-in crosses the budget, mid-run.
    ///
    /// The budget has to refuse work while it is being consumed rather than report it afterwards,
    /// and a dense backend's live count has to mean what the sparse one's means — the number of
    /// field elements that are not zero — or the two budgets are not comparable.
    #[test]
    fn test_the_budget_is_enforced_mid_elimination() {
        // A dense first row makes each two-entry row a full one, so the peak is far above both the
        // input and the result.
        let width = 20;
        let mut rows: Vec<SparseRow<F>> = vec![SparseRow::new(
            &(0..width).map(|c| (c, F::ONE)).collect::<Vec<_>>(),
        )];
        rows.extend((1..width).map(|i| SparseRow::new(&[(0, F::ONE), (i, F::ONE)])));
        let original = SparseMatrix::new(width, rows);

        let unbounded = row_echelon(&mut original.clone());
        assert!(unbounded.peak_nonzeros > original.nonzeros(), "no fill-in");

        for backend in BACKENDS {
            let budget = unbounded.peak_nonzeros - 1;
            let mut matrix = original.clone();
            let observed = row_echelon_with(backend, &mut matrix, budget)
                .expect_err("the budget should have been exceeded");
            assert!(
                observed > budget,
                "{:?} reported {} for a budget of {}",
                backend,
                observed,
                budget
            );

            // The same budget is enough when it covers the peak exactly.
            let mut matrix = original.clone();
            let statistics = row_echelon_with(backend, &mut matrix, unbounded.peak_nonzeros)
                .expect("a budget at the peak is enough");
            assert_eq!(statistics, unbounded, "{:?}", backend);
        }
    }

    /// Every backend rejects a split beyond the row count.
    #[test]
    fn test_every_backend_rejects_a_split_beyond_the_row_count() {
        for backend in BACKENDS {
            let result = std::panic::catch_unwind(|| {
                let mut matrix = matrix_of(&[&[(0, 1)], &[(1, 1)], &[(2, 1)]], 3);
                let _ = reduce_rows_against_pivots_with(backend, &mut matrix, 5, usize::MAX);
            });
            assert!(
                result.is_err(),
                "{:?} accepted an impossible split",
                backend
            );
        }
    }

    /// FNV-1a over a matrix and the statistics its elimination reported.
    ///
    /// Hand-rolled rather than `DefaultHasher`, and over `Display` rather than a field's bytes, so
    /// that a digest recorded today still means the same thing under a later toolchain and a
    /// different internal representation. That is the whole point of the oracle: the recorded
    /// constants have to survive the refactors they exist to police.
    fn absorb(state: &mut u64, bytes: &[u8]) {
        for byte in bytes {
            *state ^= u64::from(*byte);
            *state = state.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }

    fn absorb_usize(state: &mut u64, value: usize) {
        absorb(state, &(value as u64).to_le_bytes());
    }

    fn absorb_result<G: FiniteField>(
        state: &mut u64,
        matrix: &SparseMatrix<G>,
        statistics: &EliminationStatistics,
    ) {
        absorb_usize(state, matrix.num_rows());
        absorb_usize(state, matrix.num_columns());
        for row in matrix.rows() {
            absorb_usize(state, row.nonzeros());
            for (column, coefficient) in row.entries() {
                absorb_usize(state, *column);
                absorb(state, format!("{}", coefficient).as_bytes());
            }
        }
        for field in [
            statistics.rank,
            statistics.zero_rows,
            statistics.initial_nonzeros,
            statistics.final_nonzeros,
            statistics.peak_nonzeros,
            statistics.row_operations,
            statistics.pivot_inversions,
        ] {
            absorb_usize(state, field);
        }
    }

    /// Every elimination path over the whole corpus, folded into one digest per path.
    ///
    /// Order: the corpus in `comparison_cases` order, over five fields, then for each case a full
    /// echelon, then the split path at a third and at two thirds of an echelon arrangement.
    fn path_digests() -> [u64; 5] {
        // [sparse, dense, adaptive, row_echelon, reduced_row_echelon]
        let mut digests = [0xcbf2_9ce4_8422_2325u64; 5];

        fn check<G: FiniteField>(digests: &mut [u64; 5]) {
            for (_, original) in comparison_cases::<G>() {
                for (slot, backend) in BACKENDS.iter().enumerate() {
                    let mut matrix = original.clone();
                    let statistics = row_echelon_with(*backend, &mut matrix, usize::MAX)
                        .expect("unbounded cannot fail");
                    absorb_result(&mut digests[slot], &matrix, &statistics);
                }

                let mut reference = original.clone();
                let statistics = row_echelon(&mut reference);
                absorb_result(&mut digests[3], &reference, &statistics);

                let mut reduced = original.clone();
                let statistics = reduced_row_echelon(&mut reduced);
                absorb_result(&mut digests[4], &reduced, &statistics);

                // An echelon arrangement, so that any prefix is a valid upper block.
                let mut prepared = original.clone();
                let _ = row_echelon(&mut prepared);
                prepared.sort_rows_by_leading_column();
                for divisor in [3, 2] {
                    let split = prepared.num_rows() / divisor;
                    for (slot, backend) in BACKENDS.iter().enumerate() {
                        let mut matrix = prepared.clone();
                        let statistics = reduce_rows_against_pivots_with(
                            *backend,
                            &mut matrix,
                            split,
                            usize::MAX,
                        )
                        .expect("unbounded cannot fail");
                        absorb_result(&mut digests[slot], &matrix, &statistics);
                    }
                }
            }
        }

        check::<Zp7>(&mut digests);
        check::<Zp13>(&mut digests);
        check::<Zp541>(&mut digests);
        check::<Zp2147483647>(&mut digests);
        check::<Zp18446744073709551557>(&mut digests);
        digests
    }

    /// Every elimination path reproduces the results and statistics recorded before #159.
    ///
    /// The cross-backend tests above compare the backends to each other, so a change that moved
    /// all of them together would pass every one of them. These constants were taken from the
    /// `HashMap<usize, usize>` implementation and are the only check that the indexed pivot store
    /// did not perturb a matrix, a rank, a row-operation count, or an inversion count anywhere in
    /// the corpus — degenerate shapes and five fields included.
    #[test]
    fn test_every_path_reproduces_the_pre_indexed_pivot_oracle() {
        assert_eq!(
            path_digests(),
            [
                0x9e6b_81f2_7b05_3b21,
                0x9e6b_81f2_7b05_3b21,
                0x9e6b_81f2_7b05_3b21,
                0x30c3_cba3_4ed1_1175,
                0x54bd_4ffb_bc2e_6995,
            ],
            "an elimination path no longer reproduces the pre-#159 results"
        );
    }

    /// Every backend rejects an upper block whose rows do not satisfy the precondition.
    #[test]
    fn test_every_backend_rejects_a_malformed_upper_block() {
        for backend in BACKENDS {
            // Two upper rows leading with the same column.
            let duplicated = std::panic::catch_unwind(|| {
                let mut matrix = matrix_of(&[&[(0, 1), (1, 2)], &[(0, 1), (2, 3)]], 3);
                let _ = reduce_rows_against_pivots_with(backend, &mut matrix, 2, usize::MAX);
            });
            assert!(
                duplicated.is_err(),
                "{:?} accepted duplicate upper pivots",
                backend
            );

            // An upper pivot that is not one.
            let unnormalized = std::panic::catch_unwind(|| {
                let mut matrix = matrix_of(&[&[(0, 3), (1, 2)], &[(1, 1)]], 3);
                let _ = reduce_rows_against_pivots_with(backend, &mut matrix, 1, usize::MAX);
            });
            assert!(
                unnormalized.is_err(),
                "{:?} accepted an unnormalized upper pivot",
                backend
            );
        }
    }
}
