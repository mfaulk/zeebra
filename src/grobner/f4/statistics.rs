//! Counters describing the work an F4 computation performed.
//!
//! Wall-clock time says a computation was slow; it does not say whether the matrices were large,
//! whether elimination filled them in, or how many of the rows were there only to make the
//! reduction possible. These are the numbers that attribute the cost, and they are plain counters,
//! so they belong in an example binary rather than in Criterion.

use crate::linalg::sparse::EliminationStatistics;

/// What one batch of critical pairs cost.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BatchStatistics {
    /// Pairs reduced in this batch, after the product criterion.
    pub pairs: usize,

    /// Rows in the Macaulay matrix.
    pub rows: usize,

    /// Of those, rows that are reducer multiples rather than halves of a critical pair.
    ///
    /// These are the rows symbolic preprocessing had to add to make the reduction possible. A high
    /// proportion means the batch spent most of its matrix on reduction scaffolding.
    pub reducer_rows: usize,

    /// Columns in the Macaulay matrix, i.e. distinct monomials across all rows.
    pub columns: usize,

    /// What the elimination did.
    pub elimination: EliminationStatistics,

    /// New basis elements extracted, i.e. rows whose leading monomial was new.
    pub candidates: usize,
}

/// What a whole F4 computation cost.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct F4Statistics {
    /// Pairs taken off the queue.
    pub pairs_considered: usize,

    /// Pairs discarded by Buchberger's first criterion, without reaching a matrix.
    pub pairs_eliminated_by_product_criterion: usize,

    /// Pairs that reached a matrix.
    pub pairs_reduced: usize,

    /// Batches reduced. A batch with every pair eliminated by the criterion is not counted.
    pub batches: usize,

    /// The largest batch, in pairs.
    pub max_pairs_per_batch: usize,

    /// Basis elements appended during the computation, before interreduction.
    pub elements_added: usize,

    /// Batches that produced no new basis element at all.
    ///
    /// The F4 analogue of Buchberger's zero reductions: the whole matrix reduced to relations the
    /// basis already implied. Buchberger pays one full reduction per such pair; F4 pays one matrix
    /// for all of them at once, which is the saving the algorithm exists for.
    pub empty_batches: usize,

    /// The largest lcm degree of any pair selected.
    pub max_pair_degree: u64,

    /// The largest number of rows in any matrix.
    pub max_matrix_rows: usize,

    /// The largest number of columns in any matrix.
    pub max_matrix_columns: usize,

    /// The largest number of nonzero entries live in any elimination.
    pub max_live_nonzeros: usize,

    /// Summed over every batch: nonzero entries in the matrices as built.
    pub total_initial_nonzeros: usize,

    /// Summed over every batch: nonzero entries after elimination.
    pub total_final_nonzeros: usize,

    /// Summed over every batch: row operations performed.
    pub row_operations: usize,

    /// Summed over every batch: modular inverses taken to normalize a pivot.
    pub pivot_inversions: usize,

    /// Summed over every batch: rows that reduced to zero.
    pub zero_rows: usize,

    /// Summed over every batch: reducer multiples added by symbolic preprocessing.
    pub reducer_rows: usize,

    /// The largest number of terms in any basis element produced.
    pub max_terms: usize,
}

impl F4Statistics {
    /// Fold one batch's counters into the totals.
    ///
    /// Public because [`super::reduce_batch`] is: a caller driving batches itself accumulates the
    /// same way the main loop does.
    pub fn record(&mut self, batch: &BatchStatistics) {
        self.batches += 1;
        self.max_pairs_per_batch = self.max_pairs_per_batch.max(batch.pairs);
        self.max_matrix_rows = self.max_matrix_rows.max(batch.rows);
        self.max_matrix_columns = self.max_matrix_columns.max(batch.columns);
        self.max_live_nonzeros = self.max_live_nonzeros.max(batch.elimination.peak_nonzeros);
        self.total_initial_nonzeros += batch.elimination.initial_nonzeros;
        self.total_final_nonzeros += batch.elimination.final_nonzeros;
        self.row_operations += batch.elimination.row_operations;
        self.pivot_inversions += batch.elimination.pivot_inversions;
        self.zero_rows += batch.elimination.zero_rows;
        self.reducer_rows += batch.reducer_rows;
        if batch.candidates == 0 {
            self.empty_batches += 1;
        }
    }

    /// The fraction of matrix rows that were reduction scaffolding rather than pair halves.
    ///
    /// Zero when no matrix was built.
    pub fn reducer_row_fraction(&self) -> f64 {
        let rows = 2 * self.pairs_reduced + self.reducer_rows;
        if rows == 0 {
            0.0
        } else {
            self.reducer_rows as f64 / rows as f64
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{BatchStatistics, F4Statistics};
    use crate::linalg::sparse::EliminationStatistics;

    /// Recording a batch accumulates the sums and raises the maxima.
    #[test]
    fn test_record_accumulates() {
        let mut statistics = F4Statistics::default();

        statistics.record(&BatchStatistics {
            pairs: 3,
            rows: 8,
            reducer_rows: 2,
            columns: 12,
            elimination: EliminationStatistics {
                rank: 6,
                zero_rows: 2,
                initial_nonzeros: 20,
                final_nonzeros: 18,
                peak_nonzeros: 25,
                row_operations: 7,
                pivot_inversions: 1,
            },
            candidates: 1,
        });
        statistics.record(&BatchStatistics {
            pairs: 1,
            rows: 4,
            reducer_rows: 1,
            columns: 20,
            elimination: EliminationStatistics {
                rank: 3,
                zero_rows: 1,
                initial_nonzeros: 9,
                final_nonzeros: 7,
                peak_nonzeros: 11,
                row_operations: 2,
                pivot_inversions: 0,
            },
            candidates: 0,
        });

        assert_eq!(statistics.batches, 2);
        assert_eq!(statistics.max_pairs_per_batch, 3);
        assert_eq!(statistics.max_matrix_rows, 8);
        assert_eq!(
            statistics.max_matrix_columns, 20,
            "the maximum, not the last"
        );
        assert_eq!(statistics.max_live_nonzeros, 25);
        assert_eq!(statistics.total_initial_nonzeros, 29);
        assert_eq!(statistics.total_final_nonzeros, 25);
        assert_eq!(statistics.row_operations, 9);
        assert_eq!(statistics.pivot_inversions, 1);
        assert_eq!(statistics.zero_rows, 3);
        assert_eq!(statistics.reducer_rows, 3);
        assert_eq!(
            statistics.empty_batches, 1,
            "the second batch produced none"
        );
    }

    /// The reducer fraction is zero before any matrix is built, and a proportion after.
    #[test]
    fn test_reducer_row_fraction() {
        let mut statistics = F4Statistics::default();
        assert_eq!(statistics.reducer_row_fraction(), 0.0);

        // Two pairs give four halves; six reducer rows out of ten is 0.6.
        statistics.pairs_reduced = 2;
        statistics.reducer_rows = 6;
        assert_eq!(statistics.reducer_row_fraction(), 0.6);
    }
}
