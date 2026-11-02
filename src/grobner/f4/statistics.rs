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
    ///
    /// This is the memory question: how big did the biggest matrix get. It is deliberately not the
    /// fill-in question — see `worst_fill_in_peak`.
    pub max_live_nonzeros: usize,

    /// Nonzero entries in the matrix that reached `max_live_nonzeros`, as it was built.
    ///
    /// Context for `max_live_nonzeros`: how dense the biggest matrix was to begin with.
    pub max_live_nonzeros_as_built: usize,

    /// The peak live entries of the batch whose elimination filled in the most, proportionally.
    ///
    /// Tracked separately from `max_live_nonzeros` because **the biggest matrix is not necessarily
    /// the one that densified worst**. A batch going from 100 entries to 800 fills in eightfold; a
    /// batch going from 1000 to 1500 fills in by half but has the larger absolute peak. Reporting
    /// the second as the worst fill-in would understate how badly sparse elimination can behave,
    /// which is precisely the measurement a later dense/sparse threshold has to rest on.
    pub worst_fill_in_peak: usize,

    /// That same batch's entry count as built — the denominator of [`F4Statistics::worst_fill_in`].
    pub worst_fill_in_as_built: usize,

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
        if batch.elimination.peak_nonzeros > self.max_live_nonzeros {
            self.max_live_nonzeros = batch.elimination.peak_nonzeros;
            self.max_live_nonzeros_as_built = batch.elimination.initial_nonzeros;
        }

        // The worst *ratio*, which is a different batch in general. Compared by cross-multiplying
        // rather than by dividing, so the comparison is exact; `u128` because the product of two
        // entry counts can exceed a `u64` on a large enough problem.
        let (peak, built) = (
            batch.elimination.peak_nonzeros as u128,
            batch.elimination.initial_nonzeros as u128,
        );
        let (worst_peak, worst_built) = (
            self.worst_fill_in_peak as u128,
            self.worst_fill_in_as_built as u128,
        );
        // A batch with no entries has no ratio. Otherwise take it if nothing is recorded yet, or
        // if its ratio beats what is: peak/built > worst_peak/worst_built, cross-multiplied.
        let beats_the_record = worst_built == 0 || peak * worst_built > worst_peak * built;
        if built > 0 && beats_the_record {
            self.worst_fill_in_peak = batch.elimination.peak_nonzeros;
            self.worst_fill_in_as_built = batch.elimination.initial_nonzeros;
        }
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

    /// The worst fill-in observed: over every batch, the largest ratio of peak live entries to the
    /// entries that batch's matrix was built with.
    ///
    /// One when no matrix was built. Above one means elimination made some matrix denser than it
    /// started, which is the cost a sparse representation pays and the reason the peak is budgeted.
    ///
    /// This is a maximum over ratios, not the ratio at the maximum: see
    /// [`F4Statistics::worst_fill_in_peak`] for why those differ and why both are reported.
    pub fn worst_fill_in(&self) -> f64 {
        if self.worst_fill_in_as_built == 0 {
            1.0
        } else {
            self.worst_fill_in_peak as f64 / self.worst_fill_in_as_built as f64
        }
    }

    /// The fill-in of the largest matrix, which is not in general the worst fill-in.
    ///
    /// Reported alongside [`F4Statistics::worst_fill_in`] so the two can be compared: when they
    /// differ, the matrix that strained memory most and the matrix that densified most were
    /// different batches.
    pub fn fill_in_of_the_largest_matrix(&self) -> f64 {
        if self.max_live_nonzeros_as_built == 0 {
            1.0
        } else {
            self.max_live_nonzeros as f64 / self.max_live_nonzeros_as_built as f64
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
        assert_eq!(
            statistics.max_live_nonzeros_as_built, 20,
            "the denominator comes from the batch that peaked, not the other one"
        );
        // The first batch grew 20 -> 25 and the second 9 -> 11, so 1.25x beats 1.22x: here
        // the worst ratio and the largest matrix happen to be the same batch.
        assert_eq!(
            (
                statistics.worst_fill_in_peak,
                statistics.worst_fill_in_as_built
            ),
            (25, 20)
        );
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

    /// Fill-in is one before any matrix is built.
    #[test]
    fn test_worst_fill_in_of_nothing() {
        let statistics = F4Statistics::default();
        assert_eq!(statistics.worst_fill_in(), 1.0);
        assert_eq!(statistics.fill_in_of_the_largest_matrix(), 1.0);
    }

    /// The worst fill-in is the largest *ratio*, not the ratio of the largest matrix.
    ///
    /// Regression test. The implementation used to record the batch with the greatest absolute
    /// peak and then divide that batch's peak by its own initial count, which answers a different
    /// question. On the two batches below — 1000 entries growing to 1500, and 100 growing to 800 —
    /// it reported 1.5x as the worst fill-in when the honest answer is 8x. That mattered because
    /// the next milestone has to use this number to decide when sparse elimination stops paying.
    #[test]
    fn test_worst_fill_in_is_the_largest_ratio() {
        let batch = |initial: usize, peak: usize| BatchStatistics {
            elimination: EliminationStatistics {
                initial_nonzeros: initial,
                peak_nonzeros: peak,
                ..Default::default()
            },
            ..Default::default()
        };

        let mut statistics = F4Statistics::default();
        statistics.record(&batch(1000, 1500)); // 1.5x, and the larger matrix
        statistics.record(&batch(100, 800)); // 8.0x, and the worse fill-in

        assert_eq!(statistics.worst_fill_in(), 8.0);
        assert_eq!(
            statistics.max_live_nonzeros, 1500,
            "memory is still sized by the largest matrix"
        );
        assert_eq!(
            statistics.fill_in_of_the_largest_matrix(),
            1.5,
            "and that matrix's own fill-in is still available"
        );

        // Order of arrival does not matter.
        let mut reversed = F4Statistics::default();
        reversed.record(&batch(100, 800));
        reversed.record(&batch(1000, 1500));
        assert_eq!(reversed.worst_fill_in(), 8.0);
        assert_eq!(reversed.max_live_nonzeros, 1500);
    }

    /// A batch that did not densify at all does not displace a worse one.
    #[test]
    fn test_worst_fill_in_ignores_flat_batches() {
        let mut statistics = F4Statistics::default();
        statistics.record(&BatchStatistics {
            elimination: EliminationStatistics {
                initial_nonzeros: 10,
                peak_nonzeros: 25,
                ..Default::default()
            },
            ..Default::default()
        });
        assert_eq!(statistics.worst_fill_in(), 2.5);

        // Bigger absolute peak, but it barely grew.
        statistics.record(&BatchStatistics {
            elimination: EliminationStatistics {
                initial_nonzeros: 1000,
                peak_nonzeros: 1001,
                ..Default::default()
            },
            ..Default::default()
        });
        assert_eq!(statistics.worst_fill_in(), 2.5);
        assert_eq!(statistics.max_live_nonzeros, 1001);

        // An empty matrix has no ratio to speak of and must not divide by zero.
        statistics.record(&BatchStatistics::default());
        assert_eq!(statistics.worst_fill_in(), 2.5);
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
