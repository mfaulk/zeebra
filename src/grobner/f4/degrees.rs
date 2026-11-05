//! Where F4's work went, degree by degree, and which of it carried new algebraic information.
//!
//! [`super::statistics`] answers "what did this computation cost". It cannot answer "at which
//! degree did the matrices become unaffordable, and was the work there useful", because every
//! counter it holds is a sum or a maximum over the whole run. That second question is the one a
//! scheduling change has to be judged on: a strategy that moves work from degree 6 to degree 5 and
//! finishes no faster has still changed something worth knowing about.
//!
//! # Attribution, not zero-counting
//!
//! The obvious measure of wasted work is the zero-row count, and it is the wrong one. A batch's
//! rows are of two kinds (see [`RowKind`](super::RowKind)): the two halves of each critical pair,
//! and the reducer multiples symbolic preprocessing added so that the matrix can perform the
//! reductions polynomial division would. The reducer rows have distinct leading monomials by
//! construction, so they are linearly independent and **none of them ever reduces to zero**. Every
//! zero row is therefore a dependent *pair* row, and a pair contributes two rows — so the zero-row
//! count is not a count of useless pairs in either direction.
//!
//! What is informative is how much rank the pair rows added on top of the reducer block:
//!
//! ```text
//! candidate_rank_contribution = rank - reducer_rows
//! ```
//!
//! Exact, and independent of the order elimination took the rows in, because rank is. Reducer rows
//! span a space of dimension exactly `reducer_rows`, so everything above that came from the pairs.
//!
//! A second identity pins down how much of that contribution became *basis elements* rather than
//! relations the batch already represented. Writing `L` for the leading monomials of the input rows
//! — [`BatchStatistics::input_leading_monomials`](super::BatchStatistics::input_leading_monomials) —
//! every monomial in `L` leads some row, hence is a pivot column of the echelon form, so
//!
//! ```text
//! new basis elements = rank - |L|
//! ```
//!
//! and since `|L| = reducer_rows + (distinct lcms among the batch's pairs)`, the gap between the
//! rank the pairs contributed and the elements they yielded is exactly the number of distinct lcms
//! the batch worked at. Both identities are asserted in the tests rather than assumed.

use std::{collections::BTreeMap, time::Duration};

use super::statistics::BatchStatistics;

/// What F4 did at one selection degree.
///
/// A degree here is the total degree of the lcm of the critical pairs a batch was selected at.
/// [`PairQueue::select_batch`](crate::grobner::PairQueue::select_batch) takes pairs of one degree
/// at a time, so every batch has exactly one, and a degree may span several batches when the pair
/// cap splits it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DegreeStatistics {
    /// The lcm degree of the pairs selected.
    pub degree: u64,

    /// Pairs taken off the queue at this degree.
    pub pairs_considered: usize,

    /// Of those, pairs that reached a matrix.
    pub pairs_reduced: usize,

    /// Of those, pairs a selection-time criterion discarded.
    ///
    /// The product and chain criteria, which act on a selected batch. **Gebauer–Möller is not
    /// counted here**: it discards pairs as they are *inserted*, which happens while a batch of
    /// some other degree is being processed, so attributing its removals to a selection degree
    /// would be arbitrary. They stay in
    /// [`F4Statistics::criteria`](super::F4Statistics::criteria).
    pub pairs_rejected_by_criteria: usize,

    /// Matrices built at this degree.
    pub batches: usize,

    /// Summed over those matrices: reducer multiples added by symbolic preprocessing.
    pub reducer_rows: usize,

    /// Summed over those matrices: rows that are halves of a critical pair.
    pub candidate_rows: usize,

    /// Summed over those matrices: rank the pair rows added on top of the reducer block.
    ///
    /// `rank - reducer_rows`. See the module documentation for why this and not the zero-row count.
    pub candidate_rank_contribution: usize,

    /// Summed over those matrices: pair rows that added no rank.
    ///
    /// `candidate_rows - candidate_rank_contribution`, which is also the zero-row count — reducer
    /// rows never reduce to zero. Reported under this name because the equality is a *finding*
    /// about where dependencies live, not a definition, and a later change to row handling could
    /// break it.
    pub dependent_candidate_rows: usize,

    /// The largest matrix at this degree, in rows.
    pub max_matrix_rows: usize,

    /// The largest matrix at this degree, in columns.
    pub max_matrix_columns: usize,

    /// The largest number of nonzero entries live in any elimination at this degree.
    pub peak_live_nonzeros: usize,

    /// The largest [`BatchStatistics::estimated_bytes`] of any batch at this degree.
    pub peak_estimated_bytes: usize,

    /// New basis elements extracted at this degree, before interreduction.
    pub new_basis_elements: usize,

    /// Of those, elements whose own total degree is **below** the selection degree.
    ///
    /// The mutant count: a matrix built at degree `d` can produce a relation of degree less than
    /// `d`, which is information arriving earlier than the schedule expected. Measured here so
    /// that M22-D can ask whether such relations are common before any mechanism is built for
    /// them.
    pub new_elements_below_degree: usize,

    /// The smallest total degree of any element extracted at this degree, if any was.
    pub min_new_element_degree: Option<u64>,

    /// The largest total degree of any element extracted at this degree, if any was.
    pub max_new_element_degree: Option<u64>,

    /// The largest total degree of any monomial that appeared as a matrix column at this degree.
    ///
    /// Distinct from [`DegreeStatistics::degree`], and usually larger: symbolic preprocessing adds
    /// reducer multiples whose own monomials can exceed the lcm the batch was selected at. Zero
    /// unless [`F4Options::profile_degrees`](super::F4Options::profile_degrees) is set.
    pub max_column_degree: u64,

    /// Time spent in batches at this degree. Zero unless stage measurement is on.
    pub elapsed: Duration,
}

impl DegreeStatistics {
    /// An empty record for `degree`.
    pub fn new(degree: u64) -> Self {
        Self {
            degree,
            ..Self::default()
        }
    }

    /// Fold one batch's counters in.
    ///
    /// `pairs_considered` and `pairs_rejected_by_criteria` are not derivable from a
    /// [`BatchStatistics`] — a pair discarded by a criterion never reaches one — so
    /// [`DegreeProfile::record_selection`] carries them separately.
    pub fn record(&mut self, batch: &BatchStatistics) {
        self.batches += 1;
        self.reducer_rows += batch.reducer_rows;
        self.candidate_rows += batch.candidate_rows();
        self.candidate_rank_contribution += batch.candidate_rank_contribution();
        self.dependent_candidate_rows += batch.dependent_candidate_rows();
        self.max_matrix_rows = self.max_matrix_rows.max(batch.rows);
        self.max_matrix_columns = self.max_matrix_columns.max(batch.columns);
        self.peak_live_nonzeros = self.peak_live_nonzeros.max(batch.elimination.peak_nonzeros);
        self.peak_estimated_bytes = self.peak_estimated_bytes.max(batch.estimated_bytes());
        self.new_basis_elements += batch.candidates;
        self.new_elements_below_degree += batch.candidates_below_batch_degree;
        self.min_new_element_degree =
            merge_min(self.min_new_element_degree, batch.min_candidate_degree);
        self.max_new_element_degree =
            merge_max(self.max_new_element_degree, batch.max_candidate_degree);
        self.max_column_degree = self.max_column_degree.max(batch.max_column_degree);
        self.elapsed += batch.stages.sum();
    }

    /// The share of this degree's pair rows that added no rank.
    ///
    /// Zero when no pair row was built. One means every pair row was a dependency — the degree's
    /// whole matrix told the computation nothing it could not already derive.
    pub fn dependent_fraction(&self) -> f64 {
        if self.candidate_rows == 0 {
            0.0
        } else {
            self.dependent_candidate_rows as f64 / self.candidate_rows as f64
        }
    }

    /// The share of this degree's rows that were reduction scaffolding.
    pub fn reducer_fraction(&self) -> f64 {
        let rows = self.reducer_rows + self.candidate_rows;
        if rows == 0 {
            0.0
        } else {
            self.reducer_rows as f64 / rows as f64
        }
    }
}

/// The smaller of two optional degrees, taking whichever is present.
fn merge_min(current: Option<u64>, next: Option<u64>) -> Option<u64> {
    match (current, next) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

/// The larger of two optional degrees, taking whichever is present.
fn merge_max(current: Option<u64>, next: Option<u64>) -> Option<u64> {
    match (current, next) {
        (Some(a), Some(b)) => Some(a.max(b)),
        (a, b) => a.or(b),
    }
}

/// Per-degree records, in ascending degree.
///
/// A `BTreeMap` rather than a vector indexed by degree: F4 visits degrees in ascending order and
/// usually consecutively, but a batch's candidates can create lower-degree pairs, so the sequence
/// is not monotone and the first degree is not zero. Ordered iteration is what every report wants.
///
/// Empty unless [`F4Options::profile_degrees`](super::F4Options::profile_degrees) is set, which is
/// what keeps an ordinary computation from paying for a map insertion per batch.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DegreeProfile {
    degrees: BTreeMap<u64, DegreeStatistics>,
}

impl DegreeProfile {
    /// An empty profile.
    pub fn new() -> Self {
        Self::default()
    }

    /// True if nothing has been recorded.
    pub fn is_empty(&self) -> bool {
        self.degrees.is_empty()
    }

    /// How many distinct degrees were reached.
    pub fn len(&self) -> usize {
        self.degrees.len()
    }

    /// The record for `degree`, if there is one.
    pub fn get(&self, degree: u64) -> Option<&DegreeStatistics> {
        self.degrees.get(&degree)
    }

    /// Every record, in ascending degree.
    pub fn iter(&self) -> impl Iterator<Item = &DegreeStatistics> + '_ {
        self.degrees.values()
    }

    /// Record a batch's *selection*: the pairs taken off the queue and those a criterion discarded.
    ///
    /// Called before the matrix is built, so that a batch whose every pair is discarded — which
    /// builds nothing and reaches no [`BatchStatistics`] — still appears at its degree. That is the
    /// case a report most needs to see, since it is work the queue produced and the criteria paid
    /// for.
    pub fn record_selection(&mut self, degree: u64, considered: usize, rejected: usize) {
        let entry = self
            .degrees
            .entry(degree)
            .or_insert_with(|| DegreeStatistics::new(degree));
        entry.pairs_considered += considered;
        entry.pairs_rejected_by_criteria += rejected;
        entry.pairs_reduced += considered - rejected;
    }

    /// Record a batch's matrix work at `degree`.
    pub fn record(&mut self, degree: u64, batch: &BatchStatistics) {
        self.degrees
            .entry(degree)
            .or_insert_with(|| DegreeStatistics::new(degree))
            .record(batch);
    }

    /// The largest degree any batch was selected at.
    pub fn max_degree(&self) -> Option<u64> {
        self.degrees.keys().copied().next_back()
    }

    /// The largest degree any matrix column reached, over every degree.
    pub fn max_column_degree(&self) -> u64 {
        self.iter().map(|d| d.max_column_degree).max().unwrap_or(0)
    }

    /// The degree whose matrices held the most live entries, and that count.
    ///
    /// The answer to "where did this computation become unaffordable". `None` before any matrix.
    pub fn peak_degree(&self) -> Option<(u64, usize)> {
        self.iter()
            .filter(|d| d.batches > 0)
            .max_by_key(|d| (d.peak_live_nonzeros, d.degree))
            .map(|d| (d.degree, d.peak_live_nonzeros))
    }

    /// Pair rows that added no rank, over every degree, against pair rows built.
    ///
    /// The headline redundancy figure, and the one M22's first research question is stated in.
    /// Zero when no pair row was built.
    pub fn dependent_fraction(&self) -> f64 {
        let built: usize = self.iter().map(|d| d.candidate_rows).sum();
        let dependent: usize = self.iter().map(|d| d.dependent_candidate_rows).sum();
        if built == 0 {
            0.0
        } else {
            dependent as f64 / built as f64
        }
    }

    /// Elements extracted below the degree of the batch that produced them, over every degree.
    pub fn mutant_elements(&self) -> usize {
        self.iter().map(|d| d.new_elements_below_degree).sum()
    }
}

#[cfg(test)]
mod tests {
    use super::{DegreeProfile, DegreeStatistics};
    use crate::{grobner::f4::BatchStatistics, linalg::sparse::EliminationStatistics};

    /// A batch with the given shape, as `reduce_batch` would report it.
    fn batch(reducer_rows: usize, pair_rows: usize, rank: usize, leads: usize) -> BatchStatistics {
        BatchStatistics {
            rows: reducer_rows + pair_rows,
            reducer_rows,
            columns: rank + 3,
            elimination: EliminationStatistics {
                rank,
                zero_rows: reducer_rows + pair_rows - rank,
                peak_nonzeros: 10 * rank,
                ..Default::default()
            },
            candidates: rank - leads,
            input_leading_monomials: leads,
            ..Default::default()
        }
    }

    /// The rank attribution splits a batch's rank into the reducer block and what the pairs added.
    #[test]
    fn test_candidate_rank_contribution() {
        // Six reducer rows, four pair rows, rank eight: the pairs added two.
        let one = batch(6, 4, 8, 7);
        assert_eq!(one.candidate_rows(), 4);
        assert_eq!(one.candidate_rank_contribution(), 2);
        assert_eq!(one.dependent_candidate_rows(), 2);
        // Which is also the zero-row count, because reducer rows are independent.
        assert_eq!(one.dependent_candidate_rows(), one.elimination.zero_rows);
    }

    /// New basis elements are exactly the pivots in columns no input row led with.
    #[test]
    fn test_new_elements_are_rank_minus_input_leads() {
        let one = batch(6, 4, 8, 7);
        assert_eq!(
            one.candidates,
            one.elimination.rank - one.input_leading_monomials
        );
        // And the gap to the pairs' rank contribution is the distinct lcms the batch worked at.
        let distinct_lcms = one.input_leading_monomials - one.reducer_rows;
        assert_eq!(
            one.candidates,
            one.candidate_rank_contribution() - distinct_lcms
        );
    }

    /// A batch with no rows at all has no ratios and does not divide by zero.
    #[test]
    fn test_empty_batch_attribution() {
        let nothing = BatchStatistics::default();
        assert_eq!(nothing.candidate_rows(), 0);
        assert_eq!(nothing.candidate_rank_contribution(), 0);
        assert_eq!(nothing.dependent_candidate_rows(), 0);
    }

    /// Recording accumulates sums, raises maxima, and keeps the degree it was filed under.
    #[test]
    fn test_degree_statistics_accumulate() {
        let mut degree = DegreeStatistics::new(5);
        degree.record(&batch(6, 4, 8, 7));
        degree.record(&batch(2, 6, 5, 4));

        assert_eq!(degree.degree, 5);
        assert_eq!(degree.batches, 2);
        assert_eq!(degree.reducer_rows, 8);
        assert_eq!(degree.candidate_rows, 10);
        assert_eq!(degree.candidate_rank_contribution, 2 + 3);
        assert_eq!(degree.dependent_candidate_rows, 2 + 3);
        assert_eq!(degree.max_matrix_rows, 10, "the maximum, not the last");
        assert_eq!(degree.peak_live_nonzeros, 80);
        assert_eq!(degree.new_basis_elements, 1 + 1);
    }

    /// A degree's dependent and reducer fractions are proportions, and zero before any row.
    #[test]
    fn test_degree_fractions() {
        let empty = DegreeStatistics::new(3);
        assert_eq!(empty.dependent_fraction(), 0.0);
        assert_eq!(empty.reducer_fraction(), 0.0);

        let mut degree = DegreeStatistics::new(3);
        degree.record(&batch(6, 4, 8, 7));
        assert_eq!(degree.dependent_fraction(), 0.5);
        assert_eq!(degree.reducer_fraction(), 0.6);
    }

    /// The lowest and highest degree of the elements a degree produced are kept separately.
    #[test]
    fn test_new_element_degree_range() {
        let with_degrees = |min: u64, max: u64, below: usize| BatchStatistics {
            min_candidate_degree: Some(min),
            max_candidate_degree: Some(max),
            candidates_below_batch_degree: below,
            ..Default::default()
        };

        let mut degree = DegreeStatistics::new(6);
        assert_eq!(degree.min_new_element_degree, None);

        degree.record(&with_degrees(6, 6, 0));
        degree.record(&with_degrees(4, 7, 1));
        assert_eq!(degree.min_new_element_degree, Some(4));
        assert_eq!(degree.max_new_element_degree, Some(7));
        assert_eq!(degree.new_elements_below_degree, 1);

        // A batch that produced nothing does not erase the range.
        degree.record(&BatchStatistics::default());
        assert_eq!(degree.min_new_element_degree, Some(4));
    }

    /// A profile files batches under their degree and iterates in ascending order.
    #[test]
    fn test_profile_orders_by_degree() {
        let mut profile = DegreeProfile::new();
        assert!(profile.is_empty());

        profile.record(7, &batch(1, 2, 2, 1));
        profile.record(3, &batch(1, 2, 2, 1));
        profile.record(5, &batch(1, 2, 2, 1));
        profile.record(3, &batch(1, 2, 2, 1));

        let degrees: Vec<u64> = profile.iter().map(|d| d.degree).collect();
        assert_eq!(degrees, vec![3, 5, 7]);
        assert_eq!(profile.len(), 3);
        assert_eq!(profile.get(3).unwrap().batches, 2);
        assert_eq!(profile.max_degree(), Some(7));
    }

    /// A degree whose every pair was discarded still appears, with no matrix against it.
    ///
    /// The case the selection record exists for: the queue produced the pairs and the criteria paid
    /// to examine them, so a report that showed nothing at that degree would hide real work.
    #[test]
    fn test_a_degree_with_no_matrix_is_still_recorded() {
        let mut profile = DegreeProfile::new();
        profile.record_selection(4, 3, 3);

        let degree = profile.get(4).expect("the degree was selected");
        assert_eq!(degree.pairs_considered, 3);
        assert_eq!(degree.pairs_rejected_by_criteria, 3);
        assert_eq!(degree.pairs_reduced, 0);
        assert_eq!(degree.batches, 0, "nothing was built");
    }

    /// The peak degree is where the matrices were largest, not where the most batches ran.
    #[test]
    fn test_peak_degree() {
        let mut profile = DegreeProfile::new();
        assert_eq!(profile.peak_degree(), None);

        profile.record(2, &batch(1, 2, 2, 1)); // peak 20
        profile.record(2, &batch(1, 2, 2, 1));
        profile.record(2, &batch(1, 2, 2, 1));
        profile.record(6, &batch(10, 20, 25, 20)); // peak 250
        assert_eq!(profile.peak_degree(), Some((6, 250)));
    }

    /// The headline redundancy figure is dependent pair rows over pair rows built.
    #[test]
    fn test_profile_dependent_fraction() {
        let mut profile = DegreeProfile::new();
        assert_eq!(profile.dependent_fraction(), 0.0);

        profile.record(3, &batch(0, 4, 4, 4)); // 4 pair rows, none dependent
        profile.record(4, &batch(0, 4, 0, 0)); // 4 pair rows, all dependent
        assert_eq!(profile.dependent_fraction(), 0.5);
    }
}
