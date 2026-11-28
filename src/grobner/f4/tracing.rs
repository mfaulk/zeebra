//! Learn/apply tracing, the learn half: what a replay would build, keep and skip (#1190).
//!
//! A trace is recorded from conventional F4 through [`BatchObserver`], so it describes the live
//! path. Each round keeps the selected pairs, the matrix columns, every row's origin and every
//! row's *fate* under a reference forward elimination: reducer rows are the pivots they already
//! are, and pair rows are reduced in matrix order against those and against earlier pair rows.
//! A pair row ends as zero or as a pivot at some column. The model is the engine's
//! reducers-first forward pass; the engine's own row order and kernels may differ, which moves
//! which rows end zero but not how many.
//!
//! [`compare`] asks whether a trace learned on one instance replays on another: same pairs, same
//! columns, same rows and same fates in every round. The first round that differs is classified
//! by whether a replay could notice. A replay builds only the rows the learned trace kept, so a
//! kept row that changes fate, or a column set that changes, is visible to it. A row the learned
//! trace saw reduce to zero but that is nonzero here is invisible to a replay that skips it; that
//! is the silent failure the issue asks to count.

use crate::{
    grobner::{
        f4::{
            macaulay::MacaulayMatrix,
            observer::BatchObserver,
            options::{F4Error, F4Options},
            symbolic::{MonicBasis, RowKind},
        },
        pairs::CriticalPair,
    },
    linalg::{sparse::SparseRow, DenseAccumulator},
    poly::{Monomial, MonomialOrder},
    FiniteField, MultivariatePolynomial,
};

/// How a row ended under the reference forward elimination.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum RowFate {
    /// A reducer multiple: a pivot from the start, never reduced.
    Reducer,
    /// A pair row that reduced to zero. A replay skips it.
    Zero,
    /// A pair row that became the pivot at this column index. `new` when the column is not the
    /// leading monomial of any row the round built, which is what makes it a new basis element.
    Pivot { column: usize, new: bool },
}

/// One matrix row: a basis element times a monomial, and what became of it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TracedRow<const N: usize> {
    pub multiplier: Monomial<N>,
    pub basis_index: usize,
    pub kind: RowKind,
    pub fate: RowFate,
    /// Coefficient products spent reducing this row (pivot-row entries per subtraction).
    pub products: usize,
}

/// One F4 round as a replay would see it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TraceRound<const N: usize> {
    /// Basis size when the round started.
    pub basis_len: usize,
    pub pairs: Vec<CriticalPair<N>>,
    pub columns: Vec<Monomial<N>>,
    pub rows: Vec<TracedRow<N>>,
}

impl<const N: usize> TraceRound<N> {
    /// Products spent on all pair rows.
    pub fn products(&self) -> usize {
        self.rows.iter().map(|row| row.products).sum()
    }

    /// Products spent on pair rows that ended zero: what a replay skips in elimination.
    pub fn zero_row_products(&self) -> usize {
        self.rows
            .iter()
            .filter(|row| row.fate == RowFate::Zero)
            .map(|row| row.products)
            .sum()
    }

    pub fn pair_rows(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| r.fate != RowFate::Reducer)
            .count()
    }

    pub fn zero_rows(&self) -> usize {
        self.rows.iter().filter(|r| r.fate == RowFate::Zero).count()
    }

    /// Rows that became new basis elements.
    pub fn new_elements(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| matches!(r.fate, RowFate::Pivot { new: true, .. }))
            .count()
    }
}

/// Every round of one conventional-F4 run.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct F4Trace<const N: usize> {
    pub rounds: Vec<TraceRound<N>>,
}

impl<const N: usize> F4Trace<N> {
    pub fn products(&self) -> usize {
        self.rounds.iter().map(TraceRound::products).sum()
    }

    pub fn zero_row_products(&self) -> usize {
        self.rounds.iter().map(TraceRound::zero_row_products).sum()
    }

    pub fn pair_rows(&self) -> usize {
        self.rounds.iter().map(TraceRound::pair_rows).sum()
    }

    pub fn zero_rows(&self) -> usize {
        self.rounds.iter().map(TraceRound::zero_rows).sum()
    }
}

/// The observer that records an [`F4Trace`].
#[derive(Clone, Debug, Default)]
pub struct TraceRecorder<const N: usize> {
    trace: F4Trace<N>,
    pending: Option<TraceRound<N>>,
}

impl<const N: usize> TraceRecorder<N> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn into_trace(self) -> F4Trace<N> {
        self.trace
    }
}

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for TraceRecorder<N> {
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]) {
        // The previous round's new elements are exactly what the basis grew by; checked here,
        // where both are in hand, so the fate model cannot drift from the engine silently.
        if let Some(previous) = self.trace.rounds.last() {
            assert_eq!(
                previous.basis_len + previous.new_elements(),
                basis.len(),
                "the reference elimination disagrees with F4 on the new elements"
            );
        }
        self.pending = Some(TraceRound {
            basis_len: basis.len(),
            pairs: pairs.to_vec(),
            ..TraceRound::default()
        });
    }

    fn matrix(&mut self, matrix: &MacaulayMatrix<N, F>) {
        let mut round = self.pending.take().expect("batch precedes matrix");
        round.columns = matrix.columns().to_vec();
        round.rows = fates(matrix);
        self.trace.rounds.push(round);
    }
}

/// Reference reducers-first forward elimination on a copy of the rows.
fn fates<const N: usize, F: FiniteField>(matrix: &MacaulayMatrix<N, F>) -> Vec<TracedRow<N>> {
    let origins = matrix.row_origins();
    let rows = matrix.matrix().rows();
    assert_eq!(origins.len(), rows.len());
    let width = matrix.num_columns();
    let mut leading = vec![false; width];
    for row in rows {
        if let Some(column) = row.leading_column() {
            leading[column] = true;
        }
    }
    // Column -> pivot row, reducers first. Reducer multiples of a monic basis lead with one.
    let mut pivot: Vec<Option<SparseRow<F>>> = vec![None; width];
    for (origin, row) in origins.iter().zip(rows) {
        if origin.kind == RowKind::Reducer {
            let column = row.leading_column().expect("a reducer row is nonzero");
            debug_assert!(pivot[column].is_none(), "one reducer per column");
            pivot[column] = Some(row.clone());
        }
    }
    let mut accumulator = DenseAccumulator::<F>::new(width);
    origins
        .iter()
        .zip(rows)
        .map(|(origin, row)| {
            let traced = |fate, products| TracedRow {
                multiplier: origin.multiplier,
                basis_index: origin.basis_index,
                kind: origin.kind,
                fate,
                products,
            };
            if origin.kind == RowKind::Reducer {
                return traced(RowFate::Reducer, 0);
            }
            accumulator.load(row);
            let mut products = 0;
            let fate = loop {
                let Some(column) = accumulator.leading_column() else {
                    break RowFate::Zero;
                };
                match &pivot[column] {
                    Some(pivot_row) => {
                        let factor = accumulator.leading_coefficient().expect("nonzero row");
                        products += pivot_row.nonzeros();
                        accumulator.subtract_scaled(pivot_row, factor);
                    }
                    None => {
                        accumulator.normalize();
                        break RowFate::Pivot {
                            column,
                            new: !leading[column],
                        };
                    }
                }
            };
            let reduced = accumulator.take();
            if let RowFate::Pivot { column, .. } = fate {
                pivot[column] = Some(reduced);
            }
            traced(fate, products)
        })
        .collect()
}

/// Run conventional F4 and record its trace. The basis is what [`super::f4_with_options`]
/// returns: the recorder only reads.
///
/// # Errors
/// As [`super::f4_with_options`].
pub fn learn<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> Result<(Vec<MultivariatePolynomial<N, F>>, F4Trace<N>), F4Error> {
    let mut recorder = TraceRecorder::new();
    let (basis, _) = super::f4_observed(generators, order, options, &mut recorder)?;
    Ok((basis, recorder.into_trace()))
}

/// Why a learned trace stops describing another run, at the first round that differs.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Divergence {
    /// Different pairs were selected: the bases already differ in leading monomials.
    Pairs,
    /// Same pairs, different columns or row origins: a support changed by cancellation, and the
    /// observed round needs a column or row the learned one lacks. A replay sees it when it
    /// builds the learned rows and finds a term with no reducer.
    Support,
    /// As [`Divergence::Support`], but the observed columns and rows are subsets of the learned
    /// ones: terms cancelled. A replay that builds the learned rows carries those as zero
    /// columns, so the comparison stops here only because this one is exact.
    SupportShrank,
    /// The same columns and rows in another order: reducer choice or emission order moved,
    /// the support did not. A replay that keeps the learned order is unaffected by it.
    Reordered,
    /// Same matrix shape, and a row the learned trace kept ends differently. A replay sees a
    /// vanished or moved pivot.
    KeptRow,
    /// Same matrix shape and every kept row ends as learned, but a row the learned trace saw
    /// vanish is nonzero here. A replay that skips it misses an element: silent.
    SkippedRow,
    /// One run has rounds the other does not.
    Length,
}

impl Divergence {
    /// Whether a replay that checks columns and the pivots of the rows it built would notice.
    pub fn detectable(self) -> bool {
        !matches!(self, Divergence::SkippedRow)
    }
}

/// How far a learned trace describes an observed run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Comparison {
    /// Rounds identical in pairs, columns, rows and fates before the first difference.
    pub matched_rounds: usize,
    /// `None` when the whole trace replays.
    pub divergence: Option<Divergence>,
}

impl Comparison {
    pub fn transfers(&self) -> bool {
        self.divergence.is_none()
    }
}

/// Compare a trace learned on one instance with the trace of another instance.
pub fn compare<const N: usize>(learned: &F4Trace<N>, observed: &F4Trace<N>) -> Comparison {
    for (index, (a, b)) in learned.rounds.iter().zip(&observed.rounds).enumerate() {
        if let Some(divergence) = round_divergence(a, b) {
            return Comparison {
                matched_rounds: index,
                divergence: Some(divergence),
            };
        }
    }
    let matched = learned.rounds.len().min(observed.rounds.len());
    Comparison {
        matched_rounds: matched,
        divergence: (learned.rounds.len() != observed.rounds.len()).then_some(Divergence::Length),
    }
}

fn round_divergence<const N: usize>(a: &TraceRound<N>, b: &TraceRound<N>) -> Option<Divergence> {
    if a.basis_len != b.basis_len || a.pairs != b.pairs {
        return Some(Divergence::Pairs);
    }
    let origin = |r: &TracedRow<N>| (r.multiplier, r.basis_index, r.kind);
    if a.columns != b.columns
        || a.rows.len() != b.rows.len()
        || a.rows.iter().map(origin).ne(b.rows.iter().map(origin))
    {
        // Both lists are in a canonical order (columns descending, rows as preprocessing emits
        // them), but a subset need not keep positions, so membership is by set.
        let columns: std::collections::HashSet<_> = a.columns.iter().collect();
        // `RowKind` is not `Hash`; its pair index is the whole of what distinguishes one.
        let key = |r: &TracedRow<N>| {
            let pair = match r.kind {
                RowKind::PairComponent { pair } => Some(pair),
                RowKind::Reducer => None,
            };
            (r.multiplier, r.basis_index, pair)
        };
        let rows: std::collections::HashSet<_> = a.rows.iter().map(key).collect();
        let shrank = b.columns.iter().all(|c| columns.contains(c))
            && b.rows.iter().all(|r| rows.contains(&key(r)));
        let same_size = b.columns.len() == a.columns.len() && b.rows.len() == a.rows.len();
        return Some(if shrank && same_size {
            Divergence::Reordered
        } else if shrank {
            Divergence::SupportShrank
        } else {
            Divergence::Support
        });
    }
    let mut skipped_changed = false;
    for (x, y) in a.rows.iter().zip(&b.rows) {
        if x.fate == y.fate {
            continue;
        }
        if x.fate == RowFate::Zero {
            skipped_changed = true;
        } else {
            return Some(Divergence::KeptRow);
        }
    }
    skipped_changed.then_some(Divergence::SkippedRow)
}

#[cfg(test)]
mod tests {
    use super::{compare, learn, Divergence, RowFate};
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura},
            f4::{f4_with_options, options::F4Options},
        },
        poly::MonomialOrder,
        FiniteField, MultivariatePolynomial,
    };

    type F = Zp2147483647;
    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    /// Every nonconstant coefficient replaced by a seeded nonzero draw: same support, new instance.
    fn rescaled<const N: usize>(
        system: &[MultivariatePolynomial<N, F>],
        seed: u64,
    ) -> Vec<MultivariatePolynomial<N, F>> {
        let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
        let mut draw = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            F::new(1 + state % 2_147_483_646)
        };
        system
            .iter()
            .map(|p| {
                let mut monomials: Vec<_> = p.terms().keys().copied().collect();
                monomials.sort();
                let terms: Vec<_> = monomials.into_iter().map(|m| (m, draw())).collect();
                MultivariatePolynomial::new(&terms)
            })
            .collect()
    }

    #[test]
    fn test_learning_does_not_change_the_basis() {
        let options = F4Options::default();
        for system in [katsura::<5, F>(), cyclic::<5, F>()] {
            let plain = f4_with_options(&system, GREVLEX, &options).unwrap().0;
            let (traced, trace) = learn(&system, GREVLEX, &options).unwrap();
            assert_eq!(plain, traced);
            assert!(!trace.rounds.is_empty());
        }
    }

    // The recorder asserts each round's new elements against the basis growth; a whole run is
    // that check on every round but the last.
    #[test]
    fn test_reference_fates_agree_with_f4_on_new_elements() {
        let (_, trace) = learn(&katsura::<6, F>(), GREVLEX, &F4Options::default()).unwrap();
        assert!(trace.rounds.iter().any(|r| r.new_elements() > 0));
    }

    #[test]
    fn test_katsura_has_zero_rows_and_their_products_are_a_share() {
        let (_, trace) = learn(&katsura::<6, F>(), GREVLEX, &F4Options::default()).unwrap();
        assert!(trace.zero_rows() > 0);
        assert!(trace.zero_row_products() > 0);
        assert!(trace.zero_row_products() <= trace.products());
        for round in &trace.rounds {
            for row in &round.rows {
                if row.fate == RowFate::Reducer {
                    assert_eq!(row.products, 0);
                }
            }
        }
    }

    #[test]
    fn test_a_trace_replays_on_itself() {
        let (_, trace) = learn(&katsura::<5, F>(), GREVLEX, &F4Options::default()).unwrap();
        let comparison = compare(&trace, &trace);
        assert!(comparison.transfers());
        assert_eq!(comparison.matched_rounds, trace.rounds.len());
    }

    // Generic coefficients over a 31-bit prime: Katsura's trace should transfer, and the
    // learned trace and the observed one must report the same skippable work.
    #[test]
    fn test_katsura_trace_transfers_across_generic_coefficients() {
        let options = F4Options::default();
        let (_, learned) = learn(&rescaled(&katsura::<5, F>(), 1), GREVLEX, &options).unwrap();
        for seed in 2..5 {
            let (_, observed) =
                learn(&rescaled(&katsura::<5, F>(), seed), GREVLEX, &options).unwrap();
            let comparison = compare(&learned, &observed);
            assert!(comparison.transfers(), "seed {seed}: {comparison:?}");
            assert_eq!(learned.zero_rows(), observed.zero_rows());
        }
    }

    #[test]
    fn test_a_different_system_diverges_detectably_in_round_zero() {
        let options = F4Options::default();
        let (_, a) = learn(&katsura::<5, F>(), GREVLEX, &options).unwrap();
        let (_, b) = learn(&cyclic::<5, F>(), GREVLEX, &options).unwrap();
        let comparison = compare(&a, &b);
        assert_eq!(comparison.matched_rounds, 0);
        let divergence = comparison.divergence.unwrap();
        assert!(divergence.detectable());
        assert_ne!(divergence, Divergence::SkippedRow);
    }

    // A support that lost terms is distinguished from one that gained them: a replay that builds
    // the learned rows can carry an absent monomial as a zero column, not a missing reducer.
    #[test]
    fn test_support_divergence_says_whether_the_support_shrank() {
        let (_, learned) = learn(&katsura::<5, F>(), GREVLEX, &F4Options::default()).unwrap();
        let round = learned
            .rounds
            .iter()
            .position(|r| r.rows.iter().any(|x| x.fate == RowFate::Reducer))
            .unwrap();
        let reducer = learned.rounds[round]
            .rows
            .iter()
            .position(|x| x.fate == RowFate::Reducer)
            .unwrap();
        let mut shrunk = learned.clone();
        shrunk.rounds[round].rows.remove(reducer);
        shrunk.rounds[round].columns.pop();
        assert_eq!(
            compare(&learned, &shrunk).divergence,
            Some(Divergence::SupportShrank)
        );
        assert_eq!(
            compare(&shrunk, &learned).divergence,
            Some(Divergence::Support)
        );
    }

    // Same rows in another order is neither a shrink nor a growth.
    #[test]
    fn test_reordered_rows_are_their_own_divergence() {
        let (_, learned) = learn(&katsura::<5, F>(), GREVLEX, &F4Options::default()).unwrap();
        let round = learned
            .rounds
            .iter()
            .position(|r| r.rows.iter().filter(|x| x.fate == RowFate::Reducer).count() > 1)
            .unwrap();
        let mut reordered = learned.clone();
        let rows = &mut reordered.rounds[round].rows;
        let reducers: Vec<usize> = (0..rows.len())
            .filter(|&i| rows[i].fate == RowFate::Reducer)
            .collect();
        rows.swap(reducers[0], reducers[1]);
        assert_eq!(
            compare(&learned, &reordered).divergence,
            Some(Divergence::Reordered)
        );
    }

    // A round whose only change is a skipped row turning nonzero is the silent case.
    #[test]
    fn test_a_skipped_row_turning_nonzero_is_silent() {
        let (_, learned) = learn(&katsura::<6, F>(), GREVLEX, &F4Options::default()).unwrap();
        let mut observed = learned.clone();
        let (round, row) = observed
            .rounds
            .iter()
            .enumerate()
            .find_map(|(i, r)| {
                r.rows
                    .iter()
                    .position(|x| x.fate == RowFate::Zero)
                    .map(|j| (i, j))
            })
            .unwrap();
        observed.rounds[round].rows[row].fate = RowFate::Pivot {
            column: 0,
            new: true,
        };
        let comparison = compare(&learned, &observed);
        assert_eq!(comparison.matched_rounds, round);
        assert_eq!(comparison.divergence, Some(Divergence::SkippedRow));
        assert!(!Divergence::SkippedRow.detectable());

        let mut kept = learned.clone();
        let target = kept.rounds[round]
            .rows
            .iter()
            .position(|x| matches!(x.fate, RowFate::Pivot { .. }))
            .unwrap();
        kept.rounds[round].rows[target].fate = RowFate::Zero;
        assert_eq!(
            compare(&learned, &kept).divergence,
            Some(Divergence::KeptRow)
        );
    }
}
