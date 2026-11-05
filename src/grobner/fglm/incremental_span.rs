//! Incremental linear dependence over a finite field, reporting coefficients.
//!
//! FGLM asks the same question repeatedly: is this quotient vector in the span of the ones already
//! accepted, and if so, with what coefficients? The coefficients are the answer that matters —
//! they become the coefficients of an emitted lex basis polynomial — and they must be relative to
//! the **accepted vectors**, not to the internally reduced rows.
//!
//! That is why `linalg::reduce_rows_against_pivots_with` cannot be used here. It rewrites the rows
//! and reports statistics, not the multipliers it applied. Recovering the multipliers means
//! carrying a second block through the elimination, which is what each row does below: alongside
//! its coordinates it holds its own expression in terms of the accepted vectors.
//!
//! # Neither block is square
//! An echelon row inserted when the accepted rank is `r` is a combination of the `r + 1` vectors
//! accepted up to and including the one that produced it. It **cannot** involve a vector accepted
//! afterwards, so its combination needs `r + 1` coefficients and not `D`. Summed over the rows that
//! is `D (D + 1) / 2` cells against `D^2`.
//!
//! The coordinates are the same argument from the other end. A row is reduced against every
//! earlier row before it is inserted, so it is zero below its own pivot, and nothing writes to a
//! row afterwards — [`IncrementalSpan::reduce`] only reads. So each row stores its coordinates
//! from its pivot on: `D - pivot` cells. At full rank the pivots are a permutation of `0..D`, so
//! the block is `D (D + 1) / 2` as well, and the span holds `D (D + 1)` field elements rather than
//! `D^2 + D (D + 1) / 2`: a third less in the limit, and 33.3% less at `D = 1,024`. Nothing is
//! approximated and nothing is traded — both paddings were zeros — but note the arithmetic rather
//! than the slogan: against the conversion's three dense blocks, of which the span is two, the
//! same cells are a fifth and not a quarter.
//!
//! # The reduction happens in registers the span owns
//! A reduction needs a `D`-cell dense vector and an `r`-cell coefficient vector, and the lex walk
//! performs `D + |G|` of them. Those two live in the span, as
//! [`DenseAccumulator`](crate::linalg::DenseAccumulator)'s buffer lives in it rather than in its
//! caller, so **the dependence test** allocates nothing per reduction:
//! [`IncrementalSpan::reduce_in_place`] fills them and [`IncrementalSpan::insert_scratch`] reads
//! them back. [`IncrementalSpan::reduce`] is the value-returning form and hands the buffers out,
//! which costs one allocation per call — what it cost before the registers existed.
//!
//! The registers are `2 D` cells the span now holds for its lifetime, and
//! [`FglmMemory`](super::FglmMemory) does not count them: it reports the `O(D^2)` blocks, and
//! these are `O(D)` — 0.1% of them at `D = 1,024` and 6% at `D = 16`. Nor do they raise the peak,
//! since the per-call vectors they replace were live during every reduction anyway. See
//! [`FglmMemory::dense_blocks_for`](super::FglmMemory::dense_blocks_for), which says so.

use crate::FiniteField;

/// One echelon row, with its expression in terms of the accepted vectors.
#[derive(Clone, Debug)]
struct SpanRow<F: FiniteField> {
    /// `coordinates = sum_j combination[j] * accepted_j`. The invariant everything rests on.
    ///
    /// **Stored from the pivot on**: `coordinates[k]` is the coefficient of column `pivot + k`, so
    /// the vector is `dimension - pivot` long. Everything below the pivot was cleared when the row
    /// was reduced and nothing writes to a row afterwards, so the padding this drops was zeros —
    /// see the module documentation.
    coordinates: Vec<F>,

    /// Coefficients over the accepted vectors, of length `index + 1` for the row at `index`.
    ///
    /// **Not padded to the dimension.** A row inserted at rank `r` cannot involve a vector accepted
    /// later, so coefficients beyond `r` are structurally zero — see the module documentation.
    /// Every loop over this zips against it rather than indexing, so the shorter length is a
    /// shorter loop and not a bounds hazard.
    combination: Vec<F>,

    /// The column this row leads with, distinct from every other row's.
    pivot: usize,
}

/// What reducing a vector against the accepted ones found.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Dependence<F: FiniteField> {
    /// The vector is not in the span. Carries what to hand back to [`IncrementalSpan::insert`].
    Independent {
        /// The vector with the span's contribution removed, i.e. `v - sum_j c_j * accepted_j`.
        residue: Vec<F>,
        /// The `c_j` above, one per **accepted** vector rather than one per dimension.
        combination: Vec<F>,
    },

    /// `v = sum_j coefficients[j] * accepted_j`, one coefficient per accepted vector.
    Dependent { coefficients: Vec<F> },
}

/// The span of a growing set of vectors, in row echelon form, with coefficients recoverable.
#[derive(Clone, Debug)]
pub struct IncrementalSpan<F: FiniteField> {
    rows: Vec<SpanRow<F>>,
    dimension: usize,

    /// Row subtractions performed, for the statistics. One subtraction against the row at `r`
    /// leading at `pivot` touches `D - pivot` coordinates and `r + 1` coefficients, not `2 * D`.
    row_operations: usize,

    /// The working register a reduction happens in: `D` cells, reused across calls.
    ///
    /// Held by the span rather than allocated per call, as
    /// [`DenseAccumulator`](crate::linalg::DenseAccumulator) holds its own. The lex walk
    /// reduces `D + |G|` vectors, so a per-call `Vec` is `D + |G|` allocations of `D` cells for one
    /// register's worth of live data.
    residue: Vec<F>,

    /// The second working register: the residue's expression over the accepted vectors.
    ///
    /// Resized to the accepted count on each reduction, which after the first call of a given rank
    /// writes `r` zeros and allocates nothing.
    combination: Vec<F>,
}

impl<F: FiniteField> IncrementalSpan<F> {
    /// An empty span over `dimension`-dimensional vectors.
    pub fn new(dimension: usize) -> Self {
        Self {
            rows: Vec::new(),
            dimension,
            row_operations: 0,
            residue: vec![F::zero(); dimension],
            combination: Vec::with_capacity(dimension),
        }
    }

    /// How many vectors have been accepted, which is the rank of the span.
    pub fn accepted(&self) -> usize {
        self.rows.len()
    }

    /// Row subtractions performed over this span's lifetime.
    pub fn row_operations(&self) -> usize {
        self.row_operations
    }

    /// Whether `v` lies in the span, and the coefficients either way.
    ///
    /// The value-returning form, for a caller that wants owned vectors back. The walk uses
    /// [`Self::reduce_in_place`] instead, which allocates nothing of its own.
    ///
    /// The registers' buffers leave with the value rather than being copied out of, so this costs
    /// what it cost before the registers existed — one allocation per call — and no more.
    /// [`Self::insert`] hands them back.
    ///
    /// # Panics
    /// If `v` is not of the span's dimension.
    pub fn reduce(&mut self, v: &[F]) -> Dependence<F> {
        if self.reduce_in_place(v) {
            Dependence::Dependent {
                coefficients: std::mem::take(&mut self.combination),
            }
        } else {
            Dependence::Independent {
                residue: std::mem::take(&mut self.residue),
                combination: std::mem::take(&mut self.combination),
            }
        }
    }

    /// As [`Self::reduce`], into the span's own registers: `true` if `v` lies in the span.
    ///
    /// The coefficients are [`Self::scratch_combination`] either way, and an independent `v` is
    /// accepted with [`Self::insert_scratch`], which reads the registers this left behind. Nothing
    /// is allocated once the registers have reached their size.
    ///
    /// A single forward pass suffices, and that is not obvious: the rows are in echelon form but
    /// are *not* reduced against each other, so subtracting a later row could in principle
    /// reintroduce a nonzero in an earlier row's pivot column. It cannot, because row `r` was
    /// produced by reducing against rows `0..r`, hence is zero in each of their pivot columns. So
    /// once a pivot column has been cleared no later row disturbs it.
    ///
    /// # Panics
    /// If `v` is not of the span's dimension.
    pub(crate) fn reduce_in_place(&mut self, v: &[F]) -> bool {
        assert_eq!(
            v.len(),
            self.dimension,
            "a vector of {} entries in a span of dimension {}",
            v.len(),
            self.dimension
        );

        // Disjoint borrows of the fields, so the rows can be read while the registers are written.
        let Self {
            rows,
            row_operations,
            residue,
            combination,
            ..
        } = self;

        residue.clear();
        residue.extend_from_slice(v);
        // One coefficient per accepted vector, not per dimension: there is nothing for the rest to
        // be a coefficient of. At rank `r` this is `r` cells where M17 allocated `D`.
        combination.clear();
        combination.resize(rows.len(), F::zero());

        for row in rows.iter() {
            let multiple = residue[row.pivot];
            if multiple.is_zero() {
                continue;
            }
            // The row is monic at its pivot, so the multiple is the entry itself. The row is
            // stored from its pivot on and the residue is full width, so the slice aligns the two
            // and the zip is exact rather than truncating.
            for (slot, value) in residue[row.pivot..].iter_mut().zip(&row.coordinates) {
                *slot -= multiple * *value;
            }
            for (slot, value) in combination.iter_mut().zip(&row.combination) {
                *slot += multiple * *value;
            }
            *row_operations += 1;
        }

        residue.iter().all(|value| value.is_zero())
    }

    /// The coefficients the last [`Self::reduce_in_place`] produced.
    pub(crate) fn scratch_combination(&self) -> &[F] {
        &self.combination
    }

    /// Accept a vector that [`Self::reduce`] found independent.
    ///
    /// `residue` and `combination` must be the ones that call returned, and no vector may have
    /// been accepted in between.
    ///
    /// The new row is `residue / residue[pivot]`, and its combination is
    /// `(e_k - combination) / residue[pivot]` where `k` is the index this vector takes: the
    /// residue is `a_k - sum_j c_j a_j` by construction, so that is what the row expresses. One
    /// modular inverse per pivot, and the rest is multiply-and-subtract.
    ///
    /// # Panics
    /// If `residue` is zero — the caller has handed back a dependent vector — or if `residue` is
    /// not of the span's dimension, or `combination` is not of the accepted count, or the span is
    /// already of full rank.
    pub fn insert(&mut self, residue: Vec<F>, combination: Vec<F>) {
        assert_eq!(residue.len(), self.dimension, "residue of the wrong length");
        assert_eq!(
            combination.len(),
            self.rows.len(),
            "a combination of {} coefficients over {} accepted vectors",
            combination.len(),
            self.rows.len()
        );

        // Into the registers, so that there is one insertion path and not two. The buffers
        // `reduce` handed out come back here, which is why alternating the two entry points
        // allocates once per reduction rather than once per reduction and once per insertion.
        self.residue = residue;
        self.combination = combination;
        self.insert_scratch();
    }

    /// Accept the vector the last [`Self::reduce_in_place`] found independent.
    ///
    /// Reads the registers that call left behind, so nothing is handed back and forth. The row it
    /// builds is as [`Self::insert`] describes.
    ///
    /// # Panics
    /// If the register holds the zero vector — the caller has accepted a dependent vector — or if
    /// it does not hold a vector at all, which is the state [`Self::reduce`] leaves behind, or if
    /// the span is already of full rank.
    pub(crate) fn insert_scratch(&mut self) {
        assert_eq!(
            self.residue.len(),
            self.dimension,
            "the register holds no reduced vector: `reduce` hands its buffer out, so a caller \
             mixing it with the register form must accept through `insert`"
        );
        let index = self.rows.len();
        assert!(
            index < self.dimension,
            "a {}-dimensional span cannot accept a {}th vector",
            self.dimension,
            index + 1
        );

        let pivot = self
            .residue
            .iter()
            .position(|value| !value.is_zero())
            .expect("an independent vector has a nonzero entry");
        let scale = self.residue[pivot].inverse();

        // From the pivot on. `residue[..pivot]` is zero by the definition of `pivot` above, and no
        // later write reintroduces a nonzero there, so there is nothing to store.
        let coordinates: Vec<F> = self.residue[pivot..]
            .iter()
            .map(|value| *value * scale)
            .collect();
        // `index + 1` coefficients: the negated input over the vectors already accepted, then the
        // one for the vector being accepted now. Exactly the row's own expression, with no padding.
        let mut row_combination: Vec<F> = Vec::with_capacity(index + 1);
        row_combination.extend(
            self.combination
                .iter()
                .map(|value| (F::zero() - *value) * scale),
        );
        row_combination.push(scale);

        self.rows.push(SpanRow {
            coordinates,
            combination: row_combination,
            pivot,
        });
    }

    /// Field-element cells the rows hold: `D - pivot` coordinates plus `r + 1` combination
    /// coefficients each.
    ///
    /// `D (D + 1)` at full rank, two triangles. Reported rather than derived from `D` so that a
    /// caller measuring a partial conversion sees what is really there — and a partial span's
    /// figure is not `r (r + 1)`, because the rows' pivots are whatever columns the input led with.
    pub fn stored_cells(&self) -> usize {
        self.rows
            .iter()
            .map(|row| row.coordinates.len() + row.combination.len())
            .sum()
    }

    /// The cells a span of this dimension holds at full rank, or `None` on overflow.
    ///
    /// `D (D + 1)`: two triangular blocks of `D (D + 1) / 2`. At full rank the pivots are a
    /// permutation of `0..D`, so the coordinates sum to `sum_pivot (D - pivot)` exactly, and the
    /// combinations to `sum_r (r + 1)`. Checked arithmetic, since a budget computed from a wrapped
    /// product would be no budget at all.
    pub fn cells_at_full_rank(dimension: usize) -> Option<usize> {
        dimension.checked_mul(dimension.checked_add(1)?)
    }
}

#[cfg(test)]
mod tests {
    use super::{Dependence, IncrementalSpan};
    use crate::{fields::Zp2147483647, FiniteField, One, Zero};

    type F = Zp2147483647;

    fn field(values: &[u64]) -> Vec<F> {
        values.iter().map(|v| F::new(*v)).collect()
    }

    /// `sum_j coefficients[j] * vectors[j]`, for checking a reported dependence.
    fn combine(vectors: &[Vec<F>], coefficients: &[F]) -> Vec<F> {
        let dimension = vectors.first().map(|v| v.len()).unwrap_or(0);
        let mut total = vec![F::zero(); dimension];
        for (vector, coefficient) in vectors.iter().zip(coefficients) {
            for (slot, value) in total.iter_mut().zip(vector) {
                *slot += *coefficient * *value;
            }
        }
        total
    }

    /// Feed `vectors` to a span, returning it beside the ones it accepted.
    fn fill(dimension: usize, vectors: &[Vec<F>]) -> (IncrementalSpan<F>, Vec<Vec<F>>) {
        let mut span = IncrementalSpan::new(dimension);
        let mut accepted: Vec<Vec<F>> = Vec::new();
        for vector in vectors {
            if let Dependence::Independent {
                residue,
                combination,
            } = span.reduce(vector)
            {
                span.insert(residue, combination);
                accepted.push(vector.clone());
            }
        }
        (span, accepted)
    }

    /// The rank of a set of vectors, by textbook dense Gaussian elimination.
    ///
    /// Deliberately independent of [`IncrementalSpan`]: no pivot reuse, no combination block, no
    /// incrementality. Agreement between the two is therefore evidence rather than a tautology.
    fn rank_by_elimination(vectors: &[Vec<F>]) -> usize {
        let mut rows: Vec<Vec<F>> = vectors.to_vec();
        let columns = rows.first().map(|r| r.len()).unwrap_or(0);
        let mut rank = 0;
        for column in 0..columns {
            let pivot = (rank..rows.len()).find(|r| !rows[*r][column].is_zero());
            let Some(pivot) = pivot else { continue };
            rows.swap(rank, pivot);
            let scale = rows[rank][column].inverse();
            for value in rows[rank].iter_mut() {
                *value *= scale;
            }
            for r in 0..rows.len() {
                if r == rank || rows[r][column].is_zero() {
                    continue;
                }
                let multiple = rows[r][column];
                for c in 0..columns {
                    rows[r][c] = rows[r][c] - multiple * rows[rank][c];
                }
            }
            rank += 1;
        }
        rank
    }

    /// Feed vectors in one at a time, accepting the independent ones, and check each verdict.
    ///
    /// Returns the accepted vectors, so a caller can assert the rank.
    fn feed(dimension: usize, vectors: &[Vec<F>]) -> Vec<Vec<F>> {
        let mut span = IncrementalSpan::new(dimension);
        let mut accepted: Vec<Vec<F>> = Vec::new();

        for v in vectors {
            match span.reduce(v) {
                Dependence::Independent {
                    residue,
                    combination,
                } => {
                    span.insert(residue, combination);
                    accepted.push(v.clone());
                }
                Dependence::Dependent { coefficients } => {
                    // Every reported dependence must reconstruct the vector exactly. This is the
                    // check the whole structure exists to pass.
                    assert_eq!(
                        combine(&accepted, &coefficients),
                        *v,
                        "the reported coefficients {:?} do not reconstruct {:?}",
                        &coefficients[..accepted.len()],
                        v
                    );
                    // Coefficients beyond the accepted count must be zero: there is nothing for
                    // them to refer to.
                    assert!(
                        coefficients[accepted.len()..]
                            .iter()
                            .all(|value| value.is_zero()),
                        "a coefficient refers to a vector that was never accepted"
                    );
                }
            }
            assert_eq!(span.accepted(), accepted.len());
        }
        accepted
    }

    /// Unit vectors are independent, and each one is accepted.
    #[test]
    fn test_unit_vectors_are_independent() {
        let vectors: Vec<Vec<F>> = (0..4)
            .map(|i| {
                let mut v = vec![F::zero(); 4];
                v[i] = F::one();
                v
            })
            .collect();
        assert_eq!(feed(4, &vectors).len(), 4);
    }

    /// A repeated vector is dependent with coefficient one on its first occurrence.
    #[test]
    fn test_a_repeated_vector_is_dependent() {
        let v = field(&[1, 2, 3]);
        let mut span = IncrementalSpan::new(3);
        match span.reduce(&v) {
            Dependence::Independent {
                residue,
                combination,
            } => span.insert(residue, combination),
            other => panic!("the first vector should be independent, got {:?}", other),
        }
        match span.reduce(&v) {
            Dependence::Dependent { coefficients } => {
                assert_eq!(coefficients[0], F::one());
                assert!(coefficients[1..].iter().all(|c| c.is_zero()));
            }
            other => panic!("a repeat should be dependent, got {:?}", other),
        }
    }

    /// The zero vector is dependent on nothing at all, with no coefficients.
    ///
    /// The edge case that distinguishes "in the span" from "a combination of something": the empty
    /// span contains zero.
    #[test]
    fn test_the_zero_vector_is_dependent_on_the_empty_span() {
        let mut span = IncrementalSpan::new(3);
        match span.reduce(&[F::zero(); 3]) {
            Dependence::Dependent { coefficients } => {
                assert!(coefficients.iter().all(|c| c.is_zero()));
            }
            other => panic!("zero should be dependent, got {:?}", other),
        }
        assert_eq!(span.accepted(), 0);
    }

    /// A known linear combination is reported with exactly the coefficients that produced it.
    #[test]
    fn test_a_known_combination_is_reported_exactly() {
        let a = field(&[1, 0, 2]);
        let b = field(&[0, 1, 3]);
        let mut span = IncrementalSpan::new(3);
        for v in [&a, &b] {
            match span.reduce(v) {
                Dependence::Independent {
                    residue,
                    combination,
                } => span.insert(residue, combination),
                other => panic!("{:?} should be independent, got {:?}", v, other),
            }
        }

        // 5a + 7b
        let target: Vec<F> = a
            .iter()
            .zip(&b)
            .map(|(x, y)| F::new(5) * *x + F::new(7) * *y)
            .collect();
        match span.reduce(&target) {
            Dependence::Dependent { coefficients } => {
                assert_eq!(coefficients[0], F::new(5));
                assert_eq!(coefficients[1], F::new(7));
                assert!(coefficients[2..].iter().all(|c| c.is_zero()));
            }
            other => panic!("5a + 7b should be dependent, got {:?}", other),
        }
    }

    /// The rank the span arrives at is the rank dense elimination arrives at.
    ///
    /// Several deliberately awkward sets: a dependency only visible after three vectors, a vector
    /// whose leading entries are zero, and a set of full rank.
    #[test]
    fn test_the_rank_agrees_with_dense_elimination() {
        let sets: Vec<Vec<Vec<F>>> = vec![
            vec![field(&[1, 1, 0]), field(&[0, 1, 1]), field(&[1, 2, 1])],
            vec![field(&[0, 0, 5]), field(&[0, 3, 0]), field(&[7, 0, 0])],
            vec![field(&[1, 2, 3]), field(&[2, 4, 6]), field(&[0, 0, 0])],
            vec![
                field(&[1, 0, 0, 0]),
                field(&[1, 1, 0, 0]),
                field(&[1, 1, 1, 0]),
                field(&[1, 1, 1, 1]),
                field(&[4, 3, 2, 1]),
            ],
            vec![field(&[2, 4]), field(&[3, 6]), field(&[1, 1])],
        ];

        for set in &sets {
            let dimension = set[0].len();
            let accepted = feed(dimension, set);
            assert_eq!(
                accepted.len(),
                rank_by_elimination(set),
                "the span and dense elimination disagree on the rank of {:?}",
                set
            );
        }
    }

    /// Order of presentation changes which vectors are accepted but not how many.
    ///
    /// The rank is a property of the set. A span whose pivot bookkeeping were wrong would be
    /// sensitive to the order, which is why this is worth checking rather than assuming.
    #[test]
    fn test_the_rank_does_not_depend_on_the_order() {
        let vectors = vec![
            field(&[1, 1, 0, 0]),
            field(&[0, 1, 1, 0]),
            field(&[1, 0, 1, 0]), // the sum of the first two less twice the... dependent
            field(&[0, 0, 0, 1]),
        ];
        let forwards = feed(4, &vectors).len();

        let mut reversed = vectors.clone();
        reversed.reverse();
        let backwards = feed(4, &reversed).len();

        assert_eq!(forwards, backwards);
        assert_eq!(forwards, rank_by_elimination(&vectors));
    }

    /// A full-rank span rejects a further vector rather than growing past its dimension.
    #[test]
    #[should_panic(expected = "cannot accept")]
    fn test_a_full_rank_span_cannot_grow() {
        let mut span = IncrementalSpan::new(2);
        for i in 0..2 {
            let mut v = vec![F::zero(); 2];
            v[i] = F::one();
            match span.reduce(&v) {
                Dependence::Independent {
                    residue,
                    combination,
                } => span.insert(residue, combination),
                other => panic!("{:?}", other),
            }
        }
        // Nothing in a 2-dimensional space is independent of two independent vectors, so this is
        // reachable only by lying to `insert`.
        span.insert(field(&[1, 1]), field(&[0, 0]));
    }

    /// Both blocks are triangular: `D - pivot` coordinates and `r + 1` coefficients per row.
    #[test]
    fn test_the_rows_hold_two_triangular_blocks() {
        const D: usize = 12;
        // Unit vectors in a scrambled order, so the rows' pivots are not their indices and the
        // triangularity cannot be an accident of the input being already echelonized.
        let order = [5usize, 0, 9, 2, 11, 7, 1, 8, 3, 10, 4, 6];
        let vectors: Vec<Vec<F>> = order
            .iter()
            .map(|k| {
                let mut v = vec![F::zero(); D];
                v[*k] = F::one();
                v
            })
            .collect();

        let (span, accepted) = fill(D, &vectors);
        assert_eq!(span.accepted(), D, "the unit vectors should be a basis");
        assert_eq!(accepted.len(), D);

        // At full rank the pivots are a permutation of `0..D`, so the coordinate block is
        // `sum (D - pivot) = D (D + 1) / 2` cells, and the combination block is the same figure
        // from the other direction: `r + 1` coefficients for the row at `r`.
        assert_eq!(
            span.stored_cells(),
            D * (D + 1) / 2 + D * (D + 1) / 2,
            "both blocks should be triangular, not one"
        );
        assert_eq!(span.stored_cells(), D * (D + 1), "which is `D (D + 1)`");
        assert_eq!(
            span.stored_cells(),
            IncrementalSpan::<F>::cells_at_full_rank(D).expect("representable")
        );
        // Strictly less than the square coordinate block alone, which is the whole point.
        assert!(span.stored_cells() < D * D + D * (D + 1) / 2);
    }

    /// A single row stores `D - pivot` coordinates, and still reduces a dependent vector exactly.
    ///
    /// The aggregate figure above would also hold if a row stored the wrong `D - pivot` cells — a
    /// span of full rank has one row per pivot either way. This pins one row's length against its
    /// own pivot, and then checks that the offset row still clears the column it leads with.
    #[test]
    fn test_a_row_stores_its_coordinates_from_its_pivot() {
        const D: usize = 8;
        const PIVOT: usize = 3;
        let mut span = IncrementalSpan::new(D);

        // Leading zeros, so the pivot is 3 rather than 0 and an off-by-one is visible.
        let v = field(&[0, 0, 0, 2, 5, 0, 7, 11]);
        match span.reduce(&v) {
            Dependence::Independent {
                residue,
                combination,
            } => span.insert(residue, combination),
            other => panic!("the first vector should be independent, got {:?}", other),
        }
        // `D - PIVOT` coordinates and the one combination coefficient of the row at index 0.
        assert_eq!(span.stored_cells(), (D - PIVOT) + 1);

        // Three times the vector is dependent with coefficient three, which it cannot be unless
        // the stored coordinates are aligned to the pivot they were offset by.
        let target: Vec<F> = v.iter().map(|value| F::new(3) * *value).collect();
        match span.reduce(&target) {
            Dependence::Dependent { coefficients } => assert_eq!(coefficients, field(&[3])),
            other => panic!("three times the row should be dependent, got {:?}", other),
        }

        // And a vector that differs only below the pivot keeps that difference: the row has
        // nothing stored there to subtract.
        let mut below = v.clone();
        below[0] = F::new(9);
        match span.reduce(&below) {
            Dependence::Independent { residue, .. } => {
                assert_eq!(residue, field(&[9, 0, 0, 0, 0, 0, 0, 0]));
            }
            other => panic!("a new leading entry should be independent, got {:?}", other),
        }
    }

    /// The register path and the value path produce the same verdicts, coefficients and rows.
    ///
    /// The conversion uses the first and every test here uses the second, so an answer that
    /// differed between them would be invisible to both.
    #[test]
    fn test_the_register_path_agrees_with_the_value_path() {
        const D: usize = 9;
        // A Vandermonde basis followed by combinations of it, so the sequence contains both
        // verdicts and the dependent ones have coefficients worth comparing.
        let mut vectors: Vec<Vec<F>> = (0..D)
            .map(|k| {
                let node = F::new(k as u64 + 2);
                let mut row = Vec::with_capacity(D);
                let mut power = F::one();
                for _ in 0..D {
                    row.push(power);
                    power *= node;
                }
                row
            })
            .collect();
        for weights in [
            vec![1u64, 0, 0, 0, 0, 0, 0, 0, 0],
            vec![0, 0, 3, 0, 0, 5, 0, 0, 0],
            vec![2, 3, 5, 7, 11, 13, 17, 19, 23],
        ] {
            let combined = combine(&vectors[..D], &field(&weights));
            vectors.push(combined);
        }

        let mut by_value = IncrementalSpan::new(D);
        let mut by_register = IncrementalSpan::new(D);
        for v in &vectors {
            let dependent = by_register.reduce_in_place(v);
            let register_combination = by_register.scratch_combination().to_vec();
            match by_value.reduce(v) {
                Dependence::Dependent { coefficients } => {
                    assert!(dependent, "the register path called {:?} independent", v);
                    assert_eq!(coefficients, register_combination);
                }
                Dependence::Independent {
                    residue,
                    combination,
                } => {
                    assert!(!dependent, "the register path called {:?} dependent", v);
                    assert_eq!(combination, register_combination);
                    by_value.insert(residue, combination);
                    by_register.insert_scratch();
                }
            }
            assert_eq!(by_value.accepted(), by_register.accepted());
            assert_eq!(by_value.stored_cells(), by_register.stored_cells());
            assert_eq!(by_value.row_operations(), by_register.row_operations());
        }
        assert_eq!(by_value.accepted(), D, "the basis should have full rank");
        // Identical rows, not merely identical verdicts: the rows are what the next reduction
        // reads, so equality here is equality for every future answer as well.
        assert_eq!(
            format!("{:?}", by_value.rows),
            format!("{:?}", by_register.rows)
        );
    }

    /// Accepting from a register that `reduce` emptied is a loud panic, not a wrong row.
    #[test]
    #[should_panic(expected = "holds no reduced vector")]
    fn test_accepting_from_an_emptied_register_panics() {
        let mut span = IncrementalSpan::new(3);
        // `reduce` hands the register's buffer out with the value, so the register is empty and
        // the independent vector it found is the caller's to hand back through `insert`.
        let _ = span.reduce(&field(&[1, 2, 3]));
        span.insert_scratch();
    }

    /// A dependence's coefficients are exact over the *original* accepted vectors.
    ///
    /// §8.2's correctness-critical requirement, and the one the triangular block could break: the
    /// coefficients must be relative to the vectors as they were handed in, not to the internally
    /// echelonized rows. Checked on vectors with no structure to hide an error.
    #[test]
    fn test_dependence_coefficients_are_exact_over_the_accepted_vectors() {
        const D: usize = 9;
        // A Vandermonde basis — row `k` is the powers of `k + 2` — which is invertible because the
        // nodes are distinct. Dense, with no zero and no structure an error could hide behind.
        let basis: Vec<Vec<F>> = (0..D)
            .map(|k| {
                let node = F::new(k as u64 + 2);
                let mut row = Vec::with_capacity(D);
                let mut power = F::one();
                for _ in 0..D {
                    row.push(power);
                    power *= node;
                }
                row
            })
            .collect();

        let (mut span, accepted) = fill(D, &basis);
        assert_eq!(span.accepted(), D, "the probe basis should have full rank");

        for weights in [
            vec![1u64, 0, 0, 0, 0, 0, 0, 0, 0],
            vec![0, 0, 3, 0, 0, 5, 0, 0, 0],
            vec![2, 3, 5, 7, 11, 13, 17, 19, 23],
        ] {
            let coefficients = field(&weights);
            let target = combine(&accepted, &coefficients);
            match span.reduce(&target) {
                Dependence::Dependent { coefficients } => {
                    assert_eq!(
                        coefficients.len(),
                        accepted.len(),
                        "one coefficient per accepted vector"
                    );
                    assert_eq!(
                        combine(&accepted, &coefficients),
                        target,
                        "the reported coefficients do not rebuild the vector"
                    );
                }
                other => panic!("{:?} should have been dependent, got {:?}", weights, other),
            }
        }
    }

    /// A combination of the wrong length is rejected rather than silently padded.
    #[test]
    #[should_panic(expected = "a combination of")]
    fn test_a_combination_of_the_wrong_length_is_rejected() {
        let mut span: IncrementalSpan<F> = IncrementalSpan::new(4);
        // The span has accepted nothing, so the only valid combination is empty.
        span.insert(field(&[1, 0, 0, 0]), field(&[0, 0, 0, 0]));
    }

    /// An unrepresentable dimension has no full-rank cell count rather than a wrapped one.
    #[test]
    fn test_an_unrepresentable_dimension_has_no_cell_count() {
        assert_eq!(IncrementalSpan::<F>::cells_at_full_rank(usize::MAX), None);
    }

    /// Row operations are counted, and a reduction against nothing performs none.
    #[test]
    fn test_row_operations_are_counted() {
        let mut span = IncrementalSpan::new(2);
        assert_eq!(span.row_operations(), 0);

        let v = field(&[1, 1]);
        match span.reduce(&v) {
            Dependence::Independent {
                residue,
                combination,
            } => span.insert(residue, combination),
            other => panic!("{:?}", other),
        }
        // No rows existed, so nothing was subtracted.
        assert_eq!(span.row_operations(), 0);

        // Now one row exists and the vector meets it.
        let _ = span.reduce(&field(&[2, 2]));
        assert_eq!(span.row_operations(), 1);
    }
}
