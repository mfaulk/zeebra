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

use crate::FiniteField;

/// One echelon row, with its expression in terms of the accepted vectors.
#[derive(Clone, Debug)]
struct SpanRow<F: FiniteField> {
    /// `coordinates = sum_j combination[j] * accepted_j`. The invariant everything rests on.
    coordinates: Vec<F>,

    /// Coefficients over the accepted vectors, zero-padded to the quotient dimension.
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
        /// The `c_j` above.
        combination: Vec<F>,
    },

    /// `v = sum_j coefficients[j] * accepted_j`.
    Dependent { coefficients: Vec<F> },
}

/// The span of a growing set of vectors, in row echelon form, with coefficients recoverable.
#[derive(Clone, Debug)]
pub struct IncrementalSpan<F: FiniteField> {
    rows: Vec<SpanRow<F>>,
    dimension: usize,

    /// Row subtractions performed, for the statistics. One subtraction touches `2 * D` entries.
    row_operations: usize,
}

impl<F: FiniteField> IncrementalSpan<F> {
    /// An empty span over `dimension`-dimensional vectors.
    pub fn new(dimension: usize) -> Self {
        Self {
            rows: Vec::new(),
            dimension,
            row_operations: 0,
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
    /// A single forward pass suffices, and that is not obvious: the rows are in echelon form but
    /// are *not* reduced against each other, so subtracting a later row could in principle
    /// reintroduce a nonzero in an earlier row's pivot column. It cannot, because row `r` was
    /// produced by reducing against rows `0..r`, hence is zero in each of their pivot columns. So
    /// once a pivot column has been cleared no later row disturbs it.
    ///
    /// # Panics
    /// If `v` is not of the span's dimension.
    pub fn reduce(&mut self, v: &[F]) -> Dependence<F> {
        assert_eq!(
            v.len(),
            self.dimension,
            "a vector of {} entries in a span of dimension {}",
            v.len(),
            self.dimension
        );

        let mut residue = v.to_vec();
        let mut combination = vec![F::zero(); self.dimension];

        for row in &self.rows {
            let multiple = residue[row.pivot];
            if multiple.is_zero() {
                continue;
            }
            // The row is monic at its pivot, so the multiple is the entry itself.
            for (slot, value) in residue.iter_mut().zip(&row.coordinates) {
                *slot -= multiple * *value;
            }
            for (slot, value) in combination.iter_mut().zip(&row.combination) {
                *slot += multiple * *value;
            }
            self.row_operations += 1;
        }

        if residue.iter().all(|value| value.is_zero()) {
            Dependence::Dependent {
                coefficients: combination,
            }
        } else {
            Dependence::Independent {
                residue,
                combination,
            }
        }
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
    /// If `residue` is zero — the caller has handed back a dependent vector — or if either vector
    /// is not of the span's dimension, or if the span is already of full rank.
    pub fn insert(&mut self, residue: Vec<F>, combination: Vec<F>) {
        assert_eq!(residue.len(), self.dimension, "residue of the wrong length");
        assert_eq!(
            combination.len(),
            self.dimension,
            "combination of the wrong length"
        );
        let index = self.rows.len();
        assert!(
            index < self.dimension,
            "a {}-dimensional span cannot accept a {}th vector",
            self.dimension,
            index + 1
        );

        let pivot = residue
            .iter()
            .position(|value| !value.is_zero())
            .expect("an independent vector has a nonzero entry");
        let scale = residue[pivot].inverse();

        let coordinates: Vec<F> = residue.iter().map(|value| *value * scale).collect();
        let mut row_combination: Vec<F> = combination
            .iter()
            .map(|value| (F::zero() - *value) * scale)
            .collect();
        row_combination[index] += scale;

        self.rows.push(SpanRow {
            coordinates,
            combination: row_combination,
            pivot,
        });
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
