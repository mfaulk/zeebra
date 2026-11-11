//! Multiplication by a variable, as a linear operator on the quotient algebra.
//!
//! The columns are stored three ways because the object has three shapes, and which one a column
//! has is a property of the ideal rather than of the operator.
//!
//! The standard monomials are closed downwards, so only the outer surface of the staircase leaves
//! it under multiplication: for most basis monomials `b_j` the product `x_i b_j` is itself standard
//! and the column is a unit vector costing no storage and no reduction. A dense `D x D` matrix per
//! variable would hold `N * D^2` field elements of which the great majority are structurally zero.
//!
//! A column that *does* leave the staircase, though, is not necessarily sparse. Measured over the
//! benchmark corpus, a reduced column holds **79% of `D` on katsura-7 and 0.14% on planted-10** —
//! and at `size_of::<(usize, F)>()` against `size_of::<F>()`, a sparse column costs twice a dense
//! cell per entry, so it only saves below half fill. Katsura is above it and the rest is far below.
//! Hence [`OperatorStorage`](super::OperatorStorage), which decides per column rather than per
//! operator or per crate.
//!
//! See §7 of `docs/MILESTONE-FGLM-SCALABILITY.md`.

use std::mem::size_of;

use crate::{grobner::fglm::options::OperatorStorage, FiniteField};

/// Column `j` of an operator: where multiplication sends the `j`-th standard monomial.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Column<F: FiniteField> {
    /// The product is the standard monomial at this index, so the column is a unit vector.
    Standard(usize),

    /// The product left the staircase and reduced to this combination of standard monomials,
    /// ascending by index. Empty when the product reduced to zero, which allocates nothing and is
    /// the compact representation of a zero column.
    Sparse(Box<[(usize, F)]>),

    /// The same column as `D` coefficients, zeros included.
    ///
    /// Cheaper than [`Self::Sparse`] above half fill, since an entry carries an index and a cell
    /// does not. Never chosen for a column that is not, which is the whole point of deciding per
    /// column.
    Dense(Box<[F]>),
}

// `Box<[T]>` and not `Vec<T>`, for two reasons that both matter at `N * D` columns. A boxed slice
// is two words where a `Vec` is three, and with two of the three variants holding one the
// difference decides whether the enum is 24 bytes or 32 — on planted-10's 10,240 columns, 80 kB.
// And a boxed slice has no capacity to diverge from its length, so the bytes reported are the bytes
// allocated with nothing to reason about. The columns are never mutated after construction, so
// nothing is given up.

impl<F: FiniteField> Column<F> {
    /// The representation `storage` asks for, for a column of `entries` in dimension `dimension`.
    ///
    /// # Panics
    /// If an entry's index is not below `dimension`, which would make the dense form impossible
    /// and the sparse form a lie.
    fn build(entries: Vec<(usize, F)>, dimension: usize, storage: OperatorStorage) -> Self {
        debug_assert!(
            entries.iter().all(|(index, _)| *index < dimension),
            "a column entry is outside dimension {}",
            dimension
        );

        let dense = match storage {
            OperatorStorage::Sparse => false,
            OperatorStorage::Dense => true,
            // Bytes, not a fill fraction: the comparison is between what the two representations
            // would really allocate, so it stays right if either element size changes. The column
            // spine costs the same either way and so cancels.
            OperatorStorage::Adaptive => {
                dense_bytes::<F>(dimension) < sparse_bytes::<F>(entries.len())
            }
        };

        if !dense {
            return Column::Sparse(entries.into_boxed_slice());
        }
        let mut values = vec![F::zero(); dimension];
        for (index, value) in entries {
            values[index] = value;
        }
        Column::Dense(values.into_boxed_slice())
    }

    /// Nonzero coefficients, which is what the entry budget counts.
    ///
    /// `O(D)` for a dense column, since the zeros have to be skipped over to be excluded. Called
    /// once per conversion, not per application.
    fn entries(&self) -> usize {
        match self {
            Column::Standard(_) => 0,
            Column::Sparse(entries) => entries.len(),
            Column::Dense(values) => values.iter().filter(|value| !value.is_zero()).count(),
        }
    }

    /// Field-element cells the representation allocates, zero or not.
    fn cells(&self) -> usize {
        match self {
            Column::Standard(_) => 0,
            Column::Sparse(entries) => entries.len(),
            Column::Dense(values) => values.len(),
        }
    }

    /// Heap bytes. Exact: a boxed slice has no capacity beyond its length.
    fn bytes(&self) -> usize {
        match self {
            Column::Standard(_) => 0,
            Column::Sparse(entries) => sparse_bytes::<F>(entries.len()),
            Column::Dense(values) => dense_bytes::<F>(values.len()),
        }
    }
}

/// What a sparse column of `entries` costs on the heap.
pub(super) fn sparse_bytes<F: FiniteField>(entries: usize) -> usize {
    entries * size_of::<(usize, F)>()
}

/// What a dense column in `dimension` dimensions costs on the heap.
pub(super) fn dense_bytes<F: FiniteField>(dimension: usize) -> usize {
    dimension * size_of::<F>()
}

/// `T_i : A -> A`, multiplication by one variable on `A = R/I`, in the standard monomial basis.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MultiplicationOperator<F: FiniteField> {
    columns: Vec<Column<F>>,
}

impl<F: FiniteField> MultiplicationOperator<F> {
    /// `D`, the dimension of the space the operator acts on.
    pub fn dimension(&self) -> usize {
        self.columns.len()
    }

    /// The operator applied to a coordinate vector.
    ///
    /// # Panics
    /// If `v` is not of length [`Self::dimension`]. A coordinate vector of the wrong length is a
    /// caller error that would otherwise give a silently truncated answer.
    pub fn apply(&self, v: &[F]) -> Vec<F> {
        assert_eq!(
            v.len(),
            self.columns.len(),
            "a coordinate vector of {} entries in a quotient algebra of dimension {}",
            v.len(),
            self.columns.len()
        );

        let mut result = vec![F::zero(); self.columns.len()];
        for (j, coefficient) in v.iter().enumerate() {
            // Skipped rather than multiplied: a quotient vector is often sparse, and for a
            // `Standard` column the whole contribution is one addition.
            if coefficient.is_zero() {
                continue;
            }
            match &self.columns[j] {
                // `+=` rather than `=`, though no earlier column can have written to `k`. If
                // column `j` is a unit vector at `k` then `b_k = x_i b_j`, and for any earlier
                // column `j'` the terms of `normal_form(x_i b_j')` are all strictly below
                // `x_i b_j'`, which is below `x_i b_j = b_k` because multiplying by a variable
                // preserves the order. So the slot is provably zero here — but the argument
                // depends on the basis being sorted ascending, and accumulating does not.
                Column::Standard(k) => result[*k] += *coefficient,
                Column::Sparse(entries) => {
                    for (k, value) in entries {
                        result[*k] += *coefficient * *value;
                    }
                }
                // Two sequential slices and no indices to follow, against `D` multiplications
                // where the sparse form does one per entry. Worth it exactly when the column is
                // dense enough that those are nearly the same number — which is the condition
                // `Adaptive` already selects on, for storage. Whether it is also the right
                // condition for *time* is what `benches/fglm.rs` measures.
                Column::Dense(values) => {
                    for (slot, value) in result.iter_mut().zip(values) {
                        *slot += *coefficient * *value;
                    }
                }
            }
        }
        result
    }

    /// Apply the transpose without materializing a dense matrix.
    pub(super) fn apply_transpose(&self, v: &[F]) -> Vec<F> {
        assert_eq!(
            v.len(),
            self.dimension(),
            "coordinate vector has wrong dimension"
        );
        self.columns
            .iter()
            .map(|column| match column {
                Column::Standard(k) => v[*k],
                Column::Sparse(entries) => entries
                    .iter()
                    .map(|(k, value)| v[*k] * *value)
                    .fold(F::zero(), |a, b| a + b),
                Column::Dense(values) => v
                    .iter()
                    .zip(values)
                    .map(|(a, b)| *a * *b)
                    .fold(F::zero(), |a, b| a + b),
            })
            .collect()
    }

    /// Column `j` as a dense coordinate vector: the matrix view.
    ///
    /// # Panics
    /// If `j` is not below [`Self::dimension`].
    pub fn column(&self, j: usize) -> Vec<F> {
        match &self.columns[j] {
            Column::Standard(k) => {
                let mut dense = vec![F::zero(); self.columns.len()];
                dense[*k] = F::one();
                dense
            }
            Column::Sparse(entries) => {
                let mut dense = vec![F::zero(); self.columns.len()];
                for (k, value) in entries {
                    dense[*k] = *value;
                }
                dense
            }
            // Already the answer, so no scatter: the representation a caller of this method wants
            // is the one the column is in.
            Column::Dense(values) => values.to_vec(),
        }
    }

    /// Nonzero coefficients across every column, which is what `max_operator_entries` counts.
    ///
    /// **Mathematical nonzeros, not allocated cells.** A dense column of a mostly-zero operator
    /// contributes its few nonzeros here and its whole length to [`Self::stored_cells`], which is
    /// why both exist. A unit-vector column contributes none to either.
    pub fn stored_entries(&self) -> usize {
        self.columns.iter().map(Column::entries).sum()
    }

    /// Field-element cells the columns allocate, zero or not.
    ///
    /// Equals [`Self::stored_entries`] when every reduced column is sparse, and exceeds it
    /// wherever one is dense.
    pub fn stored_cells(&self) -> usize {
        self.columns.iter().map(Column::cells).sum()
    }

    /// Bytes this operator's representation occupies, column spine included.
    ///
    /// Not the same as `stored_entries() * size_of::<(usize, F)>()`, in two directions: the spine
    /// costs one `Column` per column whether it stores anything or not, and a dense column costs
    /// cells rather than entries. The column heaps themselves are exact, since a boxed slice has
    /// no capacity to diverge from its length.
    ///
    /// Still an estimate of the representation and not a measurement of the process — it has no
    /// way to see the allocator's own per-allocation overhead. See
    /// [`FglmMemory`](super::FglmMemory) for the three quantities this is one of.
    pub fn stored_bytes(&self) -> usize {
        let spine = self.columns.capacity() * size_of::<Column<F>>();
        let heap: usize = self.columns.iter().map(Column::bytes).sum();
        spine + heap
    }

    /// How many columns are unit vectors, i.e. products that stayed inside the staircase.
    ///
    /// Reported because it is the property the representation is chosen for, so a caller can see
    /// whether it holds on their input rather than taking this module's word for it.
    pub fn standard_columns(&self) -> usize {
        self.columns
            .iter()
            .filter(|column| matches!(column, Column::Standard(_)))
            .count()
    }

    /// How many reduced columns are held densely.
    ///
    /// Zero under [`OperatorStorage::Sparse`], and under [`OperatorStorage::Adaptive`] the count of
    /// columns dense enough that a dense column was the smaller of the two.
    pub fn dense_columns(&self) -> usize {
        self.columns
            .iter()
            .filter(|column| matches!(column, Column::Dense(_)))
            .count()
    }
}

/// Builds one operator's columns in the representation it was asked for.
pub(super) struct OperatorBuilder<F: FiniteField> {
    columns: Vec<Column<F>>,
    dimension: usize,
    storage: OperatorStorage,
}

impl<F: FiniteField> OperatorBuilder<F> {
    pub(super) fn new(dimension: usize, storage: OperatorStorage) -> Self {
        Self {
            columns: Vec::with_capacity(dimension),
            dimension,
            storage,
        }
    }

    /// The product was itself a standard monomial, at `index`.
    pub(super) fn push_standard(&mut self, index: usize) {
        self.columns.push(Column::Standard(index));
    }

    /// The product reduced to `entries`, which must be ascending by index.
    ///
    /// Returns the bytes the stored column occupies, so a caller enforcing a byte budget does not
    /// have to re-derive which representation was chosen.
    pub(super) fn push_reduced(&mut self, entries: Vec<(usize, F)>) -> usize {
        let column = Column::build(entries, self.dimension, self.storage);
        let bytes = column.bytes();
        self.columns.push(column);
        bytes
    }

    pub(super) fn finish(self) -> MultiplicationOperator<F> {
        MultiplicationOperator {
            columns: self.columns,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{dense_bytes, sparse_bytes, Column, MultiplicationOperator, OperatorBuilder};
    use crate::{
        fields::Zp2147483647, grobner::fglm::options::OperatorStorage, FiniteField, One, Zero,
    };
    use std::mem::size_of;

    type F = Zp2147483647;

    const STORAGES: [OperatorStorage; 3] = [
        OperatorStorage::Sparse,
        OperatorStorage::Adaptive,
        OperatorStorage::Dense,
    ];

    /// An operator of the given columns, in the given representation.
    fn operator(
        dimension: usize,
        columns: &[Option<Vec<(usize, F)>>],
        storage: OperatorStorage,
    ) -> MultiplicationOperator<F> {
        let mut builder = OperatorBuilder::new(dimension, storage);
        for column in columns {
            match column {
                None => builder.push_standard(0),
                Some(entries) => {
                    builder.push_reduced(entries.clone());
                }
            }
        }
        builder.finish()
    }

    /// A column with a mixture of shapes: a unit vector, a zero, a sparse one, and a full one.
    fn mixed_columns() -> Vec<Option<Vec<(usize, F)>>> {
        vec![
            None,
            Some(Vec::new()),
            Some(vec![(1, F::new(3))]),
            Some((0..4).map(|k| (k, F::new(k as u64 + 7))).collect()),
        ]
    }

    /// Every representation gives the same columns and the same application.
    ///
    /// The whole correctness requirement for M18-3: the representation is a storage choice, so no
    /// observable answer may depend on it.
    #[test]
    fn test_every_representation_agrees() {
        let columns = mixed_columns();
        let reference = operator(4, &columns, OperatorStorage::Sparse);

        for storage in STORAGES {
            let operator = operator(4, &columns, storage);

            for j in 0..4 {
                assert_eq!(
                    operator.column(j),
                    reference.column(j),
                    "{:?}: column {} differs",
                    storage,
                    j
                );
            }

            // Dense, sparse and unit input vectors, since the application branches on the input's
            // zeros as well as on the column's representation.
            let probes: [Vec<F>; 4] = [
                vec![F::one(), F::zero(), F::zero(), F::zero()],
                vec![F::zero(), F::zero(), F::new(5), F::zero()],
                (0..4).map(|k| F::new(k as u64 + 1)).collect(),
                vec![F::zero(); 4],
            ];
            for probe in &probes {
                assert_eq!(
                    operator.apply(probe),
                    reference.apply(probe),
                    "{:?}: apply differs on {:?}",
                    storage,
                    probe
                );
            }

            // Nonzeros are a property of the column, not of how it is held.
            assert_eq!(
                operator.stored_entries(),
                reference.stored_entries(),
                "{:?}: the nonzero count depends on the representation",
                storage
            );
        }
    }

    /// `Sparse` holds no column densely and `Dense` holds every reduced column densely.
    #[test]
    fn test_the_storage_strategies_do_what_they_say() {
        let columns = mixed_columns();

        assert_eq!(
            operator(4, &columns, OperatorStorage::Sparse).dense_columns(),
            0
        );
        // Three reduced columns of the four; the first is a unit vector.
        assert_eq!(
            operator(4, &columns, OperatorStorage::Dense).dense_columns(),
            3
        );
    }

    /// `Adaptive` holds a column densely exactly when a dense column is the smaller of the two.
    #[test]
    fn test_adaptive_chooses_the_smaller_representation() {
        // At D = 4 a dense column is 32 bytes and a sparse entry is 16, so a column is held
        // densely from two entries up.
        assert_eq!(dense_bytes::<F>(4), 4 * size_of::<F>());
        assert_eq!(sparse_bytes::<F>(2), 2 * size_of::<(usize, F)>());

        let dense_of = |entries: usize| -> usize {
            let column: Vec<(usize, F)> = (0..entries).map(|k| (k, F::new(k as u64 + 1))).collect();
            operator(4, &[Some(column)], OperatorStorage::Adaptive).dense_columns()
        };

        assert_eq!(dense_of(0), 0, "an empty column should stay sparse");
        assert_eq!(dense_of(1), 0, "a one-entry column should stay sparse");
        assert_eq!(dense_of(2), 0, "a half-full column is a tie, so sparse");
        assert_eq!(
            dense_of(3),
            1,
            "a three-quarters-full column should be dense"
        );
        assert_eq!(dense_of(4), 1, "a full column should be dense");
    }

    /// A dense column costs cells where a sparse one costs entries, and both are reported.
    #[test]
    fn test_cells_and_entries_differ_only_for_a_dense_column() {
        let column: Vec<(usize, F)> = vec![(0, F::one()), (1, F::one()), (2, F::one())];

        let sparse = operator(4, &[Some(column.clone())], OperatorStorage::Sparse);
        assert_eq!(sparse.stored_entries(), 3);
        assert_eq!(sparse.stored_cells(), 3);

        let dense = operator(4, &[Some(column)], OperatorStorage::Dense);
        assert_eq!(
            dense.stored_entries(),
            3,
            "nonzeros are a property of the column"
        );
        assert_eq!(dense.stored_cells(), 4, "a dense column allocates D cells");
    }

    /// Bytes are the spine plus the heap, and the heap is what each representation really takes.
    ///
    /// The spine is the *capacity* of the column vector, which the builder sets to the dimension —
    /// so an operator built with one column of four still carries four columns' worth of spine.
    /// That is what the allocator was asked for and so what is reported.
    #[test]
    fn test_bytes_account_for_the_spine_and_the_heap() {
        let spine = 4 * size_of::<Column<F>>();
        let column: Vec<(usize, F)> = vec![(0, F::one()), (1, F::one()), (2, F::one())];

        let sparse = operator(4, &[Some(column.clone())], OperatorStorage::Sparse);
        assert_eq!(sparse.stored_bytes(), spine + 3 * size_of::<(usize, F)>());

        let dense = operator(4, &[Some(column)], OperatorStorage::Dense);
        assert_eq!(dense.stored_bytes(), spine + 4 * size_of::<F>());

        // A unit-vector column has no heap at all, so only the spine is left.
        let unit = operator(4, &[None], OperatorStorage::Adaptive);
        assert_eq!(unit.stored_bytes(), spine);
    }

    /// A column costs two words of spine, not three.
    ///
    /// The reason the variants hold boxed slices. At `N * D` columns the difference between a
    /// 24-byte and a 32-byte `Column` is 80 kB on planted-10, which is more than the entries of
    /// that instance's operators come to.
    #[test]
    fn test_a_column_is_three_words() {
        assert_eq!(size_of::<Column<F>>(), 3 * size_of::<usize>());
    }

    /// A zero column allocates nothing, whichever strategy is in force.
    ///
    /// §7.2 of the milestone proposal asks for a compact representation of a zero column. The
    /// sparse form already is one — an empty `Vec` allocates no heap — and `Adaptive` reaches it,
    /// since zero entries are always the cheaper side of the comparison.
    #[test]
    fn test_a_zero_column_allocates_nothing() {
        // Full width, so the operator can be applied: every one of the eight columns is zero.
        let columns: Vec<Option<Vec<(usize, F)>>> = (0..8).map(|_| Some(Vec::new())).collect();
        for storage in [OperatorStorage::Sparse, OperatorStorage::Adaptive] {
            let zero = operator(8, &columns, storage);
            assert_eq!(
                zero.stored_bytes(),
                8 * size_of::<Column<F>>(),
                "{:?}: a zero column allocated heap beyond the spine",
                storage
            );
            assert_eq!(zero.stored_entries(), 0);
            assert_eq!(zero.stored_cells(), 0);
            assert!(
                zero.apply(&[F::one(); 8]).iter().all(|v| v.is_zero()),
                "{:?}: the zero operator did not annihilate",
                storage
            );
        }
    }

    /// The zero-dimensional operator of the unit ideal has no columns and no storage.
    #[test]
    fn test_the_empty_operator_is_empty() {
        for storage in STORAGES {
            let empty = operator(0, &[], storage);
            assert_eq!(empty.dimension(), 0);
            assert_eq!(empty.stored_entries(), 0);
            assert_eq!(empty.stored_cells(), 0);
            assert!(empty.apply(&[]).is_empty());
        }
    }

    /// `push_reduced` reports the bytes the column it stored occupies.
    ///
    /// The byte budget is enforced from this, so a wrong figure would make the budget wrong rather
    /// than merely the report.
    #[test]
    fn test_push_reduced_reports_the_bytes_it_stored() {
        let entries: Vec<(usize, F)> = vec![(0, F::one()), (1, F::one()), (2, F::one())];

        let mut sparse = OperatorBuilder::<F>::new(4, OperatorStorage::Sparse);
        assert_eq!(
            sparse.push_reduced(entries.clone()),
            3 * size_of::<(usize, F)>()
        );

        let mut dense = OperatorBuilder::<F>::new(4, OperatorStorage::Dense);
        assert_eq!(dense.push_reduced(entries), 4 * size_of::<F>());

        let mut unit = OperatorBuilder::<F>::new(4, OperatorStorage::Adaptive);
        unit.push_standard(2);
        assert_eq!(unit.finish().stored_bytes(), 4 * size_of::<Column<F>>());
    }
    // Transposition preserves the dot-product duality for standard, zero, sparse and dense columns.
    #[test]
    fn test_transpose_duality_in_every_storage() {
        let u = [F::new(2), F::new(3), F::new(5), F::new(7)];
        let v = [F::new(11), F::new(13), F::new(17), F::new(19)];
        for storage in STORAGES {
            let op = operator(4, &mixed_columns(), storage);
            let left: F = u
                .iter()
                .zip(op.apply(&v))
                .map(|(a, b)| *a * b)
                .fold(F::zero(), |a, b| a + b);
            let right: F = op
                .apply_transpose(&u)
                .iter()
                .zip(v)
                .map(|(a, b)| *a * b)
                .fold(F::zero(), |a, b| a + b);
            assert_eq!(left, right);
            for j in 0..4 {
                let expected: F = op
                    .column(j)
                    .iter()
                    .zip(u)
                    .map(|(a, b)| *a * b)
                    .fold(F::zero(), |a, b| a + b);
                assert_eq!(op.apply_transpose(&u)[j], expected);
            }
        }
    }

    // Transposed application rejects a coordinate vector from a different space.
    #[test]
    #[should_panic(expected = "coordinate vector")]
    fn test_transpose_rejects_wrong_dimension() {
        operator(4, &mixed_columns(), OperatorStorage::Adaptive).apply_transpose(&[]);
    }
}
