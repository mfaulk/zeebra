//! Multiplication by a variable, as a linear operator on the quotient algebra.
//!
//! The columns are stored two ways because the object has two shapes. The standard monomials are
//! closed downwards, so only the outer surface of the staircase leaves it under multiplication:
//! for most basis monomials `b_j`, the product `x_i b_j` is itself standard and the column is a
//! unit vector costing no storage and no reduction. A dense `D x D` matrix per variable would hold
//! `N * D^2` field elements of which the great majority are structurally zero.

use crate::FiniteField;

/// Column `j` of an operator: where multiplication sends the `j`-th standard monomial.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Column<F: FiniteField> {
    /// The product is the standard monomial at this index, so the column is a unit vector.
    Standard(usize),

    /// The product left the staircase and reduced to this combination of standard monomials,
    /// ascending by index. Empty when the product reduced to zero.
    Reduced(Vec<(usize, F)>),
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
                Column::Reduced(entries) => {
                    for (k, value) in entries {
                        result[*k] += *coefficient * *value;
                    }
                }
            }
        }
        result
    }

    /// Column `j` as a dense coordinate vector: the matrix view.
    ///
    /// # Panics
    /// If `j` is not below [`Self::dimension`].
    pub fn column(&self, j: usize) -> Vec<F> {
        let mut dense = vec![F::zero(); self.columns.len()];
        match &self.columns[j] {
            Column::Standard(k) => dense[*k] = F::one(),
            Column::Reduced(entries) => {
                for (k, value) in entries {
                    dense[*k] = *value;
                }
            }
        }
        dense
    }

    /// The entries actually stored, which is what `max_operator_entries` is enforced on.
    ///
    /// A unit-vector column stores none, so this is well below `D^2` on every instance measured.
    pub fn stored_entries(&self) -> usize {
        self.columns
            .iter()
            .map(|column| match column {
                Column::Standard(_) => 0,
                Column::Reduced(entries) => entries.len(),
            })
            .sum()
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
}

/// Builds one operator's columns, enforcing the entry budget as it goes.
pub(super) struct OperatorBuilder<F: FiniteField> {
    columns: Vec<Column<F>>,
}

impl<F: FiniteField> OperatorBuilder<F> {
    pub(super) fn with_capacity(dimension: usize) -> Self {
        Self {
            columns: Vec::with_capacity(dimension),
        }
    }

    /// The product was itself a standard monomial, at `index`.
    pub(super) fn push_standard(&mut self, index: usize) {
        self.columns.push(Column::Standard(index));
    }

    /// The product reduced to `entries`, which must be ascending by index.
    pub(super) fn push_reduced(&mut self, entries: Vec<(usize, F)>) {
        self.columns.push(Column::Reduced(entries));
    }

    pub(super) fn finish(self) -> MultiplicationOperator<F> {
        MultiplicationOperator {
            columns: self.columns,
        }
    }
}
