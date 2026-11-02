//! A sparse row of a finite-field matrix.
//!
//! The representation is a vector of `(column, coefficient)` pairs sorted by column, with no
//! duplicates and no zero coefficients, so an empty row is the zero vector. Every operation here
//! preserves that, and `debug_assert` checks it.
//!
//! A sorted vector rather than a `HashMap` per row: elimination subtracts one whole row from
//! another, which two sorted vectors do in a single linear pass over sequential memory, and the
//! leading column — the operation Gröbner reduction asks for most — is the first element.

use crate::FiniteField;

/// A sparse row: the columns holding a nonzero coefficient, in increasing column order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SparseRow<F: FiniteField> {
    entries: Vec<(usize, F)>,
}

impl<F: FiniteField> SparseRow<F> {
    /// The zero row.
    pub fn zero() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// A row from arbitrary entries, which are sorted, merged, and stripped of zeros.
    ///
    /// Duplicate columns are summed, as they are in a polynomial's terms, so that a caller need
    /// not canonicalize first.
    pub fn new(entries: &[(usize, F)]) -> Self {
        let mut entries = entries.to_vec();
        entries.sort_by_key(|(column, _)| *column);

        let mut merged: Vec<(usize, F)> = Vec::with_capacity(entries.len());
        for (column, coefficient) in entries {
            match merged.last_mut() {
                Some((last, accumulated)) if *last == column => *accumulated += coefficient,
                _ => merged.push((column, coefficient)),
            }
        }
        merged.retain(|(_, coefficient)| !coefficient.is_zero());

        Self { entries: merged }
    }

    /// A row from entries that are already sorted by column, deduplicated, and nonzero.
    ///
    /// Avoids the sort [`SparseRow::new`] performs, for a caller that already has canonical data.
    ///
    /// # Errors
    /// [`NotCanonical`] if the entries are not strictly increasing by column, or if any
    /// coefficient is zero. Validated in every build, not only in debug: a row that violates the
    /// invariant makes `is_zero` wrong, makes the merge in `subtract_scaled` wrong, and lets
    /// [`SparseMatrix::new`](super::SparseMatrix::new) accept out-of-range columns, since that
    /// relies on the last stored column being the largest.
    pub fn from_sorted(entries: Vec<(usize, F)>) -> Result<Self, NotCanonical> {
        let row = Self { entries };
        match row.first_violation() {
            Some(violation) => Err(violation),
            None => Ok(row),
        }
    }

    /// As [`SparseRow::from_sorted`], without the validation.
    ///
    /// Crate-internal, for the paths that generate the entries themselves and so cannot produce a
    /// non-canonical row: a polynomial's terms shifted by a monomial are distinct and nonzero, and
    /// a monomial order is multiplicative, so sorting the terms sorts the columns. Validated by
    /// `debug_assert`, which is what makes that reasoning testable rather than merely asserted.
    pub(crate) fn from_sorted_unchecked(entries: Vec<(usize, F)>) -> Self {
        let row = Self { entries };
        debug_assert_eq!(
            row.first_violation(),
            None,
            "{:?} is not canonical",
            row.entries
        );
        row
    }

    /// The nonzero entries, in increasing column order.
    pub fn entries(&self) -> &[(usize, F)] {
        &self.entries
    }

    /// The number of nonzero entries.
    pub fn nonzeros(&self) -> usize {
        self.entries.len()
    }

    /// True if every coefficient is zero, i.e. no entry is stored.
    pub fn is_zero(&self) -> bool {
        self.entries.is_empty()
    }

    /// The leftmost column holding a nonzero coefficient, or `None` for the zero row.
    pub fn leading_column(&self) -> Option<usize> {
        self.entries.first().map(|(column, _)| *column)
    }

    /// The coefficient in the leftmost nonzero column, or `None` for the zero row.
    pub fn leading_coefficient(&self) -> Option<F> {
        self.entries.first().map(|(_, coefficient)| *coefficient)
    }

    /// The coefficient in the given column, which is zero when no entry is stored for it.
    pub fn coefficient(&self, column: usize) -> F {
        match self
            .entries
            .binary_search_by_key(&column, |(index, _)| *index)
        {
            Ok(position) => self.entries[position].1,
            Err(_) => F::zero(),
        }
    }

    /// The largest column index holding a nonzero coefficient, or `None` for the zero row.
    pub fn trailing_column(&self) -> Option<usize> {
        self.entries.last().map(|(column, _)| *column)
    }

    /// Multiply every coefficient by `factor`.
    ///
    /// # Panics
    /// If `factor` is zero, which would silently discard the row rather than scale it. Use
    /// `SparseRow::zero` to construct the zero row.
    pub fn scale(&mut self, factor: &F) {
        assert!(!factor.is_zero(), "scaling by zero is not a row operation");
        for (_, coefficient) in self.entries.iter_mut() {
            *coefficient *= *factor;
        }
    }

    /// Scale the row so that its leading coefficient is one.
    ///
    /// Returns `true` if a modular inverse was computed, which is the cost worth counting: a row
    /// whose pivot is already one needs no arithmetic at all, and in F4 most do not, because the
    /// basis elements the rows are built from are monic.
    pub fn normalize(&mut self) -> bool {
        let Some(coefficient) = self.leading_coefficient() else {
            return false;
        };
        if coefficient == F::ONE {
            return false;
        }

        // One inverse for the row, not one division per entry. `Div` on a field element is
        // multiplication by `inverse()`, and `inverse()` is a modular exponentiation of about
        // log2(q) multiplications.
        let inverse = coefficient.inverse();
        for (_, entry) in self.entries.iter_mut() {
            *entry *= inverse;
        }
        debug_assert_eq!(self.leading_coefficient(), Some(F::ONE));
        true
    }

    /// `self -= factor * other`, using `scratch` as the merge buffer.
    ///
    /// Both rows are sorted by column, so this is a two-pointer merge: linear in the two lengths,
    /// writing sequentially into a buffer the caller reuses across operations rather than
    /// allocating one per row operation. Columns that cancel are dropped, which is what keeps the
    /// representation canonical and lets `is_zero` be a length test.
    pub fn subtract_scaled(&mut self, other: &Self, factor: &F, scratch: &mut Vec<(usize, F)>) {
        if factor.is_zero() || other.is_zero() {
            return;
        }

        scratch.clear();
        scratch.reserve(self.entries.len() + other.entries.len());

        let mut i = 0;
        let mut j = 0;
        while i < self.entries.len() && j < other.entries.len() {
            let (own_column, own_coefficient) = self.entries[i];
            let (other_column, other_coefficient) = other.entries[j];
            if own_column < other_column {
                scratch.push((own_column, own_coefficient));
                i += 1;
            } else if own_column > other_column {
                scratch.push((other_column, F::zero() - *factor * other_coefficient));
                j += 1;
            } else {
                let merged = own_coefficient - *factor * other_coefficient;
                if !merged.is_zero() {
                    scratch.push((own_column, merged));
                }
                i += 1;
                j += 1;
            }
        }
        scratch.extend_from_slice(&self.entries[i..]);
        for (column, coefficient) in &other.entries[j..] {
            scratch.push((*column, F::zero() - *factor * *coefficient));
        }

        std::mem::swap(&mut self.entries, scratch);
        debug_assert!(self.is_canonical(), "{:?} is not canonical", self.entries);
    }

    /// The row as a dense vector of `num_columns` coefficients.
    ///
    /// # Panics
    /// If any stored column is outside the given width.
    pub fn to_dense(&self, num_columns: usize) -> Vec<F> {
        let mut dense = vec![F::zero(); num_columns];
        for (column, coefficient) in &self.entries {
            assert!(
                *column < num_columns,
                "column {} is outside a width of {}",
                column,
                num_columns
            );
            dense[*column] = *coefficient;
        }
        dense
    }

    /// A row from a dense vector of coefficients, keeping only the nonzero ones.
    pub fn from_dense(coefficients: &[F]) -> Self {
        // Enumerating a slice yields strictly increasing indices and the zeros are filtered out,
        // so the result is canonical by construction.
        Self::from_sorted_unchecked(
            coefficients
                .iter()
                .enumerate()
                .filter(|(_, coefficient)| !coefficient.is_zero())
                .map(|(column, coefficient)| (column, *coefficient))
                .collect(),
        )
    }

    /// The first way these entries break the representation invariant, if they do.
    fn first_violation(&self) -> Option<NotCanonical> {
        if let Some((column, _)) = self
            .entries
            .iter()
            .find(|(_, coefficient)| coefficient.is_zero())
        {
            return Some(NotCanonical::ZeroCoefficient { column: *column });
        }
        for pair in self.entries.windows(2) {
            if pair[0].0 == pair[1].0 {
                return Some(NotCanonical::DuplicateColumn { column: pair[0].0 });
            }
            if pair[0].0 > pair[1].0 {
                return Some(NotCanonical::OutOfOrder {
                    column: pair[0].0,
                    followed_by: pair[1].0,
                });
            }
        }
        None
    }

    /// True if the entries are strictly increasing by column and all nonzero.
    pub(crate) fn is_canonical(&self) -> bool {
        self.first_violation().is_none()
    }
}

/// Why a sequence of entries is not a valid sparse row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NotCanonical {
    /// A stored coefficient was zero. An omitted entry is the only representation of zero, so a
    /// stored zero would make `is_zero` disagree with the row's value.
    ZeroCoefficient { column: usize },

    /// The same column appeared twice.
    DuplicateColumn { column: usize },

    /// A column was followed by a smaller one.
    OutOfOrder { column: usize, followed_by: usize },
}

impl std::fmt::Display for NotCanonical {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ZeroCoefficient { column } => {
                write!(f, "column {} holds a zero coefficient", column)
            }
            Self::DuplicateColumn { column } => write!(f, "column {} appears twice", column),
            Self::OutOfOrder {
                column,
                followed_by,
            } => write!(f, "column {} is followed by {}", column, followed_by),
        }
    }
}

impl std::error::Error for NotCanonical {}

#[cfg(test)]
mod tests {
    use super::NotCanonical;
    use super::SparseRow;
    use crate::{fields::Zp13, FiniteField, One, Zero};

    type F = Zp13;

    /// The zero row stores nothing and reports no leading column.
    #[test]
    fn test_zero_row() {
        let row = SparseRow::<F>::zero();
        assert!(row.is_zero());
        assert_eq!(row.nonzeros(), 0);
        assert_eq!(row.leading_column(), None);
        assert_eq!(row.leading_coefficient(), None);
        assert_eq!(row.trailing_column(), None);
        assert_eq!(row.coefficient(0), F::zero());
    }

    /// `new` sorts entries by column, merges duplicates, and drops zero coefficients.
    #[test]
    fn test_new_canonicalizes() {
        let row = SparseRow::new(&[
            (5, F::new(3)),
            (1, F::new(2)),
            (5, F::new(4)), // merges with the other column 5 to give 7
            (3, F::zero()), // dropped
            (9, F::new(6)),
            (9, F::new(7)), // 6 + 7 = 13 = 0, so column 9 disappears entirely
        ]);
        assert_eq!(
            row.entries(),
            &[(1, F::new(2)), (5, F::new(7))],
            "{:?}",
            row
        );
    }

    /// Accessors read the leading, trailing, and arbitrary columns.
    #[test]
    fn test_accessors() {
        let row = SparseRow::new(&[(2, F::new(5)), (7, F::new(11))]);
        assert_eq!(row.leading_column(), Some(2));
        assert_eq!(row.leading_coefficient(), Some(F::new(5)));
        assert_eq!(row.trailing_column(), Some(7));
        assert_eq!(row.coefficient(2), F::new(5));
        assert_eq!(row.coefficient(7), F::new(11));
        // A column with no stored entry reads as zero rather than panicking.
        assert_eq!(row.coefficient(0), F::zero());
        assert_eq!(row.coefficient(5), F::zero());
        assert_eq!(row.coefficient(1000), F::zero());
    }

    /// Scaling multiplies every coefficient and keeps the support unchanged.
    #[test]
    fn test_scale() {
        let mut row = SparseRow::new(&[(0, F::new(1)), (4, F::new(2))]);
        row.scale(&F::new(3));
        assert_eq!(row.entries(), &[(0, F::new(3)), (4, F::new(6))]);
        assert_eq!(row.nonzeros(), 2, "scaling cannot change the support");
    }

    /// Scaling by zero is rejected rather than silently emptying the row.
    #[test]
    #[should_panic(expected = "scaling by zero")]
    fn test_scale_by_zero_panics() {
        let mut row = SparseRow::new(&[(0, F::new(1))]);
        row.scale(&F::zero());
    }

    /// Normalizing divides through by the leading coefficient and reports the inverse it needed.
    #[test]
    fn test_normalize() {
        // 5 inverse mod 13 is 8, since 5*8 = 40 = 1.
        let mut row = SparseRow::new(&[(1, F::new(5)), (3, F::new(2))]);
        assert!(row.normalize(), "an inverse was required");
        assert_eq!(row.leading_coefficient(), Some(F::ONE));
        // 2 * 8 = 16 = 3 mod 13.
        assert_eq!(row.entries(), &[(1, F::ONE), (3, F::new(3))]);

        // A row whose pivot is already one needs no arithmetic, which is the case worth skipping.
        let mut monic = SparseRow::new(&[(1, F::ONE), (3, F::new(7))]);
        let before = monic.clone();
        assert!(!monic.normalize(), "no inverse should have been computed");
        assert_eq!(monic, before);

        // The zero row has no pivot to normalize.
        let mut zero = SparseRow::<F>::zero();
        assert!(!zero.normalize());
        assert!(zero.is_zero());
    }

    /// Subtracting a scaled row merges supports and drops columns that cancel.
    #[test]
    fn test_subtract_scaled() {
        let mut scratch = Vec::new();

        // Disjoint supports interleave, and nothing cancels.
        let mut row = SparseRow::new(&[(0, F::new(1)), (4, F::new(1))]);
        let other = SparseRow::new(&[(2, F::new(1)), (6, F::new(1))]);
        row.subtract_scaled(&other, &F::new(1), &mut scratch);
        assert_eq!(
            row.entries(),
            &[
                (0, F::new(1)),
                (2, F::new(12)),
                (4, F::new(1)),
                (6, F::new(12))
            ]
        );

        // An exact multiple cancels to the zero row.
        let mut row = SparseRow::new(&[(1, F::new(6)), (3, F::new(9))]);
        let other = SparseRow::new(&[(1, F::new(2)), (3, F::new(3))]);
        row.subtract_scaled(&other, &F::new(3), &mut scratch);
        assert!(row.is_zero(), "{:?}", row);

        // A single shared column cancels and leaves the rest.
        let mut row = SparseRow::new(&[(1, F::new(4)), (5, F::new(7))]);
        let other = SparseRow::new(&[(1, F::new(2)), (9, F::new(1))]);
        row.subtract_scaled(&other, &F::new(2), &mut scratch);
        assert_eq!(row.entries(), &[(5, F::new(7)), (9, F::new(11))]);
    }

    /// Subtracting by a zero factor, or subtracting the zero row, changes nothing.
    #[test]
    fn test_subtract_scaled_no_ops() {
        let mut scratch = Vec::new();
        let original = SparseRow::new(&[(1, F::new(4)), (5, F::new(7))]);

        let mut row = original.clone();
        row.subtract_scaled(&SparseRow::new(&[(1, F::new(2))]), &F::zero(), &mut scratch);
        assert_eq!(row, original);

        let mut row = original.clone();
        row.subtract_scaled(&SparseRow::zero(), &F::new(5), &mut scratch);
        assert_eq!(row, original);
    }

    /// Subtracting a row from itself with factor one is the zero row, for any support shape.
    #[test]
    fn test_subtract_self_is_zero() {
        let mut scratch = Vec::new();
        for entries in [
            vec![(0, F::new(1))],
            vec![(0, F::new(3)), (1, F::new(4))],
            vec![(7, F::new(12))],
            vec![(0, F::new(1)), (100, F::new(2)), (1000, F::new(3))],
        ] {
            let row = SparseRow::new(&entries);
            let mut copy = row.clone();
            copy.subtract_scaled(&row, &F::ONE, &mut scratch);
            assert!(copy.is_zero(), "{:?} did not cancel itself", row);
        }
    }

    /// Dense and sparse representations round-trip.
    #[test]
    fn test_dense_round_trip() {
        let dense = vec![F::zero(), F::new(3), F::zero(), F::zero(), F::new(7)];
        let row = SparseRow::from_dense(&dense);
        assert_eq!(row.nonzeros(), 2);
        assert_eq!(row.to_dense(5), dense);

        // An all-zero dense vector is the zero row, which widens back to any width.
        let zero = SparseRow::<F>::from_dense(&[F::zero(); 4]);
        assert!(zero.is_zero());
        assert_eq!(zero.to_dense(4), vec![F::zero(); 4]);
    }

    /// Widening a row below its largest column is rejected rather than truncating silently.
    #[test]
    #[should_panic(expected = "outside a width")]
    fn test_to_dense_too_narrow_panics() {
        let row = SparseRow::new(&[(0, F::new(1)), (9, F::new(1))]);
        let _ = row.to_dense(5);
    }

    /// `from_sorted` accepts canonical entries and names what is wrong with the rest.
    ///
    /// Validated in release as well as debug. A non-canonical row would make `is_zero` wrong, make
    /// the merge in `subtract_scaled` wrong, and let `SparseMatrix::new` accept an out-of-range
    /// column, since that range-checks only the last stored entry.
    #[test]
    fn test_from_sorted_validates() {
        assert_eq!(
            SparseRow::from_sorted(vec![(1, F::new(2)), (4, F::new(3))])
                .expect("canonical")
                .entries(),
            &[(1, F::new(2)), (4, F::new(3))]
        );
        // The zero row is canonical.
        assert!(SparseRow::<F>::from_sorted(vec![])
            .expect("canonical")
            .is_zero());

        assert_eq!(
            SparseRow::from_sorted(vec![(5, F::new(1)), (2, F::new(1))]),
            Err(NotCanonical::OutOfOrder {
                column: 5,
                followed_by: 2
            })
        );
        assert_eq!(
            SparseRow::from_sorted(vec![(2, F::new(1)), (2, F::new(1))]),
            Err(NotCanonical::DuplicateColumn { column: 2 })
        );
        assert_eq!(
            SparseRow::from_sorted(vec![(2, F::zero())]),
            Err(NotCanonical::ZeroCoefficient { column: 2 })
        );
    }

    /// The rejection reasons describe themselves, since they reach a caller as an error.
    #[test]
    fn test_not_canonical_messages() {
        assert!(NotCanonical::ZeroCoefficient { column: 7 }
            .to_string()
            .contains('7'));
        assert!(NotCanonical::DuplicateColumn { column: 7 }
            .to_string()
            .contains('7'));
        assert!(NotCanonical::OutOfOrder {
            column: 7,
            followed_by: 3
        }
        .to_string()
        .contains('3'));
    }

    /// An out-of-range column cannot slip past `SparseMatrix::new` by being stored out of order.
    ///
    /// Regression test: the matrix range-checks only the last stored entry, so the row
    /// `[(9, 1), (1, 1)]` would have passed a width of five had `from_sorted` not rejected it.
    #[test]
    fn test_unsorted_row_cannot_hide_an_out_of_range_column() {
        assert!(SparseRow::from_sorted(vec![(9, F::new(1)), (1, F::new(1))]).is_err());
    }
}
