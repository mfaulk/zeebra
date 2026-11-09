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

    /// Entries the row's buffer is *allocated* for, which is what the allocator holds.
    ///
    /// Apart from [`SparseRow::nonzeros`] because the two diverge and the difference is paid in
    /// resident memory. The gap was **11.44x** on `katsura-11`'s interreduction matrix while
    /// [`SparseRow::subtract_scaled`] installed the merge buffer in the row; it is **1.81x** there
    /// since #554 copies the result back instead — see `docs/research/f4-resource-scaling.md` §§12
    /// and 13. What remains is the row's own growth history: a `Vec` that doubled and then
    /// cancelled down is still resident at its doubled size, and nothing shrinks it.
    pub fn capacity(&self) -> usize {
        self.entries.capacity()
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
    ///
    /// # Why the result is copied back rather than swapped in (#554)
    ///
    /// `scratch` stays the caller's. The merge result is copied into the row's own buffer, which
    /// costs one sequential `memcpy` of the merged length over a `std::mem::swap`.
    ///
    /// The swap is what the 11.44x of `docs/research/f4-resource-scaling.md` §12 was, and the
    /// mechanism is not that the reservation is too large — the merge genuinely may need
    /// `self.len() + other.len()` slots. It is that handing the reserved buffer to the row leaves
    /// `scratch` holding the row's *old* one, so `scratch` has to regrow at the next merge, and its
    /// high-water capacity is then installed in whichever row is merged next however short that
    /// merge is. One long merge early in a pass therefore sizes every later row's buffer: on
    /// `mq-random-10` 37.4 MB of payload was held in 678.8 MB of capacity. Copying back keeps one
    /// grown buffer instead of one per row, and bounds a row's capacity by `Vec`'s own doubling
    /// against its own high-water length rather than by the longest pivot in the pass.
    ///
    /// The copy is not a cost: it replaces an allocation it was already paying, and §13 measures the
    /// interreduction stage **1.9% to 6.6% faster** than the swap on all four rungs it was taken on,
    /// at 2.3x to 4.8x less resident memory.
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

        self.entries.clear();
        self.entries.extend_from_slice(scratch);
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
    use crate::{
        fields::{Zp13, Zp18446744073709551557, Zp2, Zp2147483647, Zp32003},
        FiniteField, One, Zero,
    };
    use rand::{prelude::StdRng, Rng, SeedableRng};

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

    /// One `(self, other, factor)` case, chosen to drive a named corner of the merge.
    ///
    /// The shapes are the ones that decide how much of the worst-case reservation is written:
    /// disjoint supports write all of it, a full overlap writes half or less, and a cancellation
    /// writes none.
    fn merge_case<G: FiniteField>(
        shape: usize,
        rng: &mut StdRng,
    ) -> (SparseRow<G>, SparseRow<G>, G) {
        let coefficient = |rng: &mut StdRng| {
            // Nonzero, so the rows stay canonical; drawn narrow so that small fields cancel often.
            let mut value = G::new(rng.gen_range(1..64));
            while value.is_zero() {
                value = G::new(rng.gen_range(1..64));
            }
            value
        };
        let factor = coefficient(rng);
        let width = rng.gen_range(1..40);
        let support = |stride: usize, offset: usize| {
            (0..width).map(|k| offset + stride * k).collect::<Vec<_>>()
        };
        let row = |columns: &[usize], rng: &mut StdRng| {
            SparseRow::<G>::new(
                &columns
                    .iter()
                    .map(|column| (*column, coefficient(rng)))
                    .collect::<Vec<_>>(),
            )
        };

        match shape % 9 {
            // Disjoint supports: nothing cancels and the merge writes every reserved slot.
            0 => {
                let own = row(&support(2, 0), rng);
                let other = row(&support(2, 1), rng);
                (own, other, factor)
            }
            // Identical supports: every column is a candidate for cancellation.
            1 => {
                let columns = support(3, 0);
                (row(&columns, rng), row(&columns, rng), factor)
            }
            // An exact multiple, which cancels to the zero row.
            2 => {
                let own = row(&support(1, 0), rng);
                let mut other = own.clone();
                other.scale(&factor.inverse());
                (own, other, factor)
            }
            // The leading column cancels and the rest of the supports are disjoint, so the result's
            // leading column moves right.
            3 => {
                let mut own_columns = vec![0usize];
                own_columns.extend(support(2, 2));
                let mut other_columns = vec![0usize];
                other_columns.extend(support(2, 3));
                let mut own = row(&own_columns, rng);
                let other = row(&other_columns, rng);
                let shared = other.coefficient(0) * factor;
                let entries: Vec<(usize, G)> = own
                    .entries()
                    .iter()
                    .map(|(column, value)| (*column, if *column == 0 { shared } else { *value }))
                    .collect();
                own = SparseRow::from_sorted(entries).expect("canonical");
                (own, other, factor)
            }
            // The zero row on either side, and on both.
            4 => (SparseRow::zero(), row(&support(1, 0), rng), factor),
            5 => (row(&support(1, 0), rng), SparseRow::zero(), factor),
            6 => (SparseRow::zero(), SparseRow::zero(), factor),
            // Random supports with a random overlap.
            7 => {
                let own: Vec<usize> = (0..width).map(|_| rng.gen_range(0..64)).collect();
                let other: Vec<usize> = (0..width).map(|_| rng.gen_range(0..64)).collect();
                (row(&own, rng), row(&other, rng), factor)
            }
            // One support contained in the other, in both directions over the case sequence.
            _ => {
                let long = support(1, 0);
                let short: Vec<usize> = long.iter().copied().step_by(3).collect();
                let (a, b) = (row(&long, rng), row(&short, rng));
                if shape.is_multiple_of(2) {
                    (a, b, factor)
                } else {
                    (b, a, factor)
                }
            }
        }
    }

    /// `subtract_scaled` agrees entry for entry with a dense reference, over one field.
    ///
    /// The reference shares only the field arithmetic: it widens both rows, subtracts coefficient
    /// by coefficient at an index, and narrows the result, so it exercises none of the merge's
    /// two-pointer logic, its cancellation test, or its buffer policy. Field arithmetic is exact,
    /// so agreement is bit-identity and not a tolerance.
    fn merge_agrees_with_a_dense_reference<G: FiniteField>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut scratch = Vec::new();

        for shape in 0..360 {
            let (own, other, factor) = merge_case::<G>(shape, &mut rng);
            let width = own
                .trailing_column()
                .unwrap_or(0)
                .max(other.trailing_column().unwrap_or(0))
                + 1;

            let mut dense = own.to_dense(width);
            for (column, coefficient) in other.entries() {
                dense[*column] -= factor * *coefficient;
            }
            let expected = SparseRow::from_dense(&dense);

            let mut row = own.clone();
            row.subtract_scaled(&other, &factor, &mut scratch);
            assert_eq!(
                row.entries(),
                expected.entries(),
                "shape {} over {} entries: {:?} - {:?} * {:?}",
                shape,
                width,
                own.entries(),
                factor,
                other.entries()
            );
        }
    }

    /// The merge is bit-identical to a dense reference over fields of five different widths.
    ///
    /// Across characteristics because the cancellation rate is a function of the field: over GF(2)
    /// a shared column cancels half the time, over a 61-bit prime almost never, and the merge's
    /// shortest and longest outputs are those two ends.
    #[test]
    fn test_subtract_scaled_matches_a_dense_reference() {
        merge_agrees_with_a_dense_reference::<Zp2>(11);
        merge_agrees_with_a_dense_reference::<Zp13>(12);
        merge_agrees_with_a_dense_reference::<Zp32003>(13);
        merge_agrees_with_a_dense_reference::<Zp2147483647>(14);
        merge_agrees_with_a_dense_reference::<Zp18446744073709551557>(15);
    }

    /// A short merge does not inherit the buffer an earlier long merge grew.
    ///
    /// The invariant #554 is about, and it locates the mechanism more precisely than "the reserve
    /// is too large": the reserve is for the merge the caller asked for, but installing that buffer
    /// in the row leaves the *scratch* holding the row's old one, so the scratch's high-water
    /// capacity is handed to whichever row is merged next, however short that merge is. One long
    /// merge early in a pass therefore sizes every later row's buffer.
    ///
    /// The bound allows `Vec`'s amortized doubling, which is growth the row is entitled to.
    #[test]
    fn test_a_short_merge_does_not_inherit_a_long_merges_buffer() {
        let mut scratch = Vec::new();

        // One long merge, to put a large capacity in play.
        let mut long =
            SparseRow::from_sorted((0..512).map(|column| (2 * column, F::new(1))).collect())
                .expect("canonical");
        let other_long =
            SparseRow::from_sorted((0..512).map(|column| (2 * column + 1, F::new(1))).collect())
                .expect("canonical");
        long.subtract_scaled(&other_long, &F::ONE, &mut scratch);
        assert_eq!(long.nonzeros(), 1024);

        // Then a short one, between two two-entry rows.
        let mut row = SparseRow::new(&[(3, F::new(4)), (9, F::new(5))]);
        let short = SparseRow::new(&[(3, F::new(2)), (11, F::new(6))]);
        let before = row.capacity();
        row.subtract_scaled(&short, &F::new(2), &mut scratch);

        let allowed = (2 * before).max(2 * row.nonzeros()).max(4);
        assert!(
            row.capacity() <= allowed,
            "a {}-entry row holds capacity for {} after a merge whose worst case was {}",
            row.nonzeros(),
            row.capacity(),
            before + short.nonzeros()
        );
    }

    /// The scratch buffer stays with the caller, so capacity does not migrate into the rows.
    ///
    /// The mechanism behind the 11.44x of `docs/research/f4-resource-scaling.md` §12 is not the
    /// reserve on its own but the reserve *plus* installing that buffer in the row: the caller's
    /// scratch is then the row's old buffer, so the next merge reserves again and the large buffers
    /// accumulate across the matrix instead of being one buffer reused.
    #[test]
    fn test_the_scratch_buffer_is_not_handed_to_the_row() {
        let mut scratch = Vec::new();
        let pivot = SparseRow::from_sorted(
            (0..256)
                .map(|column| (column, F::new(1 + (column as u64 % 11))))
                .collect(),
        )
        .expect("canonical");

        // Many short rows, each merged against the one long pivot.
        let mut rows: Vec<SparseRow<F>> = (0..32)
            .map(|k| SparseRow::new(&[(k, F::new(3)), (300 + k, F::new(5))]))
            .collect();
        for row in rows.iter_mut() {
            row.subtract_scaled(&pivot, &F::new(2), &mut scratch);
        }

        let payload: usize = rows.iter().map(SparseRow::nonzeros).sum();
        let capacity: usize = rows.iter().map(SparseRow::capacity).sum();
        assert!(
            capacity <= 2 * payload,
            "{} entries of payload are held in {} entries of capacity across {} rows",
            payload,
            capacity,
            rows.len()
        );
        // One buffer, reused: the scratch is allowed to be as large as the largest merge.
        assert!(scratch.capacity() >= 256, "the scratch was given away");
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
