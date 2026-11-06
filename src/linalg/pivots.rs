//! Which row is the pivot for a given column, stored by column rather than hashed.
//!
//! The keys are dense column indices in `0..num_columns`, so a hash table is a hash table keyed by
//! an integer that is already its own slot number. The elimination's inner loop consults this once
//! per row operation, which is where the cost is.
//!
//! Two representations, because neither alone is safe at both extremes. [`Store::Indexed`] is the
//! one that matters: `4 * num_columns` bytes, one load per lookup. [`Store::Hashed`] is the
//! fallback for the two shapes it cannot serve — more rows than a `u32` can name, and a width the
//! sparse backend has no per-column allocation of its own to amortise an array against. Which one
//! is in use never changes during an elimination, so the branch is perfectly predicted.

use std::collections::HashMap;

/// No pivot. Reserving the top `u32` costs one row index that no matrix of this size could reach.
const VACANT: u32 = u32::MAX;

/// Row counts at or above this get the hashed store.
///
/// A matrix of exactly `u32::MAX` rows would in fact still fit — its last index is `u32::MAX - 1`,
/// which is distinct from [`VACANT`] — so the guard gives up one row it could have had, in
/// exchange for a boundary stated as the marker's own value rather than one below it.
const MAX_INDEXED_ROWS: usize = VACANT as usize;

/// Columns above which the indexed array is not built: 64 Mi columns, i.e. 256 MiB of `u32`.
///
/// The sparse backend allocates nothing per column, so unlike the accumulator it has no existing
/// per-column buffer to measure an array against. The cap is what keeps a matrix that is far wider
/// than it is tall from paying a dense array for it. Nothing measured comes near: the widest
/// instance in `examples/elimination_density.rs` is katsura-7 grevlex at 6862 columns, four orders
/// of magnitude below.
const MAX_INDEXED_COLUMNS: usize = 1 << 26;

#[derive(Clone, Debug)]
enum Store {
    Indexed(Vec<u32>),
    Hashed(HashMap<usize, usize>),
}

/// The pivot row of each column, for one elimination.
///
/// Shared by the two-phase block entry points: [`crate::linalg::reduce_rows_against_pivots_with`]
/// builds one from the upper block and hands it to a backend, which goes on inserting into it.
#[derive(Clone, Debug)]
pub(crate) struct PivotIndex {
    store: Store,
}

/// Whether a matrix of this shape gets the indexed store.
///
/// A predicate rather than an inline condition so the two boundaries can be tested without
/// allocating the array that either side of them implies.
fn indexable(num_columns: usize, num_rows: usize) -> bool {
    num_rows < MAX_INDEXED_ROWS && num_columns <= MAX_INDEXED_COLUMNS
}

impl PivotIndex {
    /// An empty index for a matrix of the given shape.
    ///
    /// `num_rows` decides representability, not capacity: a row index has to fit in a `u32`
    /// without colliding with [`VACANT`], and a matrix too tall for that falls back to hashing
    /// rather than truncating silently.
    pub(crate) fn new(num_columns: usize, num_rows: usize) -> Self {
        let store = if indexable(num_columns, num_rows) {
            Store::Indexed(vec![VACANT; num_columns])
        } else {
            Store::Hashed(HashMap::new())
        };
        Self { store }
    }

    /// The row that is the pivot for `column`, if any.
    #[inline]
    pub(crate) fn pivot_of(&self, column: usize) -> Option<usize> {
        match &self.store {
            // Out of range reads as vacant. `SparseMatrix::new` rejects a column at or beyond the
            // declared width, so this is unreachable rather than a policy.
            Store::Indexed(rows) => match rows.get(column) {
                Some(&VACANT) | None => None,
                Some(&row) => Some(row as usize),
            },
            Store::Hashed(map) => map.get(&column).copied(),
        }
    }

    /// Record `row` as the pivot for `column`, returning the row it displaced.
    ///
    /// The return value is what lets the block entry point reject an upper block that declares two
    /// pivots for one column, which would otherwise drop one of the two relations silently.
    pub(crate) fn insert(&mut self, column: usize, row: usize) -> Option<usize> {
        match &mut self.store {
            Store::Indexed(rows) => {
                assert!(
                    row < MAX_INDEXED_ROWS,
                    "pivot row {} does not fit the indexed store",
                    row
                );
                if column >= rows.len() {
                    rows.resize(column + 1, VACANT);
                }
                let previous = std::mem::replace(&mut rows[column], row as u32);
                (previous != VACANT).then_some(previous as usize)
            }
            Store::Hashed(map) => map.insert(column, row),
        }
    }

    /// Bytes of pivot storage held, for the tests that police the cost of each representation.
    ///
    /// Not called outside them: a caller that wants the figure for a report can compute it from
    /// the width, and an accessor on the hot type is not the place to put a measurement.
    #[cfg(test)]
    pub(crate) fn storage_bytes(&self) -> usize {
        match &self.store {
            Store::Indexed(rows) => rows.len() * std::mem::size_of::<u32>(),
            // One `(usize, usize)` bucket plus hashbrown's control byte, which is the floor; the
            // table is overallocated to keep its load factor and this does not say by how much.
            Store::Hashed(map) => map.len() * (2 * std::mem::size_of::<usize>() + 1),
        }
    }

    /// Whether the indexed representation is in use, for the tests that police the fallback.
    #[cfg(test)]
    pub(crate) fn is_indexed(&self) -> bool {
        matches!(self.store, Store::Indexed(_))
    }
}

#[cfg(test)]
mod tests {
    use super::{indexable, PivotIndex, MAX_INDEXED_COLUMNS, MAX_INDEXED_ROWS, VACANT};

    /// A fresh index reports no pivot for any column in range or out of it.
    #[test]
    fn test_empty_reports_no_pivot() {
        let pivots = PivotIndex::new(8, 4);
        assert!(pivots.is_indexed());
        for column in 0..10 {
            assert_eq!(pivots.pivot_of(column), None, "column {}", column);
        }
    }

    /// Insertion is visible to lookup, and returns the row it displaced rather than discarding it.
    #[test]
    fn test_insert_and_displace() {
        let mut pivots = PivotIndex::new(8, 8);
        assert_eq!(pivots.insert(3, 0), None);
        assert_eq!(pivots.pivot_of(3), Some(0));
        assert_eq!(pivots.insert(3, 5), Some(0));
        assert_eq!(pivots.pivot_of(3), Some(5));
        assert_eq!(pivots.pivot_of(2), None);
    }

    /// Row zero is a pivot like any other and is not confused with the vacant marker.
    #[test]
    fn test_row_zero_is_not_vacant() {
        let mut pivots = PivotIndex::new(4, 4);
        assert_eq!(pivots.insert(0, 0), None);
        assert_eq!(pivots.pivot_of(0), Some(0));
    }

    /// A zero-width matrix has no columns to index and still answers lookups.
    #[test]
    fn test_zero_width() {
        let pivots = PivotIndex::new(0, 5);
        assert!(pivots.is_indexed());
        assert_eq!(pivots.pivot_of(0), None);
    }

    /// Both fallback boundaries are exactly where they are documented to be.
    ///
    /// Through the predicate, so the array neither side implies is never allocated: `u32::MAX`
    /// rows, because the last row index must stay distinct from the vacant marker, and 64 Mi
    /// columns.
    #[test]
    fn test_the_fallback_boundaries() {
        assert!(indexable(8, MAX_INDEXED_ROWS - 1));
        assert!(!indexable(8, MAX_INDEXED_ROWS));
        assert!(!indexable(8, MAX_INDEXED_ROWS + 1));
        assert!(indexable(MAX_INDEXED_COLUMNS, 4));
        assert!(!indexable(MAX_INDEXED_COLUMNS + 1, 4));
    }

    /// A matrix too tall for a `u32` stores its row indices intact instead of truncating them.
    #[test]
    fn test_a_tall_matrix_does_not_truncate_a_row_index() {
        // The row index a `Vec<u32>` would have turned into the vacant marker, and the one it
        // would have wrapped to zero, both survive the fallback.
        let mut pivots = PivotIndex::new(8, MAX_INDEXED_ROWS + 2);
        assert!(!pivots.is_indexed());
        assert_eq!(pivots.insert(1, VACANT as usize), None);
        assert_eq!(pivots.pivot_of(1), Some(VACANT as usize));
        assert_eq!(pivots.insert(2, VACANT as usize + 1), None);
        assert_eq!(pivots.pivot_of(2), Some(VACANT as usize + 1));
        assert_eq!(pivots.pivot_of(3), None);
    }

    /// A matrix wider than the column cap serves lookups from the hashed store.
    #[test]
    fn test_a_very_wide_matrix_uses_the_hashed_store() {
        let mut pivots = PivotIndex::new(MAX_INDEXED_COLUMNS + 1, 4);
        assert!(!pivots.is_indexed());
        assert_eq!(pivots.insert(MAX_INDEXED_COLUMNS, 2), None);
        assert_eq!(pivots.pivot_of(MAX_INDEXED_COLUMNS), Some(2));
        assert_eq!(pivots.storage_bytes(), 2 * std::mem::size_of::<usize>() + 1);
    }

    /// The indexed store costs four bytes per column, whatever is in it.
    #[test]
    fn test_storage_is_four_bytes_per_column() {
        let mut pivots = PivotIndex::new(1000, 10);
        assert_eq!(pivots.storage_bytes(), 4000);
        assert_eq!(pivots.insert(7, 3), None);
        assert_eq!(pivots.storage_bytes(), 4000);
    }

    /// `Option<u32>` is twice the width of a `u32`, which is why the sentinel is the one shipped.
    ///
    /// A `u32` has no invalid bit pattern for a discriminant to occupy, so the niche optimization
    /// the issue asked about does not apply. `Option<NonZeroU32>` would be four bytes, at the cost
    /// of offsetting every row index by one.
    #[test]
    fn test_option_u32_has_no_niche() {
        assert_eq!(std::mem::size_of::<u32>(), 4);
        assert_eq!(std::mem::size_of::<Option<u32>>(), 8);
        assert_eq!(std::mem::size_of::<Option<std::num::NonZeroU32>>(), 4);
    }
}
