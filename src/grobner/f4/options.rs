//! What an F4 computation is allowed to do, and how it reports running out of room.
//!
//! An F4 matrix can be far larger than its inputs suggest, and elimination can make it denser
//! still. Those are the two ways an F4 computation dies, so both are budgeted: exceeding a budget
//! is an [`F4Error`], never a basis that looks complete and is not.

use std::fmt::{Display, Formatter};

/// Limits on an F4 computation.
///
/// Public fields with a `Default`, so a caller changes what it cares about:
///
/// ```ignore
/// let options = F4Options { max_pairs_per_batch: Some(16), ..F4Options::default() };
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct F4Options {
    /// The largest batch of critical pairs to reduce at once, or `None` for every pair at the
    /// lowest available degree.
    ///
    /// Capping the batch bounds the matrix, at the cost of the batching that makes F4 worthwhile.
    /// `Some(1)` degenerates to one S-polynomial per matrix, which is useful for testing and is
    /// otherwise a slow way to run Buchberger.
    pub max_pairs_per_batch: Option<usize>,

    /// The largest Macaulay matrix to build, in rows.
    pub max_matrix_rows: usize,

    /// The largest Macaulay matrix to build, in columns.
    pub max_matrix_columns: usize,

    /// The most nonzero entries that may be live at once, in construction and in elimination.
    ///
    /// Counted as the matrix is written and again after every row operation, so neither a dense
    /// batch nor fill-in can quietly exhaust memory. An entry is a column index and a field
    /// element, so the byte cost is roughly this times `size_of::<(usize, F)>()`.
    ///
    /// This is a budget on the entries F4 holds, not a ceiling on the process. It does not account
    /// for the monomial-to-column map, the term vectors of the basis, the scratch buffer
    /// elimination merges through, or allocator overhead — all of which are bounded by the row and
    /// column budgets but are not counted here. Treat it as the knob that keeps matrix growth
    /// recoverable, not as a memory limit.
    pub max_live_nonzeros: usize,

    /// The most batches to process before giving up, or `None` for no limit.
    pub max_batches: Option<usize>,

    /// The most basis elements to accumulate before giving up, or `None` for no limit.
    ///
    /// Counts elements appended during the computation, before interreduction removes the
    /// redundant ones.
    pub max_basis_elements: Option<usize>,
}

impl Default for F4Options {
    /// Limits high enough not to interfere with a computation that was going to finish, and low
    /// enough to fail before exhausting a workstation.
    ///
    /// `max_live_nonzeros` of 20 million is about 320 MB at 16 bytes per entry.
    fn default() -> Self {
        Self {
            max_pairs_per_batch: None,
            max_matrix_rows: 200_000,
            max_matrix_columns: 200_000,
            max_live_nonzeros: 20_000_000,
            max_batches: None,
            max_basis_elements: None,
        }
    }
}

/// Why an F4 computation stopped without a basis.
///
/// Every variant means a limit in [`F4Options`] was crossed. There is deliberately no variant for
/// "finished but incomplete": a successful return is always a complete reduced Gröbner basis.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum F4Error {
    /// Symbolic preprocessing needed more rows than allowed.
    ///
    /// Carries only the limit. The row count is not reported because preprocessing stops as soon
    /// as the limit is crossed, so any number it could report would be the limit plus one rather
    /// than the size the batch would really have reached.
    TooManyRows { limit: usize },

    /// A Macaulay matrix held more distinct monomials than the column budget allowed. Carries only
    /// the limit, for the same reason as `TooManyRows`.
    TooManyColumns { limit: usize },

    /// Construction or elimination needed more live nonzero entries than allowed.
    ///
    /// `nonzeros` is the live count when the limit was crossed. Unlike the two above it is
    /// informative: the overshoot is bounded by a single row, because the count is tested after
    /// every row written and after every row operation.
    TooManyNonzeros { nonzeros: usize, limit: usize },

    /// The computation did not finish within the allowed number of batches.
    TooManyBatches { limit: usize },

    /// The basis held, or grew beyond, more elements than allowed.
    TooManyBasisElements { elements: usize, limit: usize },
}

impl Display for F4Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooManyRows { limit } => write!(
                f,
                "symbolic preprocessing needed more than the {} rows allowed",
                limit
            ),
            Self::TooManyColumns { limit } => write!(
                f,
                "a Macaulay matrix needed more than the {} columns allowed",
                limit
            ),
            Self::TooManyNonzeros { nonzeros, limit } => write!(
                f,
                "{} live nonzero entries were needed, over the limit of {}",
                nonzeros, limit
            ),
            Self::TooManyBatches { limit } => {
                write!(f, "the computation did not finish within {} batches", limit)
            }
            Self::TooManyBasisElements { elements, limit } => write!(
                f,
                "the basis grew to {} elements, over the limit of {}",
                elements, limit
            ),
        }
    }
}

impl std::error::Error for F4Error {}

#[cfg(test)]
mod tests {
    use super::{F4Error, F4Options};

    /// The defaults leave the batch size and the overall limits unbounded.
    #[test]
    fn test_defaults() {
        let options = F4Options::default();
        assert_eq!(options.max_pairs_per_batch, None);
        assert_eq!(options.max_batches, None);
        assert_eq!(options.max_basis_elements, None);
        assert!(options.max_matrix_rows > 0);
        assert!(options.max_matrix_columns > 0);
        assert!(options.max_live_nonzeros > 0);
    }

    /// Overriding one field leaves the rest at their defaults.
    #[test]
    fn test_partial_override() {
        let options = F4Options {
            max_pairs_per_batch: Some(4),
            ..F4Options::default()
        };
        assert_eq!(options.max_pairs_per_batch, Some(4));
        assert_eq!(
            options.max_matrix_rows,
            F4Options::default().max_matrix_rows
        );
    }

    /// Each error names the limit it crossed and the value that crossed it.
    #[test]
    fn test_error_messages_name_the_limit() {
        let cases = [
            F4Error::TooManyRows { limit: 5 },
            F4Error::TooManyColumns { limit: 5 },
            F4Error::TooManyNonzeros {
                nonzeros: 10,
                limit: 5,
            },
            F4Error::TooManyBatches { limit: 5 },
            F4Error::TooManyBasisElements {
                elements: 10,
                limit: 5,
            },
        ];
        for error in cases {
            let message = error.to_string();
            assert!(message.contains('5'), "{:?} does not name its limit", error);
        }
    }
}
