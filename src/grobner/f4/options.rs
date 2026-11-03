//! What an F4 computation is allowed to do, and how it reports running out of room.
//!
//! An F4 matrix can be far larger than its inputs suggest, and elimination can make it denser
//! still. Those are the two ways an F4 computation dies, so both are budgeted: exceeding a budget
//! is an [`F4Error`], never a basis that looks complete and is not.
//!
//! Beyond the budgets, [`F4Options`] is also where every optimization is selected. There is one
//! field per independent strategy rather than a single "fast" switch, because the question each
//! one has to answer is whether *it* pays, and a combined switch cannot be ablated. Every
//! strategy is required to return the identical basis: a reduced Gröbner basis is unique for a
//! given ideal and order, so an option that changes the answer is a defect, not a trade-off.

use std::fmt::{Display, Formatter};

use crate::{
    grobner::{f4::symbolic::CacheMode, pairs::PairCriteria},
    linalg::echelon::Backend,
};

/// How the rows of a Macaulay matrix are eliminated.
///
/// Symbolic preprocessing produces two kinds of row: the halves of the selected critical pairs,
/// and the reducer multiples added so that the matrix can perform the reductions polynomial
/// division would. The second kind is 27% to 96% of the rows in the instances measured in the
/// preceding milestone, and the two kinds play different roles — one is the work, the other is the
/// machinery that reduces it.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ReductionStrategy {
    /// One echelon pass over every row in the order preprocessing produced them.
    ///
    /// The measured baseline. Reducer rows are reduced against pair rows and against one another
    /// as readily as the other way round, because the elimination knows nothing about which is
    /// which.
    #[default]
    Unstructured,

    /// Reducer rows are established as pivots first, and the pair rows are reduced against them.
    ///
    /// Reducer multiples have distinct leading monomials by construction, so putting them first
    /// and in column order makes them a pivot set that needs no discovering and no reducing
    /// against itself. This performs **more** row operations than the unstructured path, not
    /// fewer, and far less fill-in: on katsura-7 grevlex it takes peak live entries from 1 390 812
    /// to 63 087. See [`super::structured`] and `docs/MILESTONE-F4-OPTIMIZATION.md` §7.1.
    ///
    /// Row echelon form depends on the order the rows are taken in, so the two paths produce
    /// different candidate *polynomials*. They cannot produce different leading monomials — pivot
    /// columns are fixed by the columns' ranks — so the reduced basis is identical, which is
    /// asserted. What is **not** comparable across the two paths is the trajectory: different
    /// candidates make different later batches, so `batches` and `pairs_reduced` differ.
    Structured,
}

/// How symbolic preprocessing chooses which basis element reduces a monomial.
///
/// Any choice gives a correct closure, so this is purely a cost decision — but it is not a local
/// one: a different divisor gives a different multiplier, hence a different row, hence different
/// columns and a different matrix.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ReducerSelection {
    /// The first basis element, in index order, whose leading monomial divides. The baseline.
    #[default]
    FirstApplicable,

    /// The element whose leading monomial is largest, giving the smallest multiplier.
    ///
    /// Not yet implemented; currently first-applicable.
    LargestLeadingMonomial,
}

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

    /// Which representation elimination uses. See [`Backend`].
    pub elimination: Backend,

    /// How the Macaulay matrix's rows are eliminated. See [`ReductionStrategy`].
    pub reduction: ReductionStrategy,

    /// How symbolic preprocessing picks a reducer. See [`ReducerSelection`].
    pub reducer_selection: ReducerSelection,

    /// Which criteria may discard a critical pair before a matrix is built. See [`PairCriteria`].
    pub criteria: PairCriteria,

    /// Whether reducer multiples are remembered between batches. See [`CacheMode`].
    ///
    /// Whether caching pays depends on how often the same `(basis_index, multiplier)` recurs
    /// across batches, which successive batches working at successive degrees give no reason to
    /// expect. [`CacheMode::Count`] measures that without changing what is computed, and is the
    /// configuration to run before [`CacheMode::Store`] is implemented at all.
    pub reducer_cache: CacheMode,

    /// Record how long each stage of each batch took, into [`super::F4Statistics::stages`].
    ///
    /// Off by default, and the only reason it is a flag rather than always on: the shipping path
    /// should contain no timing at all. When it is set, the clock is read four times per *batch* —
    /// not per row or per row operation — so it attributes cost at a granularity that does not
    /// distort what it measures.
    pub measure_stages: bool,
}

impl F4Options {
    /// The configuration the preceding milestone measured: every optimization off.
    ///
    /// Named permanently, and separately from [`F4Options::default`], so that a comparison against
    /// the baseline stays possible after the default moves. An ablation study whose reference is
    /// "the default" measures something that changes underneath it.
    pub fn baseline() -> Self {
        Self {
            max_pairs_per_batch: None,
            max_matrix_rows: 200_000,
            max_matrix_columns: 200_000,
            max_live_nonzeros: 20_000_000,
            max_batches: None,
            max_basis_elements: None,
            elimination: Backend::Sparse,
            reduction: ReductionStrategy::Unstructured,
            reducer_selection: ReducerSelection::FirstApplicable,
            criteria: PairCriteria::PRODUCT_ONLY,
            reducer_cache: CacheMode::Off,
            measure_stages: false,
        }
    }
}

impl Default for F4Options {
    /// Limits high enough not to interfere with a computation that was going to finish, and low
    /// enough to fail before exhausting a workstation.
    ///
    /// `max_live_nonzeros` of 20 million is about 320 MB at 16 bytes per entry.
    ///
    /// Currently identical to [`F4Options::baseline`]: the default path is the measured baseline
    /// until the measurements justify moving it, which is a decision for the end of the milestone
    /// rather than a side effect of landing an optimization.
    fn default() -> Self {
        Self::baseline()
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
    ///
    /// Applies to the generators as supplied, not only to what the computation appends: a basis
    /// that starts over the limit is over the limit.
    TooManyBasisElements { elements: usize, limit: usize },

    /// The options cannot be satisfied by any computation.
    InvalidOptions { reason: &'static str },
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
                "the basis held {} elements, over the limit of {}",
                elements, limit
            ),
            Self::InvalidOptions { reason } => {
                write!(f, "the options are unsatisfiable: {}", reason)
            }
        }
    }
}

impl std::error::Error for F4Error {}

#[cfg(test)]
mod tests {
    use super::{F4Error, F4Options, ReducerSelection, ReductionStrategy};
    use crate::{
        grobner::{f4::symbolic::CacheMode, pairs::PairCriteria},
        linalg::echelon::Backend,
    };

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

    /// The default is the baseline, so the shipping path is the measured one.
    #[test]
    fn test_default_is_the_baseline() {
        assert_eq!(F4Options::default(), F4Options::baseline());
    }

    /// Every strategy field starts at the baseline value, and timing starts off.
    #[test]
    fn test_baseline_selects_no_optimization() {
        let options = F4Options::baseline();
        assert_eq!(options.elimination, Backend::Sparse);
        assert_eq!(options.reduction, ReductionStrategy::Unstructured);
        assert_eq!(options.reducer_selection, ReducerSelection::FirstApplicable);
        assert_eq!(options.criteria, PairCriteria::PRODUCT_ONLY);
        assert_eq!(options.reducer_cache, CacheMode::Off);
        assert!(
            !options.measure_stages,
            "the shipping path must contain no timing"
        );
    }

    /// Every strategy variant is constructible through the options, which is what makes an
    /// ablation study expressible without touching this file again.
    #[test]
    fn test_every_strategy_is_selectable() {
        for elimination in [Backend::Sparse, Backend::Dense, Backend::Adaptive] {
            for reduction in [
                ReductionStrategy::Unstructured,
                ReductionStrategy::Structured,
            ] {
                for reducer_selection in [
                    ReducerSelection::FirstApplicable,
                    ReducerSelection::LargestLeadingMonomial,
                ] {
                    for criteria in [
                        PairCriteria::NONE,
                        PairCriteria::PRODUCT_ONLY,
                        PairCriteria::ALL,
                    ] {
                        let options = F4Options {
                            elimination,
                            reduction,
                            reducer_selection,
                            criteria,
                            reducer_cache: CacheMode::Store,
                            measure_stages: true,
                            ..F4Options::baseline()
                        };
                        assert_eq!(options.elimination, elimination);
                        assert_eq!(options.reduction, reduction);
                        assert_eq!(options.reducer_selection, reducer_selection);
                        assert_eq!(options.criteria, criteria);
                        // The budgets are untouched by a strategy choice.
                        assert_eq!(
                            options.max_live_nonzeros,
                            F4Options::baseline().max_live_nonzeros
                        );
                    }
                }
            }
        }
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
