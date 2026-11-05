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

use std::{
    fmt::{Display, Formatter},
    mem::size_of,
};

use crate::{
    grobner::{
        f4::symbolic::CacheMode,
        pairs::{PairCriteria, PairSchedule},
    },
    linalg::echelon::Backend,
    FiniteField,
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
    /// **Measured and rejected as a default.** The intuition is that a smaller multiplier gives a
    /// smaller multiple and so a smaller closure; the measurement says the opposite, because the
    /// reducer row leads with the monomial `u` being covered either way, so what the choice
    /// changes is the row's *tail*. A large divisor's tail sits just below `u` and is still
    /// reducible, so each such row spawns more rows. On katsura-7 grevlex this takes the largest
    /// matrix from 6810x6862 to 16750x16812 and the computation from 887 ms to 3045 ms. Only the
    /// lex instances of cyclic gain. Selectable for ablation; see
    /// `docs/MILESTONE-F4-OPTIMIZATION.md` §7.2.
    LargestLeadingMonomial,
}

/// Limits on an F4 computation.
///
/// Public fields with a `Default`, so a caller changes what it cares about:
///
/// ```
/// use zeebra::grobner::F4Options;
///
/// let options = F4Options {
///     max_pairs_per_batch: Some(16),
///     ..F4Options::default()
/// };
/// assert_eq!(options.max_pairs_per_batch, Some(16));
/// // Everything else is the recommended configuration, which is what `default()` is.
/// assert_eq!(options.criteria, F4Options::recommended().criteria);
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

    /// The bytes those live entries may occupy at once.
    ///
    /// **A second budget rather than a redefinition of [`max_live_nonzeros`](Self::max_live_nonzeros),**
    /// for the same reason FGLM's
    /// [`max_operator_bytes`](crate::grobner::FglmOptions::max_operator_bytes) is one: changing what
    /// the older limit counted would make every figure recorded against it ambiguous. Both are
    /// enforced, and [`live_entry_allowance`](Self::live_entry_allowance) is the smaller of the two.
    ///
    /// An entry is a column index and a field element, so it costs `size_of::<(usize, F)>()`:
    /// **16 bytes over a 64-bit prime field and 40 over a 254-bit one.** An entry budget alone
    /// therefore admits 2.5x the memory over BN254 as over `Zp18446744073709551557` — the budget
    /// means something different at every field width, which is what this limit fixes by being
    /// stated in the unit that is allocated.
    ///
    /// It covers the same storage [`max_live_nonzeros`](Self::max_live_nonzeros) does and no more:
    /// not the monomial-to-column map, not the basis's term vectors, not the dense buffer a
    /// backend reduces through, and not allocator overhead. The dense buffers are *reported*
    /// instead — see [`BatchStatistics::dense_buffer_bytes`](super::BatchStatistics::dense_buffer_bytes)
    /// — because enforcing them here would make the default refuse computations the entry budget
    /// admits, and under [`Backend::Dense`] they are a function of the shape alone, which the row
    /// and column budgets already bound. This is still not a ceiling on the process; it is the
    /// entry budget in bytes.
    pub max_live_bytes: usize,

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

    /// In what order the pairs of one degree are taken. See [`PairSchedule`].
    ///
    /// A schedule discards nothing, so this cannot change the basis — only which pairs share a
    /// matrix, and then only when [`Self::max_pairs_per_batch`] caps the batch.
    pub schedule: PairSchedule,

    /// Whether reducer multiples are tracked between batches. See [`CacheMode`].
    ///
    /// **Nothing is served from this**, and that is the measured conclusion: the repetition rate
    /// is high — 43% to 95% of multiples had been built in an earlier batch — and serving them is
    /// still slower than rebuilding them, because rebuilding is one integer addition per variable
    /// per term. [`CacheMode::Count`] measures the rate without changing what is computed.
    pub reducer_cache: CacheMode,

    /// Record how long each stage of each batch took, into [`super::F4Statistics::stages`].
    ///
    /// Off by default, and the only reason it is a flag rather than always on: the shipping path
    /// should contain no timing at all. When it is set, the clock is read four times per *batch* —
    /// not per row or per row operation — so it attributes cost at a granularity that does not
    /// distort what it measures.
    pub measure_stages: bool,

    /// Break the work down by the degree it was done at, into
    /// [`super::F4Statistics::degrees`].
    ///
    /// Off by default, and a flag for the same reason [`Self::measure_stages`] is: the shipping
    /// path should contain no profiling. What it costs when on is a map insertion per batch and one
    /// scan of each matrix's column vector — per *batch*, not per row — so it does not distort the
    /// measurement it takes. The rank attribution the profile is built on is free either way, since
    /// it is arithmetic on counters the elimination already returns.
    pub profile_degrees: bool,
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
            max_live_bytes: 320_000_000,
            max_batches: None,
            max_basis_elements: None,
            elimination: Backend::Sparse,
            reduction: ReductionStrategy::Unstructured,
            reducer_selection: ReducerSelection::FirstApplicable,
            criteria: PairCriteria::PRODUCT_ONLY,
            schedule: PairSchedule::DegreeThenLcm,
            reducer_cache: CacheMode::Off,
            measure_stages: false,
            profile_degrees: false,
        }
    }

    /// Every strategy the milestone's measurements justified.
    ///
    /// Structured elimination, all pair criteria, and the dense accumulator. This is what
    /// [`F4Options::default`] is, and it is named separately so that a caller can say which
    /// configuration it meant rather than inheriting whatever the default becomes next.
    ///
    /// Two of M16's improvements are **not** here, because they are not options: a cheaper
    /// monomial hash in symbolic preprocessing and the rewritten final interreduction are
    /// unconditional and apply to [`F4Options::baseline`] too. The strategies that M16 measured
    /// and *rejected* are likewise absent: [`ReducerSelection::LargestLeadingMonomial`] remains
    /// selectable so its rejection can be reproduced, and reducer caching was removed outright
    /// because an option named for a behaviour it does not have is worse than no option.
    ///
    /// Chosen from the ablation in `docs/MILESTONE-F4-OPTIMIZATION.md` §8.1, where this
    /// combination is the fastest of twelve on ten of eleven instances. On the eleventh,
    /// katsura-6 under lex, the criteria have already reduced elimination to 9% of the total, so
    /// the dense accumulator's gain there is smaller than the harness's run-to-run variation and
    /// the ordering against `Structured + ALL` alone flips between runs. It is still selected,
    /// because on the instances where elimination dominates it is worth 1.9x on its own.
    pub fn recommended() -> Self {
        Self {
            elimination: Backend::Adaptive,
            reduction: ReductionStrategy::Structured,
            criteria: PairCriteria::ALL,
            ..Self::baseline()
        }
    }

    /// Bytes one live matrix entry over `F` occupies.
    ///
    /// A [`SparseRow`](crate::linalg::sparse::SparseRow) holds `Vec<(usize, F)>`, so this is the
    /// pair's size — including any padding the field's alignment forces, which is why it is
    /// `size_of::<(usize, F)>()` and not `8 + size_of::<F>()`.
    pub fn bytes_per_entry<F: FiniteField>() -> usize {
        size_of::<(usize, F)>()
    }

    /// The live entries this configuration admits over `F`.
    ///
    /// The smaller of [`max_live_nonzeros`](Self::max_live_nonzeros) and what
    /// [`max_live_bytes`](Self::max_live_bytes) pays for. One number, so construction and
    /// elimination cannot be checked against two budgets that disagree, and so the two cannot
    /// drift apart as either check moves.
    ///
    /// Never divides by zero: an entry carries a `usize` whatever `F` is, so the divisor is at
    /// least 8.
    pub fn live_entry_allowance<F: FiniteField>(&self) -> usize {
        self.max_live_nonzeros
            .min(self.max_live_bytes / Self::bytes_per_entry::<F>())
    }

    /// Whether [`max_live_bytes`](Self::max_live_bytes) is the budget that binds over `F`.
    ///
    /// Strictly smaller, so that when the two budgets describe the same quantity the older error
    /// is the one reported and a figure recorded against it keeps its meaning.
    pub fn bytes_bind_first<F: FiniteField>(&self) -> bool {
        self.live_entry_allowance::<F>() < self.max_live_nonzeros
    }

    /// The error for a live-entry count that crossed whichever budget binds over `F`.
    pub(crate) fn entry_budget_error<F: FiniteField>(&self, nonzeros: usize) -> F4Error {
        if self.bytes_bind_first::<F>() {
            F4Error::TooManyLiveBytes {
                bytes: nonzeros.saturating_mul(Self::bytes_per_entry::<F>()),
                limit: self.max_live_bytes,
            }
        } else {
            F4Error::TooManyNonzeros {
                nonzeros,
                limit: self.max_live_nonzeros,
            }
        }
    }
}

impl Default for F4Options {
    /// Limits high enough not to interfere with a computation that was going to finish, and low
    /// enough to fail before exhausting a workstation, with every strategy the measurements
    /// justified.
    ///
    /// `max_live_nonzeros` of 20 million is about 320 MB at 16 bytes per entry, and
    /// `max_live_bytes` is that same 320 MB stated in the unit that is allocated. The two bind
    /// together over a 64-bit prime field, which is the width every figure in M16 was measured at,
    /// and the byte budget binds first over anything wider: at BN254's 40 bytes an entry it admits
    /// 8 million entries rather than 20. That is the point of having it — the same default now
    /// describes the same memory at every field width instead of 2.5x more of it over a wide one.
    ///
    /// This is [`F4Options::recommended`], **not** [`F4Options::baseline`]. The two were identical
    /// until the ablation was run: an optimization milestone should not move its own default as a
    /// side effect of landing an optimization, because then nothing has a fixed reference. The
    /// default moved once, at the end, on the evidence.
    fn default() -> Self {
        Self::recommended()
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

    /// Construction or elimination needed more bytes of live entries than allowed.
    ///
    /// Reported in place of `TooManyNonzeros` exactly when
    /// [`F4Options::max_live_bytes`] is the budget that binds for the field in use, so the two are
    /// never both plausible for one failure. `bytes` is the live count when the limit was crossed,
    /// times `size_of::<(usize, F)>()`.
    TooManyLiveBytes { bytes: usize, limit: usize },

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
            Self::TooManyLiveBytes { bytes, limit } => write!(
                f,
                "{} bytes of live entries were needed, over the limit of {}",
                bytes, limit
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
        fields::{Bls12_381Fr, Bn254Fr, Zp18446744073709551557},
        grobner::{f4::symbolic::CacheMode, pairs::PairCriteria},
        linalg::echelon::Backend,
    };

    /// The width every figure in M16 was measured at, and the width the two budgets agree over.
    type Narrow = Zp18446744073709551557;

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
        assert!(options.max_live_bytes > 0);
    }

    /// The default is the recommended configuration, and the baseline remains reachable.
    ///
    /// Both halves matter. A caller who passes nothing gets what the measurements chose; a caller
    /// reproducing the milestone's numbers can still ask for the configuration they were taken
    /// against, which a default that absorbed the baseline would have made impossible.
    #[test]
    fn test_default_is_the_recommended_configuration() {
        assert_eq!(F4Options::default(), F4Options::recommended());
        assert_ne!(F4Options::default(), F4Options::baseline());
    }

    /// The recommended configuration selects what the ablation chose, and nothing it rejected.
    #[test]
    fn test_recommended_selects_what_was_measured() {
        let options = F4Options::recommended();
        assert_eq!(options.elimination, Backend::Adaptive);
        assert_eq!(options.reduction, ReductionStrategy::Structured);
        assert_eq!(options.criteria, PairCriteria::ALL);
        // Rejected by measurement: a smaller multiplier enlarges the closure, and caching a
        // multiple's terms costs more than rebuilding them even at a 95% repetition rate.
        assert_eq!(options.reducer_selection, ReducerSelection::FirstApplicable);
        assert_eq!(options.reducer_cache, CacheMode::Off);
        // The shipping path still contains no timing.
        assert!(!options.measure_stages);
        // And only the strategies differ from the baseline; the budgets are untouched.
        assert_eq!(
            options.max_live_nonzeros,
            F4Options::baseline().max_live_nonzeros
        );
        assert_eq!(
            options.max_matrix_rows,
            F4Options::baseline().max_matrix_rows
        );
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
                            reducer_cache: CacheMode::Count,
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
            F4Error::TooManyLiveBytes {
                bytes: 10,
                limit: 5,
            },
        ];
        for error in cases {
            let message = error.to_string();
            assert!(message.contains('5'), "{:?} does not name its limit", error);
        }
    }

    /// An entry's byte cost is the index-and-coefficient pair's, which grows with the field width.
    #[test]
    fn test_bytes_per_entry_follows_the_field_width() {
        assert_eq!(F4Options::bytes_per_entry::<Narrow>(), 16);
        assert_eq!(F4Options::bytes_per_entry::<Bn254Fr>(), 40);
        assert_eq!(F4Options::bytes_per_entry::<Bls12_381Fr>(), 40);
    }

    /// The default's two budgets describe the same memory over the 64-bit field M16 measured at.
    #[test]
    fn test_the_default_budgets_agree_over_a_64_bit_field() {
        let options = F4Options::default();
        assert_eq!(
            options.max_live_bytes,
            options.max_live_nonzeros * F4Options::bytes_per_entry::<Narrow>()
        );
        assert_eq!(options.live_entry_allowance::<Narrow>(), 20_000_000);
        assert!(
            !options.bytes_bind_first::<Narrow>(),
            "with the two budgets equal the older one must be the one reported"
        );
    }

    /// Over a wide field the same default admits 2.5x fewer entries, which is the same memory.
    #[test]
    fn test_the_byte_budget_binds_first_over_a_wide_field() {
        let options = F4Options::default();
        assert_eq!(options.live_entry_allowance::<Bn254Fr>(), 8_000_000);
        assert!(options.bytes_bind_first::<Bn254Fr>());
        // The entry budget alone would have admitted 800 MB here against the 320 MB it describes
        // over a 64-bit field. The byte budget is what makes the default mean one quantity.
        assert_eq!(
            options.live_entry_allowance::<Bn254Fr>() * F4Options::bytes_per_entry::<Bn254Fr>(),
            options.max_live_bytes
        );
    }

    /// The allowance is the smaller of the two budgets, whichever that is.
    #[test]
    fn test_the_allowance_is_the_smaller_budget() {
        let entries_bind = F4Options {
            max_live_nonzeros: 100,
            max_live_bytes: 320_000_000,
            ..F4Options::default()
        };
        assert_eq!(entries_bind.live_entry_allowance::<Narrow>(), 100);
        assert!(!entries_bind.bytes_bind_first::<Narrow>());

        let bytes_bind = F4Options {
            max_live_nonzeros: usize::MAX,
            max_live_bytes: 1_600,
            ..F4Options::default()
        };
        assert_eq!(bytes_bind.live_entry_allowance::<Narrow>(), 100);
        assert!(bytes_bind.bytes_bind_first::<Narrow>());

        // A budget that does not pay for one whole entry admits none, rather than rounding up to
        // one and allocating memory it did not grant.
        let starved = F4Options {
            max_live_bytes: 15,
            ..F4Options::default()
        };
        assert_eq!(starved.live_entry_allowance::<Narrow>(), 0);
    }

    /// A crossing reports the budget that bound, and converts to bytes only when that was the one.
    #[test]
    fn test_the_error_names_the_budget_that_bound() {
        let entries_bind = F4Options {
            max_live_nonzeros: 100,
            max_live_bytes: 320_000_000,
            ..F4Options::default()
        };
        assert_eq!(
            entries_bind.entry_budget_error::<Narrow>(101),
            F4Error::TooManyNonzeros {
                nonzeros: 101,
                limit: 100
            }
        );

        let bytes_bind = F4Options {
            max_live_nonzeros: usize::MAX,
            max_live_bytes: 1_600,
            ..F4Options::default()
        };
        assert_eq!(
            bytes_bind.entry_budget_error::<Narrow>(101),
            F4Error::TooManyLiveBytes {
                bytes: 101 * 16,
                limit: 1_600
            }
        );

        // The same options over a wider field: the same entry count is more bytes.
        assert_eq!(
            bytes_bind.entry_budget_error::<Bn254Fr>(101),
            F4Error::TooManyLiveBytes {
                bytes: 101 * 40,
                limit: 1_600
            }
        );
    }

    /// Converting an entry count to bytes saturates rather than wrapping to a small figure.
    #[test]
    fn test_the_byte_error_does_not_wrap() {
        let options = F4Options {
            max_live_nonzeros: usize::MAX,
            max_live_bytes: 16,
            ..F4Options::default()
        };
        assert_eq!(
            options.entry_budget_error::<Bn254Fr>(usize::MAX),
            F4Error::TooManyLiveBytes {
                bytes: usize::MAX,
                limit: 16
            }
        );
    }
}
