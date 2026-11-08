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
    time::Duration,
};

use crate::{
    grobner::{
        f4::hilbert_driven::HilbertSelection,
        f4::symbolic::CacheMode,
        pairs::{PairCriteria, PairSchedule},
    },
    linalg::echelon::Backend,
    FiniteField, MonomialOrder,
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

/// How final interreduction reduces each basis element against the others.
///
/// Both routes return the **same object**: a reduced Gröbner basis is determined by its leading
/// monomials, so the choice is purely a cost one, and
/// `interreduce::tests::test_the_matrix_route_reproduces_the_division_route` asserts exact equality
/// over three orders and two fields.
///
/// # Why a route is worth conditioning on the order
///
/// `docs/research/groebner-jl-gap.md` §3 measured the division route at **13 871x** Groebner.jl's
/// on `mq-random-10`, against 11.6x–97.1x for every other stage, and §4 attributes the outlier to
/// the stage computing the right thing the wrong way. The matrix route is the same computation
/// Groebner.jl's `f4_autoreduce!` performs — and #507 measured it across the whole corpus ladder,
/// where it splits cleanly on the order (`docs/research/interreduction-cost.md` §3c):
///
/// | order | over the rungs above the noise floor | worst rung |
/// |---|---|---|
/// | grevlex | **1.01x–3.78x faster** | katsura-6, a wash at 1.01x |
/// | grlex | **1.15x–1.71x faster** | katsura-5 at 1.15x |
/// | lex | **1.59x–6.25x slower** | katsura-6 at 6.25x |
///
/// "Above the noise floor" is the thirteen rungs taking 0.5 ms or more. The four that run in
/// 25–170 µs are excluded because their ratios cross 1.00x between runs of identical work — see
/// §3d.2, which quotes the case.
///
/// The mechanism is shape position, and the matrix shape shows it: katsura-6 under lex builds a
/// **7 983 × 8 015** matrix for a **six-element** basis, where grevlex builds 217 × 249 for
/// twenty-two, and that shape is exact and reproduces to the digit across trees. A lex basis in
/// shape position — linear elements over one univariate of high degree
/// — is the **best** case for iterated division, because the ascending-order sort leaves every
/// substituted tail already in normal form, and the **worst** case for a matrix, which must carry
/// columns spanning the univariate's whole degree range.
///
/// So the criterion is the order, which is free to read. Shape position is the *explanation* and
/// would be the finer criterion; `fglm::shape` ships a tested detector that is deliberately
/// unwired, and choosing a route from the instance as well as the order is **#273**'s.
///
/// # Why [`InterreductionRoute::ByOrder`] is nevertheless **not** the default
///
/// Because the time is not the whole cost, and the other half is unbudgeted. #507 measured peak
/// RSS beside every wall time, one row per process, and the matrix route's memory does not scale
/// with its speedup:
///
/// | rung | division | matrix | memory | time |
/// |---|---:|---:|---:|---:|
/// | `mq-random-10` | 163.4 MB | 600.8 MB | 3.68x | 3.74x faster |
/// | `katsura-11` | **534.6 MB** | **13 148.3 MB** | **24.59x** | 2.29x faster |
///
/// **No budget refused the katsura-11 pass.** The matrix route's refusal tests rows, columns and
/// live *entries*, and the entries are not where the memory goes: `mq-random-10`'s matrix holds
/// 893 531 nonzeros — on the order of ten megabytes — against a 437 MB increase in process peak.
/// The cost is in building the closure, which is #477's mechanism, and it is invisible to the
/// quantity being budgeted. That is the defect `docs/research/f4-resource-scaling.md` §10 records
/// for symbolic preprocessing before #305, in a different stage: **the budget sees a fraction of
/// what the run costs.**
///
/// A default that can take a 535 MB computation to 13.1 GB with every budget satisfied is not a
/// default, however much faster it is — it converts a working computation into an OOM on any
/// machine smaller than this one. So the route ships *selectable and measured*, and the default
/// stays where every published figure was taken. Flipping it is gated on the matrix pass's working
/// set becoming a budgeted quantity, which is **#536**.
///
/// Siting a size threshold instead would need a measured crossover, and two points — 3.68x and
/// 24.59x — do not locate one.
///
/// # When the matrix route falls back
///
/// The matrix is subject to the same row, column and entry budgets as any batch's — a stage exempt
/// from them would be a way to exceed the computation's budgets by waiting until the end. If any
/// budget would be crossed, the division route runs instead, and the fallback is recorded in
/// [`super::F4Statistics::interreduction_matrix`] rather than being silent.
///
/// **The entry budget covers the elimination and not only the construction**, which is #536:
/// back-substitution clears every pivot column out of every row holding one, and on `katsura-11`
/// under grevlex that takes 9.18x the entries the matrix was built with and 5.19x the allowance
/// that admitted the construction. Until the budget looked at that number, the route could take a
/// 533.0 MB computation to 13 144.3 MB with every limit satisfied. So a rung whose interreduction
/// working set exceeds [`live_entry_allowance`](Self::live_entry_allowance) now **falls back by
/// default**, and running it by matrix is a matter of raising the allowance deliberately — see
/// [`with_live_budget`](Self::with_live_budget).
///
/// Note what that does to the ladder table above: it was taken **before** #536, so every rung in it
/// ran the route to completion. Which of them still do is #575's first question.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum InterreductionRoute {
    /// One division per basis element, whatever the order.
    ///
    /// The default, and the configuration every published figure was taken in. Kept nameable
    /// separately from [`F4Options::default`] so that an ablation against it stays possible after
    /// the default moves — the same reason [`F4Options::baseline`] exists. It is also the fallback
    /// when a budget refuses the matrix, and the oracle the matrix route is tested against.
    #[default]
    Division,

    /// One Macaulay matrix under a graded order, one division per basis element under lex.
    ///
    /// **Measured ahead of the default on every graded rung of the ladder and behind it on every
    /// lex one** (the table above), and not the default only because of the memory the table
    /// after it reports. This is the route to select when the working set is known to fit.
    ByOrder,

    /// One Macaulay matrix, whatever the order.
    ///
    /// Needed to measure the lex regression [`InterreductionRoute::ByOrder`] exists to avoid: a
    /// route no option can ask for is a route no A/B can reach.
    Matrix,
}

impl InterreductionRoute {
    /// Whether this route builds a matrix under `order`.
    ///
    /// The one place the order criterion is written down, so the dispatch and anything reporting
    /// which route will run cannot disagree about it.
    pub fn builds_a_matrix(self, order: MonomialOrder) -> bool {
        match self {
            Self::Division => false,
            Self::Matrix => true,
            Self::ByOrder => !matches!(order, MonomialOrder::Lexicographic),
        }
    }
}

/// How symbolic preprocessing chooses which basis element reduces a monomial.
///
/// Any choice gives a correct closure, so this is purely a cost decision — but it is not a local
/// one: a different divisor gives a different multiplier, hence a different row, hence different
/// columns and a different matrix.
///
/// Two axes are offered. [`ReducerSelection::LargestLeadingMonomial`] ranks by **multiplier size**,
/// which every [`PairSchedule`] does too; [`ReducerSelection::FewestTerms`] ranks by **term
/// count**, which is orthogonal to it — the monomial being covered is the row's leading monomial
/// under either, so what the two choices trade is the row's tail against the row's length.
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

    /// The divisor with the fewest terms, which is the sparsest row the closure can be given.
    ///
    /// Singular's measured winner. It keeps its reduction set sorted so the first divisor found is
    /// the preferred one, and `initBuchMoraPos` records that `posInT_EcartpLength` beat the
    /// alternatives in a bake-off; that comparator orders by ecart and then by `pLength`, the term
    /// count, and in a global order the ecart is zero. In F4's symbolic preprocessing the reducer
    /// chosen *is* the row added, so the sparsest reducer is directly the sparsest row. See
    /// `docs/research/singular-engine-notes.md` §4.
    ///
    /// Equal term counts are broken by the smaller basis index, because "fewest" alone is not a
    /// total order on the basis and preprocessing has to be deterministic.
    FewestTerms,

    /// The divisor with the *most* terms. The control for [`ReducerSelection::FewestTerms`], and
    /// not optional.
    ///
    /// If sparse reducer rows narrow the matrix, dense ones should widen it. A policy that beats
    /// the baseline in both directions is measuring run-to-run variation, and without the opposite
    /// direction there is no way to tell — which is the argument
    /// `docs/research/pair-scheduling.md` §4 rests on for the schedules.
    MostTerms,
}

impl ReducerSelection {
    /// Every policy, for an ablation that should not have to be edited when one is added.
    pub const ALL: [Self; 4] = [
        Self::FirstApplicable,
        Self::LargestLeadingMonomial,
        Self::FewestTerms,
        Self::MostTerms,
    ];

    /// A short name, for a table column.
    pub fn name(&self) -> &'static str {
        match self {
            Self::FirstApplicable => "first",
            Self::LargestLeadingMonomial => "largest",
            Self::FewestTerms => "fewest-terms",
            Self::MostTerms => "most-terms",
        }
    }
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
    /// This is a budget on the entries of **one batch's matrix**, not a ceiling on the process, and
    /// the gap between those is measured at 75x rather than being a rounding note. See
    /// [`max_live_bytes`](Self::max_live_bytes) for the full list of what no budget here bounds —
    /// notably symbolic preprocessing's monomial queue and the `O(|G|²)` pair queue, neither of
    /// which the row and column budgets bound either. Treat it as the knob that keeps matrix growth
    /// recoverable, not as a memory limit.
    ///
    /// **Not the effective limit on its own.** That is
    /// [`live_entry_allowance`](Self::live_entry_allowance), the `min` of this and what
    /// [`max_live_bytes`](Self::max_live_bytes) pays for — and at
    /// [`recommended`](Self::recommended) over a 16-byte entry the two are *equal*, so assigning
    /// this field by itself moves nothing (#322). [`with_live_entries`](Self::with_live_entries)
    /// sets both.
    pub max_live_nonzeros: usize,

    /// The bytes those live entries may occupy at once.
    ///
    /// **A second budget rather than a redefinition of [`max_live_nonzeros`](Self::max_live_nonzeros),**
    /// for the same reason FGLM's
    /// [`max_operator_bytes`](crate::grobner::FglmOptions::max_operator_bytes) is one: changing what
    /// the older limit counted would make every figure recorded against it ambiguous. Both are
    /// enforced, and [`live_entry_allowance`](Self::live_entry_allowance) is the smaller of the two.
    ///
    /// **So the two knobs interact, and at [`recommended`](Self::recommended) they are numerically
    /// identical over a 16-byte entry** — `320_000_000 / 16` is exactly `20_000_000`. Assigning
    /// either alone therefore leaves the other binding at precisely the old value;
    /// [`with_live_budget`](Self::with_live_budget) sets both from one number (#322).
    ///
    /// An entry is a column index and a field element, so it costs `size_of::<(usize, F)>()`:
    /// **16 bytes over a 64-bit prime field and 40 over a 254-bit one.** An entry budget alone
    /// therefore admits 2.5x the memory over BN254 as over `Zp18446744073709551557` — the budget
    /// means something different at every field width, which is what this limit fixes by being
    /// stated in the unit that is allocated.
    ///
    /// # What it bounds, exactly
    ///
    /// **The `Vec<(usize, F)>` payload of the [`SparseRow`](crate::linalg::sparse::SparseRow)s of
    /// the one batch currently being reduced, at that batch's peak, and nothing else.** That is the
    /// whole scope. In particular it does **not** bound, and nothing in F4 bounds in bytes:
    ///
    /// - **symbolic preprocessing's pending monomial queue**, which is bounded in *monomials* by
    ///   [`Self::max_matrix_columns`] since #305 — it admits only distinct monomials, and a
    ///   batch's distinct monomials are its columns — but by nothing stated in bytes. At twenty
    ///   variables a monomial is 80 bytes against an entry's 16. See
    ///   [`F4Statistics::max_pending_monomials`](super::F4Statistics::max_pending_monomials).
    /// - the `examined` and `covered` monomial sets, and the preprocessed row vector;
    /// - the column vector, the monomial-to-column map, and the two temporaries construction
    ///   builds them from — four copies of the column monomials, three live at once;
    /// - **the pair queue**, which is `O(|G|²)` in the basis size while every budget here bounds a
    ///   function of one batch, plus two lazy-deletion sets that only grow. See
    ///   [`F4Statistics::peak_pair_queue`](super::F4Statistics::peak_pair_queue).
    /// - **the basis**, held twice for the whole computation and three times during the final
    ///   interreduction, at several times an entry's cost per term. See
    ///   [`F4Statistics::peak_basis_terms`](super::F4Statistics::peak_basis_terms).
    /// - the dense buffer a backend reduces through, which is *reported* instead — see
    ///   [`BatchStatistics::dense_buffer_bytes`](super::BatchStatistics::dense_buffer_bytes) —
    ///   because enforcing it here would make the default refuse computations the entry budget
    ///   admits, and under [`Backend::Dense`] it is a function of the shape alone, which the row
    ///   and column budgets already bound;
    /// - the elimination scratch buffer, which grows to its high-water mark and is never shrunk;
    /// - allocator slack: a `HashMap`'s power-of-two capacity and a `Vec`'s doubling, which the
    ///   payload arithmetic above excludes by construction.
    ///
    /// # How much that is
    ///
    /// **Measured, not estimated.** On `fukuoka-mq-III-n20-seed0` at a 20 000 000-entry cap the
    /// accounted peak is 195 MB and the process peaks at 14 075 MB: this budget sees **1.3%**. The
    /// omission does not scale with the budget either, so it cannot be used as a proxy even
    /// roughly. `docs/research/f4-resource-scaling.md` §9 has the per-site attribution and the
    /// method; `examples/f4_memory.rs` reproduces it.
    ///
    /// **So this is not a ceiling on the process and must not be read as one.** It is the knob that
    /// keeps *matrix* growth recoverable — which is what it was added for, and what it does well:
    /// the quantity is reproducible on any machine, where a resident-size limit is not. For the
    /// process figure use [`crate::util::peak_resident_bytes`].
    ///
    /// The name is deliberately unchanged. `max_entry_bytes` would describe the scope better, and
    /// the cost of renaming it is that every figure recorded against the old name becomes
    /// ambiguous — the same objection that made this a second budget rather than a redefinition of
    /// [`max_live_nonzeros`](Self::max_live_nonzeros). The scope is stated here instead.
    pub max_live_bytes: usize,

    /// The most batches to process before giving up, or `None` for no limit.
    pub max_batches: Option<usize>,

    /// How long the computation may run before giving up, or `None` — the default — for no limit.
    ///
    /// **Checked once per batch**, beside [`Self::max_batches`], which is what makes the statistics
    /// a crossing leaves behind describe whole batches rather than a matrix caught halfway through
    /// being built. `None` means no clock is read anywhere, so the shipping path contains no timing
    /// whether or not [`Self::measure_stages`] is set.
    ///
    /// **Not a resource bound, and the distinction is in the type**: a crossing is
    /// [`F4Error::TimeBudgetExceeded`], whose [`stop_kind`](F4Error::stop_kind) is
    /// [`StopKind::Time`] and never [`StopKind::Resource`]. A wall clock is a fact about one
    /// machine under one load, so a run stopped by it must not be compared against a run stopped
    /// by an entry count, which is reproducible anywhere. Ranking the two together would make a
    /// frontier depend on how busy the box was.
    ///
    /// It does not replace an external supervisor. A batch can be arbitrarily long — the elapsed
    /// time at a crossing is the budget *plus* whatever the batch in progress still needed — so a
    /// caller that must bound its own wall clock keeps a `recv_timeout` or equivalent as a hard
    /// backstop. What this adds is that the cooperative stop **returns**, and a return carries the
    /// statistics an abandoned thread cannot.
    pub max_wall_time: Option<Duration>,

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

    /// Whether a Hilbert prediction may influence how many pairs a degree contributes to one
    /// batch. See [`HilbertSelection`].
    ///
    /// **Not a criterion, and not a completeness risk.** Neither limiting mode discards a pair:
    /// a capped batch leaves the rest pending, and a deferred degree's pairs are promoted back
    /// before the computation can end. A wrong prediction therefore costs batches and never the
    /// answer — which is asserted over the correctness corpus, because the prediction is wrong on
    /// exactly the systems this milestone is about.
    pub hilbert: HilbertSelection,

    /// Check the returned basis independently before returning it.
    ///
    /// Off by default: the algorithm's completeness does not rest on it, and the check is
    /// `|G|²/2` normal forms. On when a caller wants the plan's §8.3 establishment of the result
    /// rather than an inference from the strategy having run — and whenever a measurement needs
    /// §8.5's total-including-the-check figure. A failed check is
    /// [`F4Error::CertificationFailed`], never a returned basis.
    pub certify: bool,

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

    /// Count the operations final interreduction's reductions perform, into
    /// [`super::F4Statistics::interreduction`].
    ///
    /// Separate from [`Self::measure_stages`] because the two have incomparable costs. That flag
    /// reads a clock four times a batch; this one increments a counter **once per reducer per term
    /// popped**, which is the innermost loop in F4, and it was measured at **36%** on
    /// `mq-random-10` where `measure_stages` costs 3.8%–11.5%.
    ///
    /// So a run cannot report both a trustworthy stage split and these counters, and the two are
    /// taken by separate runs. The counters are exact and machine-independent, which is what makes
    /// a slower run an acceptable price for them; the durations from such a run are not quotable.
    ///
    /// Setting this implies the split that `measure_stages` records, so it does not need both.
    pub count_interreduction: bool,

    /// How final interreduction is performed. See [`InterreductionRoute`].
    pub interreduction: InterreductionRoute,

    /// Leave each batch's rows in **reduced** row echelon form rather than merely echelon.
    ///
    /// Off by default until the A/B is on record, which is the discipline every other strategy
    /// flag in this struct follows.
    ///
    /// # What it changes, and what it cannot change
    ///
    /// Candidates are extracted from the rows whose leading column is new. Echelon is enough for
    /// that selection — back-substitution never changes a row's *leading* column — so this flag
    /// **cannot** change which rows become candidates, and
    /// `reduction::tests::test_the_row_form_does_not_change_candidate_selection` asserts that
    /// rather than arguing it. What it changes is each candidate's **tail**: an echelon row still
    /// carries entries in other pivots' columns, i.e. monomials that other basis elements lead
    /// with, so every batch emits candidates that are not in normal form and the debt is paid once
    /// at the end by final interreduction. #477 measured that final matrix at 405x the cells
    /// Groebner.jl's carries, and attributed it here.
    ///
    /// It cannot change the answer either, for the same reason
    /// [`Self::interreduce_by_matrix`] cannot: a reduced Gröbner basis is determined by its
    /// leading monomials.
    ///
    /// # What it costs
    ///
    /// A second sweep over every batch matrix, where the flag above pays one over a single much
    /// smaller matrix at the end. Back-substitution is quadratic in the rows whatever the sparsity
    /// (#168), the batch stage is already 13.90% of `mq-random-10`, and
    /// [`super::BlockPlan::InterreducedBlock`] was measured and **rejected** for filling in the
    /// reducer block — which is the same fill-in paid before the elimination instead of after it.
    /// So the prior is unfavourable and the measurement is the point.
    pub reduce_batch_rows: bool,

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
            max_wall_time: None,
            max_basis_elements: None,
            elimination: Backend::Sparse,
            reduction: ReductionStrategy::Unstructured,
            reducer_selection: ReducerSelection::FirstApplicable,
            criteria: PairCriteria::PRODUCT_ONLY,
            schedule: PairSchedule::DegreeThenLcm,
            hilbert: HilbertSelection::Off,
            certify: false,
            reducer_cache: CacheMode::Off,
            measure_stages: false,
            count_interreduction: false,
            interreduction: InterreductionRoute::Division,
            reduce_batch_rows: false,
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
    ///
    /// # The two live budgets this inherits are numerically identical over a 16-byte entry
    ///
    /// `max_live_nonzeros` is 20 000 000 and `max_live_bytes` is 320 000 000, and
    /// `320_000_000 / 16` is **exactly** 20 000 000. Over every `PrimeFieldElement64`
    /// instantiation — most of the corpus — the two knobs are therefore the same number by
    /// construction, and since
    /// [`live_entry_allowance`](Self::live_entry_allowance) is their `min`, **raising either one
    /// alone has no effect whatsoever**. Use [`with_live_budget`](Self::with_live_budget) or
    /// [`with_live_entries`](Self::with_live_entries), which set the pair together. The run #322
    /// was filed from lifted `max_live_nonzeros` to 200 000 000, met the identical refusal, and
    /// had to read the source to find out why.
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
        self.live_entry_allowance_for(Self::bytes_per_entry::<F>())
    }

    /// [`live_entry_allowance`](Self::live_entry_allowance) for a caller holding the entry width
    /// rather than the field type.
    ///
    /// A [`F4Statistics`](super::F4Statistics) record outlives the type parameter it was produced
    /// under and carries
    /// [`bytes_per_entry`](super::F4Statistics::bytes_per_entry) instead, so the budget
    /// arithmetic has to be reachable from the number. Delegated to rather than duplicated, which
    /// is what keeps the two from drifting apart.
    ///
    /// `bytes_per_entry` of zero — a statistics record from a run that built no matrix — is read
    /// as one rather than dividing by zero. [`budget_pressure`](super::F4Statistics::budget_pressure)
    /// rejects that case before it gets here.
    pub fn live_entry_allowance_for(&self, bytes_per_entry: usize) -> usize {
        self.max_live_nonzeros
            .min(self.max_live_bytes / bytes_per_entry.max(1))
    }

    /// Both live budgets set to the same quantity of memory, stated in bytes.
    ///
    /// **Use this rather than assigning either field alone.** The effective limit is the `min` of
    /// the two, so assigning one leaves the other binding — and at
    /// [`recommended`](Self::recommended) over a 16-byte entry they are numerically identical, so
    /// a lift of `max_live_nonzeros` by itself changes the limit by exactly nothing (#322). There
    /// is nothing to keep in step here: the entry count is derived.
    ///
    /// Generic over `F` because an entry's cost is, and the derivation is wrong by a factor of 2.5
    /// if it assumes the wrong width.
    pub fn with_live_budget<F: FiniteField>(mut self, bytes: usize) -> Self {
        self.max_live_bytes = bytes;
        self.max_live_nonzeros = bytes / Self::bytes_per_entry::<F>();
        self
    }

    /// Both live budgets set to the same quantity of memory, stated in entries.
    ///
    /// [`with_live_budget`](Self::with_live_budget) from the other direction, which is the
    /// direction the run #322 was filed from came at it: the caller thought in entries, raised
    /// `max_live_nonzeros` alone, and was refused at the old limit.
    pub fn with_live_entries<F: FiniteField>(mut self, entries: usize) -> Self {
        self.max_live_nonzeros = entries;
        self.max_live_bytes = entries.saturating_mul(Self::bytes_per_entry::<F>());
        self
    }

    /// Whether [`max_live_bytes`](Self::max_live_bytes) is the budget that binds over `F`.
    ///
    /// Strictly smaller, so that when the two budgets describe the same quantity the older error
    /// is the one reported and a figure recorded against it keeps its meaning.
    pub fn bytes_bind_first<F: FiniteField>(&self) -> bool {
        self.bytes_bind_first_for(Self::bytes_per_entry::<F>())
    }

    /// [`bytes_bind_first`](Self::bytes_bind_first) for a caller holding the entry width rather
    /// than the field type. See [`live_entry_allowance_for`](Self::live_entry_allowance_for).
    pub fn bytes_bind_first_for(&self, bytes_per_entry: usize) -> bool {
        self.live_entry_allowance_for(bytes_per_entry) < self.max_live_nonzeros
    }

    /// The live-memory allowance that binds over `F`, as prose for a provenance record.
    ///
    /// **A record has to quote the budget that bound, not whichever of the pair was written down.**
    /// The effective limit is the `min` of the two (#322), so a run configured with
    /// `max_live_bytes: 400_000_000` and `max_live_nonzeros` left at 20 000 000 is bounded at 320 MB
    /// over a 16-byte entry and the 400 MB is slack that never binds. A scoreboard row that
    /// recorded the slack figure overstated its own budget by 25%, and a reader reconciling a
    /// `stopped_at_limit` against it got the wrong number to compare with (#469).
    ///
    /// Derived rather than written out at the call site, which is what stops the text and the
    /// allowance drifting apart a second time. Names the field that bound, the same name
    /// [`F4Error::limit_name`] reports, so a record and the refusal it explains agree.
    ///
    /// Megabytes are powers of ten, matching how the budgets themselves are written.
    pub fn live_budget_policy<F: FiniteField>(&self) -> String {
        let entries = self.live_entry_allowance::<F>();
        format!(
            "{} MB live ({} entries at {} bytes; {} binds)",
            entries.saturating_mul(Self::bytes_per_entry::<F>()) / 1_000_000,
            entries,
            Self::bytes_per_entry::<F>(),
            if self.bytes_bind_first::<F>() {
                "max_live_bytes"
            } else {
                "max_live_nonzeros"
            }
        )
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

/// What kind of thing stopped an F4 computation.
///
/// Exists so that a consumer which ranks stops against each other cannot accidentally rank a wall
/// clock against an entry count. A resource stop is a reproducible property of the system and the
/// budget: the same system under the same budget crosses it on any machine, at the same degree,
/// with the same counters. A time stop is a property of **one machine under one load**, so two time
/// stops are not comparable with each other either, and a time stop compared against a resource
/// stop makes a frontier depend on how busy the box was.
///
/// Matched exhaustively by anything that reports a stop, so a new variant of [`F4Error`] forces the
/// question "is this a budget, a clock, or a caller mistake?" to be answered at the point it is
/// added rather than defaulted.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StopKind {
    /// A budget on the work the computation holds or does: rows, columns, entries, bytes, batches,
    /// basis elements. Reproducible, and rankable against another resource stop.
    Resource,

    /// [`F4Options::max_wall_time`] elapsed. **Never rankable against a [`Self::Resource`] stop.**
    Time,

    /// The options cannot be satisfied by any computation. A caller mistake, not an outcome.
    Caller,

    /// The computation finished and its basis failed [`F4Options::certify`]. Reaching this would be
    /// a defect in this crate, not a resource outcome.
    Certification,
}

/// Why an F4 computation stopped without a basis.
///
/// Most variants mean a limit in [`F4Options`] was crossed. The exceptions are
/// [`F4Error::CertificationFailed`], which means the computation finished and its result failed an
/// independent check, and [`F4Error::TimeBudgetExceeded`], which is a clock rather than a budget on
/// the work — see [`StopKind`] for why those two have to be told apart. There is deliberately no
/// variant for "finished but incomplete": a successful return is always a complete reduced Gröbner
/// basis.
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

    /// The computation did not finish within [`F4Options::max_wall_time`].
    ///
    /// **Not a resource bound.** [`Self::stop_kind`] reports [`StopKind::Time`], which is how a
    /// consumer keeps it out of a comparison against an entry or byte count: those are facts about
    /// a system and reproduce on any machine, and this is a fact about one machine under one load.
    ///
    /// `degree` is the selection degree of the batch the budget was noticed at — the batch had not
    /// been reduced, so it is the degree the computation *reached*, one above the highest it
    /// completed. The group-B counters that describe the work are **not** carried here; they are in
    /// the [`F4Statistics`](super::F4Statistics) that
    /// [`f4_reported`](crate::grobner::f4_reported) and
    /// [`f4_observed_reported`](crate::grobner::f4_observed_reported) return beside the `Result`,
    /// which is the whole point of a cooperative stop over an abandoned thread: the counters
    /// survive because the function returns.
    ///
    /// `elapsed_millis` is at least `budget_millis`, and may exceed it by a whole batch: the check
    /// is between batches, so a batch already in progress runs to completion. Both are reported so
    /// the overshoot is visible rather than inferred.
    TimeBudgetExceeded {
        degree: u64,
        elapsed_millis: u64,
        budget_millis: u64,
    },

    /// [`F4Options::max_wall_time`] elapsed during **final interreduction**, after the batch loop
    /// had finished.
    ///
    /// Separate from [`Self::TimeBudgetExceeded`] because that variant's `degree` is the selection
    /// degree of the batch the budget was noticed at, and this stage has no batch and no selection
    /// degree — reporting one would be a fabrication. The element counts are the honest measure of
    /// how far the stage got.
    ///
    /// **This is not a rare stop.** #349 measured interreduction at **80.4%** of `mq-random-10`,
    /// the instance M25 compared against Singular, so a budget that is honored at every batch can
    /// still be overrun by four fifths of the computation (#395). Before that issue the stage was
    /// not checked at all, and a bounded run could return an order of magnitude late.
    ///
    /// `elapsed_millis` may exceed `budget_millis` by one element's reduction: the check is before
    /// each element, and a single `normal_form` against a large basis is not interruptible.
    InterreductionTimeBudgetExceeded {
        /// Basis elements whose normal form was written back before the stop.
        elements_reduced: usize,
        /// Elements the minimized basis held, which is how many the stage had to do.
        elements: usize,
        elapsed_millis: u64,
        budget_millis: u64,
    },

    /// The basis held, or grew beyond, more elements than allowed.
    ///
    /// Applies to the generators as supplied, not only to what the computation appends: a basis
    /// that starts over the limit is over the limit.
    TooManyBasisElements { elements: usize, limit: usize },

    /// The options cannot be satisfied by any computation.
    InvalidOptions { reason: &'static str },

    /// The computation finished and the basis failed its independent check.
    ///
    /// Not a crossed limit, and the one variant that is not. It exists so that
    /// [`F4Options::certify`] has somewhere to report to **without** a code path that returns a
    /// basis which failed: the enum still has no variant meaning "finished but incomplete", and
    /// this one means "finished, checked, and the check said no" — which is a refusal, not a
    /// partial answer.
    ///
    /// Reaching it would be a defect rather than a resource outcome: no strategy in this crate
    /// discards a critical pair on heuristic grounds. It is wired up because a correctness claim
    /// that cannot fail is not a check.
    CertificationFailed { reason: &'static str },
}

impl F4Error {
    /// What kind of stop this is. See [`StopKind`].
    ///
    /// Exhaustive rather than defaulted, so adding a variant to [`F4Error`] stops compiling here
    /// until somebody says which kind it is.
    pub fn stop_kind(&self) -> StopKind {
        match self {
            Self::TooManyRows { .. }
            | Self::TooManyColumns { .. }
            | Self::TooManyNonzeros { .. }
            | Self::TooManyLiveBytes { .. }
            | Self::TooManyBatches { .. }
            | Self::TooManyBasisElements { .. } => StopKind::Resource,
            Self::TimeBudgetExceeded { .. } | Self::InterreductionTimeBudgetExceeded { .. } => {
                StopKind::Time
            }
            Self::InvalidOptions { .. } => StopKind::Caller,
            Self::CertificationFailed { .. } => StopKind::Certification,
        }
    }

    /// A stable name for the limit that bound, for a consumer to key a record on.
    ///
    /// The option's own field name wherever there is one, so a recorded result says which knob to
    /// turn. `invalid_options` and `certification` are not knobs and are named for what they are.
    pub fn limit_name(&self) -> &'static str {
        match self {
            Self::TooManyRows { .. } => "max_matrix_rows",
            Self::TooManyColumns { .. } => "max_matrix_columns",
            Self::TooManyNonzeros { .. } => "max_live_nonzeros",
            Self::TooManyLiveBytes { .. } => "max_live_bytes",
            Self::TooManyBatches { .. } => "max_batches",
            Self::TooManyBasisElements { .. } => "max_basis_elements",
            Self::TimeBudgetExceeded { .. } | Self::InterreductionTimeBudgetExceeded { .. } => {
                "max_wall_time"
            }
            Self::InvalidOptions { .. } => "invalid_options",
            Self::CertificationFailed { .. } => "certification",
        }
    }
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
            Self::TimeBudgetExceeded {
                degree,
                elapsed_millis,
                budget_millis,
            } => write!(
                f,
                "the computation did not finish within {} ms, and had reached degree {} after {} ms",
                budget_millis, degree, elapsed_millis
            ),
            Self::InterreductionTimeBudgetExceeded {
                elements_reduced,
                elements,
                elapsed_millis,
                budget_millis,
            } => write!(
                f,
                "the computation did not finish within {} ms: final interreduction had reduced {} \
                 of {} basis elements after {} ms",
                budget_millis, elements_reduced, elements, elapsed_millis
            ),
            Self::TooManyBasisElements { elements, limit } => write!(
                f,
                "the basis held {} elements, over the limit of {}",
                elements, limit
            ),
            Self::InvalidOptions { reason } => {
                write!(f, "the options are unsatisfiable: {}", reason)
            }
            Self::CertificationFailed { reason } => write!(
                f,
                "the computed basis failed its independent check: {}",
                reason
            ),
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
                for reducer_selection in ReducerSelection::ALL {
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

    /// Raising the entry budget alone changes the allowance by nothing, and the error says so.
    ///
    /// The trap #322 was filed for. `recommended()`'s two budgets are numerically identical over a
    /// 16-byte entry, so the effective limit is the `min` and lifting one knob leaves the other
    /// binding at exactly the old value. What made it cost a run is that the refusal has to name
    /// the budget that *bound* and not the one the caller just raised, or the message points away
    /// from the cause.
    #[test]
    fn test_raising_the_entry_budget_alone_moves_nothing_and_the_error_names_the_byte_budget() {
        let default = F4Options::default();
        let lifted = F4Options {
            max_live_nonzeros: 200_000_000,
            ..F4Options::default()
        };
        assert_eq!(
            lifted.live_entry_allowance::<Narrow>(),
            default.live_entry_allowance::<Narrow>(),
            "a 10x lift of one knob must not change the effective limit when the other binds"
        );
        assert!(lifted.bytes_bind_first::<Narrow>());
        assert_eq!(
            lifted.entry_budget_error::<Narrow>(20_000_112),
            F4Error::TooManyLiveBytes {
                bytes: 20_000_112 * 16,
                limit: 320_000_000
            },
            "the refusal must not name the 200000000 the caller set and the run never met"
        );
    }

    /// `with_live_budget` sets the pair consistently, so the half-done lift cannot be written.
    #[test]
    fn test_one_live_budget_sets_both_knobs_at_every_field_width() {
        for bytes in [320_000_000usize, 3_200_000_000, 1_000] {
            let narrow = F4Options::default().with_live_budget::<Narrow>(bytes);
            assert_eq!(narrow.max_live_bytes, bytes);
            assert_eq!(narrow.live_entry_allowance::<Narrow>(), bytes / 16);
            assert_eq!(narrow.max_live_nonzeros, bytes / 16);
            assert!(
                !narrow.bytes_bind_first::<Narrow>(),
                "the two must describe the same quantity, so neither binds first"
            );

            // The same bytes over a 40-byte entry is a different entry count, which is the whole
            // reason the derivation has to know the field.
            let wide = F4Options::default().with_live_budget::<Bn254Fr>(bytes);
            assert_eq!(wide.max_live_nonzeros, bytes / 40);
            assert_eq!(wide.live_entry_allowance::<Bn254Fr>(), bytes / 40);
        }
    }

    /// `with_live_entries` is the same consistency from the other direction, the victim's own.
    #[test]
    fn test_one_live_budget_in_entries_sets_the_byte_budget_to_match() {
        let lifted = F4Options::default().with_live_entries::<Narrow>(200_000_000);
        assert_eq!(lifted.max_live_nonzeros, 200_000_000);
        assert_eq!(lifted.max_live_bytes, 200_000_000 * 16);
        assert_eq!(lifted.live_entry_allowance::<Narrow>(), 200_000_000);
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

    /// The policy prose states the allowance that binds, and names the budget it came from.
    ///
    /// The #469 configuration is the case: `max_live_bytes: 400_000_000` with `max_live_nonzeros`
    /// left at the default is **320 MB** over a 16-byte entry, and a record that quoted the
    /// 400 MB overstated its own budget by 25%.
    #[test]
    fn test_the_policy_prose_states_the_budget_that_binds() {
        let scoreboard = F4Options {
            max_live_bytes: 400_000_000,
            ..F4Options::default()
        };
        assert_eq!(F4Options::bytes_per_entry::<Narrow>(), 16);
        assert_eq!(
            scoreboard.live_budget_policy::<Narrow>(),
            "320 MB live (20000000 entries at 16 bytes; max_live_nonzeros binds)"
        );
        assert!(!scoreboard.live_budget_policy::<Narrow>().contains("400"));

        // When the byte budget is the one that binds, the prose says so and quotes what it pays
        // for rather than the entry count that did not apply.
        let wide = F4Options {
            max_live_bytes: 400_000_000,
            ..F4Options::default()
        };
        assert!(wide.bytes_bind_first::<Bn254Fr>());
        assert_eq!(
            wide.live_budget_policy::<Bn254Fr>(),
            "400 MB live (10000000 entries at 40 bytes; max_live_bytes binds)"
        );
    }

    /// The prose and the error cannot disagree about which budget bound.
    ///
    /// They are two renderings of one fact, and the failure #469 records is a record whose policy
    /// text names a different budget from the refusal it is supposed to explain.
    #[test]
    fn test_the_policy_prose_and_the_error_name_the_same_budget() {
        for options in [
            F4Options::default(),
            F4Options {
                max_live_bytes: 400_000_000,
                ..F4Options::default()
            },
            F4Options {
                max_live_nonzeros: usize::MAX,
                max_live_bytes: 1_600,
                ..F4Options::default()
            },
        ] {
            let crossed = options.live_entry_allowance::<Narrow>() + 1;
            let name = options.entry_budget_error::<Narrow>(crossed).limit_name();
            assert!(
                options.live_budget_policy::<Narrow>().contains(name),
                "the policy prose {:?} does not name {}",
                options.live_budget_policy::<Narrow>(),
                name
            );
        }
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
