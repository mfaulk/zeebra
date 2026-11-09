//! Counters describing the work an F4 computation performed.
//!
//! Wall-clock time says a computation was slow; it does not say whether the matrices were large,
//! whether elimination filled them in, or how many of the rows were there only to make the
//! reduction possible. These are the numbers that attribute the cost, and they are plain counters,
//! so they belong in an example binary rather than in Criterion.

use std::time::{Duration, Instant};

use crate::{
    grobner::pairs::CriterionCounts, linalg::sparse::EliminationStatistics, poly::NormalFormCounts,
};

/// The shape of the one matrix a matrix interreduction built, and whether it ran at all.
///
/// Reported because the stage's cost is a property of this shape, and because the comparand's is
/// known: Groebner.jl's `f4_autoreduce!` on `mq-random-10` built **250 x 604** and spent 1.74 ms
/// in it (`docs/research/groebner-jl-gap.md` §4).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct MatrixInterreduction {
    /// Rows: the minimized basis elements, plus the reducer multiples the closure added.
    pub rows: usize,
    /// Columns, i.e. distinct monomials in the closure.
    pub columns: usize,
    /// Nonzero entries at construction.
    pub nonzeros: usize,
    /// Nonzero entries live at once at elimination's high-water mark.
    ///
    /// Reported beside [`Self::nonzeros`] because the two are far apart and only this one is
    /// comparable with the live-entry allowance: on `katsura-11` under grevlex the matrix is built
    /// at 11 311 802 entries and reduced at 103 865 277, 5.19x the 20 000 000 the allowance admits
    /// (#536). Zero when the route fell back, since no elimination ran.
    pub peak_nonzeros: usize,
    /// Entries the rows' buffers were allocated for at that high-water.
    ///
    /// The figure that explains the resident cost. On `katsura-11` it was **18 126.4 MB** against a
    /// 1 584.9 MB payload and a 13 144.3 MB process peak — more than the peak, because capacity is
    /// reserved and `VmHWM` counts touched pages, so the one site covered the whole of it (#536).
    /// #554 closed the gap by having
    /// [`SparseRow::subtract_scaled`](crate::linalg::sparse::SparseRow::subtract_scaled) copy the
    /// merge result back rather than install the buffer it reserved, which takes the same rung to
    /// 1.81x the payload; what is left is each row's own `Vec` growth history.
    pub peak_entry_capacity: usize,
    /// Elements in the minimized basis, i.e. how many rows were seeds rather than reducers.
    pub elements: usize,
    /// Set when a budget refused the matrix and the division route ran instead.
    ///
    /// A run that fell back produces the same basis by the old mechanism, so its timings describe
    /// the division route and must not be quoted as the matrix route's.
    pub fell_back: bool,

    /// Which budget refused, when one did.
    ///
    /// Recorded rather than discarded for the reason #322 exists: that issue is three of F4's four
    /// budgets having been discovered one refusal at a time, because a refusal named a budget that
    /// was not the binding one. A fallback that reported only *that* it happened would repeat the
    /// mistake on a new path.
    pub refused_by: Option<MatrixRefusal>,
}

/// Which budget refused a matrix interreduction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MatrixRefusal {
    /// The closure needed more rows than `max_matrix_rows`.
    Rows { limit: usize },
    /// The matrix needed more distinct monomials than `max_matrix_columns`.
    Columns { limit: usize },
    /// The matrix needed more nonzero entries than the live-entry allowance **to build**.
    Nonzeros { nonzeros: usize },
    /// Elimination's fill-in crossed the live-entry allowance.
    ///
    /// The refusal #536 added, and the one that fires in practice: a matrix well inside the
    /// allowance at construction can be reduced at tens of times it.
    LiveEntries { nonzeros: usize },
}

/// Where the time in a batch, or in a whole computation, went.
///
/// A total says a computation was slow. Only a breakdown says whether to attack preprocessing,
/// construction, or the linear algebra — and, after a change, whether cost was removed or merely
/// moved from one stage to another. Zero throughout unless
/// [`F4Options::measure_stages`](super::F4Options::measure_stages) is set.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct StageTimings {
    /// Symbolic preprocessing: finding the rows the batch needs.
    pub symbolic: Duration,

    /// Macaulay matrix construction: the column mapping and writing the entries.
    pub construction: Duration,

    /// Elimination.
    pub elimination: Duration,

    /// Candidate extraction, including converting the surviving rows back to polynomials.
    pub extraction: Duration,

    /// The final interreduction: minimizing the basis and reducing each element modulo the rest.
    ///
    /// Not per batch — it happens once, after the pair queue empties — but reported here so that
    /// it is inside [`StageTimings::sum`] and therefore inside the stage breakdown. It is here at
    /// all because the first measurement taken with this instrumentation found it to be **84% of
    /// katsura-6 under lex**, which no counter in the preceding milestone could have shown: that
    /// instance builds 59 matrices and returns a six-element basis, so the cost is neither in the
    /// matrices nor in the answer but in the reduction between them.
    pub interreduction: Duration,

    /// [`minimize_grobner_basis`]'s half of `interreduction`: monic scaling, deduplication, the
    /// divisibility prune, and the ascending sort.
    ///
    /// Split out because #436 measured the two halves at **0.06% / 99.94%** on `mq-random-10` and
    /// that figure existed only in a commit message — this field is one `Duration`, so nothing in
    /// the tree could re-derive which half the stage was in. `interreduction_minimize +
    /// interreduction_reduce == interreduction`, asserted by
    /// `test_the_interreduction_split_sums_to_the_stage`.
    pub interreduction_minimize: Duration,

    /// The reduction loop's half of `interreduction`: one `normal_form` per basis element.
    ///
    /// This is the one `docs/research/groebner-jl-gap.md` §4 is about, and the stage share it
    /// carries is why: 24 136 ms over 247 elements against a comparand's 1.74 ms for the same
    /// stage.
    pub interreduction_reduce: Duration,

    /// How `construction` divided between column collection, the map, and the scatter.
    ///
    /// Refines `construction` rather than extending it, like the interreduction split above, so it
    /// is folded by [`StageTimings::add`] and excluded from [`StageTimings::sum`].
    pub construction_split: ConstructionTimings,
}

/// Where [`MacaulayMatrix::build_measured`](super::macaulay::MacaulayMatrix::build_measured)
/// spent its time, as a partition of the whole call.
///
/// The three phases exist as separate counters because #330 stated its refutation condition on
/// their ratio before anything was implemented: handing out column indices during interning can
/// only remove `columns` and `map`, so if those two are a small share of the total then the cost
/// is in `scatter`, which that restructuring does not touch.
///
/// That is what happened, so `scatter` carries two refining fields of its own (#582). Refinements
/// are excluded from [`Self::total`]: `collect + sort + map + scatter` is the whole call, and
/// `scatter_rows + scatter_assemble` is the whole of `scatter`.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ConstructionTimings {
    /// Inserting every row monomial into the distinct-monomial set.
    ///
    /// Split from `sort` because the two have different fates under a column-index handout: this
    /// phase repeats hashing that symbolic preprocessing already did in its own `examined` set and
    /// is therefore removable, while the sort is not — msolve orders its columns too.
    pub collect: Duration,

    /// Sorting the distinct monomials into descending column order.
    pub sort: Duration,

    /// Building the monomial-to-column map over the sorted columns.
    pub map: Duration,

    /// Writing every row's entries through the map, and assembling the matrix.
    pub scatter: Duration,

    /// The per-row half of `scatter`: the multiplier shift, the column lookup and the row build.
    ///
    /// Refines `scatter` rather than extending it, so it is **not** in [`Self::total`]. Split out
    /// for #582, which found the scatter at 89% of construction with no counter ever having been
    /// inside it. The finer split the issue asks for — shift against lookup against row build — is
    /// per *term*, where a clock read costs more than the work it would time, so it comes from
    /// [`ScatterPrefix`](super::macaulay::ScatterPrefix)'s ablation instead of from a counter here.
    pub scatter_rows: Duration,

    /// The assembly half of `scatter`: `SparseMatrix::new` and the row-provenance copy.
    ///
    /// #582's hypothesis 3 is exactly this field being non-negligible: `preprocessed.rows.clone()`
    /// is a `Vec<PreprocessedRow<N>>` per matrix and was inside the undivided scatter lap.
    pub scatter_assemble: Duration,
}

impl ConstructionTimings {
    /// Every phase added together, which is the whole of the measured call.
    pub fn total(&self) -> Duration {
        self.collect + self.sort + self.map + self.scatter
    }

    /// The set and the sort together: #330's phase (1), before it was split further.
    pub fn columns(&self) -> Duration {
        self.collect + self.sort
    }

    /// The share of the total spent on the phases #330's kill criterion is stated on.
    ///
    /// That is `columns() + map`, phases (1)+(2) of the issue, over the whole. Under one third,
    /// #330 said to close. Zero when nothing was measured, so a caller does not have to guard
    /// against a zero total.
    pub fn handout_share(&self) -> f64 {
        self.share(self.columns() + self.map)
    }

    /// The share a column-index handout could actually remove: the set and the map, not the sort.
    ///
    /// This is the narrower and more honest figure. `handout_share` charges the sort to the
    /// hypothesis, but interning with an index does not remove a sort from anybody — msolve sorts
    /// its columns as well, and that sort is where its A|B split comes from. So this is the number
    /// an implementation decision should rest on, and it can be far below `handout_share`.
    pub fn removable_share(&self) -> f64 {
        self.share(self.collect + self.map)
    }

    /// The share of the **scatter** spent assembling the matrix rather than writing rows.
    ///
    /// Over `scatter` and not over the total, because it prices one hypothesis inside one stage.
    /// Zero when nothing was measured.
    pub fn assembly_share(&self) -> f64 {
        let scatter = self.scatter.as_secs_f64();
        if scatter == 0.0 {
            return 0.0;
        }
        self.scatter_assemble.as_secs_f64() / scatter
    }

    /// `part` over the total, or zero when nothing was measured.
    fn share(&self, part: Duration) -> f64 {
        let total = self.total().as_secs_f64();
        if total == 0.0 {
            return 0.0;
        }
        part.as_secs_f64() / total
    }

    /// Fold another matrix's phases into these.
    pub fn add(&mut self, other: &Self) {
        self.collect += other.collect;
        self.sort += other.sort;
        self.map += other.map;
        self.scatter += other.scatter;
        self.scatter_rows += other.scatter_rows;
        self.scatter_assemble += other.scatter_assemble;
    }
}

impl StageTimings {
    /// Every stage added together.
    ///
    /// Still less than a computation's wall clock: pair selection and basis bookkeeping are
    /// outside every stage. The difference is left visible rather than folded into one of them,
    /// which is what [`F4Statistics::stage_coverage`] reports.
    pub fn sum(&self) -> Duration {
        // The interreduction and construction splits are deliberately **not** added: they refine
        // a stage rather than extending it, and adding them would double every millisecond they
        // describe in the coverage figure.
        self.symbolic + self.construction + self.elimination + self.extraction + self.interreduction
    }

    /// Fold another batch's timings into these.
    pub fn add(&mut self, other: &Self) {
        self.symbolic += other.symbolic;
        self.construction += other.construction;
        self.elimination += other.elimination;
        self.extraction += other.extraction;
        self.interreduction += other.interreduction;
        self.interreduction_minimize += other.interreduction_minimize;
        self.interreduction_reduce += other.interreduction_reduce;
        self.construction_split.add(&other.construction_split);
    }
}

/// A clock that is not read at all when measurement is off.
///
/// `Instant::now()` is a syscall-free read of a monotonic counter, but it is still tens of
/// nanoseconds and it is a compiler fence. Holding an `Option` rather than a flag means the
/// disabled path is a null check that branch prediction gets right every time, and that the clock
/// read does not appear in the instruction stream of the measured code at all.
#[derive(Clone, Copy, Debug)]
pub struct StageClock {
    /// When the clock was created, for [`StageClock::elapsed`]. `None` when disabled.
    start: Option<Instant>,

    /// When the current lap started.
    lap: Option<Instant>,
}

impl StageClock {
    /// A clock that measures only if `enabled`.
    pub fn new(enabled: bool) -> Self {
        let now = enabled.then(Instant::now);
        Self {
            start: now,
            lap: now,
        }
    }

    /// The time since the last `lap`, or since construction if there has not been one, and start
    /// a new lap.
    ///
    /// Zero when disabled, so a caller adds it unconditionally rather than branching. Consecutive
    /// laps partition the interval: they do not overlap and they leave no gap, so adding them up
    /// gives the time from construction to the last lap.
    pub fn lap(&mut self) -> Duration {
        match self.lap.as_mut() {
            Some(lap) => {
                let now = Instant::now();
                let elapsed = now.duration_since(*lap);
                *lap = now;
                elapsed
            }
            None => Duration::ZERO,
        }
    }

    /// The time since construction. Laps do not reset it.
    pub fn elapsed(&self) -> Duration {
        match self.start {
            Some(start) => start.elapsed(),
            None => Duration::ZERO,
        }
    }
}

/// What a Hilbert-driven selection predicted and what happened.
///
/// Zero throughout unless [`F4Options::hilbert`](super::F4Options::hilbert) is active. The two
/// element counts are the comparison the strategy has to be judged on: a prediction that is
/// consistently *below* what a degree yields is capping too hard and costing batches, and one that
/// is consistently above is inert.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct HilbertCounts {
    /// Degrees at which the predicted quota was smaller than the pairs available.
    pub degrees_limited: usize,

    /// Pairs a cap left pending for a later batch at the same degree.
    pub pairs_withheld: usize,

    /// Pairs moved out of the pending set and into the deferred set.
    pub pairs_deferred: usize,

    /// Deferred pairs returned to the pending set.
    ///
    /// Must equal [`Self::pairs_deferred`] less whatever Gebauer-Moller removed while they were
    /// deferred. A successful computation with pairs still deferred would be a defect, and the main
    /// loop cannot produce one: its termination test counts deferred pairs as work.
    pub pairs_promoted: usize,

    /// Times the exact or predicted half of the quota could not be computed.
    ///
    /// A failure means **no limit** was applied, which is the safe reading. Counted because a run
    /// in which it happened often is a run whose cap was mostly inert, and that is not the same
    /// result as a cap that did not bite.
    pub predictions_unavailable: usize,

    /// Summed over the degrees where a quota was computed: the quota, before slack and clamping.
    pub predicted_new_elements: i128,

    /// Summed over those same degrees: the new basis elements the degree actually produced.
    pub observed_new_elements: usize,

    /// The model's degree of regularity, if the expansion reached it.
    pub degree_of_regularity: Option<u64>,
}

impl HilbertCounts {
    /// Predicted new elements against observed, over the degrees a quota was computed for.
    ///
    /// One means the prediction was exactly right in total; below one means it predicted fewer than
    /// appeared, which is the direction that caps too hard. Zero when nothing was observed.
    pub fn prediction_ratio(&self) -> f64 {
        if self.observed_new_elements == 0 {
            0.0
        } else {
            self.predicted_new_elements as f64 / self.observed_new_elements as f64
        }
    }
}

/// What one batch of critical pairs cost.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BatchStatistics {
    /// Pairs reduced in this batch, after the product criterion.
    pub pairs: usize,

    /// Rows in the Macaulay matrix.
    pub rows: usize,

    /// Of those, rows that are reducer multiples rather than halves of a critical pair.
    ///
    /// These are the rows symbolic preprocessing had to add to make the reduction possible. A high
    /// proportion means the batch spent most of its matrix on reduction scaffolding.
    pub reducer_rows: usize,

    /// Columns in the Macaulay matrix, i.e. distinct monomials across all rows.
    pub columns: usize,

    /// What the elimination did.
    pub elimination: EliminationStatistics,

    /// New basis elements extracted, i.e. rows whose leading monomial was new.
    pub candidates: usize,

    /// `size_of::<(usize, F)>()` for the field this batch ran over.
    ///
    /// Carried rather than derived because nothing downstream of here knows `F`: these counters
    /// are field-agnostic, and the whole point of a byte figure is that it is not.
    pub bytes_per_entry: usize,

    /// Bytes the elimination backend allocated outside the sparse rows.
    ///
    /// `rows * columns` cells under [`Backend::Dense`](crate::linalg::echelon::Backend::Dense),
    /// one row-wide accumulator under
    /// [`Adaptive`](crate::linalg::echelon::Backend::Adaptive), nothing under
    /// [`Sparse`](crate::linalg::echelon::Backend::Sparse).
    ///
    /// **Not covered by [`F4Options::max_live_bytes`](super::F4Options::max_live_bytes)**, and
    /// reported here so that the figure the budget omits is at least visible. Under the dense
    /// backend it dwarfs the entries: katsura-7's largest grevlex matrix is 6810x6862, which is
    /// 374 MB of cells against roughly 22 MB of entries.
    pub dense_buffer_bytes: usize,

    /// Where this batch's time went. Zero unless stage measurement is on.
    pub stages: StageTimings,

    /// Reducer rows whose built form came from a cache rather than being rebuilt.
    ///
    /// Zero unless reducer reuse is on. Reported next to [`BatchStatistics::reducer_rows`] because
    /// the ratio of the two is the only thing that says whether caching was worth doing.
    pub reducer_rows_reused: usize,

    /// Divisor lookups symbolic preprocessing performed, i.e. monomials tested for reducibility.
    pub divisor_queries: usize,

    /// Basis elements examined across all those lookups.
    ///
    /// With a linear scan this is on the order of `divisor_queries` times the basis size; the
    /// point of an index is to break that relationship, and this is the counter that shows whether
    /// it did.
    pub divisor_scan_steps: usize,

    /// Divisibility tests the divmask probe replayed; see
    /// [`SymbolicCounts::divmask_tests`](super::SymbolicCounts::divmask_tests). Zero unless
    /// [`F4Options::measure_divmask`](super::F4Options::measure_divmask) is set.
    pub divmask_tests: usize,

    /// Of those, the tests that answered not-divisible.
    pub divmask_negative: usize,

    /// Of those negatives, the tests a 32-bit calibrated mask would have decided.
    pub divmask_decided: usize,

    /// Monomials symbolic preprocessing offered to its queue, before the deduplication test.
    pub monomials_enqueued: usize,

    /// The largest the pending monomial queue grew, in monomials.
    ///
    /// Reported beside [`Self::dense_buffer_bytes`] and for the same reason: it is memory this
    /// batch held and no budget counted. At twenty variables a monomial is 80 bytes, so this
    /// exceeds [`Self::peak_live_bytes`] whenever the queue holds more than a twentieth as many
    /// monomials as the matrix holds entries. Since #305 it is at most [`Self::columns`], the
    /// batch's distinct monomials, so `max_matrix_columns` bounds it even though no budget names
    /// it.
    pub max_pending_monomials: usize,

    /// True if this batch was eliminated by the structured path rather than the one-pass echelon.
    pub structured: bool,

    /// Rows that were established as pivots without any row operation.
    ///
    /// For the structured path this is the reducer block, whose rows have distinct leading
    /// monomials by construction. The unstructured path finds the same thing by accident where it
    /// happens, so this is comparable between the two.
    pub free_pivots: usize,

    /// Rows the back-substitution pass examined, or `None` when
    /// [`super::F4Options::reduce_batch_rows`] was off.
    ///
    /// `Some(0)` and `None` are different findings: the first says the batch's echelon form was
    /// already reduced and so carried no debt forward, the second says nobody looked. #477 exists
    /// because the debt is real on `mq-random-10`, and this is where a batch reports its share.
    pub back_substituted_rows: Option<usize>,

    /// Distinct leading monomials among the input rows.
    ///
    /// `reducer_rows` of them come from the reducer block, whose leading monomials are distinct by
    /// construction, and the rest are the distinct lcms of the batch's pairs. Every one is a pivot
    /// column of the echelon form, which makes `rank - input_leading_monomials` exactly the number
    /// of new basis elements — see [`super::degrees`] for the identity and its test.
    pub input_leading_monomials: usize,

    /// The lcm degree the batch was selected at: the largest pair degree in it.
    ///
    /// Zero for an empty batch. The main loop selects one degree at a time, so for every batch it
    /// drives this is *the* degree; a caller calling [`super::reduce_batch`] with pairs of mixed
    /// degree gets the largest, which is what the candidate-degree comparison below needs.
    pub batch_degree: u64,

    /// The smallest total degree of any new basis element this batch produced.
    pub min_candidate_degree: Option<u64>,

    /// The largest total degree of any new basis element this batch produced.
    pub max_candidate_degree: Option<u64>,

    /// New basis elements whose own total degree is below [`Self::batch_degree`].
    ///
    /// Mutants: relations arriving at a lower degree than the schedule that found them. Always
    /// counted — it is one `degree()` call per candidate, and candidates are rare — because
    /// M22-D's question is whether they occur at all.
    pub candidates_below_batch_degree: usize,

    /// The largest total degree of any monomial appearing as a matrix column.
    ///
    /// Zero unless [`F4Options::profile_degrees`](super::F4Options::profile_degrees) is set: it is
    /// a scan of the column vector, which costs nothing against building the matrix but is still
    /// work the shipping path has no use for.
    pub max_column_degree: u64,
}

impl BatchStatistics {
    /// Rows that are halves of a critical pair rather than reduction scaffolding.
    pub fn candidate_rows(&self) -> usize {
        self.rows.saturating_sub(self.reducer_rows)
    }

    /// Rank the pair rows added on top of the reducer block.
    ///
    /// Reducer rows have distinct leading monomials, so they span a space of dimension exactly
    /// `reducer_rows`; everything the elimination found above that came from the pairs. Exact and
    /// independent of the order the rows were eliminated in, because rank is.
    pub fn candidate_rank_contribution(&self) -> usize {
        self.elimination.rank.saturating_sub(self.reducer_rows)
    }

    /// Pair rows that added no rank.
    ///
    /// Equal to [`BatchStatistics::elimination`]'s zero-row count, since reducer rows never reduce
    /// to zero. Named for what it measures rather than how it is computed.
    pub fn dependent_candidate_rows(&self) -> usize {
        self.candidate_rows()
            .saturating_sub(self.candidate_rank_contribution())
    }
    /// Bytes of matrix entries live at this batch's peak.
    ///
    /// What [`F4Options::max_live_bytes`](super::F4Options::max_live_bytes) is enforced on.
    pub fn peak_live_bytes(&self) -> usize {
        self.elimination
            .peak_nonzeros
            .saturating_mul(self.bytes_per_entry)
    }

    /// Bytes this batch is estimated to have held at once: its entries plus its dense buffers.
    ///
    /// The two are live together, so they are added rather than maxed. Still an estimate of the
    /// matrix alone — see [`F4Options::max_live_bytes`](super::F4Options::max_live_bytes) for what
    /// no figure here accounts for.
    pub fn estimated_bytes(&self) -> usize {
        self.peak_live_bytes()
            .saturating_add(self.dense_buffer_bytes)
    }
}

/// What a whole F4 computation cost.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct F4Statistics {
    /// Pairs taken off the queue.
    pub pairs_considered: usize,

    /// Pairs discarded by Buchberger's first criterion, without reaching a matrix.
    ///
    /// Kept as its own field rather than folded into [`F4Statistics::criteria`] because it is the
    /// counter the preceding milestone's measurements are stated in, and a comparison against them
    /// has to read the same number.
    pub pairs_eliminated_by_product_criterion: usize,

    /// Pairs discarded, broken down by the criterion that discarded them.
    pub criteria: CriterionCounts,

    /// Pairs that reached a matrix.
    pub pairs_reduced: usize,

    /// Batches reduced. A batch with every pair eliminated by the criterion is not counted.
    pub batches: usize,

    /// The largest batch, in pairs.
    pub max_pairs_per_batch: usize,

    /// Basis elements appended during the computation, before interreduction.
    pub elements_added: usize,

    /// Batches that produced no new basis element at all.
    ///
    /// The F4 analogue of Buchberger's zero reductions: the whole matrix reduced to relations the
    /// basis already implied. Buchberger pays one full reduction per such pair; F4 pays one matrix
    /// for all of them at once, which is the saving the algorithm exists for.
    pub empty_batches: usize,

    /// The largest lcm degree of any pair selected.
    pub max_pair_degree: u64,

    /// The selection degree of each batch, in the order the batches ran.
    ///
    /// Magma's `GroebnerBasis` added exactly this as a second return value in V2.26 — "the integer
    /// sequence of degrees encountered in each step of the F4 algorithm" — and the sequence is
    /// strictly more informative than [`F4Statistics::max_pair_degree`]: the degree a system
    /// stalls at, whether it climbed monotonically or jumped, and where a degree-fall happened are
    /// all invisible in a maximum. [`F4Statistics::degrees`] is not a substitute either, because
    /// it is keyed *by* degree, so a degree revisited after a drop appears once and the order is
    /// gone.
    ///
    /// # One entry per batch that built a matrix
    /// `step_degrees.len() == batches`, by construction: the push sits beside the increment in
    /// [`F4Statistics::record`]'s caller. A selection every pair criterion discarded built nothing
    /// and is **not** a step here, which is also why the maximum of this sequence can be *below*
    /// `max_pair_degree` — that field is accumulated over the pairs as selected, before the
    /// criteria run. The two agree on every system in the corpus; the inequality is the invariant.
    ///
    /// Always collected. One `u64` push per batch, against batch counts in the hundreds, is
    /// unmeasurable beside a matrix construction — so unlike `degrees` it is not gated on an
    /// option a measurement has to remember to set.
    pub step_degrees: Vec<u64>,

    /// The largest number of rows in any matrix.
    pub max_matrix_rows: usize,

    /// The largest number of columns in any matrix.
    pub max_matrix_columns: usize,

    /// The largest number of nonzero entries live in any elimination.
    ///
    /// This is the memory question: how big did the biggest matrix get. It is deliberately not the
    /// fill-in question — see `worst_fill_in_peak`.
    pub max_live_nonzeros: usize,

    /// Nonzero entries in the matrix that reached `max_live_nonzeros`, as it was built.
    ///
    /// Context for `max_live_nonzeros`: how dense the biggest matrix was to begin with.
    pub max_live_nonzeros_as_built: usize,

    /// `size_of::<(usize, F)>()` for the field the computation ran over.
    ///
    /// Set before the first batch, so it is right even for a computation that builds no matrix at
    /// all. The one number here that depends on the field rather than on the system, and the one
    /// that turns every entry count above into a quantity of memory.
    pub bytes_per_entry: usize,

    /// The largest [`BatchStatistics::dense_buffer_bytes`] of any batch.
    pub max_dense_buffer_bytes: usize,

    /// The largest [`BatchStatistics::estimated_bytes`] of any batch.
    ///
    /// The max of a per-batch *sum*, not the sum of two maxima: entries and dense buffers are live
    /// together within a batch, and the batch with the biggest matrix is not necessarily the one
    /// with the widest buffer.
    pub max_estimated_bytes: usize,

    /// The peak live entries of the batch whose elimination filled in the most, proportionally.
    ///
    /// Tracked separately from `max_live_nonzeros` because **the biggest matrix is not necessarily
    /// the one that densified worst**. A batch going from 100 entries to 800 fills in eightfold; a
    /// batch going from 1000 to 1500 fills in by half but has the larger absolute peak. Reporting
    /// the second as the worst fill-in would understate how badly sparse elimination can behave,
    /// which is precisely the measurement a later dense/sparse threshold has to rest on.
    pub worst_fill_in_peak: usize,

    /// That same batch's entry count as built — the denominator of [`F4Statistics::worst_fill_in`].
    pub worst_fill_in_as_built: usize,

    /// Summed over every batch: nonzero entries in the matrices as built.
    pub total_initial_nonzeros: usize,

    /// Summed over every batch: nonzero entries after elimination.
    pub total_final_nonzeros: usize,

    /// Summed over every batch: row operations performed.
    pub row_operations: usize,

    /// Summed over every batch: modular inverses taken to normalize a pivot.
    pub pivot_inversions: usize,

    /// Summed over every batch: rows that reduced to zero.
    pub zero_rows: usize,

    /// Summed over every batch: reducer multiples added by symbolic preprocessing.
    pub reducer_rows: usize,

    /// The largest number of terms in any basis element produced.
    pub max_terms: usize,

    /// Summed over every batch: where the time went. Zero unless stage measurement is on.
    pub stages: StageTimings,

    /// The whole computation's wall clock, including the work outside any stage.
    ///
    /// Zero unless stage measurement is on. Reported so that `stages.sum()` can be compared
    /// against it: what the stages do not account for is pair selection, basis bookkeeping, and
    /// the final interreduction, and if that difference is large it is the thing to look at next.
    pub total: Duration,

    /// Summed over every batch: reducer rows served from a cache rather than rebuilt.
    pub reducer_rows_reused: usize,

    /// Summed over every batch: monomials tested for reducibility.
    pub divisor_queries: usize,

    /// Summed over every batch: basis elements examined across those tests.
    pub divisor_scan_steps: usize,

    /// Summed over every batch: divisibility tests the divmask probe replayed.
    ///
    /// Equal to [`Self::divisor_scan_steps`] when
    /// [`F4Options::measure_divmask`](super::F4Options::measure_divmask) is set and zero when it
    /// is not, which is what makes the two figures below read against the population the shipping
    /// path actually performs rather than against a second traversal of the basis.
    pub divmask_tests: usize,

    /// Summed over every batch: of those tests, the ones that answered not-divisible.
    pub divmask_negative: usize,

    /// Summed over every batch: of those negatives, the ones a 32-bit calibrated mask would have
    /// decided without an exponent comparison.
    ///
    /// The #331 figure. [`Self::divmask_decided_share`] is it as a fraction, and the share worth
    /// quoting is of [`Self::divmask_tests`] and not of [`Self::divmask_negative`]: a positive
    /// answer is a test no mask can shortcut, and it is in the stage's cost regardless.
    pub divmask_decided: usize,

    /// What the **final interreduction** cost in operations, as opposed to in time.
    ///
    /// `divisor_queries` and `divisor_scan_steps` above cover the *batch* path only, so the stage
    /// `docs/research/groebner-jl-gap.md` §3 measures at 13 871x the comparand's had no operation
    /// counters at all — and §4's attribution of it to intermediate swell was explicitly recorded
    /// as inferred rather than measured. This is the measurement.
    ///
    /// Zero unless [`F4Options::measure_stages`](super::F4Options::measure_stages) is set.
    pub interreduction: NormalFormCounts,

    /// What the matrix interreduction route did, when
    /// [`F4Options::interreduction`](super::F4Options::interreduction) selected it.
    ///
    /// `None` when the division route ran — either because the flag was off, or because a budget
    /// refused the matrix and the run fell back. The distinction is recorded rather than silent,
    /// because a figure taken from a run that fell back is a figure about the division route.
    pub interreduction_matrix: Option<MatrixInterreduction>,

    /// Elements in the minimized basis that final interreduction reduced.
    ///
    /// Not [`Self::elements_added`]: minimization runs first and drops the subsumed ones, so this
    /// is the loop's actual trip count and the denominator for a per-element cost.
    pub interreduction_elements: usize,

    /// Summed over every batch: monomials symbolic preprocessing offered to its queue, before the
    /// deduplication test.
    ///
    /// See [`SymbolicCounts::monomials_enqueued`](super::SymbolicCounts::monomials_enqueued). The
    /// repetition factor rather than a memory figure: since #305 only the distinct offers are
    /// admitted, so the gap between this and
    /// [`Self::max_pending_monomials`](Self::max_pending_monomials) is what the deduplication
    /// saves rather than what the queue costs.
    pub monomials_enqueued: usize,

    /// The largest the pending monomial queue grew in any batch, in monomials.
    ///
    /// Costs `size_of::<Monomial<N>>()` each — 80 bytes at twenty variables — and is still **not**
    /// covered by [`F4Options::max_live_bytes`](super::F4Options::max_live_bytes), which bounds
    /// matrix entries. It is nonetheless bounded, by `max_matrix_columns`: the queue holds only
    /// distinct monomials, and a batch's distinct monomials are its columns. A maximum rather than
    /// a sum: one batch's queue is dropped before the next one's is built.
    pub max_pending_monomials: usize,

    /// The pair queue at its largest, in entries, measured once per batch.
    ///
    /// The structure that grows as `O(B²)` in the basis size while every budget in
    /// [`F4Options`](super::F4Options) bounds a function of one batch. Each field peaks at its own
    /// moment, so they are maxed independently — see
    /// [`PairQueueFootprint::max`](crate::grobner::pairs::PairQueueFootprint::max).
    pub peak_pair_queue: crate::grobner::pairs::PairQueueFootprint,

    /// Basis elements held at the computation's largest, before interreduction.
    ///
    /// The basis is stored twice while the loop runs — as polynomials and as a
    /// [`MonicBasis`](super::MonicBasis) — and three times during the final interreduction. None of
    /// it is in the entry budget.
    pub peak_basis_elements: usize,

    /// Terms summed over every basis element, at the moment the basis was largest.
    ///
    /// The quantity that turns [`Self::peak_basis_elements`] into bytes: a term is a
    /// `Monomial<N>` and a field element in a hash map, so it costs more than
    /// [`Self::bytes_per_entry`] per term and is counted by neither budget.
    pub peak_basis_terms: usize,

    /// Batches eliminated by the structured path.
    pub structured_batches: usize,

    /// Summed over every batch: pivots established without a row operation.
    pub free_pivots: usize,

    /// Summed over every batch: rows the back-substitution pass examined, or `None` when
    /// [`super::F4Options::reduce_batch_rows`] was off for every batch.
    ///
    /// The price side of #477's trade, in the unit the price is paid in. The payoff side is
    /// [`Self::interreduction_matrix`]'s shape, which is why the two are reported together.
    pub back_substituted_rows: Option<usize>,

    /// Summed over every batch: rank the pair rows added on top of the reducer block.
    ///
    /// The useful-work figure. See [`super::degrees`] for why this and not the zero-row count.
    pub candidate_rank_contribution: usize,

    /// Summed over every batch: pair rows that added no rank.
    pub dependent_candidate_rows: usize,

    /// Summed over every batch: new basis elements of degree below their batch's selection degree.
    pub mutant_elements: usize,

    /// Batches that produced at least one such element.
    ///
    /// Distinct from [`Self::mutant_elements`]: one batch can produce several, and the question
    /// M22-D asks is about *batches* — whether a batch that finds a lower-degree relation is
    /// followed by work at a lower degree.
    pub batches_with_mutants: usize,

    /// The largest gap between a batch's selection degree and the degree of an element it produced.
    ///
    /// Three means a degree-7 matrix yielded a degree-4 relation. The size of the gap is what
    /// decides whether a mutant is interesting: a relation one degree early is the ordinary
    /// behaviour of an inhomogeneous computation, and one four degrees early is information the
    /// schedule had no way to anticipate.
    pub max_mutant_degree_gap: u64,

    /// Batches whose selection degree was **below** the previous batch's.
    ///
    /// The operational measure of whether lower-degree relations are exploited. F4 selects the
    /// lowest pending degree every time, so a relation that creates lower-degree pairs is acted on
    /// at the very next batch — and this counts the times that happened, rather than arguing that
    /// it must.
    pub degree_regressions: usize,

    /// Of those, regressions immediately after a batch that produced a mutant.
    ///
    /// The attribution. A regression can also follow an ordinary batch — a new element of the
    /// batch's own degree can pair low with an old one — so the two counts have to be separate or
    /// the mechanism cannot be credited with anything.
    pub regressions_after_mutants: usize,

    /// The largest drop in selection degree between consecutive batches.
    pub max_degree_drop: u64,

    /// The largest total degree of any monomial that appeared as a matrix column.
    ///
    /// **Not the same quantity as [`F4Statistics::max_pair_degree`]**, and in general larger:
    /// reducer multiples carry monomials above the lcm their batch was selected at. Neither figure
    /// is the solving degree or the degree of regularity, which are properties of the ideal and not
    /// of a run. Zero unless
    /// [`F4Options::profile_degrees`](super::F4Options::profile_degrees) is set.
    pub max_monomial_degree: u64,

    /// What a Hilbert-driven selection predicted and what happened.
    ///
    /// Zero throughout unless [`F4Options::hilbert`](super::F4Options::hilbert) is active.
    pub hilbert: HilbertCounts,

    /// What certifying the returned basis checked and cost.
    ///
    /// `None` unless [`F4Options::certify`](super::F4Options::certify) is set. Reported separately
    /// from [`F4Statistics::total`] — which includes it — so that a strategy that skips work can be
    /// compared on its cost both with and without the check, which is what the milestone plan's
    /// §8.5 requires.
    pub certification: Option<super::certify::CertificationReport>,

    /// What happened at each selection degree.
    ///
    /// Empty unless [`F4Options::profile_degrees`](super::F4Options::profile_degrees) is set. The
    /// counters above are sums and maxima over the whole run; this is the same work broken out by
    /// the degree it was done at.
    pub degrees: super::degrees::DegreeProfile,
}

impl F4Statistics {
    /// Append one batch's selection degree to [`F4Statistics::step_degrees`].
    ///
    /// Separate from [`F4Statistics::record`] because [`BatchStatistics`] does not carry the
    /// degree its batch was selected at — the main loop reads it off the pair queue — and because
    /// a caller driving batches itself has to supply it. Call it once per `record`, so the two
    /// stay in step.
    pub fn record_step_degree(&mut self, degree: u64) {
        self.step_degrees.push(degree);
    }

    /// The largest degree any batch was selected at, or `None` if no matrix was built.
    ///
    /// The quantity `cost_model`'s `solving_degree` wants: a run's observed maximum selection
    /// degree. **Not the solving degree or the degree of regularity of the ideal**, which are
    /// properties of the ideal rather than of a run — see
    /// [`F4Statistics::max_monomial_degree`] for the same caution.
    ///
    /// `None` rather than zero for an empty run, because zero is a degree a batch could in
    /// principle be selected at and a consumer cannot tell the two apart.
    pub fn observed_solving_degree(&self) -> Option<u64> {
        self.step_degrees.iter().copied().max()
    }

    /// Fold one batch's counters into the totals.
    ///
    /// Public because [`super::reduce_batch`] is: a caller driving batches itself accumulates the
    /// same way the main loop does.
    pub fn record(&mut self, batch: &BatchStatistics) {
        self.batches += 1;
        self.max_pairs_per_batch = self.max_pairs_per_batch.max(batch.pairs);
        self.max_matrix_rows = self.max_matrix_rows.max(batch.rows);
        self.max_matrix_columns = self.max_matrix_columns.max(batch.columns);
        if batch.elimination.peak_nonzeros > self.max_live_nonzeros {
            self.max_live_nonzeros = batch.elimination.peak_nonzeros;
            self.max_live_nonzeros_as_built = batch.elimination.initial_nonzeros;
        }

        // Constant across a computation, so assigned rather than maxed. A caller driving batches
        // itself gets it from the first batch; the main loop sets it before any batch runs, so a
        // computation that builds no matrix still reports the field's entry size.
        self.bytes_per_entry = batch.bytes_per_entry;
        self.max_dense_buffer_bytes = self.max_dense_buffer_bytes.max(batch.dense_buffer_bytes);
        self.max_estimated_bytes = self.max_estimated_bytes.max(batch.estimated_bytes());

        // The worst *ratio*, which is a different batch in general. Compared by cross-multiplying
        // rather than by dividing, so the comparison is exact; `u128` because the product of two
        // entry counts can exceed a `u64` on a large enough problem.
        let (peak, built) = (
            batch.elimination.peak_nonzeros as u128,
            batch.elimination.initial_nonzeros as u128,
        );
        let (worst_peak, worst_built) = (
            self.worst_fill_in_peak as u128,
            self.worst_fill_in_as_built as u128,
        );
        // A batch with no entries has no ratio. Otherwise take it if nothing is recorded yet, or
        // if its ratio beats what is: peak/built > worst_peak/worst_built, cross-multiplied.
        let beats_the_record = worst_built == 0 || peak * worst_built > worst_peak * built;
        if built > 0 && beats_the_record {
            self.worst_fill_in_peak = batch.elimination.peak_nonzeros;
            self.worst_fill_in_as_built = batch.elimination.initial_nonzeros;
        }
        self.total_initial_nonzeros += batch.elimination.initial_nonzeros;
        self.total_final_nonzeros += batch.elimination.final_nonzeros;
        self.row_operations += batch.elimination.row_operations;
        self.pivot_inversions += batch.elimination.pivot_inversions;
        self.zero_rows += batch.elimination.zero_rows;
        self.reducer_rows += batch.reducer_rows;
        self.stages.add(&batch.stages);
        self.reducer_rows_reused += batch.reducer_rows_reused;
        self.divisor_queries += batch.divisor_queries;
        self.divisor_scan_steps += batch.divisor_scan_steps;
        self.divmask_tests += batch.divmask_tests;
        self.divmask_negative += batch.divmask_negative;
        self.divmask_decided += batch.divmask_decided;
        self.monomials_enqueued += batch.monomials_enqueued;
        self.max_pending_monomials = self.max_pending_monomials.max(batch.max_pending_monomials);
        self.free_pivots += batch.free_pivots;
        if let Some(rows) = batch.back_substituted_rows {
            *self.back_substituted_rows.get_or_insert(0) += rows;
        }
        self.candidate_rank_contribution += batch.candidate_rank_contribution();
        self.dependent_candidate_rows += batch.dependent_candidate_rows();
        self.mutant_elements += batch.candidates_below_batch_degree;
        self.max_monomial_degree = self.max_monomial_degree.max(batch.max_column_degree);
        if batch.structured {
            self.structured_batches += 1;
        }
        if batch.candidates == 0 {
            self.empty_batches += 1;
        }
    }

    /// The fraction of reducer rows that were served from a cache rather than rebuilt.
    ///
    /// Zero when nothing was cached, which is also the answer when caching is off. This is the
    /// number that decides whether a reducer cache earns its complexity, and it should be measured
    /// before one is built.
    pub fn reducer_reuse_fraction(&self) -> f64 {
        if self.reducer_rows == 0 {
            0.0
        } else {
            self.reducer_rows_reused as f64 / self.reducer_rows as f64
        }
    }

    /// The fraction of symbolic preprocessing's divisibility tests a 32-bit calibrated divisor
    /// mask would have decided, in `[0, 1]`.
    ///
    /// Zero when the probe was off, which is also what it reports for a probe that decided
    /// nothing. The two are told apart by [`Self::divmask_tests`] being zero or not, and a caller
    /// that quotes this figure has to say which it had.
    pub fn divmask_decided_share(&self) -> f64 {
        if self.divmask_tests == 0 {
            0.0
        } else {
            self.divmask_decided as f64 / self.divmask_tests as f64
        }
    }

    /// Basis elements examined per divisor lookup, on average.
    ///
    /// One for a perfect index, and on the order of the basis size for a linear scan. Zero when no
    /// lookup was counted.
    pub fn divisor_scan_steps_per_query(&self) -> f64 {
        if self.divisor_queries == 0 {
            0.0
        } else {
            self.divisor_scan_steps as f64 / self.divisor_queries as f64
        }
    }

    /// The reduction loop's share of the final interreduction stage, as a fraction in `[0, 1]`.
    ///
    /// Zero unless [`F4Options::measure_stages`](super::F4Options::measure_stages) is set. #436
    /// measured **0.9994** on `mq-random-10`, against `minimize_grobner_basis`'s 0.0006: the
    /// stage's cost is a statement about `normal_form`, not about the duplicated basis storage
    /// #304 removed.
    pub fn interreduction_reduce_share(&self) -> f64 {
        let total = self.stages.interreduction_minimize + self.stages.interreduction_reduce;
        if total.is_zero() {
            0.0
        } else {
            self.stages.interreduction_reduce.as_secs_f64() / total.as_secs_f64()
        }
    }

    /// Terms `normal_form` popped per term of the final reduced basis, over the whole stage.
    ///
    /// The swell factor, and the number `docs/research/groebner-jl-gap.md` §4 inferred rather than
    /// measured. One means every term the stage looked at survived into the answer; a hundred
    /// means it built and destroyed ninety-nine for every one it kept, which is the cost a matrix
    /// formulation does not pay.
    pub fn interreduction_swell_factor(&self) -> f64 {
        self.interreduction.swell_factor()
    }

    /// The share of the computation's wall clock the four stages account for.
    ///
    /// Zero when nothing was timed. Well below one means the cost is somewhere the stage
    /// breakdown does not look — pair selection, basis bookkeeping, or interreduction.
    pub fn stage_coverage(&self) -> f64 {
        if self.total.is_zero() {
            0.0
        } else {
            self.stages.sum().as_secs_f64() / self.total.as_secs_f64()
        }
    }

    /// The worst fill-in observed: over every batch, the largest ratio of peak live entries to the
    /// entries that batch's matrix was built with.
    ///
    /// One when no matrix was built. Above one means elimination made some matrix denser than it
    /// started, which is the cost a sparse representation pays and the reason the peak is budgeted.
    ///
    /// This is a maximum over ratios, not the ratio at the maximum: see
    /// [`F4Statistics::worst_fill_in_peak`] for why those differ and why both are reported.
    pub fn worst_fill_in(&self) -> f64 {
        if self.worst_fill_in_as_built == 0 {
            1.0
        } else {
            self.worst_fill_in_peak as f64 / self.worst_fill_in_as_built as f64
        }
    }

    /// The fill-in of the largest matrix, which is not in general the worst fill-in.
    ///
    /// Reported alongside [`F4Statistics::worst_fill_in`] so the two can be compared: when they
    /// differ, the matrix that strained memory most and the matrix that densified most were
    /// different batches.
    pub fn fill_in_of_the_largest_matrix(&self) -> f64 {
        if self.max_live_nonzeros_as_built == 0 {
            1.0
        } else {
            self.max_live_nonzeros as f64 / self.max_live_nonzeros_as_built as f64
        }
    }

    /// Bytes of matrix entries live at the peak of the largest elimination.
    ///
    /// [`max_live_nonzeros`](Self::max_live_nonzeros) in the unit
    /// [`F4Options::max_live_bytes`](super::F4Options::max_live_bytes) is enforced in. This is the
    /// figure that differs between field widths on an otherwise identical computation, by the ratio
    /// of their [`bytes_per_entry`](Self::bytes_per_entry).
    pub fn peak_live_bytes(&self) -> usize {
        self.max_live_nonzeros.saturating_mul(self.bytes_per_entry)
    }

    /// The fraction of matrix rows that were reduction scaffolding rather than pair halves.
    ///
    /// Zero when no matrix was built.
    pub fn reducer_row_fraction(&self) -> f64 {
        let rows = 2 * self.pairs_reduced + self.reducer_rows;
        if rows == 0 {
            0.0
        } else {
            self.reducer_rows as f64 / rows as f64
        }
    }

    /// The fraction of pair rows that added no rank.
    ///
    /// M22's first research question — *what fraction of F4's work is redundant* — in one number.
    /// It is deliberately stated over **pair rows** rather than over pairs: a pair contributes two
    /// rows and either, neither, or both can be dependent, so there is no pair-level reading of
    /// this figure. Zero when no pair row was built.
    pub fn dependent_row_fraction(&self) -> f64 {
        let built = self.dependent_candidate_rows + self.candidate_rank_contribution;
        if built == 0 {
            0.0
        } else {
            self.dependent_candidate_rows as f64 / built as f64
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{BatchStatistics, ConstructionTimings, F4Statistics, StageClock, StageTimings};
    use crate::linalg::sparse::EliminationStatistics;
    use std::time::Duration;

    /// Recording a batch accumulates the sums and raises the maxima.
    #[test]
    fn test_record_accumulates() {
        let mut statistics = F4Statistics::default();

        statistics.record(&BatchStatistics {
            pairs: 3,
            rows: 8,
            reducer_rows: 2,
            columns: 12,
            elimination: EliminationStatistics {
                rank: 6,
                zero_rows: 2,
                initial_nonzeros: 20,
                final_nonzeros: 18,
                peak_nonzeros: 25,
                row_operations: 7,
                pivot_inversions: 1,
            },
            candidates: 1,
            ..Default::default()
        });
        statistics.record(&BatchStatistics {
            pairs: 1,
            rows: 4,
            reducer_rows: 1,
            columns: 20,
            elimination: EliminationStatistics {
                rank: 3,
                zero_rows: 1,
                initial_nonzeros: 9,
                final_nonzeros: 7,
                peak_nonzeros: 11,
                row_operations: 2,
                pivot_inversions: 0,
            },
            candidates: 0,
            ..Default::default()
        });

        assert_eq!(statistics.batches, 2);
        assert_eq!(statistics.max_pairs_per_batch, 3);
        assert_eq!(statistics.max_matrix_rows, 8);
        assert_eq!(
            statistics.max_matrix_columns, 20,
            "the maximum, not the last"
        );
        assert_eq!(statistics.max_live_nonzeros, 25);
        assert_eq!(
            statistics.max_live_nonzeros_as_built, 20,
            "the denominator comes from the batch that peaked, not the other one"
        );
        // The first batch grew 20 -> 25 and the second 9 -> 11, so 1.25x beats 1.22x: here
        // the worst ratio and the largest matrix happen to be the same batch.
        assert_eq!(
            (
                statistics.worst_fill_in_peak,
                statistics.worst_fill_in_as_built
            ),
            (25, 20)
        );
        assert_eq!(statistics.total_initial_nonzeros, 29);
        assert_eq!(statistics.total_final_nonzeros, 25);
        assert_eq!(statistics.row_operations, 9);
        assert_eq!(statistics.pivot_inversions, 1);
        assert_eq!(statistics.zero_rows, 3);
        assert_eq!(statistics.reducer_rows, 3);
        assert_eq!(
            statistics.empty_batches, 1,
            "the second batch produced none"
        );
    }

    /// Fill-in is one before any matrix is built.
    #[test]
    fn test_worst_fill_in_of_nothing() {
        let statistics = F4Statistics::default();
        assert_eq!(statistics.worst_fill_in(), 1.0);
        assert_eq!(statistics.fill_in_of_the_largest_matrix(), 1.0);
    }

    /// The worst fill-in is the largest *ratio*, not the ratio of the largest matrix.
    ///
    /// Regression test. The implementation used to record the batch with the greatest absolute
    /// peak and then divide that batch's peak by its own initial count, which answers a different
    /// question. On the two batches below — 1000 entries growing to 1500, and 100 growing to 800 —
    /// it reported 1.5x as the worst fill-in when the honest answer is 8x. That mattered because
    /// the next milestone has to use this number to decide when sparse elimination stops paying.
    #[test]
    fn test_worst_fill_in_is_the_largest_ratio() {
        let batch = |initial: usize, peak: usize| BatchStatistics {
            elimination: EliminationStatistics {
                initial_nonzeros: initial,
                peak_nonzeros: peak,
                ..Default::default()
            },
            ..Default::default()
        };

        let mut statistics = F4Statistics::default();
        statistics.record(&batch(1000, 1500)); // 1.5x, and the larger matrix
        statistics.record(&batch(100, 800)); // 8.0x, and the worse fill-in

        assert_eq!(statistics.worst_fill_in(), 8.0);
        assert_eq!(
            statistics.max_live_nonzeros, 1500,
            "memory is still sized by the largest matrix"
        );
        assert_eq!(
            statistics.fill_in_of_the_largest_matrix(),
            1.5,
            "and that matrix's own fill-in is still available"
        );

        // Order of arrival does not matter.
        let mut reversed = F4Statistics::default();
        reversed.record(&batch(100, 800));
        reversed.record(&batch(1000, 1500));
        assert_eq!(reversed.worst_fill_in(), 8.0);
        assert_eq!(reversed.max_live_nonzeros, 1500);
    }

    /// A batch that did not densify at all does not displace a worse one.
    #[test]
    fn test_worst_fill_in_ignores_flat_batches() {
        let mut statistics = F4Statistics::default();
        statistics.record(&BatchStatistics {
            elimination: EliminationStatistics {
                initial_nonzeros: 10,
                peak_nonzeros: 25,
                ..Default::default()
            },
            ..Default::default()
        });
        assert_eq!(statistics.worst_fill_in(), 2.5);

        // Bigger absolute peak, but it barely grew.
        statistics.record(&BatchStatistics {
            elimination: EliminationStatistics {
                initial_nonzeros: 1000,
                peak_nonzeros: 1001,
                ..Default::default()
            },
            ..Default::default()
        });
        assert_eq!(statistics.worst_fill_in(), 2.5);
        assert_eq!(statistics.max_live_nonzeros, 1001);

        // An empty matrix has no ratio to speak of and must not divide by zero.
        statistics.record(&BatchStatistics::default());
        assert_eq!(statistics.worst_fill_in(), 2.5);
    }

    /// The reducer fraction is zero before any matrix is built, and a proportion after.
    #[test]
    fn test_reducer_row_fraction() {
        let mut statistics = F4Statistics::default();
        assert_eq!(statistics.reducer_row_fraction(), 0.0);

        // Two pairs give four halves; six reducer rows out of ten is 0.6.
        statistics.pairs_reduced = 2;
        statistics.reducer_rows = 6;
        assert_eq!(statistics.reducer_row_fraction(), 0.6);
    }

    /// A disabled clock reports no time at all, so the measured path has none in it.
    #[test]
    fn test_a_disabled_clock_measures_nothing() {
        let mut clock = StageClock::new(false);
        for _ in 0..4 {
            assert_eq!(clock.lap(), Duration::ZERO);
        }
        assert_eq!(clock.elapsed(), Duration::ZERO);
    }

    /// Consecutive laps partition the interval they cover: their sum is bounded by the total.
    #[test]
    fn test_laps_partition_the_elapsed_time() {
        let mut clock = StageClock::new(true);

        // Enough work that the clock has something to measure.
        let mut sum = 0u64;
        let mut laps = Duration::ZERO;
        for round in 0..4u64 {
            for i in 0..50_000u64 {
                sum = sum.wrapping_add(i * round);
            }
            laps += clock.lap();
        }
        assert_ne!(sum, u64::MAX, "the work must not be optimized away");

        let total = clock.elapsed();
        assert!(laps > Duration::ZERO, "the clock measured nothing");
        // The laps end at the last `lap` call, which is before `elapsed` was read, so the sum of
        // the laps cannot exceed the total.
        assert!(
            laps <= total,
            "laps {:?} exceeded the total {:?}",
            laps,
            total
        );
    }

    /// Stage timings fold together and sum to their parts.
    #[test]
    fn test_stage_timings_accumulate() {
        let one = StageTimings {
            symbolic: Duration::from_micros(10),
            construction: Duration::from_micros(20),
            elimination: Duration::from_micros(30),
            extraction: Duration::from_micros(40),
            interreduction: Duration::from_micros(50),
            interreduction_minimize: Duration::from_micros(2),
            interreduction_reduce: Duration::from_micros(48),
            construction_split: ConstructionTimings {
                collect: Duration::from_micros(3),
                sort: Duration::from_micros(1),
                map: Duration::from_micros(2),
                scatter: Duration::from_micros(14),
                scatter_rows: Duration::from_micros(12),
                scatter_assemble: Duration::from_micros(2),
            },
        };
        // Both refinements — the interreduction halves and the construction phases — refine a
        // stage rather than extending it, so the sum is still 150 and not 220. A coverage figure
        // that double-counted a stage would exceed 1.0.
        assert_eq!(one.sum(), Duration::from_micros(150));
        assert_eq!(
            one.interreduction_minimize + one.interreduction_reduce,
            one.interreduction
        );
        assert_eq!(one.construction_split.total(), one.construction);

        let mut total = StageTimings::default();
        total.add(&one);
        total.add(&one);
        assert_eq!(total.symbolic, Duration::from_micros(20));
        assert_eq!(total.interreduction, Duration::from_micros(100));
        assert_eq!(total.sum(), Duration::from_micros(300));
        assert_eq!(total.construction_split.scatter, Duration::from_micros(28));
        assert_eq!(total.construction_split.total(), total.construction);
    }

    /// The construction split's two shares price different things: the criterion charges the sort
    /// to the hypothesis and the removable share does not.
    #[test]
    fn test_the_construction_shares_price_the_criterion_and_the_sort_separately() {
        let split = ConstructionTimings {
            collect: Duration::from_micros(20),
            sort: Duration::from_micros(10),
            map: Duration::from_micros(10),
            scatter: Duration::from_micros(60),
            ..ConstructionTimings::default()
        };
        assert_eq!(split.total(), Duration::from_micros(100));
        assert_eq!(split.columns(), Duration::from_micros(30));
        // (collect + sort + map) / total, which is what #330's criterion is stated on.
        assert_eq!(split.handout_share(), 0.4);
        // (collect + map) / total: the sort survives the restructuring, so it is not counted.
        assert_eq!(split.removable_share(), 0.3);
        assert_eq!(ConstructionTimings::default().handout_share(), 0.0);
        assert_eq!(ConstructionTimings::default().removable_share(), 0.0);
    }

    /// The scatter's halves refine the stage rather than extending it, and fold independently.
    #[test]
    fn test_the_scatter_halves_refine_the_scatter() {
        let split = ConstructionTimings {
            collect: Duration::from_micros(20),
            sort: Duration::from_micros(10),
            map: Duration::from_micros(10),
            scatter: Duration::from_micros(60),
            scatter_rows: Duration::from_micros(50),
            scatter_assemble: Duration::from_micros(10),
        };
        // The halves are inside `scatter`, so the total is 100 and not 160.
        assert_eq!(split.total(), Duration::from_micros(100));
        assert_eq!(split.scatter_rows + split.scatter_assemble, split.scatter);
        assert!((split.assembly_share() - 1.0 / 6.0).abs() < 1e-12);
        assert_eq!(ConstructionTimings::default().assembly_share(), 0.0);

        let mut folded = ConstructionTimings::default();
        folded.add(&split);
        folded.add(&split);
        assert_eq!(folded.scatter_rows, Duration::from_micros(100));
        assert_eq!(folded.scatter_assemble, Duration::from_micros(20));
        assert_eq!(
            folded.scatter_rows + folded.scatter_assemble,
            folded.scatter
        );
        assert_eq!(folded.total(), Duration::from_micros(200));
    }

    /// Recording a batch accumulates the new per-stage and per-strategy counters too.
    #[test]
    fn test_record_accumulates_the_strategy_counters() {
        let batch = |structured: bool| BatchStatistics {
            reducer_rows: 10,
            reducer_rows_reused: 4,
            divisor_queries: 100,
            divisor_scan_steps: 700,
            structured,
            free_pivots: 6,
            stages: StageTimings {
                symbolic: Duration::from_micros(5),
                ..Default::default()
            },
            ..Default::default()
        };

        let mut statistics = F4Statistics::default();
        statistics.record(&batch(true));
        statistics.record(&batch(false));

        assert_eq!(statistics.reducer_rows, 20);
        assert_eq!(statistics.reducer_rows_reused, 8);
        assert_eq!(statistics.reducer_reuse_fraction(), 0.4);
        assert_eq!(statistics.divisor_queries, 200);
        assert_eq!(statistics.divisor_scan_steps, 1400);
        assert_eq!(statistics.divisor_scan_steps_per_query(), 7.0);
        assert_eq!(statistics.structured_batches, 1, "one of the two");
        assert_eq!(statistics.free_pivots, 12);
        assert_eq!(statistics.stages.symbolic, Duration::from_micros(10));
    }

    /// The derived ratios are zero rather than NaN before anything has been measured.
    #[test]
    fn test_ratios_of_nothing() {
        let statistics = F4Statistics::default();
        assert_eq!(statistics.reducer_reuse_fraction(), 0.0);
        assert_eq!(statistics.divisor_scan_steps_per_query(), 0.0);
        assert_eq!(statistics.stage_coverage(), 0.0);
    }

    /// Stage coverage is the share of the total the four stages account for.
    #[test]
    fn test_stage_coverage() {
        let statistics = F4Statistics {
            stages: StageTimings {
                symbolic: Duration::from_millis(1),
                construction: Duration::from_millis(1),
                elimination: Duration::from_millis(1),
                extraction: Duration::from_millis(1),
                interreduction: Duration::from_millis(0),
                ..Default::default()
            },
            total: Duration::from_millis(5),
            ..Default::default()
        };
        assert!((statistics.stage_coverage() - 0.8).abs() < 1e-12);
    }
}
