use crate::grobner::fglm::BorderBatch;

/// How the multiplication operators' columns are computed.
///
/// Every variant must produce **the same operators**, entry for entry. They differ in how much
/// reduction work is shared, not in what the answer is, and the tests assert that by comparing
/// whole [`QuotientAlgebra`](super::QuotientAlgebra) values across strategies rather than by
/// comparing the lex basis they eventually lead to.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum OperatorConstruction {
    /// One normal form per nonstandard column, as M17 did.
    ///
    /// The reference. A border monomial reached from several columns is reduced several times, and
    /// the repeated answers are provably identical — which is the waste the other variants remove,
    /// and the reason this one is kept as something to compare against rather than deleted.
    PerColumn,

    /// One normal form per *distinct* border monomial, reused by every column that reaches it.
    ///
    /// Strictly fewer reductions than [`Self::PerColumn`] — between a fifth and a third fewer on
    /// the benchmark corpus — at the cost of holding `|∂B|` coordinate vectors at once. That is
    /// not free and is measured rather than waved away: see §5 of
    /// `docs/MILESTONE-FGLM-SCALABILITY.md`.
    DeduplicatedBorder,

    /// Border monomials reduced in batches, sharing a symbolic closure and its reducer multiples.
    ///
    /// Deduplicated too — a batch's targets are the *distinct* border monomials — so this is
    /// [`Self::DeduplicatedBorder`] with F4-style linear algebra where the scalar reductions were.
    /// The closure is built once per batch and the arithmetic runs over integer column indices
    /// rather than through a polynomial's hash map.
    ///
    /// **The targets do not reduce one another.** Each has its own normal form, so the pivots are
    /// fixed before any target is touched and no target becomes one. See
    /// [`batch`](super::batch) and [`BorderBatch`](super::BorderBatch) for the limits.
    ///
    /// The default since M18-5, whose ablation measured it at least as fast as [`Self::PerColumn`]
    /// on every system in the corpus at [`BorderBatch::recommended`]'s batch size.
    #[default]
    BatchedBorder,
}

/// How a reduced multiplication-operator column is stored.
///
/// A storage choice and nothing more: every variant must give the same columns, the same
/// applications, and the same nonzero counts. Only the cells and the bytes may differ.
///
/// The crossover is real inside the benchmark corpus rather than hypothetical. A reduced column
/// holds 79% of `D` on katsura-7 and 0.14% on planted-10, and a sparse entry costs an index as well
/// as a coefficient — so neither representation wins everywhere and nor does any whole-operator
/// choice. See §7 of `docs/MILESTONE-FGLM-SCALABILITY.md`.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum OperatorStorage {
    /// Every reduced column as `(index, coefficient)` pairs, as M17 did. The reference.
    Sparse,

    /// Each column in whichever of the two allocates fewer bytes.
    ///
    /// Decided **per column**, not per operator: different columns of one operator have
    /// substantially different densities, so a whole-operator choice would be wrong for some of
    /// them by construction. A column with no entries is always the sparse side, so a zero column
    /// still allocates nothing.
    ///
    /// The default since M18-5. It is never larger than [`Self::Sparse`] — it picks whichever is
    /// smaller a column at a time — and 1.41x smaller on katsura-7, for a few percent of operator
    /// *application*, which is not where a conversion's time goes.
    #[default]
    Adaptive,

    /// Every reduced column as `D` coefficients.
    ///
    /// For measurement: it is the wrong choice on most of the corpus, and exists so that the
    /// adaptive policy can be shown to be better than either extreme rather than just better than
    /// one.
    Dense,
}

/// Limits on what an FGLM computation may build, and which strategies to use.
///
/// Separate from [`F4Options`](crate::grobner::F4Options) rather than merged into it: the source
/// basis and the conversion are bounded by different quantities, and a caller that raises one
/// usually does not mean to raise the other.
///
/// Every limit is on the **representation** — monomials enumerated, entries stored. None of them
/// is a process-memory limit, and none accounts for allocator overhead.
///
/// # Source compatibility
/// Every field is public, so a downstream struct literal naming all of them stops compiling when
/// a field is added. Construct from [`FglmOptions::recommended`], [`FglmOptions::unbounded`], or
/// [`Default`] and assign the fields that matter, which is what this crate's own callers do and
/// what survives a new field.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FglmOptions {
    /// Standard monomials enumerated before the computation is abandoned.
    ///
    /// This is `D`, which controls everything else: the operators hold up to `N * D` columns and
    /// the conversion's dense blocks are `D^2 + D (D + 1)` field elements.
    pub max_quotient_dimension: usize,

    /// Multiplication-operator entries stored, summed over all `N` operators.
    ///
    /// Counts entries rather than bytes, the same accounting as
    /// [`F4Options::max_live_nonzeros`](crate::grobner::F4Options::max_live_nonzeros). A column
    /// for a product that is itself a standard monomial stores none, which is the common case.
    pub max_operator_entries: usize,

    /// Field-element cells the conversion's dense blocks may hold at full rank.
    ///
    /// `D^2 + D (D + 1)`: the span's two *triangular* blocks — a row leading at `pivot` stores
    /// `D - pivot` coordinates and a row at `r` stores `r + 1` combination coefficients — and the
    /// accepted quotient vectors the walk retains. Checked from `D` before anything
    /// is allocated rather than as it fills, because the space is a function of the dimension
    /// alone, and with checked arithmetic, because a budget computed from a wrapped product would
    /// be no budget at all.
    ///
    /// # This limit's meaning has changed twice
    /// In M17 it was `2 * D^2`, counting the span's two blocks as squares and omitting the accepted
    /// vectors altogether. Two things were wrong with that and they pull in opposite directions:
    /// the combination block is triangular rather than square, and there was a third block. So at
    /// `D = 16` it counted 512 cells where the conversion then allocated 648 — a budget cannot
    /// protect memory it does not know about. M18-4 made it count all three.
    ///
    /// The span's coordinate block then became triangular too, which took `D = 16` from 648 cells
    /// to 528. A budget that priced a block the conversion no longer allocates would be the same
    /// bug in the other direction. [`FglmMemory`](super::FglmMemory) reports each block
    /// separately, so a figure quoted against either older meaning can be recomputed.
    ///
    /// # It counts the quadratic blocks only
    /// The span also holds two `D`-cell working registers, and this does **not** price them: they
    /// are `O(D)` beside the blocks' `O(D^2)` — 2,048 cells against 2,098,176 at `D = 1,024` — and
    /// the per-call vectors they replaced were live during every reduction anyway, so admitting
    /// them would not have changed which conversions this limit refuses. A third change of meaning
    /// for a term that rounds to nothing against the limit's own quantity would cost more in
    /// comparability than it bought in accuracy. §8.7 of
    /// `docs/MILESTONE-FGLM-SCALABILITY.md` states the choice and its arithmetic.
    pub max_span_entries: usize,

    /// Bytes those dense blocks may occupy at full rank.
    ///
    /// The byte counterpart of [`max_span_entries`](Self::max_span_entries), standing to it exactly
    /// as [`max_operator_bytes`](Self::max_operator_bytes) stands to
    /// [`max_operator_entries`](Self::max_operator_entries) and as
    /// [`F4Options::max_live_bytes`](crate::grobner::F4Options::max_live_bytes) stands to that
    /// struct's entry budget. A cell is one `F`: **8 bytes over a 64-bit prime field and 32 over a
    /// 254-bit one**, so a cell budget alone admits 4x the memory over BN254. Both are enforced,
    /// and the bytes are checked against the same `D^2 + D (D + 1)` figure, from `D`, before
    /// anything is allocated.
    pub max_span_bytes: usize,

    /// Whether to fill in [`FglmStageTimings`](super::FglmStatistics).
    ///
    /// Off by default, and not merely out of caution: the operator loop runs `N * D` times and
    /// reads the clock several times per column, which on a system where most columns are unit
    /// vectors is a measurable fraction of what the loop does. The same trade-off, and the same
    /// [`StageClock`](crate::grobner::f4::StageClock), as
    /// [`F4Options::measure_stages`](crate::grobner::F4Options::measure_stages).
    ///
    /// The counters in [`FglmStatistics`](super::FglmStatistics) are collected either way. Only
    /// the durations depend on this.
    pub measure_stages: bool,

    /// How to compute the multiplication operators' columns.
    ///
    /// Does not change the answer. See [`OperatorConstruction`].
    pub operator_construction: OperatorConstruction,

    /// How to store the multiplication operators' columns.
    ///
    /// Does not change the answer. See [`OperatorStorage`].
    pub operator_storage: OperatorStorage,

    /// Bytes the operators' column heaps may occupy, summed over all `N` operators.
    ///
    /// **A second budget rather than a redefinition of
    /// [`max_operator_entries`](Self::max_operator_entries).** Entries are mathematical nonzeros
    /// and bytes are allocations, and under [`OperatorStorage::Dense`] the two diverge by a factor
    /// of `D / entries per column`. Changing what the older limit counted would have made every
    /// figure recorded against it ambiguous, so this is added beside it and both are enforced.
    ///
    /// Counts the column heaps and not the `N * D` column spine, which is a function of the
    /// dimension alone and is therefore already bounded by
    /// [`max_quotient_dimension`](Self::max_quotient_dimension).
    pub max_operator_bytes: usize,

    /// Batch size and limits for [`OperatorConstruction::BatchedBorder`].
    ///
    /// Ignored by every other strategy. See [`BorderBatch`].
    pub border_batch: BorderBatch,
}

/// Field-element cells [`FglmOptions::recommended`] lets the conversion's dense blocks hold.
///
/// Named because [`RECOMMENDED_MAX_QUOTIENT_DIMENSION`] is *derived* from it, and a change here
/// without a re-derivation there is the defect this constant exists to make impossible.
pub const RECOMMENDED_MAX_SPAN_ENTRIES: usize = 20_000_000;

/// [`FglmOptions::recommended`]'s quotient-dimension cap.
///
/// **Derived, not chosen.** The next power of two at or above
/// `largest_quotient_dimension_within(RECOMMENDED_MAX_SPAN_ENTRIES)` — 3,162 — which puts it
/// deliberately *above* the largest dimension the span budget can admit. So the dimension cap is
/// not the limit that bounds memory; [`FglmOptions::max_span_entries`] and
/// [`FglmOptions::max_span_bytes`] are, and this is the pre-enumeration tripwire for a walk so far
/// out of envelope that enumerating `N * D` operator columns is itself the waste.
///
/// # Why it is derived and not read off the corpus
/// It used to be justified as "26x the largest quotient dimension in the benchmark corpus, which
/// is cyclic-6's 156". That was true when written and false by #261, whose cross-library corpus
/// added rungs at 16,384 — **four times the cap**, not a fraction of it (#348). A default whose
/// stated reason is a corpus figure goes stale every time the corpus grows, and nothing checked
/// it. A default derived from the budget beside it goes stale only when that budget changes, which
/// `test_the_dimension_cap_is_derived_from_the_span_budget` fails on.
pub const RECOMMENDED_MAX_QUOTIENT_DIMENSION: usize = 4_096;

/// The largest quotient dimension whose dense blocks fit in `cells` field-element cells.
///
/// The inverse of the cell count [`FglmMemory::dense_blocks_for`](super::FglmMemory::dense_blocks_for)
/// computes from `D`: the span's two triangular blocks are `D (D + 1)` cells and the retained
/// quotient vectors are `D^2`, so this is the largest `D` with `D^2 + D (D + 1) <= cells`.
///
/// Field-independent, which is the half of the budget that is: the byte budget additionally
/// depends on `size_of::<F>()` and binds first over a wide field — 20 million cells is 160 MB over
/// a 64-bit prime field and 640 MB over BN254. So this is an upper bound on what any field admits,
/// which is the right side to derive a *cap* from.
///
/// Binary search with checked arithmetic rather than a closed form: `D^2` overflows for a `cells`
/// near `usize::MAX`, and a cap computed from a wrapped product would be no cap at all — the same
/// reasoning `max_span_entries` is already enforced under.
pub fn largest_quotient_dimension_within(cells: usize) -> usize {
    let fits = |dimension: usize| {
        dimension
            .checked_mul(dimension)
            .zip(dimension.checked_mul(dimension.saturating_add(1)))
            .and_then(|(accepted, span)| accepted.checked_add(span))
            .is_some_and(|total| total <= cells)
    };

    // `fits(0)` holds for every budget, and the answer is at most `cells + 1` because one cell per
    // unit of dimension is already an underestimate of `2 D^2 + D`.
    let (mut low, mut high) = (0usize, cells.saturating_add(1));
    while low < high {
        // The *upper* midpoint, so the loop makes progress when `high == low + 1`. Written as
        // `(high - low) / 2 + 1` rather than `(high - low + 1) / 2` because the latter overflows
        // at `cells == usize::MAX`, which is the one input a search for a memory cap must survive.
        let middle = low + (high - low) / 2 + 1;
        if fits(middle) {
            low = middle;
        } else {
            high = middle - 1;
        }
    }
    low
}

impl FglmOptions {
    /// Limits high enough not to interfere with a conversion that was going to finish, and low
    /// enough to fail before exhausting a workstation.
    ///
    /// `max_quotient_dimension` is [`RECOMMENDED_MAX_QUOTIENT_DIMENSION`], **derived** from the
    /// span budget rather than from the corpus: the next power of two at or above the 3,162 that
    /// `max_span_entries` admits. The enumeration itself is cheap at any such dimension, so this
    /// limit is there to stop a walk that should not have started; the entry budgets below are what
    /// bound memory, and they are the ones that bind first.
    ///
    /// **The corpus contains rungs outside this envelope, deliberately.** The planted MQ family's
    /// quotient dimension is `2^N`, so `mq-planted-14` is 16,384 and the conversion refuses it —
    /// correctly, as a limit stop rather than a failure, while the direct lex route solves it. The
    /// refusal is what the budget is for; see `test_the_corpus_reaches_past_the_recommended_cap`
    /// for the relationship written down where a test can break it.
    ///
    /// `max_operator_entries` of 20 million is about 320 MB at 16 bytes per entry, the same figure
    /// and the same accounting as F4's live-nonzero budget. `max_span_entries` is the same number,
    /// which `D^2 + D (D + 1)` reaches at `D = 3,162` — so on a sparse staircase the dense blocks
    /// are the first limit to bind, and on a dense one the operators are.
    ///
    /// `max_operator_bytes` of 320 MB is the same quantity of memory the entry budget describes,
    /// stated in the unit that is actually allocated. The two bind together under
    /// [`OperatorStorage::Sparse`] and the byte budget binds first under
    /// [`OperatorStorage::Dense`], which is the point of having it.
    ///
    /// `max_span_bytes` of 320 MB is the same figure again, and it is the field width rather than a
    /// strategy that decides which of it and `max_span_entries` binds: 20 million cells is 160 MB
    /// over a 64-bit prime field, so the cell budget binds there, and 640 MB over BN254, so the
    /// byte budget binds and caps `D` at 2,235 rather than 3,162.
    ///
    /// # The strategies, and where they were chosen
    /// [`OperatorConstruction::BatchedBorder`] at [`BorderBatch::recommended`]'s batch of 64, and
    /// [`OperatorStorage::Adaptive`]. Both come from M18-5's ablation — §9 of
    /// `docs/MILESTONE-FGLM-SCALABILITY.md` — which measured every combination on one source basis
    /// per system with the lex basis asserted equal throughout. That configuration is **at least
    /// as fast as M17's on every system in the corpus** (1.17x on planted-10, 14.0x on katsura-7)
    /// and never stores more (1.41x less on katsura-7, equal elsewhere). [`Self::baseline`] is the
    /// M17 configuration, kept so that figure stays reproducible.
    pub fn recommended() -> Self {
        Self {
            max_quotient_dimension: RECOMMENDED_MAX_QUOTIENT_DIMENSION,
            max_operator_entries: 20_000_000,
            max_span_entries: RECOMMENDED_MAX_SPAN_ENTRIES,
            max_span_bytes: 320_000_000,
            max_operator_bytes: 320_000_000,
            measure_stages: false,
            operator_construction: OperatorConstruction::BatchedBorder,
            operator_storage: OperatorStorage::Adaptive,
            border_batch: BorderBatch::recommended(),
        }
    }

    /// No limit worth reaching, for a caller that would rather be killed by the allocator.
    ///
    /// Exists for tests and for measurement, where a limit that fires is a failed measurement
    /// rather than a protected one. Not a sensible default, which is why it is not the default.
    ///
    /// Its **strategies are the reference ones**, not the recommended ones, so that a measurement
    /// which lifts the limits does not silently also change the strategy. A caller who wants the
    /// recommended strategies without the budgets writes
    /// `FglmOptions::unbounded().with_operator_construction(..).with_operator_storage(..)`.
    pub fn unbounded() -> Self {
        Self {
            max_quotient_dimension: usize::MAX,
            max_operator_entries: usize::MAX,
            max_span_entries: usize::MAX,
            max_span_bytes: usize::MAX,
            max_operator_bytes: usize::MAX,
            measure_stages: false,
            operator_construction: OperatorConstruction::PerColumn,
            operator_storage: OperatorStorage::Sparse,
            border_batch: BorderBatch::unbounded(),
        }
    }

    /// The M17 configuration, named so that a comparison against it is reproducible.
    ///
    /// Analogous to [`F4Options::baseline`](crate::grobner::F4Options::baseline). Every M18
    /// measurement is quoted against this, and it must keep meaning "what M17 did" even after the
    /// default stops being the same thing — which is why it names every strategy explicitly rather
    /// than deriving from [`Self::recommended`].
    /// The literals are M17's own, **not** [`RECOMMENDED_MAX_QUOTIENT_DIMENSION`], even where the
    /// two currently coincide: this configuration has to keep meaning "what M17 did" after the
    /// recommended cap is re-derived, which is the same reason its strategies are named rather
    /// than inherited.
    pub fn baseline() -> Self {
        Self {
            max_quotient_dimension: 4_096,
            max_operator_entries: 20_000_000,
            max_span_entries: 20_000_000,
            max_span_bytes: 320_000_000,
            max_operator_bytes: 320_000_000,
            measure_stages: false,
            operator_construction: OperatorConstruction::PerColumn,
            operator_storage: OperatorStorage::Sparse,
            border_batch: BorderBatch::recommended(),
        }
    }

    /// These options with a different operator-construction strategy.
    ///
    /// For ablations, where the point is that nothing else differs.
    pub fn with_operator_construction(self, operator_construction: OperatorConstruction) -> Self {
        Self {
            operator_construction,
            ..self
        }
    }

    /// These options with a different operator-storage strategy.
    pub fn with_operator_storage(self, operator_storage: OperatorStorage) -> Self {
        Self {
            operator_storage,
            ..self
        }
    }

    /// These options with different border-batch limits.
    pub fn with_border_batch(self, border_batch: BorderBatch) -> Self {
        Self {
            border_batch,
            ..self
        }
    }
}

impl Default for FglmOptions {
    /// [`FglmOptions::recommended`].
    fn default() -> Self {
        Self::recommended()
    }
}

#[cfg(test)]
mod tests {
    use super::{
        largest_quotient_dimension_within, FglmOptions, OperatorConstruction, OperatorStorage,
        RECOMMENDED_MAX_QUOTIENT_DIMENSION, RECOMMENDED_MAX_SPAN_ENTRIES,
    };
    use crate::{
        fields::Zp2147483647,
        grobner::{fglm::BorderBatchSize, FglmMemory},
    };

    /// The default is the recommended configuration, not a third thing to keep in step.
    #[test]
    fn test_the_default_is_the_recommended_configuration() {
        assert_eq!(FglmOptions::default(), FglmOptions::recommended());
    }

    /// The recommended strategies are the ones M18-5's ablation chose, including the batch size.
    #[test]
    fn test_the_recommended_options_name_the_strategies_the_ablation_chose() {
        let recommended = FglmOptions::recommended();
        assert_eq!(
            recommended.operator_construction,
            OperatorConstruction::BatchedBorder
        );
        assert_eq!(recommended.operator_storage, OperatorStorage::Adaptive);
        assert_eq!(recommended.border_batch.size, BorderBatchSize::Fixed(64));
    }

    /// The baseline still names M17's strategies, so a figure quoted against it keeps its meaning.
    #[test]
    fn test_the_baseline_names_the_m17_strategies() {
        let baseline = FglmOptions::baseline();
        assert_eq!(
            baseline.operator_construction,
            OperatorConstruction::PerColumn
        );
        assert_eq!(baseline.operator_storage, OperatorStorage::Sparse);
        assert!(!baseline.measure_stages);
        assert_eq!(baseline.max_quotient_dimension, 4_096);
        assert_eq!(baseline.max_operator_entries, 20_000_000);
        assert_eq!(baseline.max_span_entries, 20_000_000);
        assert_eq!(baseline.max_operator_bytes, 320_000_000);
        assert_ne!(baseline, FglmOptions::recommended());
    }

    /// Every limit the recommended configuration sets is also the limit the baseline sets.
    ///
    /// The ablation varied the strategies and nothing else, so the two configurations must differ
    /// in the strategies and nothing else — otherwise a speedup measured against the baseline
    /// could be a budget that fired rather than a strategy that worked.
    #[test]
    fn test_the_baseline_and_the_recommended_options_differ_only_in_their_strategies() {
        let baseline = FglmOptions::baseline();
        let recommended = FglmOptions::recommended();

        assert_eq!(
            baseline.max_quotient_dimension,
            recommended.max_quotient_dimension
        );
        assert_eq!(
            baseline.max_operator_entries,
            recommended.max_operator_entries
        );
        assert_eq!(baseline.max_span_entries, recommended.max_span_entries);
        assert_eq!(baseline.max_operator_bytes, recommended.max_operator_bytes);
        assert_eq!(baseline.border_batch, recommended.border_batch);
        assert_eq!(baseline.measure_stages, recommended.measure_stages);
    }

    /// FGLM carries the same budget pairs as F4, at the same two numbers.
    ///
    /// Half of the check #322's scope note asks for: the configuration that could have the same
    /// trap. The other half — that these do **not** interact, because each is checked against its
    /// own requirement in its own unit with no `min` between them — is
    /// `conversion::tests::test_lifting_one_span_budget_leaves_the_other_binding_in_its_own_unit`.
    #[test]
    fn test_the_span_and_operator_budgets_carry_f4s_two_numbers() {
        let options = FglmOptions::baseline();
        assert_eq!(options.max_span_entries, 20_000_000);
        assert_eq!(options.max_span_bytes, 320_000_000);
        assert_eq!(options.max_operator_entries, 20_000_000);
        assert_eq!(options.max_operator_bytes, 320_000_000);
    }

    // === #348: the cap's derivation, and the corpus it is no longer a claim about ===

    /// `largest_quotient_dimension_within` really is the inverse of the dense-block cell count.
    #[test]
    fn test_the_largest_admissible_dimension_is_the_cell_counts_inverse() {
        type F = Zp2147483647;
        for cells in [0, 1, 2, 6, 7, 100, 20_000, RECOMMENDED_MAX_SPAN_ENTRIES] {
            let dimension = largest_quotient_dimension_within(cells);
            let total = |d: usize| {
                FglmMemory::dense_blocks_for::<F>(d)
                    .map(|(span, accepted, _bytes)| span + accepted)
                    .expect("representable at these sizes")
            };
            assert!(
                total(dimension) <= cells,
                "{dimension} does not fit {cells} cells"
            );
            assert!(
                total(dimension + 1) > cells,
                "{} also fits {cells} cells, so {dimension} is not the largest",
                dimension + 1
            );
        }
    }

    /// A budget near `usize::MAX` is answered without a wrapped product.
    ///
    /// The cap is enforced with checked arithmetic for exactly this reason, and the inverse has to
    /// hold to the same standard: a dimension derived from a wrapped `D^2` would be no cap at all.
    #[test]
    fn test_an_enormous_cell_budget_does_not_wrap() {
        let dimension = largest_quotient_dimension_within(usize::MAX);
        assert!(dimension > 0);
        assert!(
            dimension.checked_mul(dimension).is_some(),
            "{dimension} squared overflows, so it was not actually admissible"
        );
    }

    /// The recommended cap is derived from the span budget beside it, not from the corpus.
    ///
    /// **This is the test that keeps the number from going stale.** The old justification was a
    /// corpus figure and nothing checked it, so #261's expansion falsified it silently. Change
    /// `RECOMMENDED_MAX_SPAN_ENTRIES` and this fails until the cap is re-derived.
    #[test]
    fn test_the_dimension_cap_is_derived_from_the_span_budget() {
        let admissible = largest_quotient_dimension_within(RECOMMENDED_MAX_SPAN_ENTRIES);
        assert_eq!(admissible, 3_162, "the span budget's own dimension limit");

        assert!(
            RECOMMENDED_MAX_QUOTIENT_DIMENSION.is_power_of_two(),
            "the cap is the next power of two above {admissible}"
        );
        assert!(
            RECOMMENDED_MAX_QUOTIENT_DIMENSION >= admissible,
            "a cap below {admissible} would make the dimension limit bind before the memory one"
        );
        assert!(
            RECOMMENDED_MAX_QUOTIENT_DIMENSION / 2 < admissible,
            "{RECOMMENDED_MAX_QUOTIENT_DIMENSION} is not the *next* power of two above {admissible}"
        );
        assert_eq!(
            FglmOptions::recommended().max_quotient_dimension,
            RECOMMENDED_MAX_QUOTIENT_DIMENSION
        );
    }

    /// The span budget binds before the dimension cap does, which is what "not the memory limit"
    /// means.
    ///
    /// Stated as a property of the two numbers rather than as a comment, because the previous
    /// justification's failure was precisely a comment nothing checked.
    #[test]
    fn test_the_span_budget_binds_before_the_dimension_cap() {
        type F = Zp2147483647;
        let options = FglmOptions::recommended();
        for dimension in [3_163, 3_500, 4_096] {
            let (span, accepted, bytes) =
                FglmMemory::dense_blocks_for::<F>(dimension).expect("representable");
            assert!(
                dimension <= options.max_quotient_dimension,
                "{dimension} is past the dimension cap, so it proves nothing"
            );
            assert!(
                span + accepted > options.max_span_entries || bytes > options.max_span_bytes,
                "{dimension} is admitted by every budget, so the dimension cap is the binding one"
            );
        }
    }

    /// The planted MQ family's quotient dimension is `2^N`, and the corpus reaches N = 14.
    ///
    /// Pinned at N = 6 against a run: `conversion.rs`'s own tests convert `planted::<6>` and
    /// assert `quotient_dimension == 64`. §10.3 of `docs/MILESTONE-FGLM-SOLVING.md` records the
    /// identity across the family — 64, 1024, 4096, 16384 at N = 6, 10, 12, 14 — which is also the
    /// solution count, since those ideals are radical with every zero rational.
    const PLANTED_QUOTIENT_DIMENSIONS: &[(&str, usize)] = &[
        ("mq-planted-6", 64),
        ("mq-planted-10", 1_024),
        ("mq-planted-14", 16_384),
    ];

    /// The corpus holds rungs past the recommended cap, and these are they.
    ///
    /// The relationship #348 wants written down where a test can break it. The corpus **already**
    /// exceeds the cap and that is correct: `mq-planted-14`'s conversion is a limit stop while the
    /// direct lex route solves the same instance, so the budget is doing its job. What must not
    /// recur is the relationship being asserted nowhere — adding a planted rung, or lowering the
    /// cap, fails this.
    #[test]
    fn test_the_corpus_reaches_past_the_recommended_cap() {
        let cap = FglmOptions::recommended().max_quotient_dimension;
        let largest = PLANTED_QUOTIENT_DIMENSIONS
            .iter()
            .map(|(_name, dimension)| *dimension)
            .max()
            .expect("a nonempty table");

        assert!(
            largest > cap,
            "the table's largest dimension {largest} is within the cap {cap}; if the corpus really \
             shrank, this test and the cap's doc comment both need rewriting"
        );
        assert_eq!(largest, 16_384, "#261's cross-library rung");

        // Which rungs are inside and which are outside, so the split is data rather than prose.
        let (within, beyond): (Vec<_>, Vec<_>) = PLANTED_QUOTIENT_DIMENSIONS
            .iter()
            .partition(|(_name, dimension)| *dimension <= cap);
        assert_eq!(
            within.iter().map(|(name, _)| *name).collect::<Vec<_>>(),
            vec!["mq-planted-6", "mq-planted-10"]
        );
        assert_eq!(
            beyond.iter().map(|(name, _)| *name).collect::<Vec<_>>(),
            vec!["mq-planted-14"]
        );
    }

    /// Every planted rung on the ladder has a declared quotient dimension, and the figures agree.
    ///
    /// The anti-staleness half, and the #333 lesson applied: a statement about the corpus that
    /// lives outside the corpus has to be pinned to it, or the next expansion falsifies it in
    /// silence. Adding `mq-planted-18` fails here until its dimension is declared and the cap
    /// relationship above is reconsidered.
    ///
    /// The **figures** are pinned too, not only the names. `CorpusEntry::quotient_dimension` now
    /// carries the same numbers, and a second copy that nothing compares is the duplication #333
    /// is about: a corpus figure corrected here and not there would leave the cap argument above
    /// reasoning from the stale one.
    #[test]
    #[cfg(feature = "external-runners")]
    fn test_every_planted_rung_has_a_declared_quotient_dimension() {
        let declared: Vec<&str> = PLANTED_QUOTIENT_DIMENSIONS
            .iter()
            .map(|(name, _)| *name)
            .collect();
        let ladder = crate::grobner::external::corpus::ladder();
        let planted: Vec<&crate::grobner::external::corpus::CorpusEntry> = ladder
            .iter()
            .filter(|entry| entry.family == "mq-planted")
            .collect();
        let on_the_ladder: Vec<String> =
            planted.iter().map(|entry| entry.name.to_string()).collect();

        assert_eq!(
            on_the_ladder, declared,
            "the ladder's planted rungs and the declared dimensions have diverged"
        );
        for (entry, (name, dimension)) in planted.iter().zip(PLANTED_QUOTIENT_DIMENSIONS) {
            assert_eq!(
                entry.quotient_dimension,
                Some(*dimension as u64),
                "{name}: the corpus and the figure this cap argument reads have diverged"
            );
        }
    }

    /// Zero-dimensional rungs whose quotient dimension is **not** recorded, and the reason.
    ///
    /// Exactly one, and it is not an oversight: `mq-random-14`'s *basis* does not finish in this
    /// tree, so there is no conversion to read a dimension off. Zeebra stops at 20 006 072 live
    /// nonzero entries after 34.4 s and Singular hits its 60 s wall
    /// (`research/competitive/COMPETITIVE.md`), on the basis alone and before any order
    /// conversion. Unlike the other rungs #473 named, all of which now carry a figure, this one
    /// cannot be closed by recording something somebody already knows.
    ///
    /// **Named individually rather than exempted by family**, which is the whole point: a rung
    /// added without a dimension fails the test below instead of joining a silent exemption.
    #[cfg(feature = "external-runners")]
    const UNDECLARED_ZERO_DIMENSIONAL: &[&str] = &["mq-random-14"];

    /// Every zero-dimensional rung on the **whole** ladder declares a quotient dimension.
    ///
    /// #473: the planted test above covers three of the ladder's rungs because the planted
    /// family's dimension is an identity in `N`. The envelope assertion it exists for is about the
    /// corpus and not about one family, so a rung of another family added with no dimension used
    /// to trip nothing. Every such rung now carries one, so the assertion widens to all of them
    /// with [`UNDECLARED_ZERO_DIMENSIONAL`] as the one named exception.
    ///
    /// The converse is asserted in the same pass, because it is the error that would make the
    /// first half vacuous: a **positive-dimensional** ideal has no finite quotient dimension, so a
    /// figure on one of those rungs is a figure about something else. `cyclic-4`, `cyclic-8` and
    /// `cyclic-9` are the rungs this holds for.
    #[test]
    #[cfg(feature = "external-runners")]
    fn test_every_zero_dimensional_rung_declares_a_quotient_dimension() {
        let mut undeclared: Vec<&str> = Vec::new();
        let mut positive_dimensional = 0usize;
        for entry in crate::grobner::external::corpus::ladder() {
            match (entry.zero_dimensional, entry.quotient_dimension) {
                (true, Some(dimension)) => assert!(
                    dimension > 0,
                    "{}: a zero-dimensional ideal has a nonzero quotient dimension",
                    entry.name
                ),
                (true, None) => undeclared.push(entry.name),
                (false, None) => positive_dimensional += 1,
                (false, Some(dimension)) => panic!(
                    "{}: positive-dimensional, so it has no finite quotient dimension, yet it \
                     declares {}",
                    entry.name, dimension
                ),
            }
        }
        assert_eq!(
            undeclared, UNDECLARED_ZERO_DIMENSIONAL,
            "a zero-dimensional rung with no declared quotient dimension is outside the envelope \
             assertion; record its dimension, or name it and say why it cannot be recorded"
        );
        assert_eq!(
            positive_dimensional, 3,
            "cyclic-4, cyclic-8 and cyclic-9; a change here means the ladder's shape moved"
        );
    }
}
