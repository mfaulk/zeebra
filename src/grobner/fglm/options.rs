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
    /// the conversion's dense blocks are `2 D^2 + D (D + 1) / 2` field elements.
    pub max_quotient_dimension: usize,

    /// Multiplication-operator entries stored, summed over all `N` operators.
    ///
    /// Counts entries rather than bytes, the same accounting as
    /// [`F4Options::max_live_nonzeros`](crate::grobner::F4Options::max_live_nonzeros). A column
    /// for a product that is itself a standard monomial stores none, which is the common case.
    pub max_operator_entries: usize,

    /// Field-element cells the conversion's dense blocks may hold at full rank.
    ///
    /// `2 D^2 + D (D + 1) / 2`: the span's `D` coordinates per row, its *triangular* combination
    /// block, and the accepted quotient vectors the walk retains. Checked from `D` before anything
    /// is allocated rather than as it fills, because the space is a function of the dimension
    /// alone, and with checked arithmetic, because a budget computed from a wrapped product would
    /// be no budget at all.
    ///
    /// # This limit's meaning changed in M18-4
    /// It was `2 * D^2`, counting the span's two blocks as squares and omitting the accepted
    /// vectors altogether. Two things were wrong with that and they pull in opposite directions:
    /// the combination block is triangular rather than square, and there was a third block. So at
    /// `D = 16` it counted 512 cells where the conversion allocates 648 — a budget cannot protect
    /// memory it does not know about. [`FglmMemory`](super::FglmMemory) reports each block
    /// separately, so a figure quoted against the old meaning can be recomputed.
    pub max_span_entries: usize,

    /// Bytes those dense blocks may occupy at full rank.
    ///
    /// The byte counterpart of [`max_span_entries`](Self::max_span_entries), standing to it exactly
    /// as [`max_operator_bytes`](Self::max_operator_bytes) stands to
    /// [`max_operator_entries`](Self::max_operator_entries) and as
    /// [`F4Options::max_live_bytes`](crate::grobner::F4Options::max_live_bytes) stands to that
    /// struct's entry budget. A cell is one `F`: **8 bytes over a 64-bit prime field and 32 over a
    /// 254-bit one**, so a cell budget alone admits 4x the memory over BN254. Both are enforced,
    /// and the bytes are checked against the same `2 D^2 + D (D + 1) / 2` figure, from `D`, before
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

impl FglmOptions {
    /// Limits high enough not to interfere with a conversion that was going to finish, and low
    /// enough to fail before exhausting a workstation.
    ///
    /// `max_quotient_dimension` of 4,096 is 26x the largest quotient dimension in the benchmark
    /// corpus, which is cyclic-6's 156. The enumeration itself is cheap at any such dimension, so
    /// this limit is there to stop a walk that should not have started; the entry budgets below
    /// are what bound memory.
    ///
    /// `max_operator_entries` of 20 million is about 320 MB at 16 bytes per entry, the same figure
    /// and the same accounting as F4's live-nonzero budget. `max_span_entries` is the same number,
    /// which `2 D^2 + D (D + 1) / 2` reaches at `D` just over 2,828 — so on a sparse staircase the
    /// dense blocks are the first limit to bind, and on a dense one the operators are.
    ///
    /// `max_operator_bytes` of 320 MB is the same quantity of memory the entry budget describes,
    /// stated in the unit that is actually allocated. The two bind together under
    /// [`OperatorStorage::Sparse`] and the byte budget binds first under
    /// [`OperatorStorage::Dense`], which is the point of having it.
    ///
    /// `max_span_bytes` of 320 MB is the same figure again, and it is the field width rather than a
    /// strategy that decides which of it and `max_span_entries` binds: 20 million cells is 160 MB
    /// over a 64-bit prime field, so the cell budget binds there, and 640 MB over BN254, so the
    /// byte budget binds and caps `D` near 2,000 rather than 2,828.
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
            max_quotient_dimension: 4_096,
            max_operator_entries: 20_000_000,
            max_span_entries: 20_000_000,
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
    use super::{FglmOptions, OperatorConstruction, OperatorStorage};
    use crate::grobner::fglm::BorderBatchSize;

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
}
