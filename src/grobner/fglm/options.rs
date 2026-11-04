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
    #[default]
    PerColumn,

    /// One normal form per *distinct* border monomial, reused by every column that reaches it.
    ///
    /// Strictly fewer reductions than [`Self::PerColumn`] — between a fifth and a third fewer on
    /// the benchmark corpus — at the cost of holding `|∂B|` coordinate vectors at once. That is
    /// not free and is measured rather than waved away: see §4 of
    /// `docs/MILESTONE-FGLM-SCALABILITY.md`.
    DeduplicatedBorder,
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
    /// the dependence test of M17-C is `2 * D^2` field elements.
    pub max_quotient_dimension: usize,

    /// Multiplication-operator entries stored, summed over all `N` operators.
    ///
    /// Counts entries rather than bytes, the same accounting as
    /// [`F4Options::max_live_nonzeros`](crate::grobner::F4Options::max_live_nonzeros). A column
    /// for a product that is itself a standard monomial stores none, which is the common case.
    pub max_operator_entries: usize,

    /// Entries the dependence test's two blocks may hold, `2 * D^2` at full rank.
    ///
    /// Checked from `D` before the span is allocated rather than as it fills, because the space is
    /// a function of the dimension alone.
    pub max_span_entries: usize,

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
    /// which `2 * D^2` reaches at `D` just over 3,160 — so on a sparse staircase the span is the
    /// first of the three limits to bind, and on a dense one the operators are.
    pub fn recommended() -> Self {
        Self {
            max_quotient_dimension: 4_096,
            max_operator_entries: 20_000_000,
            max_span_entries: 20_000_000,
            measure_stages: false,
            operator_construction: OperatorConstruction::PerColumn,
        }
    }

    /// No limit worth reaching, for a caller that would rather be killed by the allocator.
    ///
    /// Exists for tests and for measurement, where a limit that fires is a failed measurement
    /// rather than a protected one. Not a sensible default, which is why it is not the default.
    pub fn unbounded() -> Self {
        Self {
            max_quotient_dimension: usize::MAX,
            max_operator_entries: usize::MAX,
            max_span_entries: usize::MAX,
            measure_stages: false,
            operator_construction: OperatorConstruction::PerColumn,
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
            measure_stages: false,
            operator_construction: OperatorConstruction::PerColumn,
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
}

impl Default for FglmOptions {
    /// [`FglmOptions::recommended`].
    fn default() -> Self {
        Self::recommended()
    }
}
