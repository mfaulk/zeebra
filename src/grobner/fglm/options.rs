/// Limits on what an FGLM computation may build.
///
/// Separate from [`F4Options`](crate::grobner::F4Options) rather than merged into it: the source
/// basis and the conversion are bounded by different quantities, and a caller that raises one
/// usually does not mean to raise the other.
///
/// Every limit is on the **representation** — monomials enumerated, entries stored. None of them
/// is a process-memory limit, and none accounts for allocator overhead.
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
}

impl FglmOptions {
    /// Limits high enough not to interfere with a conversion that was going to finish, and low
    /// enough to fail before exhausting a workstation.
    ///
    /// `max_quotient_dimension` of 4,096 is 26x the largest quotient dimension in the benchmark
    /// corpus — cyclic-6's 156 — and the point at which the operators reach about 215 MB at a
    /// tenth fill with eight variables, or 1.07 GB if every column were stored densely.
    ///
    /// `max_operator_entries` of 20 million is about 320 MB at 16 bytes per entry, the same figure
    /// and the same accounting as F4's live-nonzero budget.
    pub fn recommended() -> Self {
        Self {
            max_quotient_dimension: 4_096,
            max_operator_entries: 20_000_000,
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
        }
    }
}

impl Default for FglmOptions {
    /// [`FglmOptions::recommended`].
    fn default() -> Self {
        Self::recommended()
    }
}
