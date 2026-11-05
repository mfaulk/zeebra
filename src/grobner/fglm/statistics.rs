//! Counters and timings describing the work an FGLM conversion performed.
//!
//! The M17 statistics attributed the cost between the frontier, the operators, and the dependence
//! test. That was enough to find the bottleneck — operator construction is 95% of katsura-7's
//! conversion — and not enough to say what inside it to attack. These add the structure of the
//! border, which is where the duplicated work lives, and a stage breakdown that separates monomial
//! lookup from reduction from coordinate-vector assembly.

use std::{mem::size_of, time::Duration};

use crate::{
    grobner::fglm::{BorderBatchStatistics, IncrementalSpan},
    FiniteField,
};

/// The shape of the border, and how much of the reduction work it duplicates.
///
/// `x_i b_j` is either standard, costing nothing, or on the border `∂B` and needing a normal form.
/// The same border monomial can arise from several `(i, j)` pairs — `x*y` from both `x * y` and
/// `y * x` — and M17 reduces it once per pair. The gap between
/// [`border_columns`](Self::border_columns) and
/// [`distinct_border_monomials`](Self::distinct_border_monomials) is the duplication that gap
/// represents.
///
/// **Evidence for an optimization, not proof of one.** A high duplication rate bounds what
/// deduplication can save; it does not say that reducing a border monomial is where the time
/// goes. [`FglmStageTimings`] is for that.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct BorderStatistics {
    /// `N * D`, the columns across all operators — one per variable per standard monomial.
    pub operator_columns: usize,

    /// Columns whose product `x_i b_j` is itself standard, so the column is a unit vector.
    pub standard_columns: usize,

    /// Columns whose product left the staircase and needed a normal form.
    ///
    /// `standard_columns + border_columns == operator_columns`.
    pub border_columns: usize,

    /// `|∂B|`, the distinct monomials among those products.
    ///
    /// Not the same as [`border_columns`](Self::border_columns), and the whole point of measuring
    /// both.
    pub distinct_border_monomials: usize,

    /// Normal forms actually computed.
    ///
    /// Equals [`border_columns`](Self::border_columns) on the M17 path and
    /// [`distinct_border_monomials`](Self::distinct_border_monomials) on a deduplicated one, which
    /// is how a caller tells which path ran.
    pub normal_form_calls: usize,
}

impl BorderStatistics {
    /// Border columns beyond the first for their monomial: the reductions deduplication removes.
    pub fn repeated_border_columns(&self) -> usize {
        self.border_columns
            .saturating_sub(self.distinct_border_monomials)
    }

    /// Repeated border columns as a fraction of all border columns, or `None` if there are none.
    pub fn duplication_rate(&self) -> Option<f64> {
        if self.border_columns == 0 {
            return None;
        }
        Some(self.repeated_border_columns() as f64 / self.border_columns as f64)
    }
}

/// Where a conversion's time went.
///
/// Zero throughout unless [`FglmOptions::measure_stages`](super::FglmOptions::measure_stages) is
/// set, on the same reasoning as F4's [`StageTimings`](crate::grobner::f4::StageTimings): the
/// operator loop runs `N * D` times and a clock read inside it is not free.
///
/// The stages partition the conversion and do not overlap, so [`Self::sum`] is comparable against
/// the wall clock the caller measured.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct FglmStageTimings {
    /// Enumerating the standard monomials, i.e. [`QuotientBasis`](super::QuotientBasis).
    pub quotient_basis: Duration,

    /// Classifying each product `x_i b_j` as standard or on the border: the monomial multiply and
    /// the basis lookup, and nothing else.
    pub border_classification: Duration,

    /// Reducing border monomials to normal form, one at a time.
    ///
    /// Zero under [`OperatorConstruction::BatchedBorder`](super::OperatorConstruction), which
    /// charges to [`Self::border_symbolic`] instead — except for a batch that fell back to the
    /// scalar path, whose reductions land here.
    pub normal_forms: Duration,

    /// Building a batch's symbolic closure and reducing its targets against it.
    ///
    /// Zero under the scalar strategies. One figure rather than two because the closure and the
    /// reduction are one call: splitting them would mean a clock read between every batch's two
    /// halves, and the batch count is small enough that a split would be mostly measurement.
    pub border_symbolic: Duration,

    /// Turning a normal form into a sorted coordinate vector.
    ///
    /// Separate from the reduction because it is a different kind of cost — hashing and sorting
    /// rather than field arithmetic — and the two are addressed by different changes.
    pub column_assembly: Duration,

    /// The lex walk: the frontier, the operator applications, and the dependence test.
    pub dependence: Duration,
}

impl FglmStageTimings {
    /// Every stage added together.
    pub fn sum(&self) -> Duration {
        self.quotient_basis
            + self.border_classification
            + self.normal_forms
            + self.border_symbolic
            + self.column_assembly
            + self.dependence
    }

    /// The three stages that build the multiplication operators.
    ///
    /// The quantity M17 measured at 36.2 ms of katsura-7's 38.1 ms conversion, now broken down.
    pub fn operator_construction(&self) -> Duration {
        self.border_classification + self.normal_forms + self.border_symbolic + self.column_assembly
    }
}

/// What the conversion's representations hold, counted three ways.
///
/// The three are different numbers and the milestone depends on not confusing them:
///
/// * **Entries** are mathematical nonzeros — a term of a normal form.
/// * **Cells** are field-element slots a representation allocates, nonzero or not. A dense column
///   of a mostly-zero operator costs `D` cells and few entries.
/// * **Bytes** are what the allocation actually takes, including each entry's index and each
///   `Vec`'s spare capacity.
///
/// All three are budgeted: [`max_operator_entries`](super::FglmOptions::max_operator_entries) on
/// the entries, [`max_span_entries`](super::FglmOptions::max_span_entries) on the dense blocks'
/// cells, and [`max_operator_bytes`](super::FglmOptions::max_operator_bytes) on the bytes. The
/// byte budget is beside the entry one rather than a redefinition of it, because under
/// [`OperatorStorage::Dense`](super::OperatorStorage) the two diverge.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct FglmMemory {
    /// Nonzero entries the `N` operators hold between them.
    ///
    /// What [`max_operator_entries`](super::FglmOptions::max_operator_entries) is enforced on.
    pub operator_entries: usize,

    /// Field-element cells the operators' columns allocate, zero or not.
    ///
    /// Equals [`Self::operator_entries`] while every reduced column is sparse, and exceeds it
    /// wherever one is dense: a dense column allocates `D` cells for however many nonzeros it has.
    /// The gap is what [`OperatorStorage`](super::OperatorStorage) trades away in exchange for not
    /// storing an index per entry.
    pub operator_cells: usize,

    /// Bytes the operators' representations occupy, as the representations themselves report.
    ///
    /// What [`max_operator_bytes`](super::FglmOptions::max_operator_bytes) is enforced on, plus the
    /// `N * D` column spine, which that budget does not count because it is a function of the
    /// dimension alone.
    pub operator_bytes: usize,

    /// Of the `N * D` columns, how many are held densely.
    pub dense_columns: usize,

    /// Field-element cells the dependence test's echelon rows hold.
    ///
    /// `D (D + 1)` at full rank: `D - pivot` coordinates for a row leading at `pivot`, and a
    /// combination of `r + 1` coefficients for the row at `r`. Both blocks are triangular, and
    /// both paddings M17 held were zeros. See [`IncrementalSpan`](super::IncrementalSpan).
    pub span_cells: usize,

    /// Field-element cells the retained accepted quotient vectors hold: `D^2` at full rank.
    ///
    /// The conversion keeps every accepted vector so that a candidate's class costs one operator
    /// application instead of a reduction. It is a third dense block beyond the span's two, and
    /// M17's accounting omitted it entirely.
    pub accepted_vector_cells: usize,

    /// Bytes of the dense blocks above, at `size_of::<F>()` a cell.
    pub dense_block_bytes: usize,
}

impl FglmMemory {
    /// Every byte figure above added together.
    ///
    /// **An estimate of what this crate stores, not a measurement of the process.** It ignores
    /// allocator overhead, the source basis, every temporary, and F4's own peak while computing
    /// the input. [`peak_resident_bytes`](crate::util::peak_resident_bytes) measures the process;
    /// the two are reported side by side and are not interchangeable.
    pub fn estimated_bytes(&self) -> usize {
        self.operator_bytes + self.dense_block_bytes
    }

    /// The dense cells a conversion of this dimension needs at full rank, and their bytes.
    ///
    /// Returns `(span cells, accepted-vector cells, bytes of both)`. The span's figure is
    /// [`IncrementalSpan::cells_at_full_rank`](super::IncrementalSpan::cells_at_full_rank) —
    /// `D (D + 1)`, two triangular blocks — and the accepted vectors are `D^2`.
    ///
    /// `None` on arithmetic overflow, which `D` near `usize::MAX` would reach: a budget computed
    /// from a wrapped product would be no budget at all.
    ///
    /// # What this does not count
    /// The `O(D^2)` blocks, and nothing else. The span additionally holds two working registers of
    /// `D` cells each — see [`IncrementalSpan`](super::IncrementalSpan) — which are `O(D)`, 0.1% of
    /// the blocks at `D = 1,024`, and were live during every reduction before the span began
    /// keeping them, so they raise neither this figure meaningfully nor the peak at all. Also
    /// uncounted, and larger: the candidate vectors the walk allocates one at a time, the relation
    /// polynomials it emits, and everything F4 held while producing the input.
    pub fn dense_blocks_for<F: FiniteField>(dimension: usize) -> Option<(usize, usize, usize)> {
        let span_cells = IncrementalSpan::<F>::cells_at_full_rank(dimension)?;
        let accepted_cells = dimension.checked_mul(dimension)?;
        let bytes = span_cells
            .checked_add(accepted_cells)?
            .checked_mul(size_of::<F>())?;
        Some((span_cells, accepted_cells, bytes))
    }
}

/// What an FGLM conversion did.
///
/// The quotient dimension is the figure to quote: FGLM's cost is `O(N * D^3)` with dense linear
/// algebra, so `D` explains a timing where the variable count does not. The rest attributes that
/// cost between the frontier, the operators, and the dependence test.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct FglmStatistics {
    /// `D = dim_F(R/I)`, and therefore also the number of target standard monomials.
    pub quotient_dimension: usize,

    /// Elements of the source basis.
    pub source_basis_elements: usize,

    /// Elements of the target basis, i.e. relations emitted.
    pub target_basis_elements: usize,

    /// Entries the `N` multiplication operators hold between them.
    ///
    /// The same figure as [`FglmMemory::operator_entries`], kept at the top level because it is
    /// what the operator budget is enforced on.
    pub operator_entries: usize,

    /// Candidate monomials taken off the frontier.
    pub candidates_considered: usize,

    /// Candidates discarded because an already-emitted leading monomial divided them.
    ///
    /// Pruning is what keeps the frontier finite; a conversion where this is zero either found no
    /// relations or has a bug.
    pub candidates_pruned: usize,

    /// Candidates whose quotient vector extended the span. Equals `quotient_dimension` on success.
    pub candidates_independent: usize,

    /// Candidates whose quotient vector was dependent, each producing one relation.
    pub candidates_dependent: usize,

    /// Row subtractions performed by the dependence test. Each touches `2 * D` entries.
    pub span_row_operations: usize,

    /// The shape of the border the operators were built over.
    pub border: BorderStatistics,

    /// Where the time went, if the conversion was asked to measure.
    pub timings: FglmStageTimings,

    /// What the representations hold.
    pub memory: FglmMemory,

    /// What the batched border reduction did, or zeros under the scalar strategies.
    pub batches: BorderBatchStatistics,
}

impl FglmStatistics {
    /// Bytes the conversion's representations needed.
    ///
    /// Delegates to [`FglmMemory::estimated_bytes`]; see there for what it does and does not count.
    pub fn estimated_bytes(&self) -> usize {
        self.memory.estimated_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::{BorderStatistics, FglmMemory, FglmStageTimings, FglmStatistics};
    use crate::fields::Zp2147483647;
    use std::{mem::size_of, time::Duration};

    type F = Zp2147483647;

    /// Repeated border columns are the border columns beyond one per distinct monomial.
    #[test]
    fn test_repeated_border_columns_is_the_excess_over_distinct() {
        let border = BorderStatistics {
            operator_columns: 448,
            standard_columns: 168,
            border_columns: 280,
            distinct_border_monomials: 120,
            normal_form_calls: 280,
        };
        assert_eq!(border.repeated_border_columns(), 160);
        assert_eq!(border.duplication_rate(), Some(160.0 / 280.0));
    }

    /// A border with no nonstandard columns has no duplication rate rather than a rate of zero.
    #[test]
    fn test_a_border_free_operator_has_no_duplication_rate() {
        let border = BorderStatistics {
            operator_columns: 16,
            standard_columns: 16,
            ..BorderStatistics::default()
        };
        assert_eq!(border.repeated_border_columns(), 0);
        assert_eq!(border.duplication_rate(), None);
    }

    /// The stage breakdown sums its parts, and operator construction is the three operator stages.
    #[test]
    fn test_the_stage_breakdown_sums_its_parts() {
        let timings = FglmStageTimings {
            quotient_basis: Duration::from_micros(100),
            border_classification: Duration::from_micros(200),
            normal_forms: Duration::from_micros(3_000),
            border_symbolic: Duration::from_micros(70),
            column_assembly: Duration::from_micros(400),
            dependence: Duration::from_micros(500),
        };
        assert_eq!(timings.sum(), Duration::from_micros(4_270));
        assert_eq!(
            timings.operator_construction(),
            Duration::from_micros(3_670)
        );
    }

    /// The span is two triangles — `D (D + 1)` cells — and the accepted vectors are a square.
    #[test]
    fn test_the_dense_blocks_are_two_triangles_and_a_square() {
        let (span, accepted, bytes) = FglmMemory::dense_blocks_for::<F>(64).expect("representable");
        assert_eq!(
            span,
            64 * 65 / 2 + 64 * 65 / 2,
            "offset coordinates plus combinations"
        );
        assert_eq!(span, 64 * 65, "which is `D (D + 1)`");
        assert_eq!(accepted, 64 * 64);
        assert_eq!(bytes, (span + accepted) * size_of::<F>());

        // M17 counted two square blocks and omitted the third; both of the span's blocks are
        // triangular, so the truth is a third less than three squares — 8,256 against 12,288.
        assert!(span + accepted < 3 * 64 * 64);
        assert!(span < 64 * 64 + 64 * 65 / 2, "both blocks, not just one");
    }

    /// A dimension whose square overflows is reported as unrepresentable, not wrapped.
    #[test]
    fn test_an_unrepresentable_dimension_has_no_block_size() {
        assert_eq!(FglmMemory::dense_blocks_for::<F>(usize::MAX), None);
    }

    /// `estimated_bytes` adds the operators to the dense blocks and nothing else.
    #[test]
    fn test_estimated_bytes_adds_the_operators_to_the_dense_blocks() {
        let statistics = FglmStatistics {
            memory: FglmMemory {
                operator_bytes: 4_096,
                dense_block_bytes: 98_304,
                ..FglmMemory::default()
            },
            ..FglmStatistics::default()
        };
        assert_eq!(statistics.estimated_bytes(), 102_400);
    }
}
