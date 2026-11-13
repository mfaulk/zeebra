use std::fmt::{Display, Formatter};

/// Why an FGLM computation stopped without a result.
///
/// Modelled on [`F4Error`](crate::grobner::F4Error), including its discipline about what a variant
/// carries: a limit alone where the computation stops at the first crossing, and the measured
/// value too where the overshoot is bounded and therefore informative. There is deliberately no
/// variant for "finished but incomplete".
///
/// Variants are added as the implementation becomes able to produce them, so that every variant
/// names a failure that can really happen.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FglmError {
    /// The ideal is positive-dimensional, so R/I is infinite and has no monomial basis.
    ///
    /// Not a resource failure: no budget would make the computation possible. The zero ideal is
    /// this case too, for a ring with at least one variable.
    PositiveDimensional,

    /// The multiplication operators needed more stored entries than the limit allowed.
    ///
    /// Carries the count as well as the limit, which is informative here: the budget is tested
    /// after each column is built, so the overshoot is bounded by a single column.
    OperatorStorageExceeded { entries: usize, limit: usize },

    /// The multiplication operators' columns needed more bytes than the limit allowed.
    ///
    /// Distinct from [`Self::OperatorStorageExceeded`], which counts mathematical nonzeros. The two
    /// diverge once a column is held densely: the same nonzeros then occupy `D` cells. Carries the
    /// count as well as the limit, bounded by one column's overshoot for the same reason.
    OperatorBytesExceeded { bytes: usize, limit: usize },

    /// The dependence test needed more entries than the limit allowed.
    ///
    /// Carries the count, which is known from `D` before anything is allocated.
    SpanStorageExceeded { entries: usize, limit: usize },

    /// The dependence test's dense blocks needed more bytes than the limit allowed.
    ///
    /// Stands to [`Self::SpanStorageExceeded`] as [`Self::OperatorBytesExceeded`] stands to
    /// [`Self::OperatorStorageExceeded`]. Here the two diverge by the field width alone: a cell is
    /// one `F`, so the same cell count is 8 bytes over a 64-bit prime field and 32 over a 254-bit
    /// one. Carries the count, known from `D` before anything is allocated.
    SpanBytesExceeded { bytes: usize, limit: usize },

    /// The source was not a Gröbner basis under the order it was said to be one under.
    ///
    /// Detected, not assumed: the conversion accepts exactly `D` target standard monomials when
    /// the source is a Gröbner basis, and a different count means the quotient the operators were
    /// built over was not `R/I`. A caller wanting the precondition checked up front rather than
    /// discovered should use the checked entry point.
    NotAGrobnerBasis,

    /// A batched border reduction's closure crossed one of its limits.
    ///
    /// Carries which limit by name and its value, and **not** the measured size: the closure is
    /// discovered a row at a time and the work of finding out how large it would really have been
    /// is the work being refused. See
    /// [`BorderBatch`](crate::grobner::fglm::BorderBatch).
    BorderBatchExceeded {
        /// Which closure limit was crossed, or `"worker scratch cells"` for the opt-in
        /// `research-work` executor measurement.
        reason: &'static str,
        /// Its value.
        limit: usize,
    },

    /// More standard monomials than the limit allowed.
    ///
    /// Carries only the limit. Enumeration stops at the first crossing, so any count it could
    /// report would be the limit plus one rather than the dimension the ideal really has.
    QuotientDimensionExceeded { limit: usize },
}

impl Display for FglmError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PositiveDimensional => write!(
                f,
                "the ideal is positive-dimensional, so its quotient algebra is infinite"
            ),
            Self::OperatorStorageExceeded { entries, limit } => write!(
                f,
                "the multiplication operators needed {} entries, over the limit of {}",
                entries, limit
            ),
            Self::OperatorBytesExceeded { bytes, limit } => write!(
                f,
                "the multiplication operators needed {} bytes, over the limit of {}",
                bytes, limit
            ),
            Self::SpanStorageExceeded { entries, limit } => write!(
                f,
                "the dependence test needed {} entries, over the limit of {}",
                entries, limit
            ),
            Self::SpanBytesExceeded { bytes, limit } => write!(
                f,
                "the dependence test needed {} bytes, over the limit of {}",
                bytes, limit
            ),
            Self::NotAGrobnerBasis => {
                write!(f, "the source is not a Gröbner basis under the given order")
            }
            Self::BorderBatchExceeded { reason, limit } => write!(
                f,
                "a batched border reduction needed more {} than the limit of {}",
                reason, limit
            ),
            Self::QuotientDimensionExceeded { limit } => write!(
                f,
                "the quotient algebra has more than the {} dimensions allowed",
                limit
            ),
        }
    }
}

impl std::error::Error for FglmError {}
