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
            Self::QuotientDimensionExceeded { limit } => write!(
                f,
                "the quotient algebra has more than the {} dimensions allowed",
                limit
            ),
        }
    }
}

impl std::error::Error for FglmError {}
