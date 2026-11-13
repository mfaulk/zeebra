use super::{shape::krylov_span_bounded, Dependence, QuotientAlgebra};
use crate::{FiniteField, UnivariatePolynomial};
use std::{
    fmt,
    mem::size_of,
    time::{Duration, Instant},
};

/// Incremental limits for a spectral operation on an already constructed algebra.
///
/// Workspace excludes existing operators and allocator overhead. Work units conservatively
/// count coefficient updates, including skipped zeros; they are not CPU instructions.
#[derive(Clone, Copy, Debug)]
pub struct SpectralOptions {
    /// Largest quotient dimension admitted before workspace allocation.
    pub max_dimension: usize,
    /// Conservative incremental representation allowance, including returned coefficients.
    pub max_workspace_bytes: usize,
    /// Conservative coefficient-update allowance.
    pub max_work_units: usize,
    /// Cooperative elapsed-time limit, checked before each bounded arithmetic block.
    pub max_duration: Duration,
}

impl Default for SpectralOptions {
    fn default() -> Self {
        Self {
            max_dimension: 128,
            max_workspace_bytes: 256 * 1024 * 1024,
            max_work_units: 100_000_000,
            max_duration: Duration::from_secs(30),
        }
    }
}

/// Resource charges for one successful operation, separate from algebra construction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpectralStatistics {
    /// Conservative allowance including coefficient buffers, returned polynomial and metadata.
    pub workspace_bytes: usize,
    /// Dense matrix coefficient bytes, zero for the minimal-polynomial path.
    pub materialized_bytes: usize,
    /// Coefficient-update allowance consumed by this operation.
    pub work_units: usize,
}

/// Invalid input and resource refusal are distinct from algebra-construction errors.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpectralError {
    InvalidVariable { variable: usize, variables: usize },
    DimensionExceeded { dimension: usize, limit: usize },
    WorkspaceExceeded { bytes: usize, limit: usize },
    WorkExceeded { limit: usize },
    DeadlineExceeded,
    SizeOverflow,
}
impl fmt::Display for SpectralError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "spectral operation refused: {self:?}")
    }
}
impl std::error::Error for SpectralError {}

struct Budget<'a> {
    options: &'a SpectralOptions,
    start: Instant,
    statistics: SpectralStatistics,
}
impl<'a> Budget<'a> {
    fn new<F: FiniteField>(
        d: usize,
        dense: bool,
        options: &'a SpectralOptions,
    ) -> Result<Self, SpectralError> {
        let start = Instant::now();
        if d > options.max_dimension {
            return Err(SpectralError::DimensionExceeded {
                dimension: d,
                limit: options.max_dimension,
            });
        }
        // Four square blocks cover geometric Vec capacity growth in the span, or the
        // dense matrix plus Berkowitz registers. Linear slack covers all live temporaries.
        let cells = d
            .checked_mul(d)
            .and_then(|x| x.checked_mul(4))
            .and_then(|x| d.checked_mul(24).and_then(|y| x.checked_add(y)))
            .and_then(|x| x.checked_add(8))
            .ok_or(SpectralError::SizeOverflow)?;
        let bytes = cells
            .checked_mul(size_of::<F>())
            .and_then(|x| d.checked_mul(256).and_then(|y| x.checked_add(y)))
            .ok_or(SpectralError::SizeOverflow)?;
        if bytes > options.max_workspace_bytes {
            return Err(SpectralError::WorkspaceExceeded {
                bytes,
                limit: options.max_workspace_bytes,
            });
        }
        let mut budget = Self {
            options,
            start,
            statistics: SpectralStatistics {
                workspace_bytes: bytes,
                materialized_bytes: if dense {
                    d.checked_mul(d)
                        .and_then(|x| x.checked_mul(size_of::<F>()))
                        .ok_or(SpectralError::SizeOverflow)?
                } else {
                    0
                },
                work_units: 0,
            },
        };
        budget.charge(0)?;
        Ok(budget)
    }
    fn charge(&mut self, units: usize) -> Result<(), SpectralError> {
        if self.start.elapsed() >= self.options.max_duration {
            return Err(SpectralError::DeadlineExceeded);
        }
        let work = self
            .statistics
            .work_units
            .checked_add(units)
            .ok_or(SpectralError::SizeOverflow)?;
        if work > self.options.max_work_units {
            return Err(SpectralError::WorkExceeded {
                limit: self.options.max_work_units,
            });
        }
        self.statistics.work_units = work;
        Ok(())
    }
}

impl<const N: usize, F: FiniteField> QuotientAlgebra<N, F> {
    /// Monic minimal polynomial of multiplication by `x_variable`, in ascending coefficient order.
    ///
    /// Reuses the shape diagnostic's first Krylov dependence, without requiring shape position
    /// or radicality. For multiplication in a unital algebra, `p(T)1 = p(x) = 0` implies
    /// `p(T)b = p(x)b = 0` for every class `b`; this argument does not hold for arbitrary matrices.
    /// Both spectral operations return 1 in dimension zero and reject `variable >= N` first.
    pub fn variable_minimal_polynomial(
        &self,
        variable: usize,
        options: &SpectralOptions,
    ) -> Result<(UnivariatePolynomial<F>, SpectralStatistics), SpectralError> {
        self.check_spectral_variable(variable)?;
        let d = self.dimension();
        let mut budget = Budget::new::<F>(d, false, options)?;
        let (mut span, degree, power) =
            krylov_span_bounded(self, variable, |units| budget.charge(units))?;
        budget.charge(2usize.saturating_mul(d).saturating_mul(d + 1))?;
        let Dependence::Dependent { coefficients } = span.reduce(&power) else {
            unreachable!("full Krylov span must contain its next power")
        };
        let mut result: Vec<F> = coefficients.into_iter().map(|c| -c).collect();
        result.resize(degree + 1, F::zero());
        result[degree] = F::one();
        budget.charge(degree + 1)?;
        Ok((UnivariatePolynomial::new(&result), budget.statistics))
    }

    /// Monic `det(tI - T_variable)` with multiplicities, over every supported characteristic.
    ///
    /// Division-free Berkowitz on a dense materialization: O(D^4) coefficient work and O(D^2)
    /// workspace. Limits apply to this new workspace and work, separately from existing operators.
    pub fn variable_characteristic_polynomial(
        &self,
        variable: usize,
        options: &SpectralOptions,
    ) -> Result<(UnivariatePolynomial<F>, SpectralStatistics), SpectralError> {
        self.check_spectral_variable(variable)?;
        let d = self.dimension();
        let mut budget = Budget::new::<F>(d, true, options)?;
        let mut matrix = vec![F::zero(); d * d];
        for j in 0..d {
            budget.charge(d)?;
            for (i, c) in self.operator(variable).column(j).into_iter().enumerate() {
                matrix[i * d + j] = c;
            }
        }
        // Descending coefficients for the trailing principal submatrix, initially det(empty)=1.
        let mut polynomial = vec![F::one()];
        for k in (0..d).rev() {
            let n = d - k;
            let mut toeplitz = vec![F::zero(); n + 1];
            toeplitz[0] = F::one();
            toeplitz[1] = -matrix[k * d + k];
            let mut v: Vec<F> = (k + 1..d).map(|i| matrix[i * d + k]).collect();
            for coefficient in toeplitz.iter_mut().take(n + 1).skip(2) {
                budget.charge(n)?;
                *coefficient = -(k + 1..d)
                    .zip(&v)
                    .map(|(j, c)| matrix[k * d + j] * *c)
                    .fold(F::zero(), |a, b| a + b);
                let mut next = vec![F::zero(); n - 1];
                for (i, slot) in next.iter_mut().enumerate() {
                    budget.charge(n)?;
                    *slot = v
                        .iter()
                        .enumerate()
                        .map(|(j, c)| matrix[(k + 1 + i) * d + k + 1 + j] * *c)
                        .fold(F::zero(), |a, b| a + b);
                }
                v = next;
            }
            let mut next = vec![F::zero(); n + 1];
            for (i, slot) in next.iter_mut().enumerate() {
                budget.charge(n + 1)?;
                for j in 0..=i.min(polynomial.len() - 1) {
                    *slot += toeplitz[i - j] * polynomial[j];
                }
            }
            polynomial = next;
        }
        polynomial.reverse();
        budget.charge(d + 1)?;
        Ok((UnivariatePolynomial::new(&polynomial), budget.statistics))
    }

    fn check_spectral_variable(&self, variable: usize) -> Result<(), SpectralError> {
        if variable >= N {
            Err(SpectralError::InvalidVariable {
                variable,
                variables: N,
            })
        } else {
            Ok(())
        }
    }
}
