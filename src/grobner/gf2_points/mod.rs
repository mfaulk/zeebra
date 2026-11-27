//! `GF(2)` point solving by enumeration, outside the Gröbner pipeline (#1156).
//!
//! An opt-in route for dense quadratic Boolean systems in at most 64 variables. It returns
//! `GF(2)`-rational points — the points the field-equation pipeline
//! ([`with_field_equations`](crate::grobner::with_field_equations) then `solve_one`) returns —
//! and every point it returns has been checked by substitution into the input.
//!
//! Two methods, both complete (a `None` means the system has no `GF(2)` point):
//!
//! - [`Gf2Method::Exhaustive`]: a bitsliced Gray-code walk over all `2^n` points, two word
//!   operations per point for up to 64 equations at once.
//! - [`Gf2Method::Crossbred`]: Joux–Vitse at `(D, d = 1)`. A degree-`D` Macaulay matrix is
//!   eliminated once to find combinations of the equations whose degree in the first `k`
//!   variables is at most one. The other `n − k` variables are then enumerated, and at each guess
//!   those combinations are a linear system in `k` unknowns. Exhaustive search is the special
//!   case with nothing to keep; `(k, D) = (1, 2)` is exhaustive search over `n − 1` variables
//!   with the last one solved linearly.
//!
//! `docs/research/gf2-point-solving.md` has the design, the correctness evidence, and what the
//! gate on the bench host has to measure.

mod crossbred;
mod kernel;

use std::{
    sync::{
        atomic::{AtomicU64, Ordering},
        Mutex,
    },
    thread,
};

pub use crossbred::{CrossbredParameters, CrossbredStatistics};

use crate::{fields::Zp2, MultivariatePolynomial, One, Zero};
use kernel::QuadraticLanes;

/// The most variables a system may have: a point is one `u64`.
pub const MAX_GF2_VARIABLES: usize = 64;

/// Exhaustive search walks the low `EXHAUSTIVE_CHUNK_BITS` variables per chunk and fixes the rest.
const EXHAUSTIVE_CHUNK_BITS: usize = 20;

/// Why a system was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Gf2PointError {
    /// More than [`MAX_GF2_VARIABLES`] variables.
    TooManyVariables { variables: usize },
    /// A generator has degree above two once `x_i² = x_i` has been applied.
    NotQuadratic { generator: usize, degree: u32 },
    /// Crossbred parameters outside `1 ≤ k ≤ min(n, 63)` and `2 ≤ D ≤ n`.
    InvalidParameters {
        variables: usize,
        kept: usize,
        degree: usize,
    },
    /// The Macaulay matrix would exceed the configured budget.
    MatrixTooLarge {
        rows: usize,
        columns: usize,
        bytes: usize,
        budget: usize,
    },
    /// A point the Boolean system accepted failed on the original generators. A bug, never an
    /// input property: it would mean the conversion lost a term.
    VerificationFailed,
}

impl std::fmt::Display for Gf2PointError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooManyVariables { variables } => {
                write!(f, "{variables} variables; at most {MAX_GF2_VARIABLES}")
            }
            Self::NotQuadratic { generator, degree } => write!(
                f,
                "generator {generator} has Boolean degree {degree}; only quadratic systems"
            ),
            Self::InvalidParameters {
                variables,
                kept,
                degree,
            } => write!(
                f,
                "crossbred (k = {kept}, D = {degree}) is outside 1 ≤ k ≤ min(n, 63), 2 ≤ D ≤ n for n = {variables}"
            ),
            Self::MatrixTooLarge {
                rows,
                columns,
                bytes,
                budget,
            } => write!(
                f,
                "Macaulay matrix {rows} × {columns} needs {bytes} bytes, over the {budget}-byte budget"
            ),
            Self::VerificationFailed => {
                write!(f, "a point failed substitution into the original generators")
            }
        }
    }
}

impl std::error::Error for Gf2PointError {}

/// Which enumeration to run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Gf2Method {
    Exhaustive,
    Crossbred(CrossbredParameters),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Gf2PointOptions {
    pub method: Gf2Method,
    /// Threads that walk chunks. The returned point does not depend on it.
    pub workers: usize,
    /// The largest packed Macaulay matrix crossbred may build.
    pub matrix_budget_bytes: usize,
}

impl Default for Gf2PointOptions {
    fn default() -> Self {
        Self {
            method: Gf2Method::Exhaustive,
            workers: 1,
            matrix_budget_bytes: 1 << 30,
        }
    }
}

/// What a solve did.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Gf2PointReport {
    /// Chunks the enumeration is split into; each fixes the high enumerated variables.
    pub chunks: u64,
    /// Chunks walked before the answer was settled.
    pub chunks_walked: u64,
    /// Enumerated points per chunk.
    pub points_per_chunk: u64,
    /// Points that passed the kernel's filter and were checked against every equation.
    pub candidates: u64,
    /// Crossbred's preprocessing, when it ran.
    pub preprocessing: Option<CrossbredStatistics>,
}

/// One quadratic Boolean equation, reduced by `x_i² = x_i`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Equation {
    /// `upper[i]` bit `j > i`: the coefficient of `x_i x_j`.
    upper: Vec<u64>,
    linear: u64,
    constant: bool,
}

impl Equation {
    fn zero(vars: usize) -> Self {
        Self {
            upper: vec![0; vars],
            ..Self::default()
        }
    }

    /// Adds the monomial `Π_{i ∈ mask} x_i` (at most two variables).
    fn toggle(&mut self, mask: u64) {
        match mask.count_ones() {
            0 => self.constant ^= true,
            1 => self.linear ^= mask,
            2 => {
                let i = mask.trailing_zeros();
                self.upper[i as usize] ^= mask & !(1 << i);
            }
            _ => unreachable!("only quadratic monomials are stored"),
        }
    }

    fn value(&self, x: u64) -> bool {
        let mut parity = (self.linear & x).count_ones() & 1 == 1;
        parity ^= self.constant;
        let mut rest = x;
        while rest != 0 {
            let i = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            parity ^= (self.upper[i] & x).count_ones() & 1 == 1;
        }
        parity
    }

    /// The monomials, as variable masks.
    fn monomials(&self) -> impl Iterator<Item = u64> + '_ {
        let quadratic = self.upper.iter().enumerate().flat_map(|(i, &row)| {
            (0..64)
                .filter(move |j| row >> j & 1 == 1)
                .map(move |j| 1u64 << i | 1u64 << j)
        });
        let linear = (0..64)
            .filter(|i| self.linear >> i & 1 == 1)
            .map(|i| 1u64 << i);
        quadratic.chain(linear).chain(self.constant.then_some(0u64))
    }
}

/// A quadratic system over `GF(2)` in `n ≤ 64` variables, under `x_i² = x_i`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BooleanQuadraticSystem {
    vars: usize,
    equations: Vec<Equation>,
}

impl BooleanQuadraticSystem {
    /// Each equation is a list of monomials, a monomial being the mask of its variables. Repeated
    /// monomials cancel.
    ///
    /// # Errors
    /// More than 64 variables, a monomial outside them, or one of more than two variables.
    pub fn from_monomial_masks(vars: usize, equations: &[Vec<u64>]) -> Result<Self, Gf2PointError> {
        if vars > MAX_GF2_VARIABLES {
            return Err(Gf2PointError::TooManyVariables { variables: vars });
        }
        let outside = if vars == 64 { 0 } else { !0u64 << vars };
        let equations = equations
            .iter()
            .enumerate()
            .map(|(generator, terms)| {
                let mut equation = Equation::zero(vars);
                for &mask in terms {
                    if mask & outside != 0 || mask.count_ones() > 2 {
                        return Err(Gf2PointError::NotQuadratic {
                            generator,
                            degree: mask.count_ones(),
                        });
                    }
                    equation.toggle(mask);
                }
                Ok(equation)
            })
            .collect::<Result<_, _>>()?;
        Ok(Self { vars, equations })
    }

    /// The Boolean system of `system`: every exponent above one becomes one, which is exact on
    /// `GF(2)` points.
    ///
    /// # Errors
    /// `N > 64`, or a generator of Boolean degree above two.
    pub fn from_polynomials<const N: usize>(
        system: &[MultivariatePolynomial<N, Zp2>],
    ) -> Result<Self, Gf2PointError> {
        if N > MAX_GF2_VARIABLES {
            return Err(Gf2PointError::TooManyVariables { variables: N });
        }
        let masks: Vec<Vec<u64>> = system
            .iter()
            .map(|p| {
                p.terms()
                    .iter()
                    .filter(|(_, c)| !c.is_zero())
                    .map(|(monomial, _)| {
                        monomial
                            .exponents()
                            .iter()
                            .enumerate()
                            .filter(|(_, &e)| e > 0)
                            .fold(0u64, |mask, (i, _)| mask | 1 << i)
                    })
                    .collect()
            })
            .collect();
        Self::from_monomial_masks(N, &masks)
    }

    pub fn variables(&self) -> usize {
        self.vars
    }

    pub fn equations(&self) -> usize {
        self.equations.len()
    }

    /// Whether every equation vanishes at `x` (bit `i` is `x_i`).
    pub fn vanishes_at(&self, x: u64) -> bool {
        self.equations.iter().all(|e| !e.value(x))
    }

    /// One point, or `None` if there is none.
    ///
    /// The point is the first one in a fixed enumeration order, so it does not depend on
    /// `options.workers`.
    ///
    /// # Errors
    /// Crossbred's parameters or matrix budget; see [`Gf2PointError`].
    pub fn solve_one(
        &self,
        options: &Gf2PointOptions,
    ) -> Result<(Option<u64>, Gf2PointReport), Gf2PointError> {
        let (points, report) = self.run(options, true)?;
        Ok((points.first().copied(), report))
    }

    /// Every point, ascending.
    ///
    /// # Errors
    /// As [`solve_one`](Self::solve_one).
    pub fn all_points(
        &self,
        options: &Gf2PointOptions,
    ) -> Result<(Vec<u64>, Gf2PointReport), Gf2PointError> {
        self.run(options, false)
    }

    fn run(
        &self,
        options: &Gf2PointOptions,
        first: bool,
    ) -> Result<(Vec<u64>, Gf2PointReport), Gf2PointError> {
        match options.method {
            Gf2Method::Exhaustive => Ok(self.exhaustive(options.workers, first)),
            Gf2Method::Crossbred(parameters) => crossbred::solve(self, parameters, options, first),
        }
    }

    fn exhaustive(&self, workers: usize, first: bool) -> (Vec<u64>, Gf2PointReport) {
        let t = self.vars.min(EXHAUSTIVE_CHUNK_BITS);
        let filter = &self.equations[..self.equations.len().min(64)];
        let mut pair = vec![0u64; t * t];
        for (lane, equation) in filter.iter().enumerate() {
            for i in 0..t {
                for j in i + 1..t {
                    if equation.upper[i] >> j & 1 == 1 {
                        pair[i * t + j] |= 1 << lane;
                        pair[j * t + i] |= 1 << lane;
                    }
                }
            }
        }
        let chunks = 1u64 << (self.vars - t);
        let candidates = AtomicU64::new(0);
        let walk = |chunk: u64, emit: &mut dyn FnMut(u64) -> bool| {
            let high = chunk << t;
            let mut lanes = QuadraticLanes {
                vars: t,
                pair: pair.clone(),
                linear: vec![0; t],
                constant: 0,
            };
            for (lane, equation) in filter.iter().enumerate() {
                let bit = 1u64 << lane;
                for i in 0..t {
                    let b = (equation.linear >> i & 1)
                        ^ u64::from((equation.upper[i] & high).count_ones() & 1);
                    lanes.linear[i] |= b * bit;
                }
                if equation.value(high) {
                    lanes.constant |= bit;
                }
            }
            let mut seen = 0;
            lanes.gray_code_zeros(|low| {
                seen += 1;
                let x = high | low;
                !self.vanishes_at(x) || emit(x)
            });
            candidates.fetch_add(seen, Ordering::Relaxed);
        };
        let (points, walked) = drive(chunks, workers, first, &walk);
        let report = Gf2PointReport {
            chunks,
            chunks_walked: walked,
            points_per_chunk: 1 << t,
            candidates: candidates.into_inner(),
            preprocessing: None,
        };
        (points, report)
    }
}

/// Walks one chunk, passing each point to the callback until it returns `false`.
type ChunkWalk<'a> = dyn Fn(u64, &mut dyn FnMut(u64) -> bool) + Sync + 'a;

/// Walks chunks `0..chunks` on `workers` threads. `walk(chunk, emit)` calls `emit` with each point
/// of the chunk in its own order and stops when `emit` returns `false`.
///
/// With `first`, the result is the first point of the lowest chunk that has one — the same point a
/// serial walk returns — and chunks above it are skipped. Otherwise every point, sorted. Also
/// returns the number of chunks walked.
fn drive(chunks: u64, workers: usize, first: bool, walk: &ChunkWalk<'_>) -> (Vec<u64>, u64) {
    let next = AtomicU64::new(0);
    let settled = AtomicU64::new(u64::MAX);
    let walked = AtomicU64::new(0);
    let found = Mutex::new(Vec::<(u64, u64)>::new());
    let work = || loop {
        let chunk = next.fetch_add(1, Ordering::Relaxed);
        if chunk >= chunks || (first && chunk > settled.load(Ordering::Acquire)) {
            return;
        }
        walked.fetch_add(1, Ordering::Relaxed);
        let mut local = Vec::new();
        walk(chunk, &mut |x| {
            local.push((chunk, x));
            !first
        });
        if !local.is_empty() {
            settled.fetch_min(chunk, Ordering::AcqRel);
            found
                .lock()
                .expect("no worker panics holding it")
                .extend(local);
        }
    };
    let workers = workers.clamp(1, chunks.max(1) as usize);
    if workers == 1 {
        work();
    } else {
        thread::scope(|scope| {
            for _ in 0..workers {
                scope.spawn(work);
            }
        });
    }
    let mut found = found.into_inner().expect("no worker panicked");
    let points = if first {
        found.sort_unstable_by_key(|&(chunk, _)| chunk);
        found.first().map(|&(_, x)| x).into_iter().collect()
    } else {
        let mut points: Vec<u64> = found.into_iter().map(|(_, x)| x).collect();
        points.sort_unstable();
        points.dedup();
        points
    };
    (points, walked.into_inner())
}

/// The point `x` as field elements.
fn to_field<const N: usize>(x: u64) -> [Zp2; N] {
    std::array::from_fn(|i| {
        if x >> i & 1 == 1 {
            Zp2::one()
        } else {
            Zp2::zero()
        }
    })
}

fn verified<const N: usize>(
    system: &[MultivariatePolynomial<N, Zp2>],
    x: u64,
) -> Result<[Zp2; N], Gf2PointError> {
    let point = to_field::<N>(x);
    if system.iter().all(|p| p.eval(&point).is_zero()) {
        Ok(point)
    } else {
        Err(Gf2PointError::VerificationFailed)
    }
}

/// One `GF(2)` point of `system`, checked by substitution into `system` itself, or `None`.
///
/// # Errors
/// See [`Gf2PointError`].
pub fn gf2_solve_one<const N: usize>(
    system: &[MultivariatePolynomial<N, Zp2>],
    options: &Gf2PointOptions,
) -> Result<(Option<[Zp2; N]>, Gf2PointReport), Gf2PointError> {
    let boolean = BooleanQuadraticSystem::from_polynomials(system)?;
    let (x, report) = boolean.solve_one(options)?;
    Ok((x.map(|x| verified(system, x)).transpose()?, report))
}

/// Every `GF(2)` point of `system`, each checked by substitution, in ascending bit order.
///
/// # Errors
/// See [`Gf2PointError`].
pub fn gf2_all_points<const N: usize>(
    system: &[MultivariatePolynomial<N, Zp2>],
    options: &Gf2PointOptions,
) -> Result<(Vec<[Zp2; N]>, Gf2PointReport), Gf2PointError> {
    let boolean = BooleanQuadraticSystem::from_polynomials(system)?;
    let (points, report) = boolean.all_points(options)?;
    let points = points
        .into_iter()
        .map(|x| verified(system, x))
        .collect::<Result<_, _>>()?;
    Ok((points, report))
}

#[cfg(test)]
mod tests;
