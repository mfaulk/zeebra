//! Exact multidegree structure of a system under a declared block split of its variables.
//!
//! A bilinear or multihomogeneous system's cost is governed by its block structure, not its total
//! degree (#1034), and a solver may only use that structure once it is **verified**: a learned or
//! heuristic signal never establishes it. This module is the check. Given a [`BlockSplit`] that
//! assigns every variable to a block, [`multigrading`] reads each generator's terms and reports
//! their multidegrees: one exponent sum per block.
//!
//! Two exact statements come out of it.
//!
//! - **Multihomogeneous**: every term of a generator has the same multidegree
//!   ([`GeneratorMultidegree::homogeneous`]). For a homogeneous `(1, 1)` system this is
//!   [`MultigradedStructure::all_homogeneous_of`] with `[1, 1]`.
//! - **Within a bound**: every term's multidegree is at most `d` componentwise
//!   ([`MultigradedStructure::within`]). Such a generator is the dehomogenization of a
//!   multihomogeneous form of multidegree `d`, with one homogenizing variable per block, so an
//!   affine bilinear system `xᵀA y + bᵀx + cᵀy + e` is exactly one within `[1, 1]`. Its terms below
//!   the bound, the inhomogeneous part, are counted rather than hidden
//!   ([`GeneratorMultidegree::lower_terms`]).
//!
//! Neither statement says anything about genericity, dimension or regularity: the complexity
//! bounds of Faugère, Safey El Din and Spaenlehauer need those as well, and this module does not
//! check them. `docs/research/bilinear-feasibility.md` records which hypotheses are verified where.

use crate::{FiniteField, MultivariatePolynomial};

/// An assignment of each variable to one of `blocks` blocks, every block nonempty.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockSplit {
    block_of: Vec<usize>,
    blocks: usize,
}

/// Why a [`BlockSplit`] was refused.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BlockSplitError {
    /// The split assigns no variables.
    NoVariables,
    /// Block ids run up to the given maximum, but this block holds no variable.
    EmptyBlock(usize),
    /// The two-block split's first block is empty or holds every variable.
    DegenerateTwoBlock { variables: usize, first: usize },
    /// The split covers a different number of variables than the system has.
    WrongLength { expected: usize, found: usize },
}

impl std::fmt::Display for BlockSplitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoVariables => write!(f, "a block split needs at least one variable"),
            Self::EmptyBlock(b) => write!(f, "block {b} holds no variable"),
            Self::DegenerateTwoBlock { variables, first } => write!(
                f,
                "a two-block split of {variables} variables cannot put {first} in the first block"
            ),
            Self::WrongLength { expected, found } => write!(
                f,
                "the split covers {found} variables but the system has {expected}"
            ),
        }
    }
}

impl std::error::Error for BlockSplitError {}

impl BlockSplit {
    /// A split from `block_of[v]`, the block of variable `v`. Blocks are numbered from zero, and
    /// every id up to the largest must hold a variable.
    pub fn new(block_of: Vec<usize>) -> Result<Self, BlockSplitError> {
        let blocks = block_of
            .iter()
            .max()
            .map(|&b| b + 1)
            .ok_or(BlockSplitError::NoVariables)?;
        let mut seen = vec![false; blocks];
        for &b in &block_of {
            seen[b] = true;
        }
        if let Some(empty) = seen.iter().position(|&s| !s) {
            return Err(BlockSplitError::EmptyBlock(empty));
        }
        Ok(Self { block_of, blocks })
    }

    /// The bilinear split: variables `0 … first − 1` are block 0 (`x`), the rest block 1 (`y`).
    /// This is the split [`crate::grobner::hilbert::BigradedHilbertSeries`] uses.
    pub fn two_blocks(variables: usize, first: usize) -> Result<Self, BlockSplitError> {
        if first == 0 || first >= variables {
            return Err(BlockSplitError::DegenerateTwoBlock { variables, first });
        }
        Self::new((0..variables).map(|v| usize::from(v >= first)).collect())
    }

    /// Variables the split covers.
    pub fn variables(&self) -> usize {
        self.block_of.len()
    }

    /// Number of blocks.
    pub fn blocks(&self) -> usize {
        self.blocks
    }

    /// The block of variable `v`.
    pub fn block_of(&self, v: usize) -> usize {
        self.block_of[v]
    }

    /// Variables in each block.
    pub fn block_sizes(&self) -> Vec<usize> {
        let mut sizes = vec![0; self.blocks];
        for &b in &self.block_of {
            sizes[b] += 1;
        }
        sizes
    }

    /// The multidegree of a monomial: its exponent sum over each block.
    pub fn multidegree(&self, exponents: &[u32]) -> Vec<u64> {
        let mut degree = vec![0u64; self.blocks];
        for (v, &e) in exponents.iter().enumerate() {
            degree[self.block_of[v]] += u64::from(e);
        }
        degree
    }
}

/// One nonzero generator's multidegrees.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GeneratorMultidegree {
    /// Index of the generator in the input.
    pub generator: usize,

    /// The componentwise maximum of its terms' multidegrees: the least `d` it is within.
    /// No single term need attain it (`x + y` has bound `[1, 1]`).
    pub bound: Vec<u64>,

    /// Every term has the same multidegree, which is then [`Self::bound`].
    pub homogeneous: bool,

    /// Distinct multidegrees among its terms.
    pub multidegrees: usize,

    /// Terms whose multidegree is exactly [`Self::bound`].
    pub top_terms: usize,

    /// Terms below [`Self::bound`] in some block: the inhomogeneous part an affine system carries.
    pub lower_terms: usize,
}

/// The multidegree structure of a system under one split.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MultigradedStructure {
    /// Variables in each block of the split.
    pub block_sizes: Vec<usize>,

    /// Nonzero generators, in input order.
    pub generators: Vec<GeneratorMultidegree>,

    /// Zero generators, which have no multidegree and constrain nothing.
    pub zero_generators: usize,
}

impl MultigradedStructure {
    /// Every nonzero generator is multihomogeneous. Vacuously true for a system of zeros.
    pub fn is_multihomogeneous(&self) -> bool {
        self.generators.iter().all(|g| g.homogeneous)
    }

    /// Every nonzero generator is multihomogeneous of multidegree exactly `degree`.
    pub fn all_homogeneous_of(&self, degree: &[u64]) -> bool {
        self.generators
            .iter()
            .all(|g| g.homogeneous && g.bound == degree)
    }

    /// Every nonzero generator has all its terms at most `bound` componentwise: each is the
    /// dehomogenization of a multihomogeneous form of multidegree `bound`.
    pub fn within(&self, bound: &[u64]) -> bool {
        self.violations(bound).is_empty()
    }

    /// Generators with a term above `bound` in some block, by input index.
    pub fn violations(&self, bound: &[u64]) -> Vec<usize> {
        assert_eq!(bound.len(), self.block_sizes.len(), "one bound per block");
        self.generators
            .iter()
            .filter(|g| g.bound.iter().zip(bound).any(|(d, b)| d > b))
            .map(|g| g.generator)
            .collect()
    }

    /// Terms below their generator's bound, summed: zero exactly when every generator is
    /// multihomogeneous.
    pub fn lower_terms(&self) -> usize {
        self.generators.iter().map(|g| g.lower_terms).sum()
    }
}

/// The multidegree structure of `system` under `split`.
///
/// Exact and linear in the total number of terms times `N`.
///
/// # Errors
/// [`BlockSplitError::WrongLength`] if `split` does not cover exactly `N` variables.
pub fn multigrading<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    split: &BlockSplit,
) -> Result<MultigradedStructure, BlockSplitError> {
    if split.variables() != N {
        return Err(BlockSplitError::WrongLength {
            expected: N,
            found: split.variables(),
        });
    }
    let mut generators = Vec::new();
    let mut zero_generators = 0;
    for (index, p) in system.iter().enumerate() {
        if p.is_zero() {
            zero_generators += 1;
            continue;
        }
        let degrees: Vec<Vec<u64>> = p
            .terms()
            .keys()
            .map(|m| split.multidegree(m.exponents()))
            .collect();
        let mut bound = vec![0u64; split.blocks()];
        for d in &degrees {
            for (b, &x) in bound.iter_mut().zip(d) {
                *b = (*b).max(x);
            }
        }
        let mut distinct = degrees.clone();
        distinct.sort_unstable();
        distinct.dedup();
        let top_terms = degrees.iter().filter(|d| **d == bound).count();
        generators.push(GeneratorMultidegree {
            generator: index,
            homogeneous: distinct.len() == 1,
            multidegrees: distinct.len(),
            top_terms,
            lower_terms: degrees.len() - top_terms,
            bound,
        });
    }
    Ok(MultigradedStructure {
        block_sizes: split.block_sizes(),
        generators,
        zero_generators,
    })
}

#[cfg(test)]
mod tests {
    use super::{multigrading, BlockSplit, BlockSplitError};
    use crate::{fields::Zp32003, FiniteField, MultivariatePolynomial};

    type F = Zp32003;

    fn parse<const N: usize, K: FiniteField>(
        strings: &[&str],
        vars: [&str; N],
    ) -> Vec<MultivariatePolynomial<N, K>> {
        strings
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, vars).expect("parses"))
            .collect()
    }

    #[test]
    fn test_split_refuses_empty_and_gapped_blocks() {
        assert_eq!(BlockSplit::new(vec![]), Err(BlockSplitError::NoVariables));
        assert_eq!(
            BlockSplit::new(vec![0, 2, 2]),
            Err(BlockSplitError::EmptyBlock(1))
        );
        assert_eq!(
            BlockSplit::two_blocks(3, 0),
            Err(BlockSplitError::DegenerateTwoBlock {
                variables: 3,
                first: 0
            })
        );
        assert!(BlockSplit::two_blocks(3, 3).is_err());
        let split = BlockSplit::two_blocks(5, 2).unwrap();
        assert_eq!(split.block_sizes(), vec![2, 3]);
        assert_eq!(split.multidegree(&[1, 2, 0, 3, 1]), vec![3, 4]);
    }

    #[test]
    fn test_split_must_cover_the_ring() {
        let system = parse::<3, F>(&["x*z + y"], ["x", "y", "z"]);
        let split = BlockSplit::two_blocks(4, 2).unwrap();
        assert_eq!(
            multigrading(&system, &split),
            Err(BlockSplitError::WrongLength {
                expected: 3,
                found: 4
            })
        );
    }

    /// `x·y` and `x²` collapse to the same total degree; the split tells them apart (#207).
    #[test]
    fn test_bilinear_and_quadratic_differ_under_the_split() {
        let split = BlockSplit::two_blocks(2, 1).unwrap();
        let bilinear = multigrading(&parse::<2, F>(&["x*y - 3"], ["x", "y"]), &split).unwrap();
        let quadratic = multigrading(&parse::<2, F>(&["x^2 - 3"], ["x", "y"]), &split).unwrap();
        assert!(bilinear.within(&[1, 1]));
        assert!(!quadratic.within(&[1, 1]));
        assert_eq!(quadratic.violations(&[1, 1]), vec![0]);
        assert_eq!(quadratic.generators[0].bound, vec![2, 0]);
    }

    #[test]
    fn test_homogeneous_bilinear_system() {
        let system = parse::<4, F>(
            &["x1*y1 + 2*x2*y2", "x1*y2 - x2*y1", "0"],
            ["x1", "x2", "y1", "y2"],
        );
        let split = BlockSplit::two_blocks(4, 2).unwrap();
        let s = multigrading(&system, &split).unwrap();
        assert_eq!(s.zero_generators, 1);
        assert_eq!(s.generators.len(), 2);
        assert!(s.is_multihomogeneous());
        assert!(s.all_homogeneous_of(&[1, 1]));
        assert_eq!(s.lower_terms(), 0);
        assert_eq!(s.block_sizes, vec![2, 2]);
    }

    /// An affine bilinear generator is within `[1, 1]` and not multihomogeneous; its linear and
    /// constant terms are counted as the inhomogeneous part.
    #[test]
    fn test_affine_bilinear_counts_its_inhomogeneous_part() {
        let system = parse::<4, F>(
            &["x1*y1 + x2*y2 + 3*x1 + 5*y2 + 7", "x1 + y1"],
            ["x1", "x2", "y1", "y2"],
        );
        let split = BlockSplit::two_blocks(4, 2).unwrap();
        let s = multigrading(&system, &split).unwrap();
        assert!(s.within(&[1, 1]));
        assert!(!s.is_multihomogeneous());
        let g = &s.generators[0];
        assert_eq!(
            (g.bound.clone(), g.multidegrees, g.top_terms, g.lower_terms),
            (vec![1, 1], 4, 2, 3)
        );
        // x1 + y1 is within [1, 1] although no term attains it.
        let h = &s.generators[1];
        assert_eq!(
            (h.bound.clone(), h.top_terms, h.lower_terms),
            (vec![1, 1], 0, 2)
        );
        assert!(!s.all_homogeneous_of(&[1, 1]));
    }

    /// A perturbed control: one `x_i x_j` term breaks bilinearity, and the verifier names the
    /// generator that carries it.
    #[test]
    fn test_perturbed_control_is_refused() {
        let system = parse::<4, F>(
            &["x1*y1 + x2*y2 + 1", "x1*y2 + x1*x2 + 1", "y1*y2 + x2*y1"],
            ["x1", "x2", "y1", "y2"],
        );
        let split = BlockSplit::two_blocks(4, 2).unwrap();
        let s = multigrading(&system, &split).unwrap();
        assert_eq!(s.violations(&[1, 1]), vec![1, 2]);
        // The same system is within total degree 2 under the one-block split.
        let single = BlockSplit::new(vec![0; 4]).unwrap();
        assert!(multigrading(&system, &single).unwrap().within(&[2]));
    }

    /// Three blocks: a trilinear form is multihomogeneous of `[1, 1, 1]`.
    #[test]
    fn test_three_blocks() {
        let system = parse::<3, F>(&["x*y*z + 2*x*y*z"], ["x", "y", "z"]);
        let split = BlockSplit::new(vec![0, 1, 2]).unwrap();
        let s = multigrading(&system, &split).unwrap();
        assert!(s.all_homogeneous_of(&[1, 1, 1]));
        // 3·xyz is one term.
        assert_eq!(s.generators[0].top_terms, 1);
    }
}
