//! #1034's matrix-level instrument: the actual F4 batch matrices, regrouped by multidegree.
//!
//! A multidegree-aware F4 would build one matrix per multidegree instead of one per total degree.
//! [`BidegreeCensus`] estimates that saving without implementing it. It observes the matrices
//! conventional F4 builds and, before elimination, groups each matrix's rows by the
//! **multidegree bound** of the row under a declared [`BlockSplit`]: the componentwise maximum of
//! the multidegrees of its terms. Each group is one regrouped block. Its rows are the group's rows,
//! and its columns are the distinct monomials those rows touch.
//!
//! What the regrouping is faithful to:
//!
//! - **Multihomogeneous input.** Every built row is a monomial multiple of a multihomogeneous
//!   polynomial, so every row is multihomogeneous and the matrix is already block-diagonal by
//!   multidegree. The blocks partition the rows, columns and nonzeros, and
//!   [`BatchCensus::block_diagonal`] says so. The largest block is the largest matrix a per-bidegree
//!   construction would face for the same rows.
//! - **Affine input.** A row `t·g` multihomogenizes, with one homogenizing variable per block, to a
//!   row of multidegree `bound(t·g)`. An affine monomial in rows of two different bounds becomes two
//!   different columns, so the blocks' columns can sum to more than the matrix's.
//!   [`BatchCensus::regrouped_columns`] records that duplication. The census counts the rows F4
//!   actually built. It does **not** claim that a multihomogenized computation would build the
//!   same rows: the affine computation passes information across degrees, and a homogenized one
//!   would not.
//!
//! Every count is exact and independent of timing. Nothing here changes what F4 computes: the
//! observer only reads.

use std::collections::HashMap;

use crate::{
    grobner::{
        f4::{f4_observed, BatchObserver, F4Error, F4Options, F4Statistics, MacaulayMatrix},
        pairs::CriticalPair,
        planning::{BlockSplit, BlockSplitError},
    },
    poly::MonomialOrder,
    FiniteField, MultivariatePolynomial,
};

use super::f4::MonicBasis;

/// One regrouped block of one batch matrix.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockCount {
    /// The multidegree bound shared by the block's rows.
    pub multidegree: Vec<u64>,
    pub rows: usize,
    /// Distinct monomials the block's rows touch.
    pub columns: usize,
    pub nonzeros: usize,
}

impl BlockCount {
    /// `rows × columns`, the size measure #1034's hypothesis is stated in.
    pub fn area(&self) -> u128 {
        self.rows as u128 * self.columns as u128
    }
}

/// One F4 batch matrix, as built and as regrouped.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BatchCensus {
    /// The largest total degree of any column.
    pub degree: u64,
    /// Nonzero rows of the matrix as built.
    pub rows: usize,
    pub columns: usize,
    pub nonzeros: usize,
    /// Rows whose terms all share one multidegree.
    pub homogeneous_rows: usize,
    /// The regrouped blocks, ordered by multidegree.
    pub blocks: Vec<BlockCount>,
}

impl BatchCensus {
    /// `rows × columns` of the matrix as built.
    pub fn area(&self) -> u128 {
        self.rows as u128 * self.columns as u128
    }

    /// The block with the largest area. `None` for a matrix with no nonzero row.
    pub fn largest_block(&self) -> Option<&BlockCount> {
        self.blocks.iter().max_by_key(|b| b.area())
    }

    /// Columns summed over blocks. Equal to [`Self::columns`] for a block-diagonal matrix, and
    /// larger when an affine monomial appears in rows of different bounds.
    pub fn regrouped_columns(&self) -> usize {
        self.blocks.iter().map(|b| b.columns).sum()
    }

    /// Every row is multihomogeneous and no column is shared between blocks: the matrix is
    /// exactly the direct sum of its blocks.
    pub fn block_diagonal(&self) -> bool {
        self.homogeneous_rows == self.rows && self.regrouped_columns() == self.columns
    }
}

/// A [`BatchObserver`] that records a [`BatchCensus`] of every matrix F4 builds.
#[derive(Clone, Debug)]
pub struct BidegreeCensus {
    split: BlockSplit,
    batches: Vec<BatchCensus>,
}

impl BidegreeCensus {
    pub fn new(split: BlockSplit) -> Self {
        Self {
            split,
            batches: Vec::new(),
        }
    }

    /// One census per matrix, in the order F4 built them.
    pub fn batches(&self) -> &[BatchCensus] {
        &self.batches
    }

    /// The whole run reduced to the figures #1034's hypothesis compares.
    pub fn summary(&self) -> CensusSummary {
        let largest_matrix = self.batches.iter().map(BatchCensus::area).max();
        let largest_block = self
            .batches
            .iter()
            .filter_map(|b| b.largest_block().map(BlockCount::area))
            .max();
        CensusSummary {
            matrices: self.batches.len(),
            max_degree: self.batches.iter().map(|b| b.degree).max().unwrap_or(0),
            largest_matrix: largest_matrix.unwrap_or(0),
            largest_block: largest_block.unwrap_or(0),
            total_area: self.batches.iter().map(BatchCensus::area).sum(),
            total_block_area: self
                .batches
                .iter()
                .flat_map(|b| b.blocks.iter().map(BlockCount::area))
                .sum(),
            columns: self.batches.iter().map(|b| b.columns).sum(),
            regrouped_columns: self.batches.iter().map(|b| b.regrouped_columns()).sum(),
            block_diagonal: self.batches.iter().all(BatchCensus::block_diagonal),
        }
    }
}

/// A run's census, summed or maximized over its matrices.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CensusSummary {
    /// Matrices built.
    pub matrices: usize,
    /// The largest total degree of any matrix column: the run's solving degree.
    pub max_degree: u64,
    /// The largest `rows × columns` of any matrix as built.
    pub largest_matrix: u128,
    /// The largest `rows × columns` of any regrouped block.
    pub largest_block: u128,
    /// `rows × columns` summed over matrices as built.
    pub total_area: u128,
    /// `rows × columns` summed over every regrouped block.
    pub total_block_area: u128,
    /// Columns summed over matrices as built.
    pub columns: usize,
    /// Columns summed over every regrouped block.
    pub regrouped_columns: usize,
    /// Every matrix was block-diagonal.
    pub block_diagonal: bool,
}

impl CensusSummary {
    /// `largest_matrix / largest_block`: the reduction #1034's hypothesis states, which needs at
    /// least 2. `None` when no block was recorded.
    pub fn largest_reduction(&self) -> Option<f64> {
        (self.largest_block > 0).then(|| self.largest_matrix as f64 / self.largest_block as f64)
    }
}

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for BidegreeCensus {
    fn batch(&mut self, _basis: &MonicBasis<N, F>, _pairs: &[CriticalPair<N>]) {}

    fn matrix(&mut self, matrix: &MacaulayMatrix<N, F>) {
        let columns = matrix.columns();
        let column_degree: Vec<Vec<u64>> = columns
            .iter()
            .map(|m| self.split.multidegree(m.exponents()))
            .collect();
        let words = columns.len().div_ceil(64);
        // multidegree bound -> (rows, nonzeros, column bitset)
        let mut groups: HashMap<Vec<u64>, (usize, usize, Vec<u64>)> = HashMap::new();
        let mut rows = 0;
        let mut homogeneous_rows = 0;
        for row in matrix.matrix().rows() {
            let entries = row.entries();
            let Some(&(first, _)) = entries.first() else {
                continue;
            };
            rows += 1;
            let mut bound = column_degree[first].clone();
            let mut homogeneous = true;
            for &(c, _) in &entries[1..] {
                let d = &column_degree[c];
                homogeneous &= *d == column_degree[first];
                for (b, &x) in bound.iter_mut().zip(d) {
                    *b = (*b).max(x);
                }
            }
            homogeneous_rows += usize::from(homogeneous);
            let group = groups
                .entry(bound)
                .or_insert_with(|| (0, 0, vec![0u64; words]));
            group.0 += 1;
            group.1 += entries.len();
            for &(c, _) in entries {
                group.2[c / 64] |= 1 << (c % 64);
            }
        }
        let mut blocks: Vec<BlockCount> = groups
            .into_iter()
            .map(|(multidegree, (rows, nonzeros, bits))| BlockCount {
                multidegree,
                rows,
                columns: bits.iter().map(|w| w.count_ones() as usize).sum(),
                nonzeros,
            })
            .collect();
        blocks.sort_by(|a, b| a.multidegree.cmp(&b.multidegree));
        self.batches.push(BatchCensus {
            degree: columns.iter().map(|m| m.degree()).max().unwrap_or(0),
            rows,
            columns: columns.len(),
            nonzeros: matrix.nonzeros(),
            homogeneous_rows,
            blocks,
        });
    }
}

/// Why a census run did not complete.
#[derive(Clone, Debug, PartialEq)]
pub enum CensusError {
    Split(BlockSplitError),
    F4(F4Error),
}

/// Conventional F4 on `system`, with every batch matrix regrouped under `split`.
///
/// Returns exactly the basis and statistics [`f4_observed`] returns. The census only reads.
///
/// # Errors
/// [`CensusError::Split`] if `split` does not cover `N` variables, and [`CensusError::F4`] as
/// [`f4_observed`].
#[allow(clippy::type_complexity)]
pub fn bidegree_census<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    split: &BlockSplit,
    order: MonomialOrder,
    options: &F4Options,
) -> Result<
    (
        Vec<MultivariatePolynomial<N, F>>,
        F4Statistics,
        BidegreeCensus,
    ),
    CensusError,
> {
    if split.variables() != N {
        return Err(CensusError::Split(BlockSplitError::WrongLength {
            expected: N,
            found: split.variables(),
        }));
    }
    let mut census = BidegreeCensus::new(split.clone());
    let (basis, statistics) =
        f4_observed(system, order, options, &mut census).map_err(CensusError::F4)?;
    Ok((basis, statistics, census))
}

#[cfg(test)]
mod tests {
    use super::{bidegree_census, CensusError};
    use crate::{
        fields::Zp32003,
        grobner::{
            benchmark_systems::{bilinear, BilinearSpec},
            f4::{f4_with_options, F4Options},
            planning::{BlockSplit, BlockSplitError},
        },
        poly::MonomialOrder,
    };

    type F = Zp32003;
    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    fn spec(affine: bool, equations: usize) -> BilinearSpec {
        BilinearSpec {
            x_variables: 3,
            equations,
            affine,
            support_per_mille: 1000,
            perturbation: 0,
            planted: affine,
            seed: 11,
        }
    }

    /// Bihomogeneous input builds block-diagonal matrices: the blocks partition rows, columns and
    /// nonzeros exactly.
    #[test]
    fn test_bihomogeneous_matrices_are_block_diagonal() {
        let system = bilinear::<6, F>(&spec(false, 4)).generators;
        let split = BlockSplit::two_blocks(6, 3).unwrap();
        let (_, _, census) =
            bidegree_census(&system, &split, GREVLEX, &F4Options::default()).unwrap();
        assert!(!census.batches().is_empty());
        for batch in census.batches() {
            assert!(batch.block_diagonal(), "{batch:?}");
            assert_eq!(
                batch.blocks.iter().map(|b| b.rows).sum::<usize>(),
                batch.rows
            );
            assert_eq!(
                batch.blocks.iter().map(|b| b.nonzeros).sum::<usize>(),
                batch.nonzeros
            );
            // Rows of total degree d split by bidegree (a, d − a).
            for block in &batch.blocks {
                assert_eq!(block.multidegree.iter().sum::<u64>(), batch.degree);
            }
        }
        let summary = census.summary();
        assert!(summary.block_diagonal);
        assert!(summary.largest_reduction().unwrap() >= 1.0);
    }

    /// Affine input is not block-diagonal, and the regrouping duplicates columns rather than
    /// losing any.
    #[test]
    fn test_affine_regrouping_duplicates_columns_and_keeps_rows() {
        let system = bilinear::<6, F>(&spec(true, 6)).generators;
        let split = BlockSplit::two_blocks(6, 3).unwrap();
        let (basis, _, census) =
            bidegree_census(&system, &split, GREVLEX, &F4Options::default()).unwrap();
        assert!(!census.summary().block_diagonal);
        for batch in census.batches() {
            assert_eq!(
                batch.blocks.iter().map(|b| b.rows).sum::<usize>(),
                batch.rows
            );
            assert!(batch.regrouped_columns() >= batch.columns);
        }
        let summary = census.summary();
        assert!(summary.regrouped_columns > summary.columns);
        // Planted, so consistent: the basis is not {1}.
        assert!(basis.iter().all(|p| !p.is_constant()));
    }

    /// Observing changes nothing: same basis as the unobserved route.
    #[test]
    fn test_census_does_not_change_the_basis() {
        let system = bilinear::<6, F>(&spec(true, 6)).generators;
        let split = BlockSplit::two_blocks(6, 3).unwrap();
        let options = F4Options::default();
        let (observed, statistics, census) =
            bidegree_census(&system, &split, GREVLEX, &options).unwrap();
        let (plain, _) = f4_with_options(&system, GREVLEX, &options).unwrap();
        assert_eq!(observed, plain);
        assert_eq!(census.summary().max_degree, statistics.max_pair_degree);
    }

    #[test]
    fn test_split_must_cover_the_ring() {
        let system = bilinear::<6, F>(&spec(true, 6)).generators;
        let split = BlockSplit::two_blocks(5, 2).unwrap();
        assert_eq!(
            bidegree_census(&system, &split, GREVLEX, &F4Options::default()).unwrap_err(),
            CensusError::Split(BlockSplitError::WrongLength {
                expected: 6,
                found: 5
            })
        );
    }
}
