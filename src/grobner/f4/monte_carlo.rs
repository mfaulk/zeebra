//! Opt-in Monte Carlo zero skipping (#1184): random block combinations rule dependent pair rows out.
//!
//! The argument, the bound and the output contract are in
//! `docs/research/monte-carlo-zero-skipping.md`. In short: a batch's pair rows are cut into blocks;
//! each block is tested by reducing uniformly random combinations of its rows against the current
//! pivots, a nonzero residual becomes a pivot, and after `zero_tests` zero residuals the rest of the
//! block is discarded. Every row the matrix keeps is still a combination of its original rows, so the
//! output stays inside the ideal; the only possible error is a **missing** relation, which
//! [`F4Options::certify`](super::F4Options::certify) detects.

use rand::{rngs::StdRng, SeedableRng};

use crate::{
    grobner::f4::{macaulay::MacaulayMatrix, symbolic::RowKind, F4Statistics},
    linalg::sparse::SparseRow,
    FiniteField, KnownOrder, MultivariatePolynomial,
};

/// The Monte Carlo mode's parameters. Read only by [`f4_monte_carlo`](super::f4_monte_carlo); the
/// exact entry points refuse an [`F4Options`](super::F4Options) that carries one.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct MonteCarloZeros {
    /// The seed. A call is a deterministic function of the input, the options and this seed; batch
    /// `k` draws from a stream derived from `(seed, k)`.
    pub seed: u64,

    /// Zero residuals a block must produce before its remaining rows are discarded. Each bounds the
    /// per-block error by about one more factor of `1/q`. `0` discards every block untested, which
    /// is useful only as fault injection.
    pub zero_tests: u32,

    /// Rows per block, or `None` for `ceil(sqrt(pair rows))` per batch (Monagan–Pearce §2).
    pub block_rows: Option<usize>,

    /// The most blocks one call may screen. The rest are reduced exactly. This deterministic cap,
    /// not the observed block count, is what the whole-call bound is a union over.
    pub max_blocks: u64,
}

impl MonteCarloZeros {
    /// Two zero tests, `sqrt` blocks and a cap of 2^20 blocks.
    pub const fn new(seed: u64) -> Self {
        Self {
            seed,
            zero_tests: 2,
            block_rows: None,
            max_blocks: 1 << 20,
        }
    }

    /// This configuration for batch `index` of a call, with `used` of the call's blocks spent.
    pub(crate) fn for_batch(self, index: u64, used: u64) -> Self {
        Self {
            seed: split_mix(self.seed ^ split_mix(index)),
            max_blocks: self.max_blocks.saturating_sub(used),
            ..self
        }
    }
}

/// SplitMix64's finalizer, to spread `(seed, batch)` over the seed space.
fn split_mix(mut z: u64) -> u64 {
    z = z.wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// What screening did. Zero throughout on the exact route.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct MonteCarloStatistics {
    /// Batches that were screened.
    pub batches: usize,
    /// Nonzero pair rows offered to screening.
    pub screened_rows: usize,
    /// Rows left for exact elimination because the call's block cap ran out.
    pub unscreened_rows: usize,
    /// Blocks screened: each is one event under the whole-call bound.
    pub blocks: usize,
    /// Blocks closed by `zero_tests` zero residuals, their remaining rows discarded.
    pub discarded_blocks: usize,
    /// Blocks whose every row became a pivot, which needs no test and carries no risk.
    pub exhausted_blocks: usize,
    /// Random combinations reduced.
    pub combinations: usize,
    /// Of those, the ones that reduced to zero: the zero rows this route still reduces in full.
    pub zero_combinations: usize,
    /// Rows ruled zero without being reduced: screened rows minus the pivots they yielded.
    pub rows_ruled_zero: usize,
    /// New pivots, one per nonzero combination.
    pub pivots: usize,
    /// Coefficient products: combination building plus reduction against pivots.
    pub products: usize,
}

impl MonteCarloStatistics {
    pub(crate) fn record(&mut self, other: &Self) {
        self.batches += other.batches;
        self.screened_rows += other.screened_rows;
        self.unscreened_rows += other.unscreened_rows;
        self.blocks += other.blocks;
        self.discarded_blocks += other.discarded_blocks;
        self.exhausted_blocks += other.exhausted_blocks;
        self.combinations += other.combinations;
        self.zero_combinations += other.zero_combinations;
        self.rows_ruled_zero += other.rows_ruled_zero;
        self.pivots += other.pivots;
        self.products = self.products.saturating_add(other.products);
    }
}

/// The bound a Monte Carlo basis was computed under.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MonteCarloGuarantee {
    /// The configuration, as passed.
    pub configuration: MonteCarloZeros,
    /// The largest probability [`FiniteField::random`] gives any one element, `1/q` when uniform.
    pub atom: f64,
    /// Probability that one block discards a row outside the pivot span, under ideal draws.
    pub per_block_bound: f64,
    /// `max_blocks * per_block_bound`, capped at 1: the probability that the call drops a relation.
    pub whole_call_bound: f64,
    /// Whether [`F4Options::certify`](super::F4Options::certify) ran and passed, in which case the
    /// basis is exact and the bound no longer applies.
    pub certified: bool,
}

/// A basis from [`f4_monte_carlo`](super::f4_monte_carlo): a distinct type, so it cannot be passed
/// where an exact basis is expected without the caller saying so.
#[derive(Clone, Debug)]
pub struct MonteCarloBasis<const N: usize, F: FiniteField> {
    /// Every element is in the input ideal. Unless [`MonteCarloGuarantee::certified`], it is the
    /// reduced Gröbner basis with probability at least `1 - whole_call_bound`, and otherwise the
    /// reduced basis of a smaller leading ideal.
    pub basis: Vec<MultivariatePolynomial<N, F>>,
    /// The bound and whether it was discharged by certification.
    pub guarantee: MonteCarloGuarantee,
    /// The run's statistics; [`F4Statistics::monte_carlo`] has the screening counts.
    pub statistics: F4Statistics,
}

/// `alpha^t / prod_{k=1..t} (1 - alpha^k)`: the sum of `alpha^(r_1 + ... + r_t)` over the
/// non-increasing residual ranks `r_1 >= ... >= r_t >= 1` at which a wrong block's zero tests fall.
pub fn per_block_bound(atom: f64, zero_tests: u32) -> f64 {
    let mut bound = 1.0_f64;
    for k in 1..=zero_tests as i32 {
        bound *= atom / (1.0 - atom.powi(k));
    }
    bound.min(1.0)
}

/// The largest probability `F::random` assigns one element.
///
/// Prime fields and characteristic-two fields sample uniformly; an extension of odd characteristic
/// reduces each of its `k` coefficient words mod `p`, so its atom is `(ceil(2^64/p)/2^64)^k`.
pub fn atom<F: KnownOrder>() -> f64 {
    let as_f64 = |limbs: &[u64]| {
        limbs.iter().rev().fold(0.0_f64, |acc, &limb| {
            acc * 18_446_744_073_709_551_616.0 + limb as f64
        })
    };
    let q = as_f64(F::order_limbs());
    let p_limbs = F::characteristic_limbs();
    if F::order_limbs() == p_limbs || p_limbs == [2] {
        return 1.0 / q;
    }
    let p = as_f64(p_limbs);
    let degree = (q.ln() / p.ln()).round() as i32;
    let p_word = p_limbs[0] as u128;
    let word = (1u128 << 64).div_ceil(p_word) as f64 / 18_446_744_073_709_551_616.0;
    word.powi(degree)
}

/// Screen one matrix in place: replace each screened block by its pivots and zero rows.
///
/// The matrix keeps its row count and provenance; a replaced row is a combination of its block's
/// original rows reduced against reducers and earlier pivots, so the row space can only shrink, and
/// it shrinks only on a wrong discard.
pub(crate) fn screen<const N: usize, F: FiniteField>(
    matrix: &mut MacaulayMatrix<N, F>,
    configuration: &MonteCarloZeros,
) -> MonteCarloStatistics {
    const NONE: usize = usize::MAX;
    let rows = matrix.num_rows();
    let columns = matrix.num_columns();
    let mut statistics = MonteCarloStatistics {
        batches: 1,
        ..MonteCarloStatistics::default()
    };

    // Reducers seed the pivot table and pair rows are screened. A reducer whose column is taken,
    // or that is not monic, is neither: it stays in place for exact elimination, which keeps
    // every reducer row nonzero for the structured path.
    let mut pivot = vec![NONE; columns];
    let mut screened: Vec<usize> = Vec::new();
    for (index, origin) in matrix.row_origins().iter().enumerate() {
        let row = matrix.matrix().row(index);
        let Some(lead) = row.leading_column() else {
            continue;
        };
        match origin.kind {
            RowKind::PairComponent { .. } => screened.push(index),
            RowKind::Reducer
                if pivot[lead] == NONE && row.leading_coefficient() == Some(F::ONE) =>
            {
                pivot[lead] = index
            }
            RowKind::Reducer => {}
        }
    }
    statistics.screened_rows = screened.len();
    if screened.is_empty() {
        return statistics;
    }

    let block_rows = configuration
        .block_rows
        .unwrap_or_else(|| (screened.len() as f64).sqrt().ceil() as usize)
        .max(1);
    let mut rng = StdRng::seed_from_u64(configuration.seed);
    let mut fresh: Vec<SparseRow<F>> = Vec::new();
    // Where each block's rows go: (destination row, index into `fresh` or NONE for zero).
    let mut writes: Vec<(usize, usize)> = Vec::new();
    let mut cells = vec![F::ZERO; columns];
    let mut budget = configuration.max_blocks;

    for block in screened.chunks(block_rows) {
        if budget == 0 {
            statistics.unscreened_rows += block.len();
            continue;
        }
        budget -= 1;
        statistics.blocks += 1;
        let first_fresh = fresh.len();
        let mut zeros = 0;
        while zeros < configuration.zero_tests && fresh.len() - first_fresh < block.len() {
            statistics.combinations += 1;
            let mut lowest = columns;
            for &index in block {
                let row = matrix.matrix().row(index);
                let lambda = F::random(&mut rng);
                if lambda.is_zero() {
                    continue;
                }
                statistics.products += row.nonzeros();
                for &(column, value) in row.entries() {
                    cells[column] += lambda * value;
                }
                lowest = lowest.min(row.leading_column().unwrap_or(columns));
            }
            for column in lowest..columns {
                let factor = cells[column];
                if factor.is_zero() || pivot[column] == NONE {
                    continue;
                }
                let source = pivot[column];
                let reducer = if source < rows {
                    matrix.matrix().row(source)
                } else {
                    &fresh[source - rows]
                };
                statistics.products += reducer.nonzeros();
                for &(c, value) in reducer.entries() {
                    cells[c] -= factor * value;
                }
            }
            let mut residual = SparseRow::from_dense(&cells);
            cells[lowest..].iter_mut().for_each(|cell| *cell = F::ZERO);
            if residual.is_zero() {
                statistics.zero_combinations += 1;
                zeros += 1;
                continue;
            }
            residual.normalize();
            let lead = residual.leading_column().expect("nonzero residual");
            debug_assert_eq!(
                pivot[lead], NONE,
                "a reduced residual leads at a free column"
            );
            pivot[lead] = rows + fresh.len();
            fresh.push(residual);
        }
        let found = fresh.len() - first_fresh;
        statistics.pivots += found;
        statistics.rows_ruled_zero += block.len() - found;
        if found == block.len() {
            statistics.exhausted_blocks += 1;
        } else {
            statistics.discarded_blocks += 1;
        }
        for (offset, &destination) in block.iter().enumerate() {
            let source = if offset < found {
                first_fresh + offset
            } else {
                NONE
            };
            writes.push((destination, source));
        }
    }

    let mut fresh: Vec<Option<SparseRow<F>>> = fresh.into_iter().map(Some).collect();
    let target = matrix.matrix_mut().rows_mut();
    for (destination, source) in writes {
        target[destination] = if source == NONE {
            SparseRow::zero()
        } else {
            fresh[source].take().expect("each pivot is written once")
        };
    }
    statistics
}

#[cfg(test)]
mod tests {
    use super::{atom, per_block_bound, MonteCarloZeros};
    use crate::{
        fields::{PrimeFieldElement64, Zp2147483647},
        grobner::{
            benchmark_systems::{cyclic, eco, katsura},
            f4::{
                f4_monte_carlo, f4_reported, f4_with_options, BatchOrder, F4Error, F4Options,
                GradedEngine, ReductionStrategy,
            },
        },
        linalg::Backend,
        poly::MonomialOrder,
        KnownOrder, MultivariatePolynomial,
    };

    type F = Zp2147483647;
    type Goldilocks = PrimeFieldElement64<18446744069414584321>;
    const ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];
    const SEEDS: [u64; 3] = [1, 0x1184, u64::MAX];

    fn parse<const N: usize, G: KnownOrder>(
        names: [&str; N],
        strings: &[&str],
    ) -> Vec<MultivariatePolynomial<N, G>> {
        strings
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
            .collect()
    }

    fn corpus() -> Vec<Vec<MultivariatePolynomial<3, F>>> {
        let names = ["x", "y", "z"];
        [
            &["x^2 + y", "x^2 + z"][..],
            &["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            &["x^2*y + x", "x*y^2 + y"],
            &["x^3 - 2*x*y", "x^2*y - 2*y^2 + x"],
            &["x*z - y^2", "x^3 - z^2"],
            &["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
            &["x^2 + y^2 + z^2", "x*y + y*z"],
            &["x^2 + y + 1", "y^2 + z + 2", "z^2 + x + 3"],
            &["x^2 + y", "x^2 + z", "x^2 + y + z"],
            &["x + y", "3*x + 3*y", "y^2 - 1"],
            &["x", "x - 1"],
        ]
        .iter()
        .map(|strings| parse(names, strings))
        .collect()
    }

    fn mc(options: &F4Options, configuration: MonteCarloZeros) -> F4Options {
        F4Options {
            monte_carlo: Some(configuration),
            ..options.clone()
        }
    }

    /// The Monte Carlo basis, which must equal `expected`, and its screening counts.
    fn agrees<const N: usize, G: KnownOrder>(
        system: &[MultivariatePolynomial<N, G>],
        order: MonomialOrder,
        options: &F4Options,
        configuration: MonteCarloZeros,
        expected: &[MultivariatePolynomial<N, G>],
    ) -> super::MonteCarloStatistics {
        let result = f4_monte_carlo(system, order, &mc(options, configuration)).unwrap();
        assert_eq!(
            result.basis,
            expected,
            "{configuration:?} under {}",
            order.name()
        );
        result.statistics.monte_carlo
    }

    #[test]
    fn test_the_bound_is_the_partition_sum() {
        let alpha = 1.0 / 2_147_483_647.0;
        let two = per_block_bound(alpha, 2);
        let closed = alpha * alpha / ((1.0 - alpha) * (1.0 - alpha * alpha));
        assert!((two / closed - 1.0).abs() < 1e-12);
        assert!((two / 2.168_404e-19 - 1.0).abs() < 1e-5, "{two}");
        assert_eq!(per_block_bound(alpha, 0), 1.0);
        assert!(per_block_bound(alpha, 3) < two * alpha * 1.000_001);
        // Small fields: the bound is honest, and large enough to say the mode is pointless there.
        assert!(per_block_bound(0.5, 2) > 0.5);
        assert_eq!(atom::<F>(), alpha);
        assert_eq!(atom::<Goldilocks>(), 1.0 / 18_446_744_069_414_584_321.0);
    }

    #[test]
    fn test_exact_entry_points_refuse_the_mode() {
        let system = katsura::<3, F>();
        let order = MonomialOrder::GradedReverseLexicographic;
        let options = mc(&F4Options::default(), MonteCarloZeros::new(1));
        let refused = |error: F4Error| matches!(error, F4Error::InvalidOptions { .. });
        assert!(refused(
            f4_with_options(&system, order, &options).unwrap_err()
        ));
        assert!(refused(
            f4_reported(&system, order, &options).0.unwrap_err()
        ));
        let adaptive = F4Options {
            graded_engine: GradedEngine::Adaptive,
            ..options.clone()
        };
        assert!(refused(
            f4_with_options(&system, order, &adaptive).unwrap_err()
        ));
        assert!(refused(
            f4_monte_carlo(&system, order, &F4Options::default()).unwrap_err()
        ));
    }

    #[test]
    fn test_the_basis_is_the_exact_one_on_the_corpus() {
        let presets = [
            F4Options::default(),
            F4Options::baseline(),
            F4Options {
                reduction: ReductionStrategy::Unstructured,
                elimination: Backend::Sparse,
                ..F4Options::default()
            },
            F4Options {
                batch_order: BatchOrder::FaugereLachartre,
                ..F4Options::default()
            },
            F4Options {
                reduce_batch_rows: false,
                ..F4Options::default()
            },
        ];
        for system in corpus() {
            for order in ORDERS {
                let (expected, _) = f4_with_options(&system, order, &F4Options::default()).unwrap();
                for options in &presets {
                    for seed in SEEDS {
                        for block_rows in [None, Some(1), Some(3), Some(1_000)] {
                            let configuration = MonteCarloZeros {
                                block_rows,
                                ..MonteCarloZeros::new(seed)
                            };
                            agrees(&system, order, options, configuration, &expected);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_the_basis_is_the_exact_one_on_the_benchmark_families() {
        fn check<const N: usize>(system: Vec<MultivariatePolynomial<N, F>>, name: &str) {
            for order in [
                MonomialOrder::GradedReverseLexicographic,
                MonomialOrder::GradedLexicographic,
            ] {
                let (expected, exact) =
                    f4_with_options(&system, order, &F4Options::default()).unwrap();
                for seed in SEEDS {
                    let counts = agrees(
                        &system,
                        order,
                        &F4Options::default(),
                        MonteCarloZeros::new(seed),
                        &expected,
                    );
                    // Reduced batch rows are unique, so both routes see the same matrices and
                    // the rows ruled zero are exactly the rows the exact route reduced to zero.
                    assert_eq!(counts.rows_ruled_zero, exact.zero_rows, "{name}");
                    assert_eq!(counts.unscreened_rows, 0, "{name}");
                    assert!(counts.blocks > 0, "{name}");
                }
            }
        }
        check(katsura::<4, F>(), "katsura-4");
        check(katsura::<5, F>(), "katsura-5");
        check(cyclic::<4, F>(), "cyclic-4");
        check(cyclic::<5, F>(), "cyclic-5");
        check(eco::<6, F>(), "eco-6");
    }

    #[test]
    fn test_a_seed_reproduces_the_counts_and_seeds_differ() {
        let system = katsura::<5, F>();
        let order = MonomialOrder::GradedReverseLexicographic;
        let run = |seed| {
            let options = mc(&F4Options::default(), MonteCarloZeros::new(seed));
            f4_monte_carlo(&system, order, &options).unwrap()
        };
        let (first, again, other) = (run(3), run(3), run(4));
        assert_eq!(first.statistics.monte_carlo, again.statistics.monte_carlo);
        assert_eq!(first.guarantee, again.guarantee);
        assert_eq!(first.basis, other.basis);
        // What the bound rests on does not depend on the draws once no block fails.
        let (a, b) = (first.statistics.monte_carlo, other.statistics.monte_carlo);
        assert_eq!(
            (a.blocks, a.pivots, a.rows_ruled_zero),
            (b.blocks, b.pivots, b.rows_ruled_zero)
        );
        assert!(first.guarantee.whole_call_bound <= 2.2e-19 * (1u64 << 20) as f64);
        assert!(!first.guarantee.certified);
    }

    #[test]
    fn test_the_block_cap_bounds_the_call_and_the_rest_is_exact() {
        let system = katsura::<5, F>();
        let order = MonomialOrder::GradedReverseLexicographic;
        let (expected, _) = f4_with_options(&system, order, &F4Options::default()).unwrap();
        for max_blocks in [0, 1, 3, 17] {
            let configuration = MonteCarloZeros {
                max_blocks,
                ..MonteCarloZeros::new(9)
            };
            let counts = agrees(
                &system,
                order,
                &F4Options::default(),
                configuration,
                &expected,
            );
            assert!(counts.blocks as u64 <= max_blocks, "{counts:?}");
            if max_blocks == 0 {
                assert_eq!(counts.unscreened_rows, counts.screened_rows);
                assert_eq!(counts.combinations, 0);
            }
        }
    }

    /// Fault injection: zero tests discard every block untested. The basis loses relations, its
    /// stated bound is 1, and certification refuses it.
    #[test]
    fn test_a_wrong_zero_is_caught_by_certification() {
        let system = katsura::<4, F>();
        let order = MonomialOrder::GradedReverseLexicographic;
        let (expected, _) = f4_with_options(&system, order, &F4Options::default()).unwrap();
        let blind = MonteCarloZeros {
            zero_tests: 0,
            ..MonteCarloZeros::new(1)
        };
        let wrong = f4_monte_carlo(&system, order, &mc(&F4Options::default(), blind)).unwrap();
        assert_ne!(wrong.basis, expected);
        assert_eq!(wrong.guarantee.whole_call_bound, 1.0);
        assert!(wrong.statistics.monte_carlo.discarded_blocks > 0);

        let checked = F4Options {
            certify: true,
            ..F4Options::default()
        };
        assert!(matches!(
            f4_monte_carlo(&system, order, &mc(&checked, blind)),
            Err(F4Error::CertificationFailed { .. })
        ));
        let honest =
            f4_monte_carlo(&system, order, &mc(&checked, MonteCarloZeros::new(1))).unwrap();
        assert_eq!(honest.basis, expected);
        assert!(honest.guarantee.certified);
    }
}
