//! Block elimination of a Macaulay matrix, and the arrangements it was measured against.
//!
//! Symbolic preprocessing produces two kinds of row, and they play opposite roles: a pair row is
//! the work, a reducer multiple is the machinery that reduces it. The reducer multiples also come
//! with a property the elimination would otherwise have to discover.
//!
//! > **Reducer-block invariant.** Every reducer multiple has a distinct leading monomial, and no
//! > reducer multiple leads with a pair's lcm.
//!
//! Symbolic preprocessing establishes both halves. A reducer is added for a monomial `u` only when
//! `u` is not yet covered, and adding it covers `u`, so no monomial acquires two reducers; and every
//! pair lcm is seeded as covered before the closure starts, so no lcm acquires a reducer at all.
//! Pair rows lead with their pair's lcm, and nothing else does.
//!
//! Macaulay columns descend under the monomial order, so a row's leading column is its leading
//! monomial. Arranging the reducer rows first, ascending by leading column, therefore makes the
//! upper-left block unit upper triangular *by construction*, and
//! [`reduce_rows_against_pivots_with`] can take those pivots as given.
//!
//! The invariant is checked rather than trusted — see [`check_reducer_block`]. A duplicated leading
//! column would make block elimination drop a relation, which is a wrong answer that looks like a
//! right one.
//!
//! [`BlockPlan`] exists because the lever here is the row *arrangement*, not the elimination
//! function: an upper block that is already echelon is left alone by a full `row_echelon` too, so
//! the split-aware function on its own saves only the pivot-discovery scan. Keeping every
//! arrangement callable is what let the choice be made by measurement rather than by argument.

use std::collections::HashMap;

use crate::{
    grobner::f4::{macaulay::MacaulayMatrix, symbolic::RowKind},
    linalg::{
        echelon::{reduce_rows_against_pivots_with, row_echelon_with, Backend},
        sparse::{back_substitute_pivots_within, EliminationStatistics, SparseMatrix},
    },
    FiniteField,
};

/// How a Macaulay matrix's rows are arranged, and what is then done to them.
///
/// Four arrangements rather than two, because "block elimination wins" decomposes into claims that
/// have to be separable to be measured — whether the arrangement helps, whether the split-aware
/// elimination helps on top of it, and whether making the block an identity helps further. Two of
/// the four were measured and kept only as the evidence that rejected them; see §7.1 of
/// `docs/MILESTONE-F4-OPTIMIZATION.md` and `examples/f4_blocks.rs`, which reproduces the numbers.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum BlockPlan {
    /// The rows in the order preprocessing produced them, one echelon pass. The baseline.
    #[default]
    Baseline,

    /// Reducer rows first, then one echelon pass over everything.
    ///
    /// The control. The reducer block is already echelon, so a full pass performs no row operation
    /// on it either — and measured counters confirm this plan is indistinguishable from
    /// [`BlockPlan::ReducersFirstBlock`] in row operations and peak nonzeros on every instance.
    /// That is what establishes the lever as the arrangement rather than the function.
    ReducersFirstEchelon,

    /// Reducer rows first, taken as pivots without a pivot scan and without being touched.
    ///
    /// What [`crate::grobner::ReductionStrategy::Structured`] selects.
    ReducersFirstBlock,

    /// As [`BlockPlan::ReducersFirstBlock`], with the reducer block interreduced first.
    ///
    /// Makes the upper-left block the identity on its own columns, so a pair row needs one
    /// subtraction per reducer column instead of a chain of them — at the cost of filling in the
    /// reducer block, which the other plans never touch. **Measured and rejected**: the fill-in
    /// costs more than the shorter chains save, end to end and on replayed batches alike.
    InterreducedBlock,
}

/// What a block elimination did.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BlockOutcome {
    /// The elimination's own counters, with any preparatory work folded in.
    pub statistics: EliminationStatistics,

    /// Pivots established without a single row operation: the reducer block.
    pub free_pivots: usize,

    /// Rows the back-substitution pass examined, or `None` when it did not run.
    ///
    /// Distinguishes "the pass was off" from "the pass ran and found nothing to do", which are the
    /// two readings of a zero and mean opposite things about whether #477's debt exists.
    pub back_substituted_rows: Option<usize>,
}

/// Whether a batch elimination leaves its rows merely echelon, or reduced.
///
/// The lever #477 is about. Echelon is enough to *extract* candidates — a row's leading column is
/// the same either way, so the selection cannot change — but it leaves every candidate carrying
/// entries in other pivots' columns, i.e. reducible monomials in its tail. That debt accumulates
/// over every batch and is paid once at the end, by final interreduction, as a matrix two orders
/// of magnitude larger in cells than the comparand's.
///
/// Reducing here is not free, and the arithmetic does not say which way it goes: the batch matrices
/// are much larger than the one final interreduction builds, back-substitution is quadratic in the
/// rows whatever the sparsity (#168), and [`BlockPlan::InterreducedBlock`] was already measured and
/// rejected for filling in the reducer block — which is the same fill-in, paid before the
/// elimination instead of after it.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum RowForm {
    /// Leave the rows in echelon form. The shipped behaviour.
    #[default]
    Echelon,

    /// Clear every pivot column from every other row after the plan's elimination.
    ///
    /// Applies to whichever [`BlockPlan`] ran, including the ones that take the reducer block as
    /// given: the pass is a second sweep over the result, not a different elimination.
    Reduced,
}

/// Why a reducer block was not the triangular prefix block elimination relies on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BlockViolation {
    /// A reducer row was zero, so it carries no pivot.
    ZeroRow { row: usize },

    /// A reducer row's leading coefficient was not one.
    UnnormalizedPivot { row: usize },

    /// Two reducer rows led with the same column.
    DuplicateLead {
        first: usize,
        second: usize,
        column: usize,
    },

    /// A reducer row led with a later column than the next one, so the prefix is not triangular.
    OutOfOrder { row: usize },

    /// A pair row led with a column a reducer row owns.
    ///
    /// Not a precondition of [`reduce_rows_against_pivots_with`] — such a row would simply be
    /// reduced — but a violation of the reducer-block invariant, and therefore of the reason the
    /// block is triangular without being made so.
    PairRowSharesAReducerLead { row: usize, column: usize },
}

/// Check the structure [`BlockPlan::ReducersFirstBlock`] relies on, as a value rather than a panic.
///
/// A function rather than only an assertion because `cargo test --release` has to be able to check
/// it: a `debug_assert` is compiled out of exactly the profile the milestone measures in.
pub fn check_reducer_block<F: FiniteField>(
    matrix: &SparseMatrix<F>,
    split: usize,
) -> Result<(), BlockViolation> {
    let mut leads: Vec<usize> = Vec::with_capacity(split);
    for row in 0..split {
        let sparse = matrix.row(row);
        let Some(column) = sparse.leading_column() else {
            return Err(BlockViolation::ZeroRow { row });
        };
        if sparse.leading_coefficient() != Some(F::ONE) {
            return Err(BlockViolation::UnnormalizedPivot { row });
        }
        if let Some(&previous) = leads.last() {
            if previous == column {
                return Err(BlockViolation::DuplicateLead {
                    first: row - 1,
                    second: row,
                    column,
                });
            }
            if previous > column {
                return Err(BlockViolation::OutOfOrder { row });
            }
        }
        leads.push(column);
    }

    for row in split..matrix.num_rows() {
        if let Some(column) = matrix.row(row).leading_column() {
            if leads.binary_search(&column).is_ok() {
                return Err(BlockViolation::PairRowSharesAReducerLead { row, column });
            }
        }
    }

    Ok(())
}

/// Eliminate a Macaulay matrix under the given plan.
///
/// # Panics
/// In a debug build, if the reducer block violates [`check_reducer_block`]. In any build,
/// [`reduce_rows_against_pivots_with`] rejects a duplicated or unnormalized pivot itself, so the
/// case that would give a wrong answer is refused either way.
///
/// # Errors
/// The live entry count that crossed `max_nonzeros`, as the elimination functions report it.
pub fn eliminate<const N: usize, F: FiniteField>(
    plan: BlockPlan,
    backend: Backend,
    matrix: &mut MacaulayMatrix<N, F>,
    max_nonzeros: usize,
) -> Result<BlockOutcome, usize> {
    eliminate_to(plan, RowForm::Echelon, backend, matrix, max_nonzeros)
}

/// [`eliminate`], with the row form the result is left in chosen by the caller.
///
/// # Panics
/// As [`eliminate`].
///
/// # Errors
/// The live entry count that crossed `max_nonzeros`, from either pass.
pub fn eliminate_to<const N: usize, F: FiniteField>(
    plan: BlockPlan,
    form: RowForm,
    backend: Backend,
    matrix: &mut MacaulayMatrix<N, F>,
    max_nonzeros: usize,
) -> Result<BlockOutcome, usize> {
    let mut outcome = eliminate_in_echelon(plan, backend, matrix, max_nonzeros)?;
    if form == RowForm::Reduced {
        // The second pass is sparse whatever the backend chose for the first. The dense and
        // accumulated kernels exist for the pivot-discovery sweep over a batch matrix; this pass
        // visits only the rows that hold a pivot column, which is the shape the sparse one is
        // already output-sensitive in, and duplicating it per backend would be three copies of a
        // pass whose cost this issue exists to find out.
        let rows = back_substitute_pivots_within(
            matrix.matrix_mut(),
            max_nonzeros,
            &mut outcome.statistics,
        )?;
        outcome.back_substituted_rows = Some(rows);
    }
    Ok(outcome)
}

/// The plan's own elimination, leaving the rows in echelon form.
fn eliminate_in_echelon<const N: usize, F: FiniteField>(
    plan: BlockPlan,
    backend: Backend,
    matrix: &mut MacaulayMatrix<N, F>,
    max_nonzeros: usize,
) -> Result<BlockOutcome, usize> {
    if plan == BlockPlan::Baseline {
        let statistics = row_echelon_with(backend, matrix.matrix_mut(), max_nonzeros)?;
        return Ok(BlockOutcome {
            statistics,
            free_pivots: 0,
            back_substituted_rows: None,
        });
    }

    let split = matrix.partition_reducers_first();
    debug_assert_eq!(
        check_reducer_block(matrix.matrix(), split),
        Ok(()),
        "the reducer block is not the triangular prefix symbolic preprocessing makes it"
    );

    match plan {
        BlockPlan::Baseline => unreachable!("handled above"),

        // Every row is eliminated, including the reducer block against itself — which costs
        // nothing, since the block's leading columns are already distinct. The arrangement is the
        // only difference from the baseline.
        BlockPlan::ReducersFirstEchelon => Ok(BlockOutcome {
            statistics: row_echelon_with(backend, matrix.matrix_mut(), max_nonzeros)?,
            free_pivots: 0,
            back_substituted_rows: None,
        }),

        BlockPlan::ReducersFirstBlock => Ok(BlockOutcome {
            statistics: reduce_rows_against_pivots_with(
                backend,
                matrix.matrix_mut(),
                split,
                max_nonzeros,
            )?,
            free_pivots: split,
            back_substituted_rows: None,
        }),

        BlockPlan::InterreducedBlock => {
            let initial_nonzeros = matrix.nonzeros();
            let mut preparation = EliminationStatistics {
                initial_nonzeros,
                peak_nonzeros: initial_nonzeros,
                ..Default::default()
            };
            interreduce_prefix(matrix.matrix_mut(), split, max_nonzeros, &mut preparation)?;

            let mut statistics =
                reduce_rows_against_pivots_with(backend, matrix.matrix_mut(), split, max_nonzeros)?;
            // The elimination measured the matrix it was handed, which interreduction had already
            // rewritten. Reported against the matrix as built, so the counters stay comparable
            // with the other plans.
            statistics.initial_nonzeros = initial_nonzeros;
            statistics.row_operations += preparation.row_operations;
            statistics.peak_nonzeros = statistics.peak_nonzeros.max(preparation.peak_nonzeros);
            Ok(BlockOutcome {
                statistics,
                free_pivots: split,
                back_substituted_rows: None,
            })
        }
    }
}

/// Clear every prefix pivot column from every other prefix row.
///
/// Right to left, so that a row is already free of every pivot column to its own right by the time
/// it is subtracted from anything — which is what makes one subtraction per pivot column enough.
/// Leading columns and leading coefficients are untouched, so the prefix remains the pivot block
/// [`reduce_rows_against_pivots_with`] requires.
fn interreduce_prefix<F: FiniteField>(
    matrix: &mut SparseMatrix<F>,
    split: usize,
    max_nonzeros: usize,
    statistics: &mut EliminationStatistics,
) -> Result<(), usize> {
    let mut pivot_of_column: HashMap<usize, usize> = HashMap::with_capacity(split);
    for index in 0..split {
        if let Some(column) = matrix.row(index).leading_column() {
            pivot_of_column.insert(column, index);
        }
    }

    let mut resident = matrix.nonzeros();
    let mut scratch: Vec<(usize, F)> = Vec::new();
    for index in (0..split).rev() {
        let mut row = std::mem::take(&mut matrix.rows_mut()[index]);
        resident -= row.nonzeros();

        // Entry zero is this row's own pivot and stays. A subtraction clears the entry at
        // `position` without disturbing anything to its left, because the row subtracted leads
        // with that very column — so the cursor does not advance when it fires.
        let mut position = 1;
        while position < row.entries().len() {
            let (column, coefficient) = row.entries()[position];
            match pivot_of_column.get(&column) {
                Some(&pivot) if pivot > index => {
                    row.subtract_scaled(matrix.row(pivot), &coefficient, &mut scratch);
                    statistics.row_operations += 1;
                    let live = resident + row.nonzeros();
                    statistics.peak_nonzeros = statistics.peak_nonzeros.max(live);
                    if live > max_nonzeros {
                        return Err(live);
                    }
                }
                _ => position += 1,
            }
        }

        resident += row.nonzeros();
        matrix.rows_mut()[index] = row;
    }

    Ok(())
}

/// How many of a batch's rows are reducer multiples, which bounds what any of this can save.
pub fn reducer_rows<const N: usize, F: FiniteField>(matrix: &MacaulayMatrix<N, F>) -> usize {
    matrix
        .row_origins()
        .iter()
        .filter(|row| row.kind == RowKind::Reducer)
        .count()
}

#[cfg(test)]
mod tests {
    use super::{check_reducer_block, eliminate, reducer_rows, BlockPlan, BlockViolation};
    use crate::{
        fields::{Zp13, Zp2147483647},
        grobner::{
            benchmark_systems::{cyclic, katsura},
            f4::{
                macaulay::MacaulayMatrix,
                options::F4Options,
                symbolic::{symbolic_preprocessing, MonicBasis, RowKind},
                trace_batches,
            },
            pairs::CriticalPair,
        },
        identities::Zero,
        linalg::echelon::Backend,
        poly::MonomialOrder,
        FiniteField, MultivariatePolynomial, One,
    };

    type F = Zp13;
    const VARS: [&str; 3] = ["x", "y", "z"];
    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];
    const ALL_PLANS: [BlockPlan; 4] = [
        BlockPlan::Baseline,
        BlockPlan::ReducersFirstEchelon,
        BlockPlan::ReducersFirstBlock,
        BlockPlan::InterreducedBlock,
    ];

    fn system(strings: &[&str]) -> Vec<MultivariatePolynomial<3, F>> {
        strings
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, VARS).unwrap())
            .collect()
    }

    /// Every pair of a system, as one batch.
    fn all_pairs<const N: usize, G: FiniteField>(
        polynomials: &[MultivariatePolynomial<N, G>],
        order: MonomialOrder,
    ) -> Vec<CriticalPair<N>> {
        let mut pairs = Vec::new();
        for left in 0..polynomials.len() {
            for right in (left + 1)..polynomials.len() {
                pairs.push(CriticalPair::new(polynomials, left, right, order));
            }
        }
        pairs
    }

    /// The Macaulay matrix of every pair of a system, before elimination.
    fn matrix_of(strings: &[&str], order: MonomialOrder) -> MacaulayMatrix<3, F> {
        let polynomials = system(strings);
        let basis = MonicBasis::new(&polynomials, order);
        let pairs = all_pairs(&polynomials, order);
        let preprocessed = symbolic_preprocessing(&basis, &pairs);
        MacaulayMatrix::build(&basis, &preprocessed, order)
    }

    /// The small systems the hand checks and the per-plan comparisons run over.
    fn corpus() -> Vec<Vec<&'static str>> {
        vec![
            vec!["x^2 + y", "x^2 + z"],
            vec!["x^2 - y", "x*y - 1"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^2*y + x", "x*y^2 + y"],
            vec!["x^3 - 2*x*y", "x^2*y - 2*y^2 + x"],
            vec!["x*z - y^2", "x^3 - z^2"],
            vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
            vec!["x^2 + y^2 + z^2", "x*y + y*z"],
            vec!["x^2 + y + 1", "y^2 + z + 2", "z^2 + x + 3"],
            // Three generators sharing a leading monomial, so several pairs share an lcm.
            vec!["x^2 + y", "x^2 + z", "x^2 + y + z"],
        ]
    }

    /// Partitioning puts every reducer row first, ascending by leading column, and keeps the pair
    /// rows in arrival order.
    #[test]
    fn test_partitioning_sorts_the_reducer_block_and_preserves_the_pair_order() {
        for order in ALL_ORDERS {
            for strings in corpus() {
                let original = matrix_of(&strings, order);
                let mut matrix = original.clone();
                let split = matrix.partition_reducers_first();

                assert!(matrix.row_origins()[..split]
                    .iter()
                    .all(|row| row.kind == RowKind::Reducer));
                assert!(matrix.row_origins()[split..]
                    .iter()
                    .all(|row| row.kind != RowKind::Reducer));
                for window in matrix.matrix().rows()[..split].windows(2) {
                    assert!(
                        window[0].leading_column() < window[1].leading_column(),
                        "{:?} under {}: the reducer block is not ascending",
                        strings,
                        order.name()
                    );
                }
                let pairs_before: Vec<_> = original
                    .row_origins()
                    .iter()
                    .filter(|row| row.kind != RowKind::Reducer)
                    .collect();
                let pairs_after: Vec<_> = matrix.row_origins()[split..].iter().collect();
                assert_eq!(pairs_before, pairs_after, "{}", order.name());
            }
        }
    }

    /// Every row still round-trips to its own polynomial after the rows are permuted.
    #[test]
    fn test_partitioning_keeps_coefficients_with_their_provenance() {
        for order in ALL_ORDERS {
            let polynomials = system(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"]);
            let basis = MonicBasis::new(&polynomials, order);
            let pairs = all_pairs(&polynomials, order);
            let preprocessed = symbolic_preprocessing(&basis, &pairs);
            let mut matrix = MacaulayMatrix::build(&basis, &preprocessed, order);
            matrix.partition_reducers_first();

            for index in 0..matrix.num_rows() {
                let origin = matrix.row_origins()[index];
                assert_eq!(
                    matrix.row_polynomial(index),
                    basis.shifted_polynomial(origin.basis_index, &origin.multiplier),
                    "{}: row {}",
                    order.name(),
                    index
                );
            }
        }
    }

    /// The reducer block has distinct leading columns and unit pivots on every corpus batch.
    #[test]
    fn test_the_reducer_block_is_a_unit_triangular_prefix() {
        for order in ALL_ORDERS {
            for strings in corpus() {
                let mut matrix = matrix_of(&strings, order);
                let split = matrix.partition_reducers_first();
                assert_eq!(
                    check_reducer_block(matrix.matrix(), split),
                    Ok(()),
                    "{:?} under {}",
                    strings,
                    order.name()
                );
            }
        }
    }

    /// The reducer-block invariant holds on every batch of a real computation, in release too.
    ///
    /// The claim is about symbolic preprocessing, so it is checked on the batches F4 actually
    /// builds rather than on hand-written ones, and through a function rather than a
    /// `debug_assert` — which the profile the milestone measures in compiles out.
    #[test]
    fn test_the_invariant_holds_on_every_traced_batch() {
        type G = Zp2147483647;

        fn check<const N: usize>(
            name: &str,
            generators: &[MultivariatePolynomial<N, G>],
            order: MonomialOrder,
        ) {
            let (_, _, trace) =
                trace_batches(generators, order, &F4Options::baseline()).expect("within limits");
            for (index, batch) in trace.batches().iter().enumerate() {
                let preprocessed = symbolic_preprocessing(&batch.basis, &batch.pairs);
                let reducers = preprocessed
                    .rows
                    .iter()
                    .filter(|row| row.kind == RowKind::Reducer)
                    .count();
                let mut matrix = MacaulayMatrix::build(&batch.basis, &preprocessed, order);
                let split = matrix.partition_reducers_first();
                assert_eq!(
                    check_reducer_block(matrix.matrix(), split),
                    Ok(()),
                    "{} under {}: batch {}",
                    name,
                    order.name(),
                    index
                );
                assert_eq!(
                    split,
                    reducers,
                    "{} under {}: batch {}",
                    name,
                    order.name(),
                    index
                );
            }
        }

        for order in ALL_ORDERS {
            check("cyclic-4", &cyclic::<4, G>(), order);
            check("katsura-5", &katsura::<5, G>(), order);
        }
    }

    /// The hand-verifiable batch: x^2+y and x^2+z need no reducer, so the block is empty.
    #[test]
    fn test_a_batch_with_no_reducer_rows_splits_at_zero() {
        for order in ALL_ORDERS {
            let mut matrix = matrix_of(&["x^2 + y", "x^2 + z"], order);
            assert_eq!(matrix.num_rows(), 2, "{}", order.name());
            assert_eq!(reducer_rows(&matrix), 0, "{}", order.name());
            assert_eq!(matrix.partition_reducers_first(), 0, "{}", order.name());
        }
    }

    /// A batch of no pairs has no rows, which is the only way the split can be the row count.
    ///
    /// Every pair contributes two rows and neither is a reducer, so "every row is a reducer" is
    /// unreachable for a nonempty batch rather than merely unusual.
    #[test]
    fn test_an_empty_batch_splits_at_its_row_count() {
        let order = MonomialOrder::Lexicographic;
        let polynomials = system(&["x^2 + y"]);
        let basis = MonicBasis::new(&polynomials, order);
        let preprocessed = symbolic_preprocessing(&basis, &[]);
        let mut matrix = MacaulayMatrix::build(&basis, &preprocessed, order);
        assert_eq!(matrix.num_rows(), 0);
        assert_eq!(matrix.partition_reducers_first(), 0);

        for strings in corpus() {
            let matrix = matrix_of(&strings, order);
            let pair_rows = matrix
                .row_origins()
                .iter()
                .filter(|row| row.kind != RowKind::Reducer)
                .count();
            assert!(
                pair_rows >= 2,
                "{:?}: a nonempty batch has pair rows",
                strings
            );
        }
    }

    /// A hand-checkable block: x^2-y and x*y-1 need the reducer that puts the block above the pair.
    #[test]
    fn test_a_hand_verifiable_block() {
        // Under lex the pair is (x^2 - y, x*y - 1) with lcm x^2*y, so the halves are y*(x^2 - y)
        // and x*(x*y - 1): rows x^2*y - y^2 and x^2*y - x. The monomial y^2 is divisible by
        // nothing, x is divisible by nothing, so the one reducible monomial is none of them --
        // the batch needs no reducer. Adding y^2 - 1 makes y^2 reducible and gives exactly one.
        let order = MonomialOrder::Lexicographic;
        let mut matrix = matrix_of(&["x^2 - y", "x*y - 1", "y^2 - 1"], order);
        let before = matrix.row_origins().to_vec();
        let split = matrix.partition_reducers_first();

        assert_eq!(
            split,
            before
                .iter()
                .filter(|row| row.kind == RowKind::Reducer)
                .count()
        );
        assert_eq!(check_reducer_block(matrix.matrix(), split), Ok(()));
        // The block's own columns are the first `split` leading columns, strictly increasing, and
        // each row is zero to the left of its own pivot -- upper triangular, with ones on the
        // diagonal.
        for row in 0..split {
            let sparse = matrix.matrix().row(row);
            assert_eq!(sparse.leading_coefficient(), Some(F::ONE));
            for other in 0..row {
                let column = matrix.matrix().row(other).leading_column().unwrap();
                assert!(
                    sparse.coefficient(column).is_zero(),
                    "row {} is nonzero in row {}'s pivot column",
                    row,
                    other
                );
            }
        }
    }

    /// Every plan finds the same rank, the same zero rows, and the same pivot columns.
    ///
    /// The pivot columns of a row echelon form do not depend on the order the rows were in, so
    /// this is the property the arrangements must share — and the one candidate extraction reads.
    #[test]
    fn test_every_plan_agrees_on_rank_and_pivot_columns() {
        for order in ALL_ORDERS {
            for strings in corpus() {
                let original = matrix_of(&strings, order);
                let mut expected: Option<(usize, usize, Vec<usize>)> = None;

                for plan in ALL_PLANS {
                    let mut matrix = original.clone();
                    let outcome = eliminate(plan, Backend::Sparse, &mut matrix, usize::MAX)
                        .expect("unbounded cannot fail");
                    let mut pivots: Vec<usize> = (0..matrix.num_rows())
                        .filter_map(|index| matrix.matrix().row(index).leading_column())
                        .collect();
                    pivots.sort_unstable();
                    let observed = (
                        outcome.statistics.rank,
                        outcome.statistics.zero_rows,
                        pivots,
                    );
                    match &expected {
                        None => expected = Some(observed),
                        Some(reference) => assert_eq!(
                            &observed,
                            reference,
                            "{:?} under {} disagreed at {:?}",
                            strings,
                            order.name(),
                            plan
                        ),
                    }
                }
            }
        }
    }

    /// The structured plans report the reducer block as free pivots; the baseline reports none.
    #[test]
    fn test_free_pivots_are_the_reducer_block() {
        for order in ALL_ORDERS {
            for strings in corpus() {
                let original = matrix_of(&strings, order);
                let reducers = original
                    .row_origins()
                    .iter()
                    .filter(|row| row.kind == RowKind::Reducer)
                    .count();

                for (plan, expected) in [
                    (BlockPlan::Baseline, 0),
                    (BlockPlan::ReducersFirstEchelon, 0),
                    (BlockPlan::ReducersFirstBlock, reducers),
                    (BlockPlan::InterreducedBlock, reducers),
                ] {
                    let mut matrix = original.clone();
                    let outcome = eliminate(plan, Backend::Sparse, &mut matrix, usize::MAX)
                        .expect("unbounded cannot fail");
                    assert_eq!(
                        outcome.free_pivots,
                        expected,
                        "{:?} under {} at {:?}",
                        strings,
                        order.name(),
                        plan
                    );
                }
            }
        }
    }

    /// Interreducing the block leaves a pivot column with one entry in the block, and the pivots
    /// themselves untouched.
    #[test]
    fn test_interreduction_clears_the_block_without_moving_its_pivots() {
        for order in ALL_ORDERS {
            for strings in corpus() {
                let mut arranged = matrix_of(&strings, order);
                let split = arranged.partition_reducers_first();
                let leads: Vec<usize> = (0..split)
                    .map(|row| arranged.matrix().row(row).leading_column().unwrap())
                    .collect();

                let mut matrix = matrix_of(&strings, order);
                eliminate(
                    BlockPlan::InterreducedBlock,
                    Backend::Sparse,
                    &mut matrix,
                    usize::MAX,
                )
                .expect("unbounded cannot fail");

                for (row, &column) in leads.iter().enumerate() {
                    assert_eq!(
                        matrix.matrix().row(row).leading_column(),
                        Some(column),
                        "{:?} under {}: pivot {} moved",
                        strings,
                        order.name(),
                        row
                    );
                    for other in 0..split {
                        if other == row {
                            continue;
                        }
                        assert!(
                            matrix.matrix().row(other).coefficient(column).is_zero(),
                            "{:?} under {}: column {} is not cleared in row {}",
                            strings,
                            order.name(),
                            column,
                            other
                        );
                    }
                }
            }
        }
    }

    /// Every plan honours the entry budget, refusing the work rather than reporting it afterwards.
    #[test]
    fn test_every_plan_enforces_the_entry_budget() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let original = matrix_of(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"], order);
        let initial = original.nonzeros();

        for plan in ALL_PLANS {
            let mut matrix = original.clone();
            assert_eq!(
                eliminate(plan, Backend::Sparse, &mut matrix, initial - 1),
                Err(initial),
                "{:?}: a budget below the input should be refused immediately",
                plan
            );
            let mut matrix = original.clone();
            assert!(
                eliminate(plan, Backend::Sparse, &mut matrix, usize::MAX).is_ok(),
                "{:?}",
                plan
            );
        }
    }

    /// A duplicated reducer lead is reported rather than silently dropping a relation.
    #[test]
    fn test_a_duplicated_reducer_lead_is_a_violation() {
        let order = MonomialOrder::Lexicographic;
        let polynomials = system(&["x^2 + y", "x^2 + z"]);
        let basis = MonicBasis::new(&polynomials, order);
        let pairs = all_pairs(&polynomials, order);
        let preprocessed = symbolic_preprocessing(&basis, &pairs);
        let matrix = MacaulayMatrix::build(&basis, &preprocessed, order);

        // Both rows lead with x^2, so treating both as pivots is exactly the violation.
        assert_eq!(
            check_reducer_block(matrix.matrix(), 2),
            Err(BlockViolation::DuplicateLead {
                first: 0,
                second: 1,
                column: 0
            })
        );
        // And treating the first as a pivot leaves the second leading with its column.
        assert_eq!(
            check_reducer_block(matrix.matrix(), 1),
            Err(BlockViolation::PairRowSharesAReducerLead { row: 1, column: 0 })
        );
    }

    /// A zero, unnormalized, or descending prefix row is reported as the violation it is.
    #[test]
    fn test_the_remaining_prefix_violations_are_reported() {
        use crate::linalg::sparse::{SparseMatrix, SparseRow};

        let unnormalized = SparseMatrix::new(3, vec![SparseRow::new(&[(0, F::new(3))])]);
        assert_eq!(
            check_reducer_block(&unnormalized, 1),
            Err(BlockViolation::UnnormalizedPivot { row: 0 })
        );

        let zero = SparseMatrix::new(3, vec![SparseRow::<F>::zero()]);
        assert_eq!(
            check_reducer_block(&zero, 1),
            Err(BlockViolation::ZeroRow { row: 0 })
        );

        let descending = SparseMatrix::new(
            3,
            vec![
                SparseRow::new(&[(1, F::ONE)]),
                SparseRow::new(&[(0, F::ONE)]),
            ],
        );
        assert_eq!(
            check_reducer_block(&descending, 2),
            Err(BlockViolation::OutOfOrder { row: 1 })
        );

        // An empty prefix is vacuously fine, and so is a matrix with nothing in it.
        assert_eq!(check_reducer_block(&descending, 0), Ok(()));
        assert_eq!(
            check_reducer_block(&SparseMatrix::<F>::new(0, Vec::new()), 0),
            Ok(())
        );
    }
}
