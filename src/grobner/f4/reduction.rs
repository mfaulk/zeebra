//! The F4 reduction step: a batch of critical pairs in, new basis elements out.
//!
//! Symbolic preprocessing, matrix construction, elimination, and then the step that makes F4 F4:
//!
//! > A nonzero row of the reduced matrix is a **new** relation exactly when its leading monomial
//! > is not the leading monomial of any row that went in.
//!
//! That is Faugère's `F+ = {f in F~ : LM(f) not in LM(F)}`. Rows whose leading monomial was
//! already there carry relations the batch already represented; only a pivot in a column that no
//! input row led with is information the basis did not have.
//!
//! The closure invariant from [`super::symbolic`] is what makes this sound. Every column monomial
//! divisible by some `LM(g)` is the leading monomial of some row, hence excluded — so a candidate's
//! leading monomial is never top-reducible by the current basis. Candidate extraction does not have
//! to test for that; it gets it from the preprocessing being complete, and the tests assert the
//! consequence rather than trusting it.
//!
//! Batch reduction legitimately produces different polynomials from reducing the same pairs one at
//! a time, because a batch can use relations discovered from its other pairs. The requirement is
//! not that the polynomials match but that the ideal is unchanged and the selected pairs end up
//! resolved, which is what the tests check.

use std::mem::size_of;

use crate::{
    grobner::{
        f4::{
            macaulay::{BuildBudgetExceeded, MacaulayMatrix},
            options::{F4Error, F4Options, ReductionStrategy},
            statistics::{BatchStatistics, StageClock},
            structured::{eliminate_to, BlockPlan, RowForm},
            symbolic::{symbolic_preprocessing_with, MonicBasis, ReducerCache, RowKind},
        },
        pairs::CriticalPair,
    },
    linalg::echelon::Backend,
    poly::MonomialOrder,
    FiniteField, MultivariatePolynomial,
};

/// What one batch produced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BatchOutcome<const N: usize, F: FiniteField> {
    /// New basis elements, monic, sorted descending by leading monomial.
    ///
    /// Their leading monomials are distinct, and none is divisible by the leading monomial of a
    /// current basis element. They may still be redundant against each other; interreduction at
    /// the end of the computation deals with that.
    pub candidates: Vec<MultivariatePolynomial<N, F>>,

    /// What the batch cost.
    pub statistics: BatchStatistics,
}

/// Reduce a batch of critical pairs, returning the new basis elements it yields.
///
/// `basis` must be the basis the pairs were built against, under `order`: a pair names basis
/// elements by index and carries the lcm of their leading monomials.
///
/// # Errors
/// Returns an [`F4Error`] if the matrix or its elimination exceeds a limit in `options`. The basis
/// is left untouched, so a caller may retry with a smaller batch.
///
/// Each budget is enforced while the resource it bounds is being consumed — rows as preprocessing
/// discovers them, columns as the monomial set grows, entries as rows are written and as
/// elimination fills them in — so a limit refuses the allocation rather than reporting it after
/// the fact. See [`F4Options::max_live_nonzeros`] for what the entry budget does and does not
/// account for.
pub fn reduce_batch<const N: usize, F: FiniteField>(
    basis: &MonicBasis<N, F>,
    pairs: &[CriticalPair<N>],
    order: MonomialOrder,
    options: &F4Options,
) -> Result<BatchOutcome<N, F>, F4Error> {
    reduce_batch_in(
        basis,
        pairs,
        order,
        options,
        &mut ReducerCache::new(options.reducer_cache),
    )
}

/// As [`reduce_batch`], consulting and populating state carried between batches.
///
/// `cache` is the whole of F4's cross-batch state. It is a parameter rather than something
/// ambient because it is the only thing that could make a batch's result depend on the batches
/// before it, and "the result is a function of the input and the options" has to stay checkable.
///
/// The main loop calls this; [`reduce_batch`] is the same thing with a cache of its own, for a
/// caller driving one batch in isolation.
///
/// # Errors
/// As [`reduce_batch`].
pub fn reduce_batch_in<const N: usize, F: FiniteField>(
    basis: &MonicBasis<N, F>,
    pairs: &[CriticalPair<N>],
    order: MonomialOrder,
    options: &F4Options,
    cache: &mut ReducerCache<N>,
) -> Result<BatchOutcome<N, F>, F4Error> {
    let mut clock = StageClock::new(options.measure_stages);
    let mut stages = crate::grobner::f4::statistics::StageTimings::default();

    // The entry and byte budgets are collapsed to one entry allowance here, so that construction
    // and elimination are checked against a single number and cannot drift apart as either check
    // moves. Which budget produced it decides which error a crossing reports.
    let allowance = options.live_entry_allowance::<F>();

    // Every budget is enforced while the thing it bounds is being built, not after it exists.
    // Symbolic preprocessing discovers rows one at a time and matrix construction writes entries
    // one row at a time, so both can refuse to continue; checking afterwards would mean paying the
    // allocation in order to find out it was not allowed.
    let preprocessed = symbolic_preprocessing_with(
        basis,
        pairs,
        options.max_matrix_rows,
        options.reducer_selection,
        cache,
    )
    .map_err(|exceeded| F4Error::TooManyRows {
        limit: exceeded.limit,
    })?;
    stages.symbolic = clock.lap();

    let mut matrix = MacaulayMatrix::build_within(
        basis,
        &preprocessed,
        order,
        options.max_matrix_columns,
        allowance,
    )
    .map_err(|exceeded| match exceeded {
        BuildBudgetExceeded::Columns { limit } => F4Error::TooManyColumns { limit },
        BuildBudgetExceeded::Nonzeros { nonzeros, .. } => options.entry_budget_error::<F>(nonzeros),
    })?;
    stages.construction = clock.lap();

    let reducer_rows = preprocessed
        .rows
        .iter()
        .filter(|row| row.kind == RowKind::Reducer)
        .count();
    let rows = matrix.num_rows();
    let columns = matrix.num_columns();

    // What the chosen backend allocates on top of the sparse rows. Measured, not budgeted: under
    // `Backend::Dense` it is a function of the shape alone — which the row and column budgets
    // already bound — and charging it to `max_live_bytes` would make the default refuse
    // computations the entry budget admits, on katsura-7 among others.
    let dense_buffer_bytes = match options.elimination {
        Backend::Sparse => 0,
        Backend::Dense => rows.saturating_mul(columns).saturating_mul(size_of::<F>()),
        Backend::Adaptive => columns.saturating_mul(size_of::<F>()),
    };

    // The one elimination call site, so that a structured path and a dense backend can be chosen
    // independently of each other and neither has to touch the other's files.
    let structured = matches!(options.reduction, ReductionStrategy::Structured);
    let plan = match options.reduction {
        ReductionStrategy::Unstructured => BlockPlan::Baseline,
        ReductionStrategy::Structured => BlockPlan::ReducersFirstBlock,
    };
    let form = if options.reduce_batch_rows {
        RowForm::Reduced
    } else {
        RowForm::Echelon
    };
    let block = eliminate_to(plan, form, options.elimination, &mut matrix, allowance)
        .map_err(|nonzeros| options.entry_budget_error::<F>(nonzeros))?;
    let elimination = block.statistics;
    stages.elimination = clock.lap();

    // A pivot in a column no input row led with is a relation the basis did not have.
    let mut candidates: Vec<MultivariatePolynomial<N, F>> = (0..matrix.num_rows())
        .filter_map(|index| {
            let column = matrix.matrix().row(index).leading_column()?;
            let monomial = matrix.columns()[column];
            if preprocessed.leading_monomials.contains(&monomial) {
                return None;
            }
            Some(matrix.row_polynomial(index))
        })
        .collect();

    // Echelon rows have distinct leading columns, so the leading monomials are distinct and this
    // is a total order on the candidates — which makes the output a function of the input.
    candidates.sort_by(|a, b| order.cmp(&b.leading_monomial(order), &a.leading_monomial(order)));
    stages.extraction = clock.lap();

    // The degree this batch worked at, and the degrees of what it produced. A relation below the
    // batch degree is a mutant: information arriving earlier than the schedule expected. Counted
    // unconditionally — one `degree()` call per candidate, and candidates are the rare row.
    let batch_degree = pairs.iter().map(|pair| pair.degree).max().unwrap_or(0);
    let mut min_candidate_degree = None;
    let mut max_candidate_degree = None;
    let mut candidates_below_batch_degree = 0;
    for candidate in &candidates {
        let degree = candidate.degree();
        min_candidate_degree = Some(min_candidate_degree.map_or(degree, |d: u64| d.min(degree)));
        max_candidate_degree = Some(max_candidate_degree.map_or(degree, |d: u64| d.max(degree)));
        if degree < batch_degree {
            candidates_below_batch_degree += 1;
        }
    }

    // One scan of the column vector, and only when asked for. The columns are the matrix's
    // monomials, so this is the degree the *matrix* reached rather than the degree it was selected
    // at — the two differ because reducer multiples can exceed the lcm.
    let max_column_degree = if options.profile_degrees {
        matrix
            .columns()
            .iter()
            .map(|monomial| monomial.degree())
            .max()
            .unwrap_or(0)
    } else {
        0
    };

    let statistics = BatchStatistics {
        pairs: pairs.len(),
        rows,
        reducer_rows,
        columns,
        elimination,
        candidates: candidates.len(),
        bytes_per_entry: F4Options::bytes_per_entry::<F>(),
        dense_buffer_bytes,
        stages,
        reducer_rows_reused: preprocessed.counts.reducer_rows_reused,
        divisor_queries: preprocessed.counts.divisor_queries,
        divisor_scan_steps: preprocessed.counts.divisor_scan_steps,
        divmask_tests: preprocessed.counts.divmask_tests,
        divmask_negative: preprocessed.counts.divmask_negative,
        divmask_decided: preprocessed.counts.divmask_decided,
        monomials_enqueued: preprocessed.counts.monomials_enqueued,
        max_pending_monomials: preprocessed.counts.max_pending_monomials,
        structured,
        // The unstructured path does not distinguish a pivot it found for free from one it worked
        // for, so this is zero there. Zero is the honest answer to "how many pivots did this
        // elimination know in advance", not a missing measurement.
        free_pivots: block.free_pivots,
        back_substituted_rows: block.back_substituted_rows,
        input_leading_monomials: preprocessed.leading_monomials.len(),
        batch_degree,
        min_candidate_degree,
        max_candidate_degree,
        candidates_below_batch_degree,
        max_column_degree,
    };

    Ok(BatchOutcome {
        candidates,
        statistics,
    })
}

#[cfg(test)]
mod tests {
    use super::reduce_batch;
    use crate::{
        grobner::{
            f4::{
                options::{F4Error, F4Options},
                symbolic::MonicBasis,
            },
            pairs::CriticalPair,
            s_polynomial,
        },
        poly::MonomialOrder,
        FiniteField, MultivariatePolynomial, One,
    };

    use crate::fields::{Zp13, Zp2147483647, Zp7};

    type F = Zp13;
    const VARS: [&str; 3] = ["x", "y", "z"];
    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    fn parse(s: &str) -> MultivariatePolynomial<3, F> {
        MultivariatePolynomial::parse(s, VARS).unwrap()
    }

    fn system(strings: &[&str]) -> Vec<MultivariatePolynomial<3, F>> {
        strings.iter().map(|s| parse(s)).collect()
    }

    /// The systems the row-form tests sweep, chosen to include ones whose batches carry reducible
    /// tails — a three-variable toy often has an echelon form that is already reduced, and a test
    /// built only on those would pass without exercising anything.
    const ROW_FORM_SYSTEMS: [&[&str]; 5] = [
        &["x^2 + y", "x^2 + z"],
        &["x^2 + y", "x^2 + z", "x^2 + y + z"],
        &["x^2*y + z", "y^2*z + x", "x*z^2 + y", "x*y*z - 1"],
        &["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
        &["x*y + z^2", "x*z + y^2", "y*z + x^2", "x + y + z"],
    ];

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

    /// The textbook case: f = x^2 + y and g = x^2 + z, whose S-polynomial is y - z.
    ///
    /// The batch's one new relation is that S-polynomial, made monic. Under every order the
    /// leading monomial is y or z depending on how the order ranks them, so the candidate is
    /// y - z or z - y; both are the same relation up to a unit, and both are monic.
    #[test]
    fn test_hand_verifiable_batch() {
        for order in ALL_ORDERS {
            let polynomials = system(&["x^2 + y", "x^2 + z"]);
            let basis = MonicBasis::new(&polynomials, order);
            let pairs = all_pairs(&polynomials, order);

            let outcome =
                reduce_batch(&basis, &pairs, order, &F4Options::default()).expect("within limits");

            assert_eq!(outcome.candidates.len(), 1, "{}", order.name());
            let candidate = &outcome.candidates[0];
            assert_eq!(candidate.leading_coefficient(order), F::ONE);
            // y - z up to sign, which is the S-polynomial of the pair up to a unit.
            let s = s_polynomial(&polynomials[0], &polynomials[1], order);
            let scaled = s.scale(&s.leading_coefficient(order).inverse());
            assert_eq!(*candidate, scaled, "{}", order.name());

            // Two rows, three columns, rank two, one zero row.
            assert_eq!(outcome.statistics.rows, 2, "{}", order.name());
            assert_eq!(outcome.statistics.columns, 3, "{}", order.name());
            assert_eq!(outcome.statistics.elimination.rank, 2, "{}", order.name());
        }
    }

    /// A batch whose rows are all dependent produces nothing, without failing.
    #[test]
    fn test_batch_that_reduces_entirely_to_zero() {
        for order in ALL_ORDERS {
            // x^2 - 1 and y^3 - 1 have relatively prime leading monomials, so their S-polynomial
            // reduces to zero modulo the two of them -- and the matrix must therefore find no new
            // pivot. The product criterion would skip this pair; reducing it anyway is the point.
            let polynomials = system(&["x^2 - 1", "y^3 - 1"]);
            let basis = MonicBasis::new(&polynomials, order);
            let pairs = all_pairs(&polynomials, order);

            let outcome =
                reduce_batch(&basis, &pairs, order, &F4Options::default()).expect("within limits");
            assert!(
                outcome.candidates.is_empty(),
                "{}: expected no new relation, got {:?}",
                order.name(),
                outcome.candidates
            );
            // Something did cancel: the rank is below the row count.
            assert!(
                outcome.statistics.elimination.zero_rows > 0,
                "{}: nothing reduced to zero, so nothing was learned either",
                order.name()
            );
        }
    }

    /// A candidate's leading monomial is never divisible by a basis element's.
    ///
    /// This is the consequence of the closure invariant, and the property that makes candidate
    /// extraction sound: a pivot whose leading monomial were top-reducible would be a relation the
    /// basis already implied, dressed up as a new element.
    #[test]
    fn test_candidates_are_not_top_reducible() {
        let systems: Vec<Vec<&str>> = vec![
            vec!["x^2 + y", "x^2 + z"],
            vec!["x^2 - y", "x*y - 1"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^2*y + x", "x*y^2 + y"],
            vec!["x^3 - 2*x*y", "x^2*y - 2*y^2 + x"],
            vec!["x*z - y^2", "x^3 - z^2"],
            vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
            vec!["x^2 + y^2 + z^2", "x*y + y*z"],
            vec!["x^2 + y + 1", "y^2 + z + 2", "z^2 + x + 3"],
        ];

        for order in ALL_ORDERS {
            for strings in &systems {
                let polynomials = system(strings);
                let basis = MonicBasis::new(&polynomials, order);
                let pairs = all_pairs(&polynomials, order);
                let outcome = reduce_batch(&basis, &pairs, order, &F4Options::default())
                    .expect("within limits");

                for candidate in &outcome.candidates {
                    let monomial = candidate.leading_monomial(order);
                    assert!(
                        !basis.is_top_reducible(&monomial),
                        "{:?} under {}: candidate {} leads with a reducible monomial",
                        strings,
                        order.name(),
                        candidate
                    );
                }
            }
        }
    }

    /// Every candidate lies in the ideal generated by the batch's input.
    ///
    /// A candidate is a combination of the matrix rows, and every row is a monomial multiple of a
    /// basis element, so it belongs to the ideal by construction. Checked here against the
    /// independent `normal_form`: reducing a candidate modulo a Gröbner basis of the input must
    /// give zero. The input is not yet a Gröbner basis, so `buchberger` supplies one.
    #[test]
    fn test_candidates_lie_in_the_ideal() {
        use crate::grobner::buchberger;

        let systems: Vec<Vec<&str>> = vec![
            vec!["x^2 + y", "x^2 + z"],
            vec!["x^2 - y", "x*y - 1"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^2*y + x", "x*y^2 + y"],
            vec!["x*z - y^2", "x^3 - z^2"],
            vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
        ];

        for order in ALL_ORDERS {
            for strings in &systems {
                let polynomials = system(strings);
                let reference = buchberger(&polynomials, order);
                let basis = MonicBasis::new(&polynomials, order);
                let pairs = all_pairs(&polynomials, order);
                let outcome = reduce_batch(&basis, &pairs, order, &F4Options::default())
                    .expect("within limits");

                for candidate in &outcome.candidates {
                    assert!(
                        candidate.normal_form(&reference, order).is_zero(),
                        "{:?} under {}: candidate {} is not in the ideal",
                        strings,
                        order.name(),
                        candidate
                    );
                }
            }
        }
    }

    /// The batch resolves its own pairs: each selected S-polynomial reduces to zero modulo the
    /// basis augmented with the batch's output.
    ///
    /// This is the correctness requirement for a batch. It does not ask the candidates to match
    /// what one-pair-at-a-time reduction would produce — a batch may use relations found from its
    /// other pairs — only that the pairs it took responsibility for are now resolved.
    #[test]
    fn test_batch_resolves_its_pairs() {
        let systems: Vec<Vec<&str>> = vec![
            vec!["x^2 + y", "x^2 + z"],
            vec!["x^2 - y", "x*y - 1"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^2*y + x", "x*y^2 + y"],
            vec!["x^3 - 2*x*y", "x^2*y - 2*y^2 + x"],
            vec!["x*z - y^2", "x^3 - z^2"],
            vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
            vec!["x^2 + y^2 + z^2", "x*y + y*z"],
            // Three generators sharing a leading monomial, so several pairs share an lcm.
            vec!["x^2 + y", "x^2 + z", "x^2 + y + z"],
        ];

        for order in ALL_ORDERS {
            for strings in &systems {
                let polynomials = system(strings);
                let basis = MonicBasis::new(&polynomials, order);
                let pairs = all_pairs(&polynomials, order);
                let outcome = reduce_batch(&basis, &pairs, order, &F4Options::default())
                    .expect("within limits");

                let mut augmented = polynomials.clone();
                augmented.extend(outcome.candidates.iter().cloned());

                for pair in &pairs {
                    let s = s_polynomial(&polynomials[pair.left], &polynomials[pair.right], order);
                    assert!(
                        s.normal_form(&augmented, order).is_zero(),
                        "{:?} under {}: S({}, {}) is not resolved by the batch",
                        strings,
                        order.name(),
                        polynomials[pair.left],
                        polynomials[pair.right]
                    );
                }
            }
        }
    }

    /// A batch of several pairs resolves all of them, including linearly dependent rows.
    ///
    /// Three generators with the same leading monomial give three pairs whose six matrix rows span
    /// only a two-dimensional space of new relations, so the elimination has dependencies to find.
    #[test]
    fn test_batch_with_dependent_rows() {
        for order in ALL_ORDERS {
            let polynomials = system(&["x^2 + y", "x^2 + z", "x^2 + y + z"]);
            let basis = MonicBasis::new(&polynomials, order);
            let pairs = all_pairs(&polynomials, order);
            let outcome =
                reduce_batch(&basis, &pairs, order, &F4Options::default()).expect("within limits");

            assert_eq!(outcome.statistics.pairs, 3, "{}", order.name());
            assert_eq!(outcome.statistics.rows, 6, "{}", order.name());
            assert!(
                outcome.statistics.elimination.zero_rows > 0,
                "{}: six rows over three columns must be dependent",
                order.name()
            );
            // Candidates have distinct leading monomials, which echelon form guarantees.
            let mut leads: Vec<_> = outcome
                .candidates
                .iter()
                .map(|p| p.leading_monomial(order))
                .collect();
            let before = leads.len();
            leads.sort();
            leads.dedup();
            assert_eq!(leads.len(), before, "{}", order.name());
        }
    }

    /// Cancellation that depends on the characteristic is found over the field in question.
    ///
    /// The batch reduces `x^2 + 8y` against `x^2 + y`. Over GF(7) the coefficient 8 is 1, so the
    /// two rows are identical, the elimination finds a dependency, and there is no new relation.
    /// Over GF(2^31 - 1) they differ and the S-polynomial `7y` is a new relation. The same batch,
    /// the same code, two different answers — which is what a single-field test would not catch.
    #[test]
    fn test_characteristic_dependent_cancellation() {
        use crate::Monomial;
        let order = MonomialOrder::Lexicographic;

        fn outcome_over<G: FiniteField>(order: MonomialOrder) -> (usize, usize) {
            let x_squared = Monomial::<3>::new(&[2, 0, 0]);
            let y = Monomial::<3>::new(&[0, 1, 0]);
            let polynomials: Vec<MultivariatePolynomial<3, G>> = vec![
                MultivariatePolynomial::new(&[(x_squared, G::ONE), (y, G::new(8))]),
                MultivariatePolynomial::new(&[(x_squared, G::ONE), (y, G::ONE)]),
            ];
            let basis = MonicBasis::new(&polynomials, order);
            let pairs = vec![CriticalPair::new(&polynomials, 0, 1, order)];
            let outcome =
                reduce_batch(&basis, &pairs, order, &F4Options::default()).expect("within limits");
            (
                outcome.candidates.len(),
                outcome.statistics.elimination.zero_rows,
            )
        }

        assert_eq!(
            outcome_over::<Zp7>(order),
            (0, 1),
            "over GF(7) the rows are identical"
        );
        assert_eq!(
            outcome_over::<Zp2147483647>(order),
            (1, 0),
            "over GF(2^31 - 1) they are independent"
        );
    }

    /// An empty batch produces nothing and costs nothing.
    #[test]
    fn test_empty_batch() {
        let order = MonomialOrder::Lexicographic;
        let basis = MonicBasis::new(&system(&["x^2 + y"]), order);
        let outcome =
            reduce_batch(&basis, &[], order, &F4Options::default()).expect("within limits");
        assert!(outcome.candidates.is_empty());
        assert_eq!(outcome.statistics.rows, 0);
        assert_eq!(outcome.statistics.columns, 0);
    }

    /// Reduction is deterministic: the same batch gives the same candidates in the same order.
    #[test]
    fn test_reduction_is_deterministic() {
        for order in ALL_ORDERS {
            let polynomials = system(&["x^2*y + z", "y^2*z + x", "x*z^2 + y", "x*y*z - 1"]);
            let basis = MonicBasis::new(&polynomials, order);
            let pairs = all_pairs(&polynomials, order);

            let first = reduce_batch(&basis, &pairs, order, &F4Options::default()).unwrap();
            for _ in 0..8 {
                assert_eq!(
                    reduce_batch(&basis, &pairs, order, &F4Options::default()).unwrap(),
                    first,
                    "{}",
                    order.name()
                );
            }
        }
    }

    /// Candidates come out sorted descending by leading monomial.
    #[test]
    fn test_candidates_are_sorted() {
        for order in ALL_ORDERS {
            let polynomials = system(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"]);
            let basis = MonicBasis::new(&polynomials, order);
            let pairs = all_pairs(&polynomials, order);
            let outcome = reduce_batch(&basis, &pairs, order, &F4Options::default()).unwrap();

            for window in outcome.candidates.windows(2) {
                assert_eq!(
                    order.cmp(
                        &window[0].leading_monomial(order),
                        &window[1].leading_monomial(order)
                    ),
                    std::cmp::Ordering::Greater,
                    "{}: candidates are not sorted",
                    order.name()
                );
            }
        }
    }

    /// Each resource limit is reported as its own error, and the basis is untouched.
    #[test]
    fn test_resource_limits_are_reported() {
        let order = MonomialOrder::Lexicographic;
        let polynomials = system(&["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"]);
        let basis = MonicBasis::new(&polynomials, order);
        let pairs = all_pairs(&polynomials, order);

        // A row limit of one cannot hold even a single pair's two halves.
        assert!(matches!(
            reduce_batch(
                &basis,
                &pairs,
                order,
                &F4Options {
                    max_matrix_rows: 1,
                    ..F4Options::default()
                }
            ),
            Err(F4Error::TooManyRows { limit: 1, .. })
        ));

        assert!(matches!(
            reduce_batch(
                &basis,
                &pairs,
                order,
                &F4Options {
                    max_matrix_columns: 1,
                    ..F4Options::default()
                }
            ),
            Err(F4Error::TooManyColumns { limit: 1, .. })
        ));

        assert!(matches!(
            reduce_batch(
                &basis,
                &pairs,
                order,
                &F4Options {
                    max_live_nonzeros: 1,
                    ..F4Options::default()
                }
            ),
            Err(F4Error::TooManyNonzeros { limit: 1, .. })
        ));

        // Generous limits succeed on the same input, so the failures are the limits and not the
        // batch.
        assert!(reduce_batch(&basis, &pairs, order, &F4Options::default()).is_ok());
    }

    /// `reduce_batch_rows` cannot change which rows become candidates.
    ///
    /// Extraction keeps the rows whose leading column is not already a leading monomial of an
    /// input row, and back-substitution never changes a row's leading column — so the selection is
    /// the same either way. #477 called that an argument rather than a test; this is the test. What
    /// the flag *is* allowed to change is each candidate's tail, and the final assertion pins that
    /// the sweep actually reaches a case where it does, so the agreement above is not vacuous.
    #[test]
    fn test_the_row_form_does_not_change_candidate_selection() {
        let echelon = F4Options {
            reduce_batch_rows: false,
            ..F4Options::default()
        };
        let reduced = F4Options {
            reduce_batch_rows: true,
            ..F4Options::default()
        };

        let mut tails_differed = 0;
        for strings in ROW_FORM_SYSTEMS {
            for order in ALL_ORDERS {
                let polynomials = system(strings);
                let basis = MonicBasis::new(&polynomials, order);
                let pairs = all_pairs(&polynomials, order);

                let left = reduce_batch(&basis, &pairs, order, &echelon).expect("within limits");
                let right = reduce_batch(&basis, &pairs, order, &reduced).expect("within limits");

                let what = format!("{:?} under {}", strings, order.name());
                assert_eq!(
                    left.candidates.len(),
                    right.candidates.len(),
                    "candidate count: {}",
                    what
                );
                let leads = |outcome: &super::BatchOutcome<3, F>| -> Vec<_> {
                    outcome
                        .candidates
                        .iter()
                        .map(|c| c.leading_monomial(order))
                        .collect()
                };
                assert_eq!(leads(&left), leads(&right), "leading monomials: {}", what);

                // The statistic says which route ran, so a flag that silently did nothing would
                // make this test pass while measuring the same thing twice.
                assert_eq!(left.statistics.back_substituted_rows, None, "{}", what);
                assert!(
                    right.statistics.back_substituted_rows.is_some(),
                    "the reduced route did not report a back-substitution: {}",
                    what
                );

                if left.candidates != right.candidates {
                    tails_differed += 1;
                }
            }
        }
        assert!(
            tails_differed > 0,
            "no system in the sweep produced a candidate whose tail the reduced form changed, so \
             the agreement above is vacuous and the fixtures need to be harder"
        );
    }

    /// The reduced route's candidates are in normal form with respect to the batch's own pivots:
    /// no candidate's tail holds a monomial another candidate leads with.
    ///
    /// This is the property #477 wants and the one the echelon route does not have. Asserted
    /// against the echelon route on the same input, so a system where both happen to be reduced
    /// cannot make it look established.
    #[test]
    fn test_the_reduced_route_leaves_no_candidate_reducible_by_another() {
        let reduced = F4Options {
            reduce_batch_rows: true,
            ..F4Options::default()
        };

        for strings in ROW_FORM_SYSTEMS {
            for order in ALL_ORDERS {
                let polynomials = system(strings);
                let basis = MonicBasis::new(&polynomials, order);
                let pairs = all_pairs(&polynomials, order);
                let outcome = reduce_batch(&basis, &pairs, order, &reduced).expect("within limits");

                let leads: Vec<_> = outcome
                    .candidates
                    .iter()
                    .map(|c| c.leading_monomial(order))
                    .collect();
                for (index, candidate) in outcome.candidates.iter().enumerate() {
                    for monomial in candidate.terms().keys() {
                        if *monomial == leads[index] {
                            continue;
                        }
                        for (other, lead) in leads.iter().enumerate() {
                            if other == index {
                                continue;
                            }
                            assert_ne!(
                                monomial, lead,
                                "candidate {} carries candidate {}'s leading monomial: {:?} under {}",
                                index,
                                other,
                                strings,
                                order.name()
                            );
                        }
                    }
                }
            }
        }
    }
}
