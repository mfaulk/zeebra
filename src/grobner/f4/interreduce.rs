//! Final interreduction as one Macaulay matrix, rather than as one division per basis element.
//!
//! # Why this exists
//!
//! `docs/research/groebner-jl-gap.md` §3 measured Zeebra's final interreduction at **13 871x**
//! Groebner.jl's on `mq-random-10`, where the next worst stage is 97.1x. A spread of 8x among the
//! other three stages is an implementation constant; a 1 400x outlier among them is not an
//! implementation of the same thing. §4 says what the difference is:
//!
//! > It is not a faster interreduction. **It is linear algebra where Zeebra does division.**
//!
//! Groebner.jl's `f4_autoreduce!` builds one matrix whose rows are the non-redundant basis
//! elements, lets symbolic preprocessing supply the reducers those rows need, marks every column as
//! an unknown pivot so that all of them are eliminated against, and reduces once —
//! **250 x 604, 1.74 ms, 2.0% of its whole run.** Zeebra's [`reduce_grobner_basis_until`] instead
//! performs one `normal_form` per element, each with its own intermediate growth, and spends four
//! fifths of the computation there.
//!
//! Every component of the replacement already existed: [`MacaulayMatrix`] builds the matrix,
//! [`symbolic`](super::symbolic) finds the reducers, [`reduced_row_echelon_tracked`] eliminates, and
//! `minimize_grobner_basis` produces the row set. What was missing was the assembly.
//!
//! # Why the answer cannot change
//!
//! `buchberger.rs` already writes the argument out: a reduced Gröbner basis is **determined by its
//! leading monomials**, so the route to it cannot change it. Concretely, for a minimized basis
//! `g_1..g_n`:
//!
//! - The seed rows have distinct leading monomials, so each is a pivot —
//!   [`interreduction_rows`](super::symbolic::interreduction_rows) proves this from minimality.
//! - The closure gives every *reducible* monomial in the matrix a row that leads with it, so the
//!   pivot columns are exactly the reducible monomials.
//! - Reduced row echelon form leaves one nonzero per pivot column. So the row led by `lm(g_i)` has
//!   no monomial divisible by any `lm(g_j)` — which is the defining property of the reduced basis
//!   element with that leading monomial, and there is only one such polynomial.
//!
//! So this is a different computation of the same unique object, and the test that matters is exact
//! equality against the division route rather than a tolerance.

use crate::{
    grobner::buchberger::InterreductionStopped,
    grobner::f4::{
        macaulay::{BuildBudgetExceeded, MacaulayMatrix},
        symbolic::{interreduction_rows, MonicBasis, ReducerCache, RowBudgetExceeded},
        ReducerSelection,
    },
    linalg::sparse::reduced_row_echelon_tracked,
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

/// Why a matrix interreduction refused to run.
///
/// The stage is not exempt from the budgets the batch loop obeys. A basis of a few hundred
/// elements whose closure is wide can need a matrix as large as any batch's, and a stage that
/// ignored the budgets would be a way to exceed them by waiting until the end of the computation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum MatrixInterreductionRefused {
    /// The closure needed more rows than allowed.
    Rows { limit: usize },
    /// The matrix needed more distinct monomials than allowed.
    Columns { limit: usize },
    /// The matrix needed more nonzero entries than allowed **at construction**.
    Nonzeros { nonzeros: usize },
    /// Elimination's fill-in took more entries live at once than allowed.
    ///
    /// Separate from [`MatrixInterreductionRefused::Nonzeros`] because the two are different
    /// quantities against the same limit, and #536 is the gap between them: on `katsura-11` the
    /// matrix is built at 11 311 802 entries — inside the 20 000 000-entry allowance — and reduced
    /// at a high-water of **103 865 277**, 5.19x the allowance. A refusal that reported only
    /// "nonzeros" would hide which of the two crossed, which is the mistake #322 is a record of.
    LiveEntries { nonzeros: usize },
}

/// Why a matrix interreduction did not produce a basis.
///
/// # Why `Refused` hands the basis back
///
/// So the caller can fall back to the division route **without having cloned it**. #304/#437 spent
/// a milestone getting final interreduction down to one live copy of the basis — "one copy reaches
/// it instead of three" — and a fallback implemented by cloning the input up front would hold two
/// for the whole matrix pass, reinstating the cost on the path that is supposed to be the fast one.
///
/// # Why `Refused` also carries a report
///
/// Because a refusal on the elimination happens **after** the matrix exists, so its shape is known
/// and is the most useful thing the record can hold: "fell back, and the matrix it would have
/// reduced was 104 403 x 105 427 at 11 311 802 entries" says why, where a bare `fell_back` says
/// only that it happened. The earlier refusals have no shape to report and leave the report at its
/// default, which is the honest encoding of not knowing.
pub(crate) enum MatrixInterreductionAborted<const N: usize, F: FiniteField> {
    /// A budget refused the matrix, with the basis returned for the fallback and whatever shape
    /// had been established when it was refused.
    Refused(
        MatrixInterreductionRefused,
        Vec<MultivariatePolynomial<N, F>>,
        MatrixInterreductionReport,
    ),

    /// The caller's stop predicate fired. The basis is **not** returned: `F4Error`'s contract is
    /// that a successful return is a complete reduced basis, and a partially interreduced one
    /// handed back is exactly the confusion that contract exists to prevent.
    Stopped(InterreductionStopped),
}

/// What a matrix interreduction did, for attribution against the division route.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct MatrixInterreductionReport {
    /// Rows in the matrix: the basis elements plus the reducer multiples the closure added.
    pub rows: usize,
    /// Columns, i.e. distinct monomials in the closure. Groebner.jl's was 604 on `mq-random-10`.
    pub columns: usize,
    /// Nonzero entries at construction.
    pub nonzeros: usize,
    /// Nonzero entries live at once at elimination's high-water mark.
    ///
    /// The quantity that actually binds: reduced row echelon form clears every pivot column out of
    /// every row holding one, and the entries that takes are not a function of the matrix's shape
    /// or of its construction density. Zero on a basis too small to need a matrix.
    pub peak_nonzeros: usize,
    /// Entries the rows' buffers were *allocated* for at that high-water, which is the figure the
    /// machine pays. See [`crate::linalg::sparse::EntryBufferPeak`].
    pub peak_entry_capacity: usize,
    /// Elements in the minimized basis, which is how many rows were seeds rather than reducers.
    pub elements: usize,
}

/// Interreduce a minimized basis through one Macaulay matrix.
///
/// `minimal` must be **minimized** — monic, deduplicated, and with no leading monomial dividing
/// another — which is what `minimize_grobner_basis` produces and what the pivot argument in the
/// module documentation requires. It is also expected sorted ascending by leading monomial, as the
/// division route sorts it; the output is returned descending, matching
/// [`reduce_grobner_basis_until`]'s canonical order.
///
/// # Errors
/// [`MatrixInterreductionRefused`] if any budget would be exceeded. Nothing is partially written:
/// the budgets are checked while the closure and the matrix are built, not after.
pub(crate) fn interreduce_by_matrix<const N: usize, F: FiniteField>(
    minimal: Vec<MultivariatePolynomial<N, F>>,
    order: MonomialOrder,
    max_rows: usize,
    max_columns: usize,
    max_nonzeros: usize,
    mut should_stop: impl FnMut() -> bool,
) -> Result<
    (
        Vec<MultivariatePolynomial<N, F>>,
        MatrixInterreductionReport,
    ),
    MatrixInterreductionAborted<N, F>,
> {
    // One element is already reduced against the empty rest of the basis, and zero elements have
    // nothing to reduce. Neither needs a matrix, and `MonicBasis::new` would reject a zero
    // element anyway.
    if minimal.len() < 2 {
        let report = MatrixInterreductionReport {
            elements: minimal.len(),
            ..Default::default()
        };
        return Ok((minimal, report));
    }

    // # The stop, and the granularity it loses — which is the point of recording it
    //
    // #395 exists because this stage ran with no clock consulted in it at all, so a 120-second
    // budget returned at ten minutes. The division route fixed that by asking before each of the
    // 247 elements. **A matrix pass cannot offer that granularity**: the closure, the construction
    // and the elimination are each one indivisible call, so the honest best is to ask between
    // them — four checks here against the division route's one-per-element.
    //
    // That is a real weakening and is stated rather than hidden. What it removes is the unbounded
    // case, the same thing #395 removed; what it does not remove is overrunning by however long
    // one elimination still needed. The budgets below bound the *size* of that elimination, which
    // is the other half of the protection and the half a clock cannot give.
    macro_rules! stop_if_asked {
        ($elements:expr) => {
            if should_stop() {
                return Err(MatrixInterreductionAborted::Stopped(
                    InterreductionStopped {
                        elements_reduced: 0,
                        elements: $elements,
                    },
                ));
            }
        };
    }

    stop_if_asked!(minimal.len());

    let basis = MonicBasis::new(&minimal, order);
    let elements = basis.len();

    // The leading monomials of the seed rows, which is what the extraction below selects on. Taken
    // from the basis rather than recomputed from the polynomials so that it agrees with the set
    // `interreduction_rows` seeded `covered` with, by construction.
    let leading: Vec<Monomial<N>> = (0..elements)
        .map(|index| basis.element(index).leading_monomial)
        .collect();

    let preprocessed = interreduction_rows(
        &basis,
        max_rows,
        ReducerSelection::FirstApplicable,
        &mut ReducerCache::disabled(),
    )
    .map_err(|RowBudgetExceeded { limit }| {
        MatrixInterreductionAborted::Refused(
            MatrixInterreductionRefused::Rows { limit },
            minimal.clone(),
            MatrixInterreductionReport {
                elements,
                ..Default::default()
            },
        )
    })?;

    stop_if_asked!(elements);

    let mut matrix =
        MacaulayMatrix::build_within(&basis, &preprocessed, order, max_columns, max_nonzeros)
            .map_err(|exceeded| {
                let reason = match exceeded {
                    BuildBudgetExceeded::Columns { limit } => {
                        MatrixInterreductionRefused::Columns { limit }
                    }
                    BuildBudgetExceeded::Nonzeros { nonzeros, .. } => {
                        MatrixInterreductionRefused::Nonzeros { nonzeros }
                    }
                };
                MatrixInterreductionAborted::Refused(
                    reason,
                    minimal.clone(),
                    MatrixInterreductionReport {
                        elements,
                        ..Default::default()
                    },
                )
            })?;

    stop_if_asked!(elements);

    let mut report = MatrixInterreductionReport {
        rows: matrix.num_rows(),
        columns: matrix.num_columns(),
        nonzeros: matrix.matrix().nonzeros(),
        peak_nonzeros: 0,
        peak_entry_capacity: 0,
        elements,
    };

    // **Reduced** row echelon and not plain echelon, and this is the whole point. Plain echelon
    // leaves a pivot row carrying other pivots' columns, which is a basis element still divisible
    // by another's leading monomial — i.e. not interreduced. The back-substitution pass is what
    // performs every division the loop this replaces performed, all at once.
    // Last chance before the one call that cannot be interrupted. The row and entry budgets above
    // are what bound how long it can run.
    stop_if_asked!(elements);

    // # The budget that binds, and why construction's is not it (#536)
    //
    // `max_nonzeros` bounded the entries the matrix was **built** with, and that is the smaller
    // number by a factor this stage does not control: back-substitution clears every pivot column
    // out of every row that holds one, so the live entry count during this call is a function of
    // the fill-in and not of the shape. Measured on `katsura-11` under grevlex, a 104 403 x 105 427
    // matrix is built at 11 311 802 entries — inside the default 20 000 000 allowance, which is why
    // #507 found every budget satisfied — and reduced at a high-water of 103 865 277 live entries,
    // **5.19x the allowance**, in a run peaking at 13 144.3 MB against the division route's
    // 533.0 MB.
    // `docs/research/f4-resource-scaling.md` §11 has the attribution.
    //
    // So the same allowance is applied here, which is what `F4Options::max_live_nonzeros` already
    // documents itself as doing ("in construction and in elimination") and what the batch loop does
    // through `reduced_row_echelon_within` since #477 — whose own doc comment names this stage as
    // the one still budgeting construction instead. The basis is handed back on a crossing, so the
    // caller falls back to the division route having paid the ceiling rather than the blow-up.
    match reduced_row_echelon_tracked(matrix.matrix_mut(), max_nonzeros) {
        Ok((statistics, buffers)) => {
            report.peak_nonzeros = statistics.peak_nonzeros;
            report.peak_entry_capacity = buffers.capacity;
        }
        Err(nonzeros) => {
            // The partially reduced matrix is dropped on the way out, so the fallback starts from
            // the basis alone. `minimal` is still owned here — `basis` borrowed it and is not read
            // past construction — so the hand-back still costs no clone.
            drop(matrix);
            return Err(MatrixInterreductionAborted::Refused(
                MatrixInterreductionRefused::LiveEntries { nonzeros },
                minimal,
                report,
            ));
        }
    }

    // The row led by `lm(g_i)` is the reduced element with that leading monomial. Rows led by
    // anything else are reducer multiples, and rows that cancelled to zero have no leading column.
    let wanted: std::collections::HashSet<Monomial<N>> = leading.into_iter().collect();
    let mut reduced: Vec<MultivariatePolynomial<N, F>> = (0..matrix.num_rows())
        .filter_map(|index| {
            let column = matrix.matrix().row(index).leading_column()?;
            let monomial = matrix.columns()[column];
            if !wanted.contains(&monomial) {
                return None;
            }
            Some(matrix.row_polynomial(index))
        })
        .collect();

    debug_assert_eq!(
        reduced.len(),
        elements,
        "every minimized element's leading monomial is a pivot, so every element is recovered"
    );

    // Descending by leading monomial, which is what `reduce_grobner_basis_until` returns. The
    // leading monomials are distinct, so this is a total order and the sequence is unique.
    reduced.sort_by(|a, b| order.cmp(&b.leading_monomial(order), &a.leading_monomial(order)));
    Ok((reduced, report))
}

#[cfg(test)]
mod tests {
    use super::{interreduce_by_matrix, MatrixInterreductionAborted, MatrixInterreductionRefused};
    use crate::{
        fields::{Zp13, Zp2147483647},
        grobner::{
            benchmark_systems::{cyclic, katsura},
            buchberger::{minimal_basis_for_interreduction, reduce_grobner_basis},
            f4::{f4_with_options, trace_batches},
            F4Options,
        },
        poly::MonomialOrder,
        FiniteField, MultivariatePolynomial,
    };

    const ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    /// The minimized basis the interreduction stage actually receives: F4's basis **before** the
    /// stage runs, taken from the last traced batch as `benches/f4_stages.rs` does.
    ///
    /// Not `f4_with_options`'s return value, which is already interreduced — a reduced basis has
    /// almost nothing left to close over, so the matrix built from it has no fill-in and could not
    /// exercise an elimination budget.
    fn before_interreduction<const N: usize, F: FiniteField>(
        label: &str,
        system: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) -> Vec<MultivariatePolynomial<N, F>> {
        let (_, _, trace) = trace_batches(
            system,
            order,
            &F4Options {
                interreduce_by_matrix: false,
                ..F4Options::default()
            },
        )
        .unwrap_or_else(|error| panic!("{label} completes by the division route: {error}"));
        let last = trace
            .batches()
            .last()
            .unwrap_or_else(|| panic!("{label} reduces at least one batch"));
        let basis: Vec<MultivariatePolynomial<N, F>> = (0..last.basis.len())
            .map(|index| MultivariatePolynomial::new(&last.basis.element(index).terms))
            .collect();
        minimal_basis_for_interreduction(basis, order)
    }

    /// Both routes over the same basis, asserted equal element for element.
    fn assert_routes_agree<const N: usize, F: FiniteField>(
        label: &str,
        system: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) {
        // An F4 basis before interreduction, which is the input the stage actually receives.
        let Ok((basis, _)) = f4_with_options(
            system,
            order,
            &F4Options {
                interreduce_by_matrix: false,
                ..F4Options::default()
            },
        ) else {
            return;
        };

        let minimal = minimal_basis_for_interreduction(basis.clone(), order);
        let by_division = reduce_grobner_basis(basis, order);
        let (by_matrix, report) =
            interreduce_by_matrix(minimal, order, usize::MAX, usize::MAX, usize::MAX, || false)
                .unwrap_or_else(|_| panic!("an unbounded interreduction cannot abort"));

        assert_eq!(
            by_matrix, by_division,
            "{label} under {order:?}: the matrix route must reproduce the division route exactly"
        );
        assert_eq!(
            report.elements,
            by_division.len(),
            "{label}: every minimized element is recovered"
        );
        if report.elements >= 2 {
            assert!(report.rows >= report.elements, "the seeds are rows too");
            assert!(report.columns > 0);
        }
    }

    /// The two routes agree on the classical families, over three orders and two fields.
    #[test]
    fn test_the_matrix_route_reproduces_the_division_route() {
        for order in ORDERS {
            assert_routes_agree("katsura-4", &katsura::<4, Zp2147483647>(), order);
            assert_routes_agree("katsura-5", &katsura::<5, Zp2147483647>(), order);
            assert_routes_agree("cyclic-4", &cyclic::<4, Zp2147483647>(), order);
            assert_routes_agree("cyclic-5", &cyclic::<5, Zp2147483647>(), order);
            assert_routes_agree("katsura-4/13", &katsura::<4, Zp13>(), order);
        }
    }

    /// A one-element basis is already reduced, and needs no matrix at all.
    #[test]
    fn test_a_single_element_is_returned_unchanged() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let p = MultivariatePolynomial::<2, Zp13>::parse("x^2 + y", ["x", "y"]).expect("parses");
        let (reduced, report) = interreduce_by_matrix(
            vec![p.clone()],
            order,
            usize::MAX,
            usize::MAX,
            usize::MAX,
            || false,
        )
        .unwrap_or_else(|_| panic!("cannot abort"));
        assert_eq!(reduced, vec![p]);
        assert_eq!(report.elements, 1);
        assert_eq!(report.rows, 0, "no matrix was built");
    }

    /// The budgets are honored, and each names the resource it refused on. A stage that ignored
    /// them would be a way to exceed the computation's budgets by waiting until the end.
    #[test]
    fn test_each_budget_refuses_and_names_itself() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system = katsura::<5, Zp2147483647>();
        let (basis, _) = f4_with_options(
            &system,
            order,
            &F4Options {
                interreduce_by_matrix: false,
                ..F4Options::default()
            },
        )
        .expect("katsura-5 completes");
        let minimal = minimal_basis_for_interreduction(basis, order);

        // Each refusal also hands the basis back, which is what lets the caller fall back
        // without having cloned it.
        match interreduce_by_matrix(minimal.clone(), order, 1, usize::MAX, usize::MAX, || false) {
            Err(MatrixInterreductionAborted::Refused(
                MatrixInterreductionRefused::Rows { limit: 1 },
                returned,
                refused,
            )) => {
                assert_eq!(returned, minimal, "the basis comes back for the fallback");
                assert_eq!(
                    refused.rows, 0,
                    "no matrix was built, so there is none to report"
                );
            }
            _ => panic!("expected a row refusal"),
        }
        match interreduce_by_matrix(minimal.clone(), order, usize::MAX, 1, usize::MAX, || false) {
            Err(MatrixInterreductionAborted::Refused(
                MatrixInterreductionRefused::Columns { limit: 1 },
                returned,
                refused,
            )) => {
                assert_eq!(returned, minimal, "the basis comes back for the fallback");
                assert_eq!(refused.columns, 0);
            }
            _ => panic!("expected a column refusal"),
        }
        match interreduce_by_matrix(minimal.clone(), order, usize::MAX, usize::MAX, 1, || false) {
            Err(MatrixInterreductionAborted::Refused(
                MatrixInterreductionRefused::Nonzeros { nonzeros },
                returned,
                refused,
            )) => {
                assert!(nonzeros > 1, "the refusal reports what was needed");
                assert_eq!(returned, minimal);
                assert_eq!(refused.nonzeros, 0, "construction did not finish");
            }
            _ => panic!("expected a nonzero refusal"),
        }
    }

    /// The live-entry allowance covers elimination, not only construction — #536.
    ///
    /// An allowance that admits the matrix as **built** but not as **reduced** must refuse and hand
    /// the basis back, rather than running the elimination it cannot afford. The figures are taken
    /// from an unbounded run of the same input rather than written down, so the test asserts the
    /// relation and not a constant.
    #[test]
    fn test_the_allowance_covers_the_elimination_and_not_only_the_construction() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let minimal = before_interreduction("katsura-6", &katsura::<6, Zp2147483647>(), order);

        let (_, report) = interreduce_by_matrix(
            minimal.clone(),
            order,
            usize::MAX,
            usize::MAX,
            usize::MAX,
            || false,
        )
        .unwrap_or_else(|_| panic!("an unbounded interreduction cannot abort"));
        assert!(
            report.peak_nonzeros > report.nonzeros,
            "the premise of this test is that elimination fills the matrix in: built {}, peak {}",
            report.nonzeros,
            report.peak_nonzeros
        );

        // The allowance the defect lived in: large enough to build the matrix, too small to reduce
        // it. The old budget saw only the first of those and ran anyway.
        let allowance = report.peak_nonzeros - 1;
        assert!(
            allowance >= report.nonzeros,
            "this allowance has to admit the construction, or the refusal would be the old one"
        );
        match interreduce_by_matrix(
            minimal.clone(),
            order,
            usize::MAX,
            usize::MAX,
            allowance,
            || false,
        ) {
            Err(MatrixInterreductionAborted::Refused(
                MatrixInterreductionRefused::LiveEntries { nonzeros },
                returned,
                refused,
            )) => {
                assert!(
                    nonzeros > allowance,
                    "the refusal reports the count that crossed {allowance}, got {nonzeros}"
                );
                assert_eq!(returned, minimal, "the basis comes back for the fallback");
                // The matrix existed before it was refused, so the record describes it.
                assert_eq!(
                    (refused.rows, refused.columns, refused.nonzeros),
                    (report.rows, report.columns, report.nonzeros),
                    "a refusal on the elimination reports the shape it refused"
                );
            }
            other => panic!(
                "expected a live-entry refusal; got {}",
                match other {
                    Ok((_, report)) => format!(
                        "a completed pass at {} live entries against an allowance of {}",
                        report.peak_nonzeros, allowance
                    ),
                    Err(MatrixInterreductionAborted::Refused(reason, _, _)) =>
                        format!("{reason:?}"),
                    Err(MatrixInterreductionAborted::Stopped(_)) => "a stop".to_string(),
                }
            ),
        }

        // And an allowance of exactly the peak runs, so the budget is not merely conservative.
        let (reduced, report) = interreduce_by_matrix(
            minimal.clone(),
            order,
            usize::MAX,
            usize::MAX,
            report.peak_nonzeros,
            || false,
        )
        .unwrap_or_else(|_| panic!("an allowance of exactly the peak must suffice"));
        assert_eq!(reduced, reduce_grobner_basis(minimal, order));
        assert!(report.peak_nonzeros > 0);
    }

    /// The stop predicate is honored, which #395 is the reason for and which #461 item 4 asked
    /// for. An always-stopping predicate must abort before any work rather than after it.
    #[test]
    fn test_an_always_stopping_predicate_aborts_the_matrix_route() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system = katsura::<5, Zp2147483647>();
        let (basis, _) = f4_with_options(
            &system,
            order,
            &F4Options {
                interreduce_by_matrix: false,
                ..F4Options::default()
            },
        )
        .expect("katsura-5 completes");
        let minimal = minimal_basis_for_interreduction(basis, order);
        let elements = minimal.len();

        match interreduce_by_matrix(minimal, order, usize::MAX, usize::MAX, usize::MAX, || true) {
            Err(MatrixInterreductionAborted::Stopped(stopped)) => {
                assert_eq!(stopped.elements, elements);
                assert_eq!(
                    stopped.elements_reduced, 0,
                    "a matrix pass is all-or-nothing, so no element is partially reduced"
                );
            }
            _ => panic!("an always-stopping predicate must abort"),
        }
    }

    /// And a predicate that fires only after the closure still aborts, which is what makes the
    /// four check points worth having rather than one.
    #[test]
    fn test_a_predicate_that_fires_later_still_aborts() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system = katsura::<5, Zp2147483647>();
        let (basis, _) = f4_with_options(
            &system,
            order,
            &F4Options {
                interreduce_by_matrix: false,
                ..F4Options::default()
            },
        )
        .expect("katsura-5 completes");
        let minimal = minimal_basis_for_interreduction(basis, order);

        let mut calls = 0;
        let result =
            interreduce_by_matrix(minimal, order, usize::MAX, usize::MAX, usize::MAX, || {
                calls += 1;
                calls > 1
            });
        assert!(
            matches!(result, Err(MatrixInterreductionAborted::Stopped(_))),
            "a predicate firing at the second check point must still abort"
        );
    }
}
