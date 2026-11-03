//! FGLM: a zero-dimensional Gröbner basis under one order, converted to the lex basis.
//!
//! Monomials are visited in increasing lex order. Each one's residue class is either independent
//! of the target standard monomials accepted so far — and so becomes one of them — or dependent,
//! and the dependence is a polynomial in the ideal whose lex leading monomial is that monomial.
//! The dependent ones are the lex Gröbner basis.
//!
//! **The output needs no interreduction.** Each relation is monic, its leading monomial is the
//! candidate that produced it, and on completion the accepted monomials are exactly the lex
//! standard monomials of the ideal while the emitted leading monomials generate the lex initial
//! ideal. A standard monomial is by definition divisible by no element of the initial ideal, so no
//! non-leading term of any relation is divisible by any relation's leading monomial — which is
//! precisely what being reduced means. See `docs/MILESTONE-FGLM-SOLVING.md` §5.5.
//!
//! # References
//! * Faugère, Gianni, Lazard, Mora (1993), *Efficient Computation of Zero-dimensional Gröbner
//!   Bases by Change of Ordering*, J. Symbolic Computation 16(4), 329–344.

use std::{
    cmp::{Ordering, Reverse},
    collections::{BinaryHeap, HashSet},
};

use crate::{
    grobner::{
        fglm::{
            incremental_span::{Dependence, IncrementalSpan},
            statistics::FglmStatistics,
            FglmError, FglmOptions, QuotientAlgebra,
        },
        s_polynomial,
    },
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

/// The target order. Not a parameter: the back-substitution that consumes the result is specific
/// to lex, so a `target_order` argument would be a promise this module does not keep.
const TARGET: MonomialOrder = MonomialOrder::Lexicographic;

/// A monomial ordered by the target order, so a `BinaryHeap` can be driven by it.
///
/// `Monomial` has no intrinsic order, and `MonomialOrder::cmp` is a method rather than an `Ord`
/// impl. Wrapped in `Reverse`, this turns the max-heap into the min-heap FGLM needs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ByTargetOrder<const N: usize>(Monomial<N>);

impl<const N: usize> Ord for ByTargetOrder<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        TARGET.cmp(&self.0, &other.0)
    }
}

impl<const N: usize> PartialOrd for ByTargetOrder<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// How a candidate monomial's quotient vector is obtained.
///
/// Never by reducing a polynomial: `1` has a known vector, and every other candidate entered the
/// frontier as `x_i * t` for an accepted `t`, so one operator application gives its vector. This
/// is why the frontier carries more than a monomial.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Origin {
    /// The monomial 1.
    Identity,
    /// `x_variable` times the accepted monomial at `accepted`.
    Multiple { variable: usize, accepted: usize },
}

/// The reduced lex Gröbner basis of the ideal `source_basis` generates.
///
/// # Precondition
/// `source_basis` must be a Gröbner basis under `source_order`, and this is **not** verified.
///
/// **A violation gives a wrong basis, not an error.** The conversion works entirely inside the
/// quotient the source's leading monomials describe; if that is not `R/I` the walk still accepts
/// exactly as many monomials as that space has dimensions and still emits a consistent-looking
/// basis of the wrong ideal. Measured on eight non-Gröbner inputs, every one returned `Ok` with an
/// answer that disagreed with direct lex F4.
///
/// Use [`fglm_to_lex_checked`] for input of unknown provenance. Both engines in this crate satisfy
/// the precondition by construction, which is the case this entry point exists for — and
/// verification is not cheap enough to make the default: see [`fglm_to_lex_checked`].
///
/// # Errors
/// [`FglmError::PositiveDimensional`] if `R/I` is infinite-dimensional, a resource variant if a
/// limit in [`FglmOptions::default`] is crossed, or [`FglmError::NotAGrobnerBasis`] if the
/// precondition is violated in a way the conversion detects.
pub fn fglm_to_lex<const N: usize, F: FiniteField>(
    source_basis: &[MultivariatePolynomial<N, F>],
    source_order: MonomialOrder,
) -> Result<Vec<MultivariatePolynomial<N, F>>, FglmError> {
    fglm_to_lex_with_options(source_basis, source_order, &FglmOptions::default())
        .map(|(basis, _)| basis)
}

/// As [`fglm_to_lex`], under the given limits, additionally reporting the work performed.
pub fn fglm_to_lex_with_options<const N: usize, F: FiniteField>(
    source_basis: &[MultivariatePolynomial<N, F>],
    source_order: MonomialOrder,
    options: &FglmOptions,
) -> Result<(Vec<MultivariatePolynomial<N, F>>, FglmStatistics), FglmError> {
    let mut statistics = FglmStatistics {
        source_basis_elements: source_basis.len(),
        ..FglmStatistics::default()
    };

    // The unit ideal needs no special case, which is worth saying because it looks as though it
    // should. Its quotient is the zero space, so `one()` is the empty vector, the empty vector is
    // dependent on the empty span with no coefficients, and the relation that produces is `1` —
    // the correct lex basis. The walk then stops, because a dependent candidate enqueues no
    // children. A branch was written for this and removed when it proved to be dead.
    let algebra = QuotientAlgebra::new(source_basis, source_order, options)?;
    let dimension = algebra.dimension();
    statistics.quotient_dimension = dimension;
    statistics.operator_entries = (0..N)
        .map(|i| algebra.operator(i).stored_entries())
        .sum::<usize>();

    // The span's two blocks are `2 * D^2` entries. Checked before allocating, since the size is a
    // function of the dimension alone — not discovered as it fills.
    let span_entries = dimension
        .checked_mul(dimension)
        .and_then(|square| square.checked_mul(2))
        .ok_or(FglmError::SpanStorageExceeded {
            entries: usize::MAX,
            limit: options.max_span_entries,
        })?;
    if span_entries > options.max_span_entries {
        return Err(FglmError::SpanStorageExceeded {
            entries: span_entries,
            limit: options.max_span_entries,
        });
    }

    let mut span = IncrementalSpan::new(dimension);
    let mut accepted_monomials: Vec<Monomial<N>> = Vec::new();
    let mut accepted_vectors: Vec<Vec<F>> = Vec::new();
    let mut relations: Vec<MultivariatePolynomial<N, F>> = Vec::new();
    let mut leading: Vec<Monomial<N>> = Vec::new();

    let mut frontier: BinaryHeap<(Reverse<ByTargetOrder<N>>, Origin)> = BinaryHeap::new();
    let mut seen: HashSet<Monomial<N>> = HashSet::from([Monomial::one()]);
    frontier.push((Reverse(ByTargetOrder(Monomial::one())), Origin::Identity));

    while let Some((Reverse(ByTargetOrder(monomial)), origin)) = frontier.pop() {
        statistics.candidates_considered += 1;

        // The target staircase, as far as it is known. A multiple of an emitted leading monomial
        // is in the initial ideal, so it is neither a standard monomial nor the leading monomial
        // of a new relation.
        if leading.iter().any(|lm| monomial.checked_div(lm).is_some()) {
            statistics.candidates_pruned += 1;
            continue;
        }

        let vector = match origin {
            Origin::Identity => algebra.one(),
            Origin::Multiple { variable, accepted } => {
                algebra.multiply_by_variable(variable, &accepted_vectors[accepted])
            }
        };

        match span.reduce(&vector) {
            Dependence::Independent {
                residue,
                combination,
            } => {
                statistics.candidates_independent += 1;
                span.insert(residue, combination);
                let accepted = accepted_monomials.len();
                accepted_monomials.push(monomial);
                accepted_vectors.push(vector);

                for variable in 0..N {
                    let child = monomial * Monomial::univariate(variable, 1);
                    if seen.insert(child) {
                        frontier.push((
                            Reverse(ByTargetOrder(child)),
                            Origin::Multiple { variable, accepted },
                        ));
                    }
                }
            }
            Dependence::Dependent { coefficients } => {
                statistics.candidates_dependent += 1;
                relations.push(relation(monomial, &coefficients, &accepted_monomials));
                leading.push(monomial);
            }
        }
    }

    // FGLM's theorem: the accepted monomials are a basis of R/I under the target order, so there
    // are exactly D of them. An assertion of that invariant and **not** a validation of the input
    // — a non-Gröbner source reaches D accepted monomials just the same, over a quotient that is
    // not R/I, which is why `fglm_to_lex_checked` exists and why this is a `debug_assert`.
    debug_assert_eq!(
        accepted_monomials.len(),
        dimension,
        "the walk accepted a number of monomials other than the quotient dimension"
    );

    // Sorted by leading monomial descending, the convention both Gröbner engines return, so that
    // a comparison against either is an equality of values rather than of sets.
    relations.sort_by(|a, b| TARGET.cmp(&b.leading_monomial(TARGET), &a.leading_monomial(TARGET)));

    statistics.target_basis_elements = relations.len();
    statistics.span_row_operations = span.row_operations();
    Ok((relations, statistics))
}

/// As [`fglm_to_lex`], after verifying that the source really is a Gröbner basis.
///
/// Every S-polynomial of the source is reduced against it and must vanish — Buchberger's
/// criterion, applied with no pair-elimination criteria at all.
///
/// **This costs more than computing the basis did**, which is why it is a separate entry point
/// rather than the default. `cargo run --release --example fglm_conversion`, grevlex over
/// GF(2^31 - 1): verification runs at 0.6x the basis computation on the smallest instances and
/// 27x on katsura-7, where it takes 841 ms against a 30 ms basis and a 36 ms conversion. Making it
/// unconditional would cost an order of magnitude more than the conversion it protects.
///
/// # Errors
/// [`FglmError::NotAGrobnerBasis`] if the criterion fails, and otherwise as [`fglm_to_lex`].
pub fn fglm_to_lex_checked<const N: usize, F: FiniteField>(
    source_basis: &[MultivariatePolynomial<N, F>],
    source_order: MonomialOrder,
) -> Result<Vec<MultivariatePolynomial<N, F>>, FglmError> {
    if !is_grobner_basis(source_basis, source_order) {
        return Err(FglmError::NotAGrobnerBasis);
    }
    fglm_to_lex(source_basis, source_order)
}

/// Whether every S-polynomial of `basis` reduces to zero modulo it: Buchberger's criterion.
///
/// The definition, with no criteria applied, because this is a check and not a computation.
pub fn is_grobner_basis<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> bool {
    let nonzero: Vec<&MultivariatePolynomial<N, F>> =
        basis.iter().filter(|p| !p.is_zero()).collect();

    for (i, f) in nonzero.iter().enumerate() {
        for g in nonzero.iter().skip(i + 1) {
            let s = s_polynomial(f, g, order);
            if !s.normal_form(basis, order).is_zero() {
                return false;
            }
        }
    }
    true
}

/// `monomial - sum_j coefficients[j] * accepted[j]`, the relation a dependence stands for.
///
/// Monic in `monomial` by construction, and `monomial` is its lex leading monomial because every
/// accepted monomial was taken off the frontier before it.
fn relation<const N: usize, F: FiniteField>(
    monomial: Monomial<N>,
    coefficients: &[F],
    accepted: &[Monomial<N>],
) -> MultivariatePolynomial<N, F> {
    let mut terms: Vec<(Monomial<N>, F)> = Vec::with_capacity(accepted.len() + 1);
    terms.push((monomial, F::one()));
    for (accepted_monomial, coefficient) in accepted.iter().zip(coefficients) {
        if !coefficient.is_zero() {
            terms.push((*accepted_monomial, F::zero() - *coefficient));
        }
    }
    MultivariatePolynomial::new(&terms)
}

#[cfg(test)]
mod tests {
    use super::{
        fglm_to_lex, fglm_to_lex_checked, fglm_to_lex_with_options, is_grobner_basis, TARGET,
    };
    use crate::{
        fields::{PrimeFieldElement64, Zp2147483647},
        grobner::{
            benchmark_systems::{cyclic, katsura, planted},
            buchberger, buchberger_with_criteria, f4,
            fglm::{FglmError, FglmOptions},
            reference::buchberger_reference,
            PairCriteria,
        },
        FiniteField, MonomialOrder, MultivariatePolynomial, One,
    };

    type F = Zp2147483647;

    const SOURCE_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::GradedReverseLexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::Lexicographic,
    ];

    /// Zero-dimensional two-variable systems, covering radical, nonradical, and inconsistent.
    const SYSTEMS: [&[&str]; 9] = [
        &["x^2", "y^2"],
        &["x^2 - y", "y^3 - 1"],
        &["x + y", "x*y - 1"],
        &["x^3 - 1", "y - x^2"],
        &["x^2 - 2*x + 1", "y - x"],
        &["x^4 - x", "y^2 - x"],
        &["x^2 + y^2 - 1", "x - y"],
        &["x^5 - 1", "y^3 - x"],
        &["x^2 + 1", "y^2 + 1"],
    ];

    fn parse<const N: usize>(
        system: &[&str],
        variables: [&str; N],
    ) -> Vec<MultivariatePolynomial<N, F>> {
        system
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, variables).unwrap())
            .collect()
    }

    /// Every polynomial of `a` reduces to zero modulo `b`, i.e. `<a>` is contained in `<b>`.
    fn is_contained_in<const N: usize>(
        a: &[MultivariatePolynomial<N, F>],
        b: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) -> bool {
        a.iter().all(|p| p.normal_form(b, order).is_zero())
    }

    /// The FGLM lex basis equals the lex basis F4 computes directly.
    ///
    /// A reduced Gröbner basis is unique for an ideal and an order, and both are returned sorted
    /// by leading monomial descending, so this is an equality of values. It is the strongest
    /// single check available and it holds from every source order.
    #[test]
    fn test_the_conversion_agrees_with_direct_lex_f4() {
        for source_order in SOURCE_ORDERS {
            for system in SYSTEMS {
                let generators = parse(system, ["x", "y"]);
                let source = f4(&generators, source_order).expect("within limits");
                let converted = fglm_to_lex(&source, source_order).expect("convertible");
                let direct = f4(&generators, TARGET).expect("within limits");
                assert_eq!(
                    converted, direct,
                    "{:?} converted from {:?} disagrees with direct lex F4",
                    system, source_order
                );
            }
        }
    }

    /// It also equals what both Buchberger implementations compute directly.
    ///
    /// `buchberger_reference` is the textbook formulation with no pair criteria, kept as an
    /// oracle, so agreement with it is independent of every optimization F4 and the optimized
    /// classical engine share.
    #[test]
    fn test_the_conversion_agrees_with_both_buchberger_implementations() {
        let source_order = MonomialOrder::GradedReverseLexicographic;
        for system in SYSTEMS {
            let generators = parse(system, ["x", "y"]);
            let source = f4(&generators, source_order).expect("within limits");
            let converted = fglm_to_lex(&source, source_order).expect("convertible");

            assert_eq!(
                converted,
                buchberger(&generators, TARGET),
                "{:?} disagrees with the optimized classical engine",
                system
            );
            assert_eq!(
                converted,
                buchberger_reference(&generators, TARGET),
                "{:?} disagrees with the reference engine",
                system
            );
        }
    }

    /// The converted basis generates the same ideal, checked in both directions.
    ///
    /// Equality of reduced bases already implies this, but it is the property that matters and it
    /// is checked differently: by reduction rather than by comparison, so a shared bug in how both
    /// engines normalize could not hide it.
    #[test]
    fn test_the_conversion_preserves_the_ideal() {
        for source_order in SOURCE_ORDERS {
            for system in SYSTEMS {
                let generators = parse(system, ["x", "y"]);
                let source = f4(&generators, source_order).expect("within limits");
                let converted = fglm_to_lex(&source, source_order).expect("convertible");

                assert!(
                    is_contained_in(&source, &converted, TARGET),
                    "{:?}: the source is not inside the converted ideal",
                    system
                );
                assert!(
                    is_contained_in(&converted, &source, source_order),
                    "{:?}: the converted basis is not inside the source ideal",
                    system
                );
                // And the original generators, not only the source basis.
                assert!(
                    is_contained_in(&generators, &converted, TARGET),
                    "{:?}: a generator is not inside the converted ideal",
                    system
                );
            }
        }
    }

    /// The converted basis satisfies Buchberger's criterion under lex.
    ///
    /// Being a Gröbner basis is a property of the output alone, so this needs no second engine to
    /// compare against.
    #[test]
    fn test_the_converted_basis_is_a_grobner_basis() {
        for source_order in SOURCE_ORDERS {
            for system in SYSTEMS {
                let source = f4(&parse(system, ["x", "y"]), source_order).expect("within limits");
                let converted = fglm_to_lex(&source, source_order).expect("convertible");
                assert!(
                    is_grobner_basis(&converted, TARGET),
                    "{:?} converted from {:?} is not a Gröbner basis",
                    system,
                    source_order
                );
            }
        }
    }

    /// The converted basis is monic and reduced, with no interreduction pass.
    ///
    /// The claim in this module's header: every relation's leading coefficient is one, and no
    /// non-leading term of any relation is divisible by any relation's leading monomial.
    #[test]
    fn test_the_converted_basis_is_reduced_without_interreduction() {
        for source_order in SOURCE_ORDERS {
            for system in SYSTEMS {
                let source = f4(&parse(system, ["x", "y"]), source_order).expect("within limits");
                let converted = fglm_to_lex(&source, source_order).expect("convertible");
                let leading: Vec<_> = converted
                    .iter()
                    .map(|p| p.leading_monomial(TARGET))
                    .collect();

                for p in &converted {
                    assert_eq!(
                        p.leading_coefficient(TARGET),
                        F::one(),
                        "{} is not monic",
                        p
                    );
                    let own = p.leading_monomial(TARGET);
                    for monomial in p.terms().keys() {
                        if *monomial == own {
                            continue;
                        }
                        for lm in &leading {
                            assert!(
                                monomial.checked_div(lm).is_none(),
                                "{} of {} is divisible by the leading monomial {}",
                                monomial,
                                p,
                                lm
                            );
                        }
                    }
                }
            }
        }
    }

    /// `<x^2, y^2>` keeps its multiplicities: the lex basis is `{x^2, y^2}`, not `{x, y}`.
    ///
    /// The nonradical test the milestone turns on. Both ideals have the single zero (0, 0), so any
    /// check that compared solution sets would pass either. Committed as a literal rather than
    /// compared against another engine, because this is the case worth pinning by hand.
    #[test]
    fn test_a_nonradical_ideal_keeps_its_multiplicities() {
        let source_order = MonomialOrder::GradedReverseLexicographic;
        let source = f4(&parse(&["x^2", "y^2"], ["x", "y"]), source_order).expect("within limits");
        let converted = fglm_to_lex(&source, source_order).expect("convertible");

        let expected = parse(&["x^2", "y^2"], ["x", "y"]);
        assert_eq!(converted, expected);

        // Explicitly not the radical.
        let radical = parse(&["x", "y"], ["x", "y"]);
        assert_ne!(converted, radical);
    }

    /// `<(x-1)^2, y-x>` keeps its double root.
    #[test]
    fn test_a_double_root_survives_the_conversion() {
        let source_order = MonomialOrder::GradedReverseLexicographic;
        let generators = parse(&["x^2 - 2*x + 1", "y - x"], ["x", "y"]);
        let source = f4(&generators, source_order).expect("within limits");
        let converted = fglm_to_lex(&source, source_order).expect("convertible");

        // Quotient dimension two, so the basis cannot be the radical's {x - 1, y - 1}.
        let (_, statistics) =
            fglm_to_lex_with_options(&source, source_order, &FglmOptions::unbounded())
                .expect("convertible");
        assert_eq!(statistics.quotient_dimension, 2);
        assert_ne!(converted, parse(&["x - 1", "y - 1"], ["x", "y"]));
        assert_eq!(converted, f4(&generators, TARGET).expect("within limits"));
    }

    /// Hand-derived lex bases, committed as literals.
    ///
    /// `<x^2 - y, y^3 - 1>` is already a lex Gröbner basis: the leading monomials `x^2` and `y^3`
    /// are coprime, so Buchberger's product criterion discards the only pair and there is nothing
    /// to add. `<x^2, y^2>` is a monomial ideal and so is its own reduced basis under every order.
    ///
    /// These are derived by hand rather than taken from an external computer-algebra system. No
    /// such system was available here, so the milestone's "committed external reference" oracle
    /// remains outstanding — recorded in the milestone document rather than quietly skipped.
    #[test]
    fn test_hand_derived_lex_bases() {
        let source_order = MonomialOrder::GradedReverseLexicographic;

        let cases: [(&[&str], &[&str]); 2] = [
            (&["x^2 - y", "y^3 - 1"], &["x^2 - y", "y^3 - 1"]),
            (&["x^2", "y^2"], &["x^2", "y^2"]),
        ];
        for (system, expected) in cases {
            let source = f4(&parse(system, ["x", "y"]), source_order).expect("within limits");
            let converted = fglm_to_lex(&source, source_order).expect("convertible");
            assert_eq!(
                converted,
                parse(expected, ["x", "y"]),
                "{:?} did not convert to its hand-derived lex basis",
                system
            );
        }
    }

    /// The unit ideal converts to `{1}`.
    #[test]
    fn test_the_unit_ideal_converts_to_itself() {
        for source_order in SOURCE_ORDERS {
            let source =
                f4(&parse(&["x", "x - 1"], ["x", "y"]), source_order).expect("within limits");
            let (converted, statistics) =
                fglm_to_lex_with_options(&source, source_order, &FglmOptions::default())
                    .expect("convertible");
            assert_eq!(converted, vec![MultivariatePolynomial::<2, F>::one()]);
            assert_eq!(statistics.quotient_dimension, 0);
            assert_eq!(statistics.target_basis_elements, 1);
        }
    }

    /// A positive-dimensional ideal is rejected, cyclic-4 included.
    #[test]
    fn test_positive_dimensional_ideals_are_rejected() {
        for source_order in SOURCE_ORDERS {
            let curve = f4(&parse(&["x*y - 1"], ["x", "y"]), source_order).expect("within limits");
            assert_eq!(
                fglm_to_lex(&curve, source_order).unwrap_err(),
                FglmError::PositiveDimensional
            );

            let cyclic_4 = f4(&cyclic::<4, F>(), source_order).expect("within limits");
            assert_eq!(
                fglm_to_lex(&cyclic_4, source_order).unwrap_err(),
                FglmError::PositiveDimensional
            );
        }
    }

    /// Permuting the generators gives a byte-identical lex basis.
    #[test]
    fn test_the_result_does_not_depend_on_generator_order() {
        let source_order = MonomialOrder::GradedReverseLexicographic;
        let forwards = f4(&parse(&["x^3 - y", "y^2 - 1"], ["x", "y"]), source_order).unwrap();
        let backwards = f4(&parse(&["y^2 - 1", "x^3 - y"], ["x", "y"]), source_order).unwrap();
        assert_eq!(
            fglm_to_lex(&forwards, source_order).unwrap(),
            fglm_to_lex(&backwards, source_order).unwrap()
        );
    }

    /// The conversion agrees with direct lex F4 over several fields.
    #[test]
    fn test_the_conversion_agrees_over_several_fields() {
        fn check<const P: u64>() {
            type Vars = [&'static str; 2];
            const VARS: Vars = ["x", "y"];
            let source_order = MonomialOrder::GradedReverseLexicographic;
            for system in [
                ["x^2 - y", "y^3 - 1"],
                ["x^2", "y^2"],
                ["x + y", "x*y - 1"],
                ["x^2 + 1", "y - x"],
            ] {
                let generators: Vec<MultivariatePolynomial<2, PrimeFieldElement64<P>>> = system
                    .iter()
                    .map(|s| MultivariatePolynomial::parse(s, VARS).unwrap())
                    .collect();
                let source = f4(&generators, source_order).expect("within limits");
                let converted = super::fglm_to_lex(&source, source_order).expect("convertible");
                assert_eq!(
                    converted,
                    f4(&generators, MonomialOrder::Lexicographic).expect("within limits"),
                    "{:?} over GF({})",
                    system,
                    P
                );
            }
        }
        check::<7>();
        check::<13>();
        check::<65537>();
        check::<2147483647>();
    }

    /// The conversion agrees with direct lex F4 on the benchmark corpus.
    ///
    /// The instances the milestone exists for. katsura-6 is included because it is the one where
    /// the classical engine cannot produce a lex basis at all, so the conversion is compared
    /// against F4's.
    #[test]
    fn test_the_conversion_agrees_on_the_benchmark_corpus() {
        let source_order = MonomialOrder::GradedReverseLexicographic;

        macro_rules! check {
            ($system:expr, $name:literal) => {{
                let generators = $system;
                let source = f4(&generators, source_order).expect("within limits");
                let converted = fglm_to_lex(&source, source_order).expect("convertible");
                assert_eq!(
                    converted,
                    f4(&generators, TARGET).expect("within limits"),
                    "{} disagrees with direct lex F4",
                    $name
                );
            }};
        }

        check!(cyclic::<3, F>(), "cyclic-3");
        check!(katsura::<3, F>(), "katsura-3");
        check!(katsura::<4, F>(), "katsura-4");
        check!(katsura::<5, F>(), "katsura-5");
        check!(katsura::<6, F>(), "katsura-6");

        let point: Vec<F> = [3u64, 5, 7, 11].iter().map(|v| F::new(*v)).collect();
        check!(planted::<4, F>(&point), "planted-4");
    }

    /// Statistics add up: every candidate is pruned, accepted, or produces a relation.
    #[test]
    fn test_the_statistics_account_for_every_candidate() {
        let source_order = MonomialOrder::GradedReverseLexicographic;
        for system in SYSTEMS {
            let source = f4(&parse(system, ["x", "y"]), source_order).expect("within limits");
            let (basis, s) =
                fglm_to_lex_with_options(&source, source_order, &FglmOptions::unbounded())
                    .expect("convertible");

            assert_eq!(
                s.candidates_considered,
                s.candidates_pruned + s.candidates_independent + s.candidates_dependent,
                "{:?}: the candidate counts do not add up",
                system
            );
            assert_eq!(s.candidates_independent, s.quotient_dimension);
            assert_eq!(s.candidates_dependent, basis.len());
            assert_eq!(s.target_basis_elements, basis.len());
            assert_eq!(s.source_basis_elements, source.len());
            // At most 1 + N*D candidates ever enter the frontier.
            assert!(
                s.candidates_considered <= 1 + 2 * s.quotient_dimension,
                "{:?}: {} candidates exceeds the bound of {}",
                system,
                s.candidates_considered,
                1 + 2 * s.quotient_dimension
            );
        }
    }

    /// Resource limits produce structured errors rather than partial bases.
    #[test]
    fn test_resource_limits_are_enforced() {
        let source_order = MonomialOrder::GradedReverseLexicographic;
        let source = f4(&katsura::<5, F>(), source_order).expect("within limits");

        let mut options = FglmOptions::unbounded();
        options.max_quotient_dimension = 8;
        assert_eq!(
            fglm_to_lex_with_options(&source, source_order, &options).unwrap_err(),
            FglmError::QuotientDimensionExceeded { limit: 8 }
        );

        let mut options = FglmOptions::unbounded();
        options.max_operator_entries = 4;
        assert!(matches!(
            fglm_to_lex_with_options(&source, source_order, &options).unwrap_err(),
            FglmError::OperatorStorageExceeded { .. }
        ));

        // D = 16, so the span needs 2 * 256 = 512 entries.
        let mut options = FglmOptions::unbounded();
        options.max_span_entries = 511;
        assert_eq!(
            fglm_to_lex_with_options(&source, source_order, &options).unwrap_err(),
            FglmError::SpanStorageExceeded {
                entries: 512,
                limit: 511
            }
        );
        options.max_span_entries = 512;
        assert!(fglm_to_lex_with_options(&source, source_order, &options).is_ok());
    }

    /// `is_grobner_basis` accepts what the engines produce and rejects a non-basis.
    #[test]
    fn test_the_grobner_basis_check_discriminates() {
        let order = MonomialOrder::Lexicographic;
        let generators = parse(&["x^2 - y", "x*y - 1"], ["x", "y"]);

        // The generators alone are not a Gröbner basis: their S-polynomial does not reduce away.
        assert!(!is_grobner_basis(&generators, order));

        // What either engine returns is.
        assert!(is_grobner_basis(
            &f4(&generators, order).expect("within limits"),
            order
        ));
        assert!(is_grobner_basis(
            &buchberger_with_criteria(&generators, order, &PairCriteria::ALL).0,
            order
        ));
    }

    /// The checked entry point rejects a source that is not a Gröbner basis.
    ///
    /// The unchecked one is free to return a wrong answer on such input, which is exactly why the
    /// checked one exists.
    #[test]
    fn test_the_checked_entry_point_rejects_a_non_basis() {
        let source_order = MonomialOrder::GradedReverseLexicographic;
        let generators = parse(&["x^2 - y", "x*y - 1"], ["x", "y"]);
        assert!(!is_grobner_basis(&generators, source_order));
        assert_eq!(
            fglm_to_lex_checked(&generators, source_order).unwrap_err(),
            FglmError::NotAGrobnerBasis
        );

        // And accepts a real one, agreeing with the unchecked path.
        let source = f4(&generators, source_order).expect("within limits");
        assert_eq!(
            fglm_to_lex_checked(&source, source_order).expect("convertible"),
            fglm_to_lex(&source, source_order).expect("convertible")
        );
    }

    /// A non-Gröbner source gives a wrong basis from the unchecked path, and an error from the
    /// checked one.
    ///
    /// The hazard, recorded rather than described. Each input below has pure-power leading
    /// monomials in every variable, so it passes classification, and each generates an ideal whose
    /// real lex basis is something else. The unchecked conversion returns `Ok` on all of them.
    #[test]
    fn test_a_non_grobner_source_is_silently_wrong_unless_checked() {
        let source_order = MonomialOrder::GradedReverseLexicographic;
        let hazards: [&[&str]; 4] = [
            &["x^2 - y", "y^2 - x", "x*y"],
            &["x^2", "y^2", "x*y - 1"],
            &["x^3 - 1", "y^3 - 1", "x*y - 1"],
            &["x^4 - 1", "y^4 - 1", "x^2*y^2 - 1"],
        ];

        for system in hazards {
            let generators = parse(system, ["x", "y"]);
            assert!(
                !is_grobner_basis(&generators, source_order),
                "{:?} is a Gröbner basis after all, so it is not a hazard",
                system
            );

            // The unchecked path returns something, and that something is wrong.
            let unchecked = fglm_to_lex(&generators, source_order)
                .expect("the unchecked path does not detect this");
            let truth = f4(&generators, TARGET).expect("within limits");
            assert_ne!(
                unchecked, truth,
                "{:?} happened to convert correctly, which would make it a poor example",
                system
            );

            // The checked path refuses.
            assert_eq!(
                fglm_to_lex_checked(&generators, source_order).unwrap_err(),
                FglmError::NotAGrobnerBasis,
                "{:?} was not rejected",
                system
            );
        }
    }

    /// Converting a lex basis to lex returns it unchanged.
    ///
    /// The identity case. It exercises the whole pipeline — operators, frontier, span — and the
    /// answer is known without computing anything, so a conversion that merely echoed its input
    /// would be caught by every other test but not by this one, and vice versa.
    #[test]
    fn test_converting_a_lex_basis_is_the_identity() {
        for system in SYSTEMS {
            let source = f4(&parse(system, ["x", "y"]), TARGET).expect("within limits");
            assert_eq!(
                fglm_to_lex(&source, TARGET).expect("convertible"),
                source,
                "{:?} was changed by converting lex to lex",
                system
            );
        }
    }

    /// A three-variable system that is not in shape position.
    ///
    /// `<x^2 - 1, y^2 - 1, z - 1>` has four points and no coordinate separating them, so the lex
    /// basis is not triangular in the favourable sense and FGLM must not assume it is.
    #[test]
    fn test_a_system_not_in_shape_position() {
        let source_order = MonomialOrder::GradedReverseLexicographic;
        let generators = parse(&["x^2 - 1", "y^2 - 1", "z - 1"], ["x", "y", "z"]);
        let source = f4(&generators, source_order).expect("within limits");
        let (converted, statistics) =
            fglm_to_lex_with_options(&source, source_order, &FglmOptions::unbounded())
                .expect("convertible");

        assert_eq!(statistics.quotient_dimension, 4);
        assert_eq!(converted, f4(&generators, TARGET).expect("within limits"));
    }
}

/// Differential tests against lexicographic bases computed by Singular.
///
/// Separate from the module's own tests because the oracle is different in kind: everything there
/// compares Zeebra against Zeebra, which is strong but shares whatever this crate misunderstands.
/// Singular's `std` is Buchberger/slimgb lineage, so these are independent in algorithm.
#[cfg(test)]
mod singular_reference {
    use super::{fglm_to_lex, TARGET};
    use crate::{
        fields::PrimeFieldElement64,
        grobner::{f4, fglm::reference_bases},
        MonomialOrder, MultivariatePolynomial,
    };

    const SOURCE: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    /// Convert each reference system from grevlex and compare against Singular's lex basis.
    ///
    /// Both sides are the unique reduced lex basis of the ideal, so this is an equality of values
    /// once they are ordered the same way — Singular lists ascending by leading monomial and
    /// Zeebra descending.
    fn check<const N: usize, const P: u64>(cases: &[reference_bases::ReferenceBasis]) {
        type Poly<const N: usize, const P: u64> = MultivariatePolynomial<N, PrimeFieldElement64<P>>;

        assert!(
            !cases.is_empty(),
            "the reference table for this group is empty"
        );

        for case in cases {
            assert_eq!(case.prime, P, "{} is over the wrong field", case.name);
            let variables = <[&str; N]>::try_from(case.variables)
                .unwrap_or_else(|_| panic!("{} has the wrong variable count", case.name));

            let parse = |source: &str| -> Poly<N, P> {
                MultivariatePolynomial::parse(source, variables)
                    .unwrap_or_else(|e| panic!("{}: cannot parse {:?}: {}", case.name, source, e))
            };

            let system: Vec<Poly<N, P>> = case.system.iter().map(|s| parse(s)).collect();
            let mut expected: Vec<Poly<N, P>> = case.lex_basis.iter().map(|s| parse(s)).collect();

            let source = f4(&system, SOURCE).expect("within limits");
            let converted = fglm_to_lex(&source, SOURCE).expect("convertible");

            expected.sort_by(|a, b| {
                TARGET.cmp(&b.leading_monomial(TARGET), &a.leading_monomial(TARGET))
            });

            assert_eq!(
                converted, expected,
                "{} over GF({}): the conversion disagrees with Singular",
                case.name, P
            );
        }
    }

    /// Two-variable systems over GF(2^31 - 1), against Singular.
    #[test]
    fn test_two_variable_systems_agree_with_singular() {
        check::<2, 2147483647>(reference_bases::TWO_VARIABLE);
    }

    /// Three-variable systems over GF(2^31 - 1), against Singular.
    ///
    /// Includes cyclic-3, katsura-3, a system not in shape position, and a nonradical one.
    #[test]
    fn test_three_variable_systems_agree_with_singular() {
        check::<3, 2147483647>(reference_bases::THREE_VARIABLE);
    }

    /// Four-variable systems over GF(2^31 - 1), against Singular.
    ///
    /// katsura-4 and a planted system, the latter with a lex basis whose coefficients are large
    /// enough that agreeing on them by accident is not a possibility.
    #[test]
    fn test_four_variable_systems_agree_with_singular() {
        check::<4, 2147483647>(reference_bases::FOUR_VARIABLE);
    }

    /// The same algebra over GF(13) and GF(65537), against Singular.
    ///
    /// Singular's characteristic must be below 2^31, so it cannot check Zeebra at Goldilocks or
    /// above. The staircase and the quotient dimension are properties of the ideal rather than of
    /// the prime, so agreement here plus Zeebra's own cross-field agreement is what carries the
    /// external evidence to the fields Singular cannot reach. See §9.1 of the milestone document.
    #[test]
    fn test_smaller_fields_agree_with_singular() {
        check::<2, 13>(reference_bases::OVER_GF_13);
        check::<2, 65537>(reference_bases::OVER_GF_65537);
    }

    /// Every reference system gives the same quotient dimension at every prime it is stated over.
    ///
    /// The cross-field consistency the argument above rests on, checked rather than asserted: the
    /// four systems common to GF(13), GF(65537) and GF(2^31 - 1) must have identical quotient
    /// dimensions, since D is a property of the ideal's staircase.
    #[test]
    fn test_the_quotient_dimension_is_the_same_at_every_prime() {
        use crate::grobner::fglm::QuotientBasis;

        fn dimension<const P: u64>(system: &[&str]) -> usize {
            let polynomials: Vec<MultivariatePolynomial<2, PrimeFieldElement64<P>>> = system
                .iter()
                .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
                .collect();
            let basis = f4(&polynomials, SOURCE).expect("within limits");
            QuotientBasis::new(&basis, SOURCE, usize::MAX)
                .expect("finite")
                .dimension()
        }

        for case in reference_bases::OVER_GF_13 {
            let small = dimension::<13>(case.system);
            let medium = dimension::<65537>(case.system);
            let large = dimension::<2147483647>(case.system);
            assert_eq!(
                (small, medium),
                (large, large),
                "{} has quotient dimension {} over GF(13), {} over GF(65537) and {} over \
                 GF(2^31 - 1)",
                case.name,
                small,
                medium,
                large
            );
        }
    }
}
