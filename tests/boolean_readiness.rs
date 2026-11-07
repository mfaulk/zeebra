//! Boolean solving readiness over GF(2) and GF(2^8): the evidence behind
//! `docs/research/boolean-solving.md`.
//!
//! An integration test rather than module tests, because the subject is the *public* stack —
//! parsing, F4, FGLM and the solvers as a caller reaches them. Several of these pin a gap rather
//! than a capability; each such test names the issue that owns the gap.

use std::collections::HashSet;
use std::mem::size_of;

use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::{BinaryFieldElement, Gf256, Zp2},
    grobner::{
        classify_ideal, f4, fglm_to_lex, is_grobner_basis, rational_points_by_enumeration,
        solve_one, solve_one_with_options, solve_zero_dimensional, with_field_equations, F4Options,
        IdealClass, QuotientBasis, SolveOptions, SolveStrategy,
    },
    roots, FiniteField, KnownOrder, Monomial, MonomialOrder, MultivariatePolynomial, One,
    UnivariatePolynomial, Zero,
};

/// GF(2) reached through `BinaryFieldElement` rather than through `PrimeFieldElement32<2>`.
///
/// `0b11` is `x + 1`, the only irreducible of degree one, so this is GF(2). It has no declared
/// alias in `src/fields/irreducible_polynomials.rs`; the literal is the point of
/// [`gf2_by_either_route_is_one_field_at_twice_the_storage`].
type Gf2Binary = BinaryFieldElement<0b11>;

const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const LEX: MonomialOrder = MonomialOrder::Lexicographic;

/// A random quadratic system in `N` Boolean variables with a planted solution.
///
/// The plant is satisfied by construction: each generator is drawn, then its value at the plant is
/// subtracted, so the constant term is whatever it has to be. The same shape as
/// `grobner::field_equations`'s own test, at the `n = 8` where brute force is 256 assignments.
fn boolean_system<const N: usize>(
    seed: u64,
    generators: usize,
) -> ([Zp2; N], Vec<MultivariatePolynomial<N, Zp2>>) {
    let mut rng = StdRng::seed_from_u64(seed);
    let plant: [Zp2; N] = std::array::from_fn(|_| Zp2::new(rng.gen_range(0..2)));
    let mut system = Vec::new();
    for _ in 0..generators {
        let mut terms: Vec<(Monomial<N>, Zp2)> = Vec::new();
        for i in 0..N {
            for j in i..N {
                if rng.gen_bool(0.3) {
                    let mut exponents = [0u32; N];
                    exponents[i] += 1;
                    exponents[j] += 1;
                    terms.push((Monomial::new(&exponents), Zp2::one()));
                }
            }
        }
        let mut polynomial: MultivariatePolynomial<N, Zp2> = MultivariatePolynomial::new(&terms);
        let value = polynomial.eval(&plant);
        polynomial += MultivariatePolynomial::new(&[(Monomial::one(), Zp2::zero() - value)]);
        system.push(polynomial);
    }
    (plant, system)
}

/// The whole Boolean path over GF(2) — F4, quotient, FGLM, `solve_one` — ends at a real point.
///
/// #233 took this ideal as far as a quotient dimension. The half that #219 actually needs is the
/// rest: that FGLM converts the field-equation ideal and that the search returns a point of the
/// system, not of the extended one. Both halves are asserted against the 256-assignment
/// enumeration, which cannot itself be wrong at this size.
#[test]
fn the_gf2_boolean_path_reaches_a_point_with_field_equations() {
    let (plant, system) = boolean_system::<8>(9, 6);

    let points = rational_points_by_enumeration(&system).expect("GF(2) is a prime field");
    assert!(points.contains(&plant), "the plant must be a solution");

    let extended = with_field_equations(&system).expect("GF(2) has field equations");
    let basis = f4(&extended, GREVLEX).expect("within the default budgets");
    assert_eq!(classify_ideal(&basis, GREVLEX), IdealClass::ZeroDimensional);
    assert_eq!(
        QuotientBasis::new(&basis, GREVLEX, 4096)
            .expect("zero-dimensional")
            .dimension(),
        points.len(),
        "the ideal is radical with the field equations, so its dimension is the point count"
    );

    let lex_basis = fglm_to_lex(&basis, GREVLEX).expect("zero-dimensional, so FGLM applies");
    assert!(is_grobner_basis(&lex_basis, LEX));

    let mut rng = StdRng::seed_from_u64(3);
    let point = solve_one(&extended, &mut rng)
        .expect("zero-dimensional")
        .expect("there are GF(2) points");
    assert!(
        points.contains(&point),
        "the point must be one the enumeration found"
    );
    for polynomial in &system {
        assert!(
            polynomial.eval(&point).is_zero(),
            "the point must satisfy the original system, not only the extended one"
        );
    }
}

/// The GF(2) solver finds *every* rational point and no others, against exhaustive enumeration.
///
/// Stronger than recovering one point: a solver that dropped a solution, or invented one over an
/// extension, passes the single-point test and fails this.
#[test]
fn the_gf2_solver_finds_exactly_the_enumerated_points() {
    let (_plant, system) = boolean_system::<8>(9, 6);
    let points = rational_points_by_enumeration(&system).expect("GF(2) is a prime field");
    let extended = with_field_equations(&system).expect("GF(2) has field equations");

    let mut rng = StdRng::seed_from_u64(4);
    let found = solve_zero_dimensional(&extended, &mut rng).expect("zero-dimensional");

    let found: HashSet<[Zp2; 8]> = found.into_iter().collect();
    let expected: HashSet<[Zp2; 8]> = points.into_iter().collect();
    assert_eq!(found, expected);
}

/// Without field equations the grevlex route diagnoses the ideal correctly and the default
/// `DirectLexF4` route reports a resource failure instead.
///
/// #218's gap 2 was "nothing refuses to proceed without them". Something does, but not on the
/// default path: `GrevlexF4ThenFglm` says "not zero-dimensional" at once, while `DirectLexF4`
/// exhausts a Macaulay-matrix budget — an error that invites raising the limit when the fix is to
/// adjoin the field equations. The lex half runs under a deliberately small budget so it fails
/// quickly; at the default budget it does far more work and reports the same kind of error.
///
/// The misdiagnosis is #376, which owns the fix. Asserted rather than described so that closing
/// #376 breaks this test and forces the write-up to be corrected with it.
#[test]
fn a_missing_field_equation_is_diagnosed_on_one_route_and_not_the_other() {
    let (_plant, system) = boolean_system::<8>(9, 6);

    let bare = f4(&system, GREVLEX).expect("within the default budgets");
    assert_eq!(
        classify_ideal(&bare, GREVLEX),
        IdealClass::PositiveDimensional,
        "six quadratics in eight variables are underdetermined without the field equations"
    );

    let mut rng = StdRng::seed_from_u64(5);
    let diagnosed = solve_one_with_options(
        &system,
        &mut rng,
        &SolveOptions::with_strategy(SolveStrategy::GrevlexF4ThenFglm),
    )
    .expect_err("a positive-dimensional system has no finite solution set");
    assert!(
        !diagnosed.is_resource_failure(),
        "the grevlex route names the real problem: {diagnosed}"
    );

    let mut rng = StdRng::seed_from_u64(5);
    let misdiagnosed = solve_one_with_options(
        &system,
        &mut rng,
        &SolveOptions {
            f4: F4Options {
                max_matrix_columns: 2000,
                max_matrix_rows: 2000,
                ..Default::default()
            },
            ..SolveOptions::with_strategy(SolveStrategy::DirectLexF4)
        },
    )
    .expect_err("the lex basis is out of reach");
    assert!(
        misdiagnosed.is_resource_failure(),
        "the default route blames its budget rather than the ideal: {misdiagnosed}"
    );
}

/// GF(2)'s two representations are the same field, and the prime-field one is half the storage.
///
/// #218's question 5. The whole addition and multiplication tables are compared rather than a
/// sample, there being only four pairs: if they agreed on a sample and differed anywhere, the
/// choice between them would not be free.
#[test]
fn gf2_by_either_route_is_one_field_at_twice_the_storage() {
    assert_eq!(Gf2Binary::order_u128(), Some(2));
    assert_eq!(Gf2Binary::characteristic_u128(), Some(2));

    for a in 0..2u64 {
        for b in 0..2u64 {
            let (x, y) = (Gf2Binary::new(a), Gf2Binary::new(b));
            let (p, q) = (Zp2::new(a), Zp2::new(b));
            assert_eq!(
                (x + y).coefficients(),
                u64::from(p + q != Zp2::zero()),
                "addition differs at ({a}, {b})"
            );
            assert_eq!(
                (x * y).coefficients(),
                u64::from(p * q != Zp2::zero()),
                "multiplication differs at ({a}, {b})"
            );
        }
    }

    assert_eq!(size_of::<Zp2>(), 4);
    assert_eq!(size_of::<Gf2Binary>(), 8);
}

/// A GF(2) coefficient occupies 16 bytes in a sparse entry and 4 in a bare element.
///
/// #218's question 3, as the part that is a fact about layout rather than a measurement: the
/// `(index, coefficient)` pair a sparse row stores is padded to the index's alignment, so one bit
/// of information costs 16 bytes — the same as a GF(2^8) coefficient, and the same as a 32-bit
/// prime-field one. No arithmetic change narrows that; only a different representation does.
#[test]
fn a_gf2_coefficient_costs_the_same_sparse_entry_as_any_other() {
    assert_eq!(size_of::<(usize, Zp2)>(), 16);
    assert_eq!(size_of::<(usize, Gf256)>(), 16);
    assert_eq!(size_of::<(usize, Gf2Binary)>(), 16);

    // And a monomial is an exponent array, four bytes per variable, where a Boolean monomial is a
    // bit per variable: 32 bytes for what eight bits describe.
    assert_eq!(size_of::<Monomial<8>>(), 32);
}

/// Univariate root finding works over GF(2^8), which exercises the trace-based splitter at m > 1.
///
/// `roots` branches on the characteristic: in characteristic two the role of `h^((q^d - 1)/2)`
/// falls to the absolute trace, whose term count is `m * d`. Every test of that branch was over
/// GF(2), where `m = 1` and a wrong `m` is invisible. This is the solver's last step over
/// GF(2^8), so #197's and #198's ladders depend on it.
#[test]
fn root_finding_works_over_gf256() {
    let mut rng = StdRng::seed_from_u64(11);
    let linear = |a: Gf256| UnivariatePolynomial::new(&[Gf256::zero() - a, Gf256::one()]);
    let expected = [Gf256::new(0x57), Gf256::new(0x83), Gf256::one()];
    let f = &(&linear(expected[0]) * &linear(expected[1])) * &linear(expected[2]);

    let found: HashSet<Gf256> = roots(&f, &mut rng).into_iter().collect();
    assert_eq!(found, expected.into_iter().collect::<HashSet<_>>());
}

/// F4 accepts GF(2^8)'s degree-256 field equations and the quotient has the 256 points of a line.
///
/// The cost rule in `docs/research/boolean-solving.md` §5.1 says the mechanism is wrong over
/// GF(2^8), not that it is unavailable. This separates the two: a single quadratic is
/// positive-dimensional bare and becomes a 256-dimensional quotient — one point of GF(2^8) per
/// value of the free variable — once the equations are adjoined.
#[test]
fn gf256_field_equations_are_usable_even_where_they_are_unwise() {
    // x0^2 + x1: a parametrized line, so one GF(256) point per value of x0.
    let system: Vec<MultivariatePolynomial<2, Gf256>> = vec![MultivariatePolynomial::new(&[
        (Monomial::new(&[2, 0]), Gf256::one()),
        (Monomial::new(&[0, 1]), Gf256::one()),
    ])];

    let bare = f4(&system, GREVLEX).expect("within the default budgets");
    assert_eq!(
        classify_ideal(&bare, GREVLEX),
        IdealClass::PositiveDimensional
    );

    let extended = with_field_equations(&system).expect("GF(2^8) has representable equations");
    assert_eq!(extended[1].degree(), 256, "the generator's degree is q");

    let basis = f4(&extended, GREVLEX).expect("within the default budgets");
    assert_eq!(classify_ideal(&basis, GREVLEX), IdealClass::ZeroDimensional);
    assert_eq!(
        QuotientBasis::new(&basis, GREVLEX, 1_000_000)
            .expect("zero-dimensional")
            .dimension(),
        256,
    );
}

/// GF(2^8) solving works end to end, so the field is not what blocks the GF(2^8) issues.
///
/// `solve_one` over `Gf256` is covered by `grobner::tests::test_the_whole_pipeline_over_gf256` on
/// a `planted` system; this is the same claim on a system built by hand, to keep the result
/// independent of `planted`'s characteristic-two degeneracy into a perfect square.
#[test]
fn gf256_solving_works_on_a_system_planted_by_hand() {
    // x0 + x1 + 1 and x0*x1 + 1: a sum and a product, so x0 and x1 are roots of t^2 + t + 1.
    let system: Vec<MultivariatePolynomial<2, Gf256>> = vec![
        MultivariatePolynomial::new(&[
            (Monomial::new(&[1, 0]), Gf256::one()),
            (Monomial::new(&[0, 1]), Gf256::one()),
            (Monomial::one(), Gf256::one()),
        ]),
        MultivariatePolynomial::new(&[
            (Monomial::new(&[1, 1]), Gf256::one()),
            (Monomial::one(), Gf256::one()),
        ]),
    ];

    let mut rng = StdRng::seed_from_u64(7);
    let point = solve_one(&system, &mut rng)
        .expect("zero-dimensional")
        .expect("t^2 + t + 1 splits over GF(2^8), 8 being even");
    for polynomial in &system {
        assert!(polynomial.eval(&point).is_zero());
    }
}

/// The enumeration oracle should cover GF(2^8), and cannot: `FiniteField::new` is `todo!()` there.
///
/// `#[ignore]`d for **#377**, which owns the gap. `rational_points_by_enumeration` refuses
/// extension fields as a value today — see
/// `grobner::field_equations::tests::enumeration_refuses_a_field_it_cannot_index` — because the
/// alternatives are a panic (`BinaryFieldElement::new` is `todo!()`) or a silently wrong count
/// (`ExtensionFieldElement::new` embeds the prime subfield, so it would walk 2 of 256 elements).
/// This test asserts the behaviour #377 should deliver, so it turns green when the gap closes.
#[test]
#[ignore = "blocked on #377: FiniteField::new cannot index a characteristic-two extension field"]
fn the_enumeration_oracle_should_cover_gf256() {
    // x0 + 1: exactly one GF(2^8) point.
    let system: Vec<MultivariatePolynomial<1, Gf256>> = vec![MultivariatePolynomial::new(&[
        (Monomial::new(&[1]), Gf256::one()),
        (Monomial::one(), Gf256::one()),
    ])];
    let points = rational_points_by_enumeration(&system).expect("GF(2^8) should enumerate");
    assert_eq!(points, vec![[Gf256::one()]]);
}

/// A system over GF(2^8) should parse from text, and cannot: `from_str` is `todo!()` there.
///
/// `#[ignore]`d for **#377**. `MultivariatePolynomial::parse` calls `F::from_str(..).unwrap()`, so
/// text input over `Gf256` or any `ExtensionFieldElement` **panics**. Every text-fed path over
/// GF(2^8) inherits it: the Fukuoka importer of #197, the HFE ladder of #198, and the Singular
/// oracle, which renders systems as strings. Over GF(2) the same call works, which is why
/// nothing noticed.
#[test]
#[ignore = "blocked on #377: FiniteField::from_str is todo!() for characteristic-two extensions"]
fn a_system_over_gf256_should_parse_from_text() {
    let parsed = MultivariatePolynomial::<2, Gf256>::parse("x0*x1 + x0 + 1", ["x0", "x1"])
        .expect("the text is well formed");
    assert_eq!(parsed.terms().len(), 3);

    // The same text over GF(2) parses today, so the gap is the field and not the parser.
    let over_gf2 = MultivariatePolynomial::<2, Zp2>::parse("x0*x1 + x0 + 1", ["x0", "x1"])
        .expect("GF(2) parses");
    assert_eq!(over_gf2.terms().len(), 3);
}
