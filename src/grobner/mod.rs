//! Grobner Basis algorithms

pub mod benchmark_systems;
mod buchberger;
pub mod differential;
pub mod external;
pub mod f4;
pub mod fglm;
pub mod field_equations;
pub mod hilbert;
pub mod pairs;
pub mod planning;
pub mod reference;
pub mod research;
mod s_polynomial;
// Singular's weighted bases, committed as literals. Test data only: nothing on a shipping path
// reads it, and `weighted_reference_bases::tests` is the differential check #624 asked for.
mod solve;
mod solve_zero_dimensional;
#[cfg(test)]
mod weighted_reference_bases;

pub use buchberger::{
    buchberger, buchberger_with_criteria, buchberger_with_statistics,
    interreduce_by_matrix_for_benchmark, interreduce_for_benchmark,
    leading_monomials_are_pairwise_coprime, Statistics,
};
pub use f4::{
    certify_f4_output, certify_submitted_basis, f4, f4_observed, f4_observed_reported, f4_reported,
    f4_with_options, trace_batches, Allowance, BatchObserver, BudgetApproach, BudgetLine,
    BudgetReport, CacheMode, CertificationReport, ConstructionTimings, DegreeProfile,
    DegreeStatistics, DivmaskCalibration, F4Error, F4Options, F4Statistics, HilbertCounts,
    HilbertSelection, InterreductionRoute, MatrixInterreduction, MatrixRefusal, Provenance,
    ReducerSelection, ReductionStrategy, SelectionLimits, StopKind, SymbolicCounts, DIVMASK_BITS,
};
pub use fglm::{
    classify_ideal, fglm_to_lex, fglm_to_lex_checked, fglm_to_lex_with_options, is_grobner_basis,
    largest_quotient_dimension_within, BorderIndex, BorderStatistics, ColumnTarget, FglmError,
    FglmMemory, FglmOptions, FglmStageTimings, FglmStatistics, IdealClass, MultiplicationOperator,
    OperatorConstruction, OperatorStorage, QuotientAlgebra, QuotientBasis, QuotientStatistics,
    RECOMMENDED_MAX_QUOTIENT_DIMENSION, RECOMMENDED_MAX_SPAN_ENTRIES,
};
pub use field_equations::{
    field_equations, rational_points_by_enumeration, with_field_equations, FieldEquationError,
};
pub use hilbert::{
    is_homogeneous, leading_generators_by_degree, monomials_of_degree, top_forms, DegreeAgreement,
    HilbertComparison, HilbertError, HilbertSeries, SemiregularSeries,
};
pub use pairs::{
    CriterionCounts, CriticalPair, PairCriteria, PairQueue, PairQueueFootprint, PairSchedule,
};
pub use planning::{
    analyze, solve_one_planned, Attempt, Choice, OutcomeClass, PlanBudget, PlannedSolveOptions,
    SolvePlan, SolvePolicy, SystemShape,
};
pub use s_polynomial::s_polynomial;
pub use solve::solve;
pub use solve_zero_dimensional::{
    solve_from_lex_basis, solve_one, solve_one_reported, solve_one_with_options,
    solve_one_with_outcome, solve_zero_dimensional, solve_zero_dimensional_with_options,
    SolveError, SolveOptions, SolveOutcome, SolveStatistics, SolveStrategy,
};

#[cfg(test)]
mod tests {
    use rand::{prelude::StdRng, SeedableRng};

    use crate::{
        fields::{
            Bls12_381FrModulus, Bn254Fr, Bn254FrModulus, Gf256, PrimeFieldElement256,
            PrimeModulus256, Zp2, Zp2147483647,
        },
        grobner::{
            benchmark_systems::{cyclic, planted},
            buchberger, f4, fglm_to_lex, is_grobner_basis, solve_one,
        },
        FiniteField, KnownOrder, MonomialOrder, One, Zero,
    };

    /// The Gröbner stack runs over a coefficient type bounded only by `FiniteField`, with no field
    /// cardinality available at all.
    ///
    /// This is what lets a field wider than a `u128` be a coefficient: the algorithms never ask
    /// for an order, so nothing requires one of them. A `KnownOrder` bound reaching `f4`,
    /// `buchberger` or `fglm_to_lex` fails this at compile time, which is the point of the test —
    /// the assertions below are a sanity check on top of it.
    fn without_cardinality<const N: usize, F: FiniteField>() {
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        let system = cyclic::<N, F>();

        let reference = buchberger(&system, grevlex);
        assert!(is_grobner_basis(&reference, grevlex));

        let basis = f4(&system, grevlex).expect("within the default budgets");
        assert!(is_grobner_basis(&basis, grevlex));

        let lex = fglm_to_lex(&basis, grevlex).expect("cyclic is zero-dimensional");
        assert!(is_grobner_basis(&lex, MonomialOrder::Lexicographic));
    }

    /// F4, Buchberger and FGLM compile and agree without a `KnownOrder` bound.
    #[test]
    fn test_the_grobner_stack_needs_no_field_cardinality() {
        without_cardinality::<3, Zp2147483647>();
    }

    /// The whole pipeline over a wide field: F4, FGLM, and a verified solution.
    ///
    /// Not a smoke test. The planted point is checked against the original system by direct
    /// evaluation, every basis is checked against Buchberger's criterion, the lex basis reached
    /// through FGLM is compared against the one F4 computes directly in lex, and the point the
    /// solver returns is re-evaluated against the original system rather than against the basis
    /// it was derived from.
    ///
    /// Generic over the modulus so the two target fields run the same body and cannot drift.
    fn the_whole_pipeline_over<M: PrimeModulus256>(seed: u64, decimals: [&str; 3]) {
        type Z<M> = PrimeFieldElement256<M>;

        let grevlex = MonomialOrder::GradedReverseLexicographic;
        let lex = MonomialOrder::Lexicographic;

        // Coordinates that are not small, so a truncated or mis-reduced coefficient would show.
        let point: Vec<Z<M>> = decimals
            .iter()
            .map(|d| <Z<M> as FiniteField>::from_str(d).expect("valid decimal"))
            .collect();
        let system = planted::<3, Z<M>>(&point);

        let mut assignment = [Z::<M>::zero(); 3];
        assignment.copy_from_slice(&point);
        for polynomial in &system {
            assert!(
                polynomial.eval(&assignment).is_zero(),
                "the planted point must satisfy {polynomial}"
            );
        }

        let source = f4(&system, grevlex).expect("within the default budgets");
        assert!(is_grobner_basis(&source, grevlex));
        assert_eq!(source, buchberger(&system, grevlex));

        let converted = fglm_to_lex(&source, grevlex).expect("the system is zero-dimensional");
        assert!(is_grobner_basis(&converted, lex));

        // The two routes to lex must agree exactly, both being reduced bases of one ideal.
        let direct = f4(&system, lex).expect("within the default budgets");
        assert_eq!(converted, direct);

        // Root finding is where the field order becomes an exponent, so this is also the check
        // that the limb exponents are right: a truncated order would find no roots at all.
        let mut rng = StdRng::seed_from_u64(seed);
        let solution = solve_one(&system, &mut rng)
            .expect("the system is zero-dimensional")
            .expect("a planted point is a base-field solution");
        for polynomial in &system {
            assert!(
                polynomial.eval(&solution).is_zero(),
                "the returned point must satisfy {polynomial}"
            );
        }
    }

    /// The whole pipeline in characteristic two, which nothing exercised before #218.
    ///
    /// The arithmetic over `BinaryFieldElement` and over `PrimeFieldElement32<2>` is tested and
    /// optimized, but `grep -rl "BinaryFieldElement" src/grobner/ src/linalg/` was empty: F4,
    /// FGLM and `solve_one` over an even-characteristic field had never been run. The stack is
    /// generic over `FiniteField` and ought to work; this is the test that says whether it does.
    ///
    /// Two things make characteristic two different, and both are about `planted` rather than
    /// about the solver. Squaring is a *bijection*, so `legendre_symbol` reports every element a
    /// square and `sqrt` is `x^(q/2)` rather than Tonelli-Shanks. And `x^2 + y^2 = (x + y)^2`
    /// here, so `planted`'s first generator per pair is a **perfect square** and the ideal it
    /// generates is **not radical** — see the deliberate check below. The pipeline is therefore
    /// being asked to recover a point from a nonradical ideal, which is a harder case than the
    /// odd-characteristic twin above faces, not an equivalent one.
    fn the_whole_pipeline_in_characteristic_two<F: KnownOrder>(seed: u64, point: &[F; 3]) {
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        let lex = MonomialOrder::Lexicographic;

        assert_eq!(
            F::characteristic_u128(),
            Some(2),
            "this body is about characteristic two specifically"
        );

        let system = planted::<3, F>(point);

        for polynomial in &system {
            assert!(
                polynomial.eval(point).is_zero(),
                "the planted point must satisfy {polynomial}"
            );
        }

        let source = f4(&system, grevlex).expect("within the default budgets");
        assert!(is_grobner_basis(&source, grevlex));
        assert_eq!(source, buchberger(&system, grevlex));

        let converted = fglm_to_lex(&source, grevlex).expect("the system is zero-dimensional");
        assert!(is_grobner_basis(&converted, lex));

        // Both routes to lex must agree exactly, being reduced bases of one ideal.
        let direct = f4(&system, lex).expect("within the default budgets");
        assert_eq!(converted, direct);

        let mut rng = StdRng::seed_from_u64(seed);
        let solution = solve_one(&system, &mut rng)
            .expect("the system is zero-dimensional")
            .expect("a planted point is a base-field solution");
        for polynomial in &system {
            assert!(
                polynomial.eval(&solution).is_zero(),
                "the returned point must satisfy {polynomial}"
            );
        }
    }

    /// Over GF(2) itself, where `PrimeFieldElement32<2>` keeps the wide-remainder path.
    ///
    /// `2^32` is not invertible modulo an even number, so this is the one declared modulus that
    /// does not reach Montgomery form. The planted point can only have coordinates in {0, 1},
    /// which is why the "coordinates that are not small" precaution of the wide-field twin has no
    /// analogue here: there is nothing to truncate.
    #[test]
    fn test_the_whole_pipeline_over_gf2() {
        let point = [Zp2::one(), Zp2::zero(), Zp2::one()];
        the_whole_pipeline_in_characteristic_two::<Zp2>(4, &point);
    }

    /// Over GF(2^8) under the AES modulus, where multiplication is `PCLMULQDQ` and Barrett.
    #[test]
    fn test_the_whole_pipeline_over_gf256() {
        let point = [Gf256::new(0x57), Gf256::new(0x83), Gf256::new(0xc1)];
        the_whole_pipeline_in_characteristic_two::<Gf256>(5, &point);
    }

    /// `planted` generates a nonradical ideal in characteristic two, and that is why.
    ///
    /// Recorded as its own test because the pipeline test above depends on it and because it is a
    /// property of the *generator*, not of the field support: `x^2 + y^2 - (a^2 + b^2)` is
    /// `((x + y) - (a + b))^2` once the cross terms vanish. A reader who assumed `planted` behaves
    /// the same in every characteristic would mis-read every characteristic-two measurement taken
    /// with it, so the degeneracy is asserted rather than described.
    #[test]
    fn test_planted_degenerates_to_a_square_in_characteristic_two() {
        use crate::{Monomial, MultivariatePolynomial};

        let (a, b) = (Gf256::new(0x57), Gf256::new(0x83));
        let point = [a, b, Gf256::new(0xc1)];
        let system = planted::<3, Gf256>(&point);

        // (x0 + x1) + (a + b), squared. Addition is its own inverse here, so no signs appear.
        let sum: MultivariatePolynomial<3, Gf256> = MultivariatePolynomial::new(&[
            (Monomial::new(&[1, 0, 0]), Gf256::one()),
            (Monomial::new(&[0, 1, 0]), Gf256::one()),
            (Monomial::one(), a + b),
        ]);
        assert_eq!(
            system[0],
            sum.clone() * sum,
            "in characteristic two planted's first generator is a perfect square"
        );

        // The same polynomial over an odd-characteristic field is *not* a square, which is what
        // makes this a fact about the characteristic rather than about `planted`'s shape.
        let odd = planted::<3, Zp2147483647>(&[
            Zp2147483647::new(87),
            Zp2147483647::new(131),
            Zp2147483647::new(193),
        ]);
        let odd_sum: MultivariatePolynomial<3, Zp2147483647> = MultivariatePolynomial::new(&[
            (Monomial::new(&[1, 0, 0]), Zp2147483647::one()),
            (Monomial::new(&[0, 1, 0]), Zp2147483647::one()),
            (
                Monomial::one(),
                Zp2147483647::new(87) + Zp2147483647::new(131),
            ),
        ]);
        assert_ne!(odd[0], odd_sum.clone() * odd_sum);
    }

    /// The milestone's demonstration over BN254's 254-bit scalar field.
    #[test]
    fn test_the_whole_pipeline_over_bn254_fr() {
        the_whole_pipeline_over::<Bn254FrModulus>(
            1,
            ["7", "11", "98765432109876543210987654321098765432"],
        );
    }

    /// The same, over BLS12-381's 255-bit scalar field, whose modulus differs in every limb.
    #[test]
    fn test_the_whole_pipeline_over_bls12_381_fr() {
        the_whole_pipeline_over::<Bls12_381FrModulus>(
            2,
            [
                "3",
                "5",
                "52435875175126190479447740508185965837690552500527637822603658699938581184512",
            ],
        );
    }

    /// A system with no base-field point is reported as no solution, not as an error.
    ///
    /// The non-square is found by testing rather than assumed, since whether a given small
    /// integer is a square differs between the two target fields.
    #[test]
    fn test_a_system_without_a_base_field_point_returns_none_over_bn254_fr() {
        use crate::{Monomial, MultivariatePolynomial};

        let mut rng = StdRng::seed_from_u64(3);

        let mut non_square = None;
        for candidate in 2u64..60 {
            let n = Bn254Fr::new(candidate);
            let system: Vec<MultivariatePolynomial<1, Bn254Fr>> =
                vec![MultivariatePolynomial::new(&[
                    (Monomial::new(&[2]), Bn254Fr::one()),
                    (Monomial::one(), -n),
                ])];
            if let Ok(None) = solve_one(&system, &mut rng) {
                non_square = Some(candidate);
                break;
            }
        }

        let candidate = non_square.expect("some small integer is a non-square modulo p");

        // The companion check: a square *is* solvable, so the `None` above is about this value
        // rather than about the solver failing on every quadratic over a wide field.
        let c = Bn254Fr::new(candidate);
        let square: Vec<MultivariatePolynomial<1, Bn254Fr>> = vec![MultivariatePolynomial::new(&[
            (Monomial::new(&[2]), Bn254Fr::one()),
            (Monomial::one(), -(c * c)),
        ])];
        let [root] = solve_one(&square, &mut rng)
            .expect("solvable")
            .expect("x^2 = c^2 has a base-field root");
        // Either sign is a correct answer, so check by squaring rather than by which came back.
        assert_eq!(root * root, c * c);
    }
}
