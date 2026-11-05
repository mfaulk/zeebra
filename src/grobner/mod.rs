//! Grobner Basis algorithms

pub mod benchmark_systems;
mod buchberger;
pub mod differential;
pub mod f4;
pub mod fglm;
pub mod pairs;
pub mod planning;
pub mod reference;
mod s_polynomial;
mod solve;
mod solve_zero_dimensional;

pub use buchberger::{
    buchberger, buchberger_with_criteria, buchberger_with_statistics, Statistics,
};
pub use f4::{
    f4, f4_observed, f4_reported, f4_with_options, trace_batches, CacheMode, F4Error, F4Options,
    F4Statistics, ReducerSelection, ReductionStrategy,
};
pub use fglm::{
    classify_ideal, fglm_to_lex, fglm_to_lex_checked, fglm_to_lex_with_options, is_grobner_basis,
    BorderIndex, BorderStatistics, ColumnTarget, FglmError, FglmMemory, FglmOptions,
    FglmStageTimings, FglmStatistics, IdealClass, MultiplicationOperator, OperatorConstruction,
    OperatorStorage, QuotientAlgebra, QuotientBasis, QuotientStatistics,
};
pub use pairs::{CriterionCounts, CriticalPair, PairCriteria, PairQueue};
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
            Bls12_381FrModulus, Bn254Fr, Bn254FrModulus, PrimeFieldElement256, PrimeModulus256,
            Zp2147483647,
        },
        grobner::{
            benchmark_systems::{cyclic, planted},
            buchberger, f4, fglm_to_lex, is_grobner_basis, solve_one,
        },
        FiniteField, MonomialOrder, One, Zero,
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
