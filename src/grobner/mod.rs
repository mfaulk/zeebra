//! Grobner Basis algorithms

pub mod benchmark_systems;
mod buchberger;
pub mod differential;
pub mod f4;
pub mod fglm;
pub mod pairs;
pub mod reference;
mod s_polynomial;
mod solve;
mod solve_zero_dimensional;

pub use buchberger::{
    buchberger, buchberger_with_criteria, buchberger_with_statistics, Statistics,
};
pub use f4::{
    f4, f4_observed, f4_with_options, trace_batches, CacheMode, F4Error, F4Options, F4Statistics,
    ReducerSelection, ReductionStrategy,
};
pub use fglm::{
    classify_ideal, fglm_to_lex, fglm_to_lex_checked, fglm_to_lex_with_options, is_grobner_basis,
    BorderIndex, BorderStatistics, ColumnTarget, FglmError, FglmMemory, FglmOptions,
    FglmStageTimings, FglmStatistics, IdealClass, MultiplicationOperator, OperatorConstruction,
    OperatorStorage, QuotientAlgebra, QuotientBasis, QuotientStatistics,
};
pub use pairs::{CriterionCounts, CriticalPair, PairCriteria, PairQueue};
pub use s_polynomial::s_polynomial;
pub use solve::solve;
pub use solve_zero_dimensional::{
    solve_one, solve_one_with_options, solve_zero_dimensional, solve_zero_dimensional_with_options,
    SolveError, SolveOptions, SolveStrategy,
};

#[cfg(test)]
mod tests {
    use crate::{
        fields::Zp2147483647,
        grobner::{benchmark_systems::cyclic, buchberger, f4, fglm_to_lex, is_grobner_basis},
        FiniteField, MonomialOrder,
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
}
