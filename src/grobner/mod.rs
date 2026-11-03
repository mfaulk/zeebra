//! Grobner Basis algorithms

pub mod benchmark_systems;
mod buchberger;
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
    FglmError, FglmOptions, FglmStatistics, IdealClass, MultiplicationOperator, QuotientAlgebra,
    QuotientBasis,
};
pub use pairs::{CriterionCounts, CriticalPair, PairCriteria, PairQueue};
pub use s_polynomial::s_polynomial;
pub use solve::solve;
pub use solve_zero_dimensional::{
    solve_one, solve_one_with_options, solve_zero_dimensional, solve_zero_dimensional_with_options,
    SolveError, SolveOptions, SolveStrategy,
};
