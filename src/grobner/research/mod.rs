//! Experiment machinery: transformations whose soundness is about what they let you *claim*.
//!
//! Separate from the solvers because the discipline is different. A solver's contract is "this is
//! a Gröbner basis" or "this point satisfies these equations". Everything here produces answers
//! about a *transformed* problem, and the hard part is carrying the right statement back — which
//! is why [`SliceOutcome`] has three variants where a solver has `Option`, and why only one of
//! them says anything about the system you started with.

pub mod anemoi;
pub mod challenge;
pub mod linear;
pub mod manifest;
pub mod mq;
pub mod poseidon;
pub mod record;
pub mod reorder;
pub mod resultant;
pub mod scoreboard;
pub mod slices;
pub mod specialization;
pub mod univariate_cico;

pub use anemoi::{smallest_primitive_root, Anemoi, AnemoiError, AnemoiParameters, ANEMOI_64_PRIME};
pub use challenge::{
    challenge, dispatch_cico, registry, BenchmarkClass, ChallengeError, ChallengeManifest,
    ChallengeParameters, ChallengeProgram, CicoTarget, CicoVisitor, DisclosedMethod,
    ExternalStatus, Objective, Significance,
};
pub use linear::{eliminate_affine, AffineElimination, Elimination, LinearError};
pub use manifest::{Claim, InstanceManifest, Provenance};
pub use mq::{MqError, MqField, MqInstance, MqVisitor, SUPPORTED_DIMENSIONS};
pub use poseidon::{
    verify_against_trace, CicoInstance, GrainLfsr, Poseidon, PoseidonError, PoseidonParameters,
    PoseidonTrace, KOALABEAR_PRIME,
};
pub use record::{AttemptRecord, ExperimentRecord, Json};
pub use reorder::{ReorderError, RoundLayout, VariableOrder};
pub use resultant::{
    bivariate_resultant, bivariate_resultant_ntt, bivariate_resultant_ntt_with,
    bivariate_resultant_reference, bivariate_resultant_reference_with, cico_bivariate,
    interpolation_route, sylvester_determinant_at, ResultantError, ResultantOptions,
    ResultantRoute, ResultantStages,
};
pub use scoreboard::{
    wilson_interval, Campaign, Comparison, Environment, GrobnerFrontier, Limit, RunOutcome,
    RunRecord, Scoreboard, ScoreboardError, Stage, StageCost,
};
pub use slices::{solve_slice, SliceOutcome};
pub use specialization::{satisfies, specialize, Specialization, SpecializationError};
pub use univariate_cico::{
    cico_univariate, cico_univariate_family, cico_univariate_family_with_stats, degree_bound,
    parametrize, univariate_route, CicoFamily, FamilyError, FamilyStages, UnivariateRoute,
    SYMBOLIC_CROSSOVER,
};
