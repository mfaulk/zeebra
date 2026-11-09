//! Experiment machinery: transformations whose soundness is about what they let you *claim*.
//!
//! Separate from the solvers because the discipline is different. A solver's contract is "this is
//! a Gröbner basis" or "this point satisfies these equations". Everything here produces answers
//! about a *transformed* problem, and the hard part is carrying the right statement back — which
//! is why [`SliceOutcome`] has three variants where a solver has `Option`, and why only one of
//! them says anything about the system you started with.

pub mod anemoi;
pub mod anemoi_cico;
pub mod challenge;
pub mod cost_model;
pub mod feistel_mimc;
pub mod feistel_mimc_cico;
pub mod griffin;
pub mod linear;
pub mod manifest;
pub mod mq;
pub mod mq_generator;
pub mod poseidon;
pub mod record;
pub mod reorder;
pub mod rescue_prime;
pub mod rescue_prime_cico;
pub mod resultant;
pub mod row_cost;
pub mod scoreboard;
pub mod slices;
pub mod specialization;
pub mod univariate_cico;

pub use anemoi::{
    smallest_primitive_root, Anemoi, AnemoiError, AnemoiParameters, ANEMOI_64_PRIME,
    ANEMOI_ACICO_PRIME,
};
pub use anemoi_cico::{
    dispatch_anemoi_cico, verify_against_anemoi_trace, AnemoiCico, AnemoiCicoVisitor, AnemoiModel,
};
pub use challenge::{
    challenge, dispatch_cico, proved_acico_quotient_dimension, published_quotient_dimension,
    registry, BenchmarkClass, ChallengeError, ChallengeManifest, ChallengeParameters,
    ChallengeProgram, CicoTarget, CicoVisitor, DisclosedMethod, ExternalStatus, Objective,
    ReferencePoint, Significance,
};
pub use cost_model::{
    retained_run_stems, select_runs_by_stem, Attribution, CostModelBoard, CostRow, Figure,
    FigureBasis, Intermediate, LimitingStage, NextSizeProjection, PredictionError, Quantity,
    RunSelectionError, SchemaError, SelectedRuns, COST_MODEL_HISTORY_CONTRACT,
};
pub use feistel_mimc::{
    FeistelMimc, FeistelMimcError, FeistelMimcParameters,
    BOUNTY_ROUNDS as FEISTEL_MIMC_BOUNTY_ROUNDS, FEISTEL_MIMC_PRIME,
    WITHDRAWN_ROUNDS as FEISTEL_MIMC_WITHDRAWN_ROUNDS,
};
pub use feistel_mimc_cico::{
    dispatch_feistel_mimc_cico, verify_against_feistel_mimc_trace, FeistelMimcCico,
    FeistelMimcCicoVisitor, FeistelMimcModel,
};
pub use griffin::{FixtureError, FreeLunchSystem, FREELUNCH_PRIME, FREELUNCH_R4, FREELUNCH_R5};
pub use linear::{eliminate_affine, AffineElimination, Elimination, LinearError};
pub use manifest::{Claim, InstanceManifest, Provenance};
pub use mq::{MqError, MqField, MqInstance, MqVisitor, SUPPORTED_DIMENSIONS};
pub use mq_generator::{
    read_pi, ConstantColumn, DigitSource, GeneratedMq, MqGeneratorError, MqParameters, MqType,
    ThirtyOne, PI_LENGTH, PI_SHA256,
};
pub use poseidon::{
    verify_against_trace, CicoInstance, GrainLfsr, Poseidon, PoseidonError, PoseidonParameters,
    PoseidonTrace, KOALABEAR_PRIME,
};
pub use record::{AttemptRecord, ExperimentRecord, Json};
pub use reorder::{ReorderError, RoundLayout, VariableOrder};
pub use rescue_prime::{
    BountyInstance, RescuePrime, RescuePrimeError, RescuePrimeParameters, BOUNTY_INSTANCES,
    RESCUE_PRIME_PRIME,
};
pub use rescue_prime_cico::{
    dispatch_rescue_prime_cico, verify_against_rescue_prime_trace, RescuePrimeCico,
    RescuePrimeCicoVisitor,
};
pub use resultant::{
    bivariate_resultant, bivariate_resultant_ntt, bivariate_resultant_ntt_with,
    bivariate_resultant_predicted, bivariate_resultant_reference,
    bivariate_resultant_reference_with, cico_bivariate, fit_power_law, interpolation_route,
    predicted_resultant_degree, random_bivariate, sylvester_determinant_at,
    time_sylvester_determinants, DegreeSource, DeterminantBatch, DeterminantKernel, PowerLawFit,
    ResultantError, ResultantOptions, ResultantRoute, ResultantStages,
};
pub use row_cost::{
    determinant_core_ms, euclidean_core_ms, kernel_core_ms, specialization_operations,
    width_penalty, CostTerm, ResultantRowCost, RowVerdict, TermBasis, ABOVE_L2_EXPONENT,
    CORE_TIME_PER_DOUBLING, DETERMINANT_MS_AT_162, EUCLID_EXPONENT, EUCLID_MEASURED_ORDER,
    EUCLID_REMAINDER_MS_AT_1458, EUCLID_SPECIALIZE_NS_PER_OPERATION, MEASURED_ORDER,
};
pub use scoreboard::{
    colliding_run_file, wilson_interval, Campaign, Comparison, Environment, GrobnerFrontier, Limit,
    RunFileCollision, RunOutcome, RunRecord, Scoreboard, ScoreboardError, Stage, StageCost,
    BEST_CONTRACT, HISTORY_CONTRACT, SOLVED_CONTRACT,
};
pub use slices::{solve_slice, SliceOutcome};
pub use specialization::{satisfies, specialize, Specialization, SpecializationError};
pub use univariate_cico::{
    cico_univariate, cico_univariate_family, cico_univariate_family_with_stats, degree_bound,
    parametrize, univariate_route, CicoFamily, FamilyError, FamilyStages, UnivariateRoute,
    SYMBOLIC_CROSSOVER,
};
