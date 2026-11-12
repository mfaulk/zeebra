//! Subprocess algebra comparands with explicit capabilities, supervised limits and checked identity.
//!
//! GPL engines run only in separate processes; none is linked into the MIT library. Adapters
//! distinguish unsupported inputs, resource stops and failures from timing evidence. See
//! `docs/research/external-comparison-protocol.md` and `external-provenance-policy.md`.

#[cfg(feature = "external-runners")]
pub mod board;
#[cfg(feature = "external-runners")]
pub mod contract;
#[cfg(feature = "external-runners")]
pub mod corpus;
#[cfg(feature = "external-runners")]
pub mod grobx;
#[cfg(feature = "external-runners")]
pub mod groebner_jl;
#[cfg(feature = "external-runners")]
pub mod groebner_rs;
#[cfg(feature = "external-runners")]
pub mod msolve;
pub mod process;
#[cfg(feature = "external-runners")]
pub mod sagebrush;
#[cfg(feature = "external-runners")]
pub mod singular;
#[cfg(feature = "external-runners")]
pub mod sylvester;
#[cfg(feature = "external-runners")]
pub mod zeebra;

#[cfg(feature = "external-runners")]
pub use board::{
    BoardError, CompetitiveBoard, CompetitiveRecord, EngineRatio, Outcome, Speedup,
    COMPETITIVE_HISTORY_CONTRACT,
};
#[cfg(feature = "external-runners")]
pub use contract::{
    order_from_tag, order_tag, Answer, Disagreement, ExternalSolver, FieldSpec, Instance,
    Invariants, LimitStop, Limits, Measurement, NotComparable, RunFailure, RunReport, RunStatus,
    Support, Task, ToolVersion, Unsupported, Verification,
};
#[cfg(feature = "external-runners")]
pub use corpus::{
    cyclic_instance, instance, katsura_instance, CorpusEntry, Rung, ALTERNATE_CHARACTERISTIC,
    GENERATED_CHARACTERISTICS, REFERENCE_CHARACTERISTIC,
};
#[cfg(feature = "external-runners")]
pub use grobx::GrobxSolver;
#[cfg(feature = "external-runners")]
pub use groebner_jl::GroebnerJlSolver;
#[cfg(feature = "external-runners")]
pub use groebner_rs::GroebnerRsSolver;
#[cfg(feature = "external-runners")]
pub use msolve::MsolveSolver;
pub use process::{
    read_output, CpuBasis, Invocation, ProcessMeasurement, RssBasis, RssPolicy, SpawnError,
    Supervisor,
};
#[cfg(feature = "external-runners")]
pub use sagebrush::SagebrushSolver;
#[cfg(feature = "external-runners")]
pub use singular::SingularSolver;
#[cfg(feature = "external-runners")]
pub use sylvester::SylvesterSolver;
#[cfg(feature = "external-runners")]
pub use zeebra::ZeebraSolver;
