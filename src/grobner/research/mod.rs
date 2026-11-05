//! Experiment machinery: transformations whose soundness is about what they let you *claim*.
//!
//! Separate from the solvers because the discipline is different. A solver's contract is "this is
//! a Gröbner basis" or "this point satisfies these equations". Everything here produces answers
//! about a *transformed* problem, and the hard part is carrying the right statement back — which
//! is why [`SliceOutcome`] has three variants where a solver has `Option`, and why only one of
//! them says anything about the system you started with.

pub mod linear;
pub mod manifest;
pub mod mq;
pub mod poseidon;
pub mod record;
pub mod reorder;
pub mod slices;
pub mod specialization;

pub use linear::{eliminate_affine, AffineElimination, Elimination, LinearError};
pub use manifest::{Claim, InstanceManifest, Provenance};
pub use mq::{MqError, MqField, MqInstance, MqVisitor, SUPPORTED_DIMENSIONS};
pub use poseidon::{
    verify_against_trace, CicoInstance, GrainLfsr, Poseidon, PoseidonError, PoseidonParameters,
    PoseidonTrace, KOALABEAR_PRIME,
};
pub use record::{AttemptRecord, ExperimentRecord, Json};
pub use reorder::{ReorderError, RoundLayout, VariableOrder};
pub use slices::{solve_slice, SliceOutcome};
pub use specialization::{satisfies, specialize, Specialization, SpecializationError};
