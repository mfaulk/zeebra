//! Experiment machinery: transformations whose soundness is about what they let you *claim*.
//!
//! Separate from the solvers because the discipline is different. A solver's contract is "this is
//! a Gröbner basis" or "this point satisfies these equations". Everything here produces answers
//! about a *transformed* problem, and the hard part is carrying the right statement back — which
//! is why [`SliceOutcome`] has three variants where a solver has `Option`, and why only one of
//! them says anything about the system you started with.

pub mod slices;
pub mod specialization;

pub use slices::{solve_slice, SliceOutcome};
pub use specialization::{satisfies, specialize, Specialization, SpecializationError};
