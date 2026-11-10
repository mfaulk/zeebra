//! Transformations of a polynomial system whose soundness is about what they let you *claim*.
//!
//! A solver's contract is "this is a Gröbner basis" or "this point satisfies these equations".
//! Everything here produces answers about a *transformed* problem — fewer variables after affine
//! elimination, some variables fixed by specialization, the variables relabelled — and the hard
//! part is carrying the right statement back. That is why [`SliceOutcome`] has three variants
//! where a solver has `Option`, and why only one of them says anything about the system you
//! started with.

pub mod affine;
pub mod reorder;
pub mod slices;
pub mod specialization;

pub use affine::{eliminate_affine, AffineElimination, Elimination, LinearError};
pub use reorder::{ReorderError, VariableOrder};
pub use slices::{solve_slice, SliceOutcome};
pub use specialization::{satisfies, specialize, Specialization, SpecializationError};
