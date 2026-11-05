//! Deciding *how* to solve a system, and reporting what the decision cost.
//!
//! Separate from the solvers themselves, which keep their existing contracts exactly. Everything
//! here is either a diagnostic or an opt-in policy; nothing in `solve_zero_dimensional` changes
//! behaviour because this module exists.
//!
//! The split follows the knowledge boundary rather than the call graph. [`analysis`] is what can be
//! known before a Gröbner basis — counts and structure, no dimension claims. Quotient dimension,
//! staircase shape, and therefore every real feasibility question are only answerable *after* a
//! basis exists, and a planner that forgets which side of that line it is on will infer dimension
//! from equation counts. §3.1 of `docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md` is the argument.

pub mod analysis;

pub use analysis::{analyze, SystemShape};
