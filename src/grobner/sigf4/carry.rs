//! #1076 (M35 WP C, plan §7.3): end a signature run at a fixed degree and finish with
//! conventional F4, either from the original inputs (restart) or from the elements at minimal
//! leads plus the inputs (continue). Comparing the two at one boundary measures what carrying the
//! prefix is worth, before any online boundary rule is fitted.
//!
//! Soundness is `lead_ideal.rs`'s: every element lies in the input ideal, so F4 over any subset of
//! them together with the inputs returns the same reduced basis. Every ordinary pair obligation
//! is rebuilt by F4; none is dropped on the strength of a completed degree.
//!
//! Cost accounting. The engine state is dropped before F4 starts, so the two are never held at
//! once, and F4 gets the caller's workers and the remaining wall budget.

use std::time::Duration;

use super::SigF4Options;
use crate::grobner::f4::{F4Options, ParallelForward, ParallelSymbolic};

/// Where the conventional leg starts from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CarryMode {
    /// F4 from the original inputs only: the prefix is paid for and discarded.
    Restart,
    /// F4 from the elements at minimal leads plus the inputs.
    Continue,
}

/// Hand off once every signature degree up to `degree` is finished and work remains.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Carry {
    pub degree: u64,
    pub mode: CarryMode,
}

/// What a carried run did. Absent when the boundary was never reached with work left.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CarryReport {
    /// The last signature degree the engine finished.
    pub degree: u64,
    /// Polynomials F4 was given, inputs included.
    pub seed: usize,
    /// Signature-basis elements when the run stopped.
    pub signature_elements: usize,
    /// Wall time from the engine's start to the handoff.
    pub prefix: Duration,
    /// Wall time of the conventional leg.
    pub conventional: Duration,
    /// Conventional F4's batches.
    pub conventional_batches: usize,
}

impl Carry {
    /// Due after a batch of `degree` when the queue's next degree is past both it and the boundary.
    pub(super) fn due(self, degree: u64, next: Option<u64>) -> bool {
        degree >= self.degree && next.is_some_and(|d| d > degree)
    }
}

/// Conventional F4's options for the leg: shipping defaults on the engine's workers, under
/// `wall`.
pub(super) fn conventional_options(options: &SigF4Options, wall: Option<Duration>) -> F4Options {
    let workers = options.workers.max(1);
    F4Options {
        max_wall_time: wall,
        parallel_forward: if workers == 1 {
            ParallelForward::Serial
        } else {
            ParallelForward::Auto {
                max_workers: workers,
            }
        },
        parallel_symbolic: if workers == 1 {
            ParallelSymbolic::Serial
        } else {
            ParallelSymbolic::Auto {
                max_workers: workers,
            }
        },
        ..F4Options::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The handoff waits for the boundary degree to finish and never fires with the queue empty.
    #[test]
    fn due_only_after_the_boundary_degree_with_work_left() {
        let carry = Carry {
            degree: 5,
            mode: CarryMode::Continue,
        };
        assert!(!carry.due(4, Some(5)));
        assert!(!carry.due(5, Some(5)));
        assert!(carry.due(5, Some(6)));
        assert!(carry.due(7, Some(9)));
        assert!(!carry.due(5, None));
    }

    /// One engine worker gives a serial F4 leg, so a one-worker arm is not silently parallel.
    #[test]
    fn one_worker_leg_is_serial() {
        let options = SigF4Options::default();
        let f4 = conventional_options(&options, None);
        assert_eq!(f4.parallel_forward, ParallelForward::Serial);
        assert_eq!(f4.parallel_symbolic, ParallelSymbolic::Serial);
        let four = conventional_options(
            &SigF4Options {
                workers: 4,
                ..SigF4Options::default()
            },
            Some(Duration::from_secs(3)),
        );
        assert_eq!(four.parallel_forward.max_workers(), 4);
        assert_eq!(four.max_wall_time, Some(Duration::from_secs(3)));
    }
}
