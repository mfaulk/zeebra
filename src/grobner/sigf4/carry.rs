//! #1076 (M35 WP C, plan §7.3): end a signature run at a fixed degree and finish with
//! conventional F4, either from the original inputs (restart) or from the elements at minimal
//! leads plus the inputs (continue). Comparing the two at one boundary measures what carrying the
//! prefix is worth, before any online boundary rule is fitted.
//!
//! Soundness is `lead_ideal.rs`'s: every element lies in the input ideal, so F4 over any subset of
//! them together with the inputs returns the same reduced basis. Every ordinary pair obligation
//! is rebuilt by F4; none is dropped on the strength of a completed degree.
//!
//! The online boundary (`Boundary::LeadFall`) hands off after the first finished degree at which
//! the number of minimal leads falls below its running maximum: lower-degree leads have arrived
//! and dominate earlier ones. On #1076's development rows that is where carrying pays (Cyclic-7 at
//! 12, Cyclic-8 at 13), and it never fires on the Eco or Katsura controls.
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

/// When the signature run stops. Either way only after a finished degree with work left.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Boundary {
    /// Once every degree up to this one is finished.
    Degree(u64),
    /// Once the minimal-lead count falls below its running maximum.
    LeadFall,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Carry {
    pub boundary: Boundary,
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

/// A run's boundary and what it has seen.
pub(super) struct CarryStop {
    pub(super) carry: Carry,
    most_leads: usize,
}

impl CarryStop {
    pub(super) fn new(carry: Carry) -> Self {
        Self {
            carry,
            most_leads: 0,
        }
    }

    /// After a batch of `degree`, with the queue's next degree `next`; `leads` counts the minimal
    /// leads and is called only once a degree is finished under `LeadFall`.
    pub(super) fn due(
        &mut self,
        degree: u64,
        next: Option<u64>,
        leads: impl FnOnce() -> usize,
    ) -> bool {
        if !next.is_some_and(|d| d > degree) {
            return false;
        }
        match self.carry.boundary {
            Boundary::Degree(boundary) => degree >= boundary,
            Boundary::LeadFall => {
                let leads = leads();
                self.most_leads = self.most_leads.max(leads);
                leads < self.most_leads
            }
        }
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

    fn stop(boundary: Boundary) -> CarryStop {
        CarryStop::new(Carry {
            boundary,
            mode: CarryMode::Continue,
        })
    }

    /// The handoff waits for the boundary degree to finish and never fires with the queue empty.
    #[test]
    fn due_only_after_the_boundary_degree_with_work_left() {
        let mut carry = stop(Boundary::Degree(5));
        assert!(!carry.due(4, Some(5), || 0));
        assert!(!carry.due(5, Some(5), || 0));
        assert!(carry.due(5, Some(6), || 0));
        assert!(carry.due(7, Some(9), || 0));
        assert!(!carry.due(5, None, || 0));
    }

    /// `LeadFall` fires at the first finished degree whose minimal-lead count is below the most
    /// seen, never on a growing count, and counts only at finished degrees.
    #[test]
    fn lead_fall_fires_when_the_count_drops_below_its_maximum() {
        let mut carry = stop(Boundary::LeadFall);
        assert!(!carry.due(3, Some(3), || unreachable!("degree 3 is not finished")));
        for (degree, leads) in [(3, 10), (4, 40), (5, 40)] {
            assert!(!carry.due(degree, Some(degree + 1), || leads));
        }
        assert!(carry.due(6, Some(7), || 39));
        let mut growing = stop(Boundary::LeadFall);
        assert!((1..30).all(|d| !growing.due(d, Some(d + 1), || d as usize)));
        assert!(!stop(Boundary::LeadFall).due(6, None, || unreachable!()));
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
