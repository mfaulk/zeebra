//! Plans keep failed work as well as successful attempts, without carrying field type parameters.

use std::{fmt::Display, time::Duration};

use crate::grobner::{SolveError, SolveStatistics, SolveStrategy, SystemShape};

/// Which mathematical fact an attempt established, without the point.
///
/// The type-parameter-free shadow of [`SolveOutcome`](crate::grobner::SolveOutcome).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OutcomeClass {
    /// A verified point. The point itself is in the planner's `Result`.
    Point,
    /// Zero-dimensional, with no point over the base field.
    NoBaseFieldPoint,
    /// `1` is in the ideal.
    Inconsistent,
}

/// Why the planner chose a route.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Choice {
    /// What the caller asked for, under [`SolvePolicy::Explicit`](super::SolvePolicy::Explicit).
    Explicit,

    /// The caller requested grevlex classification before direct lex elimination.
    ClassifyBeforeLex,

    /// The conservative policy's opening move.
    ///
    /// Grevlex-then-FGLM, because **a refusal from that route is cheap by construction**: FGLM's
    /// binding budget is computed from `D` and checked before anything is allocated, while F4's is
    /// discovered during elimination and so costs the whole elimination up to the crossing. §4.3
    /// of `docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md` measures the difference at 28.3 s
    /// against 36 ms.
    ConservativeOpening,

    /// The alternative, after the first route crossed a budget.
    FallbackAfterResourceLimit,

    /// The alternative, after a *computed* `D` put the conversion outside its budget.
    ///
    /// Not a failure: nothing was spent on the conversion. The source basis and its quotient basis
    /// were enough to know it could not fit, which is the one decision in the policy made on a
    /// measured quantity rather than an estimate.
    ConversionRuledOut {
        /// `D`, counted.
        dimension: usize,
        /// What the dense blocks would have needed, in the unit of the budget that bound.
        needed: usize,
        /// Which budget bound: `"span cells"` or `"span bytes"`.
        budget: &'static str,
    },
}

impl Display for Choice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Explicit => write!(f, "the caller asked for it"),
            Self::ClassifyBeforeLex => {
                write!(f, "classify a grevlex basis before direct lex elimination")
            }
            Self::ConservativeOpening => {
                write!(
                    f,
                    "conservative policy: a cheap refusal is worth more than a fast win"
                )
            }
            Self::FallbackAfterResourceLimit => {
                write!(f, "the previous route crossed a budget")
            }
            Self::ConversionRuledOut {
                dimension,
                needed,
                budget,
            } => write!(
                f,
                "conversion ruled out from a counted D = {} needing {} {}",
                dimension, needed, budget
            ),
        }
    }
}

/// One route, run or declined.
#[derive(Clone, Debug)]
pub struct Attempt {
    /// Which route.
    pub strategy: SolveStrategy,

    /// Why the planner picked it.
    pub choice: Choice,

    /// What it spent. Present even when it failed — that is what M21-C's reported entry points
    /// are for, and a fallback that could not account for discarded work would misreport the
    /// policy's cost as the winning route's cost.
    pub statistics: SolveStatistics,

    /// Wall clock for this attempt alone.
    pub elapsed: Duration,

    /// What it established, or why it did not.
    pub result: Result<OutcomeClass, SolveError>,
}

impl Attempt {
    /// Whether this attempt established a mathematical fact.
    pub fn succeeded(&self) -> bool {
        self.result.is_ok()
    }
}

/// Every route the planner considered, in order, with what each cost.
///
/// The thing to print or record. A plan with a successful last attempt still carries the failed
/// ones, which is the point: the policy's cost is the whole plan, never the winning attempt alone.
#[derive(Clone, Debug)]
pub struct SolvePlan {
    /// The cheap structural pass, before anything was computed.
    pub shape: SystemShape,

    /// Routes attempted or declined, oldest first. Empty only when the structural pass alone
    /// settled the question — a nonzero constant generator.
    pub attempts: Vec<Attempt>,

    /// A route the policy would have tried but did not, because the shared budget was spent.
    ///
    /// Carried so that "we stopped because we ran out" is distinguishable from "there was nothing
    /// else to try".
    pub declined: Option<(SolveStrategy, &'static str)>,

    /// An outcome the structural pass settled before any route ran.
    ///
    /// A nonzero constant generator puts 1 in the ideal, which is conclusive and costs nothing —
    /// so the plan has no attempts and [`Self::outcome`], which reads the last attempt, would
    /// otherwise report `None` for a mathematically decided result.
    pub preflight: Option<OutcomeClass>,
}

impl SolvePlan {
    /// Wall clock across every attempt, including the ones that failed.
    ///
    /// The figure to quote as the policy's cost. On a system where the first route is refused
    /// expensively this is dominated by work that produced nothing, and saying so is the point.
    pub fn total_elapsed(&self) -> Duration {
        self.attempts.iter().map(|a| a.elapsed).sum()
    }

    /// Wall clock spent on attempts that established nothing.
    pub fn discarded_elapsed(&self) -> Duration {
        self.attempts
            .iter()
            .filter(|a| !a.succeeded())
            .map(|a| a.elapsed)
            .sum()
    }

    /// F4 batches summed over every attempt, discarded work included.
    ///
    /// Unlike a peak, batches are *spent*: they add across attempts and are therefore what a
    /// shared budget can meaningfully bound. See [`PlanBudget`](super::PlanBudget).
    ///
    /// A dimension diagnosis counts too — it is a real F4 run, and work the shared budget could
    /// otherwise be escaped through.
    pub fn total_batches(&self) -> usize {
        self.attempts
            .iter()
            .flat_map(|a| [a.statistics.f4.as_ref(), a.statistics.diagnosis.as_ref()])
            .flatten()
            .map(|f| f.batches)
            .sum()
    }

    /// The largest single-stage byte estimate any attempt reached.
    ///
    /// A **maximum, not a sum**: one attempt's matrices are freed before the next begins, so the
    /// peaks are not live together. This is the one place the arithmetic differs from
    /// [`Self::total_batches`], and conflating the two is how a shared budget comes to mean
    /// nothing.
    pub fn peak_estimated_bytes(&self) -> usize {
        self.attempts
            .iter()
            .map(|a| a.statistics.estimated_peak_bytes())
            .max()
            .unwrap_or(0)
    }

    /// What the plan established, if anything.
    ///
    /// The last attempt's result, or [`Self::preflight`] when the structural pass settled it and
    /// no route ran.
    pub fn outcome(&self) -> Option<OutcomeClass> {
        match self.attempts.last() {
            Some(attempt) => attempt.result.ok(),
            None => self.preflight,
        }
    }

    /// Whether every permitted route was tried and none established anything.
    ///
    /// **Inconclusive, not "no solution".** Nothing here licenses any statement about whether the
    /// system has a point; it says this configuration could not find out.
    ///
    /// False when the structural pass settled the question, which is conclusive without an
    /// attempt.
    pub fn is_inconclusive(&self) -> bool {
        self.preflight.is_none()
            && !self.attempts.is_empty()
            && self.attempts.iter().all(|a| !a.succeeded())
    }
}

impl Display for SolvePlan {
    /// The decision log, one block per attempt.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "Structure: {} variables, {} generators, max degree {}{}",
            self.shape.variables,
            self.shape.generators,
            self.shape.max_degree,
            if self.shape.constant_contradiction {
                ", a nonzero constant generator"
            } else {
                ""
            }
        )?;

        if let Some(class) = self.preflight {
            writeln!(
                f,
                "No route attempted: the structure settled it — {:?}",
                class
            )?;
        } else if self.attempts.is_empty() {
            writeln!(f, "No route attempted.")?;
        }

        for (index, attempt) in self.attempts.iter().enumerate() {
            writeln!(f)?;
            writeln!(f, "Attempt {}: {:?}", index + 1, attempt.strategy)?;
            writeln!(f, "  Chosen because: {}", attempt.choice)?;
            if let Some(stats) = attempt.statistics.f4.as_ref() {
                writeln!(
                    f,
                    "  Gröbner: {} batches, largest matrix {}x{}, {} peak entries ({} bytes)",
                    stats.batches,
                    stats.max_matrix_rows,
                    stats.max_matrix_columns,
                    stats.max_live_nonzeros,
                    stats.peak_live_bytes()
                )?;
            }
            if let Some(stats) = attempt.statistics.diagnosis.as_ref() {
                if attempt.choice == Choice::ClassifyBeforeLex {
                    writeln!(
                        f,
                        "  Preclassification: grevlex F4 used {} batches",
                        stats.batches
                    )?;
                } else {
                    writeln!(
                    f,
                    "  Diagnosis: a grevlex basis in {} batches, to tell a crossed budget from a \
                     positive-dimensional ideal",
                    stats.batches
                )?;
                }
            }
            if let Some(stats) = attempt.statistics.fglm.as_ref() {
                writeln!(
                    f,
                    "  Conversion: D = {}, {} estimated bytes",
                    stats.quotient_dimension,
                    stats.estimated_bytes()
                )?;
            }
            writeln!(f, "  Elapsed: {:?}", attempt.elapsed)?;
            match &attempt.result {
                Ok(class) => writeln!(f, "  Result: {:?}", class)?,
                Err(e) => writeln!(f, "  Result: inconclusive — {}", e)?,
            }
        }

        if let Some((strategy, why)) = self.declined {
            writeln!(f)?;
            writeln!(f, "Not attempted: {:?} — {}", strategy, why)?;
        }

        writeln!(f)?;
        write!(
            f,
            "Total: {:?} over {} attempt(s), {:?} of it discarded; {} batches, {} peak bytes",
            self.total_elapsed(),
            self.attempts.len(),
            self.discarded_elapsed(),
            self.total_batches(),
            self.peak_estimated_bytes()
        )
    }
}
