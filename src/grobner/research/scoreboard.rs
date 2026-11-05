//! What one run established about one registered problem, and what two runs may be compared on.
//!
//! The layer above [`ExperimentRecord`]. An experiment record says what a solve cost; a
//! [`RunRecord`] says **which public problem** that was, under which formulation, on which machine,
//! and what the result is allowed to claim. It carries the challenge's identity digest rather than
//! only its name, which is what makes the one rule this module exists for enforceable:
//!
//! > a comparison across two different mathematical problems is refused, not rendered.
//!
//! # What is deliberately not here
//!
//! **A single score.** [`Scoreboard::best`] is keyed by problem and never aggregates across
//! [`BenchmarkClass`], because a `t = 2` planted witness and a `t = 16` official witness are not
//! summable in any direction.
//!
//! **A ranking of unfinished runs.** A run that stopped at a resource limit records the limit, the
//! degree it reached and the last completed stage. It is *not* scored against another unfinished
//! run: reaching a higher degree does not imply less work remains, so "further" is not "better" and
//! the type refuses to pretend otherwise — `best` returns witnesses only, and unfinished runs are
//! reported beside them as what they are.
//!
//! **Floats.** As [`Json`], and for the same reason. A ratio is two integers; a speedup is in
//! per-mille, an interval in basis points.

use std::{
    collections::BTreeMap,
    fmt::{Display, Formatter},
    time::Duration,
};

use crate::grobner::{
    f4::{DegreeProfile, F4Statistics},
    research::{
        challenge::{BenchmarkClass, ChallengeManifest, Significance},
        record::{ExperimentRecord, Json},
    },
};

/// Where a run stopped, when it stopped without an answer.
///
/// The plan's "limiting resource and last fully completed stage", as a type rather than as a
/// sentence, so a report cannot omit it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Limit {
    /// Which bound bound: `"max_matrix_columns"`, `"max_live_bytes"`, `"span_storage"`, …
    pub resource: String,

    /// The error in the solver's own words.
    pub detail: String,

    /// The pair degree F4 had reached, when a Gröbner stage was running.
    pub degree: Option<u64>,

    /// The last stage that ran to completion.
    pub last_completed_stage: Stage,
}

impl Display for Limit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ({}", self.resource, self.detail)?;
        if let Some(degree) = self.degree {
            write!(f, ", at degree {}", degree)?;
        }
        write!(f, "; last completed stage {})", self.last_completed_stage)
    }
}

/// What a run produced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RunOutcome {
    /// A witness, checked by the problem's independent verifier.
    VerifiedWitness,

    /// A candidate that the independent verifier **rejected**. A defect, not an absence.
    WitnessRejected,

    /// Zero-dimensional with no point over the base field. A correct answer about this instance.
    NoBaseFieldPoint,

    /// `1` is in the ideal.
    Inconsistent,

    /// A completed Gröbner basis and no witness: positive-dimensional, or none was attempted.
    BasisOnly,

    /// A specialized slice has no point, which says **nothing** about the problem it is a slice of.
    ///
    /// Distinct from [`Self::NoBaseFieldPoint`] and [`Self::Inconsistent`], and the distinction is
    /// load-bearing: a slice is `I + ⟨x_i − a_i⟩`, so a witness on it *is* a witness for the
    /// original system, and an empty slice is a fact about the slice alone. Only exhausting every
    /// `q^|S|` slice would settle the original, which is M21-E's rule. A run that reported an empty
    /// slice as "no base-field point" would be claiming the problem has no solution.
    SliceEstablishedNothing,

    /// Stopped at a bound.
    StoppedAtLimit(Limit),
}

impl RunOutcome {
    /// The stable name a consumer keys on.
    pub fn name(&self) -> &'static str {
        match self {
            Self::VerifiedWitness => "verified_witness",
            Self::WitnessRejected => "witness_rejected",
            Self::NoBaseFieldPoint => "no_base_field_point",
            Self::Inconsistent => "inconsistent",
            Self::BasisOnly => "basis_only",
            Self::SliceEstablishedNothing => "slice_established_nothing",
            Self::StoppedAtLimit(_) => "stopped_at_limit",
        }
    }

    /// Whether this is a witness that passed independent verification.
    pub fn is_verified_witness(&self) -> bool {
        matches!(self, Self::VerifiedWitness)
    }

    /// A table-width summary: the bound and the degree, without the solver's whole sentence.
    ///
    /// `Display` keeps the sentence, because a record read on its own should carry the detail; a
    /// table cell holding sixty words of it is unreadable, and the detail is a field away in the
    /// JSON.
    pub fn short(&self) -> String {
        match self {
            Self::StoppedAtLimit(limit) => match limit.degree {
                Some(degree) => format!("stopped: {} at degree {}", limit.resource, degree),
                None => format!("stopped: {}", limit.resource),
            },
            other => other.to_string(),
        }
    }
}

impl Display for RunOutcome {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::VerifiedWitness => write!(f, "verified witness"),
            Self::WitnessRejected => write!(f, "WITNESS REJECTED"),
            Self::NoBaseFieldPoint => write!(f, "no base-field point"),
            Self::Inconsistent => write!(f, "inconsistent"),
            Self::BasisOnly => write!(f, "basis only, no witness"),
            Self::SliceEstablishedNothing => {
                write!(
                    f,
                    "the slice is empty, which says nothing about the problem"
                )
            }
            Self::StoppedAtLimit(limit) => write!(f, "stopped: {}", limit),
        }
    }
}

/// A pipeline stage, measured separately because a total would hide the one that dominates.
///
/// M20 measured that over a wide field the cost is not in the matrices, and the EF program's
/// Gröbner request is explicitly for per-stage cost and memory.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum Stage {
    /// Building the polynomial system, including any transformation applied to it.
    Generation,
    /// The Gröbner basis.
    Grobner,
    /// Elimination by something that is not a Gröbner basis — a resultant, say.
    ///
    /// Its own stage rather than reported as `Grobner`, because the point of measuring an
    /// alternative elimination is that it is not that one.
    Elimination,
    /// Monomial-order conversion.
    Conversion,
    /// Univariate factorization and root finding.
    Univariate,
    /// The independent check of a candidate.
    Verification,
    /// Nothing ran.
    Nothing,
}

impl Stage {
    /// The stable name.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Generation => "generation",
            Self::Grobner => "grobner",
            Self::Elimination => "elimination",
            Self::Conversion => "conversion",
            Self::Univariate => "univariate",
            Self::Verification => "verification",
            Self::Nothing => "nothing",
        }
    }

    /// The stage with this stable name.
    pub fn named(name: &str) -> Option<Self> {
        [
            Self::Generation,
            Self::Grobner,
            Self::Elimination,
            Self::Conversion,
            Self::Univariate,
            Self::Verification,
            Self::Nothing,
        ]
        .into_iter()
        .find(|stage| stage.name() == name)
    }
}

impl Display for Stage {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// One stage's cost.
#[derive(Clone, Debug)]
pub struct StageCost {
    /// Which stage.
    pub stage: Stage,

    /// Wall clock for this stage alone.
    pub elapsed: Duration,

    /// The stage's own peak byte **estimate**, where it has one. Not a process measurement.
    pub estimated_peak_bytes: Option<usize>,

    /// Stage-specific integers: matrix dimensions, a quotient dimension, a polynomial degree.
    pub detail: Vec<(String, i128)>,
}

impl StageCost {
    /// A stage that ran for `elapsed` and reports nothing else.
    pub fn new(stage: Stage, elapsed: Duration) -> Self {
        Self {
            stage,
            elapsed,
            estimated_peak_bytes: None,
            detail: Vec::new(),
        }
    }

    /// Add one named integer.
    pub fn with(mut self, key: impl Into<String>, value: impl Into<i128>) -> Self {
        self.detail.push((key.into(), value.into()));
        self
    }

    /// Add the stage's byte estimate.
    pub fn with_estimated_bytes(mut self, bytes: usize) -> Self {
        self.estimated_peak_bytes = Some(bytes);
        self
    }

    /// The cost as JSON.
    pub fn to_json(&self) -> Json {
        let mut fields = vec![
            ("stage", Json::string(self.stage.name())),
            ("elapsed_nanos", Json::nanos(self.elapsed)),
            (
                "estimated_peak_bytes",
                match self.estimated_peak_bytes {
                    Some(bytes) => Json::size(bytes),
                    None => Json::Null,
                },
            ),
        ];
        fields.push((
            "detail",
            Json::Object(
                self.detail
                    .iter()
                    .map(|(k, v)| (k.clone(), Json::Int(*v)))
                    .collect(),
            ),
        ));
        Json::object(fields)
    }
}

/// How far the algebra got, for a problem with no witness.
///
/// The plan's group B. Every field here is a fact about one computation on one machine; none of
/// them is a fraction of the work remaining, and `highest_completed_degree` in particular is a
/// diagnostic rather than a progress bar.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct GrobnerFrontier {
    /// Whether the basis computation finished.
    pub completed: bool,

    /// The highest lcm degree any pair was selected at.
    pub max_pair_degree: u64,

    /// The highest degree whose work finished before the limit was crossed.
    ///
    /// `None` when no degree finished, which is a different statement from zero.
    pub highest_completed_degree: Option<u64>,

    /// The largest Macaulay matrix.
    pub max_matrix_rows: usize,

    /// Its width, which need not come from the same matrix.
    pub max_matrix_columns: usize,

    /// Peak live nonzero entries.
    pub peak_live_nonzeros: usize,

    /// Peak live bytes, estimated from the entry count and the field's entry size.
    pub peak_estimated_bytes: usize,

    /// Pairs that reached a matrix.
    pub pairs_reduced: usize,

    /// Basis elements appended before interreduction.
    pub elements_added: usize,

    /// `D = dim_F R/I`, when something established it.
    pub quotient_dimension: Option<usize>,
}

impl GrobnerFrontier {
    /// Read the frontier off F4's statistics.
    ///
    /// `completed` is the caller's to state, because the statistics look the same whether the
    /// computation returned a basis or stopped: F4 records what it did either way, and only the
    /// `Result` says which happened.
    pub fn of(statistics: &F4Statistics, completed: bool) -> Self {
        Self {
            completed,
            max_pair_degree: statistics.max_pair_degree,
            highest_completed_degree: None,
            max_matrix_rows: statistics.max_matrix_rows,
            max_matrix_columns: statistics.max_matrix_columns,
            peak_live_nonzeros: statistics.max_live_nonzeros,
            peak_estimated_bytes: statistics.max_estimated_bytes,
            pairs_reduced: statistics.pairs_reduced,
            elements_added: statistics.elements_added,
            quotient_dimension: None,
        }
    }

    /// Fill in the highest completed degree from a degree profile.
    ///
    /// The last degree in the profile is the one that was *running* when a limit was crossed, so
    /// for an incomplete computation the highest **completed** degree is the one before it. For a
    /// complete one every degree finished.
    pub fn with_profile(mut self, profile: &DegreeProfile) -> Self {
        let degrees: Vec<u64> = profile.iter().map(|d| d.degree).collect();
        self.highest_completed_degree = if self.completed {
            degrees.last().copied()
        } else if degrees.len() >= 2 {
            Some(degrees[degrees.len() - 2])
        } else {
            None
        };
        self
    }

    /// State the quotient dimension, which is usually an observation rather than a fact.
    pub fn with_quotient_dimension(mut self, dimension: usize) -> Self {
        self.quotient_dimension = Some(dimension);
        self
    }

    /// The frontier as JSON.
    pub fn to_json(&self) -> Json {
        Json::object([
            ("completed", Json::Bool(self.completed)),
            ("max_pair_degree", Json::int(self.max_pair_degree)),
            (
                "highest_completed_degree",
                match self.highest_completed_degree {
                    Some(degree) => Json::int(degree),
                    None => Json::Null,
                },
            ),
            ("max_matrix_rows", Json::size(self.max_matrix_rows)),
            ("max_matrix_columns", Json::size(self.max_matrix_columns)),
            ("peak_live_nonzeros", Json::size(self.peak_live_nonzeros)),
            (
                "peak_estimated_bytes",
                Json::size(self.peak_estimated_bytes),
            ),
            ("pairs_reduced", Json::size(self.pairs_reduced)),
            ("elements_added", Json::size(self.elements_added)),
            (
                "quotient_dimension",
                match self.quotient_dimension {
                    Some(d) => Json::size(d),
                    None => Json::Null,
                },
            ),
        ])
    }
}

/// A randomized specialization campaign, including the slices that found nothing.
///
/// Reported as a whole because a fast successful slice is misleading if its success probability is
/// low: the honest cost of a witness is the total work divided by the witnesses, and the honest
/// statement about the rate has an interval on it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Campaign {
    /// Slices attempted.
    pub trials: usize,

    /// Slices that reached **no verdict**: they stopped at a resource limit.
    ///
    /// Separate from the witness count, and the distinction is the difference between a rate and a
    /// fiction. A slice that ran out of budget did not test whether it contains a solution, so it
    /// cannot be a Bernoulli trial of that question — counting it as a failure would report
    /// "0 witnesses in 8 slices" for a campaign that established nothing at all. Found by running
    /// the Fukuoka type VI `n = 15` campaign, where all eight slices crossed the entry cap.
    pub stopped: usize,

    /// Slices that produced an independently verified witness.
    pub witnesses: usize,

    /// Wall clock across every slice, the unsuccessful ones included.
    pub total: Duration,

    /// The seeds, so the campaign reconstructs.
    pub seeds: Vec<u64>,

    /// Variables fixed in each slice.
    pub fixed: usize,
}

impl Campaign {
    /// Expected work per witness, as `(nanoseconds, witnesses)`.
    ///
    /// A ratio of integers rather than a float, and `None` when there were no witnesses — where a
    /// division would produce either a panic or an infinity presented as a measurement.
    pub fn work_per_witness(&self) -> Option<(u128, usize)> {
        (self.witnesses > 0).then_some((self.total.as_nanos(), self.witnesses))
    }

    /// Trials that reached a verdict: a witness, or a slice shown to be empty.
    ///
    /// The denominator of the success rate. The others measured the budget, not the problem.
    pub fn decided(&self) -> usize {
        self.trials.saturating_sub(self.stopped)
    }

    /// A 95% Wilson score interval for the success rate, in basis points.
    ///
    /// Over the trials that **reached a verdict**, so a campaign whose slices all ran out of
    /// budget has no rate rather than a rate of zero. Wilson rather than the normal approximation
    /// because the rates of interest are near zero and small-sample: at 1 success in 20 the normal
    /// interval runs negative, which is not a probability.
    pub fn success_rate_basis_points(&self) -> Option<(u32, u32)> {
        wilson_interval(self.witnesses, self.decided())
    }

    /// The campaign as JSON.
    pub fn to_json(&self) -> Json {
        let mut fields = vec![
            ("trials", Json::size(self.trials)),
            ("stopped_at_limit", Json::size(self.stopped)),
            ("decided", Json::size(self.decided())),
            ("witnesses", Json::size(self.witnesses)),
            ("fixed_variables", Json::size(self.fixed)),
            ("total_nanos", Json::nanos(self.total)),
            (
                "seeds",
                Json::Array(self.seeds.iter().map(|s| Json::int(*s)).collect()),
            ),
        ];
        fields.push((
            "work_per_witness",
            match self.work_per_witness() {
                Some((nanos, witnesses)) => Json::object([
                    ("nanos", Json::Int(nanos as i128)),
                    ("witnesses", Json::size(witnesses)),
                ]),
                None => Json::Null,
            },
        ));
        fields.push((
            "success_rate_basis_points",
            match self.success_rate_basis_points() {
                Some((low, high)) => Json::object([
                    ("low", Json::int(low)),
                    ("high", Json::int(high)),
                    ("method", Json::string("wilson-95")),
                ]),
                None => Json::Null,
            },
        ));
        Json::object(fields)
    }
}

/// A 95% Wilson score interval, in basis points of probability.
///
/// `z = 1.96`. Floating point internally and rounded to integers on the way out, because a record
/// holds no floats — see the module docs.
pub fn wilson_interval(successes: usize, trials: usize) -> Option<(u32, u32)> {
    if trials == 0 {
        return None;
    }
    let n = trials as f64;
    let p = successes as f64 / n;
    let z = 1.96_f64;
    let z2 = z * z;
    let denominator = 1.0 + z2 / n;
    let center = (p + z2 / (2.0 * n)) / denominator;
    let half = z * ((p * (1.0 - p) / n) + z2 / (4.0 * n * n)).sqrt() / denominator;
    let low = ((center - half).max(0.0) * 10_000.0).round() as u32;
    let high = ((center + half).min(1.0) * 10_000.0).round() as u32;
    Some((low, high.min(10_000)))
}

/// The machine and the build a measurement came from.
///
/// Carried on every run because a runtime comparison across two of these is not a comparison.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Environment {
    /// The commit the binary was built from.
    pub commit: String,

    /// A machine label: hostname, or a description.
    pub machine: String,

    /// Logical CPUs, and whatever pinning policy was applied.
    pub cpu: String,

    /// `RUSTFLAGS` and the profile, which decide whether two timings are comparable at all.
    pub build: String,

    /// The resource policy the run was given, in its own words.
    pub policy: String,
}

impl Environment {
    /// The environment as JSON.
    pub fn to_json(&self) -> Json {
        Json::object([
            ("commit", Json::string(&self.commit)),
            ("machine", Json::string(&self.machine)),
            ("cpu", Json::string(&self.cpu)),
            ("build", Json::string(&self.build)),
            ("policy", Json::string(&self.policy)),
        ])
    }

    /// Whether two runs were measured under conditions a runtime may be compared across.
    pub fn comparable(&self, other: &Self) -> bool {
        self.machine == other.machine && self.cpu == other.cpu && self.build == other.build
    }
}

/// What one run established about one registered problem.
#[derive(Clone, Debug)]
pub struct RunRecord {
    /// Schema version.
    pub schema: u32,

    /// The registered problem's id.
    pub challenge: String,

    /// Its identity digest. **The reference**; the id is for humans.
    pub challenge_digest: String,

    /// The class, copied from the manifest for rendering. The registry remains the authority, and
    /// [`Scoreboard::add`] checks that this run's digest still matches it.
    pub class: BenchmarkClass,

    /// Which formulation of the problem was solved: `"as generated"`, `"last-round-first"`, …
    ///
    /// Not part of the problem's identity — every formulation is the same problem — and therefore
    /// the axis M23-C compares along.
    pub formulation: String,

    /// Transformations applied, in order, each of which must be invertible.
    pub transformations: Vec<String>,

    /// What happened.
    pub outcome: RunOutcome,

    /// How the answer was checked, in words. Empty when there was nothing to check.
    pub verification: String,

    /// Per-stage cost.
    pub stages: Vec<StageCost>,

    /// How far the algebra got.
    pub frontier: Option<GrobnerFrontier>,

    /// The campaign this run summarizes, if it was one.
    pub campaign: Option<Campaign>,

    /// The machine and build.
    pub environment: Environment,

    /// The per-attempt detail, when a planned solve ran.
    pub experiment: Option<ExperimentRecord>,

    /// The command that reproduces this run.
    pub reproduce: String,
}

impl RunRecord {
    /// The current schema version.
    pub const SCHEMA: u32 = 1;

    /// An empty record against `manifest`, which fixes the identity, the class and the verifier.
    pub fn new(manifest: &ChallengeManifest, formulation: impl Into<String>) -> Self {
        Self {
            schema: Self::SCHEMA,
            challenge: manifest.id.to_string(),
            challenge_digest: manifest.digest(),
            class: manifest.class,
            formulation: formulation.into(),
            transformations: Vec::new(),
            outcome: RunOutcome::BasisOnly,
            verification: String::new(),
            stages: Vec::new(),
            frontier: None,
            campaign: None,
            environment: Environment {
                commit: String::new(),
                machine: String::new(),
                cpu: String::new(),
                build: String::new(),
                policy: String::new(),
            },
            experiment: None,
            reproduce: String::new(),
        }
    }

    /// Total wall clock across the stages.
    pub fn elapsed(&self) -> Duration {
        self.stages.iter().map(|s| s.elapsed).sum()
    }

    /// One stage's cost, if it ran.
    pub fn stage(&self, stage: Stage) -> Option<&StageCost> {
        self.stages.iter().find(|s| s.stage == stage)
    }

    /// What this run's result is allowed to claim, computed from the registry's manifest.
    ///
    /// Takes the manifest rather than reading the copied class, so that the rule has one home and
    /// a stale copy cannot quietly upgrade a claim.
    pub fn significance(&self, manifest: &ChallengeManifest) -> Significance {
        manifest.significance(self.outcome.is_verified_witness())
    }

    /// Read a stored record back, taking its class from the registry.
    ///
    /// Needed because a scoreboard **accumulates**: comparing two runs from different commits
    /// means loading at least one of them from a file. The class comes from `manifest` rather than
    /// from the stored name, and the stored digest is checked against it — so loading a record of
    /// a problem that has since been redefined fails here, exactly as adding one does.
    ///
    /// **The per-attempt [`ExperimentRecord`] is not reconstructed.** Nothing the scoreboard
    /// renders or compares reads it, it is a large surface to parse, and the run file keeps it
    /// verbatim. A loaded record is therefore for rendering and comparison, and `results/history`
    /// is appended as raw JSON rather than rewritten from loaded records — otherwise that detail
    /// would be dropped on each pass.
    ///
    /// # Errors
    /// [`ScoreboardError::MalformedRun`] naming the first field it cannot read, or
    /// [`ScoreboardError::StaleIdentity`].
    pub fn from_json(value: &Json, manifest: &ChallengeManifest) -> Result<Self, ScoreboardError> {
        let text = |key: &'static str| -> Result<String, ScoreboardError> {
            value
                .get(key)
                .and_then(Json::as_str)
                .map(|s| s.to_string())
                .ok_or(ScoreboardError::MalformedRun { field: key })
        };
        let challenge = text("challenge")?;
        let challenge_digest = text("challenge_digest")?;
        if challenge_digest != manifest.digest() {
            return Err(ScoreboardError::StaleIdentity {
                id: challenge,
                recorded: challenge_digest,
                registry: manifest.digest(),
            });
        }

        let outcome = match value
            .get("outcome")
            .and_then(Json::as_str)
            .ok_or(ScoreboardError::MalformedRun { field: "outcome" })?
        {
            "verified_witness" => RunOutcome::VerifiedWitness,
            "witness_rejected" => RunOutcome::WitnessRejected,
            "no_base_field_point" => RunOutcome::NoBaseFieldPoint,
            "inconsistent" => RunOutcome::Inconsistent,
            "basis_only" => RunOutcome::BasisOnly,
            "slice_established_nothing" => RunOutcome::SliceEstablishedNothing,
            "stopped_at_limit" => {
                let limit = value
                    .get("limit")
                    .ok_or(ScoreboardError::MalformedRun { field: "limit" })?;
                RunOutcome::StoppedAtLimit(Limit {
                    resource: limit
                        .get("resource")
                        .and_then(Json::as_str)
                        .unwrap_or_default()
                        .to_string(),
                    detail: limit
                        .get("detail")
                        .and_then(Json::as_str)
                        .unwrap_or_default()
                        .to_string(),
                    degree: limit.get("degree").and_then(Json::as_int).map(|d| d as u64),
                    last_completed_stage: limit
                        .get("last_completed_stage")
                        .and_then(Json::as_str)
                        .and_then(Stage::named)
                        .unwrap_or(Stage::Nothing),
                })
            }
            _ => return Err(ScoreboardError::MalformedRun { field: "outcome" }),
        };

        let stages = value
            .get("stages")
            .map(|stages| {
                stages
                    .items()
                    .iter()
                    .filter_map(|stage| {
                        Some(StageCost {
                            stage: Stage::named(stage.get("stage")?.as_str()?)?,
                            elapsed: Duration::from_nanos(
                                stage.get("elapsed_nanos")?.as_int()? as u64
                            ),
                            estimated_peak_bytes: stage
                                .get("estimated_peak_bytes")
                                .and_then(Json::as_int)
                                .map(|b| b as usize),
                            detail: match stage.get("detail") {
                                Some(Json::Object(fields)) => fields
                                    .iter()
                                    .filter_map(|(k, v)| Some((k.clone(), v.as_int()?)))
                                    .collect(),
                                _ => Vec::new(),
                            },
                        })
                    })
                    .collect()
            })
            .unwrap_or_default();

        let frontier = match value.get("grobner_frontier") {
            Some(Json::Object(_)) => {
                let f = value.get("grobner_frontier").expect("just matched");
                let size = |key: &str| f.get(key).and_then(Json::as_int).unwrap_or(0) as usize;
                Some(GrobnerFrontier {
                    completed: matches!(f.get("completed"), Some(Json::Bool(true))),
                    max_pair_degree: f.get("max_pair_degree").and_then(Json::as_int).unwrap_or(0)
                        as u64,
                    highest_completed_degree: f
                        .get("highest_completed_degree")
                        .and_then(Json::as_int)
                        .map(|d| d as u64),
                    max_matrix_rows: size("max_matrix_rows"),
                    max_matrix_columns: size("max_matrix_columns"),
                    peak_live_nonzeros: size("peak_live_nonzeros"),
                    peak_estimated_bytes: size("peak_estimated_bytes"),
                    pairs_reduced: size("pairs_reduced"),
                    elements_added: size("elements_added"),
                    quotient_dimension: f
                        .get("quotient_dimension")
                        .and_then(Json::as_int)
                        .map(|d| d as usize),
                })
            }
            _ => None,
        };

        let campaign = match value.get("campaign") {
            Some(Json::Object(_)) => {
                let c = value.get("campaign").expect("just matched");
                let size = |key: &str| c.get(key).and_then(Json::as_int).unwrap_or(0) as usize;
                Some(Campaign {
                    trials: size("trials"),
                    stopped: size("stopped_at_limit"),
                    witnesses: size("witnesses"),
                    total: Duration::from_nanos(
                        c.get("total_nanos").and_then(Json::as_int).unwrap_or(0) as u64,
                    ),
                    seeds: c
                        .get("seeds")
                        .map(|seeds| {
                            seeds
                                .items()
                                .iter()
                                .filter_map(|s| s.as_int().map(|s| s as u64))
                                .collect()
                        })
                        .unwrap_or_default(),
                    fixed: size("fixed_variables"),
                })
            }
            _ => None,
        };

        let environment = value
            .get("environment")
            .ok_or(ScoreboardError::MalformedRun {
                field: "environment",
            })?;
        let field = |key: &str| {
            environment
                .get(key)
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string()
        };

        Ok(Self {
            schema: value.get("schema").and_then(Json::as_int).unwrap_or(1) as u32,
            challenge: text("challenge")?,
            challenge_digest,
            class: manifest.class,
            formulation: text("formulation")?,
            transformations: value
                .get("transformations")
                .map(|t| {
                    t.items()
                        .iter()
                        .filter_map(|v| v.as_str().map(|s| s.to_string()))
                        .collect()
                })
                .unwrap_or_default(),
            outcome,
            verification: value
                .get("verification")
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string(),
            stages,
            frontier,
            campaign,
            environment: Environment {
                commit: field("commit"),
                machine: field("machine"),
                cpu: field("cpu"),
                build: field("build"),
                policy: field("policy"),
            },
            experiment: None,
            reproduce: value
                .get("reproduce")
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string(),
        })
    }

    /// The record as JSON.
    pub fn to_json(&self, manifest: &ChallengeManifest) -> Json {
        let mut fields = vec![
            ("schema", Json::int(self.schema)),
            ("challenge", Json::string(&self.challenge)),
            ("challenge_digest", Json::string(&self.challenge_digest)),
            ("class", Json::string(self.class.name())),
            ("formulation", Json::string(&self.formulation)),
            (
                "transformations",
                Json::Array(self.transformations.iter().map(Json::string).collect()),
            ),
            ("outcome", Json::string(self.outcome.name())),
        ];
        if let RunOutcome::StoppedAtLimit(limit) = &self.outcome {
            fields.push((
                "limit",
                Json::object([
                    ("resource", Json::string(&limit.resource)),
                    ("detail", Json::string(&limit.detail)),
                    (
                        "degree",
                        match limit.degree {
                            Some(degree) => Json::int(degree),
                            None => Json::Null,
                        },
                    ),
                    (
                        "last_completed_stage",
                        Json::string(limit.last_completed_stage.name()),
                    ),
                ]),
            ));
        }
        fields.push((
            "significance",
            Json::string(self.significance(manifest).to_string()),
        ));
        fields.push(("verification", Json::string(&self.verification)));
        fields.push(("elapsed_nanos", Json::nanos(self.elapsed())));
        fields.push((
            "stages",
            Json::Array(self.stages.iter().map(StageCost::to_json).collect()),
        ));
        fields.push((
            "grobner_frontier",
            match &self.frontier {
                Some(frontier) => frontier.to_json(),
                None => Json::Null,
            },
        ));
        fields.push((
            "campaign",
            match &self.campaign {
                Some(campaign) => campaign.to_json(),
                None => Json::Null,
            },
        ));
        fields.push(("environment", self.environment.to_json()));
        fields.push((
            "experiment",
            match &self.experiment {
                Some(experiment) => experiment.to_json(),
                None => Json::Null,
            },
        ));
        fields.push(("reproduce", Json::string(&self.reproduce)));
        Json::object(fields)
    }
}

/// Why a run could not be added to a scoreboard, or two runs could not be compared.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ScoreboardError {
    /// A stored record is missing a field the scoreboard reads, or has it at the wrong type.
    MalformedRun {
        /// Which field.
        field: &'static str,
    },

    /// The run names a problem the registry does not hold.
    UnknownChallenge {
        /// The id it named.
        id: String,
    },

    /// The run's digest does not match the registry's.
    ///
    /// **The failure this module exists to prevent.** It means the problem was redefined after the
    /// run, so the measurement is about something the registry no longer describes, and quoting it
    /// against the current definition would be a false comparison.
    StaleIdentity {
        /// The problem's id.
        id: String,
        /// What the run recorded.
        recorded: String,
        /// What the registry says now.
        registry: String,
    },

    /// Two runs are of different problems.
    DifferentProblems {
        /// The first run's problem.
        left: String,
        /// The second's.
        right: String,
    },
}

impl Display for ScoreboardError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedRun { field } => {
                write!(f, "a stored run has no usable {}", field)
            }
            Self::UnknownChallenge { id } => write!(f, "no registered problem named {}", id),
            Self::StaleIdentity {
                id,
                recorded,
                registry,
            } => write!(
                f,
                "{} was redefined: the run was against {}, the registry now holds {}",
                id,
                &recorded[..12.min(recorded.len())],
                &registry[..12.min(registry.len())]
            ),
            Self::DifferentProblems { left, right } => write!(
                f,
                "refusing to compare different problems: {} against {}",
                left, right
            ),
        }
    }
}

impl std::error::Error for ScoreboardError {}

/// Two runs of the same problem, compared.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Comparison {
    /// The problem both runs are of.
    pub challenge: String,

    /// The baseline's formulation and the candidate's.
    pub formulations: (String, String),

    /// `baseline / candidate` in per-mille: 1670 is 1.67x faster.
    pub speedup_per_mille: u64,

    /// `1 − candidate/baseline` of peak estimated bytes, in basis points. Negative means worse.
    pub memory_reduction_basis_points: i64,

    /// Whether the runtime difference is outside this project's ±20% reading threshold.
    ///
    /// M22 declined to read runtime differences inside that band on this hardware, and M23 keeps
    /// the rule. A comparison that is not readable is still reported — with this `false`.
    pub runtime_readable: bool,

    /// Anything that weakens the comparison without invalidating it.
    pub caveats: Vec<String>,
}

impl Comparison {
    /// Compare `candidate` against `baseline`, refusing two different problems.
    ///
    /// # Errors
    /// [`ScoreboardError::DifferentProblems`] when the identity digests differ. The ids are not
    /// compared: two runs can agree on a name and disagree on what it means, which is the whole
    /// reason the digest exists.
    pub fn of(baseline: &RunRecord, candidate: &RunRecord) -> Result<Self, ScoreboardError> {
        if baseline.challenge_digest != candidate.challenge_digest {
            return Err(ScoreboardError::DifferentProblems {
                left: format!(
                    "{} ({})",
                    baseline.challenge,
                    &baseline.challenge_digest[..12]
                ),
                right: format!(
                    "{} ({})",
                    candidate.challenge,
                    &candidate.challenge_digest[..12]
                ),
            });
        }

        let base_nanos = baseline.elapsed().as_nanos().max(1);
        let new_nanos = candidate.elapsed().as_nanos().max(1);
        let speedup_per_mille = (base_nanos * 1_000 / new_nanos) as u64;

        let base_bytes = baseline
            .frontier
            .as_ref()
            .map(|f| f.peak_estimated_bytes)
            .unwrap_or(0);
        let new_bytes = candidate
            .frontier
            .as_ref()
            .map(|f| f.peak_estimated_bytes)
            .unwrap_or(0);
        let memory_reduction_basis_points = if base_bytes == 0 {
            0
        } else {
            10_000 - (new_bytes as i64 * 10_000 / base_bytes as i64)
        };

        let mut caveats = Vec::new();
        if !baseline.environment.comparable(&candidate.environment) {
            caveats.push(format!(
                "measured under different conditions: {} / {} against {} / {}",
                baseline.environment.machine,
                baseline.environment.build,
                candidate.environment.machine,
                candidate.environment.build
            ));
        }
        if baseline.outcome != candidate.outcome {
            caveats.push(format!(
                "different outcomes: {} against {}",
                baseline.outcome, candidate.outcome
            ));
        }
        if !baseline.outcome.is_verified_witness() || !candidate.outcome.is_verified_witness() {
            caveats.push(
                "at least one side produced no verified witness, so the runtimes are costs of \
                 different things"
                    .to_string(),
            );
        }

        Ok(Self {
            challenge: baseline.challenge.clone(),
            formulations: (baseline.formulation.clone(), candidate.formulation.clone()),
            speedup_per_mille,
            memory_reduction_basis_points,
            runtime_readable: speedup_per_mille >= 1_200 || speedup_per_mille <= 833,
            caveats,
        })
    }

    /// The comparison as JSON.
    pub fn to_json(&self) -> Json {
        Json::object([
            ("challenge", Json::string(&self.challenge)),
            ("baseline_formulation", Json::string(&self.formulations.0)),
            ("candidate_formulation", Json::string(&self.formulations.1)),
            ("speedup_per_mille", Json::int(self.speedup_per_mille)),
            (
                "memory_reduction_basis_points",
                Json::int(self.memory_reduction_basis_points),
            ),
            ("runtime_readable", Json::Bool(self.runtime_readable)),
            (
                "caveats",
                Json::Array(self.caveats.iter().map(Json::string).collect()),
            ),
        ])
    }
}

impl Display for Comparison {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {} against {} — {}.{:02}x{}, peak bytes {}{}.{:02}%",
            self.challenge,
            self.formulations.1,
            self.formulations.0,
            self.speedup_per_mille / 1_000,
            (self.speedup_per_mille % 1_000) / 10,
            if self.runtime_readable {
                ""
            } else {
                " (inside the noise band, not read)"
            },
            if self.memory_reduction_basis_points < 0 {
                "+"
            } else {
                "−"
            },
            self.memory_reduction_basis_points.abs() / 100,
            self.memory_reduction_basis_points.abs() % 100,
        )
    }
}

/// Every run, with the registry's problems, rendered.
#[derive(Clone, Debug, Default)]
pub struct Scoreboard {
    runs: Vec<RunRecord>,
}

impl Scoreboard {
    /// An empty scoreboard.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a run, checking its identity against `registry`.
    ///
    /// # Errors
    /// [`ScoreboardError::UnknownChallenge`] or [`ScoreboardError::StaleIdentity`]. The second is
    /// the point: a run recorded against a problem that has since been redefined is not a
    /// measurement of the problem the registry now describes, and silently rendering it in the
    /// same table would be the failure this type exists to prevent.
    pub fn add(
        &mut self,
        run: RunRecord,
        registry: &[ChallengeManifest],
    ) -> Result<(), ScoreboardError> {
        let manifest = registry
            .iter()
            .find(|c| c.id == run.challenge)
            .ok_or_else(|| ScoreboardError::UnknownChallenge {
                id: run.challenge.clone(),
            })?;
        let current = manifest.digest();
        if current != run.challenge_digest {
            return Err(ScoreboardError::StaleIdentity {
                id: run.challenge.clone(),
                recorded: run.challenge_digest.clone(),
                registry: current,
            });
        }
        self.runs.push(run);
        Ok(())
    }

    /// The runs, in insertion order.
    pub fn runs(&self) -> &[RunRecord] {
        &self.runs
    }

    /// Load an accumulated history: `{"runs": [...]}` as [`Self::to_json`] writes it.
    ///
    /// This is what makes the plan's "two runs of the same instance on different commits compare
    /// automatically" possible at all — one of them is in a file. Every record is checked against
    /// the registry on the way in, so a history that outlived a redefinition fails loudly.
    ///
    /// # Errors
    /// As [`RunRecord::from_json`], plus [`ScoreboardError::UnknownChallenge`].
    pub fn load(history: &Json, registry: &[ChallengeManifest]) -> Result<Self, ScoreboardError> {
        let entries = history
            .get("runs")
            .ok_or(ScoreboardError::MalformedRun { field: "runs" })?;
        let mut board = Self::new();
        for entry in entries.items() {
            let id = entry
                .get("challenge")
                .and_then(Json::as_str)
                .ok_or(ScoreboardError::MalformedRun { field: "challenge" })?;
            let manifest = registry
                .iter()
                .find(|c| c.id == id)
                .ok_or_else(|| ScoreboardError::UnknownChallenge { id: id.to_string() })?;
            board.runs.push(RunRecord::from_json(entry, manifest)?);
        }
        Ok(board)
    }

    /// The fastest verified witness for each problem.
    ///
    /// **Witnesses only.** Runs that stopped at a limit are not ranked against each other: a
    /// higher degree does not mean less work remains, so there is no ordering to impose. Those
    /// appear in [`Self::unfinished`] instead, and in the rendered table beside this one.
    pub fn best(&self) -> BTreeMap<&str, &RunRecord> {
        let mut best: BTreeMap<&str, &RunRecord> = BTreeMap::new();
        for run in &self.runs {
            if !run.outcome.is_verified_witness() {
                continue;
            }
            best.entry(run.challenge.as_str())
                .and_modify(|current| {
                    if run.elapsed() < current.elapsed() {
                        *current = run;
                    }
                })
                .or_insert(run);
        }
        best
    }

    /// Runs that produced no verified witness, in insertion order.
    pub fn unfinished(&self) -> Vec<&RunRecord> {
        self.runs
            .iter()
            .filter(|r| !r.outcome.is_verified_witness())
            .collect()
    }

    /// Every run as JSON, with its problem's manifest resolved for significance.
    ///
    /// # Errors
    /// As [`Self::add`] — a run whose problem has since been redefined is refused here too, so an
    /// emitted file cannot contain a stale identity even if one was added before a registry change.
    pub fn to_json(&self, registry: &[ChallengeManifest]) -> Result<Json, ScoreboardError> {
        let mut runs = Vec::with_capacity(self.runs.len());
        for run in &self.runs {
            let manifest = registry
                .iter()
                .find(|c| c.id == run.challenge)
                .ok_or_else(|| ScoreboardError::UnknownChallenge {
                    id: run.challenge.clone(),
                })?;
            let current = manifest.digest();
            if current != run.challenge_digest {
                return Err(ScoreboardError::StaleIdentity {
                    id: run.challenge.clone(),
                    recorded: run.challenge_digest.clone(),
                    registry: current,
                });
            }
            runs.push(run.to_json(manifest));
        }
        Ok(Json::object([
            ("schema", Json::int(RunRecord::SCHEMA)),
            ("run_count", Json::size(runs.len())),
            ("runs", Json::Array(runs)),
        ]))
    }

    /// The scoreboard as Markdown, one table per benchmark class.
    ///
    /// One table per class rather than one table with a class column, because a single table
    /// invites a reader to compare its rows — and the classes are exactly the thing that must not
    /// be compared.
    pub fn to_markdown(&self, registry: &[ChallengeManifest]) -> String {
        let mut out = String::new();
        out.push_str("# Zeebra cryptanalysis scoreboard\n\n");
        out.push_str(
            "Generated. Every row is one registered problem; a problem's identity is the digest \
             of its parameters, not its name. **The three classes are never added together** — an \
             engineering surrogate's witness is not evidence about a public challenge.\n\n",
        );

        for class in [
            BenchmarkClass::Official,
            BenchmarkClass::FaithfulReduction { of: "" },
            BenchmarkClass::Engineering { why: "" },
        ] {
            let members: Vec<&ChallengeManifest> = registry
                .iter()
                .filter(|c| c.class.name() == class.name())
                .collect();
            if members.is_empty() {
                continue;
            }
            out.push_str(&format!(
                "## {}\n\n{}\n\n",
                match class {
                    BenchmarkClass::Official => "Official problems",
                    BenchmarkClass::FaithfulReduction { .. } => "Faithful reductions",
                    BenchmarkClass::Engineering { .. } => "Engineering surrogates",
                },
                match class {
                    BenchmarkClass::Official =>
                        "The externally specified problems, unmodified. A witness here is a \
                         witness for the public challenge.",
                    BenchmarkClass::FaithfulReduction { .. } =>
                        "The official field, state width, `k`, constants and objective; fewer \
                         rounds. A witness here says **nothing** about the official target it \
                         reduced from.",
                    BenchmarkClass::Engineering { .. } =>
                        "Surrogates: reduced width, planted targets. Evidence about the \
                         implementation, not about any challenge.",
                }
            ));
            out.push_str(
                "| problem | identity | vars | eqs | best result | external status | \
                 published method |\n\
                 |---|---|---:|---:|---|---|---|\n",
            );
            let best = self.best();
            for manifest in members {
                let result = match best.get(manifest.id) {
                    Some(run) => format!(
                        "**{}** in {:.1} ms ({})",
                        run.outcome,
                        run.elapsed().as_secs_f64() * 1e3,
                        run.formulation
                    ),
                    None => match self
                        .unfinished()
                        .into_iter()
                        .rfind(|r| r.challenge == manifest.id)
                    {
                        Some(run) => run.outcome.short(),
                        None => "not attempted".to_string(),
                    },
                };
                out.push_str(&format!(
                    "| `{}` | `{}` | {} | {} | {} | {} | {} |\n",
                    manifest.id,
                    manifest.short_digest(),
                    manifest
                        .variables()
                        .map_or("—".to_string(), |v| v.to_string()),
                    manifest
                        .equations()
                        .map_or("—".to_string(), |e| e.to_string()),
                    result,
                    // A derived row has no external status worth a column: nobody posed it, and
                    // "no public solution recorded" would imply somebody had looked.
                    match manifest.external {
                        crate::grobner::research::ExternalStatus::NotAPublicProblem =>
                            "—".to_string(),
                        status => status.to_string(),
                    },
                    // Separate from the column before it on purpose: a programme can verify a
                    // submission without naming the submitter, so "verified on this date" and
                    // "this is how it was done" are two claims and the table keeps them apart.
                    match manifest.method {
                        crate::grobner::research::DisclosedMethod::NotApplicable => "—".to_string(),
                        method => method.to_string(),
                    },
                ));
            }
            out.push('\n');
        }

        let unfinished = self.unfinished();
        if !unfinished.is_empty() {
            out.push_str("## Where the unfinished runs stopped\n\n");
            out.push_str(
                "A higher degree is **not** nearer a solution: this table is a diagnostic, not a \
                 progress bar. Each row names the bound that bound, the degree reached, and the \
                 last stage that completed.\n\n",
            );
            out.push_str(
                "| problem | formulation | outcome | deg | last deg done | max cols | peak MB |\n\
                 |---|---|---|---:|---:|---:|---:|\n",
            );
            for run in unfinished {
                let frontier = run.frontier.clone().unwrap_or_default();
                out.push_str(&format!(
                    "| `{}` | {} | {} | {} | {} | {} | {:.1} |\n",
                    run.challenge,
                    run.formulation,
                    run.outcome.short(),
                    frontier.max_pair_degree,
                    frontier
                        .highest_completed_degree
                        .map_or("none".to_string(), |d| d.to_string()),
                    frontier.max_matrix_columns,
                    frontier.peak_estimated_bytes as f64 / 1e6,
                ));
            }
            out.push('\n');
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::{
        wilson_interval, Campaign, Comparison, Environment, GrobnerFrontier, Limit, RunOutcome,
        RunRecord, Scoreboard, ScoreboardError, Stage, StageCost,
    };
    use crate::grobner::research::{challenge, registry, Significance};

    fn environment() -> Environment {
        Environment {
            commit: "deadbeef".to_string(),
            machine: "workstation".to_string(),
            cpu: "64 logical, taskset 0-7".to_string(),
            build: "release, target-cpu=x86-64-v3".to_string(),
            policy: "60k columns, 400 MB".to_string(),
        }
    }

    fn witness(id: &str, formulation: &str, millis: u64, bytes: usize) -> RunRecord {
        let manifest = challenge(id).expect("registered");
        let mut run = RunRecord::new(&manifest, formulation);
        run.outcome = RunOutcome::VerifiedWitness;
        run.verification = "through the permutation".to_string();
        run.stages = vec![StageCost::new(
            Stage::Grobner,
            Duration::from_millis(millis),
        )];
        run.frontier = Some(GrobnerFrontier {
            completed: true,
            peak_estimated_bytes: bytes,
            ..GrobnerFrontier::default()
        });
        run.environment = environment();
        run
    }

    /// A run whose problem has been redefined since is refused, by digest and not by name.
    ///
    /// The failure the scoreboard exists to prevent: two runs can agree on
    /// `"poseidon31-cico-rf6-rp8"` and disagree on what that problem is.
    #[test]
    fn test_a_stale_identity_is_refused() {
        let registry = registry();
        let mut board = Scoreboard::new();

        let good = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            356,
            3_800_000,
        );
        assert_eq!(board.add(good, &registry), Ok(()));

        let mut stale = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            356,
            3_800_000,
        );
        stale.challenge_digest = "0".repeat(64);
        let error = board.add(stale, &registry).expect_err("refused");
        assert!(matches!(error, ScoreboardError::StaleIdentity { .. }));
        assert!(error.to_string().contains("was redefined"), "{}", error);

        let mut unknown = witness("poseidon-t2-rf4-rp0-planted", "as generated", 1, 1);
        unknown.challenge = "not-a-problem".to_string();
        assert_eq!(
            board.add(unknown, &registry),
            Err(ScoreboardError::UnknownChallenge {
                id: "not-a-problem".to_string()
            })
        );

        // And the one good run is all that landed.
        assert_eq!(board.runs().len(), 1);
    }

    /// Comparing two different problems is refused rather than rendered.
    #[test]
    fn test_comparing_different_problems_is_refused() {
        let left = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            356,
            3_800_000,
        );
        let right = witness(
            "poseidon-t2-rf2-rp2-planted",
            "as generated",
            143,
            1_700_000,
        );
        let error = Comparison::of(&left, &right).expect_err("refused");
        assert!(matches!(error, ScoreboardError::DifferentProblems { .. }));
        assert!(
            error.to_string().contains("refusing to compare"),
            "{}",
            error
        );
    }

    /// A comparison of one problem under two formulations reports speedup, memory and readability.
    ///
    /// The figures are M22-E's measured `last-round-first` result on this instance, as a
    /// regression on the arithmetic rather than a new measurement.
    #[test]
    fn test_a_formulation_comparison() {
        let baseline = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            352,
            3_800_000,
        );
        let candidate = witness(
            "poseidon-t2-rf4-rp0-planted",
            "last-round-first",
            219,
            2_900_000,
        );
        let comparison = Comparison::of(&baseline, &candidate).expect("same problem");

        // 352/219 = 1.607x, in per-mille.
        assert_eq!(comparison.speedup_per_mille, 1_607);
        // 1 - 2.9/3.8 = 23.68%, in basis points.
        assert_eq!(comparison.memory_reduction_basis_points, 2_369);
        assert!(comparison.runtime_readable, "1.61x is outside ±20%");
        assert!(comparison.caveats.is_empty(), "{:?}", comparison.caveats);
        assert!(comparison.to_string().contains("1.60x"), "{}", comparison);

        // A difference inside the band is reported and marked unreadable rather than quoted.
        let noise = witness("poseidon-t2-rf4-rp0-planted", "reordered", 330, 3_800_000);
        let comparison = Comparison::of(&baseline, &noise).expect("same problem");
        assert_eq!(comparison.speedup_per_mille, 1_066);
        assert!(!comparison.runtime_readable);
        assert!(
            comparison.to_string().contains("not read"),
            "{}",
            comparison
        );
    }

    /// A comparison across machines or builds carries the caveat rather than hiding it.
    #[test]
    fn test_incomparable_environments_are_flagged() {
        let baseline = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            352,
            3_800_000,
        );
        let mut elsewhere = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            100,
            3_800_000,
        );
        elsewhere.environment.machine = "a laptop".to_string();
        let comparison = Comparison::of(&baseline, &elsewhere).expect("same problem");
        assert_eq!(comparison.caveats.len(), 1);
        assert!(comparison.caveats[0].contains("different conditions"));

        // And a comparison where one side found nothing says the runtimes measure different
        // things, which is the mistake a bare ratio invites.
        let mut stopped = witness("poseidon-t2-rf4-rp0-planted", "as generated", 18_167, 0);
        stopped.outcome = RunOutcome::StoppedAtLimit(Limit {
            resource: "max_matrix_columns".to_string(),
            detail: "the column budget of 60000 was crossed".to_string(),
            degree: Some(11),
            last_completed_stage: Stage::Generation,
        });
        let comparison = Comparison::of(&baseline, &stopped).expect("same problem");
        assert_eq!(comparison.caveats.len(), 2);
        assert!(comparison
            .caveats
            .iter()
            .any(|c| c.contains("no verified witness")));
    }

    /// Unfinished runs are never ranked against each other.
    ///
    /// `best` returns witnesses only. A scoreboard that picked the "best" of two crossed budgets
    /// would be asserting that a higher degree is nearer a solution, which is false.
    #[test]
    fn test_unfinished_runs_are_not_ranked() {
        let registry = registry();
        let mut board = Scoreboard::new();
        for (degree, millis) in [(9u64, 1_000u64), (11, 18_167)] {
            let manifest = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
            let mut run = RunRecord::new(&manifest, "as generated");
            run.outcome = RunOutcome::StoppedAtLimit(Limit {
                resource: "max_matrix_columns".to_string(),
                detail: "crossed".to_string(),
                degree: Some(degree),
                last_completed_stage: Stage::Grobner,
            });
            run.stages = vec![StageCost::new(
                Stage::Grobner,
                Duration::from_millis(millis),
            )];
            run.frontier = Some(GrobnerFrontier {
                max_pair_degree: degree,
                ..GrobnerFrontier::default()
            });
            run.environment = environment();
            board.add(run, &registry).expect("registered");
        }
        assert!(board.best().is_empty(), "nothing was solved");
        assert_eq!(board.unfinished().len(), 2);

        // The rendered table shows both, under a heading that says it is a diagnostic.
        let markdown = board.to_markdown(&registry);
        assert!(markdown.contains("Where the unfinished runs stopped"));
        assert!(markdown.contains("not** nearer a solution"));
        assert!(markdown.contains("stopped: max_matrix_columns at degree 11"));
    }

    /// The fastest verified witness wins, and classes get separate tables.
    #[test]
    fn test_best_is_per_problem_and_classes_are_separate_tables() {
        let registry = registry();
        let mut board = Scoreboard::new();
        board
            .add(
                witness(
                    "poseidon-t2-rf4-rp0-planted",
                    "as generated",
                    352,
                    3_800_000,
                ),
                &registry,
            )
            .expect("registered");
        board
            .add(
                witness(
                    "poseidon-t2-rf4-rp0-planted",
                    "last-round-first",
                    219,
                    2_900_000,
                ),
                &registry,
            )
            .expect("registered");

        let best = board.best();
        assert_eq!(best.len(), 1);
        assert_eq!(
            best["poseidon-t2-rf4-rp0-planted"].formulation,
            "last-round-first"
        );

        let markdown = board.to_markdown(&registry);
        assert!(markdown.contains("## Official problems"));
        assert!(markdown.contains("## Faithful reductions"));
        assert!(markdown.contains("## Engineering surrogates"));
        assert!(markdown.contains("never added together"));
        // An official row nobody has attempted says so rather than being absent.
        assert!(markdown.contains("not attempted"));
        // And the surrogate's own row carries its result.
        assert!(markdown.contains("verified witness"), "{}", markdown);
    }

    /// A run's significance comes from the registry, so a surrogate cannot claim a challenge.
    #[test]
    fn test_significance_comes_from_the_registry() {
        let surrogate = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            352,
            3_800_000,
        );
        let manifest = challenge("poseidon-t2-rf4-rp0-planted").expect("registered");
        assert!(matches!(
            surrogate.significance(&manifest),
            Significance::SurrogateWitness { .. }
        ));
        let json = surrogate.to_json(&manifest).to_json();
        assert!(json.contains("witness for a surrogate"), "{}", json);
        assert!(json.contains("\"class\": \"engineering\""), "{}", json);
    }

    /// A stored run loads back with everything the scoreboard reads, and compares against a new one.
    ///
    /// The acceptance criterion in one test: two runs of the same problem from different commits,
    /// one of them read from a file, compared automatically. Without a reader there is no "across
    /// commits" at all.
    #[test]
    fn test_a_history_loads_and_compares_across_commits() {
        use crate::grobner::research::{challenge, Json};

        let registry = registry();
        let manifest = challenge("poseidon-t2-rf4-rp0-planted").expect("registered");

        let mut old = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            352,
            3_800_000,
        );
        old.environment.commit = "aaaaaaa".to_string();
        old.transformations = vec!["none".to_string()];
        old.frontier = Some(GrobnerFrontier {
            completed: true,
            max_pair_degree: 5,
            highest_completed_degree: Some(5),
            max_matrix_columns: 1_341,
            peak_estimated_bytes: 3_800_000,
            quotient_dimension: Some(81),
            ..GrobnerFrontier::default()
        });
        old.stages = vec![
            StageCost::new(Stage::Grobner, Duration::from_millis(352))
                .with("max_matrix_columns", 1_341i64)
                .with_estimated_bytes(3_800_000),
            StageCost::new(Stage::Univariate, Duration::from_micros(17_400)),
        ];

        // Written as a history file would be, then read back.
        let history = Json::object([
            ("schema", Json::int(1i32)),
            ("runs", Json::Array(vec![old.to_json(&manifest)])),
        ]);
        let text = history.to_json();
        let loaded = Scoreboard::load(&Json::parse(&text).expect("valid"), &registry)
            .expect("a registered problem");
        assert_eq!(loaded.runs().len(), 1);

        let read = &loaded.runs()[0];
        assert_eq!(read.challenge_digest, old.challenge_digest);
        assert_eq!(read.class, old.class);
        assert_eq!(read.formulation, "as generated");
        assert_eq!(read.transformations, vec!["none".to_string()]);
        assert_eq!(read.outcome, RunOutcome::VerifiedWitness);
        // Exactly, in nanoseconds: 352 ms of F4 and 17.4 ms of root finding.
        assert_eq!(read.elapsed(), Duration::from_micros(369_400));
        assert_eq!(read.stages.len(), 2);
        assert_eq!(
            read.stage(Stage::Grobner).expect("ran").detail,
            vec![("max_matrix_columns".to_string(), 1_341i128)]
        );
        assert_eq!(read.frontier, old.frontier);
        assert_eq!(read.environment.commit, "aaaaaaa");

        // And the comparison a later commit wants.
        let mut new = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            219,
            2_900_000,
        );
        new.environment = read.environment.clone();
        let comparison = Comparison::of(read, &new).expect("the same problem");
        // 369.4 ms against 219 ms, over the whole pipeline rather than F4 alone.
        assert_eq!(comparison.speedup_per_mille, 1_686);
        assert!(comparison.caveats.is_empty(), "{:?}", comparison.caveats);
    }

    /// A run that stopped, and a slice that established nothing, both survive a round trip.
    #[test]
    fn test_outcomes_that_are_not_witnesses_round_trip() {
        use crate::grobner::research::{challenge, Json};

        let registry = registry();
        let manifest = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");

        let mut stopped = RunRecord::new(&manifest, "as generated");
        stopped.environment = environment();
        stopped.outcome = RunOutcome::StoppedAtLimit(Limit {
            resource: "max_live_nonzeros".to_string(),
            detail: "20000322 live nonzero entries were needed, over the limit of 20000000"
                .to_string(),
            degree: Some(6),
            last_completed_stage: Stage::Generation,
        });

        let mut slice = RunRecord::new(&manifest, "slice(12 fixed, seed 0)");
        slice.environment = environment();
        slice.outcome = RunOutcome::SliceEstablishedNothing;
        slice.transformations = vec!["specialize free inputs 2..14 at seed 0".to_string()];

        let history = Json::object([(
            "runs",
            Json::Array(vec![stopped.to_json(&manifest), slice.to_json(&manifest)]),
        )]);
        let loaded = Scoreboard::load(&Json::parse(&history.to_json()).expect("valid"), &registry)
            .expect("registered");

        assert_eq!(loaded.runs()[0].outcome, stopped.outcome);
        assert_eq!(
            loaded.runs()[1].outcome,
            RunOutcome::SliceEstablishedNothing
        );
        assert!(loaded.best().is_empty(), "neither is a witness");
        // And the slice's own Display refuses to be read as a statement about the problem.
        assert!(loaded.runs()[1]
            .outcome
            .to_string()
            .contains("says nothing about the problem"));
    }

    /// A history whose problem has been redefined fails to load, and names the field it cannot use.
    #[test]
    fn test_a_malformed_or_stale_history_is_refused() {
        use crate::grobner::research::{challenge, Json};

        let registry = registry();
        let manifest = challenge("poseidon-t2-rf4-rp0-planted").expect("registered");
        let run = witness("poseidon-t2-rf4-rp0-planted", "as generated", 1, 1);

        // Stale: the stored digest no longer matches the registry's.
        let mut stale = run.to_json(&manifest);
        if let Json::Object(fields) = &mut stale {
            for (key, value) in fields.iter_mut() {
                if key == "challenge_digest" {
                    *value = Json::string("0".repeat(64));
                }
            }
        }
        let history = Json::object([("runs", Json::Array(vec![stale]))]);
        assert!(matches!(
            Scoreboard::load(&history, &registry),
            Err(ScoreboardError::StaleIdentity { .. })
        ));

        // Malformed: no environment at all.
        let history = Json::parse(
            r#"{"runs":[{"challenge":"poseidon-t2-rf4-rp0-planted",
            "challenge_digest":"x","outcome":"basis_only","formulation":"f"}]}"#,
        )
        .expect("valid JSON");
        assert!(matches!(
            Scoreboard::load(&history, &registry),
            Err(ScoreboardError::StaleIdentity { .. })
        ));

        // And an unknown problem is named.
        let history = Json::parse(r#"{"runs":[{"challenge":"nope"}]}"#).expect("valid JSON");
        assert_eq!(
            Scoreboard::load(&history, &registry).expect_err("unknown"),
            ScoreboardError::UnknownChallenge {
                id: "nope".to_string()
            }
        );

        // A history with no `runs` key at all says which field it wanted.
        assert_eq!(
            Scoreboard::load(&Json::object([("x", Json::Null)]), &registry).expect_err("no runs"),
            ScoreboardError::MalformedRun { field: "runs" }
        );
    }

    /// A campaign reports its failures, its work per witness and an interval on the rate.
    #[test]
    fn test_a_campaign_reports_the_failures_too() {
        let campaign = Campaign {
            trials: 20,
            stopped: 0,
            witnesses: 1,
            total: Duration::from_secs(40),
            seeds: (0..20).collect(),
            fixed: 12,
        };
        assert_eq!(
            campaign.work_per_witness(),
            Some((40_000_000_000u128, 1)),
            "the honest cost is the whole campaign, not the lucky slice"
        );
        let (low, high) = campaign.success_rate_basis_points().expect("20 trials");
        assert!(low > 0 && high < 10_000, "{} {}", low, high);
        // Wilson keeps the interval inside [0, 1] where the normal approximation would not: at
        // 1/20 the normal lower bound is negative, which is not a probability.
        assert_eq!((low, high), (89, 2_361));

        let json = campaign.to_json().to_json();
        assert!(json.contains("\"trials\": 20"), "{}", json);
        assert!(json.contains("wilson-95"), "{}", json);

        // No witnesses: no work-per-witness rather than a division.
        let dead = Campaign {
            trials: 10,
            stopped: 0,
            witnesses: 0,
            total: Duration::from_secs(5),
            seeds: (0..10).collect(),
            fixed: 12,
        };
        assert_eq!(dead.work_per_witness(), None);
        assert_eq!(dead.decided(), 10);
        assert_eq!(dead.success_rate_basis_points(), Some((0, 2_775)));
        assert_eq!(wilson_interval(0, 0), None);

        // And a campaign whose every slice ran out of budget has **no rate at all**, not a rate
        // of zero: those trials measured the budget rather than the problem. The Fukuoka type VI
        // n = 15 campaign is exactly this case, and reporting "0 witnesses in 8 slices, 0% to
        // 32%" for it would be a claim about the instance that nothing established.
        let undecided = Campaign {
            trials: 8,
            stopped: 8,
            witnesses: 0,
            total: Duration::from_secs(236),
            seeds: (0..8).collect(),
            fixed: 5,
        };
        assert_eq!(undecided.decided(), 0);
        assert_eq!(undecided.success_rate_basis_points(), None);
        assert_eq!(undecided.work_per_witness(), None);
        let json = undecided.to_json().to_json();
        assert!(json.contains("\"stopped_at_limit\": 8"), "{}", json);
        assert!(json.contains("\"decided\": 0"), "{}", json);
        assert!(
            json.contains("\"success_rate_basis_points\": null"),
            "{}",
            json
        );

        // One decided slice among many stopped: the rate is over the one, and says so by being
        // extremely wide rather than by being zero.
        let partly = Campaign {
            stopped: 7,
            ..undecided
        };
        assert_eq!(partly.decided(), 1);
        assert_eq!(partly.success_rate_basis_points(), Some((0, 7_935)));
    }

    /// Stage costs are separate keys, so the dominant stage is visible.
    #[test]
    fn test_stages_are_reported_separately() {
        let manifest = challenge("fukuoka-mq-III-n10-seed0").expect("registered");
        let mut run = RunRecord::new(&manifest, "as published");
        run.outcome = RunOutcome::VerifiedWitness;
        run.environment = environment();
        run.stages = vec![
            StageCost::new(Stage::Generation, Duration::from_micros(300)),
            StageCost::new(Stage::Grobner, Duration::from_millis(113))
                .with("max_matrix_columns", 859i64)
                .with_estimated_bytes(2_700_000),
            StageCost::new(Stage::Conversion, Duration::from_micros(80)).with("D", 1i64),
            StageCost::new(Stage::Univariate, Duration::from_micros(40)),
            StageCost::new(Stage::Verification, Duration::from_micros(10)),
        ];

        assert_eq!(run.elapsed(), Duration::from_micros(113_430));
        assert_eq!(
            run.stage(Stage::Grobner).expect("ran").estimated_peak_bytes,
            Some(2_700_000)
        );
        assert!(run.stage(Stage::Nothing).is_none());

        let json = run.to_json(&manifest).to_json();
        assert!(json.contains("\"stage\": \"univariate\""), "{}", json);
        assert!(json.contains("\"max_matrix_columns\": 859"), "{}", json);
        // The total is there as well, so a reader can check the stages against it.
        assert!(json.contains("\"elapsed_nanos\": 113430000"), "{}", json);
    }

    /// For an incomplete computation the highest completed degree is the one before the last.
    ///
    /// The last degree in a profile is the one that was running when the limit was crossed.
    /// Reporting it as completed would overstate the frontier by one degree, every time.
    #[test]
    fn test_the_highest_completed_degree_excludes_the_degree_that_failed() {
        use crate::grobner::f4::DegreeProfile;

        let mut profile = DegreeProfile::new();
        for degree in 2..=5 {
            profile.record_selection(degree, 1, 0);
        }

        let incomplete = GrobnerFrontier::default().with_profile(&profile);
        assert_eq!(incomplete.highest_completed_degree, Some(4));

        let complete = GrobnerFrontier {
            completed: true,
            ..GrobnerFrontier::default()
        }
        .with_profile(&profile);
        assert_eq!(complete.highest_completed_degree, Some(5));

        // One degree and a crossing: nothing completed, which is not the same as degree zero.
        let mut one = DegreeProfile::new();
        one.record_selection(2, 1, 0);
        assert_eq!(
            GrobnerFrontier::default()
                .with_profile(&one)
                .highest_completed_degree,
            None
        );
    }
}
