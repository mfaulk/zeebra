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

use crate::{
    grobner::{
        f4::{DegreeProfile, F4Statistics},
        research::{
            challenge::{BenchmarkClass, ChallengeManifest, Significance},
            record::{ExperimentRecord, Json},
        },
    },
    util::sha256_hex,
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

/// `git diff <range> | git patch-id --stable`, or empty if either side of the pipe fails.
///
/// Its own function because the pipe is the whole awkwardness: `git patch-id` reads a diff on
/// stdin and there is no `git diff --patch-id`.
fn patch_id(range: &str) -> String {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let diff = match Command::new("git").args(["diff", range]).output() {
        Ok(out) if out.status.success() => out.stdout,
        _ => return String::new(),
    };
    let mut child = match Command::new("git")
        .args(["patch-id", "--stable"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(_) => return String::new(),
    };
    if let Some(stdin) = child.stdin.as_mut() {
        // A broken pipe here is `git patch-id` having exited early, which the wait below reports.
        let _ = stdin.write_all(&diff);
    }
    drop(child.stdin.take());
    match child.wait_with_output() {
        // `<patch-id> <commit-id>`; the first field is the content hash and the one that is stable.
        Ok(out) if out.status.success() => String::from_utf8_lossy(&out.stdout)
            .split_whitespace()
            .next()
            .unwrap_or_default()
            .to_string(),
        _ => String::new(),
    }
}

/// The machine and the build a measurement came from.
///
/// Carried on every run because a runtime comparison across two of these is not a comparison.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Environment {
    /// The commit the binary was built from.
    ///
    /// **Not durable on its own.** A sweep run on a branch records that branch's commit, and a
    /// merge that rewrites history leaves the stamp dangling: reachable from nothing, so
    /// "re-measure at this commit" is an instruction no later reader can carry out (#505, where
    /// 315 of 387 competitive rows were in that state). [`Self::base_commit`] and
    /// [`Self::patch_id`] are the half that survives, and [`Self::stamp_is_resolvable`] is the
    /// check.
    pub commit: String,

    /// The commit the measured branch was cut from: `git merge-base HEAD origin/main`.
    ///
    /// Durable **by construction** — a merge base is an ancestor of `main` and nothing can make it
    /// stop being one — so this is what is still checkout-able after the branch is rebased,
    /// squashed or deleted. Equal to [`Self::commit`] when the measurement was taken on `main`.
    /// Empty in records written before the field existed, and in records whose branch commit was
    /// already gone when the field arrived.
    pub base_commit: String,

    /// `git patch-id --stable` over `base_commit..commit`: the measured delta by its content.
    ///
    /// A patch id hashes the diff, not the history, so it is unchanged by the rebase or squash that
    /// invalidated [`Self::commit`] — which is what lets a reader find the landed equivalent of a
    /// dangling branch commit, or confirm that a tree they reconstructed is the measured one.
    /// Empty when there is no delta to identify (`base_commit == commit`) and empty in records
    /// written before the field existed.
    pub patch_id: String,

    /// A machine label: hostname, or a description.
    pub machine: String,

    /// Logical CPUs, and whatever pinning policy was applied.
    pub cpu: String,

    /// Worker threads the solver was given. **1 for every uncontended figure**, which is what
    /// every record written before concurrency existed is read back as.
    ///
    /// Recorded beside [`Self::cpu`] rather than folded into it because it is the one condition the
    /// comparison path **refuses** on rather than merely caveats: a parallel wall clock and a
    /// single-threaded one are costs of different things, and a ratio between them read as a solver
    /// speedup would be false. See [`Comparison::of`].
    pub concurrency: usize,

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
            ("base_commit", Json::string(&self.base_commit)),
            ("patch_id", Json::string(&self.patch_id)),
            ("machine", Json::string(&self.machine)),
            ("cpu", Json::string(&self.cpu)),
            ("concurrency", Json::size(self.concurrency)),
            ("build", Json::string(&self.build)),
            ("policy", Json::string(&self.policy)),
        ])
    }

    /// The provenance fields read from git; every other field left empty for the caller.
    ///
    /// Three reads, each degrading to **empty rather than to a guess**: the commit, the merge base
    /// against `origin/main` (then `main`, for a checkout with no remote), and the patch id of the
    /// delta between them. A writer that cannot name its base records that it cannot, which
    /// [`Self::stamp_is_resolvable`] reports — the failure #505 is about is a stamp that *looks*
    /// resolvable and is not, so inventing a base here would be worse than leaving it blank.
    ///
    /// `concurrency` comes back `0`, which is not a valid worker count: every caller sets it, and a
    /// reader coerces an absent or zero count to 1.
    pub fn from_git() -> Self {
        let git = |arguments: &[&str]| -> String {
            std::process::Command::new("git")
                .args(arguments)
                .output()
                .ok()
                .filter(|out| out.status.success())
                .and_then(|out| String::from_utf8(out.stdout).ok())
                .map(|text| text.trim().to_string())
                .unwrap_or_default()
        };
        let commit = git(&["rev-parse", "--short", "HEAD"]);
        let base = ["origin/main", "main"]
            .iter()
            .map(|reference| git(&["merge-base", "HEAD", reference]))
            .find(|base| !base.is_empty())
            .unwrap_or_default();
        let base_short = if base.is_empty() {
            String::new()
        } else {
            git(&["rev-parse", "--short", &base])
        };
        // A patch id and not a tree hash, though the tree hash is the cheaper read. A tree object
        // lives only as long as something reaches it, so a tree hash recorded on a branch dies
        // with the branch — the same failure as the commit, one indirection along. A patch id is a
        // *function of the diff*, so a later reader recomputes it over a candidate range on `main`
        // and compares; it needs no object to have survived.
        let delta = if base.is_empty() || base_short == commit {
            String::new()
        } else {
            patch_id(&format!("{}..HEAD", base))
        };
        Self {
            commit,
            base_commit: base_short,
            patch_id: delta,
            machine: String::new(),
            cpu: String::new(),
            concurrency: 0,
            build: String::new(),
            policy: String::new(),
        }
    }

    /// Whether what this figure was measured with can still be reached.
    ///
    /// Two ways to pass, and recording [`Self::commit`] alone is neither: the measurement was taken
    /// at the base itself, so there is nothing to reconstruct; or it records a base — permanently
    /// reachable — **and** the patch id of the delta from it. A branch commit with no base is the
    /// #505 state: a stamp that satisfies #335's letter and resolves to nothing.
    ///
    /// Deliberately **not** part of [`Self::comparable`]: two figures taken at the same commit are
    /// comparable whether or not a later reader can check that commit out. Resolvability is a
    /// reproducibility property, not a comparability one.
    pub fn stamp_is_resolvable(&self) -> bool {
        if self.base_commit.is_empty() {
            return false;
        }
        self.base_commit == self.commit || !self.patch_id.is_empty()
    }

    /// Whether two runs were measured under conditions a runtime may be compared across.
    ///
    /// Concurrency is deliberately **not** here: a mismatch in it is refused by
    /// [`Comparison::of`] rather than carried as a caveat, so this answers the narrower question
    /// of whether the machine and the build agree.
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

    /// Peak **process** resident memory, measured, when the runner measured it.
    ///
    /// Deliberately not inside [`GrobnerFrontier`] and deliberately not named like
    /// `peak_estimated_bytes`, which is an estimate of the live matrix entries at 16 bytes apiece.
    /// The two differ by two orders of magnitude on an F4 run — 195 MB accounted inside a 14.75 GB
    /// process on Fukuoka III `n = 20` (#237) — so a reader must never be able to mistake one for
    /// the other. A route with no Macaulay matrix at all, like the resultant, has no frontier and
    /// would otherwise carry no memory figure.
    pub measured_peak_resident_bytes: Option<usize>,

    /// How many scoreboard rows the process that produced
    /// `measured_peak_resident_bytes` had recorded, including this one.
    ///
    /// **`VmHWM` is a process high-water mark, so attribution is not free.** A process that runs
    /// seven rows reports one figure covering all seven, and that figure is a *ceiling* over them
    /// rather than a measurement of any one — the row with the largest footprint sets it and the
    /// other six inherit it. `Some(1)` says the process ran this row and nothing else, which is
    /// the only case where the figure is this row's;
    /// [`Self::measured_peak_is_attributable`] is that check.
    ///
    /// `None` exactly when `measured_peak_resident_bytes` is `None`: the count is a property of
    /// the measurement and there is nothing to qualify without one. Absent in every record
    /// written before this field existed, where it must not be read as an attributable `1`.
    pub measured_peak_rows_in_process: Option<usize>,

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
                base_commit: String::new(),
                patch_id: String::new(),
                machine: String::new(),
                cpu: String::new(),
                concurrency: 1,
                build: String::new(),
                policy: String::new(),
            },
            experiment: None,
            measured_peak_resident_bytes: None,
            measured_peak_rows_in_process: None,
            reproduce: String::new(),
        }
    }

    /// The filename stem this run's own record is written under, without the extension.
    ///
    /// `<challenge>--<formulation slug>--<commit>--<twelve hex digits of [`Self::digest`]>`.
    ///
    /// **Uniqueness comes from the digest, and from nothing else in the name** (#540). The three
    /// readable components are there to be read; they are not what distinguishes one run from
    /// another, so the scheme no longer depends on prose spelling a slice index out.
    ///
    /// What that fixes, measured on the committed tree before the change:
    ///
    /// * **Sixteen retained runs had no record file that held them.** Identity was
    ///   `challenge--formulation--commit`, so a re-measurement at one commit overwrote its
    ///   predecessor's file — three `poseidon-t2-rf4-rp0-planted` runs at `86aaa53` measured
    ///   369.4 ms, 360.9 ms and 369.3 ms in Gröbner and only the last was on disk. The digest
    ///   covers the measurement, so those are now three names.
    /// * **Seven stems named a file that did not exist, and seven files matched no stem.** Both
    ///   sets numbered 89 and were not the same set: the slug rule had changed under the committed
    ///   names, leaving `…--resultant--slice-12-fixed--seed-1---c32--86aaa53.json` beside a
    ///   history row whose stem was `…--resultant,-slice(12-fixed,-seed-1)--86aaa53`. A stem
    ///   derived from prose through a rule that is free to change is a citation that can rot.
    ///
    /// Two byte-identical records still share a stem, and that is correct: they are
    /// interchangeable, so one file holds both. [`colliding_run_file`] is what asserts that a
    /// shared stem means exactly that.
    pub fn run_file_stem(&self) -> String {
        format!(
            "{}--{}--{}--{}",
            self.challenge,
            formulation_slug(&self.formulation),
            self.environment.commit,
            self.short_digest()
        )
    }

    /// True if the measured peak is this row's and not a ceiling over several.
    ///
    /// Requires both a measurement and a row count of exactly one. An absent count is **not**
    /// attributable: every record written before the count existed has one, and treating those as
    /// single-row would be asserting something nobody recorded.
    pub fn measured_peak_is_attributable(&self) -> bool {
        self.measured_peak_resident_bytes.is_some() && self.measured_peak_rows_in_process == Some(1)
    }

    /// The measured process peak as a multiple of the accounted entry estimate.
    ///
    /// `measured / estimated`, and the interesting quantity rather than either figure alone: it is
    /// what says the 16-byte-per-entry estimate is an accounting of the Macaulay matrices and not
    /// a model of the process. 195 MB accounted inside a 14.75 GB process is a factor of 75.
    ///
    /// `None` unless the record carries both — a route with no Macaulay matrix, like the
    /// resultant, has no frontier and so no estimate, and a run on a platform with no `/proc` has
    /// no measurement. Also `None` for a zero estimate, which no ratio can use.
    ///
    /// Note that the ratio is only *about this row* when
    /// [`Self::measured_peak_is_attributable`]; otherwise the numerator is a ceiling over several
    /// rows and the ratio is an upper bound.
    pub fn measured_to_estimated_ratio(&self) -> Option<f64> {
        let measured = self.measured_peak_resident_bytes? as f64;
        let estimated = self.frontier.as_ref()?.peak_estimated_bytes as f64;
        if estimated <= 0.0 {
            return None;
        }
        Some(measured / estimated)
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
                // Absent in every record written before #505; empty reads as unrecorded.
                base_commit: field("base_commit"),
                patch_id: field("patch_id"),
                machine: field("machine"),
                cpu: field("cpu"),
                // Absent in every record written before concurrency was a field, and those runs
                // were single-threaded — so the default is the fact, not a guess.
                concurrency: environment
                    .get("concurrency")
                    .and_then(Json::as_int)
                    .unwrap_or(1)
                    .max(1) as usize,
                build: field("build"),
                policy: field("policy"),
            },
            experiment: None,
            // Absent in every record written before the field existed. `None` means "not
            // measured", which is the fact about those runs — it must never read as zero.
            measured_peak_resident_bytes: value
                .get("measured_peak_resident_bytes")
                .and_then(Json::as_int)
                .map(|b| b as usize),
            // Absent in every record written before the count existed, and absent must not read
            // as an attributable `1` — those runs' figures cover however many rows their process
            // ran, which is not recorded and cannot be recovered.
            measured_peak_rows_in_process: value
                .get("measured_peak_rows_in_process")
                .and_then(Json::as_int)
                .map(|rows| rows as usize),
            reproduce: value
                .get("reproduce")
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string(),
        })
    }

    /// The record as JSON.
    pub fn to_json(&self, manifest: &ChallengeManifest) -> Json {
        let mut fields = self.json_fields();
        // `significance` is the one field the record cannot compute alone, and it is inserted
        // rather than appended so the key order is unchanged from when it was written inline.
        let at = fields
            .iter()
            .position(|(key, _)| *key == "verification")
            .expect("`verification` is always emitted");
        fields.insert(
            at,
            (
                "significance",
                Json::string(self.significance(manifest).to_string()),
            ),
        );
        Json::object(fields)
    }

    /// Every field of the record except `significance`, which is derived from the registry.
    ///
    /// Split out so that [`Self::canonical`] covers the whole record without a second field list
    /// to keep in step: a field added here is in the digest, and therefore in the identity, by
    /// construction rather than by remembering.
    fn json_fields(&self) -> Vec<(&'static str, Json)> {
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
        // Omitted rather than `null` when absent, matching `ExperimentRecord`: "not measured" is
        // the fact about those runs, and a key holding `null` invites being coerced to zero.
        if let Some(bytes) = self.measured_peak_resident_bytes {
            fields.push(("measured_peak_resident_bytes", Json::Int(bytes as i128)));
            if let Some(rows) = self.measured_peak_rows_in_process {
                fields.push(("measured_peak_rows_in_process", Json::size(rows)));
            }
        }
        fields.push(("environment", self.environment.to_json()));
        fields.push((
            "experiment",
            match &self.experiment {
                Some(experiment) => experiment.to_json(),
                None => Json::Null,
            },
        ));
        fields.push(("reproduce", Json::string(&self.reproduce)));
        fields
    }

    /// The record as canonical JSON: every field except the registry-derived `significance`.
    ///
    /// `Json`'s serializer is deterministic and its objects keep insertion order, so this is the
    /// same bytes for the same record on any machine — which is what lets [`Self::digest`] stand
    /// in for the record's content.
    ///
    /// `significance` is excluded because it is a function of the manifest and the outcome, so two
    /// runs of one challenge with one outcome cannot differ in it, and including it would make the
    /// identity depend on a file this record does not carry.
    pub fn canonical(&self) -> String {
        Json::object(self.json_fields()).to_json()
    }

    /// SHA-256 of [`Self::canonical`], lowercase hex: this *run's* identity, as
    /// [`ChallengeManifest::digest`] is its problem's.
    pub fn digest(&self) -> String {
        sha256_hex(self.canonical().as_bytes())
    }

    /// The first twelve hex digits of [`Self::digest`], which is what the filename carries.
    pub fn short_digest(&self) -> String {
        self.digest()[..12].to_string()
    }
}

/// A formulation as a filename component: anything outside `[A-Za-z0-9._-]` becomes `-`, and runs
/// of `-` collapse.
///
/// Previously the rule was `replace(' ', "-")`, which left `(`, `)` and `,` in 41 of the committed
/// filenames and — because the rule itself changed over time — orphaned seven files whose names no
/// longer matched any stem the code produces. Sanitizing is not what makes a name unique; the
/// digest is. This only keeps the readable part of the name a filename.
fn formulation_slug(formulation: &str) -> String {
    let mut slug = String::with_capacity(formulation.len());
    for character in formulation.chars() {
        if character.is_ascii_alphanumeric() || matches!(character, '.' | '_' | '-') {
            slug.push(character);
        } else if !slug.ends_with('-') {
            slug.push('-');
        }
    }
    slug.trim_matches('-').to_string()
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

    /// Two runs of the same problem were measured at different degrees of parallelism.
    ///
    /// Refused rather than caveated. A parallel wall clock divided by a single-threaded one is a
    /// core count, not a solver speedup, and the ratio is the number a reader would quote. The
    /// single-threaded figures stay comparable with each other and with every row recorded before
    /// any of this was parallel; a scaling study compares the concurrencies itself, outside the
    /// scoreboard.
    DifferentConcurrency {
        /// The problem both runs are of.
        id: String,
        /// The baseline's worker count.
        baseline: usize,
        /// The candidate's.
        candidate: usize,
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
            Self::DifferentConcurrency {
                id,
                baseline,
                candidate,
            } => write!(
                f,
                "refusing to compare {} at concurrency {} against concurrency {}: the ratio would \
                 be a core count rather than a speedup",
                id, candidate, baseline
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
    ///
    /// [`ScoreboardError::DifferentConcurrency`] when the two were measured on different worker
    /// counts — the one condition that makes a ratio of wall clocks mean something other than what
    /// it looks like. A difference in machine or build is a caveat because the comparison is still
    /// of the same quantity measured imperfectly; a difference in concurrency is not.
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

        if baseline.environment.concurrency != candidate.environment.concurrency {
            return Err(ScoreboardError::DifferentConcurrency {
                id: baseline.challenge.clone(),
                baseline: baseline.environment.concurrency,
                candidate: candidate.environment.concurrency,
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

/// What `research/scoreboard/results/history.json` promises a consumer, written into the file.
///
/// **The append-only property is load-bearing, not housekeeping.** [`Scoreboard`] keeps its runs
/// in insertion order and [`Scoreboard::load`] preserves the order of the file, so array position
/// is the only record of *when* a run was taken — and [`Scoreboard::verified_somehow`] reads it to
/// break a tie on worker count. A rewrite that sorted, deduplicated or regenerated the array would
/// leave every record present and make the rendered representative arbitrary, which is the kind of
/// change that does not look like a change.
///
/// Lives here rather than in the writer because it describes an assumption of *this* module's
/// code, and because `test_the_committed_history_declares_its_append_only_contract` compares the
/// committed file against it character for character.
pub const HISTORY_CONTRACT: &str = "every run ever recorded, APPEND-ONLY and in the order \
     recorded. Array position is the only record of when a run was taken, and \
     results/solved.json's tie-break reads it: among verified witnesses tied on \
     environment.concurrency it keeps the LAST, because the later record is the one later code \
     wrote and so carries at least as many fields. Appending is safe; sorting, deduplicating or \
     regenerating this file is not, and would silently change what solved.json claims. run_count \
     must equal runs.length.";

/// What `research/scoreboard/results/best.json` promises a consumer.
///
/// [`Scoreboard::best`] is [`Scoreboard::best_at`] at one worker, so this file is a **like-for-like
/// serial ranking** and a problem solved only on multiple workers is absent from it by design. Ask
/// `solved.json` for solved status.
pub const BEST_CONTRACT: &str = "the fastest verified witness per problem AMONG SINGLE-THREADED \
     RUNS. A problem solved only on multiple workers is deliberately absent; ask solved.json for \
     solved status.";

/// What `research/scoreboard/results/solved.json` promises a consumer.
///
/// Describes [`Scoreboard::verified_somehow`], **including its dependency on the order of
/// `history.json`** — see that method and [`HISTORY_CONTRACT`]. The string committed before M25
/// said the tie went "to the first recorded" while the code kept the last; a contract a consumer
/// cannot check is a contract that drifts, which is why it is a constant here and asserted against
/// the committed file.
pub const SOLVED_CONTRACT: &str = "one verified witness per problem at ANY concurrency -- an \
     existence claim, not a ranking. The representative is the one using the fewest workers, ties \
     to the LAST recorded in history.json; no runtimes are compared across worker counts. That \
     tie-break reads the order of history.json, which is append-only -- see its contract field. \
     Every entry carries environment.concurrency, and an entry with concurrency > 1 is not \
     comparable with a figure in best.json.";

/// Two runs that differ but whose per-run filenames would not.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunFileCollision {
    /// The filename stem both runs map to.
    pub stem: String,

    /// The formulation of the run that would be overwritten.
    pub first: String,

    /// The formulation of the run that would overwrite it.
    pub second: String,
}

impl Display for RunFileCollision {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?} and {:?} would both be written to {}.json",
            self.first, self.second, self.stem
        )
    }
}

/// The first pair of runs in `runs` that differ in content but would share a per-run filename.
///
/// The failure this detects is **silent**: one record overwrites another and the directory simply
/// has one fewer file than there were runs, with nothing to notice. The writer calls it before
/// writing anything, so a collision stops the run instead of losing a record.
///
/// Since #540 the stem carries [`RunRecord::short_digest`], so **a shared stem means the two
/// records are the same content** — interchangeable, and one file legitimately holds both. What
/// this function now checks is that the digest is doing that job: a shared stem whose canonical
/// forms differ is a twelve-hex-digit collision, or a bug in [`RunRecord::canonical`], and either
/// way it must stop the write rather than silently drop a record.
///
/// The comparison is on [`RunRecord::canonical`] and not on the formulation, which is what it used
/// to be: the formulation alone could not see two runs that differed only in their measurement,
/// which is exactly the sixteen runs #540 was filed for.
pub fn colliding_run_file(runs: &[RunRecord]) -> Option<RunFileCollision> {
    let mut seen: BTreeMap<String, (&str, String)> = BTreeMap::new();
    for run in runs {
        let stem = run.run_file_stem();
        let canonical = run.canonical();
        match seen.get(&stem) {
            Some((first, first_canonical)) if *first_canonical != canonical => {
                return Some(RunFileCollision {
                    stem,
                    first: first.to_string(),
                    second: run.formulation.clone(),
                })
            }
            Some(_) => {}
            None => {
                seen.insert(stem, (run.formulation.as_str(), canonical));
            }
        }
    }
    None
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

    /// The fastest verified witness for each problem, among **uncontended** runs.
    ///
    /// **Witnesses only.** Runs that stopped at a limit are not ranked against each other: a
    /// higher degree does not mean less work remains, so there is no ordering to impose. Those
    /// appear in [`Self::unfinished`] instead, and in the rendered table beside this one.
    ///
    /// **Single-threaded only**, which is [`Self::best_at`]'s doc comment.
    pub fn best(&self) -> BTreeMap<&str, &RunRecord> {
        self.best_at(1)
    }

    /// The same, among runs measured on `concurrency` workers.
    ///
    /// [`Self::best`] is `best_at(1)`, and that asymmetry is deliberate: the rendered table is the
    /// headline a reader takes away, and a parallel wall clock dropped into it would displace the
    /// single-threaded figure it is **not comparable with** — the same refusal
    /// [`ScoreboardError::DifferentConcurrency`] makes explicit. A parallel figure is reported by
    /// this method, by its own run file, and by the research document that measured it, never by
    /// quietly becoming the row a reader reads as progress.
    pub fn best_at(&self, concurrency: usize) -> BTreeMap<&str, &RunRecord> {
        let mut best: BTreeMap<&str, &RunRecord> = BTreeMap::new();
        for run in &self.runs {
            if !run.outcome.is_verified_witness() || run.environment.concurrency != concurrency {
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

    /// One verified witness per problem at **any** concurrency — an existence claim, not a ranking.
    ///
    /// [`Self::best`] admits single-threaded runs only, so that a parallel wall clock cannot
    /// displace the figure it is not comparable with. That rule is right and this method does not
    /// weaken it. It exists because the *fallback* was wrong: a problem whose only witness was
    /// parallel fell through to [`Self::unfinished`] and rendered as a resource stop, so the
    /// headline table asserted that no witness existed for a problem that had one. An absent row is
    /// a gap a reader can see; a row naming a limit is a false statement about what is known.
    ///
    /// **The representative is chosen without comparing runtimes, and that is deliberate.** Ranking
    /// an 8-worker run against a 32-worker one would reintroduce exactly the cross-concurrency
    /// comparison [`ScoreboardError::DifferentConcurrency`] refuses in [`Comparison::of`], and it
    /// would do so in the one place a reader takes a figure away from. The rule is instead: the
    /// **fewest workers**, then the **most recently recorded**. Among witnesses for one problem the
    /// one making the smallest hardware demand is the strongest existence claim, and it is the
    /// nearest thing to the serial figure the table is otherwise built from.
    ///
    /// The tie-break is "latest", not "first", and that was a correction: history is appended, so
    /// two runs of one row at the same worker count differ by *when* they were recorded, and the
    /// later one is written by later code. Preferring the earlier one made the rendered row drop a
    /// `measured_peak_resident_bytes` that the newer record carried — a tie-break silently
    /// choosing the less complete record. Neither candidate's runtime is read either way.
    ///
    /// # The precondition: insertion order must be chronological
    ///
    /// **"Later" is read off the position in `self.runs` and nowhere else.** No record carries a
    /// timestamp, so the tie-break is sound only while position is chronology, which rests on two
    /// properties that are easy to break without noticing:
    ///
    /// * [`Self::load`] preserves the order of the `runs` array it is given, and
    /// * `research/scoreboard/results/history.json` is **append-only** — see [`HISTORY_CONTRACT`],
    ///   which is written into the file so that a consumer sees it too.
    ///
    /// Sorting, deduplicating or regenerating that history would leave every record present and
    /// make this choice arbitrary. Both properties are pinned by tests:
    /// `test_loading_a_history_preserves_its_recorded_order`,
    /// `test_the_tie_break_depends_on_the_recorded_order`, and
    /// `test_the_committed_history_declares_its_append_only_contract`.
    ///
    /// The cheaper alternative considered and not taken was a per-run timestamp. It would remove
    /// the dependency, but it would also add a field to every record for the sake of a tie that
    /// arises once in ninety-three runs, and it would not make the *rendering* of a tie any more
    /// meaningful — the two candidates still differ only in completeness, which is what "latest"
    /// is a proxy for. Worth revisiting if history ever stops being append-only for some other
    /// reason.
    ///
    /// Use [`Self::best_at`] to compare runtimes within a fixed worker count.
    pub fn verified_somehow(&self) -> BTreeMap<&str, &RunRecord> {
        let mut found: BTreeMap<&str, &RunRecord> = BTreeMap::new();
        for run in &self.runs {
            if !run.outcome.is_verified_witness() {
                continue;
            }
            found
                .entry(run.challenge.as_str())
                .and_modify(|current| {
                    // Fewest workers wins; `<=` makes a tie keep the *latest*, since `self.runs`
                    // is in insertion order and history is appended. No runtime is read.
                    if run.environment.concurrency <= current.environment.concurrency {
                        *current = run;
                    }
                })
                .or_insert(run);
        }
        found
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
            let solved = self.verified_somehow();
            for manifest in members {
                let result = match best.get(manifest.id) {
                    Some(run) => format!(
                        "**{}** in {:.1} ms ({})",
                        run.outcome,
                        run.elapsed().as_secs_f64() * 1e3,
                        run.formulation
                    ),
                    // A witness measured on more than one worker does not enter `best`, so that
                    // it cannot displace a single-threaded figure. It must still be reported here:
                    // falling straight through to `unfinished` rendered a resource stop for a
                    // problem that is solved, which is a false statement rather than a missing one.
                    // The concurrency is in the cell, so the figure cannot be read as serial.
                    None => match solved.get(manifest.id) {
                        Some(run) => format!(
                            "**{}** in {:.1} ms on {} workers ({})",
                            run.outcome,
                            run.elapsed().as_secs_f64() * 1e3,
                            run.environment.concurrency,
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
                 last stage that completed.\n\nOne row per distinct rendering, not per run: \
                 repeated runs of the same problem differ in commit and elapsed time, and this \
                 table has a column for neither, so `runs` says how many a row stands for and \
                 `commits` says where they were taken. A row reading `3` is three runs that \
                 agreed, not one run recorded three times.\n\n",
            );
            out.push_str(
                "| problem | formulation | outcome | deg | last deg done | max cols | peak MB | \
                 runs | commits |\n\
                 |---|---|---|---:|---:|---:|---:|---:|---|\n",
            );
            // Runs whose every rendered column agrees are one row carrying their count, and the
            // commits they were taken at are what distinguishes them (#506). Repeats are real —
            // three `poseidon-t3-rf2-rp1-planted` runs differ in commit and elapsed time, neither
            // of which this table has a column for — so they are counted rather than dropped, and
            // a reader tallying stopped runs off the table cannot overcount.
            let mut rows: Vec<(String, usize, Vec<&str>)> = Vec::new();
            for run in unfinished {
                // A campaign summary is a tally over its slices and has no matrix of its own, so
                // there is nothing to put in these four columns. An em dash rather than a zero
                // from `unwrap_or_default`: a row that measured nothing must not read as a row
                // that measured zero in a table whose other rows are measurements.
                let figures = match &run.frontier {
                    Some(frontier) => format!(
                        "{} | {} | {} | {:.1}",
                        frontier.max_pair_degree,
                        frontier
                            .highest_completed_degree
                            .map_or("none".to_string(), |d| d.to_string()),
                        frontier.max_matrix_columns,
                        frontier.peak_estimated_bytes as f64 / 1e6,
                    ),
                    None => "— | — | — | —".to_string(),
                };
                let rendered = format!(
                    "| `{}` | {} | {} | {} |",
                    run.challenge,
                    run.formulation,
                    run.outcome.short(),
                    figures,
                );
                let commit = run.environment.commit.trim();
                match rows.iter_mut().find(|(text, _, _)| *text == rendered) {
                    Some((_, count, commits)) => {
                        *count += 1;
                        if !commit.is_empty() && !commits.contains(&commit) {
                            commits.push(commit);
                        }
                    }
                    None => rows.push((
                        rendered,
                        1,
                        if commit.is_empty() {
                            Vec::new()
                        } else {
                            vec![commit]
                        },
                    )),
                }
            }
            for (rendered, count, commits) in rows {
                out.push_str(&format!(
                    "{} {} | {} |\n",
                    rendered,
                    count,
                    if commits.is_empty() {
                        "—".to_string()
                    } else {
                        commits.join(", ")
                    },
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
        wilson_interval, Campaign, Comparison, Environment, GrobnerFrontier, Json, Limit,
        RunOutcome, RunRecord, Scoreboard, ScoreboardError, Stage, StageCost,
    };
    use crate::grobner::research::{challenge, registry, Significance};

    fn environment() -> Environment {
        Environment {
            commit: "deadbeef".to_string(),
            base_commit: "deadbeef".to_string(),
            patch_id: String::new(),
            machine: "workstation".to_string(),
            cpu: "64 logical, taskset 0-7".to_string(),
            concurrency: 1,
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

    /// A problem whose only witness is parallel renders as solved, not as a resource stop.
    ///
    /// The defect this guards: `best` admits single-threaded runs only, so a parallel witness fell
    /// through to `unfinished` and the headline table printed that run's limit — asserting no
    /// witness existed for a problem that had one. A missing row is a gap; a row naming a limit is
    /// a false statement.
    #[test]
    fn test_a_parallel_witness_is_not_rendered_as_a_resource_stop() {
        let registry = registry();
        let mut board = Scoreboard::new();

        let mut stopped = witness(
            "poseidon31-cico-t16-rf2-rp4",
            "as generated",
            9_717,
            1 << 20,
        );
        stopped.outcome = RunOutcome::StoppedAtLimit(Limit {
            resource: "max_live_nonzeros".to_string(),
            detail: "20000001 live nonzero entries were needed".to_string(),
            degree: Some(5),
            last_completed_stage: Stage::Generation,
        });
        stopped.frontier = Some(GrobnerFrontier::default());
        board.add(stopped, &registry).expect("registered");

        let mut parallel = witness(
            "poseidon31-cico-t16-rf2-rp4",
            "resultant, slice(12 fixed, seed 1)",
            3_429_792,
            1 << 20,
        );
        parallel.environment.concurrency = 32;
        board.add(parallel, &registry).expect("registered");

        // The serial table still refuses the parallel figure, which is the rule that was right.
        assert!(
            !board.best().contains_key("poseidon31-cico-t16-rf2-rp4"),
            "a 32-worker run must not enter the single-threaded headline"
        );
        assert_eq!(
            board
                .verified_somehow()
                .get("poseidon31-cico-t16-rf2-rp4")
                .map(|r| r.environment.concurrency),
            Some(32)
        );

        let rendered = board.to_markdown(&registry);
        let row = rendered
            .lines()
            .find(|l| l.contains("poseidon31-cico-t16-rf2-rp4"))
            .expect("the row is rendered");
        assert!(
            row.contains("on 32 workers"),
            "the row must state the concurrency so it cannot be read as serial: {row}"
        );
        assert!(
            !row.contains("max_live_nonzeros"),
            "a solved problem must not render as the resource stop of an earlier run: {row}"
        );
    }

    /// The parallel fallback picks a representative without comparing runtimes across worker counts.
    ///
    /// `Comparison::of` refuses a cross-concurrency comparison outright, so the renderer's fallback
    /// must not perform one by the back door. The rule is fewest workers, then first recorded: here
    /// the 8-worker run is chosen over a 32-worker run that is **four times faster**, which is the
    /// whole point — a faster wall clock bought with four times the cores is not a better result,
    /// and the one place a reader takes a figure away from is the worst place to imply it is.
    #[test]
    fn test_the_parallel_fallback_does_not_rank_across_worker_counts() {
        let registry = registry();
        let mut board = Scoreboard::new();

        let mut wide = witness(
            "poseidon31-cico-t16-rf2-rp4",
            "resultant, 32 workers",
            1_000,
            1 << 20,
        );
        wide.environment.concurrency = 32;
        board.add(wide, &registry).expect("registered");

        let mut narrow = witness(
            "poseidon31-cico-t16-rf2-rp4",
            "resultant, 8 workers",
            4_000,
            1 << 20,
        );
        narrow.environment.concurrency = 8;
        board.add(narrow, &registry).expect("registered");

        let chosen = board
            .verified_somehow()
            .get("poseidon31-cico-t16-rf2-rp4")
            .map(|r| (r.environment.concurrency, r.elapsed()))
            .expect("a witness exists");
        assert_eq!(
            chosen.0, 8,
            "fewest workers must win, not the fastest wall clock"
        );
        assert_eq!(chosen.1, Duration::from_millis(4_000));

        // And neither enters the single-threaded headline.
        assert!(!board.best().contains_key("poseidon31-cico-t16-rf2-rp4"));

        let row = board
            .to_markdown(&registry)
            .lines()
            .find(|l| l.contains("poseidon31-cico-t16-rf2-rp4"))
            .map(str::to_string)
            .expect("the row is rendered");
        assert!(row.contains("on 8 workers"), "{row}");
    }

    /// `measured_peak_resident_bytes` round-trips, and its absence reads as "not measured".
    ///
    /// It must never default to zero. A route with no Macaulay matrix carries no
    /// `peak_estimated_bytes` either, so a zero here would be the only memory figure a reader
    /// sees and would say the run used none.
    #[test]
    fn test_a_measured_peak_is_distinct_from_an_estimate_and_optional() {
        let manifest = challenge("poseidon31-cico-t16-rf2-rp4").expect("registered");

        let mut run = witness("poseidon31-cico-t16-rf2-rp4", "resultant", 3_429_792, 0);
        run.frontier = None;
        run.measured_peak_resident_bytes = Some(56_987_300_000);
        let json = run.to_json(&manifest).to_json();
        assert!(json.contains("measured_peak_resident_bytes"));
        assert!(
            !json.contains("peak_estimated_bytes"),
            "a route with no matrix must not emit an entry-storage estimate"
        );
        let back = RunRecord::from_json(&super::Json::parse(&json).expect("valid"), &manifest)
            .expect("round trips");
        assert_eq!(back.measured_peak_resident_bytes, Some(56_987_300_000));

        // A record written before the field existed parses as not-measured, not as zero.
        let mut old = witness("poseidon31-cico-t16-rf2-rp4", "resultant", 1_000, 0);
        old.measured_peak_resident_bytes = None;
        let text = old.to_json(&manifest).to_json();
        assert!(!text.contains("measured_peak_resident_bytes"));
        let parsed = RunRecord::from_json(&super::Json::parse(&text).expect("valid"), &manifest)
            .expect("round trips");
        assert_eq!(parsed.measured_peak_resident_bytes, None);
    }

    /// Two witnesses at the same worker count: the tie goes to the later, more complete record.
    ///
    /// Found by the six-round row producing two records at 32 workers, the second carrying a
    /// `measured_peak_resident_bytes` the first predated. A "first recorded" tie-break silently
    /// rendered the less complete one, which is the sort of thing a scoreboard should not do
    /// quietly. Still no runtime is compared — the earlier record here is the *faster* one.
    #[test]
    fn test_a_tie_on_worker_count_keeps_the_later_record() {
        let registry = registry();
        let mut board = Scoreboard::new();

        let mut earlier = witness(
            "poseidon31-cico-t16-rf2-rp4",
            "resultant, first pass",
            3_274_316,
            1 << 20,
        );
        earlier.environment.concurrency = 32;
        earlier.measured_peak_resident_bytes = None;
        board.add(earlier, &registry).expect("registered");

        let mut later = witness(
            "poseidon31-cico-t16-rf2-rp4",
            "resultant, second pass",
            3_429_792,
            1 << 20,
        );
        later.environment.concurrency = 32;
        later.measured_peak_resident_bytes = Some(56_990_154_752);
        board.add(later, &registry).expect("registered");

        let solved = board.verified_somehow();
        let chosen = solved
            .get("poseidon31-cico-t16-rf2-rp4")
            .expect("a witness exists");
        assert_eq!(
            chosen.formulation, "resultant, second pass",
            "the tie must keep the later record, which is the one later code wrote"
        );
        assert_eq!(
            chosen.measured_peak_resident_bytes,
            Some(56_990_154_752),
            "and it must therefore carry the measured figure the earlier record lacked"
        );
    }

    /// Two formulations whose slugs are the same no longer share a filename — #540.
    ///
    /// `"slice 3"` and `"slice-3"` slug identically, and under the old scheme that was a silent
    /// overwrite: one record replaced the other and the directory simply had one fewer file than
    /// there were runs. The digest closes it from both sides, and that is worth asserting
    /// explicitly because the collision check can no longer demonstrate it: `canonical` covers the
    /// formulation, so two records that slug the same still digest differently.
    #[test]
    fn test_formulations_that_slug_alike_no_longer_share_a_filename() {
        let one = witness("poseidon31-cico-t16-rf2-rp4", "slice 3", 1_000, 1 << 20);
        let other = witness("poseidon31-cico-t16-rf2-rp4", "slice-3", 2_000, 1 << 20);

        assert_ne!(
            one.run_file_stem(),
            other.run_file_stem(),
            "two runs that slug alike must not share a record file"
        );
        assert!(
            one.run_file_stem().contains("slice-3"),
            "the readable part is still readable: {}",
            one.run_file_stem()
        );
        assert_eq!(
            super::colliding_run_file(&[one, other]).map(|c| c.stem),
            None,
            "distinct stems are not a collision"
        );
    }

    /// Two runs of one problem at one commit, differing only in what they measured, are two names.
    ///
    /// This is #540's sixteen runs in miniature: identity used to be
    /// `challenge--formulation--commit`, so the second record overwrote the first's file and the
    /// first was retained in the history with nothing on disk holding it.
    #[test]
    fn test_a_rerun_that_measured_something_else_gets_its_own_file() {
        let first = witness(
            "poseidon31-cico-t16-rf2-rp4",
            "resultant",
            3_274_316,
            1 << 20,
        );
        let second = witness(
            "poseidon31-cico-t16-rf2-rp4",
            "resultant",
            3_301_004,
            1 << 20,
        );

        assert_ne!(
            first.run_file_stem(),
            second.run_file_stem(),
            "a re-measurement is a different run and needs a different file"
        );
        assert_eq!(
            first
                .run_file_stem()
                .rsplit_once("--")
                .map(|(head, _)| head),
            second
                .run_file_stem()
                .rsplit_once("--")
                .map(|(head, _)| head),
            "and everything before the digest is the same, so the two sort together"
        );
        assert_eq!(super::colliding_run_file(&[first, second]), None);
    }

    /// The same record twice is one file, and that is not a collision.
    ///
    /// Two byte-identical records are interchangeable, so collapsing them is correct rather than
    /// lossy — it is the one case where a shared stem is the right answer.
    #[test]
    fn test_byte_identical_records_share_one_file() {
        let run = witness(
            "poseidon31-cico-t16-rf2-rp4",
            "resultant",
            3_274_316,
            1 << 20,
        );
        let copy = run.clone();

        assert_eq!(run.run_file_stem(), copy.run_file_stem());
        assert_eq!(run.canonical(), copy.canonical());
        assert_eq!(super::colliding_run_file(&[run, copy]), None);
    }

    /// The slug keeps a filename a filename: no parentheses, commas or spaces.
    ///
    /// 41 of the committed run files carried literal `(` and `)` before #540, and the rule that
    /// produced them had changed at least once — which is what orphaned seven of them from the
    /// history. The digest is what makes a name unique; this only keeps the readable part portable.
    #[test]
    fn test_the_formulation_slug_is_filename_safe() {
        assert_eq!(
            super::formulation_slug("resultant, slice(12 fixed, seed 1)"),
            "resultant-slice-12-fixed-seed-1"
        );
        assert_eq!(super::formulation_slug("as published"), "as-published");
        assert_eq!(
            super::formulation_slug("a  b"),
            "a-b",
            "runs of separators collapse"
        );
        assert_eq!(
            super::formulation_slug("--edge--"),
            "edge",
            "and do not dangle"
        );

        let run = witness(
            "poseidon31-cico-t16-rf2-rp4",
            "resultant, slice(12 fixed, seed 1)",
            1_000,
            1 << 20,
        );
        let stem = run.run_file_stem();
        assert!(
            !stem.contains('(')
                && !stem.contains(')')
                && !stem.contains(',')
                && !stem.contains(' '),
            "{stem}"
        );
    }

    /// Runs whose filenames differ are not reported, and nor is the same run recorded twice.
    ///
    /// The second case matters: two records with the same formulation *are* the same row rerun,
    /// and the later one legitimately replaces the earlier file.
    #[test]
    fn test_distinct_filenames_and_an_honest_rerun_are_not_collisions() {
        let runs = vec![
            witness(
                "poseidon31-cico-t16-rf2-rp4",
                "slice(3 fixed, seed 0)",
                1,
                0,
            ),
            witness(
                "poseidon31-cico-t16-rf2-rp4",
                "slice(3 fixed, seed 1)",
                1,
                0,
            ),
            witness("poseidon31-cico-t16-rf2-rp4", "as generated", 1, 0),
        ];
        assert_eq!(super::colliding_run_file(&runs), None);

        let rerun = vec![
            witness("poseidon31-cico-t16-rf2-rp4", "as generated", 1, 0),
            witness("poseidon31-cico-t16-rf2-rp4", "as generated", 2, 0),
        ];
        assert_eq!(
            super::colliding_run_file(&rerun),
            None,
            "the same formulation twice is a rerun, not a collision"
        );
    }

    /// The committed run files are exactly the stems the writer would produce, with none lost.
    ///
    /// Checks the property as *files*: a silent overwrite shows up here as a directory with fewer
    /// entries than the history has distinct rows.
    #[test]
    fn test_the_committed_run_files_have_no_collisions() {
        let history = Json::parse(include_str!(
            "../../../research/scoreboard/results/history.json"
        ))
        .expect("committed history.json parses");
        let registry = registry();
        let board = Scoreboard::load(&history, &registry).expect("the committed history");
        assert_eq!(
            super::colliding_run_file(board.runs()),
            None,
            "two committed runs would share a per-run filename"
        );
    }

    /// A stamp resolves when it names a base, and a bare branch commit does not.
    ///
    /// The three cases #505 turns on. The middle one is the defect: a recorded commit satisfies
    /// #335's letter and resolves to nothing once the branch it names is rewritten away.
    #[test]
    fn test_a_stamp_resolves_only_when_it_names_a_reachable_base() {
        // Taken on `main`: the commit is its own base, and there is no delta to identify.
        let on_main = Environment {
            commit: "663097a".to_string(),
            base_commit: "663097a".to_string(),
            patch_id: String::new(),
            ..environment()
        };
        assert!(on_main.stamp_is_resolvable());

        // The #505 state: a branch commit and nothing else.
        let dangling = Environment {
            commit: "7adb29e".to_string(),
            base_commit: String::new(),
            patch_id: String::new(),
            ..environment()
        };
        assert!(!dangling.stamp_is_resolvable());

        // The same measurement, stamped: the base is an ancestor of `main` and stays one, and the
        // patch id identifies the delta by content rather than by a commit name.
        let stamped = Environment {
            commit: "7adb29e".to_string(),
            base_commit: "7ab1e86".to_string(),
            patch_id: "b2b959eaed689079fb7c88ff3095dbef54a4c756".to_string(),
            ..environment()
        };
        assert!(stamped.stamp_is_resolvable());

        // A base with no patch id, where the two differ, is not enough: the base alone does not say
        // what was measured on top of it.
        let half = Environment {
            patch_id: String::new(),
            ..stamped.clone()
        };
        assert!(!half.stamp_is_resolvable());

        // Resolvability is not comparability: these two differ only in what a reader can check out.
        assert!(dangling.comparable(&stamped));
    }

    /// The durable half of the stamp round-trips, and is absent rather than invented when missing.
    #[test]
    fn test_the_durable_stamp_round_trips_and_absence_stays_absent() {
        let manifest = challenge("poseidon31-cico-t16-rf2-rp4").expect("registered");
        let mut run = witness("poseidon31-cico-t16-rf2-rp4", "row", 1_000, 1 << 20);
        run.environment = Environment {
            commit: "7adb29e".to_string(),
            base_commit: "7ab1e86".to_string(),
            patch_id: "b2b959eaed689079fb7c88ff3095dbef54a4c756".to_string(),
            ..environment()
        };
        let text = run.to_json(&manifest).to_json();
        let back = RunRecord::from_json(&Json::parse(&text).expect("valid"), &manifest)
            .expect("round trips");
        assert_eq!(back.environment.base_commit, "7ab1e86");
        assert_eq!(
            back.environment.patch_id,
            "b2b959eaed689079fb7c88ff3095dbef54a4c756"
        );
        assert!(back.environment.stamp_is_resolvable());

        // A record written before the fields existed reads back unstamped, which is the fact about
        // it — never the commit copied into the base, which would claim it was taken on `main`.
        let legacy = Json::parse(&text.replace("\"base_commit\": \"7ab1e86\"", "\"unused\": \"\""))
            .expect("valid");
        let legacy = RunRecord::from_json(&legacy, &manifest).expect("round trips");
        assert_eq!(legacy.environment.commit, "7adb29e");
        assert!(legacy.environment.base_commit.is_empty());
        assert!(!legacy.environment.stamp_is_resolvable());
    }

    /// Every committed cryptanalysis run records a stamp a later reader can resolve.
    ///
    /// The scoreboard side of #505, which the competitive side is named for: one commit here —
    /// `1409a48`, two runs — was also unreachable from `main`. Its base `1985504` is an ancestor
    /// and stays one.
    ///
    /// **What this passing does not establish (#547).** The four `a3e5d66` runs were measured on
    /// #530's branch, cut *before* the stamp fields existed, and their `base_commit` and `patch_id`
    /// were reconstructed afterwards from the commit the records already named — following
    /// [`Environment::capture`] exactly, `merge-base` then `git diff base..HEAD | git patch-id
    /// --stable`. That makes them resolvable to the commit they name, which is what this asserts.
    /// It does **not** by itself make the delta recomputable from `main`, and the whole-commit range
    /// is the wrong place to look for it: `30348938..8d6f0cfe` does not reproduce `9762e649…`,
    /// because the squash also carries the four run records the measurement *produced*, which did
    /// not exist in the tree it was taken from. Compare the **code half** and the figures are
    /// reconstructable after all — `examples/scoreboard.rs`, `src/grobner/research/challenge.rs`
    /// and `src/grobner/research/mq.rs` each have the same patch id over `a772145..a3e5d66` as
    /// over `8d6f0cfe^..8d6f0cfe` (#550). So the measured tree is `a772145` plus a delta reachable
    /// from `main`.
    ///
    /// The general rule that leaves is narrower than "squash merges lose this": a patch id taken
    /// over a range that a later commit *extends* with the measurement's own output will not match
    /// that commit, and a reader checking one has to exclude the record files. A branch whose
    /// squash adds nothing beyond what was measured matches directly.
    #[test]
    fn test_every_committed_run_carries_a_resolvable_stamp() {
        let history = Json::parse(include_str!(
            "../../../research/scoreboard/results/history.json"
        ))
        .expect("committed history.json parses");
        let board = Scoreboard::load(&history, &registry()).expect("the committed history");

        let unresolvable: Vec<&str> = board
            .runs()
            .iter()
            .filter(|run| !run.environment.stamp_is_resolvable())
            .map(|run| run.challenge.as_str())
            .collect();
        assert!(
            unresolvable.is_empty(),
            "{} of {} runs record a commit nothing can resolve: {:?}",
            unresolvable.len(),
            board.runs().len(),
            unresolvable
        );
    }

    /// A measured peak carries the number of rows the measuring process ran, and round-trips.
    ///
    /// `VmHWM` is a **process** high-water mark, so a figure from a process that ran seven rows is
    /// a ceiling over all seven and not a measurement of any one of them. One row means the figure
    /// is attributable; more means it is not, and the record has to say which — a resource bound
    /// read as a resource measurement is the error the whole memory vocabulary here exists to
    /// prevent.
    #[test]
    fn test_a_measured_peak_records_how_many_rows_the_process_covered() {
        let manifest = challenge("poseidon31-cico-t16-rf2-rp4").expect("registered");

        let mut sole = witness("poseidon31-cico-t16-rf2-rp4", "row", 1_000, 1 << 20);
        sole.measured_peak_resident_bytes = Some(14_750_000_000);
        sole.measured_peak_rows_in_process = Some(1);
        assert!(sole.measured_peak_is_attributable());

        let text = sole.to_json(&manifest).to_json();
        let back = RunRecord::from_json(&Json::parse(&text).expect("valid"), &manifest)
            .expect("round trips");
        assert_eq!(back.measured_peak_resident_bytes, Some(14_750_000_000));
        assert_eq!(back.measured_peak_rows_in_process, Some(1));
        assert!(back.measured_peak_is_attributable());

        let mut shared = witness("poseidon31-cico-t16-rf2-rp4", "smoke", 1_000, 1 << 20);
        shared.measured_peak_resident_bytes = Some(14_750_000_000);
        shared.measured_peak_rows_in_process = Some(7);
        assert!(
            !shared.measured_peak_is_attributable(),
            "a seven-row process reports a ceiling, not this row's peak"
        );
        let text = shared.to_json(&manifest).to_json();
        let back = RunRecord::from_json(&Json::parse(&text).expect("valid"), &manifest)
            .expect("round trips");
        assert_eq!(back.measured_peak_rows_in_process, Some(7));
        assert!(!back.measured_peak_is_attributable());
    }

    /// With no measurement both memory keys are omitted, and absence parses as not-measured.
    ///
    /// Omission rather than `null`, matching `ExperimentRecord`, and the property every record
    /// written before these fields existed depends on: absent must never read as zero, and an
    /// absent row count must never read as an attributable figure.
    #[test]
    fn test_an_unmeasured_peak_omits_both_keys_and_is_not_attributable() {
        let manifest = challenge("poseidon31-cico-t16-rf2-rp4").expect("registered");
        let mut run = witness("poseidon31-cico-t16-rf2-rp4", "row", 1_000, 1 << 20);
        run.measured_peak_resident_bytes = None;
        run.measured_peak_rows_in_process = None;

        let text = run.to_json(&manifest).to_json();
        assert!(!text.contains("measured_peak_resident_bytes"));
        assert!(!text.contains("measured_peak_rows_in_process"));

        let back = RunRecord::from_json(&Json::parse(&text).expect("valid"), &manifest)
            .expect("round trips");
        assert_eq!(back.measured_peak_resident_bytes, None);
        assert_eq!(back.measured_peak_rows_in_process, None);
        assert!(!back.measured_peak_is_attributable());
        assert_eq!(back.measured_to_estimated_ratio(), None);
    }

    /// For an F4 row the estimated-to-measured ratio is recoverable from the record alone.
    ///
    /// The point of populating both figures. 195 MB of accounted matrix entries inside a 14.75 GB
    /// process is a factor of 75, and that factor is the interesting quantity — it is what says
    /// the entry estimate is not a model of the process.
    #[test]
    fn test_the_estimated_to_measured_ratio_is_recoverable_from_one_record() {
        let mut run = witness("poseidon31-cico-t16-rf2-rp4", "row", 1_000, 195_000_000);
        run.measured_peak_resident_bytes = Some(14_750_000_000);
        run.measured_peak_rows_in_process = Some(1);

        let ratio = run
            .measured_to_estimated_ratio()
            .expect("both figures are present");
        assert!(
            (ratio - 75.64).abs() < 0.01,
            "{} is not the 14.75 GB / 195 MB ratio",
            ratio
        );

        // A route with no Macaulay matrix has no estimate, so there is no ratio to report.
        run.frontier = None;
        assert_eq!(run.measured_to_estimated_ratio(), None);
    }

    /// Loading a history preserves the order the file recorded, record for record.
    ///
    /// The precondition `verified_somehow`'s tie-break rests on. If `load` ever sorted, deduped or
    /// reordered, insertion order would stop meaning "when it was recorded" and the tie-break
    /// would start choosing arbitrarily — silently, because every record would still be present.
    #[test]
    fn test_loading_a_history_preserves_its_recorded_order() {
        let registry = registry();
        let manifest = challenge("poseidon31-cico-t16-rf2-rp4").expect("registered");
        let formulations = ["first", "second", "third"];

        let entries: Vec<Json> = formulations
            .iter()
            .map(|formulation| {
                witness("poseidon31-cico-t16-rf2-rp4", formulation, 1_000, 1 << 20)
                    .to_json(&manifest)
            })
            .collect();
        let history = Json::object([("runs", Json::Array(entries))]);

        let board = Scoreboard::load(&history, &registry).expect("a history this program wrote");
        let order: Vec<&str> = board
            .runs()
            .iter()
            .map(|run| run.formulation.as_str())
            .collect();
        assert_eq!(
            order, formulations,
            "load must preserve the recorded order; the tie-break depends on it"
        );
    }

    /// The tie-break's answer depends on the recorded order, and the later record wins.
    ///
    /// The assumption stated as a test rather than as a comment: the **same two records** in the
    /// **other order** give the other representative. That is not a defect — it is the documented
    /// behaviour, and it is only sound because `results/history.json` is append-only, so position
    /// in the array *is* chronology. This test fails if that stops being true in either direction:
    /// if the ordering is lost, or if the tie-break stops reading it.
    #[test]
    fn test_the_tie_break_depends_on_the_recorded_order() {
        let registry = registry();
        let manifest = challenge("poseidon31-cico-t16-rf2-rp4").expect("registered");

        let at_32 = |formulation: &str, millis: u64| {
            let mut run = witness("poseidon31-cico-t16-rf2-rp4", formulation, millis, 1 << 20);
            run.environment.concurrency = 32;
            run.to_json(&manifest)
        };
        // Deliberately the *faster* run first, so that a tie-break reading runtimes rather than
        // order would pick it and fail this test.
        let faster = at_32("faster, recorded first", 1_000);
        let slower = at_32("slower, recorded second", 9_000);

        for (order, expected) in [
            (
                vec![faster.clone(), slower.clone()],
                "slower, recorded second",
            ),
            (vec![slower, faster], "faster, recorded first"),
        ] {
            let history = Json::object([("runs", Json::Array(order))]);
            let board = Scoreboard::load(&history, &registry).expect("a valid history");
            let solved = board.verified_somehow();
            let chosen = solved
                .get("poseidon31-cico-t16-rf2-rp4")
                .expect("a witness exists");
            assert_eq!(
                chosen.formulation, expected,
                "the representative must be the last-recorded of the tied pair"
            );
        }
    }

    /// The committed history declares, in the file, that it is append-only.
    ///
    /// The dependency is load-bearing for `solved.json`, and a consumer of the file cannot read a
    /// Rust doc comment. `run_count` is checked against the array for the same reason: a rewrite
    /// that dropped or reordered records is exactly what the contract forbids, and a mismatch is
    /// the cheapest evidence of one.
    #[test]
    fn test_the_committed_history_declares_its_append_only_contract() {
        let history = Json::parse(include_str!(
            "../../../research/scoreboard/results/history.json"
        ))
        .expect("committed history.json parses");

        let contract = history
            .get("contract")
            .and_then(Json::as_str)
            .expect("history.json carries a contract string");
        assert_eq!(
            contract,
            super::HISTORY_CONTRACT,
            "the committed contract must be the one the writer emits, character for character"
        );
        assert!(
            contract.contains("APPEND-ONLY"),
            "the contract must state the append-only dependency"
        );

        let runs = history.get("runs").expect("a runs array").items();
        let count = history
            .get("run_count")
            .and_then(Json::as_int)
            .expect("a run_count");
        assert_eq!(
            count as usize,
            runs.len(),
            "run_count disagrees with the array, so the file was rewritten rather than appended to"
        );
    }

    /// The **committed** result files honour their contracts, checked as files and not as renderer output.
    ///
    /// `best.json` and `solved.json` are what a machine consumer reads, and a renderer test says
    /// nothing about them. The defect this guards is the one that reached `main`: a problem solved
    /// only on multiple workers was absent from every machine-readable summary, so a consumer could
    /// not discover that it had a witness at all.
    #[test]
    fn test_the_committed_result_files_honour_their_contracts() {
        let best = Json::parse(include_str!(
            "../../../research/scoreboard/results/best.json"
        ))
        .expect("committed best.json parses");
        let solved = Json::parse(include_str!(
            "../../../research/scoreboard/results/solved.json"
        ))
        .expect("committed solved.json parses");

        // The contract strings are the writer's own constants, character for character. The
        // committed solved.json said the tie went "to the first recorded" while
        // `verified_somehow` kept the last — a contract nothing checked, so it drifted. This is
        // the check.
        assert_eq!(
            best.get("contract").and_then(Json::as_str),
            Some(super::BEST_CONTRACT),
            "best.json's contract has drifted from the writer's"
        );
        assert_eq!(
            solved.get("contract").and_then(Json::as_str),
            Some(super::SOLVED_CONTRACT),
            "solved.json's contract has drifted from the writer's"
        );
        assert!(
            super::SOLVED_CONTRACT.contains("LAST recorded"),
            "solved.json must describe the tie-break the code actually implements"
        );

        // Each states its own contract, so neither can be read as the other.
        for file in [&best, &solved] {
            let contract = file
                .get("contract")
                .and_then(Json::as_str)
                .expect("a stated contract");
            assert!(!contract.is_empty());
        }

        let ids = |file: &Json, key: &str| -> Vec<String> {
            file.get(key)
                .expect("the list")
                .items()
                .iter()
                .filter_map(|r| {
                    r.get("challenge")
                        .and_then(Json::as_str)
                        .map(str::to_string)
                })
                .collect()
        };
        let serial = ids(&best, "best");
        let any = ids(&solved, "solved");

        // The six-round row is solved on 32 workers. It must appear in `solved.json` and must NOT
        // appear in `best.json`, which is the serial performance ranking.
        const PARALLEL_ONLY: &str = "poseidon31-cico-t16-rf2-rp4";
        assert!(
            any.iter().any(|id| id == PARALLEL_ONLY),
            "a verified witness must be discoverable from solved.json"
        );
        assert!(
            !serial.iter().any(|id| id == PARALLEL_ONLY),
            "a 32-worker figure must not enter the single-threaded ranking"
        );

        // Every `best.json` row is single-threaded; every `solved.json` row states its concurrency.
        let concurrency = |r: &Json| {
            r.get("environment")
                .and_then(|e| e.get("concurrency"))
                .and_then(Json::as_int)
                .unwrap_or(1)
        };
        for row in best.get("best").expect("the list").items() {
            assert_eq!(concurrency(row), 1, "best.json must stay serial-only");
        }
        for row in solved.get("solved").expect("the list").items() {
            assert!(concurrency(row) >= 1);
        }

        // Everything serial-best is also solved; solved is the superset.
        for id in &serial {
            assert!(
                any.contains(id),
                "{id} is in best.json but missing from solved.json"
            );
        }
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

    /// The data rows of the "where the unfinished runs stopped" table, and nothing else.
    ///
    /// Filtering the whole document on a challenge id would also match that problem's row in the
    /// registry table above, so the section is sliced out first.
    fn unfinished_rows(markdown: &str) -> Vec<&str> {
        markdown
            .split("## Where the unfinished runs stopped")
            .nth(1)
            .expect("the section renders")
            .lines()
            .take_while(|l| !l.starts_with("## "))
            .filter(|l| l.starts_with("| `"))
            .collect()
    }

    /// Repeated runs of one problem collapse to one row carrying the count and the commits.
    ///
    /// Three runs of `poseidon-t3-rf2-rp1-planted` rendered three byte-identical rows (#506),
    /// because the table's columns omit the two fields that distinguish them — the commit and the
    /// elapsed time — so a reader tallying stopped runs off the table overcounted. The runs are
    /// real and must not be dropped: the row says how many there were and which commits they were
    /// taken at.
    #[test]
    fn test_repeated_unfinished_runs_render_as_one_row_with_a_count() {
        let registry = registry();
        let mut board = Scoreboard::new();
        for commit in ["744fdf9", "7e333fb", "7e333fb"] {
            let manifest = challenge("poseidon-t3-rf2-rp1-planted").expect("registered");
            let mut run = RunRecord::new(&manifest, "as generated");
            run.outcome = RunOutcome::StoppedAtLimit(Limit {
                resource: "max_matrix_columns".to_string(),
                detail: "the column budget of 60000 was crossed".to_string(),
                degree: Some(11),
                last_completed_stage: Stage::Grobner,
            });
            run.frontier = Some(GrobnerFrontier {
                max_pair_degree: 11,
                highest_completed_degree: Some(10),
                max_matrix_columns: 42_229,
                peak_estimated_bytes: 155_300_000,
                ..GrobnerFrontier::default()
            });
            run.environment = Environment {
                commit: commit.to_string(),
                ..environment()
            };
            board.add(run, &registry).expect("registered");
        }
        assert_eq!(board.unfinished().len(), 3, "three runs are retained");

        let markdown = board.to_markdown(&registry);
        let rows = unfinished_rows(&markdown);
        assert_eq!(rows.len(), 1, "one row for three identical renderings");
        assert!(
            rows[0].contains("| 3 |"),
            "the row states how many runs it stands for: {}",
            rows[0]
        );
        // First-seen order, not sorted: it is the order the history holds them in.
        assert!(
            rows[0].contains("744fdf9, 7e333fb"),
            "the row names the distinct commits: {}",
            rows[0]
        );
    }

    /// Two runs that disagree stay two rows, distinguished by the commit they were taken at.
    ///
    /// The other half of #506: `slice(12 fixed, seed 0)` on `poseidon31-cico-t16-rf2-rp0` appears
    /// twice with identical matrix figures and **different outcomes** — `basis_only` at `3fe69c6`
    /// and `slice_established_nothing` at `7e333fb`, the same computation under a later and more
    /// precise verdict. Collapsing those would assert they were one run; leaving them unlabelled
    /// left a reader with two contradictory rows and no way to order them.
    #[test]
    fn test_unfinished_runs_that_disagree_are_kept_apart_by_commit() {
        let registry = registry();
        let mut board = Scoreboard::new();
        for (commit, resource) in [
            ("3fe69c6", "basis only, no witness"),
            (
                "7e333fb",
                "the slice is empty, which says nothing about the problem",
            ),
        ] {
            let manifest = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
            let mut run = RunRecord::new(&manifest, "slice(12 fixed, seed 0)");
            run.outcome = RunOutcome::StoppedAtLimit(Limit {
                resource: resource.to_string(),
                detail: "recorded verdict".to_string(),
                degree: Some(4),
                last_completed_stage: Stage::Grobner,
            });
            run.frontier = Some(GrobnerFrontier {
                max_pair_degree: 4,
                highest_completed_degree: Some(4),
                max_matrix_columns: 17_424,
                peak_estimated_bytes: 102_778_752,
                ..GrobnerFrontier::default()
            });
            run.environment = Environment {
                commit: commit.to_string(),
                ..environment()
            };
            board.add(run, &registry).expect("registered");
        }

        let markdown = board.to_markdown(&registry);
        let rows = unfinished_rows(&markdown);
        assert_eq!(rows.len(), 2, "two verdicts are two rows");
        assert!(rows[0].contains("3fe69c6") && rows[1].contains("7e333fb"));
        assert!(
            rows.iter().all(|r| r.contains("| 1 |")),
            "each stands for one run: {:?}",
            rows
        );
    }

    /// A run whose environment records no commit renders an em dash rather than an empty cell.
    #[test]
    fn test_an_unfinished_run_without_a_commit_renders_a_dash() {
        let registry = registry();
        let mut board = Scoreboard::new();
        let manifest = challenge("poseidon-t3-rf2-rp1-planted").expect("registered");
        let mut run = RunRecord::new(&manifest, "as generated");
        run.outcome = RunOutcome::StoppedAtLimit(Limit {
            resource: "max_matrix_columns".to_string(),
            detail: "crossed".to_string(),
            degree: Some(11),
            last_completed_stage: Stage::Grobner,
        });
        run.environment = Environment {
            commit: String::new(),
            ..environment()
        };
        board.add(run, &registry).expect("registered");

        let markdown = board.to_markdown(&registry);
        let rows = unfinished_rows(&markdown);
        assert_eq!(rows.len(), 1);
        assert!(rows[0].ends_with("| 1 | — |"), "got {}", rows[0]);
    }

    /// A record with no Gröbner frontier renders dashes, not zeros.
    ///
    /// A campaign summary is a tally over its slices and has no matrix of its own, so
    /// `unwrap_or_default` put `0` in the degree, column and memory columns of a table whose other
    /// rows are measurements — a run that measured nothing reading as one that measured zero. The
    /// campaign row of the #454 diagnostic at Fukuoka VI `n = 24` is where this showed up.
    #[test]
    fn test_a_run_without_a_frontier_renders_no_figures() {
        let registry = registry();
        let mut board = Scoreboard::new();
        let manifest = challenge("fukuoka-mq-VI-n24-seed0").expect("registered");
        let mut run = RunRecord::new(&manifest, "campaign over 1 slices");
        run.outcome = RunOutcome::StoppedAtLimit(Limit {
            resource: "campaign reached no verdict".to_string(),
            detail: "all 1 slices stopped at a resource limit".to_string(),
            degree: None,
            last_completed_stage: Stage::Generation,
        });
        run.stages = vec![StageCost::new(
            Stage::Grobner,
            Duration::from_millis(50_922),
        )];
        run.frontier = None;
        run.environment = environment();
        board.add(run, &registry).expect("registered");

        let markdown = board.to_markdown(&registry);
        let row = markdown
            .lines()
            .find(|l| l.contains("campaign over 1 slices"))
            .expect("the campaign row is rendered");
        // The four figure columns, then the run count and the commit the run was taken at.
        assert!(
            row.ends_with("| — | — | — | — | 1 | deadbeef |"),
            "a row with no frontier must not report figures: {}",
            row
        );
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

    /// A parallel row is refused against a single-threaded one rather than caveated.
    #[test]
    fn test_a_concurrent_row_is_not_compared_against_an_uncontended_one() {
        let baseline = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            51_983,
            3_800_000,
        );
        let mut parallel = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            1_700,
            3_800_000,
        );
        parallel.environment.concurrency = 32;

        let refused = Comparison::of(&baseline, &parallel).expect_err("not comparable");
        assert_eq!(
            refused,
            ScoreboardError::DifferentConcurrency {
                id: "poseidon-t2-rf4-rp0-planted".to_string(),
                baseline: 1,
                candidate: 32,
            }
        );
        // The message says why, so a reader does not take it for a missing-field error.
        assert!(refused.to_string().contains("core count"), "{}", refused);
        // Refused in both directions: a single-threaded candidate against a parallel baseline is
        // the same false ratio upside down.
        assert!(Comparison::of(&parallel, &baseline).is_err());
        // And the single-core history stays comparable with itself.
        assert!(Comparison::of(&baseline, &baseline).is_ok());
    }

    /// A parallel row never displaces the single-core figure in the headline table.
    #[test]
    fn test_a_parallel_row_does_not_become_the_best() {
        let registry = registry();
        let mut board = Scoreboard::new();
        let single = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            51_983,
            3_800_000,
        );
        let mut parallel = witness(
            "poseidon-t2-rf4-rp0-planted",
            "as generated",
            1_700,
            3_800_000,
        );
        parallel.environment.concurrency = 32;
        board.add(single, &registry).expect("registered");
        board.add(parallel, &registry).expect("registered");

        // The faster row is 30x quicker and still not the one quoted: it is a core count.
        let best = board.best();
        assert_eq!(best.len(), 1);
        assert_eq!(
            best["poseidon-t2-rf4-rp0-planted"].elapsed().as_millis(),
            51_983
        );
        // It is reachable, just not by the headline.
        let parallel_best = board.best_at(32);
        assert_eq!(
            parallel_best["poseidon-t2-rf4-rp0-planted"]
                .elapsed()
                .as_millis(),
            1_700
        );
        // And the rendered table carries the single-core figure, not the parallel one.
        let markdown = board.to_markdown(&registry);
        assert!(markdown.contains("51983.0 ms"), "{}", markdown);
        assert!(!markdown.contains("1700.0 ms"), "{}", markdown);
    }

    /// Concurrency survives a round trip, and a record written without it reads as 1.
    #[test]
    fn test_concurrency_round_trips_and_defaults_to_one() {
        use crate::grobner::research::{challenge, Json};

        let registry = registry();
        let manifest = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
        let mut run = RunRecord::new(&manifest, "resultant, slice(12 fixed, seed 1)");
        run.environment = Environment {
            concurrency: 32,
            ..environment()
        };
        run.outcome = RunOutcome::VerifiedWitness;
        run.verification = "through the permutation".to_string();

        let stored = run.to_json(&manifest);
        let history = Json::object([("runs", Json::Array(vec![stored.clone()]))]);
        let loaded = Scoreboard::load(&Json::parse(&history.to_json()).expect("valid"), &registry)
            .expect("registered");
        assert_eq!(loaded.runs()[0].environment.concurrency, 32);

        // A record from before the field existed: its environment has no `concurrency`, and those
        // runs were single-threaded, so 1 is the fact rather than a guess.
        let text = stored.to_json().replace("\"concurrency\": 32,", "");
        assert!(!text.contains("concurrency"), "the field is gone");
        let legacy = Json::object([(
            "runs",
            Json::Array(vec![Json::parse(&text).expect("still valid JSON")]),
        )]);
        let loaded = Scoreboard::load(&Json::parse(&legacy.to_json()).expect("valid"), &registry)
            .expect("registered");
        assert_eq!(loaded.runs()[0].environment.concurrency, 1);
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
