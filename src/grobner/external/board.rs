//! The competitive board: one row per (problem, task, library), including the runs that failed.
//!
//! # What it records
//!
//! Each row is one library's attempt at one problem, identified by the digest of the exact text
//! every engine was handed — so two rows are the same problem only if they are the same bytes. Its
//! outcome vocabulary distinguishes an input a tool cannot represent from one it failed on, which
//! is the distinction a cross-library comparison exists to make; §6 of
//! `docs/research/external-comparison-protocol.md` has the argument.
//!
//! The conventions are the ones that make a board trustworthy: hand-rolled JSON through [`Json`],
//! a generated Markdown renderer so the human-readable table cannot drift from the data, identity
//! frozen by digest, an append-only history with its contract written into the file, and
//! **unsuccessful runs recorded rather than dropped** — a board that kept only its successes would
//! report each library's best cases as its behaviour.
//!
//! # Whose problems
//!
//! A ratio is published only for a problem whose ideal equivalence across engines is recorded, and
//! that record is a [`CorpusEntry`]. The board consults the public [`ladder`] by default; a caller
//! benchmarking systems of its own supplies their entries with [`CompetitiveBoard::with_corpus`]
//! and gets the same gates.
//!
//! # The one arithmetic rule
//!
//! A ratio is computed only by [`CompetitiveBoard::speedups`], which delegates to
//! [`RunReport::speedup_over`]'s checks and adds the two that are properties of the *environment*
//! rather than of the run: same machine, same build. Everything it refuses is recorded as the
//! resource limit or the missing capability instead of a number.

use std::{collections::BTreeMap, fmt::Write as _, time::Duration};

use super::{
    contract::{order_from_tag, order_tag, Invariants, LimitStop, Limits, RunFailure, Unsupported},
    corpus::{ladder, CorpusEntry, Equivalence},
    FieldSpec, Instance, RunReport, RunStatus, Verification,
};
use crate::{
    MonomialOrder,
    {grobner::record::Environment, util::Json},
};

/// What `research/competitive/results/history.json` promises a consumer.
///
/// Append-only for the same reason the cryptanalysis history is: array position is the only record
/// of when a row was taken. This board has no order-dependent tie-break today, but a renderer that
/// reported "the latest figure per library" would acquire one, and a history that had already been
/// reordered would make it wrong silently.
pub const COMPETITIVE_HISTORY_CONTRACT: &str = "every cross-library row ever recorded, \
     APPEND-ONLY and in the order recorded, INCLUDING the runs that produced no answer. A row \
     whose outcome is unsupported, stopped-by-limit or failed carries NO publishable time: see \
     docs/research/external-comparison-protocol.md section 3. Ratios are valid only between rows \
     agreeing on problem_digest, task, limits, machine and build, with both outcomes answered and \
     their invariants agreed.";

/// How a run ended, without the answer itself.
///
/// [`RunStatus`] carries the basis text, which a board row has no use for and which would make the
/// history unreadable. The discrimination is preserved exactly — in particular *unsupported* stays
/// distinct from *stopped by a limit*, which is the whole point.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome {
    /// The library answered, and nothing independent has checked it.
    Complete,

    /// The library answered and something independent agreed.
    Verified,

    /// A declared limit stopped it. The wall time **is** the limit.
    StoppedByLimit(LimitStop),

    /// The library cannot accept this input or task. **There is no time.**
    Unsupported(Unsupported),

    /// It failed. **There is no time**, and for three variants it did not even run:
    /// [`RunFailure::Unavailable`] (the tool is absent), [`RunFailure::Environment`] (the
    /// harness's own environment would have invalidated the measurement) and
    /// [`RunFailure::Harness`] (the harness's own filesystem work failed). All three render through
    /// [`Self::instead_of_a_time`] with text that says so.
    Failed(RunFailure),
}

impl Outcome {
    /// The stable tag used in records and tables.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::Complete => "complete",
            Self::Verified => "verified",
            Self::StoppedByLimit(_) => "stopped-by-limit",
            Self::Unsupported(_) => "unsupported",
            Self::Failed(_) => "failed",
        }
    }

    /// True if a wall time from this row may be used as a measurement.
    pub fn is_timing_evidence(&self) -> bool {
        matches!(self, Self::Complete | Self::Verified)
    }

    /// What goes in the cell where a time would be, when there is no time.
    ///
    /// The protocol's requirement that a failure record "the resource limit or the missing
    /// capability instead of a ratio", made concrete.
    pub fn instead_of_a_time(&self) -> Option<String> {
        // `prefixed` is idempotent: a detail that already begins with its tag is left alone, so a
        // row stored by an older writer — which saved the *rendered* form — does not acquire a
        // second prefix on the way out. `Outcome::detail` is what new rows store, and it is bare.
        let prefixed = |tag: &str, text: String| {
            if text.starts_with(tag) {
                text
            } else {
                format!("{}: {}", tag, text)
            }
        };
        match self {
            Self::Complete | Self::Verified => None,
            Self::StoppedByLimit(stop) => Some(stop.to_string()),
            Self::Unsupported(reason) => Some(prefixed("unsupported", reason.to_string())),
            Self::Failed(failure) => Some(prefixed("failed", failure.to_string())),
        }
    }

    /// The **bare** reason, with no `unsupported:`/`failed:` prefix.
    ///
    /// What gets stored. [`Self::instead_of_a_time`] adds the prefix for display, so storing its
    /// output and reading it back into a variant's detail field double-prefixed it on the next
    /// render — `unsupported: unsupported: characteristic ...`, visible in the first 72 rows the
    /// board ever held. The stored form has to be the datum, not the rendering of it.
    pub fn detail(&self) -> Option<String> {
        match self {
            Self::Complete | Self::Verified => None,
            Self::StoppedByLimit(stop) => Some(stop.to_string()),
            Self::Unsupported(reason) => Some(reason.to_string()),
            Self::Failed(failure) => Some(failure.to_string()),
        }
    }

    /// A short note for a table cell: the tag, or the tag with the reason.
    fn cell(&self) -> String {
        match self.instead_of_a_time() {
            Some(detail) => detail,
            None => self.tag().to_string(),
        }
    }
}

/// Why a stored row could not be read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BoardError {
    /// A field the board reads is missing, or is at the wrong type.
    MalformedRow { field: &'static str },
}

impl std::fmt::Display for BoardError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedRow { field } => write!(f, "a stored row has no usable {}", field),
        }
    }
}

impl std::error::Error for BoardError {}

/// One library's attempt at one task on one problem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompetitiveRecord {
    /// Schema version.
    pub schema: u32,

    /// The problem's corpus name. For humans.
    pub problem: String,

    /// Its identity digest. **The reference**; the name is for humans.
    pub problem_digest: String,

    /// The family, for grouping a table: `katsura`, `cyclic`, `mq`.
    pub family: String,

    /// What was asked. A column, and never conflated with another.
    pub task: super::Task,

    /// The coefficient field, precisely enough that two rows can be checked to share one.
    pub field: FieldSpec,

    /// The monomial order the task was posed under.
    pub order: MonomialOrder,

    /// How many variables.
    pub variable_count: usize,

    /// The library's id: `zeebra`, `singular`, `msolve`, `groebner.jl`, `sagebrush`.
    pub library: String,

    /// The library's version, as it reported it when probed.
    ///
    /// `None` only where the probe was not run, which is itself worth seeing: a figure without a
    /// version is not reproducible.
    pub library_version: Option<String>,

    /// The machine, build and commit. `Environment::policy` holds the limits summary.
    pub environment: Environment,

    /// The resources the run was allowed, declared before it started.
    pub limits: Limits,

    /// How it ended.
    pub outcome: Outcome,

    /// Invariants extracted from the answer, which is what a cross-library check compares.
    pub invariants: Invariants,

    /// What independently agreed, where anything did.
    pub verification: Option<Verification>,

    /// Wall-clock time, **only when the outcome is timing evidence**.
    ///
    /// Deliberately `None` rather than zero for an unsupported input, and deliberately `None`
    /// rather than the limit for a limit stop: the limit is in [`Self::limits`], and a consumer
    /// that read it here would be reading a bound as a measurement.
    pub wall: Option<Duration>,

    /// CPU time, where the platform reported one.
    pub cpu: Option<Duration>,

    /// How `cpu` was obtained.
    pub cpu_basis: super::CpuBasis,

    /// Peak resident set size of the solver process.
    pub peak_rss_bytes: Option<u64>,

    /// How `peak_rss_bytes` was obtained. **Read before comparing two figures.**
    pub rss_basis: super::RssBasis,

    /// Stage timings the library itself reported, with its own names.
    pub stages: Vec<(String, Duration)>,

    /// The command that reproduces this row.
    pub reproduce: String,
}

impl CompetitiveRecord {
    /// The current schema version.
    pub const SCHEMA: u32 = 1;

    /// A row from a [`RunReport`], the instance it was run on, and the environment it ran in.
    ///
    /// The instance is needed because a report carries only the problem's name and digest — the
    /// field, order and variable count are properties of the problem and belong in the row so that
    /// a reader does not have to resolve the digest to see what was solved.
    pub fn of(report: &RunReport, instance: &Instance, environment: &Environment) -> Self {
        let (outcome, invariants, verification) = match &report.status {
            RunStatus::Complete(answer) => (Outcome::Complete, answer.invariants.clone(), None),
            RunStatus::Verified(answer, verification) => (
                // A verification that compared nothing is not one, and the row must not claim it
                // was. Same rule as `RunStatus::is_verified`.
                if verification.is_substantive() {
                    Outcome::Verified
                } else {
                    Outcome::Complete
                },
                answer.invariants.clone(),
                Some(verification.clone()),
            ),
            RunStatus::StoppedByLimit(stop) => (
                Outcome::StoppedByLimit(stop.clone()),
                Invariants::none(),
                None,
            ),
            RunStatus::Unsupported(reason) => (
                Outcome::Unsupported(reason.clone()),
                Invariants::none(),
                None,
            ),
            RunStatus::Failed(failure) => {
                (Outcome::Failed(failure.clone()), Invariants::none(), None)
            }
        };

        Self {
            schema: Self::SCHEMA,
            problem: report.instance.clone(),
            problem_digest: report.instance_digest.clone(),
            family: instance.family.clone(),
            task: report.task,
            field: instance.field.clone(),
            order: instance.order,
            variable_count: instance.variable_count(),
            library: report.solver.clone(),
            library_version: report.version.as_ref().map(ToString::to_string),
            environment: environment.clone(),
            limits: report.limits.clone(),
            // Only an answered run carries a time. See the field's documentation.
            wall: outcome
                .is_timing_evidence()
                .then_some(report.measurement.wall),
            outcome,
            invariants,
            verification,
            cpu: report.measurement.cpu,
            cpu_basis: report.measurement.cpu_basis,
            peak_rss_bytes: report.measurement.peak_rss_bytes,
            rss_basis: report.measurement.rss_basis,
            stages: report.measurement.stages.clone(),
            reproduce: report.command_line.clone().unwrap_or_default(),
        }
    }

    /// True if this row's wall time may be used as a measurement.
    pub fn is_timing_evidence(&self) -> bool {
        self.outcome.is_timing_evidence() && self.wall.is_some()
    }

    /// True if `other` measured the same thing under the same conditions.
    ///
    /// Problem, task, limits, machine, build, **commit and policy**. The precondition of a ratio,
    /// minus the invariant agreement, which is checked separately because it is a property of the
    /// *answers*.
    ///
    /// `Environment::comparable` covers machine, cpu and build and **not** `commit` or `policy`,
    /// and both omissions let the board compare two different things.
    ///
    /// **Commit.** `build` is `release, rustc <version>`, which is identical across every source
    /// change, so without this a re-measure taken after an engine change pairs against the rows the
    /// change superseded — a ratio between two versions of this crate, rendered as a ratio against
    /// a competitor. Caught when a rebase picked up an F4 change and the stale rows were still on
    /// the board.
    ///
    /// **Policy** is where the measurement discipline lives — `many rows per process (no memory
    /// figure)` against `one row per process`. Two different measurements of the same row: one is cold in a fresh
    /// process, the other inherits the allocator and cache state of every row that ran before it in
    /// the same one. Left to `Environment::comparable` alone the board paired them, which doubled
    /// its own pair count and ratioed a cold row against a warm one. Checked here rather than in
    /// `Environment` because that type is shared with other experiment records, whose own
    /// comparability rules are theirs to change — written out in
    /// `docs/research/mq-comparison-methodology.md` §2, which also records that the startup floor
    /// below is this board's.
    pub fn comparable_with(&self, other: &CompetitiveRecord) -> bool {
        self.problem_digest == other.problem_digest
            && self.task == other.task
            && self.limits.comparable_with(&other.limits)
            && self.environment.comparable(&other.environment)
            && self.environment.commit == other.environment.commit
            && self.environment.policy == other.environment.policy
    }

    /// The row as JSON.
    ///
    /// Absent optional figures are **omitted**, never `null`: "not measured" is not zero, and a key
    /// holding `null` invites being coerced to one. Same rule as the cryptanalysis records.
    pub fn to_json(&self) -> Json {
        let mut fields = vec![
            ("schema", Json::int(self.schema)),
            ("problem", Json::string(&self.problem)),
            ("problem_digest", Json::string(&self.problem_digest)),
            ("family", Json::string(&self.family)),
            ("task", Json::string(self.task.tag())),
            (
                "field",
                Json::object([
                    ("name", Json::string(&self.field.name)),
                    ("characteristic", Json::int(self.field.characteristic)),
                    ("extension_degree", Json::int(self.field.extension_degree)),
                    (
                        "defining_polynomial",
                        match &self.field.defining_polynomial {
                            Some(polynomial) => Json::string(polynomial),
                            None => Json::Null,
                        },
                    ),
                ]),
            ),
            ("order", Json::string(order_tag(self.order))),
            ("variable_count", Json::size(self.variable_count)),
            ("library", Json::string(&self.library)),
        ];
        if let Some(version) = &self.library_version {
            fields.push(("library_version", Json::string(version)));
        }
        fields.push(("environment", self.environment.to_json()));
        fields.push((
            "limits",
            Json::object([
                ("wall_nanos", Json::nanos(self.limits.wall)),
                ("workers", Json::size(self.limits.workers)),
                (
                    "max_rss_bytes",
                    match self.limits.max_rss_bytes {
                        Some(bytes) => Json::int(bytes),
                        None => Json::Null,
                    },
                ),
                (
                    "tool_caps",
                    Json::Array(self.limits.tool_caps.iter().map(Json::string).collect()),
                ),
            ]),
        ));
        fields.push(("outcome", Json::string(self.outcome.tag())));
        if let Some(detail) = self.outcome.detail() {
            // The cell that stands where a number would be. Emitted under a name that cannot be
            // mistaken for one, and **bare** — see `Outcome::detail`, because storing the
            // prefixed rendering double-prefixes it on the next read.
            fields.push(("outcome_detail", Json::string(detail)));
        }
        fields.push(("invariants", invariants_to_json(&self.invariants)));
        if let Some(verification) = &self.verification {
            fields.push((
                "verification",
                Json::object([
                    (
                        "checked_against",
                        Json::string(&verification.checked_against),
                    ),
                    (
                        "shared_invariants",
                        Json::size(verification.shared_invariants),
                    ),
                    (
                        "note",
                        match &verification.note {
                            Some(note) => Json::string(note),
                            None => Json::Null,
                        },
                    ),
                ]),
            ));
        }
        if let Some(wall) = self.wall {
            fields.push(("wall_nanos", Json::nanos(wall)));
        }
        if let Some(cpu) = self.cpu {
            fields.push(("cpu_nanos", Json::nanos(cpu)));
        }
        fields.push(("cpu_basis", Json::string(cpu_basis_tag(self.cpu_basis))));
        if let Some(bytes) = self.peak_rss_bytes {
            fields.push(("peak_rss_bytes", Json::int(bytes)));
            // The basis travels with the figure or not at all: a byte count whose provenance is
            // unstated is the thing this board is most able to get wrong.
            fields.push(("peak_rss_basis", Json::string(self.rss_basis.to_string())));
        }
        if !self.stages.is_empty() {
            fields.push((
                "stages",
                Json::Array(
                    self.stages
                        .iter()
                        .map(|(name, elapsed)| {
                            Json::object([
                                ("name", Json::string(name)),
                                ("elapsed_nanos", Json::nanos(*elapsed)),
                            ])
                        })
                        .collect(),
                ),
            ));
        }
        fields.push(("reproduce", Json::string(&self.reproduce)));
        Json::object(fields)
    }

    /// A row read back from JSON.
    ///
    /// Reads the fields a table and a ratio need. The answer itself is not stored, so what comes
    /// back is what the board renders — not a `RunReport`.
    ///
    /// # Errors
    /// [`BoardError::MalformedRow`], naming the field.
    pub fn from_json(value: &Json) -> Result<Self, BoardError> {
        let string = |key: &'static str| -> Result<String, BoardError> {
            Ok(value
                .get(key)
                .and_then(Json::as_str)
                .ok_or(BoardError::MalformedRow { field: key })?
                .to_string())
        };
        let nanos = |parent: &Json, key: &'static str| -> Option<Duration> {
            parent
                .get(key)
                .and_then(Json::as_int)
                .map(|n| Duration::from_nanos(n as u64))
        };

        // Identity first, so that a row missing its problem says so rather than reporting
        // whichever field the reader happened to reach first.
        let problem = string("problem")?;
        let problem_digest = string("problem_digest")?;
        let family = string("family")?;

        let task_tag = string("task")?;
        let task =
            super::Task::from_tag(&task_tag).ok_or(BoardError::MalformedRow { field: "task" })?;
        let order_text = string("order")?;
        let order =
            order_from_tag(&order_text).ok_or(BoardError::MalformedRow { field: "order" })?;

        let field_object = value
            .get("field")
            .ok_or(BoardError::MalformedRow { field: "field" })?;
        let field = FieldSpec {
            characteristic: field_object
                .get("characteristic")
                .and_then(Json::as_int)
                .ok_or(BoardError::MalformedRow {
                    field: "field.characteristic",
                })? as u64,
            extension_degree: field_object
                .get("extension_degree")
                .and_then(Json::as_int)
                .unwrap_or(1) as u32,
            name: field_object
                .get("name")
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string(),
            defining_polynomial: field_object
                .get("defining_polynomial")
                .and_then(Json::as_str)
                .map(str::to_string),
        };

        let limits_object = value
            .get("limits")
            .ok_or(BoardError::MalformedRow { field: "limits" })?;
        let limits = Limits {
            wall: nanos(limits_object, "wall_nanos").unwrap_or_default(),
            workers: limits_object
                .get("workers")
                .and_then(Json::as_int)
                .unwrap_or(1) as usize,
            max_rss_bytes: limits_object
                .get("max_rss_bytes")
                .and_then(Json::as_int)
                .map(|b| b as u64),
            tool_caps: limits_object
                .get("tool_caps")
                .map(|caps| {
                    caps.items()
                        .iter()
                        .filter_map(Json::as_str)
                        .map(str::to_string)
                        .collect()
                })
                .unwrap_or_default(),
        };

        // Stripped on the way in, which is what makes `load` -> `to_json` a **fixed point**.
        //
        // An older writer stored `instead_of_a_time`'s rendered form rather than the bare datum,
        // so reading it into a variant's detail field and writing it back added a prefix — and
        // because this board is *regenerated* rather than hand-edited, each regeneration added
        // another. Six stored rows reached `unsupported: unsupported: ...` that way. A lossy
        // round trip in a regenerable artifact does not stay the same size; it grows.
        //
        // Stripping here heals those rows on the next regeneration and makes the property
        // testable: `test_loading_and_rewriting_is_a_fixed_point`.
        let detail = strip_outcome_tags(
            value
                .get("outcome_detail")
                .and_then(Json::as_str)
                .unwrap_or_default(),
        );
        // The reason text is not re-parsed into its variant: it was rendered for a human, and a
        // round trip through prose would invent a structure the file does not have. `Representation`
        // and `ToolCap` carry it verbatim, which is honest about what was stored.
        let outcome = match string("outcome")?.as_str() {
            "complete" => Outcome::Complete,
            "verified" => Outcome::Verified,
            "stopped-by-limit" => Outcome::StoppedByLimit(LimitStop::ToolCap { detail }),
            "unsupported" => Outcome::Unsupported(Unsupported::Representation { detail }),
            "failed" => Outcome::Failed(RunFailure::Reported { message: detail }),
            _ => return Err(BoardError::MalformedRow { field: "outcome" }),
        };

        let environment_object = value.get("environment").ok_or(BoardError::MalformedRow {
            field: "environment",
        })?;

        Ok(Self {
            schema: value.get("schema").and_then(Json::as_int).unwrap_or(1) as u32,
            problem,
            problem_digest,
            family,
            task,
            field,
            order,
            variable_count: value
                .get("variable_count")
                .and_then(Json::as_int)
                .unwrap_or(0) as usize,
            library: string("library")?,
            library_version: value
                .get("library_version")
                .and_then(Json::as_str)
                .map(str::to_string),
            environment: environment_from_json(environment_object),
            limits,
            invariants: invariants_from_json(value.get("invariants")),
            verification: value.get("verification").map(|object| Verification {
                checked_against: object
                    .get("checked_against")
                    .and_then(Json::as_str)
                    .unwrap_or_default()
                    .to_string(),
                agreed: Invariants::none(),
                shared_invariants: object
                    .get("shared_invariants")
                    .and_then(Json::as_int)
                    .unwrap_or(0) as usize,
                note: object
                    .get("note")
                    .and_then(Json::as_str)
                    .map(str::to_string),
            }),
            // Absent for every row that is not timing evidence, which is the invariant the writer
            // maintains. Read back as absent rather than as zero.
            wall: nanos(value, "wall_nanos"),
            cpu: nanos(value, "cpu_nanos"),
            cpu_basis: match value.get("cpu_basis").and_then(Json::as_str) {
                Some("proc-stat-ticks") => super::CpuBasis::ProcStatTicks { user_hz: 100 },
                _ => super::CpuBasis::Unavailable,
            },
            peak_rss_bytes: value
                .get("peak_rss_bytes")
                .and_then(Json::as_int)
                .map(|b| b as u64),
            // Not round-tripped into its variant for the same reason as `outcome`: the stored form
            // is prose. A consumer comparing two figures reads `peak_rss_basis` from the file.
            rss_basis: super::RssBasis::Unavailable,
            stages: value
                .get("stages")
                .map(|stages| {
                    stages
                        .items()
                        .iter()
                        .filter_map(|stage| {
                            Some((
                                stage.get("name").and_then(Json::as_str)?.to_string(),
                                nanos(stage, "elapsed_nanos")?,
                            ))
                        })
                        .collect()
                })
                .unwrap_or_default(),
            reproduce: value
                .get("reproduce")
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string(),
            outcome,
        })
    }
}

/// Remove any leading `unsupported:` / `failed:` tags, however many an older writer accumulated.
///
/// The stored datum is the bare reason; the tags belong to the rendering. See
/// [`CompetitiveRecord::from_json`] on why they accumulated at all.
fn strip_outcome_tags(detail: &str) -> String {
    // Two families, and both have to go.
    //
    // The outcome **tags** are what `instead_of_a_time` prepends. The **wrappers** are the
    // `Display` prefixes of the three variants `from_json` reconstructs into — `Reported` renders
    // "the tool reported an error: {message}" and `ToolCap` renders "stopped at the tool's own
    // cap: {detail}" — so reading a rendered string into one of them and writing it back wraps it
    // again. Stripping both is what cancels the wrapping and makes `load` -> `to_json` a fixed
    // point; `Unsupported::Representation` needs no wrapper stripped because its `Display` is
    // already the identity on its payload, which is why it was chosen for the round trip.
    const PREFIXES: [&str; 5] = [
        "unsupported:",
        "failed:",
        "stopped-by-limit:",
        "the tool reported an error:",
        "stopped at the tool's own cap:",
    ];
    let mut text = detail.trim();
    loop {
        let stripped = PREFIXES
            .iter()
            .find_map(|prefix| text.strip_prefix(prefix))
            .map(str::trim_start);
        match stripped {
            Some(rest) => text = rest,
            None => return text.to_string(),
        }
    }
}

/// The stable tag for a CPU-time basis.
fn cpu_basis_tag(basis: super::CpuBasis) -> &'static str {
    match basis {
        super::CpuBasis::ProcStatTicks { .. } => "proc-stat-ticks",
        super::CpuBasis::Unavailable => "unavailable",
    }
}

/// Invariants as JSON, omitting what was not reported.
fn invariants_to_json(invariants: &Invariants) -> Json {
    let mut fields: Vec<(&str, Json)> = Vec::new();
    if let Some(dimension) = invariants.quotient_dimension {
        fields.push(("quotient_dimension", Json::size(dimension)));
    }
    if let Some(monomials) = &invariants.leading_monomials {
        fields.push((
            "leading_monomials",
            Json::Array(monomials.iter().map(Json::string).collect()),
        ));
    }
    if let Some(cardinality) = invariants.basis_cardinality {
        fields.push(("basis_cardinality", Json::size(cardinality)));
    }
    if let Some(count) = invariants.solution_count {
        fields.push(("solution_count", Json::size(count)));
    }
    if let Some(degree) = invariants.eliminant_degree {
        fields.push(("eliminant_degree", Json::size(degree)));
    }
    Json::object(fields)
}

/// Invariants read back, with every absent key staying absent.
fn invariants_from_json(value: Option<&Json>) -> Invariants {
    let value = match value {
        Some(value) => value,
        None => return Invariants::none(),
    };
    Invariants {
        quotient_dimension: value
            .get("quotient_dimension")
            .and_then(Json::as_int)
            .map(|d| d as usize),
        leading_monomials: value.get("leading_monomials").map(|monomials| {
            monomials
                .items()
                .iter()
                .filter_map(Json::as_str)
                .map(str::to_string)
                .collect()
        }),
        basis_cardinality: value
            .get("basis_cardinality")
            .and_then(Json::as_int)
            .map(|c| c as usize),
        solution_count: value
            .get("solution_count")
            .and_then(Json::as_int)
            .map(|c| c as usize),
        eliminant_degree: value
            .get("eliminant_degree")
            .and_then(Json::as_int)
            .map(|d| d as usize),
    }
}

/// An [`Environment`] read back from the form [`Environment::to_json`] writes.
///
/// Tolerant by design: a missing field
/// becomes empty rather than failing the row, because an environment that was recorded
/// incompletely is still better evidence than no row at all.
fn environment_from_json(value: &Json) -> Environment {
    let text = |key: &str| {
        value
            .get(key)
            .and_then(Json::as_str)
            .unwrap_or_default()
            .to_string()
    };
    Environment {
        commit: text("commit"),
        // Absent in every row written before #505. Empty reads as *unrecorded*, which
        // `stamp_is_resolvable` reports as unresolvable — which is the fact about those rows.
        base_commit: text("base_commit"),
        patch_id: text("patch_id"),
        machine: text("machine"),
        cpu: text("cpu"),
        concurrency: value
            .get("concurrency")
            .and_then(Json::as_int)
            .unwrap_or(1)
            .max(1) as usize,
        build: text("build"),
        policy: text("policy"),
    }
}

/// A valid speedup between two rows, with everything that made it valid.
#[derive(Clone, Debug, PartialEq)]
pub struct Speedup {
    /// The problem both rows solved.
    pub problem: String,

    /// The task both rows performed.
    pub task: super::Task,

    /// The library in the numerator's denominator — the one being compared against.
    pub baseline: String,

    /// The faster-or-slower library.
    pub subject: String,

    /// `baseline wall / subject wall`. Above one means the subject is faster.
    pub ratio: f64,

    /// How many invariants the two answers were checked to agree on.
    ///
    /// **Zero means the ratio is between two unchecked answers**, which §5 of the protocol forbids
    /// publishing. Carried rather than filtered so that a renderer can say so.
    pub shared_invariants: usize,

    /// The **smaller** of the two operands' wall times measured against its own library's floor.
    ///
    /// **Below about 2.0 the ratio is not an engine comparison in either direction** — it is
    /// dominated by the cost of *starting* the comparand. Measured on this board: Singular's floor
    /// is 36.0 ms, and four apparent Zeebra wins of 2.2x, 3.4x, 8.4x and **450x** are entirely
    /// that floor. The 450x is the one that would have been published.
    ///
    /// **Both operands, not just the baseline.** Measuring only the baseline against its own floor
    /// checked the wrong thing: Zeebra runs in-process and has no startup, so its floor is
    /// microseconds and every ratio passed. The concern is a *comparand* sitting at its own
    /// startup, so the minimum over the two is what decides.
    ///
    /// `None` when neither library has enough rows to observe a floor. Carried rather than
    /// filtered, for the same reason as `shared_invariants`: a dropped row is a gap a reader
    /// cannot see, and the board is the artifact that has to stop somebody recomputing the 501x
    /// from the raw numbers later.
    pub floor_multiple: Option<f64>,

    /// The corpus's own record of how this problem's ideal equivalence was established.
    ///
    /// [`Equivalence::licenses_timing`] is the gate on publishing a figure at all and
    /// [`Equivalence::is_corroborated`] is the fact a published one has to state. Both were
    /// policy that nothing read: the renderer built every table from the stored records, so a
    /// rung changing variant changed nothing about what the board published (#518).
    ///
    /// `None` where the problem is **not a corpus rung**, which is not the same as having weak
    /// evidence: it is having none recorded. [`Self::licenses_timing`] therefore refuses it, and
    /// the renderer says so in the cell rather than dropping the row.
    pub equivalence: Option<Equivalence>,
}

impl Speedup {
    /// The multiple below which a ratio is startup-dominated rather than an engine comparison.
    ///
    /// Two: at that point half the comparand's wall is the cost of starting it, so the other half
    /// cannot carry a conclusion through the 20% noise band this project reads results against.
    pub const FLOOR_MULTIPLE_REQUIRED: f64 = 2.0;

    /// The band around one inside which a ratio is not read as a win or a loss.
    ///
    /// 1.2, the 20% this project reads results against — the same band the constant above is
    /// justified by. A publishable ratio inside it is a *result*, not a missing one: it says the
    /// two engines are level on that row, and counting it with the wins would overstate both.
    pub const NOISE_BAND: f64 = 1.2;

    /// Comparands whose rows are worth recording but may never be a speedup denominator.
    ///
    /// Sagebrush agreed term-for-term with every other engine on every family tried, including at
    /// a 62-bit prime — and is still five weeks old, every crate `0.1.0`, nothing on crates.io,
    /// six F4 tests, and no oracle run in its own repository exercising the elimination. A ratio
    /// against it measures something real about one unreviewed implementation and nothing about
    /// the state of the art, so it is reportable **with its SHA** and is not a conclusion.
    ///
    /// Enforced here rather than left to the prose that first recorded the judgement: now that
    /// these rows are on the board, a reader of the board alone would see a Sagebrush ratio
    /// rendered exactly like a Singular one.
    pub const NOT_AUTHORITATIVE: [&str; 1] = ["sagebrush"];

    /// Whether a conclusion may rest on this ratio's comparand.
    pub fn has_authoritative_comparand(&self) -> bool {
        !Self::NOT_AUTHORITATIVE.contains(&self.subject.as_str())
    }

    /// Whether this ratio says anything about the **engines** rather than about process startup.
    ///
    /// `false` when **either** operand's wall is within [`Self::FLOOR_MULTIPLE_REQUIRED`] of its
    /// own library's observed startup floor. An unknown floor is treated as acceptable: refusing
    /// on absent evidence would silently drop every row of a library with few measurements.
    pub fn is_engine_comparison(&self) -> bool {
        self.floor_multiple
            .is_none_or(|multiple| multiple >= Self::FLOOR_MULTIPLE_REQUIRED)
    }

    /// Whether the corpus's evidence permits a cross-library figure for this problem at all.
    ///
    /// Fail-closed on an **unrecorded** problem, which is the opposite of
    /// [`Self::is_engine_comparison`]'s reading of an unknown startup floor — and deliberately:
    /// refusing there would silently drop rows, while refusing here is visible in the cell. A
    /// problem that is not a corpus rung has no recorded equivalence, and the corpus's rule for
    /// that case is that no cross-library figure may be quoted for it.
    pub fn licenses_timing(&self) -> bool {
        self.equivalence
            .is_some_and(|equivalence| equivalence.licenses_timing())
    }

    /// Whether a **third** opinion exists, so a disagreement could name the odd one out.
    ///
    /// False for an unrecorded problem and for the two single-engine variants. A publishable
    /// ratio that is not corroborated is published **with the fact stated**, which is what the
    /// renderer's cell carries.
    pub fn is_corroborated(&self) -> bool {
        self.equivalence
            .is_some_and(|equivalence| equivalence.is_corroborated())
    }

    /// Whether this ratio may be published: recorded provenance, an engine comparison, and a
    /// checked invariant.
    ///
    /// The conjunction of the protocol's gates, so a renderer cannot satisfy one and forget the
    /// others.
    pub fn is_publishable(&self) -> bool {
        self.licenses_timing() && self.is_engine_comparison() && self.shared_invariants > 0
    }
}

/// Rows from every library, with the renderers.
#[derive(Clone, Debug, Default)]
pub struct CompetitiveBoard {
    rows: Vec<CompetitiveRecord>,
    corpus: Vec<CorpusEntry>,
}

impl CompetitiveBoard {
    /// An empty board.
    pub fn new() -> Self {
        Self::default()
    }

    /// Extend the problems this board knows the provenance of beyond the public [`ladder`].
    ///
    /// A ratio is licensed only for a problem whose cross-engine equivalence is recorded, so rows
    /// for a caller's own systems are refused until their [`CorpusEntry`] values are supplied
    /// here. An entry whose name is also a ladder rung takes precedence over the rung.
    pub fn with_corpus(mut self, entries: impl IntoIterator<Item = CorpusEntry>) -> Self {
        self.corpus.extend(entries);
        self
    }

    /// Each known problem's recorded equivalence: the ladder, then the caller's corpus.
    fn provenance(&self) -> BTreeMap<&'static str, Equivalence> {
        ladder()
            .into_iter()
            .chain(self.corpus.iter().cloned())
            .map(|entry| (entry.name, entry.equivalence))
            .collect()
    }

    /// Add a row. Every outcome is accepted, including the ones with no answer.
    ///
    /// Infallible on purpose: there is no registry to validate against here — the problem's digest
    /// *is* its identity, and a row for a problem no other library attempted is still a row worth
    /// keeping.
    pub fn add(&mut self, row: CompetitiveRecord) {
        self.rows.push(row);
    }

    /// The rows, in insertion order.
    pub fn rows(&self) -> &[CompetitiveRecord] {
        &self.rows
    }

    /// Load an accumulated history: `{"rows": [...]}` as [`Self::to_json`] writes it.
    ///
    /// # Errors
    /// [`BoardError`] from any malformed row.
    pub fn load(history: &Json) -> Result<Self, BoardError> {
        let entries = history
            .get("rows")
            .ok_or(BoardError::MalformedRow { field: "rows" })?;
        let mut board = Self::new();
        for entry in entries.items() {
            board.rows.push(CompetitiveRecord::from_json(entry)?);
        }
        Ok(board)
    }

    /// The board as JSON, with the history contract written into it.
    pub fn to_json(&self) -> Json {
        Json::object([
            ("schema", Json::int(CompetitiveRecord::SCHEMA)),
            ("contract", Json::string(COMPETITIVE_HISTORY_CONTRACT)),
            ("row_count", Json::size(self.rows.len())),
            (
                "rows",
                Json::Array(self.rows.iter().map(CompetitiveRecord::to_json).collect()),
            ),
        ])
    }

    /// Every **valid** speedup of another library over `baseline`, on equivalent tasks.
    ///
    /// A pair contributes a ratio only when [`CompetitiveRecord::comparable_with`] holds — same
    /// problem digest, same task, same limits, same machine and build — and **both** rows are
    /// timing evidence. Everything else contributes nothing: an unsupported input, a limit stop or
    /// a failure has no time, and the board shows
    /// [`Outcome::instead_of_a_time`] in that cell rather than a number.
    ///
    /// The invariant agreement is reported through [`Speedup::shared_invariants`] rather than
    /// filtered on, so that a renderer can present a ratio between two unchecked answers *as*
    /// unchecked instead of silently dropping it — a dropped row is a gap a reader cannot see.
    pub fn speedups(&self, baseline: &str) -> Vec<Speedup> {
        let mut found = Vec::new();
        let baseline_floor = self.startup_floor(baseline);
        // Built once rather than per pair: the ladder is a constructor, not a table lookup.
        let provenance = self.provenance();
        for reference in self.rows.iter().filter(|row| row.library == baseline) {
            if !reference.is_timing_evidence() {
                continue;
            }
            for subject in self.rows.iter() {
                if subject.library == baseline || !subject.is_timing_evidence() {
                    continue;
                }
                if !subject.comparable_with(reference) {
                    continue;
                }
                let (Some(theirs), Some(ours)) = (reference.wall, subject.wall) else {
                    continue;
                };
                if ours.is_zero() {
                    continue;
                }
                found.push(Speedup {
                    problem: subject.problem.clone(),
                    task: subject.task,
                    baseline: baseline.to_string(),
                    subject: subject.library.clone(),
                    ratio: theirs.as_secs_f64() / ours.as_secs_f64(),
                    shared_invariants: reference.invariants.overlap(&subject.invariants),
                    // The minimum over both operands: a ratio is startup-dominated if *either*
                    // side is sitting at its own floor, and in practice it is the subprocess
                    // comparand rather than the in-process baseline.
                    floor_multiple: [
                        (theirs, baseline_floor),
                        (ours, self.startup_floor(&subject.library)),
                    ]
                    .into_iter()
                    .filter_map(|(wall, floor)| {
                        floor
                            .filter(|floor| !floor.is_zero())
                            .map(|floor| wall.as_secs_f64() / floor.as_secs_f64())
                    })
                    .min_by(|a, b| a.total_cmp(b)),
                    equivalence: provenance.get(subject.problem.as_str()).copied(),
                });
            }
        }
        found
    }

    /// Every **engine-internal** ratio against `baseline`, on equivalent tasks (#428).
    ///
    /// The same pairing rule as [`Self::speedups`] — same problem digest, task, limits, machine and
    /// build, both rows answered — over each row's own self-reported stage times rather than its
    /// wall. A pair contributes nothing when either side reports no stage this statistic can use,
    /// which is a library-level fact and visible in the measurement table's `stages` column.
    ///
    /// Not a replacement for [`Self::speedups`] and not a correction to it. The wall-clock ratio is
    /// the cost of asking, which is what a user pays; this is the engines compared with process
    /// setup, parsing and output excluded from both, which is what an implementation study needs.
    /// The board prints them in separate sections for that reason.
    pub fn engine_ratios(&self, baseline: &str) -> Vec<EngineRatio> {
        let mut found = Vec::new();
        let provenance = self.provenance();
        for reference in self.rows.iter().filter(|row| row.library == baseline) {
            if !reference.is_timing_evidence() {
                continue;
            }
            let Some(theirs) =
                engine_internal_time(&reference.library, reference.task, &reference.stages)
            else {
                continue;
            };
            for subject in self.rows.iter() {
                if subject.library == baseline || !subject.is_timing_evidence() {
                    continue;
                }
                if !subject.comparable_with(reference) {
                    continue;
                }
                let Some(ours) =
                    engine_internal_time(&subject.library, subject.task, &subject.stages)
                else {
                    continue;
                };
                if ours.is_zero() {
                    // A zero-length engine time is the resolution speaking, not a measurement, and
                    // it has no reciprocal. Refused here rather than carried as an infinity: the
                    // refusal is already visible as the library's own `0.0 ms` stage in the
                    // measurement table.
                    continue;
                }
                found.push(EngineRatio {
                    problem: subject.problem.clone(),
                    task: subject.task,
                    baseline: baseline.to_string(),
                    subject: subject.library.clone(),
                    ratio: theirs.as_secs_f64() / ours.as_secs_f64(),
                    baseline_internal: theirs,
                    subject_internal: ours,
                    // The minimum over both operands, as with the startup floor: a ratio is
                    // resolution-dominated if *either* side is near its own granularity.
                    resolution_multiple: [
                        (theirs, stage_resolution(&reference.library)),
                        (ours, stage_resolution(&subject.library)),
                    ]
                    .into_iter()
                    .map(|(elapsed, resolution)| {
                        resolution
                            .filter(|resolution| !resolution.is_zero())
                            .map(|resolution| elapsed.as_secs_f64() / resolution.as_secs_f64())
                    })
                    .min_by(|a, b| match (a, b) {
                        // An undeclared resolution is the worst case, not a missing one.
                        (None, _) | (_, None) => std::cmp::Ordering::Less,
                        (Some(a), Some(b)) => a.total_cmp(b),
                    })
                    .flatten(),
                    shared_invariants: reference.invariants.overlap(&subject.invariants),
                    equivalence: provenance.get(subject.problem.as_str()).copied(),
                });
            }
        }
        found
    }

    /// The shortest wall time `library` recorded, which is its **process-startup floor**.
    ///
    /// Derived from the board rather than configured, which is the point: the floor is a property
    /// of a library on a machine, and the board already holds enough rows to observe it. Singular's
    /// came out at 36.0 ms across instances whose quotient dimensions differ by a factor of 2 000
    /// — five rows within 0.07 ms of each other — and a figure that constant across that range is
    /// not a computation.
    ///
    /// Requires at least [`Self::ROWS_FOR_A_FLOOR`] answered rows, because one fast row is a fast
    /// row and not a floor. `None` below that, which [`Speedup::is_engine_comparison`] then treats
    /// as acceptable rather than as a refusal.
    ///
    /// An under-estimate is the safe direction: it makes fewer ratios look startup-dominated, so a
    /// row it passes is one a reader must still check. It is an over-estimate only if the library's
    /// genuinely fastest instance is faster than its own startup, which cannot happen.
    pub fn startup_floor(&self, library: &str) -> Option<Duration> {
        let walls: Vec<Duration> = self
            .rows
            .iter()
            .filter(|row| row.library == library && row.is_timing_evidence())
            .filter_map(|row| row.wall)
            .collect();
        if walls.len() < Self::ROWS_FOR_A_FLOOR {
            return None;
        }
        walls.into_iter().min()
    }

    /// Answered rows a library needs before its fastest one counts as a startup floor.
    pub const ROWS_FOR_A_FLOOR: usize = 4;

    /// The board as Markdown, grouped by family then problem.
    ///
    /// Generated rather than hand-maintained, so the human-readable table cannot drift from the
    /// data — the same reason the cryptanalysis `SCOREBOARD.md` is generated.
    pub fn to_markdown(&self) -> String {
        let mut out = String::new();
        out.push_str("# Competitive board: Zeebra against external Gröbner engines\n\n");
        out.push_str(
            "Generated by the competitive harness. Do not edit: regenerate it.\n\n\
             Every row is one library's attempt at one task on one problem, **including the \
             attempts that produced no answer**. A row whose outcome is `unsupported`, \
             `stopped-by-limit` or `failed` carries no time, and the cell where a time would be \
             names the missing capability or the limit instead. The protocol is \
             `docs/research/external-comparison-protocol.md`.\n\n",
        );

        if self.rows.is_empty() {
            out.push_str(
                "_No rows yet. The schema and the renderer are in place; the rows arrive with \
                 the per-library adapters._\n",
            );
            return out;
        }

        // The roster, before the tables. A board that holds two libraries and a board taken on a
        // machine where only two were reachable render identically in the per-family tables, and
        // the difference is the whole value of the comparison — so it is stated rather than left
        // to be counted by hand. `RunFailure::Unavailable` is the row an unreachable engine
        // leaves, which is why a library can appear here with no answers at all.
        let mut roster: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
        for row in &self.rows {
            let entry = roster.entry(row.library.as_str()).or_insert((0, 0));
            entry.0 += 1;
            if row.outcome.is_timing_evidence() {
                entry.1 += 1;
            }
        }
        out.push_str("## Roster\n\n");
        let _ = writeln!(out, "| library | rows | answered |");
        let _ = writeln!(out, "|---|---:|---:|");
        for (library, (rows, answered)) in &roster {
            let _ = writeln!(out, "| {} | {} | {} |", library, rows, answered);
        }
        out.push('\n');

        let mut families: BTreeMap<&str, BTreeMap<&str, Vec<&CompetitiveRecord>>> = BTreeMap::new();
        for row in &self.rows {
            families
                .entry(row.family.as_str())
                .or_default()
                .entry(row.problem.as_str())
                .or_default()
                .push(row);
        }

        for (family, problems) in &families {
            let _ = writeln!(out, "## {}\n", family);
            let _ = writeln!(
                out,
                "| problem | task | field | library | commit | outcome | wall | cpu | peak RSS | stages | verification |"
            );
            let _ = writeln!(out, "|---|---|---|---|---|---|---:|---:|---:|---|---|");
            for rows in problems.values() {
                for row in rows {
                    let _ = writeln!(
                        out,
                        "| `{}` `{}` | {} | {} | {} | `{}` | {} | {} | {} | {} | {} | {} |",
                        row.problem,
                        &row.problem_digest[..row.problem_digest.len().min(12)],
                        row.task,
                        row.field,
                        library_cell(row),
                        row.environment.commit,
                        row.outcome.cell(),
                        duration_cell(row.wall),
                        duration_cell(row.cpu),
                        bytes_cell(row.peak_rss_bytes),
                        stages_cell(&row.stages),
                        verification_cell(row),
                    );
                }
            }
            out.push('\n');
        }

        let speedups = self.speedups("zeebra");
        if !speedups.is_empty() {
            out.push_str("## Speedups over Zeebra\n\n");
            out.push_str(
                "Computed only for rows agreeing on problem digest, task, limits, machine and \
                 build, with **both** outcomes answered. A ratio whose two answers share no \
                 checked invariant is marked: the protocol does not permit publishing it.\n\n",
            );
            out.push_str(
                "The **provenance** column is the corpus's own record of how the problem's ideal \
                 equivalence was established, which is the gate on quoting a figure for it at \
                 all. A problem with no recorded equivalence, or one no external engine can \
                 represent, is **refused here rather than omitted**; a ratio resting on a single \
                 external engine is published with that fact stated, because nothing can \
                 triangulate it.\n\n",
            );

            // The counts, before the table. Each gate already marks the rows it excludes, but a
            // marked row is only visible to a reader who tallies the column — and the headline of
            // this board is how *few* of its pairs survive both gates. Stated so the survivors
            // cannot be mistaken for the whole comparison.
            // Provenance is tallied first and the two gates below exclude the rows it already
            // refused, so the counts partition the pairs instead of overlapping.
            let unlicensed = speedups.iter().filter(|s| !s.licenses_timing()).count();
            let disqualified = speedups
                .iter()
                .filter(|s| s.licenses_timing() && !s.is_engine_comparison())
                .count();
            let unchecked = speedups
                .iter()
                .filter(|s| {
                    s.licenses_timing() && s.is_engine_comparison() && s.shared_invariants == 0
                })
                .count();
            let publishable: Vec<&Speedup> =
                speedups.iter().filter(|s| s.is_publishable()).collect();
            // A ratio this close to one cannot carry a conclusion through the 20% band this
            // project reads results against, so it is counted apart from the wins and losses
            // rather than reported as either.
            let in_band = publishable
                .iter()
                .filter(|s| s.ratio > 1.0 / Speedup::NOISE_BAND && s.ratio < Speedup::NOISE_BAND)
                .count();
            let unauthoritative = publishable
                .iter()
                .filter(|s| !s.has_authoritative_comparand())
                .count();
            // Counted among the publishable rather than against them: the corpus's rule is that
            // a sole-comparand ratio is publishable with the fact stated, not that it is barred.
            let uncorroborated = publishable.iter().filter(|s| !s.is_corroborated()).count();
            let _ = writeln!(
                out,
                "**{} pairs**: {} refused for want of a recorded ideal equivalence, {} \
                 disqualified by the startup floor, {} with no checked invariant, {} publishable \
                 — of which {} resting on a sole comparand and therefore uncorroborated, {} \
                 inside the 20% noise band, {} against a comparand that is not authoritative, \
                 and {} that a conclusion may rest on.\n",
                speedups.len(),
                unlicensed,
                disqualified,
                unchecked,
                publishable.len(),
                uncorroborated,
                in_band,
                unauthoritative,
                publishable
                    .iter()
                    .filter(|s| s.has_authoritative_comparand()
                        && !(s.ratio > 1.0 / Speedup::NOISE_BAND && s.ratio < Speedup::NOISE_BAND))
                    .count()
            );

            let _ = writeln!(
                out,
                "| problem | task | library | ratio | provenance | checked |"
            );
            let _ = writeln!(out, "|---|---|---|---:|---|---|");
            for speedup in &speedups {
                let _ = writeln!(
                    out,
                    "| `{}` | {} | {} | {:.2}x | {} | {} |",
                    speedup.problem,
                    speedup.task,
                    speedup.subject,
                    speedup.ratio,
                    provenance_cell(speedup),
                    verdict_cell(speedup),
                );
            }
            out.push('\n');
        }

        let engine_ratios = self.engine_ratios("zeebra");
        if !engine_ratios.is_empty() {
            out.push_str("## Engine-internal speedups over Zeebra\n\n");
            out.push_str(
                "**A different statistic from the table above, and not a correction to it.** Each \
                 operand here is the library's **own reported stage time** for the task, so \
                 process startup, parsing and output are excluded from both sides. It is therefore \
                 **not an end-to-end cost** and may not be quoted as one: what a caller pays is \
                 the wall-clock table.\n\n",
            );
            out.push_str(
                "It exists because the startup-floor guard above correctly disqualifies every \
                 classical row this board holds — Singular's wall on everything up to `katsura-6` \
                 is its own `exec` — while the data for an engine comparison is already recorded. \
                 The floor guard is **not** relaxed; there is no startup in either operand of this \
                 ratio, so the condition that replaces it is one of **resolution**: a stage \
                 printed in whole milliseconds says nothing about a figure of one or two, and a \
                 reported figure must be at least 5x its own library's granularity. Each \
                 published figure carries the quantization uncertainty the coarser operand puts on \
                 it.\n\n",
            );
            out.push_str(
                "Stage selection per library, and what is excluded from each, is \
                 `engine_internal_time`; the granularities are `stage_resolution`. A library that \
                 reports no usable stage contributes no row, which is visible as an em dash in the \
                 measurement table's `stages` column.\n\n",
            );

            let unlicensed = engine_ratios
                .iter()
                .filter(|ratio| !ratio.licenses_timing())
                .count();
            let unresolved = engine_ratios
                .iter()
                .filter(|ratio| ratio.licenses_timing() && !ratio.is_resolved())
                .count();
            let unchecked = engine_ratios
                .iter()
                .filter(|ratio| {
                    ratio.licenses_timing() && ratio.is_resolved() && ratio.shared_invariants == 0
                })
                .count();
            let publishable: Vec<&EngineRatio> = engine_ratios
                .iter()
                .filter(|ratio| ratio.is_publishable())
                .collect();
            let _ = writeln!(
                out,
                "**{} pairs**: {} refused for want of a recorded ideal equivalence, {} refused on \
                 stage resolution, {} with no checked invariant, {} publishable as an \
                 engine-internal comparison.\n",
                engine_ratios.len(),
                unlicensed,
                unresolved,
                unchecked,
                publishable.len(),
            );

            let _ = writeln!(
                out,
                "| problem | task | library | zeebra engine | their engine | ratio | provenance | \
                 checked |"
            );
            let _ = writeln!(out, "|---|---|---|---:|---:|---:|---|---|");
            for ratio in &engine_ratios {
                let _ = writeln!(
                    out,
                    "| `{}` | {} | {} | {} | {} | {} | {} | {} |",
                    ratio.problem,
                    ratio.task,
                    ratio.subject,
                    duration_cell(Some(ratio.baseline_internal)),
                    duration_cell(Some(ratio.subject_internal)),
                    engine_ratio_cell(ratio),
                    engine_provenance_cell(ratio),
                    engine_verdict_cell(ratio),
                );
            }
            out.push('\n');
        }

        out
    }
}

/// The corpus's equivalence tag, and the one external engine where there is only one.
///
/// The tag alone for the corroborated variants: naming the comparand file or the live oracle in
/// every row would bury the one fact a reader has to act on, which is how many engines agreed.
fn provenance_cell(speedup: &Speedup) -> String {
    match speedup.equivalence {
        None => "**none recorded**".to_string(),
        Some(Equivalence::SoleComparand { tool, .. }) => {
            format!("sole-comparand ({})", tool)
        }
        Some(equivalence) => equivalence.tag().to_string(),
    }
}

/// What the row may claim, in the order the gates apply.
///
/// Provenance first, because a figure the corpus does not license is not improved by passing the
/// floor gate or by agreeing on an invariant. Every refusal is **printed in the cell** rather than
/// dropping the row: a dropped row is a gap a reader cannot see, and the board is the artifact
/// that has to stop somebody recomputing the ratio from the raw numbers later.
fn verdict_cell(speedup: &Speedup) -> String {
    match speedup.equivalence {
        None => {
            return format!(
                "**NOT PUBLISHABLE: `{}` is not a corpus rung, so no ideal equivalence is \
                 recorded for it**",
                speedup.problem
            )
        }
        Some(Equivalence::NoComparand { reason }) => {
            return format!(
                "**NOT PUBLISHABLE: no cross-library check is possible — {}**",
                reason
            )
        }
        Some(_) => {}
    }
    if !speedup.is_engine_comparison() {
        return format!(
            "**NOT AN ENGINE COMPARISON: an operand is {:.1}x its startup floor**",
            speedup.floor_multiple.unwrap_or_default()
        );
    }
    if speedup.shared_invariants == 0 {
        return "**NOT PUBLISHABLE: no invariant was checked**".to_string();
    }
    let mut cell = if speedup.has_authoritative_comparand() {
        format!("{} invariants agreed", speedup.shared_invariants)
    } else {
        format!(
            "{} invariants agreed, but **NOT AUTHORITATIVE: {} may not be a speedup denominator**",
            speedup.shared_invariants, speedup.subject
        )
    };
    // Stated, not withheld: the corpus's rule for a sole comparand is that the ratio is
    // publishable *with this fact beside it*, and the board is where it has to appear.
    if let Some(Equivalence::SoleComparand { tool, reason }) = speedup.equivalence {
        let _ = write!(
            cell,
            "; **NOT CORROBORATED: {} is the only external engine here — {}**",
            tool, reason
        );
    }
    cell
}

/// The library cell: id, and its version where one was probed.
fn library_cell(row: &CompetitiveRecord) -> String {
    match &row.library_version {
        Some(version) => format!("{} ({})", row.library, version),
        // Visible rather than blank: a figure without a version is not reproducible, and the table
        // should say so where it happens.
        None => format!("{} (version not probed)", row.library),
    }
}

/// A duration cell, or an em dash where there is no figure.
fn duration_cell(duration: Option<Duration>) -> String {
    match duration {
        Some(duration) if duration >= Duration::from_secs(1) => {
            format!("{:.2} s", duration.as_secs_f64())
        }
        Some(duration) => format!("{:.1} ms", duration.as_secs_f64() * 1e3),
        None => "—".to_string(),
    }
}

/// A byte cell in the largest unit that keeps it readable, or an em dash.
fn bytes_cell(bytes: Option<u64>) -> String {
    match bytes {
        Some(bytes) if bytes >= 1 << 30 => format!("{:.2} GB", bytes as f64 / (1u64 << 30) as f64),
        Some(bytes) if bytes >= 1 << 20 => format!("{:.1} MB", bytes as f64 / (1u64 << 20) as f64),
        Some(bytes) => format!("{} B", bytes),
        None => "—".to_string(),
    }
}

/// Tool-reported stages, or an em dash.
fn stages_cell(stages: &[(String, Duration)]) -> String {
    if stages.is_empty() {
        return "—".to_string();
    }
    stages
        .iter()
        .map(|(name, elapsed)| format!("{} {}", name, duration_cell(Some(*elapsed))))
        .collect::<Vec<String>>()
        .join("; ")
}

/// What checked this row, and how much it checked.
fn verification_cell(row: &CompetitiveRecord) -> String {
    match &row.verification {
        Some(verification) if verification.is_substantive() => format!(
            "{} ({} invariants)",
            verification.checked_against, verification.shared_invariants
        ),
        // A verification that compared nothing is not one, and the cell must not imply otherwise.
        Some(verification) => format!("{} (nothing compared)", verification.checked_against),
        None => "unchecked".to_string(),
    }
}

/// The ratio with the uncertainty the coarser stage resolution puts on it.
///
/// Printed for every row, refused or not: a reader comparing two engines has to see whether the
/// figure is `2.58x ±5%` or `2.6x ±50%`, and the second is why the resolution gate exists.
fn engine_ratio_cell(ratio: &EngineRatio) -> String {
    match ratio.relative_uncertainty() {
        // `±0%` would be a claim of exactness that quantization never supports. Below half a
        // percent the honest rendering is a bound, and it is the common case: every library but
        // Singular and msolve reports microseconds.
        Some(uncertainty) if uncertainty < 0.005 => format!("{:.2}x ±<1%", ratio.ratio),
        Some(uncertainty) => format!("{:.2}x ±{:.0}%", ratio.ratio, uncertainty * 100.0),
        None => format!("{:.2}x (resolution unknown)", ratio.ratio),
    }
}

/// The corpus's equivalence tag for an engine-internal row.
fn engine_provenance_cell(ratio: &EngineRatio) -> String {
    match ratio.equivalence {
        None => "**none recorded**".to_string(),
        Some(Equivalence::SoleComparand { tool, .. }) => format!("sole-comparand ({})", tool),
        Some(equivalence) => equivalence.tag().to_string(),
    }
}

/// What an engine-internal row may claim, in the order the gates apply.
///
/// Provenance, then resolution, then the invariant — the same order as the wall-clock verdict, with
/// the startup floor replaced by resolution. Every refusal is printed in the cell rather than
/// dropping the row.
fn engine_verdict_cell(ratio: &EngineRatio) -> String {
    match ratio.equivalence {
        None => {
            return format!(
                "**NOT PUBLISHABLE: `{}` is not a corpus rung, so no ideal equivalence is \
                 recorded for it**",
                ratio.problem
            )
        }
        Some(Equivalence::NoComparand { reason }) => {
            return format!(
                "**NOT PUBLISHABLE: no cross-library check is possible — {}**",
                reason
            )
        }
        Some(_) => {}
    }
    if !ratio.is_resolved() {
        return match ratio.resolution_multiple {
            Some(multiple) => format!(
                "**NOT A RESOLVED COMPARISON: an operand is {:.1}x its own stage resolution, so \
                 the figure carries ±{:.0}%**",
                multiple,
                50.0 / multiple.max(f64::MIN_POSITIVE)
            ),
            None => "**NOT A RESOLVED COMPARISON: a library's stage resolution is not declared**"
                .to_string(),
        };
    }
    if ratio.shared_invariants == 0 {
        return "**NOT PUBLISHABLE: no invariant was checked**".to_string();
    }
    let mut cell = if ratio.has_authoritative_comparand() {
        format!("{} invariants agreed", ratio.shared_invariants)
    } else {
        format!(
            "{} invariants agreed, but **NOT AUTHORITATIVE: {} may not be a speedup denominator**",
            ratio.shared_invariants, ratio.subject
        )
    };
    if let Some(Equivalence::SoleComparand { tool, reason }) = ratio.equivalence {
        let _ = write!(
            cell,
            "; **NOT CORROBORATED: {} is the only external engine here — {}**",
            tool, reason
        );
    }
    cell
}

// --- The engine-internal statistic (#428) ----------------------------------------------------
//
// A second, separately named ratio. The wall-clock one above is the cost of *asking*, which is the
// honest end-to-end figure and is also why the startup-floor guard disqualifies every Katsura and
// Cyclic row the board holds: Singular's wall is its own `exec` up to `katsura-6`. The data for an
// engine comparison is nonetheless already here, because the adapters record each tool's
// self-reported stage times, and those are inside the process.
//
// It is **not** a relaxation of the floor guard and is never substituted into the wall-clock
// column. It compares like with like — engine-internal against engine-internal — and it has its own
// refusal conditions, because a tool-reported stage is only as good as the resolution it was
// printed at.

/// Which of a library's stages are its own engine time for `task`, summed.
///
/// `None` when the library reports nothing usable, which is a refusal and not a zero.
///
/// | library | reduced basis | lex basis by conversion | excluded, and why |
/// |---|---|---|---|
/// | `zeebra` | `basis` | `basis` + `conversion` | `conversion:` sub-stages, which are inside `conversion`; `quotient-dimension (for the invariant)`, which is work done to *report* an invariant and is already outside the published figure |
/// | `singular` | `solve` | `source-basis` + `solve` | — |
/// | `groebner.jl` | `solve` | n/a (no FGLM) | `process-wall` and `process-cpu`, which are the quantity this statistic exists to exclude — Julia's compiler |
/// | `sagebrush` | `solve` | `solve` | — |
/// | `msolve` | `f4: overall(elapsed)` | `f4:` + `sparse-fglm: overall(elapsed)` | every named sub-stage, which would double-count its own total |
///
/// msolve is the one library whose labels are its **own** rather than translated — deliberately,
/// because the correspondence with Zeebra's stage names is a finding that belongs in
/// `docs/research/msolve-implementation.md` and renaming here would hide it. So the selector names
/// msolve's totals rather than mapping them, and at the sizes this board reaches msolve's **10 ms**
/// stage resolution refuses the ratio anyway (see [`stage_resolution`]).
fn engine_internal_time(
    library: &str,
    task: super::Task,
    stages: &[(String, Duration)],
) -> Option<Duration> {
    let wanted: &[&str] = match (library, task) {
        ("zeebra", super::Task::LexBasisByConversion) => &["basis", "conversion"],
        ("zeebra", _) => &["basis"],
        ("singular", super::Task::LexBasisByConversion) => &["source-basis", "solve"],
        ("singular", _) => &["solve"],
        ("groebner.jl" | "sagebrush", _) => &["solve"],
        ("msolve", super::Task::LexBasisByConversion) => {
            &["f4: overall(elapsed)", "sparse-fglm: overall(elapsed)"]
        }
        ("msolve", _) => &["f4: overall(elapsed)"],
        _ => return None,
    };
    let mut total = Duration::ZERO;
    let mut found = false;
    for name in wanted {
        // Exact match on the whole label: `conversion` must not pick up `conversion: border`, and
        // a prefix match would silently double-count.
        for (_, elapsed) in stages.iter().filter(|(label, _)| label == name) {
            total += *elapsed;
            found = true;
        }
    }
    found.then_some(total)
}

/// The granularity a library prints a stage figure at, taken from the adapter that parses it.
///
/// Declared rather than inferred, and the figures are the parsers':
///
/// | library | printed as | resolution | where |
/// |---|---|---|---|
/// | `singular` | whole milliseconds | 1 ms | `singular.rs`, `@solve_ms` through `Duration::from_millis` |
/// | `msolve` | `%.2f sec` | 10 ms | `msolve.rs`, `timing_line` |
/// | `sagebrush` | `%.6f` seconds | 1 µs | `sagebrush.rs`, `#seconds:` |
/// | `groebner.jl` | Julia's own `@elapsed` | 1 µs | `groebner_jl.rs` |
/// | `zeebra` | an `Instant` difference | 1 µs | `zeebra.rs` |
///
/// 1 µs is a floor on the claim rather than a measured jitter: every one of those three reports
/// more digits than that, and no ratio on this board is within three orders of magnitude of it, so
/// a finer figure would be precision nobody can use.
fn stage_resolution(library: &str) -> Option<Duration> {
    Some(match library {
        "singular" => Duration::from_millis(1),
        "msolve" => Duration::from_millis(10),
        "sagebrush" | "groebner.jl" | "zeebra" => Duration::from_micros(1),
        _ => return None,
    })
}

/// A ratio of **engine-internal** times: the same task, with process setup excluded from both.
///
/// Deliberately a different type from [`Speedup`] rather than a field on it. The two answer
/// different questions — "what does it cost to ask" against "how fast is the engine" — and a
/// renderer that could reach for either through one type is a renderer that will eventually print
/// one under the other's heading.
#[derive(Clone, Debug, PartialEq)]
pub struct EngineRatio {
    /// The problem both rows solved.
    pub problem: String,

    /// The task both rows performed.
    pub task: super::Task,

    /// The library being compared against.
    pub baseline: String,

    /// The other library.
    pub subject: String,

    /// `baseline internal / subject internal`. Above one means the subject's engine is faster.
    pub ratio: f64,

    /// The baseline's own engine time, as it reported it.
    pub baseline_internal: Duration,

    /// The subject's own engine time, as it reported it.
    pub subject_internal: Duration,

    /// The smaller of the two operands measured in units of its own library's stage resolution.
    ///
    /// The refusal condition this statistic needs and the wall-clock one does not. Singular prints
    /// whole milliseconds, so a `0.0 ms` stage is not a fast engine and a `1 ms` stage carries
    /// ±50%. `None` when a library's resolution is not declared, which cannot happen for a row this
    /// type was built from — [`engine_internal_time`] and [`stage_resolution`] cover the same five
    /// libraries — and is read as a refusal if it ever does.
    pub resolution_multiple: Option<f64>,

    /// How many invariants the two answers were checked to agree on, as in [`Speedup`].
    pub shared_invariants: usize,

    /// The corpus's record of how this problem's ideal equivalence was established.
    pub equivalence: Option<Equivalence>,
}

impl EngineRatio {
    /// How many times its own resolution a reported stage must be before a ratio uses it.
    ///
    /// Five, which bounds the quantization error on each operand at ±10% and on the ratio at
    /// roughly ±20% in the worst case. Chosen rather than inherited: it admits the two rows this
    /// statistic was asked for — `katsura-7`'s Singular `solve` at 10 ms and `cyclic-6`'s at 7 ms —
    /// and refuses `katsura-4`'s at 0 ms, which is the case that makes a ratio meaningless. The
    /// uncertainty is not swept under it either: [`Self::relative_uncertainty`] is printed beside
    /// every figure.
    pub const RESOLUTION_MULTIPLE_REQUIRED: f64 = 5.0;

    /// Whether both operands are coarse-resolution-safe.
    pub fn is_resolved(&self) -> bool {
        self.resolution_multiple
            .is_some_and(|multiple| multiple >= Self::RESOLUTION_MULTIPLE_REQUIRED)
    }

    /// The quantization uncertainty the coarser operand puts on this ratio, as a fraction.
    ///
    /// A figure printed at resolution `r` is `x ± r/2`, so a figure of `k` resolution units carries
    /// `0.5 / k`. Reported for the coarser side only: the finer one is three orders of magnitude
    /// below it on every row this board holds.
    pub fn relative_uncertainty(&self) -> Option<f64> {
        self.resolution_multiple.map(|multiple| 0.5 / multiple)
    }

    /// Whether the corpus's evidence permits a cross-library figure for this problem at all.
    pub fn licenses_timing(&self) -> bool {
        self.equivalence
            .is_some_and(|equivalence| equivalence.licenses_timing())
    }

    /// Whether a third opinion exists, so a disagreement could name the odd one out.
    pub fn is_corroborated(&self) -> bool {
        self.equivalence
            .is_some_and(|equivalence| equivalence.is_corroborated())
    }

    /// Whether a conclusion may rest on this ratio's comparand.
    pub fn has_authoritative_comparand(&self) -> bool {
        !Speedup::NOT_AUTHORITATIVE.contains(&self.subject.as_str())
    }

    /// Whether this ratio may be published **as an engine comparison**.
    ///
    /// The same provenance and invariant gates as [`Speedup::is_publishable`], with the startup
    /// floor replaced by the resolution condition — because that is exactly the substitution this
    /// statistic is: the floor guard exists to stop a wall-clock ratio against a startup-dominated
    /// operand, and there is no startup in either operand here.
    pub fn is_publishable(&self) -> bool {
        self.licenses_timing() && self.is_resolved() && self.shared_invariants > 0
    }
}

#[cfg(test)]
mod tests {
    use super::{
        bytes_cell, duration_cell, CompetitiveBoard, CompetitiveRecord, Outcome,
        COMPETITIVE_HISTORY_CONTRACT,
    };
    use crate::{
        grobner::{
            external::{
                corpus::{CorpusEntry, Equivalence, Rung},
                Answer, FieldSpec, Instance, Invariants, LimitStop, Limits, Measurement,
                RunFailure, RunReport, RunStatus, Task, ToolVersion, Unsupported, Verification,
            },
            record::Environment,
        },
        util::Json,
        MonomialOrder,
    };
    use std::time::Duration;

    fn environment() -> Environment {
        Environment {
            commit: "deadbeef".to_string(),
            base_commit: "deadbeef".to_string(),
            patch_id: String::new(),
            machine: "workstation".to_string(),
            cpu: "64 logical, taskset 0-7".to_string(),
            concurrency: 1,
            build: "release, target-cpu=x86-64-v3".to_string(),
            policy: "600 s wall, 1 worker".to_string(),
        }
    }

    fn instance() -> Instance {
        Instance::new(
            "katsura-8",
            "katsura",
            FieldSpec::prime(65521),
            (1..=8).map(|i| format!("x{}", i)).collect(),
            vec!["x1^2+x2-1".to_string(), "x2^2-x1".to_string()],
            MonomialOrder::GradedReverseLexicographic,
        )
    }

    fn answered(dimension: usize) -> RunStatus {
        RunStatus::Complete(Answer::from_invariants(
            Invariants::none()
                .with_quotient_dimension(dimension)
                .with_leading_monomials(vec!["x1^2".to_string(), "x2^2".to_string()]),
        ))
    }

    fn row(library: &str, status: RunStatus, wall_ms: u64) -> CompetitiveRecord {
        let instance = instance();
        let report = RunReport::new(
            library,
            &instance,
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(600)),
            status,
            Measurement::wall(Duration::from_millis(wall_ms)),
        )
        .with_version(ToolVersion::new(library, "1.0"))
        .with_command_line(format!("{} katsura-8.in", library));
        CompetitiveRecord::of(&report, &instance, &environment())
    }

    /// A row on a named problem, so several rows can sit on one board without sharing a digest.
    fn named_row(
        problem: &str,
        library: &str,
        status: RunStatus,
        wall_ms: f64,
    ) -> CompetitiveRecord {
        let mut instance = instance();
        instance.name = problem.to_string();
        // The digest covers the generators, so perturb one to make each problem distinct. The
        // whole name goes in: a perturbation derived from the length and first byte collided for
        // same-shaped names like `f1`/`f2`, which silently made four problems one and had the
        // board cross-compare every pairing of their rows.
        instance.system[0] = format!("x1^2+x2-{}", problem);
        let report = RunReport::new(
            library,
            &instance,
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(600)),
            status,
            Measurement::wall(Duration::from_secs_f64(wall_ms / 1e3)),
        )
        .with_version(ToolVersion::new(library, "1.0"));
        CompetitiveRecord::of(&report, &instance, &environment())
    }

    /// A row with stage timings, for the engine-internal statistic.
    fn staged_row(library: &str, wall_ms: u64, stages: &[(&str, Duration)]) -> CompetitiveRecord {
        let instance = instance();
        let mut measurement = Measurement::wall(Duration::from_millis(wall_ms));
        for (name, elapsed) in stages {
            measurement = measurement.with_stage(*name, *elapsed);
        }
        let report = RunReport::new(
            library,
            &instance,
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(600)),
            answered(4),
            measurement,
        )
        .with_version(ToolVersion::new(library, "1.0"));
        CompetitiveRecord::of(&report, &instance, &environment())
    }

    /// The engine-internal ratio uses each library's own stage, not the wall.
    ///
    /// The statistic's reason for existing: on this row the wall-clock ratio is startup-dominated
    /// and disqualified, while the engines are 2.58x apart.
    #[test]
    fn test_the_engine_ratio_is_taken_over_stages_and_not_walls() {
        let mut board = CompetitiveBoard::new();
        board.add(staged_row(
            "zeebra",
            26,
            &[("basis", Duration::from_micros(25_800))],
        ));
        board.add(staged_row(
            "singular",
            36,
            &[("solve", Duration::from_millis(10))],
        ));
        let ratios = board.engine_ratios("zeebra");
        assert_eq!(ratios.len(), 1);
        let ratio = &ratios[0];
        assert_eq!(ratio.subject, "singular");
        assert_eq!(ratio.baseline_internal, Duration::from_micros(25_800));
        assert_eq!(ratio.subject_internal, Duration::from_millis(10));
        assert!(
            (ratio.ratio - 2.58).abs() < 0.01,
            "25.8 ms of engine against 10 ms, not 26 ms of wall against 36: {}",
            ratio.ratio
        );
        // 10 ms at Singular's 1 ms granularity, which clears the gate at exactly 10x.
        assert_eq!(ratio.resolution_multiple, Some(10.0));
        assert!(ratio.is_resolved());
        assert_eq!(ratio.relative_uncertainty(), Some(0.05));
    }

    /// A stage at its library's own granularity is refused, which is `katsura-4` against Singular.
    ///
    /// The condition that replaces the startup floor. A `0.0 ms` or `1 ms` Singular stage is the
    /// printf speaking, and a ratio against it is as meaningless as a wall-clock ratio against
    /// `exec`.
    #[test]
    fn test_a_stage_near_its_resolution_is_refused() {
        let mut board = CompetitiveBoard::new();
        board.add(staged_row(
            "zeebra",
            1,
            &[("basis", Duration::from_micros(300))],
        ));
        board.add(staged_row(
            "singular",
            36,
            &[("solve", Duration::from_millis(2))],
        ));
        let ratios = board.engine_ratios("zeebra");
        assert_eq!(ratios.len(), 1);
        assert_eq!(ratios[0].resolution_multiple, Some(2.0));
        assert!(!ratios[0].is_resolved(), "2 ms at 1 ms granularity is ±25%");
        assert!(!ratios[0].is_publishable());
        let markdown = board.to_markdown();
        assert!(
            markdown.contains("NOT A RESOLVED COMPARISON"),
            "the refusal is printed in the cell rather than dropping the row"
        );
        assert!(
            markdown.contains("1 refused on stage resolution"),
            "and counted before the table"
        );
    }

    /// A zero-length engine time yields no row at all, because it has no reciprocal.
    #[test]
    fn test_a_zero_engine_time_contributes_no_ratio() {
        let mut board = CompetitiveBoard::new();
        board.add(staged_row(
            "zeebra",
            1,
            &[("basis", Duration::from_micros(400))],
        ));
        board.add(staged_row("singular", 36, &[("solve", Duration::ZERO)]));
        assert!(board.engine_ratios("zeebra").is_empty());
    }

    /// A library reporting no usable stage contributes no row rather than a zero.
    #[test]
    fn test_a_library_with_no_usable_stage_contributes_no_ratio() {
        let mut board = CompetitiveBoard::new();
        board.add(staged_row(
            "zeebra",
            26,
            &[("basis", Duration::from_millis(26))],
        ));
        // Groebner.jl's process figures are precisely what this statistic excludes, so a row with
        // only those is a row with no engine time.
        board.add(staged_row(
            "groebner.jl",
            7_400,
            &[
                ("process-wall", Duration::from_millis(7_400)),
                ("process-cpu", Duration::from_millis(8_230)),
            ],
        ));
        assert!(board.engine_ratios("zeebra").is_empty());
    }

    /// Zeebra's conversion sub-stages are inside `conversion` and must not be counted twice.
    #[test]
    fn test_the_conversion_substages_are_not_double_counted() {
        let stages = vec![
            ("basis".to_string(), Duration::from_millis(10)),
            ("conversion".to_string(), Duration::from_millis(4)),
            (
                "conversion: dependence".to_string(),
                Duration::from_millis(3),
            ),
            ("conversion: border".to_string(), Duration::from_millis(1)),
            (
                "quotient-dimension (for the invariant)".to_string(),
                Duration::from_millis(5),
            ),
        ];
        assert_eq!(
            super::engine_internal_time("zeebra", Task::LexBasisByConversion, &stages),
            Some(Duration::from_millis(14)),
            "basis + conversion, with the sub-stages and the invariant's cost excluded"
        );
        assert_eq!(
            super::engine_internal_time("zeebra", Task::ReducedGrobnerBasis, &stages),
            Some(Duration::from_millis(10)),
            "the basis task does not pay for a conversion it did not do"
        );
    }

    /// Singular's conversion task is both of its stages; an unknown library has no selector.
    #[test]
    fn test_each_librarys_engine_stages_are_the_ones_it_reports() {
        let singular = vec![
            ("source-basis".to_string(), Duration::from_millis(10)),
            ("solve".to_string(), Duration::from_millis(8)),
        ];
        assert_eq!(
            super::engine_internal_time("singular", Task::LexBasisByConversion, &singular),
            Some(Duration::from_millis(18))
        );
        assert_eq!(
            super::engine_internal_time("singular", Task::ReducedGrobnerBasis, &singular),
            Some(Duration::from_millis(8)),
            "a direct basis is the solve stage alone"
        );
        assert_eq!(
            super::engine_internal_time("nobody", Task::ReducedGrobnerBasis, &singular),
            None,
            "an unrecognized library has no declared stage vocabulary"
        );
        assert_eq!(super::stage_resolution("nobody"), None);
    }

    /// The engine-internal section is separate from the wall-clock one and says it is not end to end.
    ///
    /// The whole point of a second statistic: a reader must not be able to mistake it for the cost
    /// of asking, and the floor guard above must still be visible on the same board.
    #[test]
    fn test_the_two_statistics_are_rendered_apart_and_labelled() {
        let mut board = CompetitiveBoard::new();
        board.add(staged_row(
            "zeebra",
            26,
            &[("basis", Duration::from_micros(25_800))],
        ));
        board.add(staged_row(
            "singular",
            36,
            &[("solve", Duration::from_millis(10))],
        ));
        let markdown = board.to_markdown();
        assert!(markdown.contains("## Speedups over Zeebra"));
        assert!(markdown.contains("## Engine-internal speedups over Zeebra"));
        assert!(
            markdown.contains("not an end-to-end cost"),
            "the exclusion has to be stated where the figure is"
        );
        assert!(
            markdown.contains("2.58x ±5%"),
            "the figure carries the coarser operand's quantization uncertainty"
        );
        // The same pair, two statistics, opposite readings: 26 ms of wall against 36 ms is 0.72x
        // and looks like a loss, while 25.8 ms of engine against 10 ms is 2.58x the other way.
        // Both are on the board, neither is substituted for the other, and that is #428's point.
        assert!(
            markdown.contains("0.72x"),
            "the wall-clock ratio is unchanged by the new statistic"
        );
    }

    /// An answered row carries a wall time; a row with no answer carries none.
    ///
    /// The field's whole purpose: an unsupported input must not present as an instantaneous
    /// success, and a limit stop must not present the limit as a measurement.
    #[test]
    fn test_only_an_answered_row_carries_a_wall_time() {
        assert_eq!(
            row("zeebra", answered(4), 120).wall,
            Some(Duration::from_millis(120))
        );

        let unsupported = row(
            "msolve",
            RunStatus::Unsupported(Unsupported::Characteristic {
                characteristic: 1 << 61,
                supported_below: 1 << 31,
            }),
            0,
        );
        assert_eq!(unsupported.wall, None);
        assert!(!unsupported.is_timing_evidence());

        let stopped = row(
            "singular",
            RunStatus::StoppedByLimit(LimitStop::WallClock {
                limit: Duration::from_secs(600),
                elapsed: Duration::from_secs(600),
            }),
            600_000,
        );
        assert_eq!(
            stopped.wall, None,
            "the limit lives in `limits`; repeating it as a time invites being read as one"
        );
        assert_eq!(stopped.limits.wall, Duration::from_secs(600));
    }

    /// A row with no answer says what stands in place of a time.
    #[test]
    fn test_a_row_with_no_answer_names_the_limit_or_the_missing_capability() {
        let unsupported = Outcome::Unsupported(Unsupported::Characteristic {
            characteristic: 1 << 61,
            supported_below: 1 << 31,
        });
        let detail = unsupported.instead_of_a_time().expect("there is no time");
        assert!(detail.contains("2147483648"), "{}", detail);

        let stopped = Outcome::StoppedByLimit(LimitStop::WallClock {
            limit: Duration::from_secs(600),
            elapsed: Duration::from_secs(600),
        });
        assert!(stopped.instead_of_a_time().is_some());

        assert_eq!(Outcome::Complete.instead_of_a_time(), None);
        assert_eq!(Outcome::Verified.instead_of_a_time(), None);
    }

    /// A row refused for the environment reads as not run, and is never timing evidence.
    ///
    /// The cell is what a reader of the board actually sees, so this is where #316's requirement —
    /// "a board must show the row as not attempted rather than as a result" — is pinned.
    #[test]
    fn test_an_environment_refusal_reads_as_not_run_and_is_not_timing_evidence() {
        let outcome = Outcome::Failed(RunFailure::Environment {
            variable: "SB_SIGF4".to_string(),
            detail: "selects the experimental signature-based F4".to_string(),
        });
        assert!(
            !outcome.is_timing_evidence(),
            "nothing ran, so there is no time to publish"
        );
        let cell = outcome.instead_of_a_time().expect("there is no time");
        assert!(cell.contains("not run"), "{}", cell);
        assert!(cell.contains("SB_SIGF4"), "{}", cell);
    }

    /// A verification that compared nothing does not make the row verified.
    #[test]
    fn test_a_verification_that_compared_nothing_is_not_verified() {
        let nothing = Invariants::none();
        let hollow = Verification::of("msolve", &nothing, &nothing).expect("no disagreement");
        let instance = instance();
        let report = RunReport::new(
            "zeebra",
            &instance,
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(600)),
            RunStatus::Verified(Answer::default(), hollow),
            Measurement::wall(Duration::from_millis(10)),
        );
        let row = CompetitiveRecord::of(&report, &instance, &environment());
        assert_eq!(row.outcome, Outcome::Complete, "not Verified");
        assert!(
            row.verification.is_some(),
            "but the check is still recorded"
        );
    }

    /// A row under a weighted order round-trips, carrying its weight vector — #625.
    ///
    /// This is the thing #625 was filed for: until the tag encoded the vector, a weighted order
    /// read back as `None` and `from_json` rejected the row, so **no record could be posed under
    /// one at all**. The assertion that matters is the last one — the order that comes back is the
    /// same order, vector and tie-break included, and not merely "some weighted order".
    #[test]
    fn test_a_row_under_a_weighted_order_round_trips_with_its_vector() {
        let order =
            MonomialOrder::weighted(&[1, 7, 49], crate::WeightedTieBreak::LastVariableFirst)
                .expect("the Griffin weight vector is positive");
        let mut original = row("zeebra", answered(8), 1_250);
        original.order = order;

        let text = original.to_json().to_json();
        assert!(
            text.contains("weighted:lastvar:1,7,49"),
            "the record must name the vector it was computed under: {text}"
        );

        let back =
            CompetitiveRecord::from_json(&Json::parse(&text).expect("valid")).expect("round trips");
        assert_eq!(back.order, order);

        // And a different vector is a different order, so two such rows cannot be conflated.
        let other =
            MonomialOrder::weighted(&[1, 7, 50], crate::WeightedTieBreak::LastVariableFirst)
                .expect("positive");
        assert_ne!(back.order, other);
    }

    /// A row round-trips through JSON, and absent figures stay absent.
    #[test]
    fn test_a_row_round_trips_and_absent_figures_stay_absent() {
        let original = row("zeebra", answered(8), 1_250);
        let text = original.to_json().to_json();
        let back =
            CompetitiveRecord::from_json(&Json::parse(&text).expect("valid")).expect("round trips");

        assert_eq!(back.problem, "katsura-8");
        assert_eq!(back.problem_digest, original.problem_digest);
        assert_eq!(back.task, Task::ReducedGrobnerBasis);
        assert_eq!(back.order, MonomialOrder::GradedReverseLexicographic);
        assert_eq!(back.field.characteristic, 65521);
        assert_eq!(back.library, "zeebra");
        assert_eq!(back.library_version.as_deref(), Some("zeebra 1.0"));
        assert_eq!(back.wall, Some(Duration::from_millis(1_250)));
        assert_eq!(back.limits.workers, 1);
        assert_eq!(back.environment.commit, "deadbeef");
        assert_eq!(back.invariants.quotient_dimension, Some(8));
        assert_eq!(back.invariants.basis_cardinality, Some(2));

        // Nothing was measured, so nothing is claimed.
        assert!(!text.contains("peak_rss_bytes"));
        assert!(!text.contains("cpu_nanos"));
        assert_eq!(back.peak_rss_bytes, None);
        assert_eq!(back.cpu, None);
    }

    /// An unsupported row round-trips without acquiring a time.
    #[test]
    fn test_an_unsupported_row_round_trips_without_a_time() {
        let original = row(
            "msolve",
            RunStatus::Unsupported(Unsupported::Characteristic {
                characteristic: 1 << 61,
                supported_below: 1 << 31,
            }),
            0,
        );
        let text = original.to_json().to_json();
        assert!(
            !text.contains("wall_nanos\": 0"),
            "an unsupported row must not carry a zero time"
        );
        let back =
            CompetitiveRecord::from_json(&Json::parse(&text).expect("valid")).expect("round trips");
        assert_eq!(back.wall, None);
        assert_eq!(back.outcome.tag(), "unsupported");
        assert!(!back.is_timing_evidence());
    }

    /// A failed row round-trips and keeps its failure visible.
    #[test]
    fn test_a_failed_row_round_trips() {
        let original = row(
            "groebner.jl",
            RunStatus::Failed(RunFailure::Unavailable {
                binary: "julia".to_string(),
                reason: "No such file or directory".to_string(),
            }),
            0,
        );
        let text = original.to_json().to_json();
        let back =
            CompetitiveRecord::from_json(&Json::parse(&text).expect("valid")).expect("round trips");
        assert_eq!(back.outcome.tag(), "failed");
        assert!(back.outcome.instead_of_a_time().is_some());
    }

    /// A speedup is computed between two answered rows on the same problem, task and environment.
    #[test]
    fn test_a_speedup_is_computed_between_equivalent_answered_rows() {
        let mut board = CompetitiveBoard::new();
        board.add(row("zeebra", answered(8), 400));
        board.add(row("singular", answered(8), 1_600));

        let speedups = board.speedups("zeebra");
        assert_eq!(speedups.len(), 1);
        assert_eq!(speedups[0].subject, "singular");
        assert!(
            (speedups[0].ratio - 0.25).abs() < 1e-9,
            "{} -- Singular is four times slower, so its ratio over Zeebra is a quarter",
            speedups[0].ratio
        );
        assert_eq!(
            speedups[0].shared_invariants, 3,
            "dimension, leading monomials and cardinality were all compared"
        );
    }

    /// No speedup is computed against an unsupported, limit-stopped or failed row.
    ///
    /// The protocol's headline rule, at the one place a ratio is produced for this board.
    #[test]
    fn test_no_speedup_against_a_row_that_produced_no_answer() {
        for status in [
            RunStatus::Unsupported(Unsupported::Characteristic {
                characteristic: 1 << 61,
                supported_below: 1 << 31,
            }),
            RunStatus::StoppedByLimit(LimitStop::WallClock {
                limit: Duration::from_secs(600),
                elapsed: Duration::from_secs(600),
            }),
            RunStatus::Failed(RunFailure::Incomplete {
                detail: "no marker".to_string(),
            }),
        ] {
            let mut board = CompetitiveBoard::new();
            board.add(row("zeebra", answered(8), 400));
            board.add(row("msolve", status.clone(), 600_000));
            assert!(
                board.speedups("zeebra").is_empty(),
                "a ratio was produced against {}",
                status.tag()
            );
        }
    }

    /// No speedup across different environments or different limits.
    #[test]
    fn test_no_speedup_across_environments_or_limits() {
        let mut board = CompetitiveBoard::new();
        board.add(row("zeebra", answered(8), 400));
        let mut elsewhere = row("singular", answered(8), 1_600);
        elsewhere.environment.machine = "laptop".to_string();
        board.add(elsewhere);
        assert!(board.speedups("zeebra").is_empty(), "different machines");

        let mut board = CompetitiveBoard::new();
        board.add(row("zeebra", answered(8), 400));
        let mut other_limits = row("singular", answered(8), 1_600);
        other_limits.limits = Limits::wall(Duration::from_secs(60));
        board.add(other_limits);
        assert!(board.speedups("zeebra").is_empty(), "different limits");
    }

    /// A ratio between two unchecked answers is reported as not publishable rather than dropped.
    #[test]
    fn test_an_unchecked_ratio_is_marked_rather_than_dropped() {
        let unchecked = || RunStatus::Complete(Answer::default());
        let mut board = CompetitiveBoard::new();
        board.add(row("zeebra", unchecked(), 400));
        board.add(row("singular", unchecked(), 1_600));

        let speedups = board.speedups("zeebra");
        assert_eq!(speedups.len(), 1);
        assert_eq!(speedups[0].shared_invariants, 0);

        let markdown = board.to_markdown();
        assert!(
            markdown.contains("NOT PUBLISHABLE"),
            "an unchecked ratio must be marked: {}",
            markdown
        );
    }

    /// Loading the board and writing it back is a **fixed point**, even on damaged input.
    ///
    /// The property a regenerable artifact needs and did not have. An older writer stored the
    /// *rendered* outcome detail, so each `competitive --write` read it into a variant and wrote
    /// it back one prefix longer — six stored rows reached `unsupported: unsupported: ...` that
    /// way, and the damage grew on every regeneration rather than staying put.
    ///
    /// Asserted from deliberately damaged input, because healing is the behaviour that matters:
    /// the rows already on disk have to come out clean.
    #[test]
    fn test_loading_and_rewriting_is_a_fixed_point() {
        let damaged = row(
            "msolve",
            RunStatus::Unsupported(Unsupported::Characteristic {
                characteristic: 1 << 61,
                supported_below: 1 << 31,
            }),
            0,
        );
        let mut json = damaged.to_json();
        // Damage it exactly the way the old writer did, twice over.
        if let Json::Object(fields) = &mut json {
            for (key, value) in fields.iter_mut() {
                if key == "outcome_detail" {
                    let inner = value.as_str().unwrap_or_default().to_string();
                    *value = Json::string(format!("unsupported: unsupported: {}", inner));
                }
            }
        }

        let once = CompetitiveRecord::from_json(&json).expect("reads damaged input");
        let healed = once.to_json().to_json();
        assert!(
            !healed.contains("unsupported: "),
            "the first rewrite must heal the prefix, not carry it: {}",
            healed
        );

        // And it is stable: a second pass changes nothing.
        let twice = CompetitiveRecord::from_json(&Json::parse(&healed).expect("valid"))
            .expect("round trips");
        assert_eq!(
            twice.to_json().to_json(),
            healed,
            "load -> write must be a fixed point"
        );

        // The same must hold for the other two reconstruction variants, whose `Display` wraps
        // their payload where `Unsupported::Representation`'s does not.
        for status in [
            RunStatus::Failed(RunFailure::Reported {
                message: "no @gbsize marker was printed".to_string(),
            }),
            RunStatus::StoppedByLimit(LimitStop::ToolCap {
                detail: "20006072 live nonzero entries".to_string(),
            }),
        ] {
            let first = row("singular", status, 0).to_json().to_json();
            let reloaded = CompetitiveRecord::from_json(&Json::parse(&first).expect("valid"))
                .expect("round trips")
                .to_json()
                .to_json();
            assert_eq!(reloaded, first, "a rewrite must not re-wrap the detail");
        }

        // The rendering still carries exactly one prefix.
        let rendered = twice.outcome.instead_of_a_time().expect("no time");
        assert_eq!(rendered.matches("unsupported").count(), 1, "{}", rendered);
    }

    /// A stored outcome detail is **bare**, so a round trip does not double-prefix it.
    ///
    /// The first 72 rows the board ever held read `unsupported: unsupported: characteristic ...`,
    /// because `to_json` stored `instead_of_a_time`'s prefixed rendering and `from_json` read it
    /// back into the variant's detail field, where the next render prefixed it again. The stored
    /// form has to be the datum, not a rendering of it.
    #[test]
    fn test_a_stored_outcome_detail_does_not_double_prefix_on_a_round_trip() {
        let row = row(
            "msolve",
            RunStatus::Unsupported(Unsupported::Characteristic {
                characteristic: 1 << 61,
                supported_below: 1 << 31,
            }),
            0,
        );
        let text = row.to_json().to_json();
        assert!(
            !text.contains("unsupported: "),
            "the stored detail must be bare: {}",
            text
        );

        let back =
            CompetitiveRecord::from_json(&Json::parse(&text).expect("valid")).expect("round trips");
        let rendered = back.outcome.instead_of_a_time().expect("there is no time");
        assert_eq!(
            rendered.matches("unsupported").count(),
            1,
            "re-rendering a read-back row must prefix exactly once: {}",
            rendered
        );
    }

    /// A startup floor is observed from the board, and a ratio against it is disqualified.
    ///
    /// The measured case, reproduced: Singular's floor on the real sweep was 36.0 ms, and
    /// `mq-planted-6` finished in 0.08 ms against Singular's 36.01 ms — an apparent **450x** that
    /// is entirely the cost of starting Singular. The board must refuse to call that an engine
    /// comparison, and must still **keep the row**, because it is the artifact that stops somebody
    /// recomputing the 450x from the raw numbers later.
    #[test]
    fn test_a_ratio_against_a_startup_floor_is_not_an_engine_comparison() {
        let mut board = CompetitiveBoard::new();
        // Four Singular rows at its floor, plus one far above it: the shape the real sweep had.
        // Named after real corpus rungs, because the provenance gate (#518) refuses a problem
        // the corpus has no recorded ideal equivalence for and would mark these rows on that
        // instead of on the floor.
        for (name, zeebra_ms, singular_ms) in [
            ("katsura-4", 0.08, 36.01),
            ("katsura-5", 0.14, 36.04),
            ("katsura-6", 0.58, 36.05),
            ("katsura-7", 0.55, 36.08),
            ("katsura-8", 29963.0, 7290.0),
        ] {
            board.add(named_row(name, "zeebra", answered(8), zeebra_ms));
            board.add(named_row(name, "singular", answered(8), singular_ms));
        }

        let floor = board
            .startup_floor("singular")
            .expect("five answered rows is enough to observe a floor");
        assert!(
            (floor.as_secs_f64() * 1e3 - 36.01).abs() < 0.001,
            "{:?} is not Singular's 36.0 ms floor",
            floor
        );

        // Asked from **Zeebra**'s side, which is how the report reads it, and the direction that
        // exposed the original bug: Zeebra runs in-process so its own floor is microseconds, and
        // measuring only the baseline against its own floor passed every ratio.
        let speedups = board.speedups("zeebra");
        let disqualified: Vec<&super::Speedup> = speedups
            .iter()
            .filter(|s| !s.is_engine_comparison())
            .collect();
        assert_eq!(
            disqualified.len(),
            4,
            "the four rows where Singular sits at its own floor must all be disqualified"
        );
        for speedup in &disqualified {
            assert!(!speedup.is_publishable());
            assert!(speedup.floor_multiple.unwrap() < 2.0);
        }

        // The one real row survives: Singular's wall there is 200x its floor.
        let real: Vec<&super::Speedup> = speedups
            .iter()
            .filter(|s| s.is_engine_comparison())
            .collect();
        assert_eq!(real.len(), 1);
        assert_eq!(real[0].problem, "katsura-8");
        assert!(real[0].is_publishable());
        assert!(
            (real[0].ratio - 29963.0 / 7290.0).abs() < 1e-6,
            "from Zeebra's side the ratio is Zeebra's wall over Singular's: {}",
            real[0].ratio
        );
        assert!(real[0].floor_multiple.unwrap() > 100.0);

        // And the rows are still on the board, all ten of them.
        assert_eq!(board.rows().len(), 10);
        let markdown = board.to_markdown();
        assert!(
            markdown.contains("NOT AN ENGINE COMPARISON"),
            "the renderer must mark the disqualification: {}",
            markdown
        );
    }

    /// Too few rows to observe a floor yields none, and does not disqualify anything.
    ///
    /// Refusing on absent evidence would silently drop every row of a library that has only been
    /// measured once or twice, which is worse than letting a reader check.
    #[test]
    fn test_too_few_rows_to_observe_a_floor_disqualifies_nothing() {
        let mut board = CompetitiveBoard::new();
        board.add(named_row("a", "zeebra", answered(8), 1.0));
        board.add(named_row("a", "singular", answered(8), 36.0));
        assert_eq!(board.startup_floor("singular"), None);

        let speedups = board.speedups("zeebra");
        assert_eq!(speedups.len(), 1);
        assert_eq!(speedups[0].floor_multiple, None);
        assert!(
            speedups[0].is_engine_comparison(),
            "an unknown floor must not be read as a disqualification"
        );
    }

    /// A ratio on a problem the corpus has no equivalence for is refused in the cell, not dropped.
    ///
    /// The gate the corpus states and nothing read (#518): `licenses_timing` and
    /// `is_corroborated` had no consumer in the renderer, so a rung's provenance could not change
    /// anything the board published. Unlike the startup floor, absent evidence here is a refusal —
    /// it is visible, where dropping the row would not be.
    #[test]
    fn test_a_ratio_with_no_recorded_equivalence_is_refused_in_the_cell() {
        let mut board = CompetitiveBoard::new();
        board.add(named_row(
            "not-a-corpus-rung",
            "zeebra",
            answered(64),
            100.0,
        ));
        board.add(named_row(
            "not-a-corpus-rung",
            "singular",
            answered(64),
            400.0,
        ));

        let speedups = board.speedups("zeebra");
        assert_eq!(speedups.len(), 1, "the pair is still computed");
        assert_eq!(speedups[0].equivalence, None);
        assert!(!speedups[0].licenses_timing());
        assert!(!speedups[0].is_corroborated());
        assert!(
            !speedups[0].is_publishable(),
            "an engine comparison with agreeing invariants is still unpublishable without \
             recorded provenance"
        );
        assert!(
            speedups[0].is_engine_comparison() && speedups[0].shared_invariants > 0,
            "the other two gates pass, so provenance is the only thing refusing it"
        );

        let markdown = board.to_markdown();
        assert!(
            markdown.contains("is not a corpus rung"),
            "the refusal names the problem\n{}",
            markdown
        );
        assert!(
            markdown.contains("| **none recorded** |"),
            "and the provenance column says there is none\n{}",
            markdown
        );
        assert!(
            markdown.contains("0.25x"),
            "the ratio is still rendered, so nobody recomputes it from the raw rows\n{}",
            markdown
        );
        assert!(
            markdown.contains("1 refused for want of a recorded ideal equivalence"),
            "and the summary counts it\n{}",
            markdown
        );
    }

    /// Two rungs over `2^64 - 353`, where Groebner.jl is the only external engine that reaches.
    fn wide_rungs() -> Vec<CorpusEntry> {
        ["wide64-n1", "wide64-n2"]
            .into_iter()
            .map(|name| CorpusEntry {
                name,
                family: "wide64",
                rung: Rung::Easy,
                zero_dimensional: true,
                quotient_dimension: Some(5),
                equivalence: Equivalence::SoleComparand {
                    tool: "Groebner.jl",
                    reason: "2^64 - 353 is above every other engine's ceiling",
                },
                digests: &[],
            })
            .collect()
    }

    /// A sole-comparand ratio is published **with the fact stated**, which is the corpus's rule.
    ///
    /// A field above `2^62` is the real case: Groebner.jl is the only external engine that reaches
    /// it, so the agreement is two-way and nothing can name the odd one out. Before #518 such a row
    /// rendered exactly like a three-engine Katsura row. The rungs are the caller's own, supplied
    /// through [`CompetitiveBoard::with_corpus`].
    #[test]
    fn test_a_sole_comparand_ratio_is_published_with_the_fact_stated() {
        let mut board = CompetitiveBoard::new().with_corpus(wide_rungs());
        for problem in ["wide64-n1", "wide64-n2"] {
            board.add(named_row(problem, "zeebra", answered(5), 4_000.0));
            board.add(named_row(problem, "groebner.jl", answered(5), 1_000.0));
        }

        let speedups = board.speedups("zeebra");
        assert_eq!(speedups.len(), 2);
        for speedup in &speedups {
            assert!(
                speedup.licenses_timing(),
                "one engine still licenses a ratio"
            );
            assert!(!speedup.is_corroborated(), "nothing triangulates it");
            assert!(
                speedup.is_publishable(),
                "publishable, with the fact stated"
            );
        }

        let markdown = board.to_markdown();
        assert!(
            markdown.contains("sole-comparand (Groebner.jl)"),
            "the provenance column names the one engine\n{}",
            markdown
        );
        assert!(
            markdown.contains("NOT CORROBORATED"),
            "and the cell states the fact beside the ratio\n{}",
            markdown
        );
        assert!(
            markdown.contains("2 resting on a sole comparand and therefore uncorroborated"),
            "and the summary counts them among the publishable\n{}",
            markdown
        );
    }

    /// A board without the caller's corpus refuses those rows, and the public ladder still applies
    /// to a board that has one.
    #[test]
    fn test_a_callers_corpus_extends_the_ladder_without_replacing_it() {
        let mut bare = CompetitiveBoard::new();
        let mut extended = CompetitiveBoard::new().with_corpus(wide_rungs());
        for board in [&mut bare, &mut extended] {
            board.add(named_row("wide64-n1", "zeebra", answered(5), 4_000.0));
            board.add(named_row("wide64-n1", "groebner.jl", answered(5), 1_000.0));
            board.add(named_row("katsura-4", "zeebra", answered(5), 4_000.0));
            board.add(named_row("katsura-4", "groebner.jl", answered(5), 1_000.0));
        }
        let licensed = |board: &CompetitiveBoard| -> Vec<String> {
            board
                .speedups("zeebra")
                .into_iter()
                .filter(|speedup| speedup.licenses_timing())
                .map(|speedup| speedup.problem)
                .collect()
        };
        assert_eq!(licensed(&bare), vec!["katsura-4".to_string()]);
        let mut both = licensed(&extended);
        both.sort();
        assert_eq!(both, vec!["katsura-4".to_string(), "wide64-n1".to_string()]);
    }

    /// A family no external engine can represent is refused by name, with the corpus's reason.
    ///
    /// No ladder rung is `NoComparand` today — #386 moved the last of them to `SoleComparand` —
    /// so the variant is exercised directly. It is the one the gate exists for: a refusal that
    /// never fires on the current corpus still has to be the behaviour when a rung needs it.
    #[test]
    fn test_a_family_with_no_comparand_is_refused_by_name() {
        let unpublishable = super::Speedup {
            problem: "a-254-bit-family".to_string(),
            task: Task::ReducedGrobnerBasis,
            baseline: "zeebra".to_string(),
            subject: "singular".to_string(),
            ratio: 7.0,
            shared_invariants: 2,
            floor_multiple: Some(500.0),
            equivalence: Some(super::Equivalence::NoComparand {
                reason: "no surveyed engine reaches a 254-bit prime",
            }),
        };

        assert!(!unpublishable.licenses_timing());
        assert!(!unpublishable.is_publishable());
        let cell = super::verdict_cell(&unpublishable);
        assert!(
            cell.contains("NOT PUBLISHABLE")
                && cell.contains("no surveyed engine reaches a 254-bit prime"),
            "the refusal carries the corpus's own reason: {}",
            cell
        );
        assert_eq!(super::provenance_cell(&unpublishable), "no-comparand");
    }

    /// The board round-trips through its history form, contract and count included.
    #[test]
    fn test_the_board_round_trips_through_its_history_form() {
        let mut board = CompetitiveBoard::new();
        board.add(row("zeebra", answered(8), 400));
        board.add(row("singular", answered(8), 1_600));

        let json = board.to_json();
        assert_eq!(
            json.get("contract").and_then(Json::as_str),
            Some(COMPETITIVE_HISTORY_CONTRACT)
        );
        assert_eq!(json.get("row_count").and_then(Json::as_int), Some(2));

        let text = json.to_json();
        let back = CompetitiveBoard::load(&Json::parse(&text).expect("valid")).expect("loads");
        assert_eq!(back.rows().len(), 2);
        let order: Vec<&str> = back.rows().iter().map(|row| row.library.as_str()).collect();
        assert_eq!(
            order,
            ["zeebra", "singular"],
            "insertion order is preserved"
        );
    }

    /// The rendered table names the missing capability where a time would be.
    #[test]
    fn test_the_table_names_the_missing_capability_instead_of_a_time() {
        let mut board = CompetitiveBoard::new();
        board.add(row("zeebra", answered(8), 400));
        board.add(row(
            "msolve",
            RunStatus::Unsupported(Unsupported::Characteristic {
                characteristic: 1 << 61,
                supported_below: 1 << 31,
            }),
            0,
        ));

        let markdown = board.to_markdown();
        assert!(markdown.contains("## katsura"), "grouped by family");
        assert!(
            markdown.contains("unsupported: characteristic"),
            "{}",
            markdown
        );
        assert!(
            markdown.contains("| — |"),
            "an absent time renders as an em dash, not a zero"
        );
        assert!(markdown.contains("katsura-8"));
    }

    /// An empty board renders as an empty board rather than as a table of nothing.
    #[test]
    fn test_an_empty_board_says_so() {
        let markdown = CompetitiveBoard::new().to_markdown();
        assert!(markdown.contains("No rows yet"));
        assert!(!markdown.contains("| problem |"));
    }

    /// Two rows built from different source commits are not comparable, so a re-measure after a
    /// change to the engine never ratios the new build against the old one.
    #[test]
    fn test_a_different_commit_is_not_comparable() {
        let before = named_row("p1", "zeebra", answered(64), 100.0);
        let mut after = named_row("p1", "zeebra", answered(64), 50.0);
        after.environment.commit = "cafef00d".to_string();

        assert!(!before.comparable_with(&after), "different source commits");

        // And the board does not pair across them: with one comparand at each commit, only the
        // one sharing the baseline's commit produces a ratio.
        let mut board = CompetitiveBoard::new();
        board.add(before);
        board.add(named_row("p1", "singular", answered(64), 400.0));
        let mut other_commit = named_row("p1", "singular", answered(64), 400.0);
        other_commit.environment.commit = "cafef00d".to_string();
        board.add(other_commit);
        assert_eq!(board.speedups("zeebra").len(), 1);
    }

    /// A ratio against a comparand that is recorded but not authoritative says so in the cell and
    /// is counted apart from the conclusions, so the board cannot be read as if it were one.
    #[test]
    fn test_a_non_authoritative_comparand_is_marked_and_counted() {
        let mut board = CompetitiveBoard::new();
        // Each library needs four answered rows before it has a floor at all, and the compared
        // rows must sit far above it or the floor gate is what marks them instead.
        for problem in ["katsura-4", "katsura-5", "katsura-6", "katsura-7"] {
            board.add(named_row(problem, "zeebra", answered(64), 0.1));
            board.add(named_row(problem, "singular", answered(64), 0.1));
            board.add(named_row(problem, "sagebrush", answered(64), 0.1));
        }
        for problem in ["cyclic-4", "cyclic-5", "cyclic-6", "cyclic-7"] {
            board.add(named_row(problem, "zeebra", answered(64), 5_000.0));
            board.add(named_row(problem, "singular", answered(64), 1_000.0));
            board.add(named_row(problem, "sagebrush", answered(64), 1_000.0));
        }

        let markdown = board.to_markdown();
        assert!(
            markdown.contains("NOT AUTHORITATIVE"),
            "a sagebrush ratio is marked in its own cell\n{}",
            markdown
        );
        assert!(
            markdown.contains("4 against a comparand that is not authoritative"),
            "and counted in the summary\n{}",
            markdown
        );
        assert!(
            !markdown.contains("| singular | 4 | 4 |\n| singular"),
            "the singular rows are untouched"
        );
    }

    /// Two rows taken under different measurement policies are not comparable, so a row measured
    /// one-per-process is never ratioed against one measured many-per-process.
    #[test]
    fn test_a_different_measurement_policy_is_not_comparable() {
        let warm = named_row("p1", "singular", answered(64), 40.0);
        let mut cold = named_row("p1", "singular", answered(64), 40.0);
        cold.environment.policy = "60 s wall, 1 worker, one row per process".to_string();

        assert!(
            warm.comparable_with(&warm.clone()),
            "a row is comparable with itself"
        );
        assert!(
            !warm.comparable_with(&cold),
            "the policy differs, so these are two different measurements"
        );

        // And the board does not pair across the two, which is what doubled its pair count.
        let mut board = CompetitiveBoard::new();
        board.add(named_row("p1", "zeebra", answered(64), 1.0));
        board.add(warm);
        board.add(cold);
        assert_eq!(
            board.speedups("zeebra").len(),
            1,
            "only the row sharing zeebra's policy pairs with it"
        );
    }

    /// The board names the libraries it holds and how many rows each answered, so a short roster
    /// is visible rather than inferred from the table.
    #[test]
    fn test_the_markdown_states_its_roster() {
        let mut board = CompetitiveBoard::new();
        board.add(named_row("p1", "zeebra", answered(64), 1.0));
        board.add(named_row("p1", "singular", answered(64), 40.0));
        board.add(named_row("p2", "zeebra", answered(64), 2.0));
        board.add(named_row(
            "p2",
            "singular",
            RunStatus::Failed(RunFailure::Unavailable {
                binary: "Singular".to_string(),
                reason: "not on PATH".to_string(),
            }),
            0.0,
        ));

        let markdown = board.to_markdown();
        assert!(markdown.contains("## Roster"), "{}", markdown);
        assert!(
            markdown.contains("| zeebra | 2 | 2 |"),
            "zeebra answered both of its rows\n{}",
            markdown
        );
        assert!(
            markdown.contains("| singular | 2 | 1 |"),
            "singular answered one of two\n{}",
            markdown
        );
    }

    /// An engine that was never reachable is counted as a library with zero answers, so a run
    /// that silently lost an engine cannot read as a run that never had it.
    #[test]
    fn test_an_unavailable_engine_is_a_roster_row_with_no_answers() {
        let mut board = CompetitiveBoard::new();
        board.add(named_row("p1", "zeebra", answered(64), 1.0));
        board.add(named_row(
            "p1",
            "msolve",
            RunStatus::Failed(RunFailure::Unavailable {
                binary: "msolve".to_string(),
                reason: "not on PATH".to_string(),
            }),
            0.0,
        ));

        let markdown = board.to_markdown();
        assert!(
            markdown.contains("| msolve | 1 | 0 |"),
            "an unreachable engine is on the roster at zero answers\n{}",
            markdown
        );
    }

    /// The speedup section counts what its own gates excluded, so a reader sees how many ratios
    /// the floor rule and the invariant rule removed rather than only the survivors.
    #[test]
    fn test_the_speedup_summary_counts_its_exclusions() {
        let mut board = CompetitiveBoard::new();
        // Four pairs where the comparand sits on its floor, which is what defines the floor.
        // Distinct first letters at a common length, because `named_row`'s digest perturbation
        // is a function of the name's length and first byte — same-shaped names collide into one
        // problem and the board then cross-compares every pairing of them.
        for problem in ["katsura-4", "katsura-5", "katsura-6", "katsura-7"] {
            board.add(named_row(problem, "zeebra", answered(64), 0.05));
            board.add(named_row(problem, "singular", answered(64), 36.0));
        }
        // One pair far above it, and one inside the noise band.
        board.add(named_row("cyclic-5", "zeebra", answered(64), 29_963.0));
        board.add(named_row("cyclic-5", "singular", answered(64), 7_291.0));
        board.add(named_row("cyclic-6", "zeebra", answered(64), 1_000.0));
        board.add(named_row("cyclic-6", "singular", answered(64), 1_050.0));

        let markdown = board.to_markdown();
        assert!(
            markdown.contains("6 pairs"),
            "every pair is counted\n{}",
            markdown
        );
        assert!(
            markdown.contains("4 disqualified by the startup floor"),
            "the floor exclusions are counted\n{}",
            markdown
        );
        assert!(
            markdown.contains("1 inside the 20% noise band"),
            "a ratio too close to 1 to carry a conclusion is counted\n{}",
            markdown
        );
    }

    /// A malformed row is refused by name rather than silently skipped.
    #[test]
    fn test_a_malformed_row_is_refused_by_name() {
        let history = Json::object([(
            "rows",
            Json::Array(vec![Json::object([("schema", Json::int(1))])]),
        )]);
        match CompetitiveBoard::load(&history) {
            Err(super::BoardError::MalformedRow { field }) => assert_eq!(field, "problem"),
            other => panic!("expected a named malformed field, got {:?}", other),
        }
        assert!(matches!(
            CompetitiveBoard::load(&Json::object([("schema", Json::int(1))])),
            Err(super::BoardError::MalformedRow { field: "rows" })
        ));
    }

    /// Every committed competitive row records a stamp a later reader can still resolve.
    ///
    /// #505: three of the four cohorts in `research/competitive/results/history.json` — 315 of 387
    /// rows, including every five-library figure M27-A is organized around — record branch commits
    /// from PR #435 that did not survive its merge. The letter of #335 was met and its purpose was
    /// not: "re-measure at `7adb29e`" is not an instruction anyone can carry out. A merge base is
    /// an ancestor of `main` and stays one, so `base_commit` plus the delta's `patch_id` is a stamp
    /// that cannot dangle.
    #[test]
    fn test_every_committed_competitive_row_carries_a_resolvable_stamp() {
        let history = Json::parse(include_str!(
            "../../../research/competitive/results/history.json"
        ))
        .expect("committed history.json parses");
        let rows = history.get("rows").expect("a rows array").items();
        assert!(!rows.is_empty(), "the committed history is not empty");

        let unresolvable: Vec<String> = rows
            .iter()
            .filter_map(|row| {
                let environment = super::environment_from_json(row.get("environment")?);
                (!environment.stamp_is_resolvable()).then(|| {
                    format!(
                        "{} at {:?} (base {:?}, patch {:?})",
                        row.get("problem")
                            .and_then(Json::as_str)
                            .unwrap_or("<no problem>"),
                        environment.commit,
                        environment.base_commit,
                        environment.patch_id,
                    )
                })
            })
            .collect();
        assert!(
            unresolvable.is_empty(),
            "{} of {} rows record a commit nothing can resolve: {:?}",
            unresolvable.len(),
            rows.len(),
            &unresolvable[..unresolvable.len().min(4)]
        );
    }

    /// Durations and byte counts render in readable units, and absence renders as an em dash.
    #[test]
    fn test_cells_render_in_readable_units() {
        assert_eq!(duration_cell(None), "—");
        assert_eq!(duration_cell(Some(Duration::from_millis(12))), "12.0 ms");
        assert_eq!(duration_cell(Some(Duration::from_secs(90))), "90.00 s");
        assert_eq!(bytes_cell(None), "—");
        assert_eq!(bytes_cell(Some(512)), "512 B");
        assert_eq!(bytes_cell(Some(2 << 20)), "2.0 MB");
        assert_eq!(bytes_cell(Some(3 << 30)), "3.00 GB");
    }
}
