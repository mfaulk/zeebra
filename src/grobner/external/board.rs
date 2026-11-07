//! The competitive board: one row per (problem, task, library), including the runs that failed.
//!
//! # Why this is not the cryptanalysis scoreboard
//!
//! [`research::Scoreboard`](crate::grobner::research::Scoreboard) answers "which of these ciphers
//! has a verified break, and at what cost". Its identity check is against a registry of *published
//! cryptanalytic problems*, its outcome vocabulary is about witnesses, and its `best.json` and
//! `solved.json` are one-row-per-problem contracts that consumers already depend on. Adding a
//! `library` dimension would silently change what both of those files claim, and `Comparison::of`
//! has no variant for an input a tool cannot represent — which is the distinction this board
//! exists to make. The argument in full is §6 of
//! `docs/research/external-comparison-protocol.md`.
//!
//! What is reused is the set of conventions that make the existing board trustworthy: hand-rolled
//! JSON through [`Json`], a generated Markdown renderer so the human-readable table cannot drift
//! from the data, identity frozen by digest, an append-only history with its contract written into
//! the file, and **unsuccessful runs recorded rather than dropped** — a board that kept only its
//! successes would report each library's best cases as its behaviour.
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
    FieldSpec, Instance, RunReport, RunStatus, Verification,
};
use crate::{
    grobner::research::{Environment, Json},
    MonomialOrder,
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

    /// It failed. **There is no time**, and for two variants it did not even run:
    /// [`RunFailure::Unavailable`] (the tool is absent) and [`RunFailure::Environment`] (the
    /// harness's own environment would have invalidated the measurement). Both render through
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
    /// Problem, task, limits, machine and build. The precondition of a ratio, minus the invariant
    /// agreement, which is checked separately because it is a property of the *answers*.
    pub fn comparable_with(&self, other: &CompetitiveRecord) -> bool {
        self.problem_digest == other.problem_digest
            && self.task == other.task
            && self.limits.comparable_with(&other.limits)
            && self.environment.comparable(&other.environment)
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
/// `research::scoreboard` reads this inline inside `RunRecord::from_json` rather than exposing a
/// reader, so this is the one place the shape is duplicated. Tolerant by design: a missing field
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

    /// Whether this ratio says anything about the **engines** rather than about process startup.
    ///
    /// `false` when **either** operand's wall is within [`Self::FLOOR_MULTIPLE_REQUIRED`] of its
    /// own library's observed startup floor. An unknown floor is treated as acceptable: refusing
    /// on absent evidence would silently drop every row of a library with few measurements.
    pub fn is_engine_comparison(&self) -> bool {
        self.floor_multiple
            .is_none_or(|multiple| multiple >= Self::FLOOR_MULTIPLE_REQUIRED)
    }

    /// Whether this ratio may be published: an engine comparison with a checked invariant.
    ///
    /// The conjunction of the protocol's two gates, so a renderer cannot satisfy one and forget
    /// the other.
    pub fn is_publishable(&self) -> bool {
        self.is_engine_comparison() && self.shared_invariants > 0
    }
}

/// Rows from every library, with the renderers.
#[derive(Clone, Debug, Default)]
pub struct CompetitiveBoard {
    rows: Vec<CompetitiveRecord>,
}

impl CompetitiveBoard {
    /// An empty board.
    pub fn new() -> Self {
        Self::default()
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

            // The counts, before the table. Each gate already marks the rows it excludes, but a
            // marked row is only visible to a reader who tallies the column — and the headline of
            // this board is how *few* of its pairs survive both gates. Stated so the survivors
            // cannot be mistaken for the whole comparison.
            let disqualified = speedups
                .iter()
                .filter(|s| !s.is_engine_comparison())
                .count();
            let unchecked = speedups
                .iter()
                .filter(|s| s.is_engine_comparison() && s.shared_invariants == 0)
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
            let _ = writeln!(
                out,
                "**{} pairs**: {} disqualified by the startup floor, {} with no checked \
                 invariant, {} publishable — of which {} inside the 20% noise band and {} \
                 outside it.\n",
                speedups.len(),
                disqualified,
                unchecked,
                publishable.len(),
                in_band,
                publishable.len() - in_band
            );

            let _ = writeln!(out, "| problem | task | library | ratio | checked |");
            let _ = writeln!(out, "|---|---|---|---:|---|");
            for speedup in &speedups {
                let _ = writeln!(
                    out,
                    "| `{}` | {} | {} | {:.2}x | {} |",
                    speedup.problem,
                    speedup.task,
                    speedup.subject,
                    speedup.ratio,
                    if !speedup.is_engine_comparison() {
                        format!(
                            "**NOT AN ENGINE COMPARISON: an operand is {:.1}x its startup floor**",
                            speedup.floor_multiple.unwrap_or_default()
                        )
                    } else if speedup.shared_invariants == 0 {
                        "**NOT PUBLISHABLE: no invariant was checked**".to_string()
                    } else {
                        format!("{} invariants agreed", speedup.shared_invariants)
                    }
                );
            }
            out.push('\n');
        }

        out
    }
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

#[cfg(test)]
mod tests {
    use super::{
        bytes_cell, duration_cell, CompetitiveBoard, CompetitiveRecord, Outcome,
        COMPETITIVE_HISTORY_CONTRACT,
    };
    use crate::{
        grobner::{
            external::{
                Answer, FieldSpec, Instance, Invariants, LimitStop, Limits, Measurement,
                RunFailure, RunReport, RunStatus, Task, ToolVersion, Unsupported, Verification,
            },
            research::{Environment, Json},
        },
        MonomialOrder,
    };
    use std::time::Duration;

    fn environment() -> Environment {
        Environment {
            commit: "deadbeef".to_string(),
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
        for (name, zeebra_ms, singular_ms) in [
            ("a", 0.08, 36.01),
            ("b", 0.14, 36.04),
            ("c", 0.58, 36.05),
            ("d", 0.55, 36.08),
            ("e", 29963.0, 7290.0),
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
        assert_eq!(real[0].problem, "e");
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
        for problem in ["a-1", "b-1", "c-1", "d-1"] {
            board.add(named_row(problem, "zeebra", answered(64), 0.05));
            board.add(named_row(problem, "singular", answered(64), 36.0));
        }
        // One pair far above it, and one inside the noise band.
        board.add(named_row("e-1", "zeebra", answered(64), 29_963.0));
        board.add(named_row("e-1", "singular", answered(64), 7_291.0));
        board.add(named_row("f-1", "zeebra", answered(64), 1_000.0));
        board.add(named_row("f-1", "singular", answered(64), 1_050.0));

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
