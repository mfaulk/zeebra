//! The machine-readable record of one experiment, serialized through [`Json`].
//!
//! # What a record is, and is not
//!
//! A record pairs an instance's **identity** with what *this machine* measured about it. The
//! identity side is an [`InstanceManifest`], which carries no measurements at all — so an instance does not change when a different workstation runs it, and
//! two records over the same manifest are comparable by construction.

mod environment;
mod manifest;

use std::time::Duration;

use crate::{
    grobner::{Attempt, OutcomeClass, SolvePlan},
    util::Json,
};

pub use environment::Environment;
pub use manifest::{Claim, InstanceManifest, Provenance};

/// One route the planner ran, as a record.
///
/// The detail an aggregate cannot carry. A two-attempt solve that reports only "two attempts,
/// 10.3 ms, four batches" does not say which route opened, why the second one happened, which
/// limit the first one reached, or how the cost split — and those are the questions a strategy
/// comparison exists to answer.
#[derive(Clone, Debug)]
pub struct AttemptRecord {
    /// Which route, e.g. `"GrevlexF4ThenFglm"`.
    pub strategy: String,

    /// Why the planner picked it, in its own words.
    pub reason: String,

    /// What it established, if anything.
    pub outcome: Option<OutcomeClass>,

    /// Why it did not, if it did not.
    pub failure: Option<String>,

    /// Wall clock for this attempt alone.
    pub elapsed: Duration,

    /// F4's figures, when a Gröbner stage ran. `(batches, rows, columns, peak entries, peak
    /// bytes)`.
    pub f4: Option<(usize, usize, usize, usize, usize)>,

    /// The conversion's figures, when it ran. `(quotient dimension, estimated bytes)`.
    pub fglm: Option<(usize, usize)>,
}

impl AttemptRecord {
    /// Read one attempt out of a plan.
    pub fn of(attempt: &Attempt) -> Self {
        Self {
            strategy: format!("{:?}", attempt.strategy),
            reason: attempt.choice.to_string(),
            outcome: attempt.result.as_ref().ok().copied(),
            failure: attempt.result.as_ref().err().map(|e| e.to_string()),
            elapsed: attempt.elapsed,
            f4: attempt.statistics.f4.as_ref().map(|f| {
                (
                    f.batches,
                    f.max_matrix_rows,
                    f.max_matrix_columns,
                    f.max_live_nonzeros,
                    f.peak_live_bytes(),
                )
            }),
            fglm: attempt
                .statistics
                .fglm
                .as_ref()
                .map(|c| (c.quotient_dimension, c.estimated_bytes())),
        }
    }

    /// The attempt as JSON.
    pub fn to_json(&self) -> Json {
        let mut fields = vec![
            ("strategy", Json::string(&self.strategy)),
            ("reason", Json::string(&self.reason)),
            (
                "outcome",
                match self.outcome {
                    Some(class) => Json::string(outcome_name(class)),
                    None => Json::Null,
                },
            ),
            (
                "failure",
                match &self.failure {
                    Some(f) => Json::string(f),
                    None => Json::Null,
                },
            ),
            ("elapsed_nanos", Json::nanos(self.elapsed)),
        ];
        fields.push((
            "grobner",
            match self.f4 {
                Some((batches, rows, columns, entries, bytes)) => Json::object([
                    ("batches", Json::size(batches)),
                    ("max_matrix_rows", Json::size(rows)),
                    ("max_matrix_columns", Json::size(columns)),
                    ("peak_live_entries", Json::size(entries)),
                    ("estimated_peak_bytes", Json::size(bytes)),
                ]),
                None => Json::Null,
            },
        ));
        fields.push((
            "conversion",
            match self.fglm {
                Some((dimension, bytes)) => Json::object([
                    ("quotient_dimension", Json::size(dimension)),
                    ("estimated_bytes", Json::size(bytes)),
                ]),
                None => Json::Null,
            },
        ));
        Json::object(fields)
    }
}

/// The stable name of an outcome class.
///
/// Separate from `Debug`, which may be reformatted by a compiler release. A consumer keys on
/// these, so they are part of the schema.
fn outcome_name(class: OutcomeClass) -> &'static str {
    match class {
        OutcomeClass::Point => "point",
        OutcomeClass::NoBaseFieldPoint => "no_base_field_point",
        OutcomeClass::Inconsistent => "inconsistent",
    }
}

/// What one experiment did, as a record.
///
/// The measurement side. Pair it with an [`InstanceManifest`] by
/// [`Self::instance`] and [`Self::manifest_sha256`] — the name alone is for humans, and a name is
/// not a reference.
#[derive(Clone, Debug)]
pub struct ExperimentRecord {
    /// Schema version, so a stored record survives a change of shape.
    pub schema: u32,

    /// The instance's identifier, matching its manifest's.
    ///
    /// Human-readable, and therefore not a reference: see [`Self::manifest_sha256`].
    pub instance: String,

    /// The SHA-256 the instance's manifest pins, if there is one.
    ///
    /// **A stable reference to the bytes a result was computed against**, which the name cannot
    /// be: two runs can agree on `"fukuoka-mq-III-n10-seed0"` and disagree on what that file is.
    /// `None` for a system this crate generates rather than imports, where the manifest's
    /// construction parameters are the identity instead.
    pub manifest_sha256: Option<String>,

    /// What was asked of the solver — a policy name, a strategy name.
    pub configuration: String,

    /// What happened, as a class rather than a point.
    pub outcome: Option<OutcomeClass>,

    /// Why nothing happened, if nothing did.
    pub failure: Option<String>,

    /// Whether the result was verified **independently of the solver**.
    ///
    /// Three states, not two. `None` means no independent verification applies — there was no
    /// answer to verify. `Some(false)` means there was one and it failed, which is a defect, not
    /// an absence.
    pub verified: Option<bool>,

    /// How the verification was done, in words.
    pub verification: String,

    /// Transformations applied before solving: a specialization, a reduction.
    pub transformations: Vec<String>,

    /// Wall clock across every attempt, discarded work included.
    pub elapsed: Duration,

    /// Of that, time on attempts that established nothing.
    pub discarded: Duration,

    /// Routes attempted, in order, with what each one cost.
    ///
    /// The aggregate fields below are sums and maxima over these. Carried because a two-attempt
    /// solve reported only as "two attempts" does not say which route opened, why the second
    /// happened, or how the cost split — and understanding which strategy worked and why is the
    /// point of the exercise.
    pub attempts: Vec<AttemptRecord>,

    /// F4 batches summed across attempts.
    pub batches: usize,

    /// The largest single-stage byte **estimate**. Not a measurement of the process.
    pub estimated_peak_bytes: usize,

    /// Measured process peak RSS, if the platform reports it.
    ///
    /// Separate from the estimate, and the two differ by 4.1x on katsura-7. Conflating them is the
    /// error §1.2 of the milestone document exists to prevent.
    pub peak_resident_bytes: Option<u64>,

    /// How to reproduce this exact run.
    pub reproduce: String,
}

impl ExperimentRecord {
    /// The current schema version.
    pub const SCHEMA: u32 = 1;

    /// An empty record for `instance` under `configuration`.
    pub fn new(instance: impl Into<String>, configuration: impl Into<String>) -> Self {
        Self {
            schema: Self::SCHEMA,
            instance: instance.into(),
            configuration: configuration.into(),
            manifest_sha256: None,
            outcome: None,
            failure: None,
            verified: None,
            verification: String::new(),
            transformations: Vec::new(),
            elapsed: Duration::ZERO,
            discarded: Duration::ZERO,
            attempts: Vec::new(),
            batches: 0,
            estimated_peak_bytes: 0,
            peak_resident_bytes: None,
            reproduce: String::new(),
        }
    }

    /// Fill in the cost and attempt fields from a plan.
    ///
    /// Keeps the per-attempt detail rather than only its aggregates — an earlier version took the
    /// sums and dropped the plan, which left a reader unable to say which route worked or why.
    pub fn with_plan(mut self, plan: &SolvePlan) -> Self {
        self.elapsed = plan.total_elapsed();
        self.discarded = plan.discarded_elapsed();
        self.attempts = plan.attempts.iter().map(AttemptRecord::of).collect();
        self.batches = plan.total_batches();
        self.estimated_peak_bytes = plan.peak_estimated_bytes();
        self
    }

    /// Reference the manifest whose checksum pins this instance's bytes.
    pub fn with_manifest_sha256(mut self, sha256: impl Into<String>) -> Self {
        self.manifest_sha256 = Some(sha256.into());
        self
    }

    /// The record as JSON.
    ///
    /// `measured_peak_resident_bytes` is **omitted** when there is no measurement, rather than
    /// emitted as `null`. `RunRecord` already omitted it, and two records of the same quantity
    /// encoding absence two ways is how a consumer acquires a special case per type. `null` is
    /// also the worse of the two: it invites being coerced to zero, and "not measured" is not
    /// zero bytes.
    pub fn to_json(&self) -> Json {
        let mut fields = vec![
            ("schema", Json::int(self.schema)),
            ("instance", Json::string(&self.instance)),
            (
                "manifest_sha256",
                match &self.manifest_sha256 {
                    Some(h) => Json::string(h),
                    None => Json::Null,
                },
            ),
            ("configuration", Json::string(&self.configuration)),
            (
                "outcome",
                match self.outcome {
                    Some(class) => Json::string(outcome_name(class)),
                    None => Json::Null,
                },
            ),
            (
                "failure",
                match &self.failure {
                    Some(f) => Json::string(f),
                    None => Json::Null,
                },
            ),
            (
                "verified",
                match self.verified {
                    Some(v) => Json::Bool(v),
                    None => Json::Null,
                },
            ),
            ("verification", Json::string(&self.verification)),
            (
                "transformations",
                Json::Array(self.transformations.iter().map(Json::string).collect()),
            ),
            ("elapsed_nanos", Json::nanos(self.elapsed)),
            ("discarded_nanos", Json::nanos(self.discarded)),
            ("attempt_count", Json::size(self.attempts.len())),
            (
                "attempts",
                Json::Array(self.attempts.iter().map(AttemptRecord::to_json).collect()),
            ),
            ("batches", Json::size(self.batches)),
            // Named `estimated_` so a consumer cannot mistake it for the measured figure beside it.
            (
                "estimated_peak_bytes",
                Json::size(self.estimated_peak_bytes),
            ),
        ];
        if let Some(bytes) = self.peak_resident_bytes {
            fields.push(("measured_peak_resident_bytes", Json::int(bytes)));
        }
        fields.push(("reproduce", Json::string(&self.reproduce)));
        Json::object(fields)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::{AttemptRecord, ExperimentRecord};
    use crate::{grobner::OutcomeClass, util::Json};

    /// An absent measured peak omits the key rather than emitting `null`.
    ///
    /// Unified with `RunRecord`, which already omitted it. Two records of the same quantity
    /// encoding absence two ways is how a consumer ends up with a special case per type; and
    /// `null` for "not measured" invites being read as a zero by anything that coerces.
    #[test]
    fn test_an_absent_measured_peak_omits_its_key() {
        let record = ExperimentRecord::new("katsura-7", "baseline");
        assert_eq!(record.peak_resident_bytes, None);

        let text = record.to_json().to_json();
        assert!(
            !text.contains("measured_peak_resident_bytes"),
            "an absent measurement must be omitted, not null: {}",
            text
        );
        // The estimate is unconditional and stays, so a reader can still tell the two apart.
        assert!(text.contains("estimated_peak_bytes"));

        let parsed = Json::parse(&text).expect("the record this type wrote");
        assert!(parsed.get("measured_peak_resident_bytes").is_none());
    }

    /// A present measured peak is emitted as an integer and parses back to the same value.
    #[test]
    fn test_a_present_measured_peak_round_trips_as_an_integer() {
        let mut record = ExperimentRecord::new("katsura-7", "baseline");
        record.estimated_peak_bytes = 195_000_000;
        record.peak_resident_bytes = Some(14_750_000_000);

        let text = record.to_json().to_json();
        let parsed = Json::parse(&text).expect("the record this type wrote");
        assert_eq!(
            parsed
                .get("measured_peak_resident_bytes")
                .and_then(Json::as_int),
            Some(14_750_000_000)
        );
        assert_eq!(
            parsed.get("estimated_peak_bytes").and_then(Json::as_int),
            Some(195_000_000),
            "the estimate sits beside the measurement so the ratio is recoverable"
        );
    }

    /// A record names its outcome, and distinguishes the three absences.
    #[test]
    fn test_a_record_distinguishes_its_absences() {
        // No answer and no verification: both null, and they mean different things.
        let empty = ExperimentRecord::new("i", "c");
        let text = empty.to_json().to_json();
        assert!(text.contains("\"outcome\": null"), "{}", text);
        assert!(text.contains("\"verified\": null"), "{}", text);
        assert!(text.contains("\"failure\": null"), "{}", text);

        // An answer that failed verification is `false`, not absent — a defect, not a gap.
        let mut failed = ExperimentRecord::new("i", "c");
        failed.outcome = Some(OutcomeClass::Point);
        failed.verified = Some(false);
        let text = failed.to_json().to_json();
        assert!(text.contains("\"outcome\": \"point\""), "{}", text);
        assert!(text.contains("\"verified\": false"), "{}", text);

        // Each outcome class has its own name.
        for (class, name) in [
            (OutcomeClass::Point, "point"),
            (OutcomeClass::NoBaseFieldPoint, "no_base_field_point"),
            (OutcomeClass::Inconsistent, "inconsistent"),
        ] {
            let mut record = ExperimentRecord::new("i", "c");
            record.outcome = Some(class);
            assert!(
                record.to_json().to_json().contains(name),
                "{:?} should serialize as {}",
                class,
                name
            );
        }
    }

    /// Estimated and measured memory are separate keys, and the estimate says so in its name.
    ///
    /// The two differ by 4.1x on katsura-7. A record with one `peak_bytes` key would invite
    /// exactly the conflation the milestone document's §1.2 exists to prevent.
    #[test]
    fn test_estimated_and_measured_memory_are_distinct_keys() {
        let mut record = ExperimentRecord::new("i", "c");
        record.estimated_peak_bytes = 320_000_000;
        record.peak_resident_bytes = Some(1_303_000_000);
        let text = record.to_json().to_json();

        assert!(
            text.contains("\"estimated_peak_bytes\": 320000000"),
            "{}",
            text
        );
        assert!(
            text.contains("\"measured_peak_resident_bytes\": 1303000000"),
            "{}",
            text
        );
        assert!(
            !text.contains("\"peak_bytes\""),
            "there must be no ambiguous key: {}",
            text
        );
    }

    /// A two-attempt plan is reconstructible from the record alone.
    ///
    /// The gap a reviewer found: the record kept the aggregates and dropped the plan, so a
    /// two-attempt solve reported "two attempts, N ms, M batches" and nothing about which route
    /// opened, why the second happened, or how the cost split. Understanding which strategy
    /// worked and why is the point of the exercise, so the detail is now in the JSON.
    #[test]
    fn test_a_two_attempt_plan_is_reconstructible_from_the_record() {
        use rand::{prelude::StdRng, SeedableRng};

        use crate::{
            fields::Zp2147483647,
            grobner::{
                benchmark_systems::planted, solve_one_planned, PlannedSolveOptions, SolvePolicy,
            },
            FiniteField,
        };

        // planted-12 is the two-attempt case: the conversion is ruled out from a counted D and
        // direct lex finishes.
        type F = Zp2147483647;
        let point: Vec<F> = (0..12).map(|i| F::new(2 * i as u64 + 3)).collect();
        let (_, plan) = solve_one_planned(
            &planted::<12, F>(&point),
            &mut StdRng::seed_from_u64(1),
            &PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback),
        );
        assert_eq!(plan.attempts.len(), 2, "planted-12 should need a fallback");

        let record = ExperimentRecord::new("planted-12", "AutoWithFallback").with_plan(&plan);
        assert_eq!(record.attempts.len(), 2);

        // Which route opened, and why.
        assert_eq!(record.attempts[0].strategy, "GrevlexF4ThenFglm");
        assert!(record.attempts[0].reason.contains("conservative policy"));
        // Why the second happened — the reason names the counted dimension.
        assert_eq!(record.attempts[1].strategy, "DirectLexF4");
        assert!(
            record.attempts[1].reason.contains("counted D = 4096"),
            "{}",
            record.attempts[1].reason
        );
        // Which limit the first reached, and that the second succeeded.
        assert!(record.attempts[0].failure.is_some());
        assert_eq!(record.attempts[0].outcome, None);
        assert_eq!(record.attempts[1].outcome, Some(OutcomeClass::Point));
        assert_eq!(record.attempts[1].failure, None);
        // And how the cost split, which the aggregate cannot say.
        assert!(record.attempts[0].f4.is_some());
        assert!(record.attempts[1].f4.is_some());
        assert_eq!(
            record.attempts.iter().map(|a| a.elapsed).sum::<Duration>(),
            record.elapsed
        );

        // The JSON carries all of it, and the aggregate beside it.
        let text = record.to_json().to_json();
        assert!(text.contains("\"attempt_count\": 2"), "{}", text);
        assert!(
            text.contains("\"strategy\": \"GrevlexF4ThenFglm\""),
            "{}",
            text
        );
        assert!(text.contains("\"strategy\": \"DirectLexF4\""), "{}", text);
        assert!(text.contains("\"max_matrix_columns\""), "{}", text);

        // And a detail the aggregate actively obscures: **no conversion ran**. The planner ruled
        // it out from a counted `D` before building an operator column, so `conversion` is null on
        // both attempts and the dimension appears only in the reason. A record that reported a
        // quotient dimension here would claim a cost that was never paid.
        assert!(record.attempts.iter().all(|a| a.fglm.is_none()));
        assert_eq!(text.matches("\"conversion\": null").count(), 2, "{}", text);
        assert!(!text.contains("\"quotient_dimension\""), "{}", text);
    }

    /// An attempt that reached no Gröbner stage says so with `null`, not with zeros.
    #[test]
    fn test_an_attempt_without_a_grobner_stage_is_null_not_zero() {
        let attempt = AttemptRecord {
            strategy: "DirectLexF4".to_string(),
            reason: "the caller asked for it".to_string(),
            outcome: None,
            failure: Some("the options are unsatisfiable".to_string()),
            elapsed: Duration::from_nanos(7),
            f4: None,
            fglm: None,
        };
        let text = attempt.to_json().to_json();
        assert!(text.contains("\"grobner\": null"), "{}", text);
        assert!(text.contains("\"conversion\": null"), "{}", text);
        // Zeros would read as "it ran and did nothing", which is a different fact.
        assert!(!text.contains("\"batches\": 0"), "{}", text);
    }

    /// The manifest reference is a checksum, not a name.
    ///
    /// Two runs can agree on `"fukuoka-mq-III-n10-seed0"` and disagree on what that file is, so a
    /// result that identified its instance only by name would not be reproducible.
    #[test]
    fn test_the_manifest_is_referenced_by_checksum() {
        let record = ExperimentRecord::new("fukuoka-mq-III-n10-seed0", "AutoWithFallback")
            .with_manifest_sha256(
                "9436e45dbd4247f152681e954f1db19d92e8cf5e76b2bc35530bed74aae522ba",
            );
        let text = record.to_json().to_json();
        assert!(text.contains("\"manifest_sha256\": \"9436e45d"), "{}", text);

        // Absent for a generated system, where the manifest's parameters are the identity.
        let generated = ExperimentRecord::new("katsura-7", "AutoWithFallback");
        assert!(generated
            .to_json()
            .to_json()
            .contains("\"manifest_sha256\": null"));
    }

    /// The same record always serializes to the same bytes.
    #[test]
    fn test_serialization_is_deterministic() {
        let mut record = ExperimentRecord::new("katsura-7", "AutoWithFallback");
        record.outcome = Some(OutcomeClass::Point);
        record.verified = Some(true);
        record.transformations = vec!["none".to_string()];
        record.elapsed = Duration::from_millis(47);
        assert_eq!(record.to_json().to_json(), record.to_json().to_json());
        // And it parses as an object with the schema first.
        let text = record.to_json().to_json();
        assert!(text.starts_with("{\n  \"schema\": 1,"), "{}", text);
    }
}
