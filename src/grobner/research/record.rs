//! The machine-readable record of one experiment, and a JSON writer that needs no dependency.
//!
//! # Why hand-written JSON
//!
//! `serde` is already a dependency and `serde_json` is not. Pulling one in for a few hundred bytes
//! of output would be the wrong trade for this crate — the measurement in
//! `docs/MILESTONE-LARGE-PRIME-FIELDS.md` §4.4 was that the shipped dependency count did not move
//! when the wide fields were implemented rather than adapted, and this is the same choice at a
//! much smaller scale. [`Json`] is about eighty lines, emits exactly the subset these records need,
//! and escapes strings to RFC 8259.
//!
//! What it deliberately does **not** do: floats. Every number here is an integer — nanoseconds,
//! bytes, counts — because a float in a record is a reproducibility problem (formatting differs,
//! `0.1` does not round-trip) and nothing here needs one. A duration is nanoseconds; a ratio is
//! two integers.
//!
//! # What a record is, and is not
//!
//! A record pairs an instance's **identity** with what *this machine* measured about it. The
//! identity side is an [`InstanceManifest`](super::InstanceManifest), which carries no
//! measurements at all — so an instance does not change when a different workstation runs it, and
//! two records over the same manifest are comparable by construction.

use std::{fmt::Write as _, time::Duration};

use crate::grobner::{Attempt, OutcomeClass, SolvePlan};

/// A JSON value, restricted to what an experiment record needs.
///
/// No floats, by design — see the module docs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Json {
    /// `null`.
    Null,
    /// `true` or `false`.
    Bool(bool),
    /// An integer. Signed, so a difference can be recorded.
    Int(i128),
    /// A string, escaped on output.
    Str(String),
    /// An array.
    Array(Vec<Json>),
    /// An object. **Insertion order is preserved**, because a record that reordered its keys
    /// between runs would make a textual diff useless.
    Object(Vec<(String, Json)>),
}

impl Json {
    /// A string value.
    pub fn string(s: impl Into<String>) -> Self {
        Self::Str(s.into())
    }

    /// An integer value from anything that converts.
    pub fn int(n: impl Into<i128>) -> Self {
        Self::Int(n.into())
    }

    /// A `usize`, which does not implement `Into<i128>`.
    pub fn size(n: usize) -> Self {
        Self::Int(n as i128)
    }

    /// A duration, as whole nanoseconds.
    ///
    /// Nanoseconds rather than fractional milliseconds: an integer round-trips and a float does
    /// not, and a consumer that wants milliseconds can divide.
    pub fn nanos(d: Duration) -> Self {
        Self::Int(d.as_nanos() as i128)
    }

    /// An object from pairs, preserving order.
    pub fn object<K: Into<String>>(fields: impl IntoIterator<Item = (K, Json)>) -> Self {
        Self::Object(fields.into_iter().map(|(k, v)| (k.into(), v)).collect())
    }

    /// Serialize, with two-space indentation.
    ///
    /// Deterministic: the same value always produces the same bytes, which is what makes a record
    /// diffable across runs.
    pub fn to_json(&self) -> String {
        let mut out = String::new();
        self.write(&mut out, 0);
        out
    }

    fn write(&self, out: &mut String, depth: usize) {
        let pad = |out: &mut String, depth: usize| {
            for _ in 0..depth {
                out.push_str("  ");
            }
        };
        match self {
            Self::Null => out.push_str("null"),
            Self::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Self::Int(n) => {
                let _ = write!(out, "{}", n);
            }
            Self::Str(s) => Self::write_string(out, s),
            Self::Array(items) if items.is_empty() => out.push_str("[]"),
            Self::Array(items) => {
                out.push_str("[\n");
                for (index, item) in items.iter().enumerate() {
                    pad(out, depth + 1);
                    item.write(out, depth + 1);
                    if index + 1 < items.len() {
                        out.push(',');
                    }
                    out.push('\n');
                }
                pad(out, depth);
                out.push(']');
            }
            Self::Object(fields) if fields.is_empty() => out.push_str("{}"),
            Self::Object(fields) => {
                out.push_str("{\n");
                for (index, (key, value)) in fields.iter().enumerate() {
                    pad(out, depth + 1);
                    Self::write_string(out, key);
                    out.push_str(": ");
                    value.write(out, depth + 1);
                    if index + 1 < fields.len() {
                        out.push(',');
                    }
                    out.push('\n');
                }
                pad(out, depth);
                out.push('}');
            }
        }
    }

    /// A JSON string literal, escaped per RFC 8259 §7.
    fn write_string(out: &mut String, s: &str) {
        out.push('"');
        for c in s.chars() {
            match c {
                '"' => out.push_str("\\\""),
                '\\' => out.push_str("\\\\"),
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\t' => out.push_str("\\t"),
                '\u{08}' => out.push_str("\\b"),
                '\u{0c}' => out.push_str("\\f"),
                // Every other control character must be escaped; everything else, including
                // non-ASCII, is passed through as UTF-8, which RFC 8259 permits.
                c if (c as u32) < 0x20 => {
                    let _ = write!(out, "\\u{:04x}", c as u32);
                }
                c => out.push(c),
            }
        }
        out.push('"');
    }
}

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
/// The measurement side. Pair it with an [`InstanceManifest`](super::InstanceManifest) by
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
    pub fn to_json(&self) -> Json {
        Json::object([
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
            (
                "measured_peak_resident_bytes",
                match self.peak_resident_bytes {
                    Some(b) => Json::int(b),
                    None => Json::Null,
                },
            ),
            ("reproduce", Json::string(&self.reproduce)),
        ])
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::{AttemptRecord, ExperimentRecord, Json};
    use crate::grobner::OutcomeClass;

    /// Scalars and containers serialize to the forms a consumer expects.
    #[test]
    fn test_scalars_and_containers() {
        assert_eq!(Json::Null.to_json(), "null");
        assert_eq!(Json::Bool(true).to_json(), "true");
        assert_eq!(Json::Bool(false).to_json(), "false");
        assert_eq!(Json::int(-17i32).to_json(), "-17");
        assert_eq!(Json::size(0).to_json(), "0");
        assert_eq!(Json::string("hi").to_json(), "\"hi\"");
        // Empty containers stay on one line; nonempty ones indent.
        assert_eq!(Json::Array(vec![]).to_json(), "[]");
        assert_eq!(Json::Object(vec![]).to_json(), "{}");
        assert_eq!(
            Json::Array(vec![Json::int(1i32), Json::int(2i32)]).to_json(),
            "[\n  1,\n  2\n]"
        );
    }

    /// Object key order is preserved, so a record diffs cleanly between runs.
    #[test]
    fn test_object_order_is_insertion_order() {
        let value = Json::object([
            ("zebra", Json::int(1i32)),
            ("apple", Json::int(2i32)),
            ("mango", Json::int(3i32)),
        ]);
        let text = value.to_json();
        let z = text.find("zebra").expect("present");
        let a = text.find("apple").expect("present");
        let m = text.find("mango").expect("present");
        assert!(z < a && a < m, "keys were reordered: {}", text);
    }

    /// Strings are escaped per RFC 8259, control characters included.
    #[test]
    fn test_string_escaping() {
        assert_eq!(
            Json::string("a\"b\\c").to_json(),
            r#""a\"b\\c""#,
            "quotes and backslashes"
        );
        assert_eq!(Json::string("a\nb\tc\rd").to_json(), r#""a\nb\tc\rd""#);
        assert_eq!(Json::string("\u{08}\u{0c}").to_json(), r#""\b\f""#);
        // Other control characters take the \u form, which is the case a naive writer gets
        // wrong: a raw control byte inside a JSON string is invalid, not merely ugly.
        assert_eq!(Json::string("\u{01}").to_json(), "\"\\u0001\"");
        assert_eq!(Json::string("\u{1f}").to_json(), "\"\\u001f\"");
        // Non-ASCII passes through as UTF-8, which RFC 8259 permits.
        assert_eq!(Json::string("Gröbner").to_json(), "\"Gröbner\"");
    }

    /// Nesting indents by depth and closes in the right order.
    #[test]
    fn test_nesting() {
        let value = Json::object([(
            "outer",
            Json::Array(vec![Json::object([("inner", Json::int(1i32))])]),
        )]);
        assert_eq!(
            value.to_json(),
            "{\n  \"outer\": [\n    {\n      \"inner\": 1\n    }\n  ]\n}"
        );
    }

    /// Durations are whole nanoseconds, so they round-trip exactly.
    ///
    /// The reason there is no float in this module: `0.1` does not round-trip through a decimal
    /// literal, and a record whose numbers change between formatters is not a record.
    #[test]
    fn test_durations_are_integer_nanoseconds() {
        assert_eq!(Json::nanos(Duration::ZERO).to_json(), "0");
        assert_eq!(Json::nanos(Duration::from_nanos(1)).to_json(), "1");
        assert_eq!(
            Json::nanos(Duration::from_micros(1_500)).to_json(),
            "1500000"
        );
        // A figure a float would mangle.
        assert_eq!(
            Json::nanos(Duration::new(28, 253_900_001)).to_json(),
            "28253900001"
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
