//! A pinned subprocess F4 whose complete reduced basis must agree with an independent solver.
use super::{
    contract::{generators_agree, order_tag},
    process::{Invocation, Supervisor},
    Answer, ExternalSolver, Instance, Invariants, LimitStop, Limits, Measurement, RunFailure,
    RunReport, RunStatus, Support, Task, ToolVersion, Unsupported, Verification, ZeebraSolver,
};
use crate::{util::Json, MonomialOrder};
use std::{
    path::PathBuf,
    time::{Duration, Instant},
};
pub const PINNED_REVISION: &str = "c3e1d630fba9b2155a4c389d9022f13e0ba09218";
/// Two-variable arithmetic control with the known root (-1, 2), outside the public ladder.
/// Only these two wide primes are registered for the focused comparison.
pub fn wide_control(modulus: u64) -> Option<Instance> {
    matches!(
        modulus,
        18_446_744_073_709_551_263 | 18_446_744_073_709_551_557
    )
    .then(|| {
        Instance::new(
            "groebner-rs-wide-control",
            "wide-prime-control",
            super::FieldSpec::prime(modulus),
            vec!["x1".into(), "x2".into()],
            vec!["x1^2+2*x1*x2+x2^2-1".into(), "x2^2-4".into()],
            MonomialOrder::GradedReverseLexicographic,
        )
    })
}
/// Provenance for the focused control; generator echoes and complete independent bases are checked.
pub fn control_entry() -> super::corpus::CorpusEntry {
    super::corpus::CorpusEntry {
        name: "groebner-rs-wide-control",
        family: "wide-prime-control",
        rung: super::corpus::Rung::Easy,
        zero_dimensional: true,
        quotient_dimension: Some(4),
        equivalence: super::corpus::Equivalence::KnownSolution,
        digests: &[
            (
                18_446_744_073_709_551_263,
                "bcb2faeded9a39f5c5b6ab7228686322b2ca9630aef5d415d42fe20628d9109e",
            ),
            (
                18_446_744_073_709_551_557,
                "9eb66aa124dfe244730678f4f78ebfabc169c5bed05fd12b90f7dffd88d77444",
            ),
        ],
    }
}
fn invalid(detail: impl Into<String>) -> RunFailure {
    RunFailure::SelfInconsistent {
        detail: detail.into(),
    }
}
fn number(json: &Json, key: &str) -> Result<u64, RunFailure> {
    json.get(key)
        .and_then(Json::as_int)
        .and_then(|n| u64::try_from(n).ok())
        .ok_or_else(|| invalid(format!("missing or invalid integer {key}")))
}
fn text<'a>(json: &'a Json, key: &str) -> Result<&'a str, RunFailure> {
    json.get(key)
        .and_then(Json::as_str)
        .ok_or_else(|| invalid(format!("missing string {key}")))
}
fn strings(json: &Json, key: &str) -> Result<Vec<String>, RunFailure> {
    let Some(Json::Array(values)) = json.get(key) else {
        return Err(invalid(format!("missing array {key}")));
    };
    values
        .iter()
        .map(|v| {
            v.as_str()
                .map(str::to_owned)
                .ok_or_else(|| invalid(format!("invalid string in {key}")))
        })
        .collect()
}
fn identity(json: &Json) -> Result<String, RunFailure> {
    if number(json, "contract")? != 1 || text(json, "revision")? != PINNED_REVISION {
        return Err(invalid("unrecognized driver contract or upstream revision"));
    }
    if text(json, "isa")? != "x86-64-v3" {
        return Err(invalid(
            "driver must be built for the matched x86-64-v3 ISA",
        ));
    }
    let metadata = text(json, "build_metadata")?;
    if !metadata.contains("PROFILE=release;")
        || !metadata.contains("OPT_LEVEL=3;")
        || !metadata.contains("CARGO_PROFILE_RELEASE_LTO=fat;")
        || !metadata.contains("CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1;")
    {
        return Err(invalid("driver must use the pinned release profile"));
    }
    let build = text(json, "build")?;
    if build.is_empty() {
        return Err(invalid("missing binary build identity"));
    }
    Ok(format!(
        "{PINNED_REVISION};isa=x86-64-v3;parallel;allocator=system;{build}"
    ))
}
fn parse_answer(
    json: &Json,
    instance: &Instance,
    workers: usize,
) -> Result<(Answer, Vec<(String, Duration)>), RunFailure> {
    identity(json)?;
    if number(json, "modulus")? != instance.field.characteristic
        || strings(json, "variables")? != instance.variables
        || text(json, "order")? != order_tag(instance.order)
        || number(json, "workers")? != workers as u64
    {
        return Err(invalid(
            "engine ring or actual worker count differs from the request",
        ));
    }
    generators_agree(
        &instance.system,
        &strings(json, "generators")?,
        instance.field.characteristic,
    )
    .map_err(|_| invalid("engine parsed a different generator system"))?;
    let basis = strings(json, "basis")?;
    let leading = strings(json, "leading")?;
    if basis.len() != leading.len() {
        return Err(invalid("basis and leading-monomial counts differ"));
    }
    let mut stages = Vec::new();
    for (key, label) in [
        ("parse_ns", "parse"),
        ("solve_ns", "solve"),
        ("serialization_ns", "serialization"),
    ] {
        stages.push((label.into(), Duration::from_nanos(number(json, key)?)));
    }
    Ok((
        Answer::from_invariants(Invariants::none().with_leading_monomials(leading))
            .with_basis(basis),
        stages,
    ))
}
fn verify_basis(
    mut answer: Answer,
    trusted: &Answer,
    modulus: u64,
) -> Result<RunStatus, RunFailure> {
    let (Some(basis), Some(reference)) = (&answer.basis, &trusted.basis) else {
        return Err(invalid(
            "missing full reduced basis for independent verification",
        ));
    };
    generators_agree(reference, basis, modulus)
        .map_err(|_| invalid("full reduced basis disagrees with independent Zeebra computation"))?;
    let verification = Verification::of("zeebra", &answer.invariants, &trusted.invariants)
        .map_err(|_| invalid("reported leading monomials disagree with the trusted basis"))?
        .with_note("full monic reduced basis agrees coefficient for coefficient; quotient dimension inferred from the matched trusted basis; verification excluded from child solve time");
    answer.invariants = trusted.invariants.clone();
    Ok(RunStatus::Verified(answer, verification))
}
/// A standalone, locked sdiehl/groebner F4 driver; every retained answer is independently checked.
#[derive(Debug, Clone)]
pub struct GroebnerRsSolver {
    binary: String,
    work_dir: PathBuf,
    runs: u64,
    version: Option<ToolVersion>,
}
impl GroebnerRsSolver {
    /// Create scratch storage; a missing executable is reported by the probe or run.
    /// # Errors
    /// Returns a harness failure if the scratch directory cannot be created.
    pub fn new(
        binary: impl Into<String>,
        work_dir: impl Into<PathBuf>,
    ) -> Result<Self, RunFailure> {
        let work_dir = work_dir.into();
        std::fs::create_dir_all(&work_dir)?;
        Ok(Self {
            binary: binary.into(),
            work_dir,
            runs: 0,
            version: None,
        })
    }
    /// Read `ZEEBRA_GROEBNER_RS_DRIVER`, defaulting to `groebner-rs-driver` on PATH.
    /// # Errors
    /// As [`Self::new`].
    pub fn from_env(work_dir: impl Into<PathBuf>) -> Result<Self, RunFailure> {
        Self::new(
            std::env::var("ZEEBRA_GROEBNER_RS_DRIVER")
                .unwrap_or_else(|_| "groebner-rs-driver".into()),
            work_dir,
        )
    }
    /// Observe the driver loader/startup floor without constructing a ring or worker pool.
    /// # Errors
    /// Returns the supervisor failure or rejects an unrecognized driver response.
    pub fn startup_measurement(&mut self, limits: &Limits) -> Result<Measurement, RunFailure> {
        let (_, output) = self.paths();
        let invocation = Invocation::new(&self.binary, &self.work_dir, &output).arg("--startup");
        let process = Supervisor::new(limits.wall)
            .with_max_rss_bytes(limits.max_rss_bytes)
            .run(&invocation)?;
        if !process.succeeded() {
            return Err(RunFailure::NonZeroExit {
                code: process.exit_code,
            });
        }
        identity(
            &Json::parse(&std::fs::read_to_string(output)?).map_err(|e| invalid(e.to_string()))?,
        )?;
        Ok(Measurement::of_process(&process))
    }
    fn paths(&mut self) -> (PathBuf, PathBuf) {
        self.runs += 1;
        (
            self.work_dir.join(format!("{}.json", self.runs)),
            self.work_dir.join(format!("{}.out", self.runs)),
        )
    }
    fn report(
        &self,
        instance: &Instance,
        task: Task,
        limits: &Limits,
        status: RunStatus,
        measurement: Measurement,
        command: Option<String>,
    ) -> RunReport {
        let mut report = RunReport::new(self.id(), instance, task, limits, status, measurement);
        if let Some(version) = &self.version {
            report = report.with_version(version.clone());
        }
        if let Some(command) = command {
            report = report.with_command_line(command);
        }
        report
    }
}
impl ExternalSolver for GroebnerRsSolver {
    fn id(&self) -> &str {
        "groebner-rs"
    }
    fn probe_version(&mut self) -> Result<ToolVersion, RunFailure> {
        let (_, output) = self.paths();
        let invocation = Invocation::new(&self.binary, &self.work_dir, &output).arg("--version");
        let process = Supervisor::new(Duration::from_secs(10)).run(&invocation)?;
        if !process.succeeded() {
            return Err(RunFailure::NonZeroExit {
                code: process.exit_code,
            });
        }
        let raw = std::fs::read_to_string(output)?;
        let json = Json::parse(&raw).map_err(|e| invalid(e.to_string()))?;
        let version = ToolVersion::new(self.id(), "0.6.0")
            .with_build(identity(&json)?)
            .with_raw(raw);
        self.version = Some(version.clone());
        Ok(version)
    }
    fn supports(&self, instance: &Instance, task: Task) -> Support {
        if instance.field.extension_degree != 1 {
            return Support::No(Unsupported::ExtensionField {
                characteristic: instance.field.characteristic,
                extension_degree: instance.field.extension_degree,
            });
        }
        if !matches!(task, Task::ReducedGrobnerBasis | Task::LexBasis) {
            return Support::No(Unsupported::Task { task });
        }
        if !matches!(
            instance.order,
            MonomialOrder::Lexicographic
                | MonomialOrder::GradedLexicographic
                | MonomialOrder::GradedReverseLexicographic
        ) || (task == Task::LexBasis && instance.order != MonomialOrder::Lexicographic)
        {
            return Support::No(Unsupported::Order {
                order: instance.order,
            });
        }
        if instance.field.characteristic < 2 {
            return Support::No(Unsupported::Representation {
                detail: "prime modulus must be >= 2".into(),
            });
        }
        Support::Yes
    }
    fn run(&mut self, instance: &Instance, task: Task, limits: &Limits) -> RunReport {
        if let Support::No(reason) = self.supports(instance, task) {
            return self.report(
                instance,
                task,
                limits,
                RunStatus::Unsupported(reason),
                Measurement::unmeasured(),
                None,
            );
        }
        if !(1..=1024).contains(&limits.workers) || !limits.tool_caps.is_empty() {
            return self.report(
                instance,
                task,
                limits,
                RunStatus::Unsupported(Unsupported::Representation {
                    detail:
                        "driver requires 1..=1024 workers and has no additional tool-specific caps"
                            .into(),
                }),
                Measurement::unmeasured(),
                None,
            );
        }
        let (input, output) = self.paths();
        let invocation = Invocation::new(&self.binary, &self.work_dir, &output).arg(&input);
        let command = Some(invocation.command_line());
        let mut measurement = Measurement::unmeasured();
        let result = (|| -> Result<RunStatus, RunFailure> {
            if let Some(absent) = invocation.unavailable() {
                return Err(absent.into());
            }
            if self.version.is_none() {
                self.probe_version()?;
            }
            let request = Json::object([
                (
                    "variables",
                    Json::Array(instance.variables.iter().map(Json::string).collect()),
                ),
                ("modulus", Json::int(instance.field.characteristic)),
                ("order", Json::string(order_tag(instance.order))),
                ("workers", Json::size(limits.workers)),
                (
                    "generators",
                    Json::Array(instance.system.iter().map(Json::string).collect()),
                ),
            ]);
            std::fs::write(&input, request.to_json())?;
            let process = Supervisor::new(limits.wall)
                .with_max_rss_bytes(limits.max_rss_bytes)
                .run(&invocation)?;
            measurement = Measurement::of_process(&process);
            if process.memory_limited {
                return Ok(RunStatus::StoppedByLimit(LimitStop::Memory {
                    limit: limits.max_rss_bytes.unwrap(),
                    observed: process.peak_rss_bytes,
                }));
            }
            if process.timed_out {
                return Ok(RunStatus::StoppedByLimit(LimitStop::WallClock {
                    limit: limits.wall,
                    elapsed: process.wall,
                }));
            }
            if !process.succeeded() {
                return Err(RunFailure::NonZeroExit {
                    code: process.exit_code,
                });
            }
            let start = Instant::now();
            let raw = std::fs::read_to_string(&output)?;
            let json = Json::parse(&raw).map_err(|e| invalid(e.to_string()))?;
            let observed_build = identity(&json)?;
            if self.version.as_ref().and_then(|v| v.build.as_deref())
                != Some(observed_build.as_str())
            {
                return Err(invalid("driver build changed between probe and solve"));
            }
            let (answer, stages) = parse_answer(&json, instance, limits.workers)?;
            measurement.stages = stages;
            measurement
                .stages
                .push(("harness-output".into(), start.elapsed()));
            let start = Instant::now();
            let trusted = ZeebraSolver::new().run(
                instance,
                task,
                &Limits {
                    workers: 1,
                    ..limits.clone()
                },
            );
            let status = match trusted.status.answer() {
                Some(reference) => verify_basis(answer, reference, instance.field.characteristic),
                None => Err(RunFailure::Incomplete {
                    detail: format!("independent verification unavailable: {:?}", trusted.status),
                }),
            };
            measurement
                .stages
                .push(("independent-verification".into(), start.elapsed()));
            status
        })();
        self.report(
            instance,
            task,
            limits,
            result.unwrap_or_else(RunStatus::Failed),
            measurement,
            command,
        )
        .with_log_path(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        grobner::external::{FieldSpec, Invariants},
        util::Json,
        MonomialOrder,
    };
    fn instance() -> Instance {
        Instance::new(
            "linear",
            "control",
            FieldSpec::prime(32003),
            vec!["x10".into(), "x1".into()],
            vec!["x10-1".into(), "x1-2".into()],
            MonomialOrder::GradedReverseLexicographic,
        )
    }
    fn output() -> Json {
        Json::parse(r#"{"contract":1,"revision":"c3e1d630fba9b2155a4c389d9022f13e0ba09218","build":"locked-test-build","build_metadata":"PROFILE=release;OPT_LEVEL=3;CARGO_PROFILE_RELEASE_LTO=fat;CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1;","isa":"x86-64-v3","variables":["x10","x1"],"modulus":32003,"order":"grevlex","workers":1,"generators":["x10+32002","x1+32001"],"basis":["x10+32002","x1+32001"],"leading":["x10","x1"],"parse_ns":1,"solve_ns":2,"serialization_ns":3}"#).unwrap()
    }
    // A provisioned driver agrees on all smoke fields and reports both wall and RSS stops.
    #[test]
    #[ignore = "requires the pinned groebner-rs driver"]
    fn test_live_driver_agreement_and_resource_stops() {
        let dir = std::env::temp_dir().join(format!("groebner-rs-live-{}", std::process::id()));
        let mut solver = GroebnerRsSolver::from_env(&dir).unwrap();
        solver.probe_version().expect("provisioned pinned driver");
        for workers in [1, 4] {
            let limits = Limits::wall(Duration::from_secs(10))
                .with_workers(workers)
                .with_max_rss_bytes(1024 * 1024 * 1024);
            for modulus in [
                32003,
                2147483647,
                18_446_744_073_709_551_263,
                18_446_744_073_709_551_557,
            ] {
                let input = wide_control(modulus).unwrap_or_else(|| {
                    super::super::corpus::instance(
                        "katsura-4",
                        modulus,
                        MonomialOrder::GradedReverseLexicographic,
                    )
                    .unwrap()
                });
                let report = solver.run(&input, Task::ReducedGrobnerBasis, &limits);
                assert!(
                    report.status.is_verified(),
                    "{modulus}/{workers}: {:?}",
                    report.status
                );
            }
        }
        for order in [
            MonomialOrder::Lexicographic,
            MonomialOrder::GradedLexicographic,
        ] {
            let input = super::super::corpus::instance("katsura-4", 32003, order).unwrap();
            let report = solver.run(
                &input,
                Task::ReducedGrobnerBasis,
                &Limits::wall(Duration::from_secs(10)),
            );
            assert!(
                report.status.is_verified(),
                "{}: {:?}",
                order.name(),
                report.status
            );
        }
        let input = super::super::corpus::instance(
            "katsura-6",
            2147483647,
            MonomialOrder::GradedReverseLexicographic,
        )
        .unwrap();
        let memory = solver.run(
            &input,
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(10)).with_max_rss_bytes(1),
        );
        assert!(
            matches!(
                memory.status,
                RunStatus::StoppedByLimit(LimitStop::Memory { .. })
            ),
            "{:?}",
            memory.status
        );
        let time = solver.run(
            &input,
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::ZERO),
        );
        assert!(
            matches!(
                time.status,
                RunStatus::StoppedByLimit(LimitStop::WallClock { .. })
            ),
            "{:?}",
            time.status
        );
        let _ = std::fs::remove_dir_all(dir);
    }

    // Both focused wide controls retain their digests and have an independently computed dimension four.
    #[test]
    fn test_wide_controls_are_pinned_and_verifiable() {
        for &(modulus, digest) in control_entry().digests {
            let input = wide_control(modulus).unwrap();
            assert_eq!(input.digest(), digest);
            let report = ZeebraSolver::new().run(
                &input,
                Task::ReducedGrobnerBasis,
                &Limits::wall(Duration::from_secs(5)),
            );
            assert_eq!(
                report
                    .status
                    .answer()
                    .expect("compiled focused field")
                    .invariants
                    .quotient_dimension,
                Some(4)
            );
        }
    }

    // An absent executable remains unavailable even when a zero wall budget is requested.
    #[test]
    fn test_missing_executable_is_not_a_resource_stop() {
        let dir = std::env::temp_dir().join(format!("groebner-rs-missing-{}", std::process::id()));
        let mut solver = GroebnerRsSolver::new("/missing/groebner-rs-driver", &dir).unwrap();
        let report = solver.run(
            &instance(),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::ZERO),
        );
        assert!(matches!(
            report.status,
            RunStatus::Failed(RunFailure::Unavailable { .. })
        ));
        assert_eq!(report.measurement, Measurement::unmeasured());
        let _ = std::fs::remove_dir_all(dir);
    }
    // Metadata permutations, modulus/order mismatch, missing fields and malformed arrays are rejected.
    #[test]
    fn test_the_driver_echo_is_checked_exactly() {
        assert!(parse_answer(&output(), &instance(), 1).is_ok());
        for (key, value) in [
            ("modulus", Json::int(101)),
            ("order", Json::string("lex")),
            (
                "variables",
                Json::Array(vec![Json::string("x1"), Json::string("x10")]),
            ),
            ("basis", Json::string("malformed")),
            ("workers", Json::int(4)),
            ("revision", Json::string("wrong")),
        ] {
            let mut changed = output();
            if let Json::Object(fields) = &mut changed {
                fields.iter_mut().find(|(k, _)| k == key).unwrap().1 = value;
            }
            assert!(parse_answer(&changed, &instance(), 1).is_err(), "{key}");
        }
    }
    // Equal leading monomials cannot conceal a wrong coefficient or an incomplete reduced basis.
    #[test]
    fn test_full_basis_agreement_is_required() {
        let (answer, _) = parse_answer(&output(), &instance(), 1).unwrap();
        let trusted = Answer::from_invariants(
            Invariants::none().with_leading_monomials(vec!["x10".into(), "x1".into()]),
        )
        .with_basis(vec!["x10-1".into(), "x1-2".into()]);
        assert!(verify_basis(answer.clone(), &trusted, 32003).is_ok());
        let wrong = Answer {
            basis: Some(vec!["x10-2".into(), "x1-2".into()]),
            ..answer
        };
        assert!(verify_basis(wrong, &trusted, 32003).is_err());
    }
}
