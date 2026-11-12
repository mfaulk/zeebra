use super::{
    contract::order_tag,
    process::{Invocation, Supervisor},
    Answer, ExternalSolver, Instance, Invariants, LimitStop, Limits, Measurement, RunFailure,
    RunReport, RunStatus, SingularSolver, Support, Task, ToolVersion, Unsupported, Verification,
};
use crate::{util::Json, MonomialOrder};
use std::{
    collections::BTreeMap,
    path::PathBuf,
    time::{Duration, Instant},
};

/// Source revision of the separately built MIT/Apache executable; the root graph is unchanged.
pub const PINNED_REVISION: &str = "ea34ddf3c9b9a275265576cd881c39c0c473e9f9";
/// Raw reduced-basis computation and computation with exact cofactor certification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Raw,
    Certified,
}
impl Mode {
    fn tag(self) -> &'static str {
        match self {
            Self::Raw => "raw",
            Self::Certified => "certified",
        }
    }
}
fn failure(detail: impl Into<String>) -> RunFailure {
    RunFailure::SelfInconsistent {
        detail: detail.into(),
    }
}
fn text<'a>(json: &'a Json, key: &str) -> Result<&'a str, RunFailure> {
    json.get(key)
        .and_then(Json::as_str)
        .ok_or_else(|| failure(format!("missing string {key}")))
}
fn number(json: &Json, key: &str) -> Result<u64, RunFailure> {
    json.get(key)
        .and_then(Json::as_int)
        .and_then(|n| u64::try_from(n).ok())
        .ok_or_else(|| failure(format!("invalid integer {key}")))
}
fn strings(json: &Json, key: &str) -> Result<Vec<String>, RunFailure> {
    let Some(Json::Array(items)) = json.get(key) else {
        return Err(failure(format!("missing array {key}")));
    };
    items
        .iter()
        .map(|v| {
            v.as_str()
                .map(str::to_owned)
                .ok_or_else(|| failure("invalid string array"))
        })
        .collect()
}
fn identity(json: &Json) -> Result<String, RunFailure> {
    if number(json, "contract")? != 1
        || text(json, "revision")? != PINNED_REVISION
        || text(json, "isa")? != "x86-64-v3"
    {
        return Err(failure("unrecognized revision, protocol or ISA"));
    }
    let metadata = text(json, "build_metadata")?;
    for setting in [
        "PROFILE=release;",
        "OPT_LEVEL=3;",
        "CARGO_PROFILE_RELEASE_LTO=fat;",
        "CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1;",
    ] {
        if !metadata.contains(setting) {
            return Err(failure("unrecognized release profile"));
        }
    }
    let build = text(json, "build")?;
    if build.is_empty() {
        return Err(failure("missing build identity"));
    }
    Ok(format!(
        "{PINNED_REVISION};isa=x86-64-v3;allocator=system;{build}"
    ))
}
fn basis_list(raw: &str) -> Result<Vec<String>, RunFailure> {
    let raw = raw
        .trim()
        .strip_suffix(':')
        .ok_or_else(|| failure("truncated basis"))?
        .trim();
    let body = raw
        .strip_prefix('[')
        .and_then(|s| s.strip_suffix(']'))
        .ok_or_else(|| failure("malformed basis"))?;
    if body.trim().is_empty() {
        return Ok(Vec::new());
    }
    body.split(',')
        .map(|s| {
            let s = s.trim();
            if s.is_empty() || s.contains(['[', ']', ':']) {
                Err(failure("malformed polynomial list"))
            } else {
                Ok(s.to_owned())
            }
        })
        .collect()
}
fn mul(a: u64, b: u64, p: u64) -> u64 {
    (a as u128 * b as u128 % p as u128) as u64
}
fn pow(mut a: u64, mut n: u32, p: u64) -> u64 {
    let mut b = 1;
    while n > 0 {
        if n & 1 == 1 {
            b = mul(b, a, p);
        }
        a = mul(a, a, p);
        n >>= 1;
    }
    b
}
// Expanded polynomial text only: aggregate like terms and compare scalar multiples without inversion.
fn terms(raw: &str, p: u64) -> Option<BTreeMap<String, u64>> {
    if p < 2 {
        return None;
    }
    let raw: String = raw.chars().filter(|c| !c.is_whitespace()).collect();
    let mut result = BTreeMap::new();
    let mut begin = 0;
    let mut negative = false;
    for (end, c) in raw.char_indices().chain(std::iter::once((raw.len(), '+'))) {
        if c != '+' && c != '-' {
            continue;
        }
        if end > begin {
            let mut coefficient = 1;
            let mut factors = BTreeMap::<String, u32>::new();
            for factor in raw[begin..end].split('*') {
                let (base, n) = match factor.split_once('^') {
                    Some((b, n)) => (b, n.parse::<u32>().ok()?),
                    None => (factor, 1),
                };
                if let Ok(a) = base.parse::<u64>() {
                    coefficient = mul(coefficient, pow(a % p, n, p), p);
                } else {
                    if base.is_empty()
                        || base.as_bytes()[0].is_ascii_digit()
                        || !base.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                    {
                        return None;
                    }
                    let entry = factors.entry(base.into()).or_default();
                    *entry = entry.checked_add(n)?;
                }
            }
            let monomial = factors
                .into_iter()
                .filter(|(_, n)| *n > 0)
                .map(|(b, n)| format!("{b}^{n}"))
                .collect::<Vec<_>>()
                .join("*");
            if negative && coefficient != 0 {
                coefficient = p - coefficient;
            }
            let entry = result.entry(monomial).or_insert(0);
            *entry = ((*entry as u128 + coefficient as u128) % p as u128) as u64;
            negative = false;
        }
        if c == '-' {
            negative = !negative;
        }
        begin = end + 1;
    }
    result.retain(|_, c| *c != 0);
    Some(result)
}
fn projectively_equal(a: &str, b: &str, p: u64) -> bool {
    let (Some(a), Some(b)) = (terms(a, p), terms(b, p)) else {
        return false;
    };
    if a.keys().ne(b.keys()) {
        return false;
    }
    match (a.first_key_value(), b.first_key_value()) {
        (None, None) => true,
        (Some((_, x)), Some((_, y))) => a
            .iter()
            .zip(&b)
            .all(|((_, a), (_, b))| mul(*a, *y, p) == mul(*b, *x, p)),
        _ => false,
    }
}
fn request(instance: &Instance, mode: Mode, limits: &Limits) -> Json {
    Json::object([
        (
            "variables",
            Json::Array(instance.variables.iter().map(Json::string).collect()),
        ),
        ("modulus", Json::int(instance.field.characteristic)),
        ("order", Json::string(order_tag(instance.order))),
        ("workers", Json::size(limits.workers)),
        ("mode", Json::string(mode.tag())),
        (
            "generators",
            Json::Array(instance.system.iter().map(Json::string).collect()),
        ),
        (
            "wall_ns",
            Json::int(limits.wall.as_nanos().min(u64::MAX as u128) as u64),
        ),
        (
            "rss_bytes",
            limits.max_rss_bytes.map(Json::int).unwrap_or(Json::Null),
        ),
    ])
}
fn objective_limits(mode: Mode, limits: &Limits) -> Limits {
    if mode == Mode::Certified {
        limits
            .clone()
            .with_tool_cap("objective=exact-certified-basis")
    } else {
        limits.clone()
    }
}
fn validate_output(
    json: &Json,
    instance: &Instance,
    mode: Mode,
    limits: &Limits,
) -> Result<Answer, RunFailure> {
    identity(json)?;
    let expected = request(instance, mode, limits);
    let actual = json
        .get("input")
        .ok_or_else(|| failure("missing input identity"))?;
    let Json::Object(fields) = expected else {
        unreachable!()
    };
    for (key, value) in fields {
        if actual.get(&key) != Some(&value) {
            return Err(failure(format!("input differs at {key}")));
        }
    }
    if json.get("stopped") != Some(&Json::Null) {
        return Err(failure("partial or stopped output"));
    }
    if mode == Mode::Certified && json.get("certified") != Some(&Json::Bool(true)) {
        return Err(failure("independent checker did not accept"));
    }
    if mode == Mode::Raw && json.get("certified") != Some(&Json::Null) {
        return Err(failure("raw result changed objective"));
    }
    let engine = strings(json, "generator_echoes")?;
    if engine.len() != instance.system.len() {
        return Err(failure("generator positions differ"));
    }
    for (original, echo) in instance.system.iter().zip(&engine) {
        let parsed = basis_list(echo)?;
        if parsed.len() > 1
            || !projectively_equal(
                original,
                parsed.first().map(String::as_str).unwrap_or("0"),
                instance.field.characteristic,
            )
        {
            return Err(failure("engine parsed a different ordered generator"));
        }
    }
    if mode == Mode::Certified && json.get("certificate").and_then(Json::as_str).is_none() {
        return Err(failure("missing exact cofactor evidence"));
    }
    if strings(json, "parsed_variables")? != instance.variables
        || number(json, "parsed_modulus")? != instance.field.characteristic
        || text(json, "backend")? != "f4"
        || number(json, "actual_workers")? != limits.workers as u64
        || json.get("complete") != Some(&Json::Bool(true))
    {
        return Err(failure(
            "actual ring, backend, workers or completion differ",
        ));
    }
    if mode == Mode::Certified && text(json, "certificate_format")? != "sylv-gb-cert-v2" {
        return Err(failure("unexpected certificate format"));
    }
    let basis = basis_list(text(json, "basis")?)?;
    Ok(
        Answer::from_invariants(Invariants::none().with_basis_cardinality(basis.len()))
            .with_basis(basis),
    )
}
fn verified(
    mut answer: Answer,
    trusted: &Answer,
    p: u64,
    oracle: &str,
) -> Result<RunStatus, RunFailure> {
    let (Some(ours), Some(theirs)) = (&answer.basis, &trusted.basis) else {
        return Err(failure("missing independent full basis"));
    };
    let normalize = |polys: &[String]| -> Option<Vec<String>> {
        let mut v = polys
            .iter()
            .map(|ptext| terms(ptext, p).map(|t| format!("{t:?}")))
            .collect::<Option<Vec<_>>>()?;
        v.sort();
        Some(v)
    };
    if normalize(ours).is_none() || normalize(ours) != normalize(theirs) {
        return Err(failure(
            "full reduced basis disagrees with independent verification",
        ));
    }
    let check=Verification::of(oracle,&answer.invariants,&trusted.invariants).map_err(|_|failure("basis cardinality differs"))?
        .with_note("exact full reduced-basis equality; verification cost excluded from child computation and retained separately");
    answer.invariants = trusted.invariants.clone();
    Ok(RunStatus::Verified(answer, check))
}
/// A pinned subprocess adapter; raw answers require an independent exact reference or cofactor check.
#[derive(Clone, Debug)]
pub struct SylvesterSolver {
    binary: String,
    work_dir: PathBuf,
    mode: Mode,
    runs: u64,
    version: Option<ToolVersion>,
}
impl SylvesterSolver {
    /// Create scratch storage for a raw or exactly certified subprocess.
    /// # Errors
    /// Returns a harness error if the directory cannot be created.
    pub fn new(
        binary: impl Into<String>,
        work_dir: impl Into<PathBuf>,
        mode: Mode,
    ) -> Result<Self, RunFailure> {
        let work_dir = work_dir.into();
        std::fs::create_dir_all(&work_dir)?;
        Ok(Self {
            binary: binary.into(),
            work_dir,
            mode,
            runs: 0,
            version: None,
        })
    }
    /// Read `ZEEBRA_SYLVESTER_DRIVER`, defaulting to `sylvester-driver` on PATH.
    /// # Errors
    /// As [`Self::new`].
    pub fn from_env(work_dir: impl Into<PathBuf>, mode: Mode) -> Result<Self, RunFailure> {
        Self::new(
            std::env::var("ZEEBRA_SYLVESTER_DRIVER").unwrap_or_else(|_| "sylvester-driver".into()),
            work_dir,
            mode,
        )
    }
    fn paths(&mut self) -> (PathBuf, PathBuf) {
        self.runs += 1;
        (
            self.work_dir.join(format!("{}.json", self.runs)),
            self.work_dir.join(format!("{}.out", self.runs)),
        )
    }
    /// Measure the loader without parsing a ring or starting an engine.
    /// # Errors
    /// Returns the supervisor error or rejects an invalid driver identity.
    pub fn startup_measurement(&mut self, limits: &Limits) -> Result<Measurement, RunFailure> {
        let (_, output) = self.paths();
        let invocation = Invocation::new(&self.binary, &self.work_dir, &output).arg("--startup");
        let process = Supervisor::new(limits.wall)
            .with_max_rss_bytes(limits.max_rss_bytes)
            .run(&invocation)?;
        if !process.succeeded() {
            return Err(failure("startup did not complete"));
        }
        let json =
            Json::parse(&std::fs::read_to_string(output)?).map_err(|e| failure(e.to_string()))?;
        identity(&json)?;
        let mut m = Measurement::of_process(&process);
        if cfg!(target_os = "linux") {
            m.peak_rss_bytes = Some(number(&json, "kernel_peak_rss_bytes")?);
            m.rss_basis = super::RssBasis::ChildSelfHighWater;
        }
        Ok(m)
    }
    fn execute(
        &mut self,
        instance: &Instance,
        mode: Mode,
        limits: &Limits,
    ) -> Result<(Json, Measurement, String, PathBuf), RunFailure> {
        let (input, output) = self.paths();
        std::fs::write(&input, request(instance, mode, limits).to_json())?;
        let invocation = Invocation::new(&self.binary, &self.work_dir, &output).arg(&input);
        let command = invocation.command_line();
        let process = Supervisor::new(limits.wall)
            .with_max_rss_bytes(limits.max_rss_bytes)
            .run(&invocation)?;
        let mut m = Measurement::of_process(&process);
        let json = if process.succeeded() {
            Json::parse(&std::fs::read_to_string(&output)?).map_err(|e| failure(e.to_string()))?
        } else {
            Json::Null
        };
        // External hard stops win over missing/truncated JSON.
        if process.memory_limited {
            return Ok((
                Json::object([("stopped", Json::string("memory"))]),
                m,
                command,
                output,
            ));
        }
        if process.timed_out {
            return Ok((
                Json::object([("stopped", Json::string("deadline"))]),
                m,
                command,
                output,
            ));
        }
        if !process.succeeded() {
            return Err(RunFailure::NonZeroExit {
                code: process.exit_code,
            });
        }
        if cfg!(target_os = "linux") {
            let peak = number(&json, "kernel_peak_rss_bytes")?;
            if peak == 0 {
                return Err(failure("missing self high-water mark"));
            }
            m.peak_rss_bytes = Some(peak.max(m.peak_rss_bytes.unwrap_or(0)));
            m.rss_basis = super::RssBasis::ChildSelfHighWater;
            if limits
                .max_rss_bytes
                .is_some_and(|cap| m.peak_rss_bytes.is_some_and(|peak| peak > cap))
            {
                return Ok((
                    Json::object([("stopped", Json::string("memory"))]),
                    m,
                    command,
                    output,
                ));
            }
        }
        Ok((json, m, command, output))
    }
}
impl ExternalSolver for SylvesterSolver {
    fn id(&self) -> &'static str {
        if self.mode == Mode::Raw {
            "sylvester"
        } else {
            "sylvester-certified"
        }
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
        let json = Json::parse(&raw).map_err(|e| failure(e.to_string()))?;
        let version = ToolVersion::new(self.id(), "0.4.0")
            .with_build(identity(&json)?)
            .with_raw(raw);
        self.version = Some(version.clone());
        Ok(version)
    }
    fn supports(&self, input: &Instance, task: Task) -> Support {
        if input.field.extension_degree != 1 {
            return Support::No(Unsupported::ExtensionField {
                characteristic: input.field.characteristic,
                extension_degree: input.field.extension_degree,
            });
        }
        if task != Task::ReducedGrobnerBasis {
            return Support::No(Unsupported::Task { task });
        }
        if input.order != MonomialOrder::GradedReverseLexicographic {
            return Support::No(Unsupported::Order { order: input.order });
        }
        if input.field.characteristic < 2
            || input.field.characteristic >= 2_147_483_648
            || input.variables.is_empty()
        {
            return Support::No(Unsupported::Representation {
                detail: "F4 requires a prime below 2^31 and named variables".into(),
            });
        }
        Support::Yes
    }
    fn run(&mut self, instance: &Instance, task: Task, limits: &Limits) -> RunReport {
        let mut measurement = Measurement::unmeasured();
        let mut command = None;
        let mut log = None;
        let result = (|| -> Result<RunStatus, RunFailure> {
            if let Support::No(reason) = self.supports(instance, task) {
                return Ok(RunStatus::Unsupported(reason));
            }
            if !(1..=1024).contains(&limits.workers)
                || (self.mode == Mode::Certified && limits.workers != 1)
                || !limits.tool_caps.is_empty()
            {
                return Ok(RunStatus::Unsupported(Unsupported::Representation {
                    detail: "certified F4 is serial; raw workers must be 1..=1024; no extra tool caps supported"
                        .into(),
                }));
            }
            if self.version.is_none() {
                self.probe_version()?;
            }
            let (json, m, cmd, path) = self.execute(instance, self.mode, limits)?;
            measurement = m;
            command = Some(cmd);
            log = Some(path);
            if limits
                .max_rss_bytes
                .is_some_and(|limit| measurement.peak_rss_bytes.is_some_and(|peak| peak > limit))
                || json.get("stopped").and_then(Json::as_str) == Some("memory")
            {
                return Ok(RunStatus::StoppedByLimit(LimitStop::Memory {
                    limit: limits.max_rss_bytes.unwrap_or(0),
                    observed: measurement.peak_rss_bytes,
                }));
            }
            if let Some(stop) = json.get("stopped").and_then(Json::as_str) {
                return Ok(RunStatus::StoppedByLimit(LimitStop::ToolCap {
                    detail: format!("sylvester {stop}"),
                }));
            }
            if number(&json, "actual_workers")? != limits.workers as u64 {
                return Ok(RunStatus::Unsupported(Unsupported::Representation {
                    detail: "F4 did not supply the requested worker pool".into(),
                }));
            }
            let answer = validate_output(&json, instance, self.mode, limits)?;
            if self.version.as_ref().and_then(|v| v.build.as_deref())
                != Some(identity(&json)?.as_str())
            {
                return Err(failure("driver build changed after probing"));
            }
            measurement.stages.push((
                "parse".into(),
                Duration::from_nanos(number(&json, "parse_ns")?),
            ));
            measurement.stages.push((
                if self.mode == Mode::Raw {
                    "solve"
                } else {
                    "certified-total"
                }
                .into(),
                Duration::from_nanos(number(&json, "solve_ns")?),
            ));
            // Persist the complete trajectory/certificate beside the output. It is not a stage ratio.
            let start = Instant::now();
            let mut oracle = SingularSolver::with_binary(
                std::env::var("SINGULAR").unwrap_or_else(|_| "Singular".into()),
                self.work_dir.join("independent-singular"),
                limits.wall,
            )?;
            let oracle_version = oracle.probe_version()?;
            let reference = oracle.run(
                instance,
                task,
                &Limits {
                    workers: 1,
                    ..limits.clone()
                },
            );
            let checked = match reference.status.answer() {
                Some(reference) => verified(
                    answer,
                    reference,
                    instance.field.characteristic,
                    &oracle_version.to_string(),
                ),
                None => Err(RunFailure::Incomplete {
                    detail: format!("independent Singular unavailable: {:?}", reference.status),
                }),
            };
            measurement
                .stages
                .push(("independent-verification".into(), start.elapsed()));
            checked
        })();
        let mut report = RunReport::new(
            self.id(),
            instance,
            task,
            &objective_limits(self.mode, limits),
            result.unwrap_or_else(RunStatus::Failed),
            measurement,
        );
        if let Some(version) = &self.version {
            report = report.with_version(version.clone());
        }
        if let Some(cmd) = command {
            report = report.with_command_line(cmd);
        }
        if let Some(path) = log {
            report = report.with_log_path(path);
        }
        report
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grobner::external::{FieldSpec, Invariants};
    use crate::MonomialOrder;
    fn instance() -> Instance {
        Instance::new(
            "control",
            "control",
            FieldSpec::prime(32003),
            vec!["x10".into(), "x1".into()],
            vec!["2*x10-2*x1".into(), "0".into(), "x1^2-1".into()],
            MonomialOrder::GradedReverseLexicographic,
        )
    }
    fn output(mode: Mode) -> Json {
        let request = request(&instance(), mode, &Limits::wall(Duration::from_secs(10)));
        Json::object([("contract",Json::int(1)),("revision",Json::string(PINNED_REVISION)),("isa",Json::string("x86-64-v3")),("build",Json::string("test-build")),("build_metadata",Json::string("PROFILE=release;OPT_LEVEL=3;CARGO_PROFILE_RELEASE_LTO=fat;CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1;")),("input",request),("parsed_modulus",Json::int(32003)),("parsed_variables",Json::Array(["x10","x1"].into_iter().map(Json::string).collect())),("backend",Json::string("f4")),("actual_workers",Json::int(1)),("complete",Json::Bool(true)),("certificate_format",Json::string("sylv-gb-cert-v2")),
            ("generator_echoes",Json::Array(["[x10+32002*x1]:\n","[]:\n","[x1^2+32002]:\n"].into_iter().map(Json::string).collect())),
            ("checker_echoes",Json::Array(["[x10+32002*x1]:\n","[]:\n","[x1^2+32002]:\n"].into_iter().map(Json::string).collect())),
            ("basis",Json::string("[x10+32002*x1,\nx1^2+32002]:\n")),("certificate",Json::string("[[1,0,0],[0,0,1]]")),("stopped",Json::Null),("certified",if mode==Mode::Certified{Json::Bool(true)}else{Json::Null}),
            ("parse_ns",Json::int(1)),("solve_ns",Json::int(10)),("kernel_peak_rss_bytes",Json::int(10000000)),
            ("report",Json::string(format!("0.000001 call entry=groebner order=grevlex seed=0 threads=1 checker={}\n0.000002 read variables=2 characteristic=32003 field=gf31\n0.000010 end result=basis time=0.000010\n",if mode==Mode::Raw {"off"} else {"exact"})))])
    }
    // Generator checks bind ordered positions and accept only a nonzero scalar normalization.
    #[test]
    fn test_echoes_preserve_order_and_wide_coefficients() {
        assert!(projectively_equal("2*x10-2*x1", "x10+32002*x1", 32003));
        assert!(projectively_equal("x1+x1", "2*x1", 32003));
        assert!(!projectively_equal("x1*x10-1", "x1^2-1", 32003));
        let p = 18446744073709551557;
        assert!(projectively_equal(
            "18446744073709551556*x10+1",
            "x10+18446744073709551556",
            p
        ));
        let mut json = output(Mode::Raw);
        assert!(validate_output(
            &json,
            &instance(),
            Mode::Raw,
            &Limits::wall(Duration::from_secs(10))
        )
        .is_ok());
        if let Json::Object(ref mut fields) = json {
            let echoes = fields
                .iter_mut()
                .find(|(k, _)| k == "generator_echoes")
                .unwrap();
            echoes.1 = Json::Array(vec![Json::string("[x1]:\n")]);
        }
        assert!(validate_output(
            &json,
            &instance(),
            Mode::Raw,
            &Limits::wall(Duration::from_secs(10))
        )
        .is_err());
    }
    // Truncated output, wrong input and unverified exact mode never become answers.
    #[test]
    fn test_rejects_forged_and_partial_outputs() {
        let limits = Limits::wall(Duration::from_secs(10));
        for (key, value) in [
            ("basis", Json::string("[x10]")),
            ("input", Json::Null),
            ("certificate", Json::Null),
            ("certified", Json::Bool(false)),
            ("stopped", Json::string("deadline")),
        ] {
            let mut json = output(Mode::Certified);
            if let Json::Object(ref mut fields) = json {
                fields.iter_mut().find(|(k, _)| k == key).unwrap().1 = value;
            }
            assert!(
                validate_output(&json, &instance(), Mode::Certified, &limits).is_err(),
                "{key}"
            );
        }
    }
    // Certification's stronger objective cannot compare with raw-basis timing records.
    #[test]
    fn test_certification_has_distinct_limits() {
        let limits = Limits::wall(Duration::from_secs(10));
        assert!(!objective_limits(Mode::Certified, &limits).comparable_with(&limits));
        assert_eq!(objective_limits(Mode::Raw, &limits), limits);
    }
    // Capabilities refuse unimplemented orders, extension fields and conversion tasks.
    #[test]
    fn test_capabilities_are_explicit() {
        let dir = std::env::temp_dir().join(format!("sylvester-support-{}", std::process::id()));
        let solver = SylvesterSolver::new("absent-sylvester-driver", &dir, Mode::Raw).unwrap();
        let mut input = instance();
        assert!(solver
            .supports(&input, Task::ReducedGrobnerBasis)
            .is_supported());
        assert!(!solver
            .supports(&input, Task::LexBasisByConversion)
            .is_supported());
        input.order = MonomialOrder::GradedLexicographic;
        assert!(!solver
            .supports(&input, Task::ReducedGrobnerBasis)
            .is_supported());
        input.field.extension_degree = 8;
        assert!(!solver
            .supports(&input, Task::ReducedGrobnerBasis)
            .is_supported());
    }
    // Full-basis verification rejects a wrong coefficient even when leading monomials agree.
    #[test]
    fn test_verification_requires_full_basis_equality() {
        let invariants = Invariants::none().with_basis_cardinality(1);
        let answer = Answer::from_invariants(invariants.clone()).with_basis(vec!["x1-1".into()]);
        let trusted = Answer::from_invariants(invariants).with_basis(vec!["x1-2".into()]);
        assert!(verified(answer, &trusted, 32003, "oracle").is_err());
    } // The provisioned driver checks small/wide ideals against exact evidence and preserves hard stops.
    #[test]
    #[ignore = "requires the pinned sylvester driver and Singular"]
    fn test_live_sylvester_exact_evidence_and_stops() {
        let dir = std::env::temp_dir().join(format!("sylvester-live-{}", std::process::id()));
        for mode in [Mode::Raw, Mode::Certified] {
            let mut solver = SylvesterSolver::from_env(dir.join(mode.tag()), mode).unwrap();
            let limits =
                Limits::wall(Duration::from_secs(20)).with_max_rss_bytes(1024 * 1024 * 1024);
            solver.probe_version().unwrap();
            for p in [32003, 2147483647] {
                for generators in [
                    vec!["0"],
                    vec!["x10", "x10-1"],
                    vec!["x10*x1"],
                    vec!["2*x10-2*x1", "0", "x1^2-1", "x1^2-1"],
                ] {
                    let input = Instance::new(
                        "live",
                        "control",
                        FieldSpec::prime(p),
                        vec!["x10".into(), "x1".into()],
                        generators.into_iter().map(str::to_owned).collect(),
                        MonomialOrder::GradedReverseLexicographic,
                    );
                    let report = solver.run(&input, Task::ReducedGrobnerBasis, &limits);
                    assert!(
                        report.status.is_verified(),
                        "{p}/{mode:?}/{:?}: {:?}",
                        input.system,
                        report.status
                    );
                }
            }
            for (p, names, system) in [
                (2, vec!["x", "y"], vec!["x^3+y^3", "x+x^2+x^2*y", "y+x^2"]),
                (3, vec!["x", "y", "z"], vec!["x^2+y^2", "x*z+x*y", "y+x*y"]),
            ] {
                let input = Instance::new(
                    "known-defect",
                    "upstream-regression",
                    FieldSpec::prime(p),
                    names.into_iter().map(str::to_owned).collect(),
                    system.into_iter().map(str::to_owned).collect(),
                    MonomialOrder::GradedReverseLexicographic,
                );
                let report = solver.run(&input, Task::ReducedGrobnerBasis, &limits);
                assert!(
                    report.status.is_verified(),
                    "known defect {p}: {:?}",
                    report.status
                );
            }
            if mode == Mode::Raw {
                let input = super::super::corpus::instance(
                    "katsura-4",
                    32003,
                    MonomialOrder::GradedReverseLexicographic,
                )
                .unwrap();
                let report = solver.run(
                    &input,
                    Task::ReducedGrobnerBasis,
                    &limits.clone().with_workers(4),
                );
                assert!(report.status.is_verified(), "raw pool: {:?}", report.status);
            }
            let input = instance();
            for limits in [
                Limits::wall(Duration::ZERO),
                Limits::wall(Duration::from_secs(10)).with_max_rss_bytes(1),
            ] {
                let report = solver.run(&input, Task::ReducedGrobnerBasis, &limits);
                assert!(
                    matches!(report.status, RunStatus::StoppedByLimit(_)),
                    "{:?}",
                    report.status
                );
            }
        }
    }
}
