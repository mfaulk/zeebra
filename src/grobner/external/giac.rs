//! Only the documented modular revlex route is exposed; GPL Giac runs as a separate process.
use super::{
    contract::generators_agree,
    process::{read_output, Invocation, Supervisor},
    Answer, ExternalSolver, Instance, Invariants, LimitStop, Limits, Measurement, RunFailure,
    RunReport, RunStatus, SingularSolver, Support, Task, ToolVersion, Unsupported, Verification,
};
use crate::MonomialOrder;
use std::{
    path::PathBuf,
    time::{Duration, Instant},
};

/// The documented F4 modular route requires p < 2^31 (Giac algorithm manual, §9.6).
pub const MAX_CHARACTERISTIC: u64 = 1 << 31;
/// The registered optimized revlex route uses fifteen variable degree slots.
pub const MAX_VARIABLES: usize = 15;

fn invalid(detail: impl Into<String>) -> RunFailure {
    RunFailure::SelfInconsistent {
        detail: detail.into(),
    }
}

// Restrict the interchange to expanded integer polynomials and rename entire identifiers.
fn translate(raw: &str, from: &[String], to: &[String]) -> Result<String, RunFailure> {
    let raw: String = raw.chars().filter(|c| !c.is_whitespace()).collect();
    if raw.is_empty() {
        return Err(invalid("empty polynomial"));
    }
    let mut output = String::new();
    let mut start = 0;
    for (end, c) in raw.char_indices().chain(std::iter::once((raw.len(), '+'))) {
        if c != '+' && c != '-' {
            continue;
        }
        if end == 0 {
            output.push(c);
            start = 1;
            continue;
        }
        if end == start {
            return Err(invalid("empty polynomial term"));
        }
        let mut degree = 0u32;
        for (index, factor) in raw[start..end].split('*').enumerate() {
            if index > 0 {
                output.push('*');
            }
            let (base, exponent) = match factor.split_once('^') {
                Some((base, n)) => (
                    base,
                    n.parse::<u32>().map_err(|_| invalid("invalid exponent"))?,
                ),
                None => (factor, 1),
            };
            if base.is_empty() {
                return Err(invalid("empty factor"));
            }
            if base.chars().all(|c| c.is_ascii_digit()) {
                base.parse::<u64>()
                    .map_err(|_| invalid("coefficient exceeds interchange range"))?;
                output.push_str(base);
            } else {
                let index = from.iter().position(|name| name == base).ok_or_else(|| {
                    invalid(format!("undeclared variable or unsupported syntax: {base}"))
                })?;
                degree = degree
                    .checked_add(exponent)
                    .filter(|d| *d <= u16::MAX as u32)
                    .ok_or_else(|| invalid("term exceeds the registered 16-bit degree route"))?;
                output.push_str(&to[index]);
            }
            if exponent > u16::MAX as u32 {
                return Err(invalid("exponent exceeds registered route"));
            }
            if factor.contains('^') {
                output.push_str(&format!("^{exponent}"));
            }
        }
        if end < raw.len() {
            output.push(c);
        }
        start = end + 1;
    }
    Ok(output)
}

fn private_variables(instance: &Instance) -> Vec<String> {
    (0..instance.variables.len())
        .map(|i| format!("zbv{i}"))
        .collect()
}

fn script(instance: &Instance, workers: usize) -> Result<String, RunFailure> {
    let variables = private_variables(instance);
    let system = instance
        .system
        .iter()
        .map(|p| translate(p, &instance.variables, &variables))
        .collect::<Result<Vec<_>, _>>()?
        .join(",");
    Ok(format!(
        "threads:={workers}:;\nproba_epsilon:=0:;\nprint(\"@giac_workers\",threads);\n\
         print(\"@giac_field\",{p});\nzbinput:=[{system}]%{p}:;\n\
         print(\"@giac_gensize\",size(zbinput));\n\
         for(zbindex:=0;zbindex<size(zbinput);zbindex++){{print(\"@giac_gen\",(zbinput%0)[zbindex]);}}:;\n\
         zbbasis:=gbasis(zbinput,[{variables}],revlex):;\n\
         print(\"@giac_size\",size(zbbasis));\n\
         for(zbindex:=0;zbindex<size(zbbasis);zbindex++){{print(\"@giac_gb\",zbbasis[zbindex]);}}:;\n\
         print(\"@giac_done\");\n",
        p=instance.field.characteristic, variables=variables.join(",")))
}

fn values<'a>(output: &'a str, marker: &str) -> Vec<&'a str> {
    output
        .lines()
        .filter_map(|line| {
            line.trim()
                .strip_prefix(marker)
                .and_then(|tail| tail.strip_prefix(','))
                .map(str::trim)
        })
        .collect()
}
fn unique<'a>(output: &'a str, marker: &str) -> Result<&'a str, RunFailure> {
    let found = values(output, marker);
    match found.as_slice() {
        [value] => Ok(value),
        _ => Err(invalid(format!("missing or duplicated marker {marker}"))),
    }
}
fn integer(output: &str, marker: &str) -> Result<u64, RunFailure> {
    unique(output, marker)?
        .parse()
        .map_err(|_| invalid(format!("invalid integer {marker}")))
}

fn parse_answer(output: &str, instance: &Instance, workers: usize) -> Result<Answer, RunFailure> {
    if output
        .lines()
        .filter(|line| line.trim() == "@giac_done")
        .count()
        != 1
        || output.contains("Error:")
        || integer(output, "@giac_field")? != instance.field.characteristic
        || integer(output, "@giac_workers")? != workers as u64
    {
        return Err(invalid(
            "incomplete Giac computation or wrong field/worker request",
        ));
    }
    let variables = private_variables(instance);
    let decode = |marker| {
        values(output, marker)
            .iter()
            .map(|p| translate(p, &variables, &instance.variables))
            .collect::<Result<Vec<_>, _>>()
    };
    let generators = decode("@giac_gen")?;
    if integer(output, "@giac_gensize")? != generators.len() as u64 {
        return Err(invalid("truncated generator echo"));
    }
    generators_agree(&instance.system, &generators, instance.field.characteristic)
        .map_err(|_| invalid("Giac parsed a different generator system"))?;
    let basis = decode("@giac_gb")?;
    if integer(output, "@giac_size")? != basis.len() as u64 {
        return Err(invalid("truncated basis output"));
    }
    Ok(
        Answer::from_invariants(Invariants::none().with_basis_cardinality(basis.len()))
            .with_basis(basis),
    )
}

fn verified(mut answer: Answer, trusted: &Answer, p: u64) -> Result<RunStatus, RunFailure> {
    let (Some(basis), Some(reference)) = (&answer.basis, &trusted.basis) else {
        return Err(invalid("independent full reduced basis is missing"));
    };
    generators_agree(basis, reference, p)
        .map_err(|_| invalid("full reduced basis disagrees with Singular"))?;
    let verification = Verification::of("singular", &answer.invariants, &trusted.invariants)
        .map_err(|_| invalid("basis cardinality disagrees with Singular"))?
        .with_note("full monic reduced basis agrees coefficient for coefficient; independent verification excluded from Giac child wall time and reported separately");
    answer.invariants = trusted.invariants.clone();
    Ok(RunStatus::Verified(answer, verification))
}

/// Giac's modular revlex subprocess, with exact independent Singular verification.
#[derive(Clone, Debug)]
pub struct GiacSolver {
    binary: String,
    work_dir: PathBuf,
    runs: u64,
    version: Option<ToolVersion>,
}
impl GiacSolver {
    /// Create scratch storage; missing executables are reported when probed or run.
    /// # Errors
    /// Returns a harness failure if scratch storage cannot be created.
    pub fn new(
        binary: impl Into<String>,
        work_dir: impl Into<PathBuf>,
    ) -> Result<Self, RunFailure> {
        let work_dir = work_dir.into();
        std::fs::create_dir_all(&work_dir)?;
        let binary = binary.into();
        let binary = if binary.contains('/') {
            std::fs::canonicalize(&binary)
                .map(|p| p.to_string_lossy().into_owned())
                .unwrap_or(binary)
        } else {
            binary
        };
        Ok(Self {
            binary,
            work_dir: std::fs::canonicalize(work_dir)?,
            runs: 0,
            version: None,
        })
    }
    /// Read `ZEEBRA_GIAC`, defaulting to `icas` on PATH.
    /// # Errors
    /// Returns the scratch storage errors from [`Self::new`].
    pub fn from_env(work_dir: impl Into<PathBuf>) -> Result<Self, RunFailure> {
        Self::new(
            std::env::var("ZEEBRA_GIAC").unwrap_or_else(|_| "icas".into()),
            work_dir,
        )
    }
    /// Measure an empty script in the same interpreter, without computing a basis.
    /// # Errors
    /// Returns process failures or rejects a missing version marker.
    pub fn startup_measurement(&mut self, limits: &Limits) -> Result<Measurement, RunFailure> {
        let (input, output) = self.paths();
        std::fs::write(&input, "print(\"@giac_version\",version());\n")?;
        let process = Supervisor::new(limits.wall)
            .with_max_rss_bytes(limits.max_rss_bytes)
            .run(&self.invocation(&input, &output))?;
        if !process.succeeded() {
            return Err(RunFailure::NonZeroExit {
                code: process.exit_code,
            });
        }
        unique(&read_output(&output), "@giac_version")?;
        Ok(Measurement::of_process(&process))
    }
    fn check_with_singular(
        &self,
        answer: Answer,
        instance: &Instance,
        limits: &Limits,
        binary: &str,
    ) -> Result<RunStatus, RunFailure> {
        use crate::grobner::differential::singular::error_line;
        let directory = self.work_dir.join(format!("verify-{}", self.runs));
        let oracle = SingularSolver::with_binary(binary, &directory, limits.wall)?;
        let input = directory.join("basis.sing");
        let output = directory.join("basis.out");
        std::fs::write(&input, oracle.script(instance, Task::ReducedGrobnerBasis))?;
        let invocation = Invocation::new(binary, &directory, &output)
            .arg("-q")
            .arg("--no-warn")
            .arg(&input);
        let process = Supervisor::new(limits.wall)
            .with_max_rss_bytes(limits.max_rss_bytes)
            .run(&invocation)?;
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
        let raw = read_output(&output);
        if error_line(&raw).is_some() || !raw.lines().any(|line| line.trim() == "@done") {
            return Err(invalid(
                "independent Singular verification did not complete",
            ));
        }
        let trusted = oracle.answer(&raw, Task::ReducedGrobnerBasis)?;
        verified(answer, &trusted, instance.field.characteristic)
    }
    fn invocation(&self, input: &std::path::Path, output: &std::path::Path) -> Invocation {
        let invocation = Invocation::new(&self.binary, &self.work_dir, output).arg(input);
        match std::env::var("ZEEBRA_GIAC_LIBRARY_PATH") {
            Ok(path) => invocation.env("LD_LIBRARY_PATH", path),
            Err(_) => invocation,
        }
    }
    fn paths(&mut self) -> (PathBuf, PathBuf) {
        self.runs += 1;
        (
            self.work_dir.join(format!("{}.cas", self.runs)),
            self.work_dir.join(format!("{}.out", self.runs)),
        )
    }
}
impl ExternalSolver for GiacSolver {
    fn id(&self) -> &str {
        "giac"
    }
    fn probe_version(&mut self) -> Result<ToolVersion, RunFailure> {
        let (input, output) = self.paths();
        std::fs::write(&input, "print(\"@giac_version\",version());\n")?;
        let invocation = self.invocation(&input, &output);
        let process = Supervisor::new(Duration::from_secs(10)).run(&invocation)?;
        if !process.succeeded() {
            return Err(RunFailure::NonZeroExit {
                code: process.exit_code,
            });
        }
        let raw = read_output(&output);
        let value = unique(&raw, "@giac_version")?;
        if !value.starts_with("giac ") {
            return Err(invalid("unrecognized Giac version"));
        }
        let version = ToolVersion::new(self.id(), value).with_raw(raw.clone());
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
        if task != Task::ReducedGrobnerBasis {
            return Support::No(Unsupported::Task { task });
        }
        if instance.order != MonomialOrder::GradedReverseLexicographic {
            return Support::No(Unsupported::Order {
                order: instance.order,
            });
        }
        if instance.field.characteristic >= MAX_CHARACTERISTIC {
            return Support::No(Unsupported::Characteristic {
                characteristic: instance.field.characteristic,
                supported_below: MAX_CHARACTERISTIC,
            });
        }
        if instance.variables.len() > MAX_VARIABLES {
            return Support::No(Unsupported::VariableCount {
                variables: instance.variables.len(),
                maximum: MAX_VARIABLES,
            });
        }
        if instance.field.characteristic < 2
            || instance.variables.is_empty()
            || instance.variables.iter().enumerate().any(|(i, v)| {
                v.is_empty()
                    || !v.as_bytes()[0].is_ascii_alphabetic()
                    || !v.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                    || instance.variables[..i].contains(v)
            })
        {
            return Support::No(Unsupported::Representation {
                detail: "requires a prime modulus and distinct polynomial identifiers".into(),
            });
        }
        match script(instance, 1) {
            Ok(_) => Support::Yes,
            Err(error) => Support::No(Unsupported::Representation {
                detail: error.to_string(),
            }),
        }
    }
    fn run(&mut self, instance: &Instance, task: Task, limits: &Limits) -> RunReport {
        if let Support::No(reason) = self.supports(instance, task) {
            return RunReport::unsupported(self.id(), instance, task, limits, reason);
        }
        if limits.workers == 0 || limits.workers > 1024 || !limits.tool_caps.is_empty() {
            return RunReport::unsupported(
                self.id(),
                instance,
                task,
                limits,
                Unsupported::Representation {
                    detail: "Giac adapter requires 1..=1024 workers and no tool-specific caps"
                        .into(),
                },
            );
        }
        let (input, output) = self.paths();
        let invocation = self.invocation(&input, &output);
        let command = invocation.command_line();
        let mut measurement = Measurement::unmeasured();
        let result = (|| -> Result<RunStatus, RunFailure> {
            if let Some(absent) = invocation.unavailable() {
                return Err(absent.into());
            }
            if self.version.is_none() {
                self.probe_version()?;
            }
            std::fs::write(&input, script(instance, limits.workers)?)?;
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
            let answer = parse_answer(&read_output(&output), instance, limits.workers)?;
            let start = Instant::now();
            let result = self.check_with_singular(
                answer,
                instance,
                limits,
                &std::env::var("ZEEBRA_SINGULAR").unwrap_or_else(|_| "Singular".into()),
            );
            measurement
                .stages
                .push(("independent-verification".into(), start.elapsed()));
            result
        })();
        let status = result.unwrap_or_else(RunStatus::Failed);
        let mut report = RunReport::new(self.id(), instance, task, limits, status, measurement)
            .with_command_line(command)
            .with_log_path(output);
        if let Some(version) = &self.version {
            report = report.with_version(version.clone());
        }
        report
    }
}

#[cfg(test)]
mod tests {
    use super::super::FieldSpec;
    use super::*;

    fn instance() -> Instance {
        Instance::new(
            "giac-control",
            "control",
            FieldSpec::prime(32003),
            vec!["x1".into(), "x10".into()],
            vec!["x1^2-1".into(), "x10-x1".into()],
            MonomialOrder::GradedReverseLexicographic,
        )
    }

    fn output() -> &'static str {
        "// banner\n@giac_field,32003\n@giac_workers,2\n@giac_gensize,2\n@giac_gen,zbv0^2-1\n@giac_gen,zbv1-zbv0\n@giac_size,2\n@giac_gb,zbv1^2-1\n@giac_gb,zbv0-zbv1\n@giac_done\n"
    }

    // The modular route accepts both board primes and refuses wide fields and other tasks.
    #[test]
    fn capability_bounds_are_explicit() {
        let solver = GiacSolver::from_env(std::env::temp_dir().join("giac-capability")).unwrap();
        let mut input = instance();
        assert_eq!(
            solver.supports(&input, Task::ReducedGrobnerBasis),
            Support::Yes
        );
        input.field = FieldSpec::prime(2147483647);
        assert_eq!(
            solver.supports(&input, Task::ReducedGrobnerBasis),
            Support::Yes
        );
        input.field = FieldSpec::prime(18446744069414584321);
        assert!(matches!(
            solver.supports(&input, Task::ReducedGrobnerBasis),
            Support::No(Unsupported::Characteristic { .. })
        ));
        assert!(matches!(
            solver.supports(&instance(), Task::LexBasisByConversion),
            Support::No(Unsupported::Task { .. })
        ));
    }

    // Whole identifier translation keeps x1 distinct from x10 and avoids interpreter builtins.
    #[test]
    fn script_uses_private_variables_and_requested_workers() {
        let script = script(&instance(), 2).unwrap();
        assert!(script.contains("threads:=2"));
        assert!(script.contains("[zbv0^2-1,zbv1-zbv0]%32003"));
        assert!(script.contains("gbasis(zbinput,[zbv0,zbv1],revlex)"));
        assert!(!script.contains("x10"));
    }

    // Unsupported polynomial syntax and undeclared identifiers are refused before execution.
    #[test]
    fn script_refuses_unrepresentable_input() {
        let mut input = instance();
        for invalid in ["x1;quit()", "x2+1", "x1^-1", "x1^65536", "x1/2"] {
            input.system[0] = invalid.into();
            assert!(script(&input, 1).is_err(), "{invalid}");
        }
    }

    // A complete report round-trips generators and restores every output variable name.
    #[test]
    fn completed_answer_preserves_full_basis() {
        let answer = parse_answer(output(), &instance(), 2).unwrap();
        assert_eq!(answer.basis.unwrap(), ["x10^2-1", "x1-x10"]);
        assert_eq!(answer.invariants.basis_cardinality, Some(2));
    }

    // Zero-exit reports with missing completion, wrong ring, workers or generator echoes fail.
    #[test]
    fn partial_or_wrong_problem_reports_fail() {
        for bad in [
            output().replace("@giac_done", ""),
            output().replace("@giac_field,32003", "@giac_field,13"),
            output().replace("@giac_workers,2", "@giac_workers,1"),
            output().replace("@giac_gen,zbv0^2-1", "@giac_gen,zbv0^2-2"),
            output().replace("@giac_size,2", "@giac_size,3"),
            output().replace("zbv1^2-1", "gbasis(zbinput,[zbv0],revlex)"),
        ] {
            assert!(parse_answer(&bad, &instance(), 2).is_err(), "{bad}");
        }
    }

    // Full-basis verification rejects a wrong coefficient despite matching cardinality.
    #[test]
    fn exact_verification_rejects_tampering() {
        let answer = parse_answer(output(), &instance(), 2).unwrap();
        let mut trusted = answer.clone();
        trusted.basis.as_mut().unwrap()[0] = "x10^2-2".into();
        assert!(verified(answer, &trusted, 32003).is_err());
    }

    // Live modular bases agree exactly with Singular across both board primes and degenerate ideals.
    #[test]
    #[ignore = "requires Giac and Singular; run with ZEEBRA_GIAC set"]
    fn live_giac_bases_agree() {
        let mut solver = GiacSolver::from_env(
            std::env::temp_dir().join(format!("giac-live-{}", std::process::id())),
        )
        .unwrap();
        solver.probe_version().unwrap();
        for p in [32003, 2147483647] {
            for system in [
                vec!["x1^2-1".into(), "x10-x1".into()],
                vec!["0".into()],
                vec!["1".into()],
            ] {
                let mut input = instance();
                input.field = FieldSpec::prime(p);
                input.system = system;
                let report = solver.run(
                    &input,
                    Task::ReducedGrobnerBasis,
                    &Limits::wall(Duration::from_secs(10))
                        .with_max_rss_bytes(2 * 1024 * 1024 * 1024),
                );
                assert!(
                    matches!(report.status, RunStatus::Verified(..)),
                    "{:?}",
                    report.status
                );
            }
        }
    }

    // The independent verifier is also stopped before exceeding its declared memory ceiling.
    #[test]
    #[cfg(target_os = "linux")]
    fn verification_obeys_memory_ceiling() {
        use std::os::unix::fs::PermissionsExt;
        let root = std::env::temp_dir().join(format!("giac-verifier-limit-{}", std::process::id()));
        let solver = GiacSolver::new("unused", &root).unwrap();
        let binary = root.join("slow-verifier");
        std::fs::write(&binary, "#!/bin/sh\nexec sleep 5\n").unwrap();
        std::fs::set_permissions(&binary, std::fs::Permissions::from_mode(0o700)).unwrap();
        let answer = parse_answer(output(), &instance(), 2).unwrap();
        let status = solver
            .check_with_singular(
                answer,
                &instance(),
                &Limits::wall(Duration::from_secs(2)).with_max_rss_bytes(0),
                binary.to_str().unwrap(),
            )
            .unwrap();
        assert!(matches!(
            status,
            RunStatus::StoppedByLimit(LimitStop::Memory { .. })
        ));
        std::fs::remove_dir_all(root).unwrap();
    }

    // Missing executables remain unavailable rather than a measured failure or limit stop.
    #[test]
    fn absent_binary_is_unavailable() {
        let mut solver = GiacSolver::new(
            "/definitely/absent/icas",
            std::env::temp_dir().join("giac-absent"),
        )
        .unwrap();
        assert!(matches!(
            solver.probe_version(),
            Err(RunFailure::Unavailable { .. })
        ));
    }
}
