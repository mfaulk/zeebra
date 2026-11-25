//! The M4GB reference implementation (#1030) as an [`ExternalSolver`].
//!
//! M4GB (Makarim & Stevens, ISSAC 2017) is GPL-3.0-or-later. It runs here as a subprocess that
//! reads a text file and writes a text file; no M4GB source is reused
//! (`docs/research/external-provenance-policy.md`). `tools/external/provision-m4gb.sh` builds it
//! at [`PINNED_REVISION`].
//!
//! The variable count and the field are compile-time constants upstream, so there is one binary per
//! `(n, p)`, named by [`binary_name`]. Each carries a `.build` sidecar written by the provisioner,
//! which is how a run checks the revision it measured.
//!
//! Capabilities, all refused rather than approximated:
//! - degree-reverse-lexicographic order only;
//! - odd primes up to [`MAX_CHARACTERISTIC`]: the field keeps log tables of `2p` entries, so a
//!   31-bit prime is out of reach. `GF(2)` is refused because upstream adds the field equations,
//!   which changes the ideal.
//!
//! M4GB reports the unit ideal by throwing and exiting 1, which this adapter reads as the basis
//! `{1}` and verifies like any other. It does not always get there: on some small unit ideals the
//! pinned revision stops making progress in pair selection (`docs/research/m4gb-m5gb-reference.md`
//! §3). Such a run ends at the wall limit, and that stop is the defect, not a lower bound on M4GB's
//! time.
use super::{
    contract::generators_agree,
    process::{Invocation, Supervisor},
    Answer, ExternalSolver, Instance, LimitStop, Limits, Measurement, RunFailure, RunReport,
    RunStatus, Support, Task, ToolVersion, Unsupported, Verification, ZeebraSolver,
};
use crate::MonomialOrder;
use std::{
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

/// The upstream commit `tools/external/provision-m4gb.sh` builds.
pub const PINNED_REVISION: &str = "01860a52dacb111d6e1533bc7547b2dc8f034073";

/// The largest characteristic admitted: the 16-bit field-element regime upstream targets.
pub const MAX_CHARACTERISTIC: u64 = 65_521;

/// The binary the provisioner builds for `n` variables over `GF(p)`.
pub fn binary_name(n: usize, p: u64) -> String {
    format!("m4gb_n{n}_gf{p}")
}

fn invalid(detail: impl Into<String>) -> RunFailure {
    RunFailure::SelfInconsistent {
        detail: detail.into(),
    }
}

/// The input file: field, explicit variable names (so M4GB's order is the instance's), generators.
fn input_text(instance: &Instance) -> String {
    let mut text = format!(
        "$fieldsize {}\n$vars {}\n",
        instance.field.characteristic,
        instance.variables.join(" ")
    );
    for generator in &instance.system {
        text.push_str(generator);
        text.push('\n');
    }
    text
}

/// The basis file: one monic polynomial per line.
fn parse_basis(text: &str) -> Result<Vec<String>, RunFailure> {
    let basis: Vec<String> = text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect();
    if basis.is_empty() {
        return Err(invalid("empty basis file"));
    }
    Ok(basis)
}

/// M4GB's own figures from its log: algorithm time (`total time`) and process CPU time.
fn engine_stages(log: &str) -> Vec<(String, Duration)> {
    let seconds = |marker: &str| {
        log.lines().find_map(|line| {
            let (_, value) = line.split_once(marker)?;
            let value = value
                .trim_start_matches([' ', ':'])
                .trim_end_matches(['s', ' ']);
            value.trim().parse::<f64>().ok()
        })
    };
    [
        ("total time", "engine-solve"),
        ("Total CPU time", "engine-cpu"),
        ("total update time", "engine-update"),
        ("total matrix time", "engine-matrix"),
        ("total selection time", "engine-selection"),
    ]
    .into_iter()
    .filter_map(|(marker, name)| Some((name.into(), Duration::from_secs_f64(seconds(marker)?))))
    .collect()
}

/// M4GB's per-iteration counters, folded from its `--loglevel 3` log.
///
/// Each iteration logs `#b` (basis size), `#cp` (pending critical pairs), `#mr` (entries in the
/// store of tail-reduced multiples, keyed by leading monomial; entries are computed lazily, so this
/// counts entries, not materialized rows) and `#mc` (the dense tail width: monomials no basis
/// element reduces), after each of its update, matrix and selection phases.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct M4gbCounters {
    /// Selection phases run.
    pub rounds: u64,
    /// Highest pair lcm degree selected.
    pub max_lcm_degree: u64,
    /// New polynomials returned by selection, summed over rounds.
    pub polynomials_added: u64,
    /// Largest basis before the final interreduction.
    pub peak_basis: u64,
    /// Basis size at the last logged iteration: the final basis on a normal exit, but not on the
    /// unit-ideal exit, which throws before the basis is reduced to `{1}`.
    pub final_basis: u64,
    /// Most critical pairs pending at once.
    pub peak_pairs: u64,
    /// Most entries in the store of multiples at once.
    pub peak_store: u64,
    /// Widest dense tail representation.
    pub peak_dense_columns: u64,
}

impl M4gbCounters {
    /// `None` when the log holds no iteration line.
    pub fn parse(log: &str) -> Option<Self> {
        let field = |line: &str, key: &str| -> Option<u64> {
            let (_, rest) = line.split_once(key)?;
            rest.split_whitespace().next()?.parse().ok()
        };
        let mut c = Self::default();
        let mut seen = false;
        for line in log.lines() {
            let Some(body) = line.strip_prefix("[m4gb]") else {
                continue;
            };
            let body = body.trim_start();
            if let Some(d) = field(body, "P lcmdegree=") {
                c.max_lcm_degree = c.max_lcm_degree.max(d);
            } else if let Some(added) = field(body, "P #n:") {
                c.rounds += 1;
                c.polynomials_added += added;
            } else if let Some(b) = field(body, "#b:") {
                seen = true;
                c.peak_basis = c.peak_basis.max(b);
                c.final_basis = b;
                c.peak_pairs = c.peak_pairs.max(field(body, "#cp:")?);
                c.peak_store = c.peak_store.max(field(body, "#mr:")?);
                c.peak_dense_columns = c.peak_dense_columns.max(field(body, "#mc:")?);
            }
        }
        seen.then_some(c)
    }
}

/// Whether M4GB's exception handler reported the unit ideal. Upstream throws
/// `contradiction: I=(1)` or `contradiction: 1=0` and exits 1; its reduced basis is `{1}`.
fn reports_unit_ideal(log: &str) -> bool {
    let mut lines = log.lines().map(str::trim);
    while let Some(line) = lines.next() {
        if line == "Caught exception:" {
            return matches!(
                lines.next(),
                Some("contradiction: I=(1)" | "contradiction: 1=0")
            );
        }
    }
    false
}

/// The sidecar's `revision=` line, which must name [`PINNED_REVISION`].
fn sidecar_identity(text: &str) -> Result<String, RunFailure> {
    let revision = text
        .lines()
        .find_map(|line| line.strip_prefix("revision="))
        .ok_or_else(|| invalid("build sidecar names no revision"))?;
    if revision.trim() != PINNED_REVISION {
        return Err(invalid(format!("unpinned M4GB revision {revision}")));
    }
    Ok(text.lines().collect::<Vec<_>>().join(";"))
}

fn verify_basis(
    basis: Vec<String>,
    trusted: &Answer,
    modulus: u64,
) -> Result<RunStatus, RunFailure> {
    let reference = trusted
        .basis
        .as_ref()
        .ok_or_else(|| invalid("missing trusted basis for verification"))?;
    generators_agree(reference, &basis, modulus)
        .map_err(|_| invalid("full reduced basis disagrees with independent Zeebra computation"))?;
    let answer = Answer::from_invariants(trusted.invariants.clone()).with_basis(basis);
    let verification = Verification::of("zeebra", &answer.invariants, &trusted.invariants)
        .map_err(|_| invalid("invariants disagree with the trusted basis"))?
        .with_note("full monic reduced basis agrees coefficient for coefficient with Zeebra; verification excluded from child solve time");
    Ok(RunStatus::Verified(answer, verification))
}

/// Pinned M4GB binaries in one directory, one per `(n, p)`.
#[derive(Debug, Clone)]
pub struct M4gbSolver {
    directory: PathBuf,
    work_dir: PathBuf,
    runs: u64,
    reference: ZeebraSolver,
    last_counters: Option<M4gbCounters>,
}

impl M4gbSolver {
    /// The iteration counters of the most recent run, if its log had any.
    pub fn last_counters(&self) -> Option<M4gbCounters> {
        self.last_counters
    }

    /// The Zeebra solver every basis is verified against, for widths the stock adapter lacks.
    pub fn with_reference(mut self, reference: ZeebraSolver) -> Self {
        self.reference = reference;
        self
    }

    /// Binaries are looked up in `directory`; scratch files go to `work_dir`.
    /// # Errors
    /// Returns a harness failure if the scratch directory cannot be created.
    pub fn new(
        directory: impl Into<PathBuf>,
        work_dir: impl Into<PathBuf>,
    ) -> Result<Self, RunFailure> {
        let work_dir = work_dir.into();
        std::fs::create_dir_all(&work_dir)?;
        Ok(Self {
            directory: directory.into(),
            work_dir,
            runs: 0,
            reference: ZeebraSolver::new(),
            last_counters: None,
        })
    }

    /// Read `ZEEBRA_M4GB_DIR`, defaulting to `$ZEEBRA_EXT_PREFIX/bin` (or `~/.local/opt/zeebra-ext/bin`).
    /// # Errors
    /// As [`Self::new`].
    pub fn from_env(work_dir: impl Into<PathBuf>) -> Result<Self, RunFailure> {
        let directory = std::env::var("ZEEBRA_M4GB_DIR").unwrap_or_else(|_| {
            let prefix = std::env::var("ZEEBRA_EXT_PREFIX").unwrap_or_else(|_| {
                format!(
                    "{}/.local/opt/zeebra-ext",
                    std::env::var("HOME").unwrap_or_default()
                )
            });
            format!("{prefix}/bin")
        });
        Self::new(directory, work_dir)
    }

    fn binary(&self, instance: &Instance) -> PathBuf {
        self.directory.join(binary_name(
            instance.variables.len(),
            instance.field.characteristic,
        ))
    }

    /// The pinned build identity of the binary serving `instance`.
    /// # Errors
    /// The sidecar is missing or names another revision.
    pub fn version_for(&self, instance: &Instance) -> Result<ToolVersion, RunFailure> {
        let sidecar = sidecar_path(&self.binary(instance));
        let text = std::fs::read_to_string(&sidecar)
            .map_err(|_| invalid(format!("no build sidecar at {}", sidecar.display())))?;
        Ok(ToolVersion::new(self.id(), "1.0.0").with_build(sidecar_identity(&text)?))
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
        if let Ok(version) = self.version_for(instance) {
            report = report.with_version(version);
        }
        if let Some(command) = command {
            report = report.with_command_line(command);
        }
        report
    }
}

fn sidecar_path(binary: &Path) -> PathBuf {
    let mut name = binary.as_os_str().to_owned();
    name.push(".build");
    PathBuf::from(name)
}

impl ExternalSolver for M4gbSolver {
    fn id(&self) -> &str {
        "m4gb"
    }

    /// Versions are per binary; this reports the sidecar of the `n = 2`, `GF(31)` smoke binary.
    fn probe_version(&mut self) -> Result<ToolVersion, RunFailure> {
        let probe = Instance::new(
            "probe",
            "probe",
            super::FieldSpec::prime(31),
            vec!["x1".into(), "x2".into()],
            vec![],
            MonomialOrder::GradedReverseLexicographic,
        );
        self.version_for(&probe)
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
        let p = instance.field.characteristic;
        if !(3..=MAX_CHARACTERISTIC).contains(&p) {
            return Support::No(Unsupported::Representation {
                detail: format!(
                    "M4GB serves odd primes up to {MAX_CHARACTERISTIC} (2p-entry log tables; GF(2) adds field equations)"
                ),
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
        self.runs += 1;
        self.last_counters = None;
        let input = self.work_dir.join(format!("{}.in", self.runs));
        let basis_path = self.work_dir.join(format!("{}.basis", self.runs));
        let log = self.work_dir.join(format!("{}.log", self.runs));
        let binary = self.binary(instance);
        let invocation = Invocation::new(binary.to_string_lossy(), &self.work_dir, &log)
            .args(["-s", "--default", "--loglevel", "3", "--nrthreads"])
            .arg(limits.workers.max(1).to_string())
            .arg("-i")
            .arg(&input)
            .arg("-o")
            .arg(&basis_path);
        let command = Some(invocation.command_line());
        let mut measurement = Measurement::unmeasured();
        let result = (|| -> Result<RunStatus, RunFailure> {
            if let Some(absent) = invocation.unavailable() {
                return Err(absent.into());
            }
            self.version_for(instance)?;
            std::fs::write(&input, input_text(instance))?;
            let process = Supervisor::new(limits.wall)
                .with_max_rss_bytes(limits.max_rss_bytes)
                .run(&invocation)?;
            measurement = Measurement::of_process(&process);
            if process.memory_limited {
                return Ok(RunStatus::StoppedByLimit(LimitStop::Memory {
                    limit: limits.max_rss_bytes.unwrap_or(0),
                    observed: process.peak_rss_bytes,
                }));
            }
            if process.timed_out {
                return Ok(RunStatus::StoppedByLimit(LimitStop::WallClock {
                    limit: limits.wall,
                    elapsed: process.wall,
                }));
            }
            let text = super::read_output(&log);
            measurement.stages = engine_stages(&text);
            self.last_counters = M4gbCounters::parse(&text);
            let basis = if process.succeeded() {
                parse_basis(&std::fs::read_to_string(&basis_path)?)?
            } else if process.exit_code == Some(1) && reports_unit_ideal(&text) {
                vec!["1".to_string()]
            } else {
                return Err(RunFailure::NonZeroExit {
                    code: process.exit_code,
                });
            };
            let start = Instant::now();
            let trusted = self.reference.clone().run(
                instance,
                task,
                &Limits {
                    workers: 1,
                    ..limits.clone()
                },
            );
            let status = match trusted.status.answer() {
                Some(reference) => verify_basis(basis, reference, instance.field.characteristic),
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
        .with_log_path(log)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grobner::external::{FieldSpec, Invariants};

    fn instance(p: u64, order: MonomialOrder) -> Instance {
        Instance::new(
            "two-points",
            "control",
            FieldSpec::prime(p),
            vec!["x1".into(), "x2".into()],
            vec!["x1^2+27".into(), "x2^2+22".into(), "x1*x2+25".into()],
            order,
        )
    }

    // The input names every variable explicitly, so M4GB's order is the instance's.
    #[test]
    fn test_the_input_declares_field_and_variables() {
        let text = input_text(&instance(31, MonomialOrder::GradedReverseLexicographic));
        assert_eq!(
            text,
            "$fieldsize 31\n$vars x1 x2\nx1^2+27\nx2^2+22\nx1*x2+25\n"
        );
    }

    // Lex, extension fields, 31-bit primes and GF(2) are refused, not approximated.
    #[test]
    fn test_unsupported_shapes_are_refused() {
        let solver = M4gbSolver::new("/missing", std::env::temp_dir()).unwrap();
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        assert_eq!(
            solver.supports(&instance(32003, grevlex), Task::ReducedGrobnerBasis),
            Support::Yes
        );
        for refused in [
            instance(31, MonomialOrder::Lexicographic),
            instance(2_147_483_647, grevlex),
            instance(2, grevlex),
        ] {
            assert!(matches!(
                solver.supports(&refused, Task::ReducedGrobnerBasis),
                Support::No(_)
            ));
        }
        assert!(matches!(
            solver.supports(&instance(31, grevlex), Task::LexBasis),
            Support::No(_)
        ));
    }

    // M4GB's own timing lines are read; an absent line is absent, not zero.
    #[test]
    fn test_engine_stages_are_read_from_the_log() {
        let log = "[m4gb]  total time          : 8.2e-05s\nTotal CPU time : 0.003181 s\nPeak memory    : 7 MiB\n";
        let stages = engine_stages(log);
        assert_eq!(stages.len(), 2);
        assert_eq!(stages[0].0, "engine-solve");
        assert_eq!(stages[0].1, Duration::from_secs_f64(8.2e-05));
        assert_eq!(stages[1].1, Duration::from_secs_f64(0.003181));
        assert!(engine_stages("nothing").is_empty());
    }

    /// A real `--loglevel 3` log: n = 14, m = 25, GF(31), planted, one thread, pinned revision.
    const ITERATION_LOG: &str = "\
[m4gb]  I 0 0 25 0
[m4gb]  U #b:  25 #cp:    94 #mr:   25 #mc:  120 s=0.000138051
[m4gb]  M #b:  25 #cp:    94 #mr:   25 #mc:   95 s=8.296e-06
[m4gb]  P lcmdegree=3
[m4gb]  P #b:  25 #cp:     0 #mr:  281 #mc:  399 s=0.00433722
[m4gb]  P #n:94
[m4gb]  U #b: 119 #cp:   825 #mr:  375 #mc:  399 s=0.00289277
[m4gb]  M #b: 119 #cp:   825 #mr:  375 #mc:  305 s=1.7493e-05
[m4gb]  P lcmdegree=4
[m4gb]  P #b: 119 #cp:   313 #mr: 2340 #mc:  720 s=0.107379
[m4gb]  P #n:360
[m4gb]  U #b: 479 #cp:  4702 #mr: 2700 #mc:  720 s=0.044014
[m4gb]  M #b: 479 #cp:  4702 #mr: 2700 #mc:  360 s=7.5403e-05
[m4gb]  P lcmdegree=4
[m4gb]  P #b: 479 #cp:  4389 #mr: 2700 #mc:  360 s=0.0651819
[m4gb]  P #n:0
[m4gb]  U #b: 479 #cp:  4389 #mr: 2700 #mc:  360 s=1.71e-07
[m4gb]  M #b: 479 #cp:  4389 #mr: 2700 #mc:  360 s=3.486e-06
[m4gb]  P lcmdegree=5
[m4gb]  P #b: 479 #cp:  3877 #mr:11213 #mc:  415 s=0.0767836
[m4gb]  P #n:14
[m4gb]  U #b:  14 #cp:     0 #mr:   14 #mc:   15 s=0.000923819
[m4gb]  M #b:  14 #cp:     0 #mr:   14 #mc:    1 s=4.879e-06
[m4gb]  upper_bound = 15 = X13^2
[m4gb]  total update time   : 0.0479688s
[m4gb]  total matrix time   : 0.000109557s
[m4gb]  total selection time: 0.253681s
[m4gb]  total time          : 0.30176s
Total CPU time : 0.313676 s
";

    // The per-iteration counters are folded into peaks and totals, including an unpadded `#mr:11213`.
    #[test]
    fn test_iteration_counters_are_read_from_the_log() {
        let c = M4gbCounters::parse(ITERATION_LOG).expect("an iteration log");
        assert_eq!(c.rounds, 4);
        assert_eq!(c.max_lcm_degree, 5);
        assert_eq!(c.polynomials_added, 94 + 360 + 14);
        assert_eq!(c.peak_basis, 479);
        assert_eq!(c.final_basis, 14);
        assert_eq!(c.peak_pairs, 4702);
        assert_eq!(c.peak_store, 11213);
        assert_eq!(c.peak_dense_columns, 720);
    }

    // A log with no iteration lines (unit ideal, crash, a tool that never started) has no counters.
    #[test]
    fn test_iteration_counters_are_absent_without_iteration_lines() {
        assert_eq!(
            M4gbCounters::parse("Caught exception:\ncontradiction: I=(1)\n"),
            None
        );
        assert_eq!(M4gbCounters::parse(""), None);
    }

    // M4GB's three phase totals are reported as stages beside the solve and CPU totals.
    #[test]
    fn test_phase_totals_are_read_as_stages() {
        let stages = engine_stages(ITERATION_LOG);
        let names: Vec<&str> = stages.iter().map(|(k, _)| k.as_str()).collect();
        assert_eq!(
            names,
            [
                "engine-solve",
                "engine-cpu",
                "engine-update",
                "engine-matrix",
                "engine-selection"
            ]
        );
        assert_eq!(stages[4].1, Duration::from_secs_f64(0.253681));
    }

    // M4GB reports the unit ideal by an exception and exit 1; only its own two messages count.
    #[test]
    fn test_the_unit_ideal_is_read_from_the_exception() {
        assert!(reports_unit_ideal(
            "[m4gb] P lcmdegree=3\nCaught exception:\ncontradiction: I=(1)\n"
        ));
        assert!(reports_unit_ideal(
            "Caught exception:\ncontradiction: 1=0\n"
        ));
        assert!(!reports_unit_ideal("Caught exception:\nupdate(p): p = 0\n"));
        assert!(
            !reports_unit_ideal("contradiction: I=(1)\n"),
            "only as the caught exception"
        );
    }

    // A sidecar must name the pinned revision.
    #[test]
    fn test_the_sidecar_pins_the_revision() {
        let pinned = format!("revision={PINNED_REVISION}\ncxx=clang\n");
        assert!(sidecar_identity(&pinned).unwrap().contains(PINNED_REVISION));
        assert!(sidecar_identity("revision=deadbeef\n").is_err());
        assert!(sidecar_identity("cxx=clang\n").is_err());
    }

    // A wrong coefficient fails verification; the correct basis, in M4GB's spacing, passes.
    #[test]
    fn test_the_full_basis_must_agree() {
        let trusted = Answer::from_invariants(
            Invariants::none().with_leading_monomials(vec!["x1".into(), "x2^2".into()]),
        )
        .with_basis(vec!["x1+20*x2".into(), "x2^2+22".into()]);
        let good = parse_basis("x1 + 20*x2\nx2^2 + 22\n").unwrap();
        assert!(verify_basis(good, &trusted, 31).is_ok());
        let wrong = parse_basis("x1 + 21*x2\nx2^2 + 22\n").unwrap();
        assert!(verify_basis(wrong, &trusted, 31).is_err());
        assert!(parse_basis("\n").is_err());
    }

    // An absent binary is unavailable, not a resource stop.
    #[test]
    fn test_a_missing_binary_is_unavailable() {
        let dir = std::env::temp_dir().join(format!("m4gb-missing-{}", std::process::id()));
        let mut solver = M4gbSolver::new("/missing", &dir).unwrap();
        let report = solver.run(
            &instance(31, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::ZERO),
        );
        assert!(
            matches!(
                report.status,
                RunStatus::Failed(RunFailure::Unavailable { .. })
            ),
            "{:?}",
            report.status
        );
        let _ = std::fs::remove_dir_all(dir);
    }
}
