//! Sagebrush as an [`ExternalSolver`], driven through the provisioned `sagebrush-gb-driver`.
//!
//! # Maturity: run it, and do not quote it as a baseline yet
//!
//! Sagebrush is the one permissively-licensed comparand in M25 (§ Licensing below), which makes it
//! the only one whose code Zeebra could lawfully reuse — and that is exactly why its *correctness*
//! has to be settled before its *speed* is quoted. What the source supports, at
//! `86d9f1c787030752dcaab1ddb8d99cf1b7fa5e1b`:
//!
//! * The repository is five weeks old (first commit 2026-10-02), 6864 commits, and **every
//!   `engine/*` crate is `version = "0.1.0"`** with no crate-level git tag.
//! * `engine/mpoly/src/f4.rs` is 1318 lines and carries **six** `#[test]`s; `f4q.rs` (913 lines,
//!   the default route over Q) and `sigf4.rs` carry **none**.
//! * The repository's Sage and Magma oracle trees are substantial — `sage-tests/` has 267 entries
//!   — but **two** of those files mention `groebner_basis` at all and both are two-variable toys;
//!   `magma-tests/` has no Gröbner test. There is no committed oracle run on cyclic-n or
//!   katsura-n.
//! * `engine/mpoly/src/sigf4.rs:28` claims validation "against Singular"; no such test, script or
//!   recorded output exists in the tree.
//!
//! So: the F4 is real, literature-cited and free of stub markers, and its correctness is
//! established on exactly one system in the provisioning smoke test. **A row from this adapter is
//! `Complete`, never self-certified, and belongs in the results table marked unverified until it
//! has agreed with Zeebra and Singular across the corpus.** A fast wrong answer is not a
//! competitive result.
//!
//! # What the driver exposes, and what Sagebrush has that it does not
//!
//! Sagebrush builds no Gröbner CLI: `engine/cli` depends on four crates that do not include
//! `mpoly` and exposes no entry point. The provisioned `sagebrush-gb-driver` — Zeebra's own MIT
//! code, built by `tools/external/provision.sh` against the pinned clone — reads an msolve-format
//! file and calls `sagebrush_mpoly::f4::groebner_p(&sys, Order::DegRevLex, p)`.
//!
//! **That driver is degrevlex-and-reduced-basis only, and the limitation is the driver's, not the
//! engine's.** Sagebrush itself has `fglm::groebner_fglm` (`engine/mpoly/src/fglm.rs:325`,
//! capped at `p < 2^31` by `:329`) and a lex route by homogenize → DegLex → dehomogenize
//! (`engine/mpoly/src/f4.rs:491-547`), and computes a quotient-space dimension internally
//! (`fglm.rs:97`) without exposing it. None of that is reachable here, so [`Self::supports`]
//! refuses every other task and order outright rather than approximating one with another.
//!
//! # The leading-monomial trap, handled in the driver
//!
//! Sagebrush keeps a polynomial's terms in decreasing **lex** order of the packed exponent word
//! whatever the monomial order is (`engine/mpoly/src/order.rs:58-60` puts variable 0 in the
//! highest field, so a plain unsigned word compare *is* a lex compare). For degrevlex the first
//! stored term is therefore **not** the leading term: on the provisioning smoke system the second
//! basis element stores as `x*z + … + z^4 + …`, whose degrevlex leading monomial is `z^4`.
//!
//! The driver computes leading terms with the public `Packing::key(o, w)`
//! (`engine/mpoly/src/order.rs:104-125`, which builds degrevlex as degree-then-complemented-and-
//! field-reversed) and prints them in a `--- leading monomials ---` section, so this adapter reads
//! that section rather than taking a first term. Taking `exps[0]` yields a plausible-looking and
//! entirely wrong leading-monomial list — the first version of the driver did exactly that, and
//! only the four-way agreement caught it.
//!
//! # Above `p = 2^31` nothing can check this tool
//!
//! msolve and Singular both stop at `p <= 2^31 - 1`. Sagebrush and Groebner.jl are the only
//! comparands that accept a larger prime, so between `2^31` and this adapter's
//! [`MAX_CHARACTERISTIC`] the only available corroboration is Groebner.jl — two implementations
//! agreeing with each other and nothing else. Such a run stays [`RunStatus::Complete`]. Combined
//! with the maturity note above, a 64-bit Sagebrush row is the weakest evidence this module
//! produces and must be labelled as such.
//!
//! # Two measurement caveats that are properties of the engine
//!
//! 1. **Above `p = 2^31` the elimination is single-threaded.** `engine/mpoly/src/f4.rs:219`
//!    switches on the modulus: below 2^31 it uses the Faugère–Lachartre sparse elimination in
//!    `engine/arith/src/spelim.rs`, which is row-parallel past 32 rows (`f4.rs:317`); at or above
//!    2^31 it uses the dense accumulator in `reduce_rows` (`f4.rs:233-278`), which has no
//!    parallelism at all. A `workers = 64` figure at a 64-bit prime is therefore a serial figure,
//!    and comparing it with a `workers = 64` figure at a 31-bit prime compares two different
//!    implementations.
//! 2. **The elimination strategy is chosen by a cost model that reads `is_x86_feature_detected!
//!    ("avx2")`** (`engine/arith/src/spelim.rs:381-384`), so the same input can take a different
//!    route on different hardware. This adapter deliberately **does not** pin `SB_F4_FL`: that
//!    would measure something no user of Sagebrush gets. It records the machine instead, and
//!    refuses to run if the variable is already set — see [`PINNED_SWITCHES`].
//!
//! # Licensing
//!
//! `NOTICE.md:3` is `Copyright (c) 2026 SageMath, Inc.`, `NOTICE.md:5-9` grants Apache-2.0 **or**
//! MIT at the licensee's option, and `engine/mpoly/Cargo.toml:5` is `license = "MIT OR
//! Apache-2.0"`. `NOTICE.md:16-18` states that nothing in Sagebrush is derived from GPL software.
//! So this is the "reuse permitted" class of `docs/research/external-provenance-policy.md` §2 —
//! and **nothing is reused here**: the driver calls a public library function across a crate
//! boundary and copies no code, so §8.1's notice obligation is not engaged. See
//! `docs/research/sagebrush-implementation.md` for what reuse *would* require.

use std::time::Duration;

use super::{
    contract::{
        Answer, ExternalSolver, Instance, Invariants, LimitStop, Limits, Measurement, RunFailure,
        RunReport, RunStatus, Support, Task, ToolVersion, Unsupported,
    },
    process::{read_output, Invocation, Supervisor},
};
use crate::MonomialOrder;

/// The commit the provisioned driver was built against.
///
/// **Not self-reported.** The driver prints an engine name and no version, and Sagebrush has no
/// crate-level tag to report — every `engine/*` crate is `0.1.0`. This constant is the pin
/// asserted by `tools/external/provision.sh`, carried into [`ToolVersion::build`] so that a record
/// says which tree produced it, and it is the adapter's claim rather than the tool's.
pub const PROVISIONED_COMMIT: &str = "86d9f1c787030752dcaab1ddb8d99cf1b7fa5e1b";

/// The largest modulus Sagebrush's own entry point accepts.
///
/// `engine/mpoly/src/lib.rs:1552-1554` rejects anything outside `[2, 2^62)`:
///
/// ```text
/// if pm < 2 || pm >= 1 << 62 {
///     return Err("the modulus must be in [2, 2^62)".into());
/// }
/// ```
///
/// and `engine/mpoly/src/sparse.rs:5` documents `Fp` as "GF(p), p < 2^62". The gate sits on
/// `call()`, which the driver bypasses by calling `f4::groebner_p` directly — so **this adapter
/// has to enforce Sagebrush's own bound on Sagebrush's behalf**, and that is why it is a constant
/// here. Past it the failure is silent rather than reported: `ZPoly::reduce_mod`
/// (`engine/mpoly/src/lib.rs:1111`) reduces by `p as i64`, which is negative for `p >= 2^63`, and
/// `sparse.rs:57-63` adds two residues in a `u64` without a widening step.
///
/// This is wider than msolve's and Singular's shared 2^31 ceiling
/// (`docs/research/external-comparands.md` §3.3, §6.2) and narrower than Groebner.jl's
/// [`MAX_CHARACTERISTIC`](super::groebner_jl::MAX_CHARACTERISTIC).
pub const MAX_CHARACTERISTIC: u64 = 1 << 62;

/// The most variables the packed exponent representation can carry.
///
/// Sagebrush packs every exponent into one `u64` with `bits` bits each, `ZPoly` holding the
/// invariant `n * bits <= 64` (`engine/mpoly/src/lib.rs:100-101`), and `f4::bits_range`
/// (`engine/mpoly/src/f4.rs:660-666`) caps `bits` at `64 / n`. The top bit of every field is a
/// **guard bit** used for branchless divisibility and overflow detection
/// (`engine/mpoly/src/order.rs:69-72`, and `divides` at `f4.rs:76-79`), so the usable exponent
/// range is `2^(bits - 1)`, not `2^bits`. At `n > 32` that leaves `bits = 1`, one guard bit and no
/// exponent — nothing above degree 0 can be represented.
///
/// **Useful capacity degrades well before this bound**, and that is not a capability statement: an
/// instance inside the bound whose exponents will not pack comes back as Sagebrush's own
/// `exponents too large to pack` (`f4.rs:680-682`, `:694-701`), which this adapter reports as
/// [`RunFailure::Reported`]. A bound in `supports` must describe what the tool declares, not
/// predict what a run will do.
pub const MAX_VARIABLES: usize = 32;

/// Environment variables that change which algorithm Sagebrush runs, or what it prints.
///
/// Every one is read with `env::var(..).is_ok()` — **truthy if set, so `SB_SIGF4=0` enables the
/// signature path** — except `SB_F4_FL`, which is value-compared. [`Invocation`] can set a child's
/// variables but not clear them, so an inherited one cannot be undone from here; the adapter
/// therefore refuses to run rather than produce a figure for an engine configuration it did not
/// choose.
///
/// | variable | site | effect |
/// |---|---|---|
/// | `SB_SIGF4` | `engine/mpoly/src/f4.rs:484` | tries the experimental signature-based F4 first |
/// | `SB_SIG_NOSYZ` | `engine/mpoly/src/sigf4.rs:170` | disables syzygy-signature pruning |
/// | `SB_SIG_NOREW` | `engine/mpoly/src/sigf4.rs:171` | disables the rewrite criterion |
/// | `SB_SIG_NOZERO` | `engine/mpoly/src/sigf4.rs:327` | stops recording zero reductions as syzygies |
/// | `SB_F4_FL` | `engine/mpoly/src/f4.rs:325-329` | overrides the elimination cost model |
/// | `SB_F4_DEBUG` | 24 sites from `engine/mpoly/src/f4.rs:196` | writes a stderr trace |
/// | `SB_F4_SHAPE` | `engine/mpoly/src/f4.rs:310` | writes matrix shape statistics |
///
/// The last two are a parsing hazard as much as a measurement one: the supervisor sends both of
/// the child's streams to one file, so a trace interleaves with the basis the adapter parses.
pub const PINNED_SWITCHES: &[&str] = &[
    "SB_SIGF4",
    "SB_SIG_NOSYZ",
    "SB_SIG_NOREW",
    "SB_SIG_NOZERO",
    "SB_F4_FL",
    "SB_F4_DEBUG",
    "SB_F4_SHAPE",
];

/// The variable Sagebrush takes its worker count from.
///
/// `engine/mpoly/src/lib.rs:1005` parses it as an integer and falls back to
/// `available_parallelism()` — **all 128 hardware threads on the provisioning machine** — when it
/// is unset. An unflagged Sagebrush run is therefore fully parallel where an unflagged msolve run
/// is serial (`docs/research/external-comparands.md` §3.6, §5.3), so this is set on every run.
const THREADS_VARIABLE: &str = "SAGEBRUSH_THREADS";

/// The separator the driver prints between the basis and its leading monomials.
const LEADING_SEPARATOR: &str = "--- leading monomials ---";

/// Sagebrush driven as a competitive solver, through the provisioned driver binary.
#[derive(Clone, Debug)]
pub struct SagebrushSolver {
    binary: String,
    work_dir: std::path::PathBuf,
    version: Option<ToolVersion>,
    runs: u64,
}

impl SagebrushSolver {
    /// A solver over the driver at `binary`, with scratch files under `work_dir`.
    ///
    /// # Errors
    /// [`RunFailure::Io`] if the scratch directory could not be created. A *missing* driver is not
    /// reported here, because nothing has been run yet: it surfaces from
    /// [`ExternalSolver::probe_version`] or [`ExternalSolver::run`] as
    /// [`RunFailure::Unavailable`].
    pub fn new(
        binary: impl Into<String>,
        work_dir: impl Into<std::path::PathBuf>,
    ) -> Result<Self, RunFailure> {
        let work_dir = work_dir.into();
        std::fs::create_dir_all(&work_dir)?;
        Ok(Self {
            binary: binary.into(),
            work_dir,
            version: None,
            runs: 0,
        })
    }

    /// A solver configured from the environment the provisioning script exports.
    ///
    /// `ZEEBRA_SAGEBRUSH_DRIVER` names the binary and defaults to `sagebrush-gb-driver`.
    ///
    /// # Errors
    /// As [`Self::new`].
    pub fn from_env(work_dir: impl Into<std::path::PathBuf>) -> Result<Self, RunFailure> {
        let binary = std::env::var("ZEEBRA_SAGEBRUSH_DRIVER")
            .unwrap_or_else(|_| "sagebrush-gb-driver".to_string());
        Self::new(binary, work_dir)
    }

    /// The scratch paths for the next run: the input file and the file both streams go to.
    fn scratch(&mut self, tag: &str) -> (std::path::PathBuf, std::path::PathBuf) {
        self.runs += 1;
        let stem = format!("{}-{}", tag, self.runs);
        (
            self.work_dir.join(format!("{}.ms", stem)),
            self.work_dir.join(format!("{}.out", stem)),
        )
    }

    /// The input file: msolve's three-part format, which the driver reads.
    ///
    /// Variables comma-separated on line 1 **in the instance's order**, which is what defines the
    /// monomial order and which the driver maps positionally onto exponent fields; the
    /// characteristic on line 2; then the generators comma-separated with no trailing comma
    /// (`docs/research/external-comparands.md` §3.1).
    fn input(instance: &Instance) -> String {
        format!(
            "{}\n{}\n{}\n",
            instance.variables.join(","),
            instance.field.characteristic,
            instance.system.join(",\n")
        )
    }

    /// An invocation of the driver on `input`, with the worker count set.
    fn invocation(
        &self,
        input: &std::path::Path,
        output: &std::path::Path,
        limits: &Limits,
    ) -> Invocation {
        Invocation::new(&self.binary, &self.work_dir, output)
            .arg(input)
            .env(THREADS_VARIABLE, limits.workers.max(1).to_string())
    }

    /// The first [`PINNED_SWITCHES`] entry the harness's own environment sets, if any.
    fn inherited_switch() -> Option<&'static str> {
        PINNED_SWITCHES
            .iter()
            .copied()
            .find(|name| std::env::var_os(name).is_some())
    }

    /// Parse the driver's output into an answer, checking its echoed headers against the request.
    ///
    /// The headers are the driver telling the adapter what it actually did, and checking them is
    /// what catches a mismatch that would otherwise produce a basis under the wrong order or in
    /// the wrong variables — the failure mode that does not announce itself.
    fn answer(&self, output: &str, instance: &Instance) -> Result<Answer, RunFailure> {
        let header = |name: &'static str| -> Result<&str, RunFailure> {
            output
                .lines()
                .find_map(|line| line.strip_prefix(name))
                .map(str::trim)
                .ok_or(RunFailure::MissingMarker {
                    marker: name.to_string(),
                })
        };

        let characteristic = header("#field characteristic:")?;
        if characteristic != instance.field.characteristic.to_string() {
            return Err(RunFailure::SelfInconsistent {
                detail: format!(
                    "the driver read characteristic {} where the instance declares {}",
                    characteristic, instance.field.characteristic
                ),
            });
        }
        let variables = header("#variable order:")?;
        if variables != instance.variables.join(", ") {
            return Err(RunFailure::SelfInconsistent {
                detail: format!(
                    "the driver read variables {} where the instance declares {}",
                    variables,
                    instance.variables.join(", ")
                ),
            });
        }
        let order = header("#monomial order:")?;
        if !order.starts_with("degrevlex") {
            return Err(RunFailure::SelfInconsistent {
                detail: format!("the driver computed a {} basis, not degrevlex", order),
            });
        }

        let length = header("#length of basis:")?;
        let size: usize = length
            .split_whitespace()
            .next()
            .unwrap_or_default()
            .parse()
            .map_err(|_| RunFailure::Unparsable {
                marker: "#length of basis:".to_string(),
                value: length.to_string(),
            })?;

        let (basis, leading) = Self::split_body(output, size)?;
        Ok(
            Answer::from_invariants(Invariants::none().with_leading_monomials(leading))
                .with_basis(basis),
        )
    }

    /// The basis lines and the leading-monomial lines, each checked against the reported count.
    ///
    /// Positional rather than marker-driven because the driver's format is positional, so the
    /// count check is the only defence against a truncated run being read as a shorter basis.
    fn split_body(output: &str, size: usize) -> Result<(Vec<String>, Vec<String>), RunFailure> {
        let body: Vec<&str> = output
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .collect();
        let separator = body
            .iter()
            .position(|line| *line == LEADING_SEPARATOR)
            .ok_or(RunFailure::MissingMarker {
                marker: LEADING_SEPARATOR.to_string(),
            })?;
        let basis = &body[..separator];
        let leading = &body[separator + 1..];
        if basis.len() != size || leading.len() != size {
            return Err(RunFailure::Unparsable {
                marker: "#length of basis:".to_string(),
                value: format!(
                    "{} basis and {} leading lines for a reported size of {}",
                    basis.len(),
                    leading.len(),
                    size
                ),
            });
        }
        Ok((
            basis.iter().map(|line| line.to_string()).collect(),
            leading.iter().map(|line| line.to_string()).collect(),
        ))
    }

    /// The driver-reported time of the `groebner_p` call alone.
    ///
    /// Recorded as a *stage* and never as the run's wall time: unlike Groebner.jl, whose process
    /// time is its compiler's, a native binary's startup is a real and small part of the cost of
    /// asking, so `wall` stays the supervised process's and stays comparable with Singular's and
    /// msolve's.
    fn solve_stage(output: &str) -> Option<Duration> {
        output
            .lines()
            .find_map(|line| line.strip_prefix("#seconds:"))
            .and_then(|value| value.trim().parse::<f64>().ok())
            .filter(|seconds| seconds.is_finite() && *seconds >= 0.0)
            .map(Duration::from_secs_f64)
    }

    /// The driver's error message, if it printed one.
    ///
    /// `main` returns `Result<(), String>`, so a failure is `Error: "..."` on stderr and a
    /// non-zero exit. Sagebrush's own packing failure — `exponents too large to pack` — arrives
    /// this way.
    fn error_line(output: &str) -> Option<String> {
        output
            .lines()
            .map(str::trim_start)
            .find(|line| line.starts_with("Error:") || line.starts_with("error:"))
            .map(|line| {
                line.trim_start_matches("Error:")
                    .trim_start_matches("error:")
                    .trim()
                    .trim_matches('"')
                    .to_string()
            })
    }
}

impl ExternalSolver for SagebrushSolver {
    fn id(&self) -> &str {
        "sagebrush"
    }

    fn probe_version(&mut self) -> Result<ToolVersion, RunFailure> {
        // The driver has no `--version`: an argument it cannot open is a path error. So presence is
        // proved the only way it can be, by solving a one-variable system and reading back the
        // engine line.
        let (input_path, output_path) = self.scratch("version");
        std::fs::write(&input_path, "x\n65521\nx^2-1\n")?;
        let invocation = Invocation::new(&self.binary, &self.work_dir, &output_path)
            .arg(&input_path)
            .env(THREADS_VARIABLE, "1");
        let measurement = Supervisor::new(Duration::from_secs(60)).run(&invocation)?;
        let output = read_output(&output_path);
        if !measurement.succeeded() {
            return Err(match Self::error_line(&output) {
                Some(message) => RunFailure::Reported { message },
                None => RunFailure::NonZeroExit {
                    code: measurement.exit_code,
                },
            });
        }
        let engine = output
            .lines()
            .find_map(|line| line.strip_prefix("#engine:"))
            .map(str::trim)
            .ok_or(RunFailure::MissingMarker {
                marker: "#engine:".to_string(),
            })?;
        let version = ToolVersion::new("sagebrush", engine)
            .with_build(PROVISIONED_COMMIT)
            .with_raw(output.clone());
        self.version = Some(version.clone());
        Ok(version)
    }

    fn supports(&self, instance: &Instance, task: Task) -> Support {
        // The driver calls `f4::groebner_p` with `Order::DegRevLex` and nothing else. Sagebrush has
        // more than that (see the module documentation), and approximating `LexBasis` with a
        // degrevlex basis is precisely the substitution the task taxonomy forbids.
        if task != Task::ReducedGrobnerBasis {
            return Support::No(Unsupported::Task { task });
        }
        if instance.order != MonomialOrder::GradedReverseLexicographic {
            return Support::No(Unsupported::Order {
                order: instance.order,
            });
        }

        if !instance.field.is_prime_field() {
            return Support::No(Unsupported::ExtensionField {
                characteristic: instance.field.characteristic,
                extension_degree: instance.field.extension_degree,
            });
        }
        if instance.field.characteristic < 2 {
            return Support::No(Unsupported::Representation {
                detail: "the driver handles prime fields only; characteristic 0 would be Q"
                    .to_string(),
            });
        }
        if instance.field.characteristic >= MAX_CHARACTERISTIC {
            return Support::No(Unsupported::Characteristic {
                characteristic: instance.field.characteristic,
                supported_below: MAX_CHARACTERISTIC,
            });
        }
        if instance.variables.is_empty() || instance.variables.len() > MAX_VARIABLES {
            return Support::No(Unsupported::VariableCount {
                variables: instance.variables.len(),
                maximum: MAX_VARIABLES,
            });
        }
        // The driver's parser splits a generator on `*` and matches each factor against a variable
        // name, so a name containing `*`, `^`, `+`, `-` or `,` cannot be told from an operator.
        if let Some(name) = instance
            .variables
            .iter()
            .find(|name| name.is_empty() || name.contains(['*', '^', '+', '-', ',', ' ']))
        {
            return Support::No(Unsupported::Representation {
                detail: format!(
                    "{:?} is not distinguishable from an operator in the driver's input syntax",
                    name
                ),
            });
        }
        Support::Yes
    }

    fn run(&mut self, instance: &Instance, task: Task, limits: &Limits) -> RunReport {
        // Cloned before the closure so that `finish` borrows nothing of `self`: the scratch-file
        // counter needs `&mut self` between here and every use of it.
        let version = self.version.clone();
        let finish = |status: RunStatus, measurement: Measurement, command: Option<String>| {
            let mut report =
                RunReport::new("sagebrush", instance, task, limits, status, measurement);
            if let Some(version) = &version {
                report = report.with_version(version.clone());
            }
            if let Some(command) = command {
                report = report.with_command_line(command);
            }
            report
        };

        if let Support::No(reason) = self.supports(instance, task) {
            return finish(
                RunStatus::Unsupported(reason),
                Measurement::unmeasured(),
                None,
            );
        }
        if let Some(switch) = Self::inherited_switch() {
            // Refusing beats measuring: an inherited switch selects a different algorithm or
            // interleaves a trace with the basis, and `Invocation` can set a variable but not
            // clear one. `Reported` is the closest variant the contract has; `RunFailure` has no
            // "the environment is wrong" arm, and that gap is worth a follow-up rather than a
            // silent overload.
            return finish(
                RunStatus::Failed(RunFailure::Reported {
                    message: format!(
                        "the environment sets {}, which changes Sagebrush's engine path and \
                         cannot be cleared from the invocation",
                        switch
                    ),
                }),
                Measurement::unmeasured(),
                None,
            );
        }

        let (input_path, output_path) = self.scratch(&instance.name);
        if let Err(error) = std::fs::write(&input_path, Self::input(instance)) {
            return finish(
                RunStatus::Failed(RunFailure::Io {
                    reason: error.to_string(),
                }),
                Measurement::unmeasured(),
                None,
            );
        }

        let invocation = self.invocation(&input_path, &output_path, limits);
        let command = Some(invocation.command_line());
        let process = match Supervisor::new(limits.wall).run(&invocation) {
            Ok(process) => process,
            Err(error) => {
                return finish(
                    RunStatus::Failed(RunFailure::from(error)),
                    Measurement::unmeasured(),
                    command,
                )
            }
        };

        if process.timed_out {
            return finish(
                RunStatus::StoppedByLimit(LimitStop::WallClock {
                    limit: limits.wall,
                    elapsed: process.wall,
                }),
                Measurement {
                    wall: limits.wall,
                    cpu: process.cpu,
                    cpu_basis: process.cpu_basis,
                    peak_rss_bytes: process.peak_rss_bytes,
                    rss_basis: process.rss_basis,
                    stages: Vec::new(),
                },
                command,
            );
        }

        let output = read_output(&output_path);
        if !process.succeeded() {
            let failure = match Self::error_line(&output) {
                Some(message) => RunFailure::Reported { message },
                None => RunFailure::NonZeroExit {
                    code: process.exit_code,
                },
            };
            return finish(
                RunStatus::Failed(failure),
                Measurement::of_process(&process),
                command,
            );
        }

        let mut measurement = Measurement::of_process(&process);
        if let Some(solve) = Self::solve_stage(&output) {
            measurement = measurement.with_stage("solve", solve);
        }

        match self.answer(&output, instance) {
            // `Complete` and not `Verified`, and for Sagebrush that distinction carries more weight
            // than for any other comparand here: see the maturity note at the top of this file.
            Ok(answer) => finish(RunStatus::Complete(answer), measurement, command),
            Err(failure) => finish(RunStatus::Failed(failure), measurement, command),
        }
        .with_log_path(output_path)
    }
}

#[cfg(test)]
mod tests {
    use super::{SagebrushSolver, MAX_CHARACTERISTIC, MAX_VARIABLES, PINNED_SWITCHES};
    use crate::{
        grobner::external::{
            ExternalSolver, FieldSpec, Instance, Limits, RunFailure, RunStatus, Support, Task,
            Unsupported,
        },
        MonomialOrder,
    };
    use std::time::Duration;

    fn instance(characteristic: u64, order: MonomialOrder) -> Instance {
        Instance::new(
            "pair",
            "smoke",
            FieldSpec::prime(characteristic),
            vec!["x1".to_string(), "x2".to_string()],
            vec!["x1^2+x2".to_string(), "x2^2-1".to_string()],
            order,
        )
    }

    fn solver(binary: &str, tag: &str) -> SagebrushSolver {
        let root = std::env::temp_dir().join(format!(
            "zeebra-sagebrush-{}-{}-{:?}",
            tag,
            std::process::id(),
            std::thread::current().id()
        ));
        SagebrushSolver::new(binary, root).expect("a writable scratch directory")
    }

    /// An absent driver is reported as unavailable from a run, not as a failed solve.
    #[test]
    fn test_an_absent_binary_is_reported_and_not_a_failed_solve() {
        let mut solver = solver("zeebra-no-such-sagebrush", "absent");
        let report = solver.run(
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(5)),
        );
        match &report.status {
            RunStatus::Failed(RunFailure::Unavailable { binary, .. }) => {
                assert_eq!(binary, "zeebra-no-such-sagebrush");
            }
            other => panic!("expected Unavailable, got {:?}", other),
        }
        assert!(report.was_skipped(), "an absent tool is a skipped row");
        assert!(report.measurement.is_unmeasured());
    }

    /// An absent driver fails the version probe the same way.
    #[test]
    fn test_an_absent_binary_fails_the_version_probe_the_same_way() {
        let mut solver = solver("zeebra-no-such-sagebrush", "absent-probe");
        match solver.probe_version() {
            Err(RunFailure::Unavailable { binary, .. }) => {
                assert_eq!(binary, "zeebra-no-such-sagebrush")
            }
            other => panic!("expected Unavailable, got {:?}", other),
        }
    }

    /// Goldilocks is inside Sagebrush's 2^62 bound; a 2^63 prime is not.
    #[test]
    fn test_the_characteristic_bound_is_sagebrushs_own_two_to_the_sixty_second() {
        let solver = solver("sagebrush-gb-driver", "char");
        assert_eq!(MAX_CHARACTERISTIC, 1 << 62);
        // 2^61 - 1, the Mersenne prime the provisioning smoke test reached.
        assert!(solver
            .supports(
                &instance(
                    2_305_843_009_213_693_951,
                    MonomialOrder::GradedReverseLexicographic
                ),
                Task::ReducedGrobnerBasis
            )
            .is_supported());
        match solver.supports(
            &instance(
                0xFFFF_FFFF_0000_0001,
                MonomialOrder::GradedReverseLexicographic,
            ),
            Task::ReducedGrobnerBasis,
        ) {
            Support::No(Unsupported::Characteristic {
                supported_below, ..
            }) => {
                assert_eq!(supported_below, MAX_CHARACTERISTIC)
            }
            other => panic!("Goldilocks is above Sagebrush's own gate, got {:?}", other),
        }
    }

    /// More variables than the packed representation can carry is a capability gap, named.
    #[test]
    fn test_too_many_variables_is_unsupported_with_the_packing_bound() {
        let solver = solver("sagebrush-gb-driver", "vars");
        let mut wide = instance(65521, MonomialOrder::GradedReverseLexicographic);
        wide.variables = (0..MAX_VARIABLES + 1).map(|i| format!("x{}", i)).collect();
        match solver.supports(&wide, Task::ReducedGrobnerBasis) {
            Support::No(Unsupported::VariableCount { variables, maximum }) => {
                assert_eq!(variables, MAX_VARIABLES + 1);
                assert_eq!(maximum, MAX_VARIABLES);
            }
            other => panic!("expected an unsupported variable count, got {:?}", other),
        }
    }

    /// Every task but a reduced basis is refused: the driver exposes one entry point.
    #[test]
    fn test_only_the_reduced_basis_task_is_offered() {
        let solver = solver("sagebrush-gb-driver", "tasks");
        let instance = instance(65521, MonomialOrder::GradedReverseLexicographic);
        for task in Task::all() {
            let support = solver.supports(&instance, task);
            if task == Task::ReducedGrobnerBasis {
                assert!(support.is_supported(), "{}", task);
            } else {
                assert!(
                    matches!(support, Support::No(Unsupported::Task { .. })),
                    "{}",
                    task
                );
            }
        }
    }

    /// Any order but degrevlex is refused, because the driver hardcodes `Order::DegRevLex`.
    #[test]
    fn test_only_degrevlex_is_offered() {
        let solver = solver("sagebrush-gb-driver", "order");
        for order in [
            MonomialOrder::Lexicographic,
            MonomialOrder::GradedLexicographic,
        ] {
            assert!(
                matches!(
                    solver.supports(&instance(65521, order), Task::ReducedGrobnerBasis),
                    Support::No(Unsupported::Order { .. })
                ),
                "{:?}",
                order
            );
        }
    }

    /// An extension field is unsupported rather than silently computed over the prime subfield.
    #[test]
    fn test_an_extension_field_is_unsupported() {
        let solver = solver("sagebrush-gb-driver", "ext");
        let mut extension = instance(2, MonomialOrder::GradedReverseLexicographic);
        extension.field = FieldSpec::extension(2, 8, "t^8+t^4+t^3+t+1");
        assert!(matches!(
            solver.supports(&extension, Task::ReducedGrobnerBasis),
            Support::No(Unsupported::ExtensionField { .. })
        ));
    }

    /// The input file declares the characteristic and the instance's variable order verbatim.
    #[test]
    fn test_the_input_declares_the_instances_variable_order() {
        let input =
            SagebrushSolver::input(&instance(65521, MonomialOrder::GradedReverseLexicographic));
        let mut lines = input.lines();
        assert_eq!(lines.next(), Some("x1,x2"));
        assert_eq!(lines.next(), Some("65521"));
        assert_eq!(lines.next(), Some("x1^2+x2,"));
        assert_eq!(lines.next(), Some("x2^2-1"));
    }

    /// The worker count reaches Sagebrush through the variable it actually reads.
    ///
    /// Unset, Sagebrush uses `available_parallelism()` — every hardware thread — so an unset
    /// worker count is not a default of one.
    #[test]
    fn test_the_worker_count_is_declared_to_the_child() {
        let solver = solver("sagebrush-gb-driver", "threads");
        let command = solver
            .invocation(
                std::path::Path::new("in.ms"),
                std::path::Path::new("out"),
                &Limits::wall(Duration::from_secs(5)).with_workers(8),
            )
            .command_line();
        assert!(command.starts_with("SAGEBRUSH_THREADS=8"), "{}", command);
    }

    /// A complete driver output parses into leading monomials and a basis cardinality.
    #[test]
    fn test_the_driver_output_parses_into_invariants() {
        let solver = solver("sagebrush-gb-driver", "parse");
        let output = "#engine:               sagebrush-mpoly f4::groebner_p\n\
                      #field characteristic: 65521\n\
                      #variable order:       x1, x2\n\
                      #monomial order:       degrevlex (Order::DegRevLex)\n\
                      #length of basis:      2 elements sorted by increasing leading monomials\n\
                      #seconds:              0.000250\n\
                      1*x2^2 + 65520\n\
                      1*x1^2 + 1*x2\n\
                      --- leading monomials ---\n\
                      x2^2\n\
                      x1^2\n";
        let answer = solver
            .answer(
                output,
                &instance(65521, MonomialOrder::GradedReverseLexicographic),
            )
            .expect("a complete run parses");
        assert_eq!(answer.invariants.basis_cardinality, Some(2));
        assert_eq!(
            answer.invariants.leading_monomials.as_deref(),
            Some(&["x1^2".to_string(), "x2^2".to_string()][..]),
            "sorted, so print order does not matter"
        );
        assert_eq!(answer.basis.as_ref().map(Vec::len), Some(2));
        assert_eq!(
            SagebrushSolver::solve_stage(output),
            Some(Duration::from_secs_f64(0.000250))
        );
        // No quotient dimension: the driver exposes none, and absent is "not reported" rather than
        // zero. A verification against Zeebra therefore overlaps on two invariants, not three.
        assert_eq!(answer.invariants.quotient_dimension, None);
    }

    /// A driver that echoed a different variable order is self-inconsistent, not a disagreement.
    ///
    /// The single most dangerous failure mode here: a basis under a permuted variable order is not
    /// comparable, and nothing else in the output would say so.
    #[test]
    fn test_an_echoed_variable_order_mismatch_is_self_inconsistent() {
        let solver = solver("sagebrush-gb-driver", "echo");
        let output = "#field characteristic: 65521\n\
                      #variable order:       x2, x1\n\
                      #monomial order:       degrevlex\n\
                      #length of basis:      1 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        match solver.answer(
            output,
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
        ) {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("x2, x1"), "{}", detail)
            }
            other => panic!("expected SelfInconsistent, got {:?}", other),
        }
    }

    /// An echoed characteristic mismatch is self-inconsistent too.
    #[test]
    fn test_an_echoed_characteristic_mismatch_is_self_inconsistent() {
        let solver = solver("sagebrush-gb-driver", "echo-char");
        let output = "#field characteristic: 65519\n#variable order:       x1, x2\n\
                      #monomial order:       degrevlex\n#length of basis:      1 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        assert!(matches!(
            solver.answer(
                output,
                &instance(65521, MonomialOrder::GradedReverseLexicographic)
            ),
            Err(RunFailure::SelfInconsistent { .. })
        ));
    }

    /// A basis shorter than its reported length is unparsable, not a smaller basis.
    #[test]
    fn test_a_truncated_basis_is_unparsable_rather_than_short() {
        let solver = solver("sagebrush-gb-driver", "truncated");
        let output = "#field characteristic: 65521\n#variable order:       x1, x2\n\
                      #monomial order:       degrevlex\n#length of basis:      2 elements\n\
                      1*x1\n--- leading monomials ---\nx1\n";
        match solver.answer(
            output,
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
        ) {
            Err(RunFailure::Unparsable { marker, .. }) => {
                assert_eq!(marker, "#length of basis:")
            }
            other => panic!("expected Unparsable, got {:?}", other),
        }
    }

    /// Sagebrush's own packing failure is extracted as the reported message.
    #[test]
    fn test_the_drivers_error_line_is_extracted() {
        assert_eq!(
            SagebrushSolver::error_line("Error: \"exponents too large to pack\"\n").as_deref(),
            Some("exponents too large to pack")
        );
        assert_eq!(SagebrushSolver::error_line("#engine: x\n"), None);
    }

    /// An inherited engine switch stops the run instead of producing a figure for another engine.
    #[test]
    fn test_an_inherited_engine_switch_refuses_the_run() {
        // Serialized against the other tests only by being the sole writer of this variable.
        let name = "SB_SIGF4";
        assert!(PINNED_SWITCHES.contains(&name));
        // SAFETY: a single-threaded section of one test; no other test reads this variable.
        unsafe { std::env::set_var(name, "0") };
        let switch = SagebrushSolver::inherited_switch();
        unsafe { std::env::remove_var(name) };
        assert_eq!(
            switch,
            Some(name),
            "a truthy-if-set switch must be detected even at the value 0"
        );
    }
}
