//! Zeebra itself as an [`ExternalSolver`], so the competitive board has something to compare to.
//!
//! # Why Zeebra goes through the same contract as the subprocesses
//!
//! The board's ratios are only meaningful if both operands were measured the same way. Putting
//! Zeebra behind the same trait as msolve and Singular means one code path decides what a `Task`
//! is, what `Limits` mean, which outcomes are timing evidence, and where a ratio may be computed —
//! so the in-crate row cannot acquire a privilege the subprocess rows lack. It also means the
//! in-crate row is subject to the same refusals: a task Zeebra does not offer comes back
//! [`Unsupported`], not silently absent.
//!
//! # What is **not** equivalent, and is recorded rather than hidden
//!
//! Zeebra runs **in this process**, so its peak RSS is [`RssBasis::SelfHighWater`] where an
//! external tool's is [`RssBasis::DirectChildHighWater`]. Those are the same *quantity* — a
//! kernel-maintained `VmHWM` for one process — and differ only in attribution: a subprocess
//! figure covers one solve because the supervisor spawns one, while this process may have run
//! several rows and whatever built their inputs. So the figure is reported **only when the caller
//! declares that this process is doing one row and nothing else**
//! ([`ZeebraSolver::measuring_one_row`]), and is withheld otherwise. Withheld, not approximated:
//! `docs/research/external-comparison-protocol.md` §4 is the reasoning, and a ceiling over several
//! rows presented as one row's footprint is exactly the confusion it exists to stop.
//!
//! Zeebra also gets no process-startup charge, where Julia's and msolve's wall times include
//! theirs. That favours Zeebra, it cannot be removed without running Zeebra as a subprocess too,
//! and it is immaterial at the sizes where the gaps are interesting and material on the
//! millisecond rungs — which is why the report states it beside the small-instance rows.
//!
//! # Dimension and field dispatch
//!
//! `f4` and `fglm_to_lex` are const-generic in the variable count and generic in the field, so a
//! text instance has to be dispatched to a compiled instantiation. [`run`](ZeebraSolver::run)
//! matches on the characteristic and then on the variable count, and the set of pairs it compiles
//! is exactly what the corpus ladder needs. A pair nobody wrote down is
//! [`Unsupported::Representation`] naming itself as an **adapter** limit rather than an engine
//! one — Zeebra solves plenty of shapes this file does not instantiate, and a board row must not
//! imply otherwise.

use std::time::{Duration, Instant};

use super::{
    contract::{
        Answer, ExternalSolver, Instance, Invariants, LimitStop, Limits, Measurement, RunFailure,
        RunReport, RunStatus, Support, Task, ToolVersion, Unsupported,
    },
    corpus::REFERENCE_CHARACTERISTIC,
    process::{CpuBasis, RssBasis},
};
use crate::{
    fields::PrimeFieldElement64,
    grobner::{
        differential::polynomial_to_string,
        f4_reported,
        fglm::{classify_ideal, fglm_to_lex_with_options, FglmOptions},
        research::{ANEMOI_64_PRIME, KOALABEAR_PRIME},
        F4Error, F4Options, IdealClass,
    },
    util::peak_resident_bytes,
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

/// Zeebra's own engine, behind the competitive contract.
#[derive(Clone, Debug)]
pub struct ZeebraSolver {
    f4_options: F4Options,
    fglm_options: FglmOptions,
    measuring_one_row: bool,
}

impl Default for ZeebraSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl ZeebraSolver {
    /// A solver at the default F4 and FGLM options, with no memory figure reported.
    pub fn new() -> Self {
        Self {
            f4_options: F4Options::default(),
            fglm_options: FglmOptions::default(),
            measuring_one_row: false,
        }
    }

    /// Set the F4 options, including `max_wall_time`, which is how [`Limits::wall`] is enforced.
    pub fn with_f4_options(mut self, options: F4Options) -> Self {
        self.f4_options = options;
        self
    }

    /// Set the FGLM options.
    pub fn with_fglm_options(mut self, options: FglmOptions) -> Self {
        self.fglm_options = options;
        self
    }

    /// Declare that this process runs **one row and nothing else**, so its peak RSS is that row's.
    ///
    /// Only then is a memory figure reported. `VmHWM` is process-wide, so in a process that ran
    /// several rows the figure is a ceiling over all of them and over whatever built their inputs
    /// — the same hazard `measured_peak_rows_in_process` records on the cryptanalysis board. Here
    /// the sweep harness runs one process per measured row and sets this; a multi-row exploratory
    /// run does not, and its rows carry no memory figure at all.
    pub fn measuring_one_row(mut self) -> Self {
        self.measuring_one_row = true;
        self
    }

    /// The peak RSS to report, which is `None` unless this process is doing one row.
    fn memory(&self) -> (Option<u64>, RssBasis) {
        if !self.measuring_one_row {
            return (None, RssBasis::Unavailable);
        }
        match peak_resident_bytes() {
            Some(bytes) => (Some(bytes), RssBasis::SelfHighWater),
            None => (None, RssBasis::Unavailable),
        }
    }
}

/// Which (characteristic, variable count) pairs this adapter compiles.
///
/// Exactly the corpus ladder's, listed so the monomorphization cost is a deliberate choice rather
/// than whatever a generic call site happened to need. Each field appears with only the dimensions
/// its own families use.
fn compiled_dimensions(characteristic: u64) -> &'static [usize] {
    match characteristic {
        // Katsura 4–7, Cyclic 4–6, random and planted MQ at 6, 10, 14.
        REFERENCE_CHARACTERISTIC => &[4, 5, 6, 7, 10, 14],
        // The three planted Poseidon rows.
        KOALABEAR_PRIME => &[5, 7, 9],
        // Anemoi FCICO at N = 1 and 2.
        ANEMOI_64_PRIME => &[2, 4],
        _ => &[],
    }
}

/// What one solve produced, before it becomes a [`RunReport`].
struct Solved {
    status: RunStatus,
    wall: Duration,
    stages: Vec<(String, Duration)>,
}

/// Run `task` on a parsed system at a compiled dimension and field.
///
/// Separate from [`ExternalSolver::run`] because it is the only part that is generic: everything
/// around it — the capability check, the measurement, the report — is dimension-agnostic and must
/// not be monomorphized with it.
fn solve<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    names: &[&str],
    task: Task,
    order: MonomialOrder,
    f4_options: &F4Options,
    fglm_options: &FglmOptions,
) -> Solved {
    let mut stages: Vec<(String, Duration)> = Vec::new();
    let started = Instant::now();

    let at = Instant::now();
    let (result, statistics) = f4_reported(generators, order, f4_options);
    let basis_time = at.elapsed();
    stages.push(("basis".to_string(), basis_time));

    let basis = match result {
        Ok(basis) => basis,
        Err(error) => {
            // A resource or time stop is **not** a failure of the engine, and the contract has a
            // separate outcome for it. `limit_name` is the stable key; `max_wall_time` is the one
            // that is a time stop, and the harness sets it from `Limits::wall`.
            let status = match error {
                F4Error::TimeBudgetExceeded {
                    elapsed_millis,
                    budget_millis,
                    ..
                } => RunStatus::StoppedByLimit(LimitStop::WallClock {
                    limit: Duration::from_millis(budget_millis),
                    elapsed: Duration::from_millis(elapsed_millis),
                }),
                F4Error::InvalidOptions { reason } => RunStatus::Failed(RunFailure::Reported {
                    message: reason.to_string(),
                }),
                other => RunStatus::StoppedByLimit(LimitStop::ToolCap {
                    detail: format!("{} ({})", other, other.limit_name()),
                }),
            };
            return Solved {
                status,
                wall: started.elapsed(),
                stages,
            };
        }
    };

    // The invariants a cross-library check compares, extracted from the basis Zeebra returned.
    // Leading monomials are the initial ideal, which is what two correct reduced bases share.
    let leading: Vec<String> = basis
        .iter()
        .map(|polynomial| polynomial.leading_monomial(order))
        .map(|monomial| crate::grobner::differential::monomial_to_string(&monomial, names))
        .collect();
    let mut invariants = Invariants::none().with_leading_monomials(leading);

    let basis_text: Vec<String> = basis
        .iter()
        .map(|polynomial| polynomial_to_string(polynomial, names, order))
        .collect();

    match task {
        Task::ReducedGrobnerBasis | Task::LexBasis => {
            // The quotient dimension is an invariant worth reporting whenever it is finite, and
            // `classify_ideal` is what says whether it is. A positive-dimensional ideal reports
            // none rather than zero.
            if classify_ideal(&basis, order) == IdealClass::ZeroDimensional {
                let at = Instant::now();
                if let Ok((_, statistics)) = fglm_to_lex_with_options(&basis, order, fglm_options) {
                    invariants = invariants.with_quotient_dimension(statistics.quotient_dimension);
                }
                // Charged as its own stage: it is work done to *report an invariant*, not part of
                // the task, and leaving it in the basis time would make this row slower than the
                // same engine asked the same question without the cross-check.
                stages.push((
                    "quotient-dimension (for the invariant)".to_string(),
                    at.elapsed(),
                ));
            }
            Solved {
                status: RunStatus::Complete(
                    Answer::from_invariants(invariants).with_basis(basis_text),
                ),
                // Excludes the invariant stage above, so the published figure is the task's cost.
                wall: basis_time,
                stages,
            }
        }
        Task::LexBasisByConversion => {
            if classify_ideal(&basis, order) != IdealClass::ZeroDimensional {
                return Solved {
                    status: RunStatus::Unsupported(Unsupported::Representation {
                        detail: "order conversion needs a finite quotient algebra, and this ideal \
                                 is positive-dimensional"
                            .to_string(),
                    }),
                    wall: started.elapsed(),
                    stages,
                };
            }
            let at = Instant::now();
            let converted = fglm_to_lex_with_options(&basis, order, fglm_options);
            let conversion_time = at.elapsed();
            stages.push(("conversion".to_string(), conversion_time));

            match converted {
                Ok((lex, statistics)) => {
                    // The lex basis's own leading monomials, which is what another engine asked
                    // for the same task would report. Not the source basis's.
                    let lex_leading: Vec<String> = lex
                        .iter()
                        .map(|p| p.leading_monomial(MonomialOrder::Lexicographic))
                        .map(|m| crate::grobner::differential::monomial_to_string(&m, names))
                        .collect();
                    let timings = statistics.timings;
                    stages.push(("conversion: dependence".to_string(), timings.dependence));
                    stages.push((
                        "conversion: border".to_string(),
                        timings.normal_forms + timings.border_symbolic,
                    ));
                    let answer = Answer::from_invariants(
                        Invariants::none()
                            .with_leading_monomials(lex_leading)
                            .with_quotient_dimension(statistics.quotient_dimension),
                    )
                    .with_basis(
                        lex.iter()
                            .map(|p| polynomial_to_string(p, names, MonomialOrder::Lexicographic))
                            .collect(),
                    );
                    Solved {
                        status: RunStatus::Complete(answer),
                        wall: basis_time + conversion_time,
                        stages,
                    }
                }
                Err(error) => Solved {
                    status: RunStatus::Failed(RunFailure::Reported {
                        message: error.to_string(),
                    }),
                    wall: started.elapsed(),
                    stages,
                },
            }
        }
        // `statistics` is read here only so that a reader can see the basis stage was genuinely
        // measured rather than reported from an unrelated run.
        _ => Solved {
            status: RunStatus::Unsupported(Unsupported::Task { task }),
            wall: started.elapsed(),
            stages: {
                let mut stages = stages;
                stages.push((format!("batches {}", statistics.batches), Duration::ZERO));
                stages
            },
        },
    }
}

/// Parse `instance`'s text at a compiled dimension and solve it.
///
/// A macro because the dimension is a const generic: one arm per compiled `N`, and the field type
/// is the caller's. Returns `None` for a dimension this field does not compile.
macro_rules! dispatch {
    ($field:ty, $instance:expr, $task:expr, $f4:expr, $fglm:expr, $($n:literal),+ $(,)?) => {{
        let names: Vec<&str> = $instance.variables.iter().map(String::as_str).collect();
        match $instance.variables.len() {
            $(
                $n => {
                    let mut compiled = [""; $n];
                    compiled.copy_from_slice(&names[..$n]);
                    let mut generators: Vec<MultivariatePolynomial<$n, $field>> = Vec::new();
                    for text in &$instance.system {
                        match MultivariatePolynomial::parse(text, compiled) {
                            Ok(polynomial) => generators.push(polynomial),
                            // A generator this crate's own renderer produced and its own parser
                            // refuses is a bug, not a capability gap, and says so.
                            Err(e) => {
                                return Err(RunFailure::Unparsable {
                                    marker: "generator".to_string(),
                                    value: format!("{}: {}", text, e),
                                })
                            }
                        }
                    }
                    Ok(solve(&generators, &compiled, $task, $instance.order, $f4, $fglm))
                }
            )+
            _ => Err(RunFailure::Incomplete {
                detail: "no compiled dimension, which `supports` should have refused".to_string(),
            }),
        }
    }};
}

impl ZeebraSolver {
    /// Parse and solve, dispatching on the characteristic and then the variable count.
    fn dispatch(&self, instance: &Instance, task: Task) -> Result<Solved, RunFailure> {
        match instance.field.characteristic {
            REFERENCE_CHARACTERISTIC => dispatch!(
                PrimeFieldElement64<REFERENCE_CHARACTERISTIC>,
                instance,
                task,
                &self.f4_options,
                &self.fglm_options,
                4,
                5,
                6,
                7,
                10,
                14
            ),
            KOALABEAR_PRIME => dispatch!(
                PrimeFieldElement64<KOALABEAR_PRIME>,
                instance,
                task,
                &self.f4_options,
                &self.fglm_options,
                5,
                7,
                9
            ),
            ANEMOI_64_PRIME => dispatch!(
                PrimeFieldElement64<ANEMOI_64_PRIME>,
                instance,
                task,
                &self.f4_options,
                &self.fglm_options,
                2,
                4
            ),
            _ => Err(RunFailure::Incomplete {
                detail: "no compiled field, which `supports` should have refused".to_string(),
            }),
        }
    }
}

impl ExternalSolver for ZeebraSolver {
    fn id(&self) -> &str {
        "zeebra"
    }

    fn probe_version(&mut self) -> Result<ToolVersion, RunFailure> {
        // No subprocess: the version is this build's, and the commit is what a record needs to be
        // reproducible. `CARGO_PKG_VERSION` is a compile-time constant, so there is nothing to
        // fail — but the signature keeps the `Result` so that no caller has to special-case
        // Zeebra, which is the whole point of putting it behind the contract.
        Ok(ToolVersion::new("zeebra", env!("CARGO_PKG_VERSION"))
            .with_build("in-process, same build as the harness"))
    }

    fn supports(&self, instance: &Instance, task: Task) -> Support {
        match task {
            Task::ReducedGrobnerBasis | Task::LexBasis | Task::LexBasisByConversion => {}
            // Zeebra has `solve_one`, but routing it through this adapter would mean reporting a
            // root-finding strategy choice as a bare timing, and no comparand offers the task at
            // all (see the protocol §3). Refused here rather than measured and unusable.
            Task::OneFiniteFieldSolution
            | Task::AllFiniteFieldSolutions
            | Task::UnivariateEliminant
            | Task::CryptanalyticWitness => {
                return Support::No(Unsupported::Task { task });
            }
        }
        if task == Task::LexBasis && instance.order != MonomialOrder::Lexicographic {
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

        let dimensions = compiled_dimensions(instance.field.characteristic);
        if !dimensions.contains(&instance.variables.len()) {
            // **An adapter limit, not an engine limit**, and the wording has to say so: Zeebra
            // solves shapes this file does not instantiate, and a board row reading "unsupported"
            // against Zeebra would otherwise be a false statement about the engine.
            return Support::No(Unsupported::Representation {
                detail: format!(
                    "this adapter compiles GF({}) at {:?} variables, not {} — an adapter \
                     monomorphization limit, not a limit of Zeebra's engine",
                    instance.field.characteristic,
                    dimensions,
                    instance.variables.len()
                ),
            });
        }
        Support::Yes
    }

    fn run(&mut self, instance: &Instance, task: Task, limits: &Limits) -> RunReport {
        let version = self.probe_version().ok();
        let finish = |status: RunStatus, measurement: Measurement| {
            let mut report = RunReport::new("zeebra", instance, task, limits, status, measurement);
            if let Some(version) = version.clone() {
                report = report.with_version(version);
            }
            report.with_command_line(format!(
                "cargo run --release --example competitive_sweep -- --row {} --task {}",
                instance.name,
                task.tag()
            ))
        };

        if let Support::No(reason) = self.supports(instance, task) {
            return finish(RunStatus::Unsupported(reason), Measurement::unmeasured());
        }

        match self.dispatch(instance, task) {
            Ok(solved) => {
                let (peak_rss_bytes, rss_basis) = self.memory();
                finish(
                    solved.status,
                    Measurement {
                        wall: solved.wall,
                        // No per-stage CPU time: this is one thread of this process, so a
                        // `/proc/self/stat` read would charge whatever else the process did.
                        cpu: None,
                        cpu_basis: CpuBasis::Unavailable,
                        peak_rss_bytes,
                        rss_basis,
                        stages: solved.stages,
                    },
                )
            }
            Err(failure) => finish(RunStatus::Failed(failure), Measurement::unmeasured()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{compiled_dimensions, ZeebraSolver};
    use crate::grobner::external::{
        corpus::{instance, REFERENCE_CHARACTERISTIC},
        ExternalSolver, Limits, RssBasis, RunStatus, Support, Task, Unsupported,
    };
    use crate::MonomialOrder;
    use std::time::Duration;

    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    fn limits() -> Limits {
        Limits::wall(Duration::from_secs(60))
    }

    /// Zeebra answers a corpus rung with a basis and the invariants a cross-check compares.
    #[test]
    fn test_zeebra_answers_a_corpus_rung_with_invariants() {
        let katsura = instance("katsura-4", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        let mut solver = ZeebraSolver::new();
        let report = solver.run(&katsura, Task::ReducedGrobnerBasis, &limits());

        let answer = match &report.status {
            RunStatus::Complete(answer) => answer,
            other => panic!("expected Complete, got {:?}", other),
        };
        assert!(answer.basis.as_ref().is_some_and(|b| !b.is_empty()));
        assert!(answer.invariants.leading_monomials.is_some());
        // 8 = 2^(n-1) at n = 3, which is Katsura's published quotient dimension. Asserting the
        // literature's number rather than whatever this run produced is what makes the row a
        // check on Zeebra rather than a recording of it.
        assert_eq!(
            answer.invariants.quotient_dimension,
            Some(8),
            "katsura-4's quotient dimension is 8"
        );
        assert!(report.status.is_timing_evidence());
        assert_eq!(report.solver, "zeebra");
    }

    /// Zeebra's quotient dimensions agree with the literature's on three corpus rungs.
    ///
    /// The cross-library check's strength rests on these invariants being right, so they are
    /// checked against **published** values rather than against a previous run of this code:
    /// Katsura-n has `2^(n-1)` solutions and cyclic-5 has 70. An engine agreeing with itself
    /// proves nothing.
    #[test]
    fn test_the_reported_invariants_agree_with_published_values() {
        for (name, published) in [("katsura-4", 8), ("katsura-5", 16), ("cyclic-5", 70)] {
            let built = instance(name, REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
            let report = ZeebraSolver::new().run(&built, Task::ReducedGrobnerBasis, &limits());
            let answer = match &report.status {
                RunStatus::Complete(answer) => answer,
                other => panic!("{} gave {:?}", name, other),
            };
            assert_eq!(
                answer.invariants.quotient_dimension,
                Some(published),
                "{}'s quotient dimension disagrees with the published value",
                name
            );
        }
    }

    /// The version probe reports this build, so a row is attributable to a commit.
    #[test]
    fn test_the_version_probe_reports_this_build() {
        let version = ZeebraSolver::new().probe_version().expect("in-process");
        assert_eq!(version.tool, "zeebra");
        assert_eq!(version.version, env!("CARGO_PKG_VERSION"));
    }

    /// No memory figure unless the caller declares this process is doing one row.
    ///
    /// `VmHWM` is process-wide, so in a multi-row process it is a ceiling over all of them. The
    /// figure is withheld rather than approximated.
    #[test]
    fn test_no_memory_figure_unless_the_process_is_doing_one_row() {
        let katsura = instance("katsura-4", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");

        let mut shared = ZeebraSolver::new();
        let report = shared.run(&katsura, Task::ReducedGrobnerBasis, &limits());
        assert_eq!(report.measurement.peak_rss_bytes, None);
        assert_eq!(report.measurement.rss_basis, RssBasis::Unavailable);

        let mut sole = ZeebraSolver::new().measuring_one_row();
        let report = sole.run(&katsura, Task::ReducedGrobnerBasis, &limits());
        if cfg!(target_os = "linux") {
            assert!(report.measurement.peak_rss_bytes.is_some());
            assert_eq!(report.measurement.rss_basis, RssBasis::SelfHighWater);
        }
    }

    /// A conversion row charges the basis and the conversion as separate stages.
    ///
    /// The report's stage attribution depends on this split: a total is not actionable.
    #[test]
    fn test_a_conversion_row_splits_basis_from_conversion() {
        let katsura = instance("katsura-4", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        let mut solver = ZeebraSolver::new();
        let report = solver.run(&katsura, Task::LexBasisByConversion, &limits());
        assert!(
            matches!(report.status, RunStatus::Complete(_)),
            "{:?}",
            report.status
        );

        let names: Vec<&str> = report
            .measurement
            .stages
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();
        assert!(names.contains(&"basis"), "{:?}", names);
        assert!(names.contains(&"conversion"), "{:?}", names);
        assert!(
            names
                .iter()
                .any(|n| n.starts_with("conversion: dependence")),
            "the lex walk is the stage the report attributes the gap to: {:?}",
            names
        );
    }

    /// A positive-dimensional ideal cannot be converted, and that is a fact about the ideal.
    ///
    /// `cyclic-4` is the corpus's positive-dimensional rung. The outcome is `Unsupported`, not a
    /// failure, and carries no time — so it cannot enter a ratio.
    #[test]
    fn test_conversion_of_a_positive_dimensional_ideal_is_unsupported() {
        let cyclic = instance("cyclic-4", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        let mut solver = ZeebraSolver::new();
        let report = solver.run(&cyclic, Task::LexBasisByConversion, &limits());
        assert!(
            matches!(
                report.status,
                RunStatus::Unsupported(Unsupported::Representation { .. })
            ),
            "{:?}",
            report.status
        );
        assert!(!report.status.is_timing_evidence());
    }

    /// An uncompiled dimension is refused as an **adapter** limit, naming itself as one.
    ///
    /// A board row reading "unsupported" against Zeebra must not be read as a limit of the engine,
    /// which solves plenty of shapes this file does not instantiate.
    #[test]
    fn test_an_uncompiled_dimension_names_itself_an_adapter_limit() {
        let mut wide = instance("katsura-4", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        wide.variables = (1..=9).map(|i| format!("x{}", i)).collect();

        match ZeebraSolver::new().supports(&wide, Task::ReducedGrobnerBasis) {
            Support::No(Unsupported::Representation { detail }) => {
                assert!(detail.contains("adapter"), "{}", detail);
                assert!(
                    detail.contains("not a limit of Zeebra's engine"),
                    "{}",
                    detail
                );
            }
            other => panic!("expected an adapter-limit refusal, got {:?}", other),
        }
    }

    /// The solution and witness tasks are refused, matching every external comparand.
    #[test]
    fn test_the_solution_tasks_are_refused() {
        let katsura = instance("katsura-4", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        let solver = ZeebraSolver::new();
        for task in [
            Task::OneFiniteFieldSolution,
            Task::AllFiniteFieldSolutions,
            Task::UnivariateEliminant,
            Task::CryptanalyticWitness,
        ] {
            assert!(
                matches!(
                    solver.supports(&katsura, task),
                    Support::No(Unsupported::Task { .. })
                ),
                "{}",
                task
            );
        }
    }

    /// Every corpus field compiles the dimensions its own families need, and no others.
    #[test]
    fn test_each_field_compiles_the_dimensions_its_families_need() {
        assert_eq!(
            compiled_dimensions(REFERENCE_CHARACTERISTIC),
            &[4, 5, 6, 7, 10, 14]
        );
        assert!(compiled_dimensions(65521).is_empty());
    }

    /// A wall-clock limit produces a limit stop, not a failure, and carries no publishable time.
    #[test]
    fn test_a_wall_clock_limit_is_a_limit_stop() {
        let katsura = instance("katsura-7", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        let mut solver = ZeebraSolver::new().with_f4_options(crate::grobner::F4Options {
            // A budget nothing can meet, so the cooperative check fires on the first boundary.
            max_wall_time: Some(Duration::from_nanos(1)),
            ..crate::grobner::F4Options::default()
        });
        let report = solver.run(&katsura, Task::ReducedGrobnerBasis, &limits());
        assert!(
            matches!(report.status, RunStatus::StoppedByLimit(_)),
            "{:?}",
            report.status
        );
        assert!(
            !report.status.is_timing_evidence(),
            "a limit stop is a lower bound, never a measurement"
        );
    }
}
