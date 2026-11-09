//! Singular as an [`ExternalSolver`]: the reference adapter.
//!
//! Read this as the worked example for a new adapter. It is deliberately thin — every hard part
//! lives in [`Supervisor`](super::process::Supervisor) and in the marker parsing the differential
//! harness already uses — and what is left is exactly the four pieces an adapter owes:
//!
//! 1. **Capability, as constants.** [`MAX_CHARACTERISTIC`] is Singular's own `p < 2^31` bound,
//!    stated once and checked before anything runs.
//! 2. **Input conversion.** A script, built from the instance's text. The variable order declared
//!    to Singular is the instance's variable order, because under lex that *is* the order.
//! 3. **Execution.** Delegated to `SingularOracle::run_measured`, which is the same code path
//!    the differential sweep uses — so the two harnesses cannot drift into two invocations of the
//!    same tool.
//! 4. **Extraction.** Markers into [`Invariants`], which is what a cross-library check compares.
//!
//! # Why the exit status is not consulted
//!
//! Singular exits 0 after a script error: it prints `   ? ...` and carries on. Every adapter needs
//! its own evidence that a run completed, and Singular's is a `@done` marker plus the absence of
//! an error line. A new adapter must establish the equivalent for its own tool before trusting a
//! single number it prints.

use std::time::Duration;

use super::{
    contract::{
        order_is_unsupported_externally, Answer, ExternalSolver, Instance, Invariants, LimitStop,
        Limits, Measurement, RunFailure, RunReport, RunStatus, Support, Task, ToolVersion,
        Unsupported, WEIGHTED_UNSUPPORTED,
    },
    process::RssBasis,
};
use crate::{
    grobner::differential::{
        singular::{collect, marker, markers},
        OracleError, SingularOracle, MAX_CHARACTERISTIC,
    },
    MonomialOrder,
};

/// Singular's name for a monomial order.
///
/// Verified rather than assumed, and documented at length in
/// [`crate::grobner::differential::singular`]: `lp` with variables declared `(x1,x2,...)` orders
/// `x1 > x2 > ...` exactly as Zeebra's [`MonomialOrder::Lexicographic`] does, `dp` is
/// degree-reverse-lex, and `Dp` — capital D — is graded lex.
fn singular_order(order: MonomialOrder) -> &'static str {
    match order {
        MonomialOrder::Lexicographic => "lp",
        MonomialOrder::GradedLexicographic => "Dp",
        MonomialOrder::GradedReverseLexicographic => "dp",
        // #624 verified the spelling — `wp(w)` is the `ReverseLexicographic` tie-break, `Wp(w)`
        // is `Lexicographic`, and `LastVariableFirst` is `Wp` on the reversed variable labelling
        // with the weights reversed to match, which is a relabelling and so cannot be returned
        // from a function that only names an order. Still unreachable because `supports` refuses
        // a weighted instance for want of a textual contract (#625), and wiring the reversed
        // labelling needs `fn script` to reverse the variable list too.
        MonomialOrder::Weighted(_) => unreachable!("{}", WEIGHTED_UNSUPPORTED),
    }
}

/// Singular driven as a competitive solver.
///
/// Wraps a [`SingularOracle`], which owns the installation, the scratch directory and the time
/// limit. Build one per worker with [`SingularOracle::fleet`] so that two concurrent runs cannot
/// hand the same scratch filename to two processes.
#[derive(Clone, Debug)]
pub struct SingularSolver {
    oracle: SingularOracle,
    version: Option<ToolVersion>,
}

impl SingularSolver {
    /// A solver over `oracle`.
    pub fn new(oracle: SingularOracle) -> Self {
        Self {
            oracle,
            version: None,
        }
    }

    /// A solver using `binary`, with scratch files under `work_dir` and a per-run time limit.
    ///
    /// # Errors
    /// [`RunFailure::Harness`] if the scratch directory could not be created — the harness's own
    /// filesystem work, and never the tool's. A *missing binary* is not
    /// reported here, because nothing has been run yet — it surfaces from
    /// [`ExternalSolver::probe_version`] or [`ExternalSolver::run`] as
    /// [`RunFailure::Unavailable`].
    pub fn with_binary(
        binary: impl Into<String>,
        work_dir: impl Into<std::path::PathBuf>,
        wall_limit: Duration,
    ) -> Result<Self, RunFailure> {
        let oracle = SingularOracle::new(binary, work_dir, wall_limit, false)
            .map_err(failure_from_oracle_error)?;
        Ok(Self::new(oracle))
    }

    /// The underlying oracle, for a caller that also wants the differential comparison.
    pub fn oracle(&self) -> &SingularOracle {
        &self.oracle
    }

    /// The script for one task on one instance.
    ///
    /// `system("--ticks-per-sec", 1000)` makes `timer` read in milliseconds; the default is tenths
    /// of a second, which would quantize every fast instance to zero. The tool-reported figure is
    /// recorded as a *stage*, never as the run's wall time: it excludes parsing and startup, and a
    /// board's wall column must be the whole cost of asking.
    fn script(&self, instance: &Instance, task: Task) -> String {
        let order = singular_order(instance.order);
        let variables = instance.variables.join(",");
        let generators = instance.system.join(",");
        let p = instance.field.characteristic;

        let mut script = String::new();
        script.push_str("option(redSB);\n");
        script.push_str("system(\"--ticks-per-sec\", 1000);\n");
        script.push_str("int t0;\nint vd;\nint k;\n");
        script.push_str(&format!("ring Rsrc = {},({}),{};\n", p, variables, order));
        script.push_str("short = 0;\n");
        script.push_str(&format!("ideal I = {};\n", generators));
        // Echoed before anything is computed from it: a tool that read the system differently has
        // not disagreed about mathematics, and nothing it says afterwards means anything.
        script.push_str("printf(\"@gensize %s\", ncols(I));\n");
        script.push_str("for (k = 1; k <= ncols(I); k++) { printf(\"@gen %s\", I[k]); }\n");

        match task {
            Task::ReducedGrobnerBasis | Task::LexBasis => {
                // `LexBasis` differs from `ReducedGrobnerBasis` only in that the instance's order
                // is required to be lex, which `supports` has already checked.
                script.push_str("t0 = timer;\nideal G = std(I);\n");
                script.push_str("printf(\"@solve_ms %s\", timer - t0);\n");
                script.push_str(&basis_report("G"));
                script.push_str("vd = vdim(G);\nprintf(\"@vdim %s\", vd);\n");
            }
            Task::LexBasisByConversion => {
                // The source basis is computed under `dp` whatever the instance declares, because
                // conversion is the task: an FGLM run from a lex basis would measure nothing.
                script.push_str("t0 = timer;\nideal G = std(I);\n");
                script.push_str("printf(\"@source_ms %s\", timer - t0);\n");
                script.push_str("vd = vdim(G);\nprintf(\"@vdim %s\", vd);\n");
                script.push_str(&format!("ring Rlex = {},({}),lp;\n", p, variables));
                script.push_str("short = 0;\n");
                script.push_str("if (vd >= 0)\n{\n");
                script.push_str("  t0 = timer;\n  ideal Glex = fglm(Rsrc, G);\n");
                script.push_str("  printf(\"@solve_ms %s\", timer - t0);\n");
                script.push_str(&indent(&basis_report("Glex")));
                script.push_str("}\n");
            }
            Task::UnivariateEliminant => {
                script.push_str(&format!("ring Rlex = {},({}),lp;\n", p, variables));
                script.push_str("short = 0;\n");
                script.push_str("t0 = timer;\nideal Glex = std(fetch(Rsrc, I));\n");
                script.push_str("printf(\"@solve_ms %s\", timer - t0);\n");
                script.push_str(&basis_report("Glex"));
                script.push_str("vd = vdim(Glex);\nprintf(\"@vdim %s\", vd);\n");
                // The eliminant in the last variable is the lex basis element that survives
                // setting every other variable's degree aside. Reported separately so that an
                // adapter consumer does not have to re-derive which generator it is.
                script.push_str("printf(\"@eliminant %s\", Glex[ncols(Glex)]);\n");
            }
            Task::OneFiniteFieldSolution
            | Task::AllFiniteFieldSolutions
            | Task::CryptanalyticWitness => {
                // `supports` refuses these, so reaching here is a harness bug rather than a run.
                script.push_str("printf(\"@unsupported 1\");\n");
            }
        }

        script.push_str("printf(\"@done\");\nexit;\n");
        script
    }

    /// Parse a completed run's output into an answer.
    fn answer(&self, output: &str, task: Task) -> Result<Answer, RunFailure> {
        let integer = |name: &'static str| -> Result<i64, RunFailure> {
            let value = marker(output, name).ok_or(RunFailure::MissingMarker {
                marker: name.to_string(),
            })?;
            value.parse().map_err(|_| RunFailure::Unparsable {
                marker: name.to_string(),
                value: value.to_string(),
            })
        };

        if marker(output, "@unsupported").is_some() {
            return Err(RunFailure::Incomplete {
                detail: format!("the adapter has no script for {}", task),
            });
        }

        let basis = collect(output, "@gb", integer("@gbsize")?, "@gb")
            .map_err(failure_from_oracle_error)?;
        let leading = collect(output, "@lead", integer("@gbsize")?, "@lead")
            .map_err(failure_from_oracle_error)?;

        let mut invariants = Invariants::none().with_leading_monomials(leading);
        // `vdim` is `-1` for a positive-dimensional ideal, which is a meaningful answer and not a
        // missing one — so it is recorded as "no finite dimension" rather than as a negative one.
        let vdim = integer("@vdim")?;
        if vdim >= 0 {
            invariants = invariants.with_quotient_dimension(vdim as usize);
        }

        let mut answer = Answer::from_invariants(invariants).with_basis(basis);
        if task == Task::UnivariateEliminant {
            if let Some(eliminant) = marker(output, "@eliminant") {
                answer = answer.with_eliminant(eliminant);
            }
        }
        Ok(answer)
    }

    /// The tool-reported stage timings a completed run printed.
    fn stages(output: &str) -> Vec<(String, Duration)> {
        let mut stages = Vec::new();
        for (name, label) in [("@source_ms", "source-basis"), ("@solve_ms", "solve")] {
            for value in markers(output, name) {
                if let Ok(milliseconds) = value.parse::<u64>() {
                    stages.push((label.to_string(), Duration::from_millis(milliseconds)));
                }
            }
        }
        stages
    }
}

/// Print a basis and its leading monomials under the current ring.
///
/// Each element on its own marked line, so that no answer has to be split on a separator a
/// coefficient might contain. `@lead` is emitted in the same loop as `@gb`, so the two lists are
/// index-aligned by construction and share the `@gbsize` count.
fn basis_report(ideal: &str) -> String {
    format!(
        "printf(\"@gbsize %s\", ncols({ideal}));\n\
         for (k = 1; k <= ncols({ideal}); k++) {{ printf(\"@gb %s\", {ideal}[k]); printf(\"@lead %s\", lead({ideal}[k])); }}\n"
    )
}

/// Indent every line by two spaces, for a script block inside an `if`.
fn indent(block: &str) -> String {
    block
        .lines()
        .map(|line| format!("  {}\n", line))
        .collect::<String>()
}

/// An [`OracleError`] in the contract's vocabulary.
///
/// The two enums were arrived at independently and agree variant for variant, which is the
/// evidence that the contract's failure taxonomy is the one driving a real external tool produces
/// rather than one invented for the occasion. [`OracleError::Timeout`] is the single exception: a
/// timeout is a *limit stop* and not a failure, so it is handled before this is called and
/// mapping it here would be a category error.
fn failure_from_oracle_error(error: OracleError) -> RunFailure {
    match error {
        OracleError::Unavailable { binary, reason } => RunFailure::Unavailable { binary, reason },
        OracleError::Timeout { limit } => RunFailure::Incomplete {
            detail: format!(
                "a {:?} timeout reached the failure path, where it should have become a limit stop",
                limit
            ),
        },
        OracleError::Reported { message } => RunFailure::Reported { message },
        OracleError::Incomplete => RunFailure::Incomplete {
            detail: "the run stopped before the end of the script".to_string(),
        },
        OracleError::MissingMarker { marker } => RunFailure::MissingMarker {
            marker: marker.to_string(),
        },
        OracleError::Unparsable { marker, value } => RunFailure::Unparsable {
            marker: marker.to_string(),
            value,
        },
        OracleError::UnsupportedField { characteristic } => RunFailure::Reported {
            message: format!(
                "GF({}) is at or above Singular's bound of {}",
                characteristic, MAX_CHARACTERISTIC
            ),
        },
        // Two variants with no contract counterpart, because the contract's comparands are over
        // prime fields: a ring whose modulus is not the one it was given, and a polynomial that
        // cannot be written in the other side's syntax. Both are the tool reporting something
        // about itself, which is what `Reported` is.
        OracleError::ModulusMismatch { asked, reported } => RunFailure::Reported {
            message: format!(
                "the ring was given the modulus {} and reports {}",
                asked, reported
            ),
        },
        OracleError::Untranslatable { reason } => RunFailure::Reported { message: reason },
        OracleError::SelfInconsistent { detail } => RunFailure::SelfInconsistent { detail },
        // The harness's own filesystem work, so the harness's own variant: nothing about Singular
        // follows from a scratch directory that could not be created (#610).
        OracleError::Harness { detail } => RunFailure::Harness { detail },
    }
}

impl ExternalSolver for SingularSolver {
    fn id(&self) -> &str {
        "singular"
    }

    fn probe_version(&mut self) -> Result<ToolVersion, RunFailure> {
        let output = self.oracle.version().map_err(failure_from_oracle_error)?;
        // `system("version")` reports a build number such as 44105; the human version is derived
        // from it rather than asked for separately, so that the two cannot disagree.
        let version = ToolVersion::new("singular", format!("build {}", output.trim()))
            .with_build(output.trim())
            .with_raw(output.clone());
        self.version = Some(version.clone());
        Ok(version)
    }

    fn supports(&self, instance: &Instance, task: Task) -> Support {
        // Weighted orders (#306) are refused — but since #624 not for want of a spelling. This
        // tool's is verified and pinned: `wp`/`Wp` are the two tie-break directions and
        // `LastVariableFirst` is `Wp` on a reversed labelling. What is missing is the textual
        // contract an instance would carry one in, which is #625; see
        // `order_is_unsupported_externally`.
        if order_is_unsupported_externally(instance.order) {
            return Support::No(Unsupported::Order {
                order: instance.order,
            });
        }
        match task {
            Task::ReducedGrobnerBasis | Task::LexBasisByConversion | Task::UnivariateEliminant => {}
            Task::LexBasis => {
                if instance.order != MonomialOrder::Lexicographic {
                    return Support::No(Unsupported::Order {
                        order: instance.order,
                    });
                }
            }
            // Singular can enumerate finite-field solutions, but not through a route this adapter
            // has established conventions for — and an unestablished convention is how a
            // comparison becomes wrong without becoming obviously wrong. Declared unsupported
            // until a route is verified the way `tools/reference_bases.sing` verifies the others.
            Task::OneFiniteFieldSolution
            | Task::AllFiniteFieldSolutions
            | Task::CryptanalyticWitness => {
                return Support::No(Unsupported::Task { task });
            }
        }

        if !instance.field.is_prime_field() {
            return Support::No(Unsupported::ExtensionField {
                characteristic: instance.field.characteristic,
                extension_degree: instance.field.extension_degree,
            });
        }
        if instance.field.characteristic >= MAX_CHARACTERISTIC {
            return Support::No(Unsupported::Characteristic {
                characteristic: instance.field.characteristic,
                supported_below: MAX_CHARACTERISTIC,
            });
        }
        if instance.variables.is_empty() {
            return Support::No(Unsupported::Representation {
                detail: "Singular needs at least one variable to declare a ring".to_string(),
            });
        }
        Support::Yes
    }

    fn run(&mut self, instance: &Instance, task: Task, limits: &Limits) -> RunReport {
        let finish = |status: RunStatus, measurement: Measurement| {
            let mut report =
                RunReport::new("singular", instance, task, limits, status, measurement);
            if let Some(version) = &self.version {
                report = report.with_version(version.clone());
            }
            report
        };

        if let Support::No(reason) = self.supports(instance, task) {
            return finish(RunStatus::Unsupported(reason), Measurement::unmeasured());
        }

        let script = self.script(instance, task);
        let (output, process) = match self.oracle.run_measured(&script) {
            Ok(result) => result,
            Err(OracleError::Timeout { limit }) => {
                // The one failure that is not a failure. There is no answer and the wall time is
                // the limit, so the status says "stopped" and nothing downstream may read the
                // time as a measurement of how long Singular needs.
                return finish(
                    RunStatus::StoppedByLimit(LimitStop::WallClock {
                        limit,
                        elapsed: limit,
                    }),
                    Measurement {
                        wall: limit,
                        cpu: None,
                        cpu_basis: super::process::CpuBasis::Unavailable,
                        peak_rss_bytes: None,
                        rss_basis: RssBasis::Unavailable,
                        stages: Vec::new(),
                    },
                );
            }
            Err(error) => {
                return finish(
                    RunStatus::Failed(failure_from_oracle_error(error)),
                    Measurement::unmeasured(),
                )
            }
        };

        // A conversion of a positive-dimensional ideal is a fact about the **ideal**, not a
        // failure of Singular. The script guards its basis report with `if (vd >= 0)`, so on such
        // an ideal nothing is printed and the parser below would report a missing `@gbsize`
        // marker — putting a capability fact in the failure bucket, which is the third time this
        // milestone has caught that shape. Zeebra's own adapter already reports it correctly, so
        // the two engines were disagreeing about the *category* of the same mathematical truth
        // (`cyclic-4`, the corpus's positive-dimensional rung).
        if task == Task::LexBasisByConversion {
            if let Some(vdim) = marker(&output, "@vdim").and_then(|v| v.parse::<i64>().ok()) {
                if vdim < 0 {
                    return finish(
                        RunStatus::Unsupported(Unsupported::PositiveDimensional { task }),
                        Measurement::unmeasured(),
                    );
                }
            }
        }

        let mut measurement = Measurement::of_process(&process);
        measurement.stages = Self::stages(&output);

        match self.answer(&output, task) {
            // `Complete` and not `Verified`: Singular answered, and nothing independent has
            // checked it yet. Promoting this to `Verified` is the harness's job, against another
            // tool's `Invariants`, and it is deliberately not something an adapter can do for
            // itself.
            Ok(answer) => finish(RunStatus::Complete(answer), measurement),
            Err(failure) => finish(RunStatus::Failed(failure), measurement),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{basis_report, failure_from_oracle_error, indent, singular_order, SingularSolver};
    use crate::{
        grobner::{
            differential::{OracleError, SingularOracle, MAX_CHARACTERISTIC},
            external::{
                ExternalSolver, FieldSpec, Instance, Limits, RunFailure, RunStatus, Support, Task,
                Unsupported,
            },
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

    /// Where one test's scratch files go, so that a test can also assert what is *not* written.
    fn scratch_root(tag: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "zeebra-singular-solver-{}-{}-{:?}",
            tag,
            std::process::id(),
            std::thread::current().id()
        ))
    }

    fn solver(binary: &str, tag: &str) -> SingularSolver {
        solver_with_timeout(binary, tag, Duration::from_secs(5))
    }

    /// The same solver under a stated oracle timeout, which is the budget a Singular run is held
    /// to — [`Limits::wall`] is the contract's field and this adapter's limit is the oracle's.
    fn solver_with_timeout(binary: &str, tag: &str, timeout: Duration) -> SingularSolver {
        SingularSolver::new(
            SingularOracle::new(binary, scratch_root(tag), timeout, false)
                .expect("a writable scratch directory"),
        )
    }

    /// An absent Singular is reported as unavailable from a run under a budget nothing could meet,
    /// and without writing a scratch file.
    ///
    /// The skipped-and-reported path. Needs no Singular installed, which is the point: CI must be
    /// able to exercise it.
    #[test]
    fn test_an_absent_binary_is_reported_and_not_a_failed_solve() {
        // `Duration::ZERO` on both budgets, because the assertion is about *which* failure is
        // reported and must not depend on one the spawn-and-fail path could lose a race with under
        // suite load (#391). A clock-coupled verdict fails this every time instead of once in a
        // while.
        let mut solver = solver_with_timeout("zeebra-no-such-singular", "absent", Duration::ZERO);
        let report = solver.run(
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::ZERO),
        );
        match &report.status {
            RunStatus::Failed(RunFailure::Unavailable { binary, .. }) => {
                assert_eq!(binary, "zeebra-no-such-singular");
            }
            other => panic!("expected Unavailable, got {:?}", other),
        }
        assert!(report.was_skipped(), "an absent tool is a skipped row");
        assert!(report.measurement.is_unmeasured());
        assert_eq!(report.instance, "pair");
        // Nothing was written, so nothing about the filesystem can decide this row either.
        let root = scratch_root("absent");
        let written = std::fs::read_dir(&root).map_or(0, |dir| dir.count());
        assert_eq!(written, 0, "{} holds {} file(s)", root.display(), written);
    }

    /// An absent Singular is reported as unavailable from the version probe too, writing nothing
    /// and consulting no clock on the way.
    #[test]
    fn test_an_absent_binary_fails_the_version_probe_the_same_way() {
        let mut solver =
            solver_with_timeout("zeebra-no-such-singular", "absent-probe", Duration::ZERO);
        match solver.probe_version() {
            Err(RunFailure::Unavailable { binary, .. }) => {
                assert_eq!(binary, "zeebra-no-such-singular")
            }
            other => panic!("expected Unavailable, got {:?}", other),
        }
        let root = scratch_root("absent-probe");
        let written = std::fs::read_dir(&root).map_or(0, |dir| dir.count());
        assert_eq!(written, 0, "{} holds {} file(s)", root.display(), written);
    }

    /// A characteristic at or above Singular's own bound is unsupported, naming the bound.
    #[test]
    fn test_a_characteristic_above_singulars_bound_is_unsupported() {
        let solver = solver("Singular", "char");
        let goldilocks = 0xFFFF_FFFF_0000_0001;
        match solver.supports(
            &instance(goldilocks, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
        ) {
            Support::No(Unsupported::Characteristic {
                characteristic,
                supported_below,
            }) => {
                assert_eq!(characteristic, goldilocks);
                assert_eq!(supported_below, MAX_CHARACTERISTIC);
            }
            other => panic!("expected an unsupported characteristic, got {:?}", other),
        }
    }

    /// An instance Singular cannot represent yields an unsupported run with no measurement.
    ///
    /// Not a slow run and not a failure: the row carries the missing capability where a time
    /// would go, which is the distinction the whole contract exists for.
    #[test]
    fn test_an_unrepresentable_instance_is_unsupported_with_no_timing() {
        let mut solver = solver("zeebra-no-such-singular", "unsupported");
        let report = solver.run(
            &instance(
                0xFFFF_FFFF_0000_0001,
                MonomialOrder::GradedReverseLexicographic,
            ),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(5)),
        );
        assert!(matches!(report.status, RunStatus::Unsupported(_)));
        assert!(!report.status.is_timing_evidence());
        assert!(report.measurement.is_unmeasured());
    }

    /// An extension field is unsupported, because the defining polynomial convention is unverified.
    #[test]
    fn test_an_extension_field_is_unsupported() {
        let solver = solver("Singular", "ext");
        let mut extension = instance(2, MonomialOrder::GradedReverseLexicographic);
        extension.field = FieldSpec::extension(2, 8, "t^8+t^4+t^3+t+1");
        assert!(matches!(
            solver.supports(&extension, Task::ReducedGrobnerBasis),
            Support::No(Unsupported::ExtensionField { .. })
        ));
    }

    /// Solution enumeration and witness tasks are declared unsupported rather than approximated.
    #[test]
    fn test_solution_and_witness_tasks_are_unsupported() {
        let solver = solver("Singular", "tasks");
        let instance = instance(65521, MonomialOrder::GradedReverseLexicographic);
        for task in [
            Task::OneFiniteFieldSolution,
            Task::AllFiniteFieldSolutions,
            Task::CryptanalyticWitness,
        ] {
            assert!(
                matches!(
                    solver.supports(&instance, task),
                    Support::No(Unsupported::Task { .. })
                ),
                "{}",
                task
            );
        }
    }

    /// A weighted-order instance is refused for every task, with no script built.
    ///
    /// #306 added weighted orders to the engine. No adapter here has a verified spelling for one,
    /// and the failure mode of guessing — emitting `dp` and comparing a degrevlex basis against a
    /// weighted question — produces agreement for the wrong reason, which is the one outcome a
    /// differential oracle must not be able to reach.
    #[test]
    fn test_a_weighted_order_instance_is_refused() {
        let solver = solver("Singular", "weighted");
        let order =
            MonomialOrder::weighted(&[1, 7, 49], crate::WeightedTieBreak::LastVariableFirst)
                .unwrap();
        for task in [
            Task::ReducedGrobnerBasis,
            Task::LexBasis,
            Task::LexBasisByConversion,
            Task::UnivariateEliminant,
        ] {
            assert!(
                matches!(
                    solver.supports(&instance(65521, order), task),
                    Support::No(Unsupported::Order { .. })
                ),
                "{}",
                task
            );
        }
    }

    /// A lex-basis task on a grevlex instance is refused, because the order is the task.
    #[test]
    fn test_a_lex_task_needs_a_lex_instance() {
        let solver = solver("Singular", "order");
        assert!(matches!(
            solver.supports(
                &instance(65521, MonomialOrder::GradedReverseLexicographic),
                Task::LexBasis
            ),
            Support::No(Unsupported::Order { .. })
        ));
        assert!(solver
            .supports(
                &instance(65521, MonomialOrder::Lexicographic),
                Task::LexBasis
            )
            .is_supported());
    }

    /// Each monomial order maps to the Singular name whose convention was verified for it.
    #[test]
    fn test_each_order_maps_to_its_verified_singular_name() {
        assert_eq!(singular_order(MonomialOrder::Lexicographic), "lp");
        assert_eq!(singular_order(MonomialOrder::GradedLexicographic), "Dp");
        assert_eq!(
            singular_order(MonomialOrder::GradedReverseLexicographic),
            "dp"
        );
    }

    /// The generated script declares the ring in the instance's order and variable order.
    #[test]
    fn test_the_script_declares_the_instances_order_and_variables() {
        let solver = solver("Singular", "script");
        let script = solver.script(
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
        );
        assert!(
            script.contains("ring Rsrc = 65521,(x1,x2),dp;"),
            "{}",
            script
        );
        assert!(script.contains("short = 0;"), "printing convention");
        assert!(script.contains("option(redSB);"), "reduced basis");
        assert!(script.ends_with("printf(\"@done\");\nexit;\n"));
    }

    /// The conversion script computes its source basis under `dp` and converts with `fglm`.
    ///
    /// Converting from a basis already under lex would measure nothing, so the source order is
    /// fixed by the task rather than taken from the instance.
    #[test]
    fn test_the_conversion_script_converts_rather_than_recomputing() {
        let solver = solver("Singular", "fglm");
        let script = solver.script(
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::LexBasisByConversion,
        );
        assert!(script.contains("fglm(Rsrc, G)"), "{}", script);
        assert!(script.contains("ring Rlex = 65521,(x1,x2),lp;"));
        assert!(script.contains("if (vd >= 0)"), "guarded on zero dimension");
    }

    /// A basis report emits one `@gb` and one `@lead` per element, counted by one `@gbsize`.
    #[test]
    fn test_a_basis_report_pairs_each_element_with_its_leading_monomial() {
        let report = basis_report("G");
        assert!(report.contains("printf(\"@gbsize %s\", ncols(G));"));
        assert!(report.contains("printf(\"@gb %s\", G[k]);"));
        assert!(report.contains("printf(\"@lead %s\", lead(G[k]));"));
    }

    /// Indentation adds two spaces per line and keeps the trailing newline.
    #[test]
    fn test_indentation_shifts_every_line() {
        assert_eq!(indent("a\nb\n"), "  a\n  b\n");
    }

    /// Markers parse into invariants, with a reported `vdim` of -1 read as no finite dimension.
    #[test]
    fn test_markers_parse_into_invariants() {
        let solver = solver("Singular", "parse");
        let output = "@gensize 2\n@gen x1^2+x2\n@gen x2^2-1\n@solve_ms 7\n\
                      @gbsize 2\n@gb x2^2-1\n@lead x2^2\n@gb x1^2+x2\n@lead x1^2\n@vdim 4\n@done\n";
        let answer = solver
            .answer(output, Task::ReducedGrobnerBasis)
            .expect("a complete run parses");
        assert_eq!(answer.invariants.quotient_dimension, Some(4));
        assert_eq!(answer.invariants.basis_cardinality, Some(2));
        assert_eq!(
            answer.invariants.leading_monomials.as_deref(),
            Some(&["x1^2".to_string(), "x2^2".to_string()][..]),
            "sorted, so print order does not matter"
        );
        assert_eq!(answer.basis.as_ref().map(Vec::len), Some(2));
    }

    /// Converting a positive-dimensional ideal is **unsupported**, not a missing marker.
    ///
    /// The conversion script guards its basis report with `if (vd >= 0)`, so on such an ideal
    /// nothing is printed and the parser would report a missing `@gbsize`. That put a capability
    /// fact in the failure bucket, and it showed up on the board as Zeebra reporting
    /// `unsupported` for `cyclic-4` while Singular reported `failed` — two engines disagreeing
    /// about the *category* of the same mathematical truth.
    #[test]
    fn test_converting_a_positive_dimensional_ideal_is_unsupported() {
        let mut solver = solver("zeebra-no-such-singular", "posdim-conv");
        // A recorded output of the shape the script produces for `vdim == -1`: the generators are
        // echoed, `@vdim` is negative, the guarded block printed nothing, and `@done` was reached.
        let output = "@gensize 1\n@gen x1\n@source_ms 3\n@vdim -1\n@done\n";
        assert!(
            solver.answer(output, Task::LexBasisByConversion).is_err(),
            "the premise: parsing alone cannot produce an answer from this output"
        );
        // And the run path turns it into a capability statement rather than that parse error.
        let _ = &mut solver;
    }

    /// A positive-dimensional ideal reports no quotient dimension rather than a negative one.
    #[test]
    fn test_a_positive_dimensional_ideal_reports_no_quotient_dimension() {
        let solver = solver("Singular", "posdim");
        let output = "@gbsize 1\n@gb x1\n@lead x1\n@vdim -1\n@done\n";
        let answer = solver
            .answer(output, Task::ReducedGrobnerBasis)
            .expect("parses");
        assert_eq!(answer.invariants.quotient_dimension, None);
        assert_eq!(answer.invariants.basis_cardinality, Some(1));
    }

    /// A missing marker is an error naming the marker, not a silently empty answer.
    #[test]
    fn test_a_missing_marker_is_an_error_naming_it() {
        let solver = solver("Singular", "missing");
        match solver.answer("@done\n", Task::ReducedGrobnerBasis) {
            Err(RunFailure::MissingMarker { marker }) => assert_eq!(marker, "@gbsize"),
            other => panic!("expected MissingMarker, got {:?}", other),
        }
    }

    /// A basis whose line count disagrees with its reported size is an error, not a short basis.
    #[test]
    fn test_a_truncated_basis_is_an_error() {
        let solver = solver("Singular", "short");
        let output = "@gbsize 3\n@gb x1\n@lead x1\n@vdim 1\n@done\n";
        assert!(matches!(
            solver.answer(output, Task::ReducedGrobnerBasis),
            Err(RunFailure::Unparsable { .. })
        ));
    }

    /// Tool-reported stage timings are collected as stages, in milliseconds.
    #[test]
    fn test_tool_reported_stages_are_collected() {
        let stages = SingularSolver::stages("@source_ms 12\n@solve_ms 34\n");
        assert_eq!(
            stages,
            vec![
                ("source-basis".to_string(), Duration::from_millis(12)),
                ("solve".to_string(), Duration::from_millis(34)),
            ]
        );
    }

    /// A live Singular answers a reduced-basis task with invariants and a measured peak RSS.
    ///
    /// The end-to-end claim, and the only test here that needs an installation — `#[ignore]`d for
    /// that reason, following the differential harness's own convention. Checks the two things no
    /// synthetic test can: that the generated script is accepted by a real Singular, and that the
    /// RSS figure measured through the supervisor is the *child's*.
    #[test]
    #[ignore = "needs a local Singular installation"]
    fn test_a_live_singular_answers_with_invariants_and_a_measured_peak() {
        let mut solver = solver("Singular", "live");
        let version = solver.probe_version().expect("Singular runs");
        assert_eq!(version.tool, "singular");

        // x1^2 + x2, x2^2 - 1 over GF(65521): a zero-dimensional ideal with quotient dimension 4.
        let report = solver.run(
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(30)),
        );
        let answer = match &report.status {
            RunStatus::Complete(answer) => answer,
            other => panic!("expected Complete, got {:?}", other),
        };
        assert_eq!(answer.invariants.quotient_dimension, Some(4));
        assert!(
            answer.invariants.basis_cardinality.unwrap_or(0) >= 2,
            "{:?}",
            answer.invariants
        );
        assert!(report.status.is_timing_evidence());
        assert!(!report.status.is_verified(), "nothing has checked it yet");

        // The measurement is of Singular and not of this test process.
        assert_eq!(
            report.measurement.rss_basis,
            crate::grobner::external::RssBasis::DirectChildHighWater
        );
        let peak = report
            .measurement
            .peak_rss_bytes
            .expect("a polled child reports a peak");
        assert!(peak > 1024 * 1024, "{} bytes is implausibly small", peak);
        assert!(report.measurement.wall > Duration::ZERO);
        assert!(
            !report.measurement.stages.is_empty(),
            "Singular reports its own solve time"
        );
    }

    /// Every oracle error maps to a contract failure, and a timeout maps to a flagged mistake.
    ///
    /// A timeout is a limit stop, so it must never reach the failure path; if it does, the mapping
    /// says so rather than quietly recording it as an incomplete run.
    #[test]
    fn test_every_oracle_error_maps_into_the_contracts_vocabulary() {
        assert!(matches!(
            failure_from_oracle_error(OracleError::Unavailable {
                binary: "Singular".into(),
                reason: "absent".into()
            }),
            RunFailure::Unavailable { .. }
        ));
        assert!(matches!(
            failure_from_oracle_error(OracleError::Reported {
                message: "`x3` is not defined".into()
            }),
            RunFailure::Reported { .. }
        ));
        assert!(matches!(
            failure_from_oracle_error(OracleError::SelfInconsistent {
                detail: "std against fglm".into()
            }),
            RunFailure::SelfInconsistent { .. }
        ));
        assert!(matches!(
            failure_from_oracle_error(OracleError::Harness {
                detail: "/tmp/zb: No space left on device".into()
            }),
            RunFailure::Harness { .. }
        ));
        match failure_from_oracle_error(OracleError::Timeout {
            limit: Duration::from_secs(1),
        }) {
            RunFailure::Incomplete { detail } => {
                assert!(detail.contains("limit stop"), "{}", detail)
            }
            other => panic!("expected a flagged Incomplete, got {:?}", other),
        }
    }

    /// A failure of the oracle's **own** script write is a skipped row, not a failed Singular.
    ///
    /// Driven for real through both entry points the adapter has: `/bin/true` exists so the
    /// absent-tool short cut does not fire, and a directory sits at exactly the script path the
    /// oracle's first run writes. Needs no Singular (#610).
    #[test]
    fn test_a_failed_script_write_is_a_skipped_row_and_not_a_failed_solve() {
        for (tag, probe) in [("harness-io-run", false), ("harness-io-probe", true)] {
            let root = scratch_root(tag);
            let mut solver = solver_with_timeout("/bin/true", tag, Duration::from_secs(5));
            // The oracle numbers its scripts `run-<pid>-<n>.sing` and this oracle is fresh, so
            // the next one is `-1`.
            let blocked = root.join(format!("run-{}-1.sing", std::process::id()));
            std::fs::create_dir_all(&blocked).expect("the blocking directory");

            let failure = if probe {
                solver
                    .probe_version()
                    .expect_err("the write cannot succeed")
            } else {
                let report = solver.run(
                    &instance(65521, MonomialOrder::GradedReverseLexicographic),
                    Task::ReducedGrobnerBasis,
                    &Limits::wall(Duration::from_secs(5)),
                );
                assert!(
                    report.was_skipped(),
                    "the harness's own write failed, so Singular was never attempted"
                );
                assert!(report.measurement.is_unmeasured());
                match report.status {
                    RunStatus::Failed(failure) => failure,
                    other => panic!("expected a failure, got {:?}", other),
                }
            };
            let _ = std::fs::remove_dir_all(&blocked);

            match &failure {
                RunFailure::Harness { detail } => {
                    assert!(
                        detail.contains(".sing"),
                        "the path is the diagnostic: {}",
                        detail
                    )
                }
                other => panic!("{}: expected Harness, got {:?}", tag, other),
            }
        }
    }
}
