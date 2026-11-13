//! Groebner.jl as an [`ExternalSolver`], driven as a generated Julia script.
//!
//! # The JIT decision, stated because silence would make the figure dishonest
//!
//! Julia compiles on first call. On the provisioning smoke system the whole process took
//! **5.47 s** while the second `groebner` call took **0.00018 s** — a factor of about 30 000
//! (`docs/research/external-comparands.md` §4.3). A process wall time is therefore a measurement
//! of the Julia compiler, not of the algorithm, and [`RunReport::speedup_over`] reads
//! [`Measurement::wall`]. So this adapter is the one place in the module where `wall` is **not**
//! the supervised process's wall time:
//!
//! * `wall` is the **tool-reported elapsed time of the timed `groebner` call**, from
//!   `@solve_ns`, taken with `time_ns()` immediately around that call and nothing else.
//! * The script first runs `groebner` on a **two-element proxy system in the same ring**, under
//!   the same ordering, and discards the result. That specializes the monomial type, the
//!   coefficient type and the ordering type — which is what the first call pays for — before the
//!   timed call. It is a warm-up excluded from the figure, and this paragraph is the statement
//!   that makes excluding it defensible.
//! * Nothing is hidden: the process wall is recorded as the stage `process-wall` and the process
//!   CPU time as `process-cpu`, so the excluded quantity is `process-wall - solve` and is
//!   recoverable from the same record.
//! * **`cpu` is `None` with [`CpuBasis::Unavailable`] on the answered path.** `/proc` reports the
//!   whole process's `utime + stime`, which is the compiler's as much as the solver's; pairing it
//!   with a `wall` that is the solve alone would invite a `cpu / wall` ratio above the worker
//!   count. The process figure is kept as a stage instead of being passed off as the solve's.
//!
//! The residual contamination is real, bounded, and **measured**: on the provisioning smoke
//! system at one worker, the first call after the proxy warm-up takes **0.227 ms** against a
//! steady state of **0.061 ms**, so the proxy leaves roughly **0.17 ms** of compilation inside the
//! timed call. That is an absolute constant, not a factor — negligible on any instance that takes
//! milliseconds, and a reason not to quote this adapter at all below that. Compare the
//! alternative: the unadjusted process wall is 5.47 s, four orders of magnitude worse. The error
//! also has a sign: a code path the proxy does not reach — a threaded or randomized
//! linear-algebra backend that engages only on a large matrix — compiles inside the timed call, so
//! the figure over-states Groebner.jl's time and never under-states it.
//!
//! **`peak_rss_bytes` is the Julia process's, and that is what it means.** The basis says
//! [`RssBasis::DirectChildHighWater`](super::process::RssBasis::DirectChildHighWater) and it is
//! exactly that; it is also ~700 MB of Julia runtime and compiled code on a system whose basis is
//! six polynomials. Read it as a cost of *deploying* Groebner.jl, not as the algorithm's working
//! set. No field is invented to paper over the difference.
//!
//! # Above `p = 2^31` nothing can check this tool
//!
//! msolve and Singular both stop at `p <= 2^31 - 1` (`docs/research/external-comparands.md` §3.3,
//! §6.2). Groebner.jl and Sagebrush are the only comparands that accept a 64-bit prime, so at
//! Goldilocks or at `2^61 - 1` **the only available corroboration is the other one of the two** —
//! and since both are the sole implementations in range, an agreement between them is two
//! implementations agreeing and nothing more. Such a run is [`RunStatus::Complete`] and must not
//! be promoted; this adapter never promotes anything, but a harness must not either. Zeebra's
//! 254/255-bit fields have no external comparand at any size, and `FieldSpec::characteristic`
//! cannot even name them.
//!
//! # Two traps this adapter is written around
//!
//! 1. **`leading_monomial` reports against the ring's `internal_ordering`, not the `ordering=`
//!    passed to `groebner`.** A lex basis read through a degrevlex ring gives a correct basis and
//!    wrong leading monomials, and nothing errors (`external-comparands.md` §4.2). The script
//!    therefore builds the ring with `internal_ordering` *equal* to the order being computed —
//!    see `internal_ordering` and `groebner_ordering`, which are a pair and must stay one.
//! 2. **`JULIA_DEPOT_PATH` must name the provisioned depot** or the child tries to resolve
//!    packages and fails on a machine with no network. It is set on every invocation.
//!
//! # Katsura and cyclic conventions
//!
//! Groebner.jl ships its own generators, and they are **not** called the way Zeebra's are:
//! `src/utils/examples.jl:57` declares `katsuran(n)` over `["x$i" for i in 0:n]`, i.e. **n + 1
//! variables**, and its formula is Zeebra's `katsura::<N, F>()`
//! (`src/grobner/benchmark_systems.rs:66`) with `N = n + 1`. So Zeebra's `katsura::<7, _>()` is
//! Groebner.jl's `katsuran(6)`, and a row that pairs `katsura::<7>` with `katsuran(7)` compares
//! two different ideals. `cyclicn(n)` at `:25` is `n` variables and matches Zeebra's
//! `cyclic::<N, F>()` at `N = n` exactly. **None of this affects a run**, because an [`Instance`]
//! carries its generators as text and this adapter declares them verbatim; it matters when a
//! figure is compared against a published one or against the tool's own example corpus.
//!
//! # Licensing
//!
//! Groebner.jl is GPL-2.0 and **self-declaredly adapted from msolve**
//! (`src/Groebner.jl:1`, `:8-15`; `docs/research/external-provenance-policy.md` §3.3). It is a
//! subprocess comparand and an algorithmic reference only. Nothing here links it, vendors it, or
//! reads its source into Zeebra.

use std::time::Duration;

use super::{
    contract::{
        generators_agree, order_is_unsupported_externally, Answer, ExternalSolver, Instance,
        Invariants, LimitStop, Limits, Measurement, RunFailure, RunReport, RunStatus, Support,
        Task, ToolVersion, Unsupported, WEIGHTED_UNSUPPORTED,
    },
    process::{read_output, CpuBasis, Invocation, Supervisor},
};
use crate::{grobner::differential::singular::markers, MonomialOrder};

/// The largest characteristic Groebner.jl handles with a native coefficient type.
///
/// `src/input_output/AbstractAlgebra.jl:65-67` demotes the ground ring to `:generic` once
/// `characteristic(R) > typemax(UInt64)`, and `src/groebner/parameters.jl:175-176` asserts
/// `0 < char < typemax(UInt64)` before choosing a coefficient type. So the native range is every
/// prime below `u64::MAX` — **wider than msolve's and Singular's shared 2^31 ceiling**
/// (`docs/research/external-comparands.md` §3.3, §6.2), and verified by running: a basis comes
/// back at 2^31 − 1, at 2^32 − 5, at Goldilocks 2^64 − 2^32 + 1 and at 2^64 − 59.
///
/// A characteristic at or above this falls to `CoeffGeneric`, which is a different and far slower
/// code path, so a timing taken there would not be a timing of the same implementation.
pub const MAX_CHARACTERISTIC: u64 = u64::MAX;

/// Julia reserved words, which cannot be bound as a polynomial variable's name.
///
/// The script binds each of the instance's variables as a top-level Julia name so that the
/// generator text — which spells its variables the way Zeebra rendered them — parses. A reserved
/// word there is a syntax error rather than a wrong answer, but it is a *representation* limit and
/// so is declared rather than discovered.
const JULIA_RESERVED: &[&str] = &[
    "baremodule",
    "begin",
    "break",
    "catch",
    "const",
    "continue",
    "do",
    "else",
    "elseif",
    "end",
    "export",
    "false",
    "finally",
    "for",
    "function",
    "global",
    "if",
    "import",
    "let",
    "local",
    "macro",
    "module",
    "quote",
    "return",
    "struct",
    "true",
    "try",
    "using",
    "while",
];

/// The prefix every identifier this adapter introduces carries.
///
/// A variable named `zb_sys` in an instance would shadow the script's own binding, so
/// [`GroebnerJlSolver::supports`] refuses the prefix outright instead of hoping for the best.
const SCRIPT_PREFIX: &str = "zb_";

/// The `AbstractAlgebra.polynomial_ring` `internal_ordering` for an order.
///
/// Paired with [`groebner_ordering`] and never set independently of it: a ring whose
/// `internal_ordering` differs from the `ordering=` given to `groebner` yields a correct basis
/// whose `leading_monomial`s are read through the wrong lens
/// (`docs/research/external-comparands.md` §4.2).
fn internal_ordering(order: MonomialOrder) -> &'static str {
    match order {
        MonomialOrder::Lexicographic => ":lex",
        MonomialOrder::GradedLexicographic => ":deglex",
        MonomialOrder::GradedReverseLexicographic => ":degrevlex",
        MonomialOrder::Weighted(_) | MonomialOrder::Block(_) => {
            unreachable!("{}", WEIGHTED_UNSUPPORTED)
        }
    }
}

/// The `Groebner` ordering constructor for an order. See [`internal_ordering`].
fn groebner_ordering(order: MonomialOrder) -> &'static str {
    match order {
        MonomialOrder::Lexicographic => "Groebner.Lex()",
        MonomialOrder::GradedLexicographic => "Groebner.DegLex()",
        MonomialOrder::GradedReverseLexicographic => "Groebner.DegRevLex()",
        MonomialOrder::Weighted(_) | MonomialOrder::Block(_) => {
            unreachable!("{}", WEIGHTED_UNSUPPORTED)
        }
    }
}

/// True if `name` can be bound as a top-level Julia identifier by the generated script.
fn is_bindable_name(name: &str) -> bool {
    let mut characters = name.chars();
    let leads = matches!(characters.next(), Some(c) if c.is_ascii_alphabetic() || c == '_');
    leads
        && characters.all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !name.starts_with(SCRIPT_PREFIX)
        && !JULIA_RESERVED.contains(&name)
}

/// Groebner.jl driven as a competitive solver.
#[derive(Clone, Debug)]
pub struct GroebnerJlSolver {
    binary: String,
    depot: Option<String>,
    work_dir: std::path::PathBuf,
    version: Option<ToolVersion>,
    runs: u64,
}

impl GroebnerJlSolver {
    /// A solver over the `julia` at `binary`, with scratch files under `work_dir`.
    ///
    /// `depot` is the value for `JULIA_DEPOT_PATH`. Pass the provisioned depot — `None` inherits
    /// the environment's, which on a machine without a user depot means Groebner.jl is not found
    /// and the run fails with `RunFailure::Reported` rather than silently resolving something
    /// else.
    ///
    /// # Errors
    /// [`RunFailure::Harness`] if the scratch directory could not be created — the harness's own
    /// filesystem work, and never the tool's. A *missing* `julia` is
    /// not reported here, because nothing has been run yet: it surfaces from
    /// [`ExternalSolver::probe_version`] or [`ExternalSolver::run`] as
    /// [`RunFailure::Unavailable`].
    pub fn new(
        binary: impl Into<String>,
        depot: Option<String>,
        work_dir: impl Into<std::path::PathBuf>,
    ) -> Result<Self, RunFailure> {
        let work_dir = work_dir.into();
        std::fs::create_dir_all(&work_dir)?;
        Ok(Self {
            binary: binary.into(),
            depot,
            work_dir,
            version: None,
            runs: 0,
        })
    }

    /// A solver configured from the environment `tools/external/env.sh` exports.
    ///
    /// `ZEEBRA_JULIA` names the binary and defaults to `julia`, which `env.sh` puts on `PATH`;
    /// `ZEEBRA_JULIA_DEPOT` names the depot and otherwise falls back to the `JULIA_DEPOT_PATH`
    /// that `env.sh` sets to the provisioned depot.
    ///
    /// # Errors
    /// As [`Self::new`].
    pub fn from_env(work_dir: impl Into<std::path::PathBuf>) -> Result<Self, RunFailure> {
        let binary = std::env::var("ZEEBRA_JULIA").unwrap_or_else(|_| "julia".to_string());
        let depot = std::env::var("ZEEBRA_JULIA_DEPOT")
            .or_else(|_| std::env::var("JULIA_DEPOT_PATH"))
            .ok();
        Self::new(binary, depot, work_dir)
    }

    /// The scratch paths for the next run: the script and the file both streams go to.
    fn scratch(&mut self, tag: &str) -> (std::path::PathBuf, std::path::PathBuf) {
        self.runs += 1;
        let stem = format!("{}-{}", tag, self.runs);
        (
            self.work_dir.join(format!("{}.jl", stem)),
            self.work_dir.join(format!("{}.out", stem)),
        )
    }

    /// An invocation of `script`, with the depot, the worker count and any heap hint set.
    ///
    /// `-t` is how Groebner.jl's `tasks = :auto` default reaches `Threads.nthreads()`
    /// (`src/groebner/parameters.jl:353-356`); the script *also* passes `tasks =` explicitly, so
    /// the worker count is stated twice and cannot be inherited by accident.
    fn invocation(
        &self,
        script: &std::path::Path,
        output: &std::path::Path,
        limits: &Limits,
    ) -> Invocation {
        let mut invocation = Invocation::new(&self.binary, &self.work_dir, output)
            .arg("--startup-file=no")
            .arg("--history-file=no")
            .arg(format!("-t{}", limits.workers.max(1)));
        if let Some(bytes) = limits.max_rss_bytes {
            // Julia's own ceiling, so the limit is enforced by the thing being measured rather
            // than by a wrapper the supervisor would then be measuring instead.
            invocation = invocation.arg(format!("--heap-size-hint={}", bytes));
        }
        invocation = invocation.arg(script);
        if let Some(depot) = &self.depot {
            invocation = invocation.env("JULIA_DEPOT_PATH", depot);
        }
        invocation
    }

    /// The script for one task on one instance.
    ///
    /// Every identifier the script introduces is [`SCRIPT_PREFIX`]-prefixed and
    /// [`Self::supports`] refuses an instance that uses the prefix, so the instance's variable
    /// bindings cannot collide with the script's own.
    fn script(&self, instance: &Instance, task: Task) -> String {
        let ordering = groebner_ordering(instance.order);
        let names = instance
            .variables
            .iter()
            .map(|name| format!("\"{}\"", name))
            .collect::<Vec<String>>()
            .join(", ");

        let mut script = String::new();
        script.push_str("import Groebner\n");
        script.push_str("using AbstractAlgebra\n");
        script.push_str(&format!(
            "zb_F = AbstractAlgebra.GF({})\n",
            instance.field.characteristic
        ));
        script.push_str(&format!(
            "zb_R, zb_vars = AbstractAlgebra.polynomial_ring(zb_F, [{}], internal_ordering={})\n",
            names,
            internal_ordering(instance.order),
        ));
        // The instance's variable order *is* the monomial order, so the binding is positional and
        // a tool that reordered the names would be answering a different question.
        for (index, name) in instance.variables.iter().enumerate() {
            script.push_str(&format!("{} = zb_vars[{}]\n", name, index + 1));
        }
        script.push_str(&format!("zb_sys = [{}]\n", instance.system.join(", ")));
        // Echoed before anything is computed from it: a tool that read the system differently has
        // not disagreed about mathematics, and nothing it says afterwards means anything.
        script.push_str("println(\"@gensize \", length(zb_sys))\n");
        script.push_str("for zb_f in zb_sys\n    println(\"@gen \", zb_f)\nend\n");

        match task {
            Task::ReducedGrobnerBasis | Task::LexBasis => {
                // The warm-up: a two-element system in the *same* ring under the *same* ordering,
                // so the first call's compilation is paid before the timed one. See the module
                // documentation for why this is excluded from the figure and where the
                // warm-up-inclusive cost is still recorded.
                script.push_str(
                    "zb_warm = [zb_vars[1]^2 + zb_vars[end] - 1, zb_vars[end]^2 - zb_vars[1]]\n",
                );
                script.push_str(&format!(
                    "Groebner.groebner(zb_warm; ordering={}, tasks={})\n",
                    ordering,
                    self.tasks_placeholder(),
                ));
                script.push_str("GC.gc()\n");
                script.push_str("zb_t0 = time_ns()\n");
                script.push_str(&format!(
                    "zb_G = Groebner.groebner(zb_sys; ordering={}, tasks={})\n",
                    ordering,
                    self.tasks_placeholder(),
                ));
                script.push_str("println(\"@solve_ns \", time_ns() - zb_t0)\n");
                script.push_str("println(\"@gbsize \", length(zb_G))\n");
                script.push_str(
                    "for zb_g in zb_G\n    println(\"@gb \", zb_g)\n    \
                     println(\"@lead \", AbstractAlgebra.leading_monomial(zb_g))\nend\n",
                );
                // `dimension` is Groebner.jl's own independent check, and `quotient_basis` is
                // defined only in the zero-dimensional case — so the guard is mathematics and not
                // defensiveness.
                script.push_str("zb_dim = Groebner.dimension(zb_G)\n");
                script.push_str("println(\"@dim \", zb_dim)\n");
                script.push_str(
                    "if zb_dim == 0\n    \
                     println(\"@vdim \", length(Groebner.quotient_basis(zb_G)))\nend\n",
                );
            }
            Task::LexBasisByConversion
            | Task::UnivariateEliminant
            | Task::OneFiniteFieldSolution
            | Task::AllFiniteFieldSolutions => {
                // `supports` refuses these, so reaching here is a harness bug rather than a run.
                script.push_str("println(\"@unsupported 1\")\n");
            }
        }

        script.push_str("println(\"@done 1\")\n");
        script
    }

    /// The `tasks =` value, which is a literal the caller substitutes per run.
    ///
    /// Kept as a separate function only so that the two `groebner` calls in [`Self::script`]
    /// cannot drift apart: the warm-up must compile the same specialization the timed call uses.
    fn tasks_placeholder(&self) -> &'static str {
        "Base.Threads.nthreads()"
    }

    /// Parse a completed run's output into an answer.
    fn answer(&self, output: &str, instance: &Instance, task: Task) -> Result<Answer, RunFailure> {
        if marker(output, "@unsupported").is_some() {
            return Err(RunFailure::Incomplete {
                detail: format!("the adapter has no script for {}", task),
            });
        }
        if marker(output, "@done").is_none() {
            return Err(RunFailure::Incomplete {
                detail: "the script did not reach its @done marker".to_string(),
            });
        }
        Self::check_echoed_generators(output, instance)?;

        let size = integer(output, "@gbsize")?;
        let basis = counted(output, "@gb", size)?;
        let leading = counted(output, "@lead", size)?;

        let mut invariants = Invariants::none().with_leading_monomials(leading);
        // Groebner.jl reports the Krull dimension; `quotient_basis` — and therefore a finite
        // quotient dimension — exists only when that is zero. An absent `@vdim` is "not
        // reported", which is what the contract means by an absent field.
        if integer(output, "@dim")? == 0 {
            invariants = invariants.with_quotient_dimension(integer(output, "@vdim")? as usize);
        }

        Ok(Answer::from_invariants(invariants).with_basis(basis))
    }

    /// Check that the system Groebner.jl read back is the one that was sent, **as a set**.
    ///
    /// # Why this is a check and not a comment
    ///
    /// The script echoes `@gen` before computing anything, and until now the echo was only ever
    /// read by a human. It has to be checked on every run because of one failure mode that
    /// **cross-validation cannot catch**: every engine is handed the same bytes, so an input that
    /// is misread is misread identically everywhere, and four engines then agree with each other
    /// while all four answer a different question. Agreement is the instrument this milestone
    /// relies on, and this is the case it is blind to.
    ///
    /// The concrete instance of it: **at ten or more variables `x1` is a prefix of `x10`**, so a
    /// greedy tokenizer reads `x1*x10` as `x1*x1*0` and silently annihilates the term. Julia's
    /// lexer is not greedy in that way — an identifier absorbs its trailing digits, so `x10` is one
    /// token — and this check is what turns that from a belief into a per-run assertion. It also
    /// catches anything else that would make the echo differ: a dropped generator, a variable the
    /// script failed to bind, a renderer change on Zeebra's side.
    ///
    /// Compared as a **set of canonical term multisets**, because the two sides legitimately spell
    /// the same polynomial differently — Zeebra writes `x1*x10-1`, Groebner.jl echoes
    /// `x1*x10 + 1073741826` — and neither term order nor generator order is meaningful.
    ///
    /// # Errors
    /// [`RunFailure::SelfInconsistent`], which is what a tool contradicting the input *is*: nothing
    /// can be concluded about any other implementation from a run whose input was not the one
    /// requested.
    fn check_echoed_generators(output: &str, instance: &Instance) -> Result<(), RunFailure> {
        let reported = integer(output, "@gensize")?;
        let echoed = counted(output, "@gen", reported)?;
        if echoed.len() != instance.system.len() {
            return Err(RunFailure::SelfInconsistent {
                detail: format!(
                    "{} generators were echoed for a system of {}",
                    echoed.len(),
                    instance.system.len()
                ),
            });
        }

        // Shared with the Sagebrush adapter, which performs the same check against its driver's
        // `#gen` echo. One implementation, because the normalization is the subtle part.
        generators_agree(&instance.system, &echoed, instance.field.characteristic).map_err(
            |(sent, read)| RunFailure::SelfInconsistent {
                detail: format!("Groebner.jl read a different system: sent {sent}, read {read}"),
            },
        )
    }

    /// The tool-reported solve time, which this adapter uses as the run's wall time.
    ///
    /// # Errors
    /// [`RunFailure::MissingMarker`] or [`RunFailure::Unparsable`]: without this figure there is
    /// no publishable timing at all, because the process wall is the Julia compiler's.
    fn solve_time(output: &str) -> Result<Duration, RunFailure> {
        let nanoseconds = integer(output, "@solve_ns")?;
        u64::try_from(nanoseconds)
            .map(Duration::from_nanos)
            .map_err(|_| RunFailure::Unparsable {
                marker: "@solve_ns".to_string(),
                value: nanoseconds.to_string(),
            })
    }
}

/// The value of the first `name` marker line.
fn marker<'a>(output: &'a str, name: &str) -> Option<&'a str> {
    markers(output, name).into_iter().next()
}

/// The first identifier in `instance`'s generators that is not a declared variable.
///
/// A generator naming a variable the ring does not declare is an **input the tool cannot
/// represent**, and it is knowable before anything runs — so it belongs in `supports` as
/// [`Unsupported::Representation`] rather than arriving as a failed run.
///
/// The check exists because of how badly the neighbouring tool handles it: msolve **silently drops
/// the factor** (`iofiles.c:57-62` has no `else`), so `x*z-1` with only `x,y` declared reads as
/// `x-1`, exits 0, and reports `#invalid equations 0` — a well-formed basis of a different ideal.
/// Measured here, neither of this module's two tools shares that behaviour: the Sagebrush driver
/// exits 1 with `not a variable or integer: "z"`, and an unbound name in the generated Julia is an
/// `UndefVarError`. Both are loud. The check is still worth making, because a capability gap
/// reported as a capability gap costs nothing and a loud failure is still a failure.
fn undeclared_identifier(instance: &Instance) -> Option<String> {
    for generator in &instance.system {
        let mut name = String::new();
        // One pass, accumulating identifier characters and flushing at every separator. An
        // identifier is matched whole, which is the same discipline that keeps `x1` and `x10`
        // apart.
        for character in generator.chars().chain(std::iter::once('+')) {
            if character.is_ascii_alphanumeric() || character == '_' {
                name.push(character);
                continue;
            }
            if !name.is_empty() {
                let token = std::mem::take(&mut name);
                // A numeric literal is a coefficient or an exponent, not a variable.
                if token.parse::<u128>().is_err() && !instance.variables.contains(&token) {
                    return Some(token);
                }
            }
        }
    }
    None
}

/// An integer-valued marker.
fn integer(output: &str, name: &'static str) -> Result<i64, RunFailure> {
    let value = marker(output, name).ok_or(RunFailure::MissingMarker {
        marker: name.to_string(),
    })?;
    value.parse().map_err(|_| RunFailure::Unparsable {
        marker: name.to_string(),
        value: value.to_string(),
    })
}

/// Exactly `expected` lines of a marker, or an error naming the mismatch.
///
/// The count Groebner.jl reported and the number of lines it printed must agree, so that a
/// truncated output — a run killed between two `println`s — is a failure rather than a short
/// basis that would silently disagree on cardinality.
fn counted(output: &str, name: &'static str, expected: i64) -> Result<Vec<String>, RunFailure> {
    let values = markers(output, name);
    let expected = usize::try_from(expected).map_err(|_| RunFailure::Unparsable {
        marker: name.to_string(),
        value: expected.to_string(),
    })?;
    if values.len() != expected {
        return Err(RunFailure::Unparsable {
            marker: name.to_string(),
            value: format!(
                "{} values for a reported size of {}",
                values.len(),
                expected
            ),
        });
    }
    Ok(values.into_iter().map(str::to_string).collect())
}

/// The first Julia error line, if the run printed one.
///
/// Julia writes `ERROR: ...` and exits non-zero, so this is corroboration rather than the only
/// signal — but the message is what a human needs and the exit code is not.
fn error_line(output: &str) -> Option<String> {
    output
        .lines()
        .map(str::trim_start)
        .find(|line| line.starts_with("ERROR:"))
        .map(|line| line.trim_start_matches("ERROR:").trim().to_string())
}

impl ExternalSolver for GroebnerJlSolver {
    fn id(&self) -> &str {
        "groebner.jl"
    }

    fn probe_version(&mut self) -> Result<ToolVersion, RunFailure> {
        let (script_path, output_path) = self.scratch("version");
        let invocation = Invocation::new(&self.binary, &self.work_dir, &output_path)
            .arg("--startup-file=no")
            .arg("--history-file=no")
            .arg(&script_path);
        let invocation = match &self.depot {
            Some(depot) => invocation.env("JULIA_DEPOT_PATH", depot),
            None => invocation,
        };
        // Absence is settled before the scratch write and before the 120 s budget below, so the
        // probe reports a missing `julia` without touching either (#391).
        if let Some(absent) = invocation.unavailable() {
            return Err(RunFailure::from(absent));
        }
        std::fs::write(
            &script_path,
            "import Groebner\nprintln(\"@groebner \", pkgversion(Groebner))\n\
             println(\"@julia \", VERSION)\nprintln(\"@done 1\")\n",
        )?;
        let measurement = Supervisor::new(Duration::from_secs(120)).run(&invocation)?;
        let output = read_output(&output_path);
        if !measurement.succeeded() {
            return Err(match error_line(&output) {
                Some(message) => RunFailure::Reported { message },
                None => RunFailure::NonZeroExit {
                    code: measurement.exit_code,
                },
            });
        }
        let groebner = marker(&output, "@groebner").ok_or(RunFailure::MissingMarker {
            marker: "@groebner".to_string(),
        })?;
        let julia = marker(&output, "@julia").unwrap_or("unknown");
        let version = ToolVersion::new("groebner.jl", groebner)
            .with_build(format!("julia {}", julia))
            .with_raw(output.clone());
        self.version = Some(version.clone());
        Ok(version)
    }

    fn supports(&self, instance: &Instance, task: Task) -> Support {
        // Weighted and block orders require script generation this adapter does not implement.
        // Refuse them before any order can be silently approximated.
        if order_is_unsupported_externally(instance.order) {
            return Support::No(Unsupported::Order {
                order: instance.order,
            });
        }
        match task {
            Task::ReducedGrobnerBasis => {}
            Task::LexBasis => {
                if instance.order != MonomialOrder::Lexicographic {
                    return Support::No(Unsupported::Order {
                        order: instance.order,
                    });
                }
            }
            // `names(Groebner)` at 0.10.11 is exactly `DegLex, DegRevLex, InputOrdering, Lex,
            // MatrixOrdering, ProductOrdering, WeightedOrdering, dimension, groebner,
            // groebner_apply!, groebner_learn, groebner_with_change_matrix, isgroebner,
            // leading_ideal, normalform, quotient_basis` — verified by running it. **There is no
            // FGLM, no eliminant and no solver.** A lex basis obtained by conversion, a univariate
            // eliminant and a finite-field solution are therefore absent tasks, not slow ones, and
            // approximating any of them with the direct lex F4 is exactly the substitution the
            // task taxonomy exists to forbid.
            Task::LexBasisByConversion
            | Task::UnivariateEliminant
            | Task::OneFiniteFieldSolution
            | Task::AllFiniteFieldSolutions => {
                return Support::No(Unsupported::Task { task });
            }
        }

        if !instance.field.is_prime_field() {
            // Groebner.jl demotes a non-prime-degree field to `CoeffGeneric`
            // (`src/input_output/AbstractAlgebra.jl:70-75`), which is a different implementation
            // and whose defining-polynomial convention is unverified against Zeebra's.
            return Support::No(Unsupported::ExtensionField {
                characteristic: instance.field.characteristic,
                extension_degree: instance.field.extension_degree,
            });
        }
        if instance.field.characteristic < 2 {
            return Support::No(Unsupported::Representation {
                detail: "this adapter drives prime fields only; characteristic 0 would be Q"
                    .to_string(),
            });
        }
        // Written against the constant rather than against its current value: `MAX_CHARACTERISTIC`
        // is `u64::MAX` today, so the comparison can only fire at equality and clippy says so —
        // but a future Groebner.jl that narrowed its native range would need this check to narrow
        // with the constant, and `== MAX_CHARACTERISTIC` would silently stop doing that.
        #[allow(clippy::absurd_extreme_comparisons)]
        if instance.field.characteristic >= MAX_CHARACTERISTIC {
            return Support::No(Unsupported::Characteristic {
                characteristic: instance.field.characteristic,
                supported_below: MAX_CHARACTERISTIC,
            });
        }
        if instance.variables.is_empty() {
            return Support::No(Unsupported::Representation {
                detail: "a polynomial ring needs at least one variable".to_string(),
            });
        }
        if let Some(name) = instance
            .variables
            .iter()
            .find(|name| !is_bindable_name(name))
        {
            return Support::No(Unsupported::Representation {
                detail: format!(
                    "{:?} cannot be bound as a Julia identifier by the generated script",
                    name
                ),
            });
        }
        if let Some(name) = undeclared_identifier(instance) {
            return Support::No(Unsupported::Representation {
                detail: format!(
                    "the generators name {:?}, which is not a declared variable",
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
                RunReport::new("groebner.jl", instance, task, limits, status, measurement);
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

        let script = self.script(instance, task);
        let (script_path, output_path) = self.scratch(&instance.name);
        let invocation = self.invocation(&script_path, &output_path, limits);
        let command = Some(invocation.command_line());
        // Settled before the script is written and before the supervisor's clock starts: an absent
        // `julia` is a skipped row, and neither a wall budget nor a scratch write may stand between
        // that fact and the report of it (#391). The command line is still recorded, so the row
        // says what would have been attempted.
        if let Some(absent) = invocation.unavailable() {
            return finish(
                RunStatus::Failed(RunFailure::from(absent)),
                Measurement::unmeasured(),
                command,
            );
        }
        if let Err(error) = std::fs::write(&script_path, &script) {
            // The harness's own write, so a skipped row: Julia was never started, and a full disk
            // is not Groebner.jl losing a race (#610).
            return finish(
                RunStatus::Failed(RunFailure::Harness {
                    detail: format!("{}: {}", script_path.display(), error),
                }),
                Measurement::unmeasured(),
                None,
            );
        }

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
            // The wall time is the limit and says nothing about how much longer Groebner.jl
            // needed, so the status — not the number — is what a board must read.
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
            let failure = match error_line(&output) {
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

        // The module documentation is the statement this block implements: `wall` is the timed
        // `groebner` call, `cpu` is withheld because the only figure available covers the compiler
        // too, and both process-level figures are kept as stages so that nothing is excluded
        // without being recorded.
        let measurement = match Self::solve_time(&output) {
            Ok(solve) => {
                let mut stages = vec![
                    ("solve".to_string(), solve),
                    ("process-wall".to_string(), process.wall),
                ];
                if let Some(cpu) = process.cpu {
                    stages.push(("process-cpu".to_string(), cpu));
                }
                Measurement {
                    wall: solve,
                    cpu: None,
                    cpu_basis: CpuBasis::Unavailable,
                    peak_rss_bytes: process.peak_rss_bytes,
                    rss_basis: process.rss_basis,
                    stages,
                }
            }
            Err(failure) => {
                return finish(
                    RunStatus::Failed(failure),
                    Measurement::of_process(&process),
                    command,
                )
            }
        };

        match self.answer(&output, instance, task) {
            // `Complete` and not `Verified`: Groebner.jl answered, and nothing independent has
            // checked it. Promotion is the harness's job against another implementation's
            // `Invariants`, and deliberately not something an adapter can do for itself.
            Ok(answer) => finish(RunStatus::Complete(answer), measurement, command),
            Err(failure) => finish(RunStatus::Failed(failure), measurement, command),
        }
        .with_log_path(output_path)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        error_line, groebner_ordering, internal_ordering, is_bindable_name, GroebnerJlSolver,
        MAX_CHARACTERISTIC,
    };
    use crate::grobner::external::contract::canonical_generator;

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

    /// Where one test's scratch files go, so that a test can also assert what is *not* written.
    fn scratch_root(tag: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "zeebra-groebner-jl-{}-{}-{:?}",
            tag,
            std::process::id(),
            std::thread::current().id()
        ))
    }

    fn solver(binary: &str, tag: &str) -> GroebnerJlSolver {
        GroebnerJlSolver::new(binary, None, scratch_root(tag))
            .expect("a writable scratch directory")
    }

    /// An absent `julia` is reported as unavailable from a run under a budget nothing could meet,
    /// and without writing a scratch file.
    #[test]
    fn test_an_absent_binary_is_reported_and_not_a_failed_solve() {
        let mut solver = solver("zeebra-no-such-julia", "absent");
        // `Duration::ZERO`, because the assertion is about *which* failure is reported and must not
        // depend on a wall budget the spawn-and-fail path could lose a race with under suite load
        // (#391). A clock-coupled verdict fails this every time instead of once in a while.
        let report = solver.run(
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::ZERO),
        );
        match &report.status {
            RunStatus::Failed(RunFailure::Unavailable { binary, .. }) => {
                assert_eq!(binary, "zeebra-no-such-julia");
            }
            other => panic!("expected Unavailable, got {:?}", other),
        }
        assert!(report.was_skipped(), "an absent tool is a skipped row");
        assert!(report.measurement.is_unmeasured());
        // Nothing was written, so nothing about the filesystem can decide this row either.
        let root = scratch_root("absent");
        let written = std::fs::read_dir(&root).map_or(0, |dir| dir.count());
        assert_eq!(written, 0, "{} holds {} file(s)", root.display(), written);
    }

    /// A failure of the harness's **own** script write is a skipped row, not a failed Groebner.jl.
    ///
    /// Driven for real: `/bin/true` exists so the absent-tool short cut does not fire, and a
    /// directory is placed at exactly the script path the first run writes, so `fs::write` cannot
    /// succeed. Needs no Julia (#610).
    #[test]
    fn test_a_failed_script_write_is_a_skipped_row_and_not_a_failed_solve() {
        let root = scratch_root("harness-io");
        std::fs::create_dir_all(root.join("pair-1.jl")).expect("the blocking directory");
        let mut solver =
            GroebnerJlSolver::new("/bin/true", None, &root).expect("a writable scratch directory");
        let report = solver.run(
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(5)),
        );
        let _ = std::fs::remove_dir_all(root.join("pair-1.jl"));

        match &report.status {
            RunStatus::Failed(RunFailure::Harness { detail }) => {
                assert!(detail.contains("pair-1.jl"), "{}", detail)
            }
            other => panic!("expected Harness, got {:?}", other),
        }
        assert!(
            report.was_skipped(),
            "the harness's own write failed, so Groebner.jl was never attempted"
        );
        assert!(report.measurement.is_unmeasured());
    }

    /// An absent `julia` fails the version probe the same way, writing nothing and consulting no
    /// clock on the way.
    #[test]
    fn test_an_absent_binary_fails_the_version_probe_the_same_way() {
        let mut solver = solver("zeebra-no-such-julia", "absent-probe");
        match solver.probe_version() {
            Err(RunFailure::Unavailable { binary, .. }) => {
                assert_eq!(binary, "zeebra-no-such-julia")
            }
            other => panic!("expected Unavailable, got {:?}", other),
        }
        // The probe carries its own 120 s budget, which an absence verdict must never reach.
        let root = scratch_root("absent-probe");
        let written = std::fs::read_dir(&root).map_or(0, |dir| dir.count());
        assert_eq!(written, 0, "{} holds {} file(s)", root.display(), written);
    }

    /// Every prime field Zeebra's `FieldSpec` can name is inside Groebner.jl's native range.
    ///
    /// The capability finding that distinguishes it from msolve and Singular, both of which stop
    /// at 2^31.
    #[test]
    fn test_goldilocks_is_inside_the_supported_characteristic_range() {
        let solver = solver("julia", "char");
        let goldilocks = 0xFFFF_FFFF_0000_0001;
        assert!(solver
            .supports(
                &instance(goldilocks, MonomialOrder::GradedReverseLexicographic),
                Task::ReducedGrobnerBasis
            )
            .is_supported());
        assert_eq!(MAX_CHARACTERISTIC, u64::MAX);
    }

    /// A characteristic at the declared bound is unsupported, naming the bound.
    #[test]
    fn test_a_characteristic_at_the_bound_is_unsupported() {
        let solver = solver("julia", "char-bound");
        match solver.supports(
            &instance(u64::MAX, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
        ) {
            Support::No(Unsupported::Characteristic {
                characteristic,
                supported_below,
            }) => {
                assert_eq!(characteristic, u64::MAX);
                assert_eq!(supported_below, MAX_CHARACTERISTIC);
            }
            other => panic!("expected an unsupported characteristic, got {:?}", other),
        }
    }

    /// An extension field is unsupported, because Groebner.jl demotes it to generic coefficients.
    #[test]
    fn test_an_extension_field_is_unsupported() {
        let solver = solver("julia", "ext");
        let mut extension = instance(2, MonomialOrder::GradedReverseLexicographic);
        extension.field = FieldSpec::extension(2, 8, "t^8+t^4+t^3+t+1");
        assert!(matches!(
            solver.supports(&extension, Task::ReducedGrobnerBasis),
            Support::No(Unsupported::ExtensionField { .. })
        ));
    }

    /// Conversion, eliminant, solution and witness tasks are refused: 0.10.11 has no such entry.
    #[test]
    fn test_the_tasks_groebner_jl_does_not_offer_are_refused() {
        let solver = solver("julia", "tasks");
        let instance = instance(65521, MonomialOrder::GradedReverseLexicographic);
        for task in [
            Task::LexBasisByConversion,
            Task::UnivariateEliminant,
            Task::OneFiniteFieldSolution,
            Task::AllFiniteFieldSolutions,
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

    /// A lex-basis task on a grevlex instance is refused, because the order is the task.
    /// A weighted-order instance is refused, because this tool has no verified spelling for one.
    ///
    /// Emitting an unweighted ordering instead would compare a correct basis for a different
    /// question, which is agreement for the wrong reason.
    #[test]
    fn test_a_weighted_order_instance_is_refused() {
        let solver = solver("julia", "weighted");
        let order =
            MonomialOrder::weighted(&[1, 7, 49], crate::WeightedTieBreak::LastVariableFirst)
                .unwrap();
        assert!(matches!(
            solver.supports(&instance(65521, order), Task::ReducedGrobnerBasis),
            Support::No(Unsupported::Order { .. })
        ));
    }

    #[test]
    fn test_a_lex_task_needs_a_lex_instance() {
        let solver = solver("julia", "order");
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

    /// A variable name the script could not bind is a representation limit, not a failure.
    #[test]
    fn test_an_unbindable_variable_name_is_unsupported() {
        let solver = solver("julia", "names");
        for name in ["end", "zb_sys", "x-1", "2x", ""] {
            let mut bad = instance(65521, MonomialOrder::GradedReverseLexicographic);
            bad.variables = vec![name.to_string(), "x2".to_string()];
            assert!(
                matches!(
                    solver.supports(&bad, Task::ReducedGrobnerBasis),
                    Support::No(Unsupported::Representation { .. })
                ),
                "{:?} should be refused",
                name
            );
        }
        assert!(is_bindable_name("u0"));
        assert!(is_bindable_name("_x"));
    }

    /// Each order maps to a matched `internal_ordering` and `Groebner` ordering pair.
    ///
    /// The pairing is the `leading_monomial` trap: a mismatch yields a correct basis whose leading
    /// monomials are read under the wrong order, and nothing errors.
    #[test]
    fn test_each_order_maps_to_a_matched_ring_and_groebner_ordering() {
        for (order, internal, groebner) in [
            (MonomialOrder::Lexicographic, ":lex", "Groebner.Lex()"),
            (
                MonomialOrder::GradedLexicographic,
                ":deglex",
                "Groebner.DegLex()",
            ),
            (
                MonomialOrder::GradedReverseLexicographic,
                ":degrevlex",
                "Groebner.DegRevLex()",
            ),
        ] {
            assert_eq!(internal_ordering(order), internal);
            assert_eq!(groebner_ordering(order), groebner);
        }
    }

    /// The script declares the ring in the instance's order with `internal_ordering` to match.
    #[test]
    fn test_the_script_matches_the_rings_internal_ordering_to_the_computed_order() {
        let solver = solver("julia", "script");
        let script = solver.script(
            &instance(65521, MonomialOrder::Lexicographic),
            Task::LexBasis,
        );
        assert!(
            script.contains("internal_ordering=:lex"),
            "ring order\n{}",
            script
        );
        assert!(script.contains("ordering=Groebner.Lex()"), "{}", script);
        assert!(script.contains("AbstractAlgebra.GF(65521)"));
    }

    /// The script binds each variable positionally, so the instance's variable order is preserved.
    #[test]
    fn test_the_script_binds_variables_in_the_instances_order() {
        let solver = solver("julia", "vars");
        let script = solver.script(
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
        );
        assert!(script.contains("[\"x1\", \"x2\"]"), "{}", script);
        assert!(script.contains("x1 = zb_vars[1]\n"), "{}", script);
        assert!(script.contains("x2 = zb_vars[2]\n"), "{}", script);
    }

    /// The script warms the JIT on a proxy system before the call it times.
    ///
    /// The warm-up is what makes `@solve_ns` a measurement of the algorithm rather than of the
    /// Julia compiler, so its absence would silently change what every figure means.
    #[test]
    fn test_the_script_warms_the_jit_before_the_timed_call() {
        let solver = solver("julia", "warm");
        let script = solver.script(
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
        );
        let warm = script.find("zb_warm").expect("a warm-up system");
        let timed = script.find("zb_t0 = time_ns()").expect("a timed call");
        assert!(
            warm < timed,
            "the warm-up must precede the timing\n{}",
            script
        );
        assert!(script.contains("GC.gc()"));
    }

    /// Markers parse into invariants, with the quotient dimension taken only at dimension zero.
    #[test]
    fn test_markers_parse_into_invariants() {
        let solver = solver("julia", "parse");
        let output = "@gensize 2\n@gen x1^2 + x2\n@gen x2^2 + 65520\n@solve_ns 1234567\n\
                      @gbsize 2\n@gb x2^2 + 65520\n@lead x2^2\n@gb x1^2 + x2\n@lead x1^2\n\
                      @dim 0\n@vdim 4\n@done 1\n";
        let answer = solver
            .answer(
                output,
                &instance(65521, MonomialOrder::GradedReverseLexicographic),
                Task::ReducedGrobnerBasis,
            )
            .expect("a complete run parses");
        assert_eq!(answer.invariants.quotient_dimension, Some(4));
        assert_eq!(answer.invariants.basis_cardinality, Some(2));
        assert_eq!(
            answer.invariants.leading_monomials.as_deref(),
            Some(&["x1^2".to_string(), "x2^2".to_string()][..]),
            "sorted, so print order does not matter"
        );
        assert_eq!(
            GroebnerJlSolver::solve_time(output).expect("a solve time"),
            Duration::from_nanos(1_234_567)
        );
    }

    /// `x1` and `x10` canonicalize apart, which is the prefix collision that agreement cannot catch.
    ///
    /// At ten or more variables a greedy tokenizer reads `x1*x10` as `x1*x1*0`. Every engine is
    /// handed the same bytes, so such a misread is identical everywhere and four engines agree
    /// while all four answer a different question.
    #[test]
    fn test_a_variable_that_is_a_prefix_of_another_canonicalizes_apart() {
        let p = 1_073_741_827;
        assert_ne!(
            canonical_generator("x1*x10-1", p),
            canonical_generator("x1*x1-1", p)
        );
        assert_ne!(
            canonical_generator("x1*x10-1", p),
            canonical_generator("x1-1", p),
            "a dropped trailing digit must not collapse the term"
        );
        // And the term that a greedy scan would annihilate survives.
        assert_eq!(canonical_generator("x1*x10-1", p), "1*x1*x10+1073741826*1");
    }

    /// A negative coefficient and its residue are the same polynomial.
    ///
    /// Zeebra writes `-1`; Groebner.jl echoes `p-1`. Without this the echo check would reject every
    /// correct run.
    #[test]
    fn test_a_signed_coefficient_and_its_residue_canonicalize_together() {
        let p = 1_073_741_827;
        assert_eq!(
            canonical_generator("x1^2+x2^2-1", p),
            canonical_generator("x1^2 + x2^2 + 1073741826", p)
        );
        assert_eq!(
            canonical_generator("-x1+2*x2", p),
            canonical_generator("1073741826*x1 + 2*x2", p)
        );
    }

    /// Term order, factor order and whitespace do not change the canonical form; a coefficient does.
    #[test]
    fn test_canonicalization_ignores_print_order_but_not_values() {
        let p = 65521;
        assert_eq!(
            canonical_generator("x2*x1 + x3", p),
            canonical_generator("x3+x1*x2", p)
        );
        assert_ne!(
            canonical_generator("2*x1", p),
            canonical_generator("3*x1", p)
        );
    }

    /// An echo that differs from the sent system is self-inconsistent, not a disagreement.
    #[test]
    fn test_a_mismatched_generator_echo_is_self_inconsistent() {
        let sent = instance(65521, MonomialOrder::GradedReverseLexicographic);
        let good = "@gensize 2\n@gen x1^2 + x2\n@gen x2^2 + 65520\n";
        GroebnerJlSolver::check_echoed_generators(good, &sent).expect("the echo matches");

        // `x2^2-1` read as `x2^2-2`: the kind of divergence agreement cannot see.
        let bad = "@gensize 2\n@gen x1^2 + x2\n@gen x2^2 + 65519\n";
        match GroebnerJlSolver::check_echoed_generators(bad, &sent) {
            Err(RunFailure::SelfInconsistent { detail }) => {
                assert!(detail.contains("read a different system"), "{}", detail)
            }
            other => panic!("expected SelfInconsistent, got {:?}", other),
        }
    }

    /// A dropped generator is caught by the count before the multisets are compared.
    #[test]
    fn test_a_dropped_generator_is_caught_by_the_echo_check() {
        let sent = instance(65521, MonomialOrder::GradedReverseLexicographic);
        let short = "@gensize 1\n@gen x1^2 + x2\n";
        assert!(matches!(
            GroebnerJlSolver::check_echoed_generators(short, &sent),
            Err(RunFailure::SelfInconsistent { .. })
        ));
    }

    /// A positive-dimensional ideal reports no quotient dimension rather than a wrong one.
    #[test]
    fn test_a_positive_dimensional_ideal_reports_no_quotient_dimension() {
        let solver = solver("julia", "posdim");
        let output = "@gensize 2\n@gen x1^2 + x2\n@gen x2^2 + 65520\n@gbsize 1\n@gb x1\n@lead x1\n@dim 1\n@done 1\n";
        let answer = solver
            .answer(
                output,
                &instance(65521, MonomialOrder::GradedReverseLexicographic),
                Task::ReducedGrobnerBasis,
            )
            .expect("a complete run parses");
        assert_eq!(answer.invariants.quotient_dimension, None);
        assert_eq!(answer.invariants.basis_cardinality, Some(1));
    }

    /// A basis shorter than its reported size is unparsable, not a smaller basis.
    #[test]
    fn test_a_truncated_basis_is_unparsable_rather_than_short() {
        let solver = solver("julia", "truncated");
        let output = "@gensize 2\n@gen x1^2 + x2\n@gen x2^2 + 65520\n@gbsize 2\n@gb x1\n@lead x1\n@dim 1\n@done 1\n";
        match solver.answer(
            output,
            &instance(65521, MonomialOrder::GradedReverseLexicographic),
            Task::ReducedGrobnerBasis,
        ) {
            Err(RunFailure::Unparsable { marker, .. }) => assert_eq!(marker, "@gb"),
            other => panic!("expected Unparsable, got {:?}", other),
        }
    }

    /// Output with no `@done` marker is incomplete, whatever else it contains.
    #[test]
    fn test_output_without_the_done_marker_is_incomplete() {
        let solver = solver("julia", "nodone");
        let output = "@gbsize 1\n@gb x1\n@lead x1\n@dim 1\n";
        assert!(matches!(
            solver.answer(
                output,
                &instance(65521, MonomialOrder::GradedReverseLexicographic),
                Task::ReducedGrobnerBasis
            ),
            Err(RunFailure::Incomplete { .. })
        ));
    }

    /// A Julia `ERROR:` line is extracted as the reported message.
    #[test]
    fn test_a_julia_error_line_is_extracted() {
        let output = "some output\nERROR: LoadError: UndefVarError: `q` not defined\n";
        assert_eq!(
            error_line(output).as_deref(),
            Some("LoadError: UndefVarError: `q` not defined")
        );
        assert_eq!(error_line("@done 1\n"), None);
    }

    /// A worker count reaches Julia as `-t N` and a memory ceiling as Julia's own heap hint.
    #[test]
    fn test_limits_reach_julia_as_its_own_flags() {
        let solver = solver("julia", "limits");
        let limits = Limits::wall(Duration::from_secs(60))
            .with_workers(8)
            .with_max_rss_bytes(1 << 30);
        let command = solver
            .invocation(
                std::path::Path::new("s.jl"),
                std::path::Path::new("s.out"),
                &limits,
            )
            .command_line();
        assert!(command.contains("-t8"), "{}", command);
        assert!(
            command.contains(&format!("--heap-size-hint={}", 1u64 << 30)),
            "{}",
            command
        );
    }

    /// The depot is set on every invocation, so the child cannot resolve some other package set.
    #[test]
    fn test_the_depot_is_declared_to_the_child() {
        let root =
            std::env::temp_dir().join(format!("zeebra-groebner-jl-depot-{}", std::process::id()));
        let solver = GroebnerJlSolver::new("julia", Some("/opt/depot".to_string()), root)
            .expect("a writable scratch directory");
        let command = solver
            .invocation(
                std::path::Path::new("s.jl"),
                std::path::Path::new("s.out"),
                &Limits::wall(Duration::from_secs(5)),
            )
            .command_line();
        assert!(
            command.starts_with("JULIA_DEPOT_PATH=/opt/depot"),
            "{}",
            command
        );
    }

    /// A generator naming an undeclared variable is a capability gap, not a failed run.
    ///
    /// msolve silently drops such a factor and returns a well-formed basis of a different ideal.
    /// Both of this module's tools fail loudly instead, but the gap is knowable before running, so
    /// it is reported as `Unsupported` rather than discovered.
    #[test]
    fn test_a_generator_naming_an_undeclared_variable_is_unsupported() {
        let solver = solver("julia", "undeclared");
        let mut bad = instance(65521, MonomialOrder::GradedReverseLexicographic);
        bad.system = vec!["x1*z-1".to_string(), "x2-1".to_string()];
        match solver.supports(&bad, Task::ReducedGrobnerBasis) {
            Support::No(Unsupported::Representation { detail }) => {
                assert!(detail.contains("\"z\""), "{}", detail)
            }
            other => panic!("expected an unsupported representation, got {:?}", other),
        }
        // Coefficients and exponents are not identifiers, so a plain system still passes.
        let mut fine = instance(65521, MonomialOrder::GradedReverseLexicographic);
        fine.system = vec!["2*x1^3+65520*x2-1".to_string()];
        assert!(solver
            .supports(&fine, Task::ReducedGrobnerBasis)
            .is_supported());
    }
}
