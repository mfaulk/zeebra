//! The contract every external Gröbner engine is driven through.
//!
//! # Read this first if you are writing an adapter
//!
//! Implement [`ExternalSolver`]. Three methods, in the order a harness calls them:
//!
//! 1. [`ExternalSolver::probe_version`] — prove the tool is installed and record *which* build.
//!    Called once per sweep. A missing tool must come back as
//!    [`RunFailure::Unavailable`], never as a slow or failed run.
//! 2. [`ExternalSolver::supports`] — answer, **without running anything**, whether this tool can
//!    accept this instance and this task. A `no` is a statement about capability and is recorded
//!    as [`Support::No`]; it is never a timing result and never a denominator in a ratio.
//! 3. [`ExternalSolver::run`] — convert, execute under [`Limits`], parse, and return a
//!    [`RunReport`].
//!
//! Everything an adapter must *not* do by itself is already done for it:
//!
//! * **Do not build a [`std::process::Command`].** Describe the invocation with
//!   [`Invocation`](super::process::Invocation) and hand it to
//!   [`Supervisor`](super::process::Supervisor). That is what keeps the solver as the harness's
//!   direct child, which is what makes the peak-RSS figure the solver's and not a wrapper's — see
//!   the [`process`](super::process) module on the 7000x error this prevents.
//! * **Do not wrap the binary in `timeout`, `taskset`, or `sh -c`.** The supervisor enforces the
//!   time limit itself; affinity belongs on the harness process and is inherited.
//! * **Do not invent a timing or memory field.** [`Measurement`] is the whole vocabulary, and it
//!   carries the *basis* of each figure so that two numbers are only ever compared when they are
//!   the same kind of quantity.
//! * **Do not report an unchecked answer as correct.** [`RunStatus::Complete`] is "the tool
//!   answered"; [`RunStatus::Verified`] additionally means something independent agreed, and
//!   carries [`Invariants`] saying what.
//!
//! # The five outcomes, and why they are not four
//!
//! [`RunStatus`] separates *did not finish in the resources given* from *cannot do this at all*.
//! Conflating them is the specific error this contract exists to prevent: a tool that cannot
//! represent a 64-bit prime field has not lost a race on Goldilocks, and quoting a speedup against
//! it is not a measurement of anything. See `docs/research/external-comparison-protocol.md`.
//!
//! # A worked skeleton
//!
//! ```no_run
//! use std::time::Duration;
//! use zeebra::grobner::external::{
//!     ExternalSolver, Instance, Limits, Measurement, RunFailure, RunReport, RunStatus, Support,
//!     Task, ToolVersion, Unsupported,
//! };
//! use zeebra::grobner::external::process::{Invocation, Supervisor, read_output};
//!
//! struct ExampleSolver {
//!     binary: String,
//!     work_dir: std::path::PathBuf,
//! }
//!
//! impl ExternalSolver for ExampleSolver {
//!     fn id(&self) -> &str {
//!         "example"
//!     }
//!
//!     fn probe_version(&mut self) -> Result<ToolVersion, RunFailure> {
//!         let output = self.work_dir.join("version.out");
//!         let invocation = Invocation::new(&self.binary, &self.work_dir, &output).arg("--version");
//!         let measurement = Supervisor::new(Duration::from_secs(30)).run(&invocation)?;
//!         if !measurement.succeeded() {
//!             return Err(RunFailure::Incomplete {
//!                 detail: "the version probe did not exit cleanly".to_string(),
//!             });
//!         }
//!         Ok(ToolVersion::new("example", read_output(&output).trim()))
//!     }
//!
//!     fn supports(&self, instance: &Instance, task: Task) -> Support {
//!         if !matches!(task, Task::ReducedGrobnerBasis) {
//!             return Support::No(Unsupported::Task { task });
//!         }
//!         // Every tool has one of these. State it as a constant, as `MAX_CHARACTERISTIC` does.
//!         const MAX: u64 = 1 << 31;
//!         if instance.field.characteristic >= MAX {
//!             return Support::No(Unsupported::Characteristic {
//!                 characteristic: instance.field.characteristic,
//!                 supported_below: MAX,
//!             });
//!         }
//!         Support::Yes
//!     }
//!
//!     fn run(&mut self, instance: &Instance, task: Task, limits: &Limits) -> RunReport {
//!         // The capability check is part of `run`, not an alternative to it: a harness that
//!         // forgot to call `supports` must still get `Unsupported` rather than a bad number.
//!         if let Support::No(reason) = self.supports(instance, task) {
//!             return RunReport::unsupported(self.id(), instance, task, limits, reason);
//!         }
//!         // ... write the input, run the supervisor, parse the output ...
//!         RunReport::new(
//!             self.id(),
//!             instance,
//!             task,
//!             limits,
//!             RunStatus::Failed(RunFailure::Incomplete {
//!                 detail: "skeleton".to_string(),
//!             }),
//!             Measurement::unmeasured(),
//!         )
//!     }
//! }
//! ```

use std::{
    fmt::{Display, Formatter},
    path::PathBuf,
    time::Duration,
};

use crate::{util::sha256_hex, MonomialOrder};

use super::process::{CpuBasis, ProcessMeasurement, RssBasis, SpawnError};

/// What is being asked of the solver.
///
/// **These are different tasks and a comparison across them is meaningless.** Each has a precise
/// mathematical output, and the cost of one is not a bound on the cost of another: a reduced
/// grevlex basis is not a lex basis, a lex basis is not a solution, and one solution is not all of
/// them. A harness must never substitute a cheaper member for an expensive one and report the
/// result as the expensive one.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Task {
    /// The reduced Gröbner basis of the ideal under the instance's declared order.
    ///
    /// The output is unique given the ideal and the order, which is what makes it comparable
    /// across libraries as an *equality* rather than a containment.
    ReducedGrobnerBasis,

    /// A Gröbner basis of the ideal under lexicographic order, however obtained.
    ///
    /// Distinct from [`Self::ReducedGrobnerBasis`] under lex only in that the route is
    /// unconstrained: a tool may compute it directly or convert from a degree order.
    LexBasis,

    /// A lex basis of a zero-dimensional ideal obtained by **order conversion** from a degree
    /// order, FGLM-style.
    ///
    /// Separated from [`Self::LexBasis`] because the two routes have different complexity and a
    /// tool that only offers one has not lost to a tool that offers the other.
    LexBasisByConversion,

    /// One solution in the instance's coefficient field.
    ///
    /// Cheaper than [`Self::AllFiniteFieldSolutions`] whenever an early solution is found, so the
    /// two must not share a column.
    OneFiniteFieldSolution,

    /// Every solution in the instance's coefficient field.
    AllFiniteFieldSolutions,

    /// The univariate eliminant: a generator of the elimination ideal in the last variable.
    ///
    /// For a zero-dimensional ideal in shape position this is the univariate polynomial a lex
    /// basis ends with, but a tool may produce it without producing the rest of the basis.
    UnivariateEliminant,

    /// A witness for a cryptanalytic statement — a CICO preimage, a collision — verified against
    /// the primitive rather than against a basis.
    ///
    /// The only task whose correctness check is not algebraic, and the only one whose value is a
    /// *claim about a cipher*. It lives in the existing cryptanalysis scoreboard and not in the
    /// competitive board.
    CryptanalyticWitness,
}

impl Task {
    /// The stable tag used in records, filenames and digests.
    ///
    /// A tag and not the `Debug` name: renaming a variant must not silently change a digest.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::ReducedGrobnerBasis => "reduced-grobner-basis",
            Self::LexBasis => "lex-basis",
            Self::LexBasisByConversion => "lex-basis-by-conversion",
            Self::OneFiniteFieldSolution => "one-finite-field-solution",
            Self::AllFiniteFieldSolutions => "all-finite-field-solutions",
            Self::UnivariateEliminant => "univariate-eliminant",
            Self::CryptanalyticWitness => "cryptanalytic-witness",
        }
    }

    /// Every task, for a renderer that must enumerate columns.
    pub fn all() -> [Task; 7] {
        [
            Self::ReducedGrobnerBasis,
            Self::LexBasis,
            Self::LexBasisByConversion,
            Self::OneFiniteFieldSolution,
            Self::AllFiniteFieldSolutions,
            Self::UnivariateEliminant,
            Self::CryptanalyticWitness,
        ]
    }

    /// The task named by [`Self::tag`].
    pub fn from_tag(tag: &str) -> Option<Self> {
        Self::all().into_iter().find(|task| task.tag() == tag)
    }
}

impl Display for Task {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.tag())
    }
}

/// The coefficient field, precisely enough that two tools can be checked to be using the same one.
///
/// Characteristic alone is not enough: `GF(2^8)` and `GF(2)` share a characteristic and are not the
/// same field, and a tool that silently works over the prime subfield has answered a different
/// question.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FieldSpec {
    /// The characteristic.
    pub characteristic: u64,

    /// The extension degree. `1` for a prime field.
    pub extension_degree: u32,

    /// The name this field is known by in records, for example `GF(2^64 - 2^32 + 1)`.
    pub name: String,

    /// The defining polynomial of the extension, as text in the generator, when
    /// `extension_degree > 1`.
    ///
    /// **Required for an extension field**, because two tools' default `GF(2^8)` need not be the
    /// same ring: different Conway polynomials give isomorphic but not identical representations,
    /// and a basis compared element by element across them will disagree for no mathematical
    /// reason.
    pub defining_polynomial: Option<String>,
}

impl FieldSpec {
    /// A prime field.
    pub fn prime(characteristic: u64) -> Self {
        Self {
            characteristic,
            extension_degree: 1,
            name: format!("GF({})", characteristic),
            defining_polynomial: None,
        }
    }

    /// An extension field with its defining polynomial.
    pub fn extension(
        characteristic: u64,
        extension_degree: u32,
        defining_polynomial: impl Into<String>,
    ) -> Self {
        Self {
            characteristic,
            extension_degree,
            name: format!("GF({}^{})", characteristic, extension_degree),
            defining_polynomial: Some(defining_polynomial.into()),
        }
    }

    /// Replace the display name without changing the mathematics.
    pub fn named(mut self, name: impl Into<String>) -> Self {
        self.name = name.into();
        self
    }

    /// True for a prime field.
    pub fn is_prime_field(&self) -> bool {
        self.extension_degree == 1
    }

    /// The canonical lines the instance digest is taken over.
    fn canonical(&self) -> String {
        let mut text = format!(
            "characteristic {}\nextension-degree {}\n",
            self.characteristic, self.extension_degree
        );
        if let Some(polynomial) = &self.defining_polynomial {
            text.push_str(&format!("defining-polynomial {}\n", polynomial));
        }
        text
    }
}

impl Display for FieldSpec {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// The problem, as text, with a digest that is its identity.
///
/// **Text is the interface.** Every tool here is driven by a generated input file or script, so a
/// polynomial system crosses the boundary as a string in a syntax the tools agree on — which is
/// also what makes an instance recordable, diffable and reproducible by hand. Use
/// [`polynomial_to_string`](crate::grobner::differential::polynomial_to_string) to produce it from
/// Zeebra's own types, since that is the renderer whose output Zeebra's parser and Singular both
/// accept.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Instance {
    /// A stable identifier, for example `katsura-8` or `anemoi-2-cico-r6`.
    pub name: String,

    /// The family this instance belongs to, for grouping a board: `katsura`, `cyclic`, `mq`.
    pub family: String,

    /// The coefficient field.
    pub field: FieldSpec,

    /// Variable names, **in the order that defines the monomial order**.
    ///
    /// Not cosmetic: under lex, `[x1, x2]` and `[x2, x1]` are different orders and give different
    /// bases. Every adapter must declare these to its tool in exactly this order, and a tool that
    /// reorders them has answered a different question.
    pub variables: Vec<String>,

    /// The generators, as text.
    pub system: Vec<String>,

    /// The monomial order the task is posed under.
    pub order: MonomialOrder,

    /// What was done to the mathematical problem to arrive at this system.
    ///
    /// Recorded because a transformation changes what a result means. An instance that has had
    /// field equations added, variables eliminated, or a slice fixed is **a different ideal**, and
    /// comparing it with an untransformed one is a comparison of two problems.
    pub transformation: Option<String>,
}

impl Instance {
    /// An instance from its parts.
    pub fn new(
        name: impl Into<String>,
        family: impl Into<String>,
        field: FieldSpec,
        variables: Vec<String>,
        system: Vec<String>,
        order: MonomialOrder,
    ) -> Self {
        Self {
            name: name.into(),
            family: family.into(),
            field,
            variables,
            system,
            order,
            transformation: None,
        }
    }

    /// Record a transformation applied to reach this system.
    pub fn transformed(mut self, description: impl Into<String>) -> Self {
        self.transformation = Some(description.into());
        self
    }

    /// The canonical text the identity digest is taken over.
    ///
    /// Line-oriented and ASCII so that the digest can be reproduced by hand or in another
    /// language, which is the property that lets an external tool's own harness agree on an
    /// instance's identity. Follows
    /// [`ChallengeManifest::canonical`](crate::grobner::research::ChallengeManifest) in shape.
    ///
    /// The name is **not** covered: renaming an instance must not make it a different problem,
    /// and two differently-named identical systems must collide so that the collision is visible.
    /// The order and the transformation *are* covered, because both change the answer.
    pub fn canonical(&self) -> String {
        let mut text = String::new();
        text.push_str(&self.field.canonical());
        text.push_str(&format!("order {}\n", order_tag(self.order)));
        text.push_str(&format!("variables {}\n", self.variables.join(",")));
        if let Some(transformation) = &self.transformation {
            text.push_str(&format!("transformation {}\n", transformation));
        }
        for generator in &self.system {
            text.push_str(&format!("generator {}\n", generator));
        }
        text
    }

    /// The identity digest: SHA-256 of [`Self::canonical`], lowercase hex.
    ///
    /// Two runs whose digests differ are **not** runs on the same problem, whatever their names
    /// say, and a comparison tool must refuse to compare them.
    pub fn digest(&self) -> String {
        sha256_hex(self.canonical().as_bytes())
    }

    /// The first twelve hex digits of [`Self::digest`], for a table.
    pub fn short_digest(&self) -> String {
        self.digest()[..12].to_string()
    }

    /// The number of variables.
    pub fn variable_count(&self) -> usize {
        self.variables.len()
    }

    /// Variable names as borrowed strings, for an API that wants `&[&str]`.
    pub fn variable_refs(&self) -> Vec<&str> {
        self.variables.iter().map(String::as_str).collect()
    }
}

/// The stable tag for a monomial order, for digests and records.
pub fn order_tag(order: MonomialOrder) -> &'static str {
    match order {
        MonomialOrder::Lexicographic => "lex",
        MonomialOrder::GradedLexicographic => "grlex",
        MonomialOrder::GradedReverseLexicographic => "grevlex",
    }
}

/// The order named by [`order_tag`].
pub fn order_from_tag(tag: &str) -> Option<MonomialOrder> {
    match tag {
        "lex" => Some(MonomialOrder::Lexicographic),
        "grlex" => Some(MonomialOrder::GradedLexicographic),
        "grevlex" => Some(MonomialOrder::GradedReverseLexicographic),
        _ => None,
    }
}

/// A polynomial as a canonical, sorted multiset of `coefficient*factors` terms over `GF(p)`.
///
/// # What this is for
///
/// Every adapter here echoes the system the tool read back and compares it against the system that
/// was sent, because of one failure mode **cross-validation cannot catch**: every engine is handed
/// the same bytes, so an input that is misread is misread identically everywhere, and four engines
/// then agree with each other while all four answer a different question. Agreement is the
/// instrument this module relies on, and this is the case it is blind to.
///
/// The concrete instance of it: **at ten or more variables `x1` is a prefix of `x10`**, so a greedy
/// tokenizer reads `x1*x10` as `x1*x1*0` and silently annihilates the term. The corpus has
/// fourteen-variable rungs, so this is live rather than hypothetical.
///
/// # Why a canonical form rather than a string compare
///
/// The two sides legitimately spell the same polynomial differently — Zeebra writes `x1*x10-1`,
/// Groebner.jl echoes `x1*x10 + 1073741826`, the Sagebrush driver `1*x1*x10 + 1073741826` — and
/// neither term order, factor order within a monomial, nor the choice between `-1` and `p-1` is
/// meaningful. Reducing every coefficient mod `p` and sorting both levels makes the comparison
/// about the polynomial.
///
/// Tokenizing is on the explicit `*` and `^` separators and variable names are then matched
/// **whole**, which is the property that makes `x1` and `x10` distinguishable — the same property
/// both drivers' parsers have, and the one a greedy longest-prefix scan would lack.
pub fn canonical_generator(text: &str, characteristic: u64) -> String {
    let p = characteristic.max(2) as i128;
    let compact: String = text.chars().filter(|c| !c.is_whitespace()).collect();

    // Split into signed chunks without losing a sign, as the drivers' parsers do.
    let mut chunks: Vec<(i128, String)> = Vec::new();
    let mut sign: i128 = 1;
    let mut current = String::new();
    for character in compact.chars() {
        match character {
            '+' | '-' if !current.is_empty() => {
                chunks.push((sign, std::mem::take(&mut current)));
                sign = if character == '-' { -1 } else { 1 };
            }
            '+' => {}
            '-' => sign = -sign,
            _ => current.push(character),
        }
    }
    if !current.is_empty() {
        chunks.push((sign, current));
    }

    let mut terms: Vec<String> = Vec::new();
    for (sign, chunk) in chunks {
        let mut coefficient: i128 = 1;
        let mut factors: Vec<String> = Vec::new();
        for factor in chunk.split('*').filter(|factor| !factor.is_empty()) {
            let (base, exponent) = match factor.split_once('^') {
                Some((base, exponent)) => (base, exponent.parse::<u32>().unwrap_or(0)),
                None => (factor, 1),
            };
            match base.parse::<i128>() {
                // A numeric factor folds into the coefficient.
                Ok(value) => {
                    for _ in 0..exponent {
                        coefficient = coefficient * value % p;
                    }
                }
                // A variable name, matched whole.
                Err(_) => factors.push(if exponent == 1 {
                    base.to_string()
                } else {
                    format!("{}^{}", base, exponent)
                }),
            }
        }
        let coefficient = (sign * coefficient).rem_euclid(p);
        if coefficient == 0 {
            continue;
        }
        factors.sort();
        let monomial = if factors.is_empty() {
            "1".to_string()
        } else {
            factors.join("*")
        };
        terms.push(format!("{}*{}", coefficient, monomial));
    }
    terms.sort();
    terms.join("+")
}

/// Whether two systems are the same set of polynomials over `GF(characteristic)`.
///
/// A **set**, because neither generator order nor term order is meaningful. Returns the first
/// canonical pair that differs, for a diagnostic: at the variable counts where this matters a full
/// dump of both systems is unreadable, and the first disagreement is the useful part.
pub fn generators_agree(
    sent: &[String],
    echoed: &[String],
    characteristic: u64,
) -> Result<(), (String, String)> {
    let mut ours: Vec<String> = sent
        .iter()
        .map(|generator| canonical_generator(generator, characteristic))
        .collect();
    let mut theirs: Vec<String> = echoed
        .iter()
        .map(|generator| canonical_generator(generator, characteristic))
        .collect();
    ours.sort();
    theirs.sort();
    if ours == theirs {
        return Ok(());
    }
    let first = ours
        .iter()
        .zip(&theirs)
        .find(|(a, b)| a != b)
        .map(|(a, b)| (a.clone(), b.clone()))
        .unwrap_or_else(|| ("the generator multisets differ".to_string(), String::new()));
    Err(first)
}

/// The resources a run is allowed, declared before it starts.
///
/// **Declared, not discovered.** A limit is part of the result: a run that stopped at 600 seconds
/// means nothing without the 600, and two runs under different limits are not comparable even when
/// both finished. Every field is recorded with the run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Limits {
    /// Wall-clock limit, enforced by the harness.
    pub wall: Duration,

    /// Worker threads or processes the tool is told to use.
    ///
    /// Part of the comparison key. A single-threaded tool has not lost to a tool given 64 cores,
    /// and the existing scoreboard already refuses to compare across worker counts.
    pub workers: usize,

    /// A memory ceiling in bytes, if one is imposed.
    ///
    /// `None` means no ceiling was set — which is a fact about the run and not the same as a
    /// ceiling that was never reached.
    pub max_rss_bytes: Option<u64>,

    /// A tool-specific cap, as the flag that set it, for anything the two fields above cannot
    /// express — a degree bound, a maximum basis size.
    pub tool_caps: Vec<String>,
}

impl Limits {
    /// A wall-clock limit at one worker, no memory ceiling, no tool caps.
    pub fn wall(wall: Duration) -> Self {
        Self {
            wall,
            workers: 1,
            max_rss_bytes: None,
            tool_caps: Vec::new(),
        }
    }

    /// Set the worker count.
    pub fn with_workers(mut self, workers: usize) -> Self {
        self.workers = workers.max(1);
        self
    }

    /// Set a memory ceiling.
    pub fn with_max_rss_bytes(mut self, bytes: u64) -> Self {
        self.max_rss_bytes = Some(bytes);
        self
    }

    /// Add a tool-specific cap, recorded as the flag that set it.
    pub fn with_tool_cap(mut self, cap: impl Into<String>) -> Self {
        self.tool_caps.push(cap.into());
        self
    }

    /// True if `other` allows exactly the same resources.
    ///
    /// The precondition of a ratio: two wall times under different limits are not a speedup.
    pub fn comparable_with(&self, other: &Limits) -> bool {
        self.wall == other.wall
            && self.workers == other.workers
            && self.max_rss_bytes == other.max_rss_bytes
            && self.tool_caps == other.tool_caps
    }
}

/// Which build of a tool produced a result.
///
/// Recorded per sweep because a Gröbner engine's performance is not stable across versions, and a
/// figure without a version is not reproducible. Prove the tool runs by obtaining this.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ToolVersion {
    /// The tool's own name, as it reports it.
    pub tool: String,

    /// The version string, as the tool reports it.
    pub version: String,

    /// A commit, build number, or other finer identifier, where one is available.
    pub build: Option<String>,

    /// The raw text the version was parsed out of, kept so a misparse is recoverable.
    pub raw: String,
}

impl ToolVersion {
    /// A version from a tool name and a version string, with the string as its own raw text.
    pub fn new(tool: impl Into<String>, version: impl Into<String>) -> Self {
        let version = version.into();
        Self {
            tool: tool.into(),
            raw: version.clone(),
            version,
            build: None,
        }
    }

    /// Record a finer build identifier.
    pub fn with_build(mut self, build: impl Into<String>) -> Self {
        self.build = Some(build.into());
        self
    }

    /// Record the raw text the version was taken from.
    pub fn with_raw(mut self, raw: impl Into<String>) -> Self {
        self.raw = raw.into();
        self
    }
}

impl Display for ToolVersion {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.build {
            Some(build) => write!(f, "{} {} ({})", self.tool, self.version, build),
            None => write!(f, "{} {}", self.tool, self.version),
        }
    }
}

/// Why a tool cannot accept an instance or a task.
///
/// **A capability statement, never a performance statement.** A run that ends here has no wall
/// time worth reporting and must not appear in any ratio; the board records the missing capability
/// in the column where a number would go.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unsupported {
    /// The characteristic is outside the tool's range. `supported_below` is the tool's own bound.
    Characteristic {
        characteristic: u64,
        supported_below: u64,
    },

    /// The tool has no extension fields, or not this one.
    ExtensionField {
        characteristic: u64,
        extension_degree: u32,
    },

    /// The tool does not offer this task.
    Task { task: Task },

    /// The tool does not offer this monomial order.
    Order { order: MonomialOrder },

    /// The instance has more variables than the tool accepts.
    VariableCount { variables: usize, maximum: usize },

    /// The task needs a finite quotient algebra and the instance is positive-dimensional.
    ///
    /// A fact about the **ideal**, which is why it is named rather than left to
    /// [`Self::Representation`]: four adapters rediscovered the same classification from first
    /// principles and two of them put it in the failure bucket, so the distinction the protocol
    /// depends on was being re-derived per tool instead of being structural.
    PositiveDimensional { task: Task },

    /// The tool cannot represent the input for a reason the variants above do not cover.
    Representation { detail: String },
}

impl Display for Unsupported {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Characteristic {
                characteristic,
                supported_below,
            } => write!(
                f,
                "characteristic {} is at or above the tool's bound of {}",
                characteristic, supported_below
            ),
            Self::ExtensionField {
                characteristic,
                extension_degree,
            } => write!(
                f,
                "GF({}^{}) is not a field this tool represents",
                characteristic, extension_degree
            ),
            Self::Task { task } => write!(f, "the tool does not offer {}", task),
            Self::Order { order } => {
                write!(f, "the tool does not offer {} order", order_tag(*order))
            }
            Self::VariableCount { variables, maximum } => write!(
                f,
                "{} variables exceeds the tool's maximum of {}",
                variables, maximum
            ),
            Self::PositiveDimensional { task } => write!(
                f,
                "{} needs a finite quotient algebra, and this ideal is positive-dimensional",
                task
            ),
            Self::Representation { detail } => write!(f, "{}", detail),
        }
    }
}

/// Whether a tool can take on an instance and task at all.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Support {
    /// The tool accepts this instance and task.
    Yes,

    /// It does not, for this reason.
    No(Unsupported),
}

impl Support {
    /// True for [`Self::Yes`].
    pub fn is_supported(&self) -> bool {
        matches!(self, Self::Yes)
    }
}

/// Which declared limit stopped a run.
///
/// **Not a failure and not a time.** A run stopped at its limit gives a *lower bound* on the time
/// the tool needs and nothing more, so it may be reported as "> limit" and never as a measurement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LimitStop {
    /// The harness's wall-clock limit expired and the child was killed.
    WallClock { limit: Duration, elapsed: Duration },

    /// A memory ceiling was reached. `observed` is what had been measured when it was.
    Memory { limit: u64, observed: Option<u64> },

    /// The tool stopped itself at one of its own caps, and said so.
    ToolCap { detail: String },
}

impl Display for LimitStop {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WallClock { limit, .. } => write!(f, "stopped at a {:?} wall-clock limit", limit),
            Self::Memory { limit, .. } => write!(f, "stopped at a {} byte memory ceiling", limit),
            Self::ToolCap { detail } => write!(f, "stopped at the tool's own cap: {}", detail),
        }
    }
}

/// Why a run produced no usable answer, other than a limit or a capability gap.
///
/// The vocabulary is
/// [`OracleError`](crate::grobner::differential::OracleError)'s, which was arrived at by driving
/// one external system for a milestone; a new adapter that needs a variant not here should say so
/// rather than overloading [`Self::Reported`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RunFailure {
    /// The tool could not be started: not installed, or not on the path given.
    ///
    /// **The skipped-and-reported case.** A sweep must continue, the board must show the row as
    /// not attempted, and nothing about Zeebra may be concluded from it.
    Unavailable { binary: String, reason: String },

    /// The tool printed an error. Carries the first one.
    ///
    /// Several of these tools exit 0 after a script error — Singular does — so a clean exit status
    /// is not evidence that a run succeeded, and every adapter needs its own error-line check.
    Reported { message: String },

    /// The run ended before reaching the end of its script.
    Incomplete { detail: String },

    /// An expected marker was absent from an otherwise complete run.
    MissingMarker { marker: String },

    /// A marker's value was not of the shape the parser expects.
    Unparsable { marker: String, value: String },

    /// The tool contradicted itself — two of its own routes disagreed.
    ///
    /// An error and not a finding: nothing can be concluded about any other implementation from a
    /// run in which the reference was unsound.
    SelfInconsistent { detail: String },

    /// The tool exited non-zero without printing anything the adapter recognised.
    NonZeroExit { code: Option<i32> },

    /// **The tool** reported a failure of its own I/O.
    ///
    /// The tool ran, got far enough to touch a file of its own, and said so — msolve's
    /// `Cannot open output file` is the live instance. An attempted run that went wrong, so it is
    /// *not* counted by [`RunReport::was_skipped`]: the row is the tool's.
    ///
    /// Not for the harness's own filesystem work, which is [`Self::Harness`]. Which side failed is
    /// the distinction this whole contract is built on, and a single `Io` variant covering both
    /// attributed a full disk to the solver (#610).
    Io { reason: String },

    /// **The harness's own** filesystem or process work failed, so the tool was never started.
    ///
    /// Writing the input file or the script, creating the scratch directory, opening the output
    /// the child's stdout is redirected to, waiting on the child: every one of these is the
    /// harness's, and none of them is evidence about any solver. A full disk, an exhausted fd
    /// table or a `/tmp` that is momentarily unwell is not msolve losing a race.
    ///
    /// Counted by [`RunReport::was_skipped`], on exactly the argument [`Self::Environment`]
    /// already won: nothing ran, so there is no measurement and nothing to conclude.
    Harness { detail: String },

    /// The harness's own environment would have changed what was measured.
    ///
    /// **Not a property of the instance and not a property of the tool: a run that ends here was
    /// not attempted.** Something inherited would have selected a different algorithm, a different
    /// thread count, or polluted the output being parsed — and an adapter can set a child's
    /// environment but cannot clear it, so the condition cannot be fixed from inside the run.
    ///
    /// Distinct from every other variant here, which is why it exists rather than overloading
    /// [`Self::Reported`]:
    ///
    /// * not [`Self::Unavailable`] — the binary is present and would have started;
    /// * not [`Unsupported`] — nothing about the *instance* is unrepresentable, and `Unsupported`
    ///   is specifically a statement about the tool's declared capability;
    /// * not [`Self::Reported`] or [`Self::NonZeroExit`] — the tool never ran, so it printed
    ///   nothing and exited nothing;
    /// * not [`Self::Io`] — nothing of the *tool's* failed, because the tool never started;
    /// * not [`Self::Harness`] — nothing of the harness's filesystem work failed either.
    ///
    /// Counted by [`RunReport::was_skipped`], because a board must show the row as not attempted
    /// rather than as a result.
    ///
    /// `variable` is the inherited name, so an operator is told what to unset; `detail` is what it
    /// would have changed, so the refusal can be judged rather than merely obeyed.
    ///
    /// The case that motivated it: `engine/mpoly` reads seven `SB_*` switches with
    /// `env::var(..).is_ok()` — **truthy if set, so `SB_SIGF4=0` enables the experimental
    /// signature path** — and two of them write a trace into the stream the basis is parsed from.
    /// Any adapter driving a tool with environment-selected internals has the same problem.
    Environment { variable: String, detail: String },
}

impl Display for RunFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unavailable { binary, reason } => write!(f, "cannot run {}: {}", binary, reason),
            Self::Reported { message } => write!(f, "the tool reported an error: {}", message),
            Self::Incomplete { detail } => write!(f, "the run did not complete: {}", detail),
            Self::MissingMarker { marker } => write!(f, "no {} marker was printed", marker),
            Self::Unparsable { marker, value } => {
                write!(f, "the {} marker reads {:?}", marker, value)
            }
            Self::SelfInconsistent { detail } => {
                write!(f, "the tool disagrees with itself: {}", detail)
            }
            Self::NonZeroExit { code } => match code {
                Some(code) => write!(f, "the tool exited {}", code),
                None => write!(f, "the tool was killed by a signal"),
            },
            Self::Io { reason } => write!(f, "the tool reported an I/O failure: {}", reason),
            Self::Harness { detail } => write!(
                f,
                "not run: the harness's own filesystem work failed: {}",
                detail
            ),
            Self::Environment { variable, detail } => write!(
                f,
                "not run: the environment sets {}, which {}",
                variable, detail
            ),
        }
    }
}

impl std::error::Error for RunFailure {}

impl From<SpawnError> for RunFailure {
    fn from(e: SpawnError) -> Self {
        match e {
            SpawnError::Unavailable { binary, reason } => Self::Unavailable { binary, reason },
            SpawnError::Harness { detail } => Self::Harness { detail },
        }
    }
}

/// The harness's own I/O, never the tool's.
///
/// An adapter sees a [`std::io::Error`] only from work it did itself — the input file, the script,
/// the scratch directory — so `?` on one is [`RunFailure::Harness`]. The tool's own I/O reaches the
/// adapter as text in a log, and is classified by reading it.
impl From<std::io::Error> for RunFailure {
    fn from(e: std::io::Error) -> Self {
        Self::Harness {
            detail: e.to_string(),
        }
    }
}

/// Mathematically meaningful quantities that any correct answer must agree on.
///
/// The cross-library check. Two libraries' bases may be printed differently, ordered differently,
/// and scaled differently while being the same ideal's reduced basis — so a textual diff is the
/// wrong test. These are the invariants that are genuinely implementation-independent, and
/// [`Self::agree`] is the gate a timing must pass before it may be published.
///
/// Every field is optional because not every task yields every quantity. [`Self::agree`] compares
/// only fields **both** sides carry: an absent field is "not reported", never "zero", and never
/// evidence of agreement.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Invariants {
    /// `dim_k k[x]/I`, the number of standard monomials. Finite exactly when `I` is
    /// zero-dimensional.
    pub quotient_dimension: Option<usize>,

    /// The leading monomials of the reduced basis, as text, **sorted** so that the comparison is
    /// insensitive to the order the tool printed them in.
    ///
    /// The initial ideal, which is an invariant of the ideal and the order. Two correct reduced
    /// bases under the same order have the same one.
    pub leading_monomials: Option<Vec<String>>,

    /// The number of elements in the reduced basis.
    ///
    /// Implied by `leading_monomials` when that is present, and useful alone when a tool reports
    /// only a count.
    pub basis_cardinality: Option<usize>,

    /// The number of solutions in the coefficient field.
    pub solution_count: Option<usize>,

    /// The degree of the univariate eliminant.
    pub eliminant_degree: Option<usize>,
}

/// One invariant on which two answers differ.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Disagreement {
    /// Which invariant, as a stable name.
    pub invariant: &'static str,

    /// What the left-hand answer said.
    pub left: String,

    /// What the right-hand answer said.
    pub right: String,
}

impl Display for Disagreement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {} against {}",
            self.invariant, self.left, self.right
        )
    }
}

impl Invariants {
    /// Nothing reported.
    pub fn none() -> Self {
        Self::default()
    }

    /// Set the quotient dimension.
    pub fn with_quotient_dimension(mut self, dimension: usize) -> Self {
        self.quotient_dimension = Some(dimension);
        self
    }

    /// Set the leading monomials, sorting them so the comparison is order-insensitive.
    pub fn with_leading_monomials(mut self, monomials: Vec<String>) -> Self {
        let mut monomials = monomials;
        monomials.sort();
        self.basis_cardinality = Some(monomials.len());
        self.leading_monomials = Some(monomials);
        self
    }

    /// Set the basis cardinality.
    pub fn with_basis_cardinality(mut self, cardinality: usize) -> Self {
        self.basis_cardinality = Some(cardinality);
        self
    }

    /// Set the solution count.
    pub fn with_solution_count(mut self, count: usize) -> Self {
        self.solution_count = Some(count);
        self
    }

    /// Set the eliminant degree.
    pub fn with_eliminant_degree(mut self, degree: usize) -> Self {
        self.eliminant_degree = Some(degree);
        self
    }

    /// True if no invariant at all was reported.
    ///
    /// Worth checking before publishing: two empty `Invariants` "agree" vacuously, and that is not
    /// a verification.
    pub fn is_empty(&self) -> bool {
        self == &Self::default()
    }

    /// How many invariants both sides reported, and therefore how much [`Self::agree`] checked.
    pub fn overlap(&self, other: &Invariants) -> usize {
        let mut shared = 0;
        if self.quotient_dimension.is_some() && other.quotient_dimension.is_some() {
            shared += 1;
        }
        if self.leading_monomials.is_some() && other.leading_monomials.is_some() {
            shared += 1;
        }
        if self.basis_cardinality.is_some() && other.basis_cardinality.is_some() {
            shared += 1;
        }
        if self.solution_count.is_some() && other.solution_count.is_some() {
            shared += 1;
        }
        if self.eliminant_degree.is_some() && other.eliminant_degree.is_some() {
            shared += 1;
        }
        shared
    }

    /// Every invariant both sides reported and disagree on.
    ///
    /// Empty means every shared invariant matched. **Empty does not mean verified** — check
    /// [`Self::overlap`], because nothing shared also produces an empty list. That distinction is
    /// why this returns the disagreements rather than a `bool`.
    pub fn agree(&self, other: &Invariants) -> Vec<Disagreement> {
        let mut found = Vec::new();
        let mut compare = |invariant: &'static str, left: Option<String>, right: Option<String>| {
            if let (Some(left), Some(right)) = (left, right) {
                if left != right {
                    found.push(Disagreement {
                        invariant,
                        left,
                        right,
                    });
                }
            }
        };
        compare(
            "quotient-dimension",
            self.quotient_dimension.map(|d| d.to_string()),
            other.quotient_dimension.map(|d| d.to_string()),
        );
        compare(
            "leading-monomials",
            self.leading_monomials.as_ref().map(|m| m.join(",")),
            other.leading_monomials.as_ref().map(|m| m.join(",")),
        );
        compare(
            "basis-cardinality",
            self.basis_cardinality.map(|c| c.to_string()),
            other.basis_cardinality.map(|c| c.to_string()),
        );
        compare(
            "solution-count",
            self.solution_count.map(|c| c.to_string()),
            other.solution_count.map(|c| c.to_string()),
        );
        compare(
            "eliminant-degree",
            self.eliminant_degree.map(|d| d.to_string()),
            other.eliminant_degree.map(|d| d.to_string()),
        );
        found
    }
}

/// What a tool produced, as text, for the harness to check and record.
///
/// Optional throughout: a tool asked for one solution has no basis to report, and a tool that
/// reports only a count has no basis elements. Absent is "not reported".
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Answer {
    /// The basis elements, as the tool printed them.
    pub basis: Option<Vec<String>>,

    /// Solutions, each a vector of coefficients in the instance's variable order.
    pub solutions: Option<Vec<Vec<String>>>,

    /// The univariate eliminant, as text.
    pub eliminant: Option<String>,

    /// Invariants extracted from the answer, which is what a cross-library check compares.
    pub invariants: Invariants,
}

impl Answer {
    /// An answer carrying only invariants.
    pub fn from_invariants(invariants: Invariants) -> Self {
        Self {
            invariants,
            ..Self::default()
        }
    }

    /// Attach the basis elements.
    pub fn with_basis(mut self, basis: Vec<String>) -> Self {
        self.basis = Some(basis);
        self
    }

    /// Attach the solutions.
    pub fn with_solutions(mut self, solutions: Vec<Vec<String>>) -> Self {
        self.solutions = Some(solutions);
        self
    }

    /// Attach the eliminant.
    pub fn with_eliminant(mut self, eliminant: impl Into<String>) -> Self {
        self.eliminant = Some(eliminant.into());
        self
    }
}

/// What independently agreed with an answer, and on what.
///
/// Carried by [`RunStatus::Verified`] so that "verified" is never a bare assertion: the record
/// says who checked, which invariants were shared, and therefore how strong the check was.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Verification {
    /// What did the checking: another tool's id, `zeebra`, or a published value.
    pub checked_against: String,

    /// The invariants that agreed.
    pub agreed: Invariants,

    /// How many invariants both sides reported. **Zero means nothing was actually checked.**
    pub shared_invariants: usize,

    /// A human-readable note on anything the fields above cannot express.
    pub note: Option<String>,
}

impl Verification {
    /// A verification against `checked_against`, agreeing on the invariants `theirs` shares with
    /// `ours`.
    ///
    /// # Errors
    /// The disagreements, if any shared invariant differs. A disagreement is never a verification.
    pub fn of(
        checked_against: impl Into<String>,
        ours: &Invariants,
        theirs: &Invariants,
    ) -> Result<Self, Vec<Disagreement>> {
        let disagreements = ours.agree(theirs);
        if !disagreements.is_empty() {
            return Err(disagreements);
        }
        Ok(Self {
            checked_against: checked_against.into(),
            agreed: ours.clone(),
            shared_invariants: ours.overlap(theirs),
            note: None,
        })
    }

    /// Add a note.
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.note = Some(note.into());
        self
    }

    /// True if at least one invariant was actually compared.
    pub fn is_substantive(&self) -> bool {
        self.shared_invariants > 0
    }
}

/// How a run ended. Five outcomes, and the distinctions between them are the point.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RunStatus {
    /// The tool produced an answer, which has not been independently checked.
    ///
    /// A timing from here is publishable only alongside the fact that it is unverified.
    Complete(Answer),

    /// The tool produced an answer **and** something independent agreed with it.
    Verified(Answer, Verification),

    /// A declared limit stopped it. There is no answer, and the wall time is the limit.
    StoppedByLimit(LimitStop),

    /// The tool cannot accept this instance or task. **Never comparable as "slower".**
    Unsupported(Unsupported),

    /// The tool ran and failed.
    Failed(RunFailure),
}

impl RunStatus {
    /// The stable tag used in records and tables.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::Complete(_) => "complete",
            Self::Verified(_, _) => "verified",
            Self::StoppedByLimit(_) => "stopped-by-limit",
            Self::Unsupported(_) => "unsupported",
            Self::Failed(_) => "failed",
        }
    }

    /// The answer, if there is one.
    pub fn answer(&self) -> Option<&Answer> {
        match self {
            Self::Complete(answer) | Self::Verified(answer, _) => Some(answer),
            _ => None,
        }
    }

    /// True if the tool produced an answer, checked or not.
    pub fn answered(&self) -> bool {
        self.answer().is_some()
    }

    /// True if the answer was independently checked **and** the check compared something.
    pub fn is_verified(&self) -> bool {
        match self {
            Self::Verified(_, verification) => verification.is_substantive(),
            _ => false,
        }
    }

    /// True if the wall time of this run may be used as a measurement of the tool's speed.
    ///
    /// **The gate on every ratio.** False for a limit stop (the time is the limit), for an
    /// unsupported input (there is no time), and for a failure (the time is the time to fail).
    pub fn is_timing_evidence(&self) -> bool {
        self.answered()
    }
}

/// One run of one tool on one instance: everything a record or a board row needs.
///
/// Produced by [`ExternalSolver::run`] for **every** outcome, including the ones with no answer. A
/// board that silently dropped its failures would report a tool's best cases as its behaviour.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunReport {
    /// The tool's id, as [`ExternalSolver::id`] gives it.
    pub solver: String,

    /// The tool's version, where the harness probed it.
    pub version: Option<ToolVersion>,

    /// The instance name.
    pub instance: String,

    /// The instance's identity digest. Two rows with different digests are different problems.
    pub instance_digest: String,

    /// What was asked.
    pub task: Task,

    /// The resources the run was allowed.
    pub limits: Limits,

    /// How it ended.
    pub status: RunStatus,

    /// What it cost.
    pub measurement: Measurement,

    /// The exact command that was run, for the reproduction field of a record.
    pub command_line: Option<String>,

    /// Where the raw output was kept, if it was kept.
    ///
    /// Worth keeping for a failure: the log is the evidence, and a parse error is not diagnosable
    /// without it.
    pub log_path: Option<PathBuf>,
}

impl RunReport {
    /// A report from its parts.
    pub fn new(
        solver: impl Into<String>,
        instance: &Instance,
        task: Task,
        limits: &Limits,
        status: RunStatus,
        measurement: Measurement,
    ) -> Self {
        Self {
            solver: solver.into(),
            version: None,
            instance: instance.name.clone(),
            instance_digest: instance.digest(),
            task,
            limits: limits.clone(),
            status,
            measurement,
            command_line: None,
            log_path: None,
        }
    }

    /// A report for an instance the tool cannot accept, with no measurement.
    ///
    /// The measurement is deliberately empty: nothing was run, so there is no time, and a zero
    /// would be read as an instantaneous success by anything that did not check the status.
    pub fn unsupported(
        solver: impl Into<String>,
        instance: &Instance,
        task: Task,
        limits: &Limits,
        reason: Unsupported,
    ) -> Self {
        Self::new(
            solver,
            instance,
            task,
            limits,
            RunStatus::Unsupported(reason),
            Measurement::unmeasured(),
        )
    }

    /// A report for a tool that could not be started.
    pub fn unavailable(
        solver: impl Into<String>,
        instance: &Instance,
        task: Task,
        limits: &Limits,
        binary: impl Into<String>,
        reason: impl Into<String>,
    ) -> Self {
        Self::new(
            solver,
            instance,
            task,
            limits,
            RunStatus::Failed(RunFailure::Unavailable {
                binary: binary.into(),
                reason: reason.into(),
            }),
            Measurement::unmeasured(),
        )
    }

    /// Record the tool version.
    pub fn with_version(mut self, version: ToolVersion) -> Self {
        self.version = Some(version);
        self
    }

    /// Record the command line that produced this run.
    pub fn with_command_line(mut self, command_line: impl Into<String>) -> Self {
        self.command_line = Some(command_line.into());
        self
    }

    /// Record where the raw output was kept.
    pub fn with_log_path(mut self, path: impl Into<PathBuf>) -> Self {
        self.log_path = Some(path.into());
        self
    }

    /// True if this run was skipped rather than attempted.
    ///
    /// The four cases a board shows as "not attempted" rather than as a result: the input is
    /// unrepresentable ([`RunStatus::Unsupported`]), the tool is absent
    /// ([`RunFailure::Unavailable`]), the harness's own environment would have invalidated the
    /// measurement ([`RunFailure::Environment`]), or the harness's own filesystem work failed
    /// ([`RunFailure::Harness`]).
    ///
    /// The common property is that **the tool did not run**, so there is no measurement and nothing
    /// about any implementation follows. Every other [`RunFailure`] describes a run that was
    /// attempted and went wrong, which is a different thing for a reader to act on — including
    /// [`RunFailure::Io`], which is the *tool's* I/O and therefore the tool's row.
    pub fn was_skipped(&self) -> bool {
        matches!(
            &self.status,
            RunStatus::Unsupported(_)
                | RunStatus::Failed(
                    RunFailure::Unavailable { .. }
                        | RunFailure::Environment { .. }
                        | RunFailure::Harness { .. }
                )
        )
    }

    /// The speedup of `self` over `other`, or why there is none.
    ///
    /// # Errors
    /// [`NotComparable`] whenever a ratio would be meaningless: different problems, different
    /// tasks, different resource limits, an outcome that is not timing evidence, or a zero
    /// denominator. This is the only place a ratio is computed, so that no caller can skip the
    /// checks.
    pub fn speedup_over(&self, other: &RunReport) -> Result<f64, NotComparable> {
        if self.instance_digest != other.instance_digest {
            return Err(NotComparable::DifferentProblems {
                left: self.instance_digest.clone(),
                right: other.instance_digest.clone(),
            });
        }
        if self.task != other.task {
            return Err(NotComparable::DifferentTasks {
                left: self.task,
                right: other.task,
            });
        }
        if !self.limits.comparable_with(&other.limits) {
            return Err(NotComparable::DifferentLimits);
        }
        if !self.status.is_timing_evidence() {
            return Err(NotComparable::NotTimingEvidence {
                solver: self.solver.clone(),
                status: self.status.tag(),
            });
        }
        if !other.status.is_timing_evidence() {
            return Err(NotComparable::NotTimingEvidence {
                solver: other.solver.clone(),
                status: other.status.tag(),
            });
        }
        let ours = self.measurement.wall.as_secs_f64();
        let theirs = other.measurement.wall.as_secs_f64();
        if ours <= 0.0 {
            return Err(NotComparable::ZeroTime {
                solver: self.solver.clone(),
            });
        }
        Ok(theirs / ours)
    }
}

/// Why two runs cannot be made into a ratio.
///
/// Every variant is a case where a published speedup would be false rather than imprecise.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NotComparable {
    /// The instance digests differ, so these are two problems.
    DifferentProblems { left: String, right: String },

    /// Different members of the task taxonomy.
    DifferentTasks { left: Task, right: Task },

    /// Different resource limits, so neither time means what the other does.
    DifferentLimits,

    /// One run's outcome is not a measurement of speed: a limit stop, an unsupported input, or a
    /// failure.
    NotTimingEvidence {
        solver: String,
        status: &'static str,
    },

    /// A wall time of zero, which no ratio can use.
    ZeroTime { solver: String },
}

impl Display for NotComparable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DifferentProblems { left, right } => write!(
                f,
                "different problems: {} against {}",
                &left[..left.len().min(12)],
                &right[..right.len().min(12)]
            ),
            Self::DifferentTasks { left, right } => {
                write!(f, "different tasks: {} against {}", left, right)
            }
            Self::DifferentLimits => write!(f, "different resource limits"),
            Self::NotTimingEvidence { solver, status } => {
                write!(f, "{} did not produce a timing: {}", solver, status)
            }
            Self::ZeroTime { solver } => write!(f, "{} recorded a wall time of zero", solver),
        }
    }
}

/// What a run cost, with the basis of every figure recorded beside it.
///
/// The basis fields are not decoration. `VmHWM` of a direct child and a sampled sum over a process
/// tree are different quantities, and a board that compared one with the other would be wrong
/// without being obviously wrong.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Measurement {
    /// Wall-clock time of the whole run, including input conversion if the adapter times it that
    /// way — which it should not; see [`Self::stages`].
    pub wall: Duration,

    /// CPU time, where the platform reported one.
    pub cpu: Option<Duration>,

    /// How `cpu` was obtained.
    pub cpu_basis: CpuBasis,

    /// Peak resident set size of the solver process, in bytes.
    pub peak_rss_bytes: Option<u64>,

    /// How `peak_rss_bytes` was obtained. **Read before comparing two figures.**
    pub rss_basis: RssBasis,

    /// Stage timings the tool itself reported, in the order it reported them.
    ///
    /// Tool-reported, so the names are the tool's and the sum need not be `wall`. Keep the
    /// harness's own costs — writing the input file, parsing the output — out of `wall` where
    /// possible and in here where not, so that a published figure is the solver's time.
    pub stages: Vec<(String, Duration)>,
}

impl Measurement {
    /// A measurement with a wall time and nothing else.
    pub fn wall(wall: Duration) -> Self {
        Self {
            wall,
            cpu: None,
            cpu_basis: CpuBasis::Unavailable,
            peak_rss_bytes: None,
            rss_basis: RssBasis::Unavailable,
            stages: Vec::new(),
        }
    }

    /// No measurement at all: nothing was run.
    ///
    /// A zero wall time **with** [`RssBasis::Unavailable`], which is how a consumer tells it from
    /// an instantaneous success. Use for [`RunStatus::Unsupported`] and for a tool that would not
    /// start.
    pub fn unmeasured() -> Self {
        Self::wall(Duration::ZERO)
    }

    /// The measurement of a supervised process.
    pub fn of_process(measurement: &ProcessMeasurement) -> Self {
        Self {
            wall: measurement.wall,
            cpu: measurement.cpu,
            cpu_basis: measurement.cpu_basis,
            peak_rss_bytes: measurement.peak_rss_bytes,
            rss_basis: measurement.rss_basis,
            stages: Vec::new(),
        }
    }

    /// Add a tool-reported stage timing.
    pub fn with_stage(mut self, name: impl Into<String>, elapsed: Duration) -> Self {
        self.stages.push((name.into(), elapsed));
        self
    }

    /// True if nothing was measured, because nothing was run.
    pub fn is_unmeasured(&self) -> bool {
        self.wall.is_zero()
            && self.cpu.is_none()
            && self.peak_rss_bytes.is_none()
            && self.stages.is_empty()
    }
}

/// An external Gröbner engine, driven as a subprocess.
///
/// # Implementing this
///
/// See the module documentation for the order a harness calls these in and the list of things an
/// adapter must not do itself. The short version: describe the invocation, let
/// [`Supervisor`](super::process::Supervisor) run it, parse markers out of the output file, and
/// return a [`RunReport`] for every outcome including the ones with no answer.
///
/// # Why `&mut self`
///
/// An adapter accumulates state across a sweep — a scratch-file counter, a cached version probe —
/// and a shared `&self` would mean two concurrent runs handing the same filename to two processes.
/// Concurrency is one adapter per worker, each with its own scratch directory, as
/// [`SingularOracle::fleet`](crate::grobner::differential::SingularOracle::fleet) does.
pub trait ExternalSolver {
    /// The tool's stable id, used as the `library` column of a board: `singular`, `msolve`,
    /// `groebner.jl`, `sagebrush`, `zeebra`.
    ///
    /// Lowercase, stable across versions, and part of no digest — the version is recorded
    /// separately.
    fn id(&self) -> &str;

    /// Which build of the tool this is, obtained by running it.
    ///
    /// Call once before a sweep. Doing so is also the cheapest way to discover that the tool is
    /// absent: the alternative is finding out once per instance, for however many instances were
    /// queued.
    ///
    /// # Errors
    /// [`RunFailure::Unavailable`] if the binary could not be started — the skipped-and-reported
    /// case. Any other [`RunFailure`] if it ran but its version could not be read.
    fn probe_version(&mut self) -> Result<ToolVersion, RunFailure>;

    /// Whether this tool can accept this instance and this task, decided **without running it**.
    ///
    /// Must be a statement about the tool's declared capabilities — a characteristic bound, an
    /// absent task, a variable limit — expressed as constants in the adapter the way
    /// [`MAX_CHARACTERISTIC`](crate::grobner::differential::MAX_CHARACTERISTIC) is. Not a guess
    /// about whether the run would finish: that is what [`Limits`] and
    /// [`RunStatus::StoppedByLimit`] are for, and the two must not be confused.
    fn supports(&self, instance: &Instance, task: Task) -> Support;

    /// Run the task on the instance under the limits, and report what happened.
    ///
    /// Infallible by design: every failure is a [`RunStatus`], because a sweep must record the
    /// failures rather than lose them, and a `Result` invites a caller to discard the `Err` arm.
    /// Re-check [`Self::supports`] here — a harness that forgot to call it must still get
    /// [`RunStatus::Unsupported`] rather than a number.
    fn run(&mut self, instance: &Instance, task: Task, limits: &Limits) -> RunReport;
}

#[cfg(test)]
mod tests {
    use super::{
        order_from_tag, order_tag, FieldSpec, Instance, Invariants, Limits, Measurement,
        NotComparable, RunFailure, RunReport, RunStatus, SpawnError, Support, Task, ToolVersion,
        Unsupported, Verification,
    };
    use crate::MonomialOrder;
    use std::time::Duration;

    fn instance() -> Instance {
        Instance::new(
            "katsura-4",
            "katsura",
            FieldSpec::prime(65521),
            vec!["x1".to_string(), "x2".to_string()],
            vec!["x1^2+x2-1".to_string(), "x2^2-x1".to_string()],
            MonomialOrder::GradedReverseLexicographic,
        )
    }

    fn report(solver: &str, status: RunStatus, wall_ms: u64) -> RunReport {
        RunReport::new(
            solver,
            &instance(),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(600)),
            status,
            Measurement::wall(Duration::from_millis(wall_ms)),
        )
    }

    fn answered() -> RunStatus {
        RunStatus::Complete(super::Answer::from_invariants(
            Invariants::none().with_quotient_dimension(4),
        ))
    }

    /// Every task tag round-trips, so a record's tag names exactly one task.
    #[test]
    fn test_every_task_tag_round_trips() {
        for task in Task::all() {
            assert_eq!(Task::from_tag(task.tag()), Some(task), "{}", task.tag());
        }
        assert_eq!(Task::from_tag("grobner"), None);
    }

    /// Every monomial order tag round-trips.
    #[test]
    fn test_every_order_tag_round_trips() {
        for order in [
            MonomialOrder::Lexicographic,
            MonomialOrder::GradedLexicographic,
            MonomialOrder::GradedReverseLexicographic,
        ] {
            assert_eq!(order_from_tag(order_tag(order)), Some(order));
        }
        assert_eq!(order_from_tag("deglex"), None);
    }

    /// The identity digest ignores the instance name and covers the generators.
    ///
    /// Renaming a problem must not make it a new one; changing an equation must.
    #[test]
    fn test_the_digest_ignores_the_name_and_covers_the_system() {
        let mut renamed = instance();
        renamed.name = "katsura-4-again".to_string();
        assert_eq!(instance().digest(), renamed.digest());

        let mut changed = instance();
        changed.system[0] = "x1^2+x2-2".to_string();
        assert_ne!(instance().digest(), changed.digest());
    }

    /// The digest covers the monomial order, the variable order, and any transformation.
    ///
    /// All three change the answer, so none of them may be absent from the problem's identity.
    #[test]
    fn test_the_digest_covers_the_order_the_variables_and_the_transformation() {
        let base = instance();

        let mut relabelled = instance();
        relabelled.order = MonomialOrder::Lexicographic;
        assert_ne!(base.digest(), relabelled.digest(), "monomial order");

        let mut reordered = instance();
        reordered.variables.reverse();
        assert_ne!(base.digest(), reordered.digest(), "variable order");

        let transformed = instance().transformed("field equations added");
        assert_ne!(base.digest(), transformed.digest(), "transformation");
    }

    /// The digest covers the field, including an extension's defining polynomial.
    ///
    /// Two tools' default `GF(2^8)` need not be the same ring, so the polynomial is identity.
    #[test]
    fn test_the_digest_covers_the_field_and_its_defining_polynomial() {
        let mut one = instance();
        one.field = FieldSpec::extension(2, 8, "t^8+t^4+t^3+t+1");
        let mut other = instance();
        other.field = FieldSpec::extension(2, 8, "t^8+t^4+t^3+t^2+1");
        assert_ne!(one.digest(), other.digest());

        let mut prime = instance();
        prime.field = FieldSpec::prime(2);
        assert_ne!(one.digest(), prime.digest());
    }

    /// Only invariants both sides report are compared, and a shared disagreement is found.
    #[test]
    fn test_only_shared_invariants_are_compared() {
        let ours = Invariants::none()
            .with_quotient_dimension(8)
            .with_leading_monomials(vec!["x2^2".to_string(), "x1".to_string()]);
        let theirs = Invariants::none().with_quotient_dimension(8);

        assert!(ours.agree(&theirs).is_empty(), "the shared one matches");
        assert_eq!(ours.overlap(&theirs), 1, "only the dimension is shared");

        let disagrees = Invariants::none().with_quotient_dimension(9);
        let found = ours.agree(&disagrees);
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].invariant, "quotient-dimension");
    }

    /// Leading monomials are sorted on the way in, so print order does not create a disagreement.
    #[test]
    fn test_leading_monomials_compare_regardless_of_print_order() {
        let ours = Invariants::none().with_leading_monomials(vec!["x1".to_string(), "x2^2".into()]);
        let theirs =
            Invariants::none().with_leading_monomials(vec!["x2^2".to_string(), "x1".into()]);
        assert!(ours.agree(&theirs).is_empty());
        assert_eq!(ours.basis_cardinality, Some(2));
    }

    /// Two empty invariant sets agree vacuously, and `overlap` is what exposes that.
    ///
    /// The trap this guards: an adapter that extracts nothing would otherwise "verify" everything.
    #[test]
    fn test_nothing_shared_is_not_a_verification() {
        let nothing = Invariants::none();
        assert!(nothing.agree(&nothing).is_empty());
        assert_eq!(nothing.overlap(&nothing), 0);
        assert!(nothing.is_empty());

        let verification = Verification::of("msolve", &nothing, &nothing).expect("no disagreement");
        assert!(
            !verification.is_substantive(),
            "a check that compared nothing is not substantive"
        );
        let status = RunStatus::Verified(super::Answer::default(), verification);
        assert!(
            !status.is_verified(),
            "Verified with nothing compared must not read as verified"
        );
    }

    /// A disagreement makes a verification an error rather than a weaker verification.
    #[test]
    fn test_a_disagreement_is_not_a_verification() {
        let ours = Invariants::none().with_quotient_dimension(8);
        let theirs = Invariants::none().with_quotient_dimension(7);
        let found = Verification::of("msolve", &ours, &theirs).expect_err("they disagree");
        assert_eq!(found.len(), 1);
    }

    /// A verified answer with something actually compared reads as verified.
    #[test]
    fn test_a_substantive_verification_reads_as_verified() {
        let ours = Invariants::none().with_quotient_dimension(8);
        let verification = Verification::of("zeebra", &ours, &ours).expect("agreement");
        assert!(verification.is_substantive());
        assert!(RunStatus::Verified(super::Answer::default(), verification).is_verified());
    }

    /// Only an answered run is timing evidence; a limit stop, an unsupported input and a failure
    /// are not.
    #[test]
    fn test_only_an_answered_run_is_timing_evidence() {
        assert!(answered().is_timing_evidence());
        assert!(!RunStatus::StoppedByLimit(super::LimitStop::WallClock {
            limit: Duration::from_secs(600),
            elapsed: Duration::from_secs(600),
        })
        .is_timing_evidence());
        assert!(!RunStatus::Unsupported(Unsupported::Task {
            task: Task::LexBasis
        })
        .is_timing_evidence());
        assert!(
            !RunStatus::Failed(RunFailure::Incomplete { detail: "x".into() }).is_timing_evidence()
        );
    }

    /// A speedup is computed for two answered runs of the same task on the same problem.
    #[test]
    fn test_a_speedup_is_computed_for_equivalent_answered_runs() {
        let fast = report("zeebra", answered(), 100);
        let slow = report("singular", answered(), 400);
        let ratio = fast.speedup_over(&slow).expect("comparable");
        assert!((ratio - 4.0).abs() < 1e-9, "{}", ratio);
    }

    /// No speedup is quoted against a tool that could not represent the input.
    ///
    /// The headline rule of the comparison protocol, enforced where the ratio is computed so that
    /// no caller can bypass it.
    #[test]
    fn test_no_speedup_is_quoted_against_an_unsupported_input() {
        let ours = report("zeebra", answered(), 100);
        let theirs = report(
            "msolve",
            RunStatus::Unsupported(Unsupported::Characteristic {
                characteristic: 1 << 61,
                supported_below: 1 << 31,
            }),
            0,
        );
        assert!(matches!(
            ours.speedup_over(&theirs),
            Err(NotComparable::NotTimingEvidence { .. })
        ));
    }

    /// No speedup is quoted against a run that was stopped by its limit.
    #[test]
    fn test_no_speedup_is_quoted_against_a_limit_stop() {
        let ours = report("zeebra", answered(), 100);
        let theirs = report(
            "singular",
            RunStatus::StoppedByLimit(super::LimitStop::WallClock {
                limit: Duration::from_secs(600),
                elapsed: Duration::from_secs(600),
            }),
            600_000,
        );
        assert!(matches!(
            ours.speedup_over(&theirs),
            Err(NotComparable::NotTimingEvidence { .. })
        ));
    }

    /// No speedup across two different problems, two different tasks, or two different limits.
    #[test]
    fn test_no_speedup_across_problems_tasks_or_limits() {
        let ours = report("zeebra", answered(), 100);

        let mut other_problem = report("singular", answered(), 400);
        other_problem.instance_digest = "deadbeef".repeat(8);
        assert!(matches!(
            ours.speedup_over(&other_problem),
            Err(NotComparable::DifferentProblems { .. })
        ));

        let mut other_task = report("singular", answered(), 400);
        other_task.task = Task::AllFiniteFieldSolutions;
        assert!(matches!(
            ours.speedup_over(&other_task),
            Err(NotComparable::DifferentTasks { .. })
        ));

        let mut other_limits = report("singular", answered(), 400);
        other_limits.limits = Limits::wall(Duration::from_secs(60)).with_workers(8);
        assert!(matches!(
            ours.speedup_over(&other_limits),
            Err(NotComparable::DifferentLimits)
        ));
    }

    /// An unsupported report carries no measurement, so nothing reads it as an instant success.
    #[test]
    fn test_an_unsupported_report_carries_no_measurement() {
        let report = RunReport::unsupported(
            "msolve",
            &instance(),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(600)),
            Unsupported::Characteristic {
                characteristic: 1 << 61,
                supported_below: 1 << 31,
            },
        );
        assert!(report.measurement.is_unmeasured());
        assert!(report.was_skipped());
        assert_eq!(report.status.tag(), "unsupported");
    }

    /// A tool that would not start is a skipped run, not a failed solve.
    #[test]
    fn test_an_absent_tool_is_a_skipped_run() {
        let report = RunReport::unavailable(
            "msolve",
            &instance(),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(600)),
            "msolve",
            "No such file or directory",
        );
        assert!(report.was_skipped());
        assert!(!report.status.answered());
    }

    /// A run refused because of the harness's own environment is a skipped run, not a failed one.
    ///
    /// Nothing ran, so there is no measurement and nothing about any implementation follows from
    /// it. A board that showed it as a result would be reporting a figure for a question nobody
    /// asked.
    #[test]
    fn test_a_hostile_environment_is_a_skipped_run_and_not_a_failed_solve() {
        let report = RunReport::new(
            "sagebrush",
            &instance(),
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(600)),
            RunStatus::Failed(RunFailure::Environment {
                variable: "SB_SIGF4".to_string(),
                detail: "selects the experimental signature-based F4".to_string(),
            }),
            Measurement::unmeasured(),
        );
        assert!(report.was_skipped(), "nothing was attempted");
        assert!(!report.status.answered());
        assert!(report.measurement.is_unmeasured());
    }

    /// `Environment` names the variable and what it would have changed.
    ///
    /// The message is the whole value of the variant over `Reported`: an operator reading it has to
    /// learn which variable to unset.
    #[test]
    fn test_the_environment_failure_names_the_variable_and_the_effect() {
        let failure = RunFailure::Environment {
            variable: "SB_F4_SHAPE".to_string(),
            detail: "writes matrix shape statistics into the parsed output".to_string(),
        };
        let rendered = failure.to_string();
        assert!(rendered.contains("SB_F4_SHAPE"), "{}", rendered);
        assert!(rendered.contains("matrix shape statistics"), "{}", rendered);
        // Not phrased as the tool's doing: the tool never ran.
        assert!(
            !rendered.contains("the tool reported"),
            "an environment refusal is not a tool error: {}",
            rendered
        );
    }

    /// A failure of the harness's own scratch I/O is a skipped run, not a failed solve.
    ///
    /// The tool was never started, so a full disk or an exhausted fd table is not the solver's
    /// loss — which is what `RunFailure::Io` made it read as before #610.
    #[test]
    fn test_a_failed_harness_write_is_a_skipped_run_and_not_a_failed_solve() {
        let report = report(
            "msolve",
            RunStatus::Failed(RunFailure::Harness {
                detail: "/tmp/zb/katsura-4.ms: No space left on device".to_string(),
            }),
            0,
        );
        assert!(report.was_skipped(), "nothing was attempted");
        assert!(!report.status.answered());
        assert!(!report.status.is_timing_evidence());
    }

    /// An I/O failure the **tool** reported is an attempted run, so it is not skipped.
    ///
    /// The other half of #610's split: msolve saying it cannot open its own output file is a row
    /// about msolve.
    #[test]
    fn test_a_tool_reported_io_failure_is_an_attempted_run() {
        let report = report(
            "msolve",
            RunStatus::Failed(RunFailure::Io {
                reason: "msolve could not open its output file".to_string(),
            }),
            0,
        );
        assert!(
            !report.was_skipped(),
            "the tool ran and reported its own I/O failure"
        );
    }

    /// The two I/O failures say which side failed, and neither borrows the other's phrasing.
    #[test]
    fn test_the_two_io_failures_name_which_side_failed() {
        let harness = RunFailure::Harness {
            detail: "/tmp/zb: Permission denied".to_string(),
        }
        .to_string();
        assert!(harness.contains("the harness's own"), "{}", harness);
        assert!(harness.starts_with("not run"), "{}", harness);
        assert!(
            !harness.contains("the tool"),
            "a harness failure is not the tool's: {}",
            harness
        );

        let tool = RunFailure::Io {
            reason: "could not open its output file".to_string(),
        }
        .to_string();
        assert!(tool.contains("the tool reported"), "{}", tool);
        assert!(!tool.contains("harness"), "{}", tool);
    }

    /// A `std::io::Error` and a supervisor `Harness` error both land on `RunFailure::Harness`.
    ///
    /// The conversions are where an adapter's `?` decides the classification, so they are the only
    /// place the split can be undone by accident.
    #[test]
    fn test_the_io_conversions_classify_as_the_harness_side() {
        let from_io: RunFailure =
            std::io::Error::new(std::io::ErrorKind::PermissionDenied, "denied").into();
        assert!(
            matches!(from_io, RunFailure::Harness { .. }),
            "{:?}",
            from_io
        );

        let from_spawn: RunFailure = SpawnError::Harness {
            detail: "denied".to_string(),
        }
        .into();
        assert!(
            matches!(from_spawn, RunFailure::Harness { .. }),
            "{:?}",
            from_spawn
        );

        let absent: RunFailure = SpawnError::Unavailable {
            binary: "msolve".to_string(),
            reason: "no such file".to_string(),
        }
        .into();
        assert!(matches!(absent, RunFailure::Unavailable { .. }));
    }

    /// Limits are comparable only when every declared resource matches.
    #[test]
    fn test_limits_are_comparable_only_when_every_resource_matches() {
        let base = Limits::wall(Duration::from_secs(600)).with_workers(1);
        assert!(base.comparable_with(&base.clone()));
        assert!(!base.comparable_with(&base.clone().with_workers(8)));
        assert!(!base.comparable_with(&Limits::wall(Duration::from_secs(60))));
        assert!(!base.comparable_with(&base.clone().with_tool_cap("-d 20")));
    }

    /// A tool version renders with its build when it has one.
    #[test]
    fn test_a_tool_version_renders_with_its_build() {
        assert_eq!(
            ToolVersion::new("singular", "4.4.1").to_string(),
            "singular 4.4.1"
        );
        assert_eq!(
            ToolVersion::new("singular", "4.4.1")
                .with_build("44105")
                .to_string(),
            "singular 4.4.1 (44105)"
        );
    }

    /// Support reports a reason when it says no.
    #[test]
    fn test_support_carries_its_reason() {
        assert!(Support::Yes.is_supported());
        let no = Support::No(Unsupported::Order {
            order: MonomialOrder::GradedLexicographic,
        });
        assert!(!no.is_supported());
        match no {
            Support::No(reason) => assert!(reason.to_string().contains("grlex")),
            Support::Yes => panic!("expected No"),
        }
    }
}
