//! The registry: which public problems M23 is measured against, frozen before anything is run.
//!
//! An [`InstanceManifest`](super::InstanceManifest) says what a *file* is. A
//! [`ChallengeManifest`] says what a **problem** is — the objective a public program stated, the
//! parameters it stated them over, and how a claimed solution is checked by something that is not
//! this crate. The two are separate because a challenge need not be a file: the 2026 CICO targets
//! are a sentence and five numbers, and their round constants are *derived* rather than published.
//!
//! # Three classes that are never added together
//!
//! [`BenchmarkClass`] is the type that keeps the scoreboard honest. A verified witness for a
//! `t = 2` planted instance and a verified witness for the official `t = 16` CICO target are both
//! "solved" in a column that aggregates them, and they are not comparable in any direction. So
//! every registered problem carries its class, a witness's meaning is computed from the class
//! rather than asserted by a report ([`Significance`]), and nothing here produces a single score.
//!
//! # Identity is a digest over the problem, not over the paperwork
//!
//! [`ChallengeManifest::digest`] covers the family, the parameters, the target values and the
//! objective — everything that changes which mathematical problem is being solved. It deliberately
//! excludes the program's URL, its reward, its external status and the prose of its verifier,
//! because those are things that get corrected or that change on the program's side, and an
//! identity that moved when a bounty was paid would break every historical comparison keyed on it.
//!
//! What this buys: a comparison tool can refuse to compare two runs whose digests differ, which is
//! the one failure the plan singles out — silently comparing different mathematical problems.
//!
//! # Frozen
//!
//! [`registry`] is a constant function and `test_the_registry_is_frozen` pins every id and digest
//! in it. Changing a registered problem therefore fails a test rather than quietly redefining what
//! an earlier measurement meant; adding one does not. The reduced-round ladder in particular is
//! frozen *before* it is run, so its rows cannot be chosen to flatter the result.

use std::fmt::{Display, Formatter};

use crate::{
    grobner::research::{
        poseidon::{CicoInstance, Poseidon, PoseidonError, PoseidonParameters, KOALABEAR_PRIME},
        Json,
    },
    util::sha256_hex,
    KnownOrder, MultivariatePolynomial,
};

/// What a result on this problem may be compared with, and what it may be quoted as.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BenchmarkClass {
    /// The externally specified problem, unmodified: its field, its width, its objective, its
    /// constants. A witness here is a witness for the public challenge.
    Official,

    /// Fewer rounds, everything else retained — field, state width, `k`, constants, objective.
    ///
    /// `of` names the official problem it was reduced from, so a row cannot be quoted without it.
    /// A witness here is a real witness for a genuinely easier problem and says **nothing** about
    /// `of`.
    FaithfulReduction {
        /// The official challenge's id.
        of: &'static str,
    },

    /// A surrogate: a different state width, a planted target, a relaxed objective.
    ///
    /// Useful for engineering — correctness, regression, profiling — and not evidence about any
    /// public challenge. `why` says which fidelity was given up.
    Engineering {
        /// What makes it a surrogate.
        why: &'static str,
    },
}

impl BenchmarkClass {
    /// The stable name a record keys on.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Official => "official",
            Self::FaithfulReduction { .. } => "faithful-reduction",
            Self::Engineering { .. } => "engineering",
        }
    }
}

impl Display for BenchmarkClass {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Official => write!(f, "official"),
            Self::FaithfulReduction { of } => write!(f, "faithful reduction of {}", of),
            Self::Engineering { why } => write!(f, "engineering surrogate ({})", why),
        }
    }
}

/// What the outside world has recorded about this problem, independently of zeebra.
///
/// Dated and sourced, because "unsolved" is a claim with a shelf life. `as_of` is when this
/// registry last checked, not when the problem was posed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExternalStatus {
    /// No public solution recorded here as of this date.
    NoneRecorded {
        /// When this registry last checked.
        as_of: &'static str,
    },

    /// The program verified a solution on this date. Zeebra's own status is a separate question.
    SolvedExternally {
        /// The date the program states.
        verified: &'static str,
    },

    /// Published together with its answer, so that an implementation can check itself.
    PublishedWithAnswer,

    /// Nobody posed this. It is a reduction or a surrogate derived here.
    ///
    /// Distinct from [`Self::NoneRecorded`], which is a dated statement about a *public* problem.
    /// Reporting a derived instance as having no recorded solution would imply someone had looked.
    NotAPublicProblem,
}

impl Display for ExternalStatus {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoneRecorded { as_of } => {
                write!(f, "no public solution recorded as of {}", as_of)
            }
            Self::SolvedExternally { verified } => {
                write!(f, "solved externally, verified {}", verified)
            }
            Self::PublishedWithAnswer => write!(f, "published with its answer"),
            Self::NotAPublicProblem => write!(f, "derived here; not a public problem"),
        }
    }
}

/// What solving means, as a tag rather than as prose.
///
/// A tag because it is part of the identity digest and a reworded sentence must not change an
/// instance's identity — while a changed *objective* must. The prose lives in
/// [`Self::statement`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Objective {
    /// `P⁺(C_1..C_k, X_1..X_{t−k})` agrees with the target in its first `k` words, **exactly**,
    /// over the base field.
    CicoExact,

    /// `F(x) = 0` for the published coefficient vectors, over the published field.
    MqRoot,
}

impl Objective {
    /// The stable tag, which is what the digest covers.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::CicoExact => "cico-exact",
            Self::MqRoot => "mq-root",
        }
    }

    /// The objective in words.
    pub fn statement(&self) -> &'static str {
        match self {
            Self::CicoExact => {
                "find the free input words for which the permutation-with-initial-linear-layer \
                 reproduces the target output words exactly; the remaining output words are \
                 unconstrained"
            }
            Self::MqRoot => "find any x over the published field with F(x) = 0",
        }
    }
}

/// A CICO instance's target, which is part of its identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CicoTarget {
    /// The program's own constants: `[C_1..C_k, C_{k+1}..C_{2k}]`.
    Stated(Vec<u64>),

    /// The target a chosen input actually produces, which is what makes a surrogate solvable.
    ///
    /// Recorded rather than left to a runner, because a planted instance's target **is** a
    /// function of the plant: two runners choosing different plants are measuring two different
    /// problems, and the digest has to say so.
    PlantedFrom {
        /// The `k` constrained input words.
        inputs: Vec<u64>,

        /// The `t − k` free input words the plant assigns.
        free: Vec<u64>,
    },
}

/// The parameters of a registered problem, typed per family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ChallengeParameters {
    /// Poseidon CICO.
    PoseidonCico {
        /// The field modulus.
        prime: u64,
        /// The S-box exponent.
        alpha: u32,
        /// State width.
        t: usize,
        /// Constrained words at each end.
        k: usize,
        /// Full rounds.
        r_f: usize,
        /// Partial rounds.
        r_p: usize,
        /// The target.
        target: CicoTarget,
    },

    /// A published multivariate quadratic system, identified by the bytes of its file.
    MqSystem {
        /// The field, as the source names it.
        field: &'static str,
        /// The challenge type, `"III"` or `"VI"`.
        kind: &'static str,
        /// Variables.
        n: usize,
        /// Polynomials.
        m: usize,
        /// The generator seed the header states.
        seed: u64,
        /// SHA-256 of the instance file, lowercase hex.
        ///
        /// The identity, for a family whose problem *is* a file. Empty for a size this registry
        /// names but does not have the bytes of — the `n = 55` entry exists to show the gap.
        sha256: &'static str,
    },
}

impl ChallengeParameters {
    /// The family's stable name.
    pub fn family(&self) -> &'static str {
        match self {
            Self::PoseidonCico { .. } => "poseidon-cico",
            Self::MqSystem { .. } => "fukuoka-mq",
        }
    }

    /// The parameters as canonical lines, which is what the digest is taken over.
    fn canonical_lines(&self) -> Vec<String> {
        match self {
            Self::PoseidonCico {
                prime,
                alpha,
                t,
                k,
                r_f,
                r_p,
                target,
            } => {
                let mut lines = vec![
                    format!("prime {}", prime),
                    format!("alpha {}", alpha),
                    format!("t {}", t),
                    format!("k {}", k),
                    format!("r_f {}", r_f),
                    format!("r_p {}", r_p),
                ];
                lines.push(match target {
                    CicoTarget::Stated(constants) => format!("target stated {}", join(constants)),
                    CicoTarget::PlantedFrom { inputs, free } => {
                        format!("target planted inputs={} free={}", join(inputs), join(free))
                    }
                });
                lines
            }
            Self::MqSystem {
                field,
                kind,
                n,
                m,
                seed,
                sha256,
            } => vec![
                format!("field {}", field),
                format!("type {}", kind),
                format!("n {}", n),
                format!("m {}", m),
                format!("seed {}", seed),
                format!("file-sha256 {}", sha256),
            ],
        }
    }
}

fn join(values: &[u64]) -> String {
    values
        .iter()
        .map(|v| v.to_string())
        .collect::<Vec<_>>()
        .join(",")
}

/// The program that posed the problem.
///
/// None of this is in the identity digest: a corrected URL or a paid bounty must not change what
/// an instance *is*.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChallengeProgram {
    /// The program's name.
    pub name: &'static str,

    /// Which edition, and when this registry read it.
    pub version: &'static str,

    /// Where to read the statement.
    pub url: &'static str,

    /// The stated reward, if any. Recorded as the program words it.
    pub reward: Option<&'static str>,

    /// Redistribution terms, in the source's own words where possible.
    pub redistribution: &'static str,
}

/// What a verified witness for this problem would mean.
///
/// Computed from the class and the external status rather than asserted by a report, which is the
/// point: the distinction between reproducing a solved challenge and solving an open one is not
/// something a summary should be free to phrase generously.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Significance {
    /// A verified witness for a public problem that already has a public solution.
    Reproduction {
        /// The date the program verified its own solution.
        externally_verified: &'static str,
    },

    /// A verified witness for an official problem with no public solution recorded here.
    ///
    /// **Not a priority claim.** It says this registry knew of no public solution when it last
    /// checked, which is a statement about the registry.
    NoPublicSolutionRecorded {
        /// When this registry last checked.
        as_of: &'static str,
    },

    /// A verified witness for a registered reduction. A real result, about a different problem.
    ReducedInstanceWitness {
        /// The official problem it was reduced from.
        of: &'static str,
    },

    /// A verified witness for a surrogate. Evidence about the implementation, not the challenge.
    SurrogateWitness {
        /// Which fidelity was given up.
        why: &'static str,
    },

    /// No verified witness. Whatever else a run measured, it did not solve this.
    NoWitness,
}

impl Display for Significance {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Reproduction {
                externally_verified,
            } => write!(
                f,
                "reproduction of a challenge solved externally on {}",
                externally_verified
            ),
            Self::NoPublicSolutionRecorded { as_of } => write!(
                f,
                "no public solution was recorded as of {} (not a priority claim)",
                as_of
            ),
            Self::ReducedInstanceWitness { of } => {
                write!(
                    f,
                    "witness for a reduction of {}; says nothing about it",
                    of
                )
            }
            Self::SurrogateWitness { why } => write!(f, "witness for a surrogate ({})", why),
            Self::NoWitness => write!(f, "no verified witness"),
        }
    }
}

/// A public problem, with everything needed to construct it and to check an answer to it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChallengeManifest {
    /// A stable identifier, e.g. `"poseidon31-cico-rf6-rp8"`.
    pub id: &'static str,

    /// Schema version, so a stored manifest can be read by a later reader that changed shape.
    pub schema: u32,

    /// What a result here may be quoted as.
    pub class: BenchmarkClass,

    /// The parameters, typed per family.
    pub parameters: ChallengeParameters,

    /// What solving means.
    pub objective: Objective,

    /// Who posed it.
    pub program: ChallengeProgram,

    /// What the outside world has recorded, independently of zeebra.
    pub external: ExternalStatus,

    /// How a claimed solution is checked **without** trusting the solver or the generator.
    pub verifier: &'static str,

    /// Anything a reader needs that the fields above do not carry.
    pub notes: &'static str,
}

impl ChallengeManifest {
    /// The current schema version.
    pub const SCHEMA: u32 = 1;

    /// The canonical form the identity digest is taken over.
    ///
    /// Line-oriented and ASCII, so a digest can be reproduced by hand or by a different language.
    /// Covers the family, the objective tag and the parameters — and nothing else. See the module
    /// docs for why the program metadata is excluded.
    pub fn canonical(&self) -> String {
        let mut lines = vec![
            format!("zeebra-challenge {}", self.schema),
            format!("family {}", self.parameters.family()),
            format!("objective {}", self.objective.tag()),
        ];
        lines.extend(self.parameters.canonical_lines());
        let mut text = lines.join("\n");
        text.push('\n');
        text
    }

    /// SHA-256 of [`Self::canonical`], lowercase hex: this problem's identity.
    pub fn digest(&self) -> String {
        sha256_hex(self.canonical().as_bytes())
    }

    /// The first twelve hex digits of the digest, for a table.
    pub fn short_digest(&self) -> String {
        self.digest()[..12].to_string()
    }

    /// What a verified witness for this problem would mean; [`Significance::NoWitness`] if there
    /// is none.
    pub fn significance(&self, verified_witness: bool) -> Significance {
        if !verified_witness {
            return Significance::NoWitness;
        }
        match (self.class, self.external) {
            (BenchmarkClass::Engineering { why }, _) => Significance::SurrogateWitness { why },
            (BenchmarkClass::FaithfulReduction { of }, _) => {
                Significance::ReducedInstanceWitness { of }
            }
            (BenchmarkClass::Official, ExternalStatus::SolvedExternally { verified }) => {
                Significance::Reproduction {
                    externally_verified: verified,
                }
            }
            (BenchmarkClass::Official, ExternalStatus::PublishedWithAnswer) => {
                Significance::Reproduction {
                    externally_verified: "publication",
                }
            }
            (BenchmarkClass::Official, ExternalStatus::NoneRecorded { as_of }) => {
                Significance::NoPublicSolutionRecorded { as_of }
            }
            // An official problem cannot be a derived one; the registry has no such row and a
            // hand-built manifest that claimed both gets the weakest reading.
            (BenchmarkClass::Official, ExternalStatus::NotAPublicProblem) => {
                Significance::SurrogateWitness {
                    why: "the manifest calls itself official and not public",
                }
            }
        }
    }

    /// The Poseidon parameters, for a CICO problem.
    pub fn poseidon_parameters(&self) -> Option<PoseidonParameters> {
        match &self.parameters {
            ChallengeParameters::PoseidonCico {
                prime,
                alpha,
                t,
                r_f,
                r_p,
                ..
            } => Some(PoseidonParameters {
                prime: *prime,
                alpha: *alpha,
                t: *t,
                r_f: *r_f,
                r_p: *r_p,
            }),
            _ => None,
        }
    }

    /// Variables the generated system has, for a CICO problem: `(t − k) + t·R_F + R_P`.
    pub fn variables(&self) -> Option<usize> {
        match &self.parameters {
            ChallengeParameters::PoseidonCico { t, k, .. } => {
                Some(t - k + self.poseidon_parameters()?.sboxes())
            }
            ChallengeParameters::MqSystem { n, .. } => Some(*n),
        }
    }

    /// Equations the generated system has, for a CICO problem: `t·R_F + R_P + k`.
    pub fn equations(&self) -> Option<usize> {
        match &self.parameters {
            ChallengeParameters::PoseidonCico { k, .. } => {
                Some(self.poseidon_parameters()?.sboxes() + k)
            }
            ChallengeParameters::MqSystem { m, .. } => Some(*m),
        }
    }

    /// The CICO instance this problem names, built from its own parameters.
    ///
    /// The registry is executable rather than descriptive: a runner takes the instance from here,
    /// so there is no second copy of the constants anywhere to drift from these.
    ///
    /// # Errors
    /// [`PoseidonError::WrongStateWidth`] if the manifest is not a CICO problem — reported as a
    /// width error rather than a panic because a caller iterating the registry will hit it.
    /// Otherwise whatever [`Poseidon::new`] and [`CicoInstance::new`] report, including
    /// [`PoseidonError::FieldMismatch`] when `F` is not the field the parameters name.
    pub fn cico_instance<F: KnownOrder>(&self) -> Result<CicoInstance<F>, PoseidonError> {
        let (k, target) = match &self.parameters {
            ChallengeParameters::PoseidonCico { k, target, .. } => (*k, target),
            ChallengeParameters::MqSystem { n, .. } => {
                return Err(PoseidonError::WrongStateWidth {
                    expected: 0,
                    found: *n,
                })
            }
        };
        let parameters = self
            .poseidon_parameters()
            .expect("the match above established the family");
        let poseidon = Poseidon::<F>::new(parameters)?;

        // `reduced_from` is carried for every row that is not itself official, so a result cannot
        // be quoted without what it reduced from.
        let reduced_from = match self.class {
            BenchmarkClass::Official => None,
            _ => Some(PoseidonParameters::bounty_cico()),
        };

        match target {
            CicoTarget::Stated(constants) => CicoInstance::new(
                poseidon,
                k,
                constants.iter().map(|c| F::new(*c)).collect(),
                reduced_from,
            ),
            CicoTarget::PlantedFrom { inputs, free } => {
                let inputs: Vec<F> = inputs.iter().map(|c| F::new(*c)).collect();
                let free: Vec<F> = free.iter().map(|c| F::new(*c)).collect();
                CicoInstance::planted(poseidon, k, &inputs, &free, reduced_from)
            }
        }
    }

    /// A digest of the derived round constants and MDS matrix.
    ///
    /// Not part of the identity — the parameters already determine these — but a **regression pin**
    /// on the generator: the constants come out of a Grain LFSR seeded with `(prime bits, alpha, t,
    /// R_F, R_P)`, so a change to the LFSR, to the rejection sampling or to the Cauchy
    /// construction would silently redefine every registered instance while leaving its digest
    /// alone. This is what notices.
    ///
    /// # Errors
    /// As [`Self::cico_instance`].
    pub fn derived_digest<F: KnownOrder>(&self) -> Result<String, PoseidonError> {
        let parameters = self
            .poseidon_parameters()
            .ok_or(PoseidonError::WrongStateWidth {
                expected: 0,
                found: 0,
            })?;
        let poseidon = Poseidon::<F>::new(parameters)?;
        let mut text = String::new();
        for row in &poseidon.round_constants {
            for constant in row {
                text.push_str(&format!("{} ", constant));
            }
            text.push('\n');
        }
        for row in &poseidon.mds {
            for entry in row {
                text.push_str(&format!("{} ", entry));
            }
            text.push('\n');
        }
        Ok(sha256_hex(text.as_bytes())[..16].to_string())
    }

    /// The manifest as JSON.
    pub fn to_json(&self) -> Json {
        let mut fields = vec![
            ("schema", Json::int(self.schema)),
            ("id", Json::string(self.id)),
            ("digest", Json::string(self.digest())),
            ("class", Json::string(self.class.name())),
        ];
        if let BenchmarkClass::FaithfulReduction { of } = self.class {
            fields.push(("reduced_from", Json::string(of)));
        }
        if let BenchmarkClass::Engineering { why } = self.class {
            fields.push(("surrogate_because", Json::string(why)));
        }
        fields.push(("family", Json::string(self.parameters.family())));
        fields.push(("objective", Json::string(self.objective.tag())));
        fields.push((
            "objective_statement",
            Json::string(self.objective.statement()),
        ));
        fields.push((
            "parameters",
            Json::Array(
                self.parameters
                    .canonical_lines()
                    .into_iter()
                    .map(Json::string)
                    .collect(),
            ),
        ));
        if let Some(variables) = self.variables() {
            fields.push(("variables", Json::size(variables)));
        }
        if let Some(equations) = self.equations() {
            fields.push(("equations", Json::size(equations)));
        }
        fields.push((
            "program",
            Json::object([
                ("name", Json::string(self.program.name)),
                ("version", Json::string(self.program.version)),
                ("url", Json::string(self.program.url)),
                (
                    "reward",
                    match self.program.reward {
                        Some(reward) => Json::string(reward),
                        None => Json::Null,
                    },
                ),
                ("redistribution", Json::string(self.program.redistribution)),
            ]),
        ));
        fields.push((
            "external_status",
            Json::object(match self.external {
                ExternalStatus::NoneRecorded { as_of } => vec![
                    ("state", Json::string("none_recorded")),
                    ("as_of", Json::string(as_of)),
                ],
                ExternalStatus::SolvedExternally { verified } => vec![
                    ("state", Json::string("solved_externally")),
                    ("verified", Json::string(verified)),
                ],
                ExternalStatus::PublishedWithAnswer => {
                    vec![("state", Json::string("published_with_answer"))]
                }
                ExternalStatus::NotAPublicProblem => {
                    vec![("state", Json::string("not_a_public_problem"))]
                }
            }),
        ));
        fields.push(("verifier", Json::string(self.verifier)));
        fields.push(("notes", Json::string(self.notes)));
        Json::object(fields)
    }
}

impl Display for ChallengeManifest {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "challenge       {}", self.id)?;
        writeln!(f, "digest          {}", self.digest())?;
        writeln!(f, "class           {}", self.class)?;
        writeln!(
            f,
            "program         {} ({})",
            self.program.name, self.program.version
        )?;
        writeln!(f, "url             {}", self.program.url)?;
        if let Some(reward) = self.program.reward {
            writeln!(f, "reward          {}", reward)?;
        }
        writeln!(f, "external        {}", self.external)?;
        writeln!(f, "objective       {}", self.objective.tag())?;
        for line in self.parameters.canonical_lines() {
            writeln!(f, "  {}", line)?;
        }
        if let (Some(variables), Some(equations)) = (self.variables(), self.equations()) {
            writeln!(
                f,
                "size            {} variables, {} equations",
                variables, equations
            )?;
        }
        writeln!(f, "verifier        {}", self.verifier)?;
        write!(f, "notes           {}", self.notes)
    }
}

/// Something to do with a CICO system once its dimension is known.
///
/// The `const N` bridge, as [`MqVisitor`](super::MqVisitor) is for the MQ family: a function
/// cannot return `Vec<MultivariatePolynomial<N, F>>` for an `N` chosen at runtime, and the
/// registry's twelve Poseidon rows have twelve different `N`.
pub trait CicoVisitor<F: KnownOrder> {
    /// What the visit produces. Must not mention the dimension.
    type Output;

    /// Called once, with the system at its own dimension.
    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> Self::Output;
}

/// Why a registered problem could not be handed to a visitor.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ChallengeError {
    /// The problem is not a Poseidon CICO problem.
    NotCico {
        /// The family it is.
        family: &'static str,
    },

    /// No dimension is compiled for this variable count.
    ///
    /// Every id [`registry`] holds is compiled, which a test asserts; this is for a manifest built
    /// by hand.
    UnsupportedDimension {
        /// Variables the system needs.
        variables: usize,
    },

    /// The instance could not be built.
    Poseidon(PoseidonError),
}

impl Display for ChallengeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotCico { family } => write!(f, "not a CICO problem: family {}", family),
            Self::UnsupportedDimension { variables } => write!(
                f,
                "no dimension compiled for {} variables; see dispatch_cico",
                variables
            ),
            Self::Poseidon(e) => write!(f, "{}", e),
        }
    }
}

impl std::error::Error for ChallengeError {}

impl From<PoseidonError> for ChallengeError {
    fn from(e: PoseidonError) -> Self {
        Self::Poseidon(e)
    }
}

/// Build a registered CICO problem's system and hand it to `visitor` at its own dimension.
///
/// # Errors
/// [`ChallengeError`].
pub fn dispatch_cico<F: KnownOrder, V: CicoVisitor<F>>(
    manifest: &ChallengeManifest,
    visitor: V,
) -> Result<V::Output, ChallengeError> {
    if !matches!(
        manifest.parameters,
        ChallengeParameters::PoseidonCico { .. }
    ) {
        return Err(ChallengeError::NotCico {
            family: manifest.parameters.family(),
        });
    }
    let instance = manifest.cico_instance::<F>()?;
    let variables = instance.variables();

    // Every dimension the registry needs, and no others: a spare `N` is a monomorphization of the
    // whole pipeline, and the solvers are generic over it.
    macro_rules! dispatch {
        ($($n:literal),+ $(,)?) => {
            match variables {
                $($n => Ok(visitor.visit(&instance.system::<$n>()?)),)+
                variables => Err(ChallengeError::UnsupportedDimension { variables }),
            }
        };
    }
    dispatch!(
        5, 7, 9, // the t = 2 and t = 3 surrogates
        46, 48, 50, // t = 16, R_F = 2
        78, 80, 82, // t = 16, R_F = 4
        110, 112, 114, // t = 16, R_F = 6, below the official round counts
        116, 118, 120, // t = 16, R_F = 6, the three official targets
    )
}

/// The Poseidon Cryptanalysis Initiative's 2026 program, as this registry read it.
const INITIATIVE: ChallengeProgram = ChallengeProgram {
    name: "Poseidon Cryptanalysis Initiative",
    version: "2026 CICO program, read 2026-11-05; the site states \"THE PROGRAM IS FINISHED\"",
    url: "https://www.poseidon-initiative.info/",
    reward: None,
    redistribution: "parameters and objective are published on the program's page; the round \
                     constants are derived, not redistributed",
};

/// The Fukuoka MQ Challenge.
const FUKUOKA: ChallengeProgram = ChallengeProgram {
    name: "Fukuoka MQ Challenge",
    version: "toy examples, retrieved 2026-11-05",
    url: "https://www.mqchallenge.org/",
    reward: None,
    redistribution: "COPYRIGHT © 2015 FUKUOKA MQ CHALLENGE All Right Reserved; instance files are \
                     not redistributed here and are fetched by tools/fetch-mq-challenge.sh",
};

/// How a CICO answer is checked without trusting anything that produced it.
const CICO_VERIFIER: &str = "CicoInstance::is_solution rebuilds the input state and runs \
                             permutation_plus_linear, so the check goes through the permutation \
                             rather than through the polynomial system — independent of the \
                             generator and of every transformation applied to it. The program's \
                             own verifier is verify_cico_solution in poseidon-tools.";

/// How an MQ answer is checked.
const MQ_VERIFIER: &str = "evaluate the imported coefficient vectors of the original published \
                           file at the candidate, inverting any specialization first";

/// The input constants every KoalaBear CICO row shares: `C_1 = 0xc09de4`, `C_2 = 0xee6282`.
const C1: u64 = 0xC0_9DE4;
const C2: u64 = 0xEE_6282;

/// The official 2026 CICO targets: `(R_P, reward, the date the program verified a solution)`.
const OFFICIAL_ROUNDS: [(usize, &str, &str); 3] = [
    (6, "$6,000", "2026-04-10"),
    (8, "$10,000", "2026-05-06"),
    (10, "$15,000", "2026-07-06"),
];

/// The frozen reduced-round ladder: `t = 16`, `k = 2`, the official constants, fewer rounds.
///
/// Chosen **before** any of it was run, which is the only way a ladder measures a frontier rather
/// than describing one. Nine rows: `R_F ∈ {2, 4, 6}` against `R_P ∈ {0, 2, 4}`, which brackets the
/// official `R_F = 6` from below in both parameters. `(6, 6)` is not here because it *is* an
/// official target.
const LADDER: [(usize, usize); 9] = [
    (2, 0),
    (2, 2),
    (2, 4),
    (4, 0),
    (4, 2),
    (4, 4),
    (6, 0),
    (6, 2),
    (6, 4),
];

/// Every problem M23 is measured against.
///
/// Frozen: `test_the_registry_is_frozen` pins each id and digest. The order is official targets,
/// then the reduced-round ladder, then the surrogates, then the MQ family — which is also the
/// order a scoreboard prints, hardest and most faithful first.
pub fn registry() -> Vec<ChallengeManifest> {
    let mut challenges = Vec::new();

    for (r_p, reward, verified) in OFFICIAL_ROUNDS {
        challenges.push(ChallengeManifest {
            id: match r_p {
                6 => "poseidon31-cico-rf6-rp6",
                8 => "poseidon31-cico-rf6-rp8",
                _ => "poseidon31-cico-rf6-rp10",
            },
            schema: ChallengeManifest::SCHEMA,
            class: BenchmarkClass::Official,
            parameters: ChallengeParameters::PoseidonCico {
                prime: KOALABEAR_PRIME,
                alpha: 3,
                t: 16,
                k: 2,
                r_f: 6,
                r_p,
                target: CicoTarget::Stated(vec![C1, C2, 0, 0]),
            },
            objective: Objective::CicoExact,
            program: ChallengeProgram {
                reward: Some(reward),
                ..INITIATIVE
            },
            external: ExternalStatus::SolvedExternally { verified },
            verifier: CICO_VERIFIER,
            notes: "Perm+(0xc09de4, 0xee6282, X_1..X_14) = (0, 0, Y_1..Y_14) over KoalaBear. The \
                    program also ships a relaxed verifier accepting a low-bit match; that is a \
                    condition on the integer representative, is not a polynomial identity, and is \
                    not this objective.",
        });
    }

    for (r_f, r_p) in LADDER {
        challenges.push(ChallengeManifest {
            id: ladder_id(r_f, r_p),
            schema: ChallengeManifest::SCHEMA,
            class: BenchmarkClass::FaithfulReduction {
                of: "poseidon31-cico-rf6-rp8",
            },
            parameters: ChallengeParameters::PoseidonCico {
                prime: KOALABEAR_PRIME,
                alpha: 3,
                t: 16,
                k: 2,
                r_f,
                r_p,
                target: CicoTarget::Stated(vec![C1, C2, 0, 0]),
            },
            objective: Objective::CicoExact,
            program: INITIATIVE,
            external: ExternalStatus::NotAPublicProblem,
            verifier: CICO_VERIFIER,
            notes:
                "The official field, state width, k, constants and objective; fewer rounds. The \
                    round constants are regenerated from (prime bits, alpha, t, R_F, R_P), so they \
                    differ from the official instance's — which is part of this row's identity, \
                    not a defect. An arbitrary CICO target need not have a base-field solution.",
        });
    }

    // The surrogates M21 and M22 measured, registered so that a regression has an identity and
    // cannot be confused with progress on a challenge.
    for (id, t, r_f, r_p, free) in [
        (
            "poseidon-t2-rf2-rp0-planted",
            2usize,
            2usize,
            0usize,
            1usize,
        ),
        ("poseidon-t2-rf2-rp2-planted", 2, 2, 2, 1),
        ("poseidon-t2-rf4-rp0-planted", 2, 4, 0, 1),
        ("poseidon-t3-rf2-rp1-planted", 3, 2, 1, 2),
    ] {
        challenges.push(ChallengeManifest {
            id,
            schema: ChallengeManifest::SCHEMA,
            class: BenchmarkClass::Engineering {
                why: "state width below 16, k = 1, and a planted target",
            },
            parameters: ChallengeParameters::PoseidonCico {
                prime: KOALABEAR_PRIME,
                alpha: 3,
                t,
                k: 1,
                r_f,
                r_p,
                target: CicoTarget::PlantedFrom {
                    inputs: vec![C1],
                    // The plant M21-B and M22-E used, recorded because it is part of the problem.
                    free: (0..free).map(|i| 1_000 + i as u64).collect(),
                },
            },
            objective: Objective::CicoExact,
            program: INITIATIVE,
            external: ExternalStatus::NotAPublicProblem,
            verifier: CICO_VERIFIER,
            notes: "A planted target, so a solution is known to exist and \"found nothing\" is \
                    distinguishable from \"is broken\". Regression and profiling only.",
        });
    }

    for (id, kind, n, m, sha256, external, notes) in [
        (
            "fukuoka-mq-III-n10-seed0",
            "III",
            10usize,
            20usize,
            "9436e45dbd4247f152681e954f1db19d92e8cf5e76b2bc35530bed74aae522ba",
            ExternalStatus::PublishedWithAnswer,
            "The overdetermined encryption family. Published with its answer so an \
             implementation can check itself; 45 variables short of the smallest real challenge.",
        ),
        (
            "fukuoka-mq-III-n15-seed0",
            "III",
            15,
            30,
            "1dcee7e5e1a5dad4885471fed133158d6bce7a61822ed4aa39a1f91c9264b97b",
            ExternalStatus::PublishedWithAnswer,
            "The next published type III size up from n = 10.",
        ),
        (
            "fukuoka-mq-III-n20-seed0",
            "III",
            20,
            40,
            "ecb087b4128d490dd0931b877f7827786d3f49fa27facabde629d9e1f057e072",
            ExternalStatus::PublishedWithAnswer,
            "The largest published type III toy example.",
        ),
        (
            "fukuoka-mq-VI-n10-seed0",
            "VI",
            10,
            7,
            "9512b6032be415ae8391b72ed8ad4f43357bafa4f0058d60b06dba3537a41af3",
            ExternalStatus::PublishedWithAnswer,
            "The signature family: n > m, so positive-dimensional as published. A specialized \
             slice is a different problem and is registered as its own instance when run.",
        ),
        (
            "fukuoka-mq-VI-n15-seed0",
            "VI",
            15,
            10,
            "ad22fe9a065688453b481fe8cb0e2990f3207920dc83e8c64f8dea2651b5e888",
            ExternalStatus::PublishedWithAnswer,
            "Five surplus variables rather than three, so a specialization campaign has a larger \
             slice space.",
        ),
        (
            "fukuoka-mq-III-n55-seed0",
            "III",
            55,
            110,
            "",
            ExternalStatus::NoneRecorded {
                as_of: "2026-11-05",
            },
            "The smallest size in the real challenge rather than the toy examples. Registered to \
             show the gap and deliberately not implemented: SUPPORTED_DIMENSIONS stops at 20, and \
             its file checksum is empty because this registry does not hold those bytes.",
        ),
    ] {
        challenges.push(ChallengeManifest {
            id,
            schema: ChallengeManifest::SCHEMA,
            class: BenchmarkClass::Official,
            parameters: ChallengeParameters::MqSystem {
                field: "GF(31)",
                kind,
                n,
                m,
                seed: 0,
                sha256,
            },
            objective: Objective::MqRoot,
            program: FUKUOKA,
            external,
            verifier: MQ_VERIFIER,
            notes,
        });
    }

    challenges
}

/// A ladder row's id. `&'static str` because an id is part of a frozen registry, not a format.
fn ladder_id(r_f: usize, r_p: usize) -> &'static str {
    match (r_f, r_p) {
        (2, 0) => "poseidon31-cico-t16-rf2-rp0",
        (2, 2) => "poseidon31-cico-t16-rf2-rp2",
        (2, 4) => "poseidon31-cico-t16-rf2-rp4",
        (4, 0) => "poseidon31-cico-t16-rf4-rp0",
        (4, 2) => "poseidon31-cico-t16-rf4-rp2",
        (4, 4) => "poseidon31-cico-t16-rf4-rp4",
        (6, 0) => "poseidon31-cico-t16-rf6-rp0",
        (6, 2) => "poseidon31-cico-t16-rf6-rp2",
        (6, 4) => "poseidon31-cico-t16-rf6-rp4",
        _ => unreachable!("LADDER holds exactly the nine rows above"),
    }
}

/// The registered problem with this id.
pub fn challenge(id: &str) -> Option<ChallengeManifest> {
    registry().into_iter().find(|c| c.id == id)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{
        challenge, dispatch_cico, registry, BenchmarkClass, ChallengeError, ChallengeParameters,
        CicoTarget, CicoVisitor, ExternalStatus, Objective, Significance,
    };
    use crate::{
        fields::PrimeFieldElement64,
        grobner::research::{verify_against_trace, KOALABEAR_PRIME},
        FiniteField, MultivariatePolynomial,
    };

    type K = PrimeFieldElement64<KOALABEAR_PRIME>;

    /// Every registered id and identity digest, pinned.
    ///
    /// This is what "frozen" means operationally: redefining a registered problem — different
    /// rounds, different constants, a different objective, a different published file — fails
    /// here, so it cannot happen as a side effect of tuning something. Adding a row fails here
    /// too, which is a one-line edit and a deliberate act.
    #[test]
    fn test_the_registry_is_frozen() {
        let expected = [
            ("poseidon31-cico-rf6-rp6", "f36d914ee7d2"),
            ("poseidon31-cico-rf6-rp8", "dfc1041fc131"),
            ("poseidon31-cico-rf6-rp10", "cf06393b5cd6"),
            ("poseidon31-cico-t16-rf2-rp0", "56ccc99d85e0"),
            ("poseidon31-cico-t16-rf2-rp2", "af93deb46aa5"),
            ("poseidon31-cico-t16-rf2-rp4", "08e66c87a885"),
            ("poseidon31-cico-t16-rf4-rp0", "a9242143a8c6"),
            ("poseidon31-cico-t16-rf4-rp2", "80957f3ccf46"),
            ("poseidon31-cico-t16-rf4-rp4", "2d8f8531107d"),
            ("poseidon31-cico-t16-rf6-rp0", "78215e51ccef"),
            ("poseidon31-cico-t16-rf6-rp2", "4e79a017932d"),
            ("poseidon31-cico-t16-rf6-rp4", "82a1d6d3a18d"),
            ("poseidon-t2-rf2-rp0-planted", "9e98ebc3abec"),
            ("poseidon-t2-rf2-rp2-planted", "84cde35887fd"),
            ("poseidon-t2-rf4-rp0-planted", "ebd238585cc0"),
            ("poseidon-t3-rf2-rp1-planted", "036ea475c0b1"),
            ("fukuoka-mq-III-n10-seed0", "ae24edf8efc8"),
            ("fukuoka-mq-III-n15-seed0", "0552d3b51070"),
            ("fukuoka-mq-III-n20-seed0", "434135c809f6"),
            ("fukuoka-mq-VI-n10-seed0", "2558f4bccd7d"),
            ("fukuoka-mq-VI-n15-seed0", "0345980a26d8"),
            ("fukuoka-mq-III-n55-seed0", "f3ac89821637"),
        ];
        let registry = registry();
        assert_eq!(registry.len(), expected.len(), "a row was added or removed");
        for (manifest, (id, digest)) in registry.iter().zip(expected) {
            assert_eq!(manifest.id, id, "order or id changed");
            assert_eq!(manifest.short_digest(), digest, "{} was redefined", id);
        }
    }

    /// No two registered problems share an identity, and no two share an id.
    #[test]
    fn test_identities_are_distinct() {
        let registry = registry();
        let ids: BTreeSet<&str> = registry.iter().map(|c| c.id).collect();
        assert_eq!(ids.len(), registry.len(), "a duplicate id");
        let digests: BTreeSet<String> = registry.iter().map(|c| c.digest()).collect();
        assert_eq!(digests.len(), registry.len(), "two rows are one problem");
    }

    /// The identity digest covers the mathematics and not the paperwork.
    ///
    /// A bounty being paid, a URL being corrected or a verifier's prose being improved must not
    /// change what an instance *is* — otherwise every historical comparison keyed on the digest
    /// breaks the day a program updates its page.
    #[test]
    fn test_the_digest_covers_the_problem_only() {
        let official = challenge("poseidon31-cico-rf6-rp8").expect("registered");

        let mut repapered = official.clone();
        repapered.external = ExternalStatus::NoneRecorded {
            as_of: "1999-01-01",
        };
        repapered.program.url = "https://example.invalid/";
        repapered.program.reward = None;
        repapered.verifier = "by hand";
        repapered.notes = "";
        assert_eq!(
            repapered.digest(),
            official.digest(),
            "paperwork must not change identity"
        );

        // But every parameter does.
        let mut fewer_rounds = official.clone();
        if let ChallengeParameters::PoseidonCico { r_p, .. } = &mut fewer_rounds.parameters {
            *r_p = 6;
        }
        assert_ne!(fewer_rounds.digest(), official.digest(), "R_P");
        assert_eq!(
            fewer_rounds.digest(),
            challenge("poseidon31-cico-rf6-rp6")
                .expect("registered")
                .digest(),
            "and it lands on the other registered problem, which is the same mathematics"
        );

        let mut other_target = official.clone();
        if let ChallengeParameters::PoseidonCico { target, .. } = &mut other_target.parameters {
            *target = CicoTarget::Stated(vec![super::C1, super::C2, 0, 1]);
        }
        assert_ne!(other_target.digest(), official.digest(), "target");

        let mut relabelled = official.clone();
        relabelled.id = "something-else";
        assert_eq!(
            relabelled.digest(),
            official.digest(),
            "an id is a name, and a name is not an identity"
        );
    }

    /// A witness means different things on an official target, a reduction and a surrogate.
    #[test]
    fn test_significance_distinguishes_reproduction_from_a_first_solution() {
        let official = challenge("poseidon31-cico-rf6-rp8").expect("registered");
        assert_eq!(
            official.significance(true),
            Significance::Reproduction {
                externally_verified: "2026-05-06"
            }
        );
        assert_eq!(official.significance(false), Significance::NoWitness);

        let ladder = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
        assert_eq!(
            ladder.significance(true),
            Significance::ReducedInstanceWitness {
                of: "poseidon31-cico-rf6-rp8"
            }
        );

        let surrogate = challenge("poseidon-t2-rf4-rp0-planted").expect("registered");
        assert!(matches!(
            surrogate.significance(true),
            Significance::SurrogateWitness { .. }
        ));

        // An official problem with nothing recorded against it is the only case that can say "no
        // public solution was recorded", and it still says it is not a priority claim.
        let open = challenge("fukuoka-mq-III-n55-seed0").expect("registered");
        assert_eq!(
            open.significance(true),
            Significance::NoPublicSolutionRecorded {
                as_of: "2026-11-05"
            }
        );
        assert!(open
            .significance(true)
            .to_string()
            .contains("not a priority claim"));
    }

    /// Every official CICO row is the published one: KoalaBear, alpha 3, t = 16, k = 2, R_F = 6,
    /// the published constants, and the exact objective.
    #[test]
    fn test_the_official_rows_are_the_published_problem() {
        let rows: Vec<_> = registry()
            .into_iter()
            .filter(|c| c.id.starts_with("poseidon31-cico-rf6"))
            .collect();
        assert_eq!(rows.len(), 3, "R_P = 6, 8, 10");
        for row in rows {
            assert_eq!(row.class, BenchmarkClass::Official);
            assert_eq!(row.objective, Objective::CicoExact);
            assert!(matches!(
                row.external,
                ExternalStatus::SolvedExternally { .. }
            ));
            let ChallengeParameters::PoseidonCico {
                prime,
                alpha,
                t,
                k,
                r_f,
                ref target,
                ..
            } = row.parameters
            else {
                panic!("a CICO row");
            };
            assert_eq!(prime, KOALABEAR_PRIME);
            assert_eq!((alpha, t, k, r_f), (3, 16, 2, 6));
            assert_eq!(
                *target,
                CicoTarget::Stated(vec![0xC0_9DE4, 0xEE_6282, 0, 0])
            );
            // 14 free inputs plus 16·6 + R_P S-box variables, against those plus two constraints.
            assert_eq!(
                row.variables().expect("a size"),
                row.equations().expect("a size") + 12
            );
        }
    }

    /// The ladder retains everything but the round count, and was frozen before it was run.
    #[test]
    fn test_the_ladder_is_faithful_in_everything_but_rounds() {
        let official = challenge("poseidon31-cico-rf6-rp8").expect("registered");
        let ChallengeParameters::PoseidonCico {
            prime: op,
            alpha: oa,
            t: ot,
            k: ok,
            target: ref ot_target,
            ..
        } = official.parameters
        else {
            panic!("a CICO row");
        };

        let ladder: Vec<_> = registry()
            .into_iter()
            .filter(|c| c.id.starts_with("poseidon31-cico-t16"))
            .collect();
        assert_eq!(ladder.len(), 9);
        for row in &ladder {
            assert_eq!(
                row.class,
                BenchmarkClass::FaithfulReduction {
                    of: "poseidon31-cico-rf6-rp8"
                },
                "a reduction must name what it reduced from"
            );
            let ChallengeParameters::PoseidonCico {
                prime,
                alpha,
                t,
                k,
                r_f,
                r_p,
                ref target,
            } = row.parameters
            else {
                panic!("a CICO row");
            };
            assert_eq!((prime, alpha, t, k), (op, oa, ot, ok), "{}", row.id);
            assert_eq!(target, ot_target, "the official constants, {}", row.id);
            assert_eq!(row.objective, Objective::CicoExact);
            assert!(r_f <= 6 && r_p <= 4, "strictly below the official rounds");
            // Underdetermined by exactly t - 2k = 12, whatever the rounds.
            assert_eq!(
                row.variables().expect("a size") - row.equations().expect("a size"),
                12
            );
        }
    }

    /// Every registered Poseidon row builds, and its S-box equations vanish at a real trace.
    ///
    /// The registry being *executable* is the point: a runner takes its instance from here, so
    /// there is no second copy of the constants to drift. And faithfulness is checked the way
    /// M21-B established — against a trace of the permutation, not against the generator.
    ///
    /// The `k` output constraints are expected **not** to vanish at an arbitrary trace, and the
    /// test asserts exactly that: they are the only equations that mention the target, so a row
    /// with a stated target that vanished everywhere would be a row whose target does nothing. A
    /// planted row's own plant does satisfy them, which the test beside this one checks.
    #[test]
    fn test_every_poseidon_row_builds_and_is_faithful() {
        /// Checks the system against a trace of the permutation on the instance's own inputs.
        struct Faithful<'a>(&'a crate::grobner::research::CicoInstance<K>);
        impl CicoVisitor<K> for Faithful<'_> {
            type Output = Vec<usize>;
            fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, K>]) -> Vec<usize> {
                let t = self.0.poseidon.parameters.t;
                // Any input state with the instance's constrained prefix: faithfulness is a
                // property of the system, not of this point.
                let mut state: Vec<K> = self.0.constants[..self.0.k].to_vec();
                state.extend((0..t - self.0.k).map(|i| K::new(7 * i as u64 + 11)));
                let trace = self.0.poseidon.run(&state, true).expect("the right width");
                verify_against_trace(self.0, system, &trace)
            }
        }

        for manifest in registry() {
            if !matches!(
                manifest.parameters,
                ChallengeParameters::PoseidonCico { .. }
            ) {
                continue;
            }
            let instance = manifest
                .cico_instance::<K>()
                .unwrap_or_else(|e| panic!("{} should build: {}", manifest.id, e));
            assert_eq!(
                instance.variables(),
                manifest.variables().expect("a size"),
                "{}",
                manifest.id
            );
            assert_eq!(
                instance.equations(),
                manifest.equations().expect("a size"),
                "{}",
                manifest.id
            );

            let failures = dispatch_cico::<K, _>(&manifest, Faithful(&instance))
                .unwrap_or_else(|e| panic!("{} should dispatch: {}", manifest.id, e));

            // The S-box equations are the first `sboxes` of them and must all vanish; the `k`
            // output constraints are the rest, and at an arbitrary input they must not.
            let sboxes = manifest.poseidon_parameters().expect("a CICO row").sboxes();
            let expected: Vec<usize> = (sboxes..instance.equations()).collect();
            assert_eq!(
                failures, expected,
                "{}: the vanishing equations are not the S-box ones",
                manifest.id
            );
        }
    }

    /// Every planted surrogate's recorded plant really is a solution of the problem it defines.
    #[test]
    fn test_a_planted_surrogates_plant_solves_it() {
        for manifest in registry() {
            let ChallengeParameters::PoseidonCico {
                target: CicoTarget::PlantedFrom { ref free, .. },
                ..
            } = manifest.parameters
            else {
                continue;
            };
            let instance = manifest.cico_instance::<K>().expect("builds");
            let plant: Vec<K> = free.iter().map(|v| K::new(*v)).collect();
            assert!(
                instance.is_solution(&plant).expect("the right width"),
                "{}: the recorded plant does not solve its own instance",
                manifest.id
            );
        }
    }

    /// The derived constants are pinned, so a change to the LFSR cannot silently redefine a row.
    ///
    /// Separate from the identity digest, which covers the parameters that *determine* these. If
    /// the Grain LFSR, its rejection sampling or the Cauchy construction changed, every registered
    /// instance would become a different permutation with an unchanged identity — which is exactly
    /// the failure a parameter checksum cannot catch.
    #[test]
    fn test_the_derived_constants_are_pinned() {
        for (id, digest) in [
            ("poseidon31-cico-rf6-rp8", "ef542c6c75e61875"),
            ("poseidon31-cico-t16-rf2-rp0", "f299dc94d29d7c8e"),
            ("poseidon-t2-rf4-rp0-planted", "6a75a45c315132c9"),
        ] {
            let manifest = challenge(id).expect("registered");
            assert_eq!(
                manifest.derived_digest::<K>().expect("builds"),
                digest,
                "{}'s derived constants changed",
                id
            );
        }
    }

    /// An MQ row cannot be dispatched as a CICO problem, and says which family it is.
    #[test]
    fn test_a_non_cico_row_is_refused_by_name() {
        struct Nothing;
        impl CicoVisitor<K> for Nothing {
            type Output = ();
            fn visit<const N: usize>(self, _: &[MultivariatePolynomial<N, K>]) {}
        }
        let mq = challenge("fukuoka-mq-III-n10-seed0").expect("registered");
        assert_eq!(
            dispatch_cico::<K, _>(&mq, Nothing),
            Err(ChallengeError::NotCico {
                family: "fukuoka-mq"
            })
        );
    }

    /// A coefficient type that is not the challenge's field is refused.
    #[test]
    fn test_the_field_is_enforced() {
        let official = challenge("poseidon31-cico-rf6-rp8").expect("registered");
        let wrong = official.cico_instance::<PrimeFieldElement64<31>>();
        assert!(wrong.is_err(), "GF(31) is not KoalaBear");
    }

    /// Every MQ row names bytes, except the one that exists to show the gap.
    #[test]
    fn test_mq_rows_pin_their_bytes() {
        for manifest in registry() {
            let ChallengeParameters::MqSystem { n, m, sha256, .. } = manifest.parameters else {
                continue;
            };
            if manifest.id == "fukuoka-mq-III-n55-seed0" {
                assert!(sha256.is_empty(), "the gap row holds no bytes");
                assert!(manifest.notes.contains("not implemented"));
                continue;
            }
            assert_eq!(sha256.len(), 64, "{} needs a checksum", manifest.id);
            // Type III is m = 2n, type VI is underdetermined.
            let ChallengeParameters::MqSystem { kind, .. } = manifest.parameters else {
                unreachable!()
            };
            if kind == "III" {
                assert_eq!(m, 2 * n, "{}", manifest.id);
            } else {
                assert!(m < n, "{}", manifest.id);
            }
        }
    }

    /// The JSON carries the identity, the class and what it reduced from.
    #[test]
    fn test_json_carries_the_class_and_the_reduction() {
        let ladder = challenge("poseidon31-cico-t16-rf4-rp2").expect("registered");
        let text = ladder.to_json().to_json();
        assert!(
            text.contains("\"class\": \"faithful-reduction\""),
            "{}",
            text
        );
        assert!(
            text.contains("\"reduced_from\": \"poseidon31-cico-rf6-rp8\""),
            "{}",
            text
        );
        assert!(text.contains(&format!("\"digest\": \"{}\"", ladder.digest())));
        assert!(text.contains("\"r_f 4\""), "{}", text);
        // 14 free inputs, 16·4 full-round S-boxes, 2 partial-round S-boxes.
        assert!(text.contains("\"variables\": 80"), "{}", text);

        let surrogate = challenge("poseidon-t2-rf2-rp0-planted").expect("registered");
        let text = surrogate.to_json().to_json();
        assert!(text.contains("\"surrogate_because\""), "{}", text);
        assert!(text.contains("target planted"), "{}", text);
    }
}
