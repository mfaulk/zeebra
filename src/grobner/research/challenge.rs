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
//! # Why the Anemoi ladder is `Official` and not a reduction
//!
//! The ten Anemoi rows are reduced round counts of a real primitive, and they are still
//! [`BenchmarkClass::Official`]. The combination has no precedent here, so the reasoning is
//! written down rather than left to the reader.
//!
//! [`BenchmarkClass::FaithfulReduction`] means *this registry reduced an official problem*, and its
//! `of` field has to name that problem so a row cannot be quoted without it. There is no such
//! problem for Anemoi. Nobody posed full-round Anemoi as a challenge, it is not registered, and an
//! `of` pointing at an unregistered row would be a dangling reference that
//! [`Significance::ReducedInstanceWitness`] would then print.
//!
//! What *is* published is the ladder itself. Six Worlds ran `N = 1 … 8` and reported those rows as
//! its own experiment, at those parameters; the registered object is the published object, not
//! something this registry shrank. So the class is `Official`, the status is
//! [`ExternalStatus::PublishedWithAnswer`], and `significance(true)` is therefore
//! [`Significance::Reproduction`] — which is the strongest honest claim available on a solved
//! reduced instance, and weaker than a first solution.
//!
//! The caveat that `FaithfulReduction` would have carried structurally is carried in each row's
//! `notes` instead: a result at `N = 5` says nothing about full-round Anemoi, which is 21 rounds at
//! 128-bit security.
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
        anemoi::{
            Anemoi, AnemoiError, AnemoiParameters, ANEMOI_17_PRIME, ANEMOI_32_PRIME,
            ANEMOI_64_PRIME,
        },
        anemoi_cico::{AnemoiCico, AnemoiModel},
        manifest::Claim,
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

    /// The same, with the **trailing** words constrained instead of the leading ones:
    /// `Perm(X_1..X_{t−k}, 0^k) = (Y_1..Y_{t−k}, 0^k)`.
    ///
    /// The 2025 bounty program's objective, and a different problem from [`Self::CicoExact`] — the
    /// constrained positions interact with the MDS layer differently, so the two are not each
    /// other with relabelled variables. `CicoInstance` constrains the leading words and this crate
    /// therefore cannot generate this one; the rows that use it are registered and refused by
    /// [`ChallengeManifest::cico_instance`] rather than silently built as the other objective.
    CicoExactTrailing,

    /// `F(x) = 0` for the published coefficient vectors, over the published field.
    MqRoot,
}

impl Objective {
    /// The stable tag, which is what the digest covers.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::CicoExact => "cico-exact",
            Self::CicoExactTrailing => "cico-exact-trailing",
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
            Self::CicoExactTrailing => {
                "find the leading input words for which the permutation reproduces the target in \
                 its trailing words exactly; the leading output words are unconstrained"
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

    /// A Poseidon CICO challenge this crate cannot construct, registered anyway.
    ///
    /// Two reasons occur: a field with no coefficient type here — the 2025 program's Poseidon-256
    /// is over a 255-bit scalar field and its Poseidon-64 over Goldilocks, neither of which this
    /// generator is wired for — and the trailing-constraint objective, which `CicoInstance` does
    /// not express. Registered because a scoreboard that only lists what it can run hides the
    /// targets that are actually open.
    PoseidonCicoUnregisterable {
        /// The field as the program names it.
        field: &'static str,
        /// The modulus in decimal, as text, since it need not fit a `u64`.
        prime: &'static str,
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
    },

    /// Anemoi CICO, with the **algebraic model inside the identity**.
    ///
    /// The model is a field rather than configuration because `FCICO` and `PCICO` are two
    /// different polynomial systems for one primitive — at `N = 5`, ten generators of degree three
    /// against six of degrees up to ten. If the model were outside [`canonical_lines`], two
    /// digests would collide on problems a solver meets completely differently, and a comparison
    /// tool keyed on the digest would compare them.
    ///
    /// [`canonical_lines`]: ChallengeParameters::canonical_lines
    AnemoiCico {
        /// The field modulus.
        prime: u64,
        /// The S-box exponent.
        alpha: u32,
        /// Columns; the state is `2ℓ` words wide.
        l: usize,
        /// Rounds.
        rounds: usize,
        /// Which algebraic model.
        model: AnemoiModel,
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
        /// names but does not have the bytes of — the type III `n = 34` entry exists to show the
        /// gap.
        sha256: &'static str,
    },
}

impl ChallengeParameters {
    /// The family's stable name.
    pub fn family(&self) -> &'static str {
        match self {
            Self::PoseidonCico { .. } | Self::PoseidonCicoUnregisterable { .. } => "poseidon-cico",
            Self::AnemoiCico { .. } => "anemoi-cico",
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
            Self::PoseidonCicoUnregisterable {
                field,
                prime,
                alpha,
                t,
                k,
                r_f,
                r_p,
            } => vec![
                format!("field {}", field),
                format!("prime {}", prime),
                format!("alpha {}", alpha),
                format!("t {}", t),
                format!("k {}", k),
                format!("r_f {}", r_f),
                format!("r_p {}", r_p),
            ],
            Self::AnemoiCico {
                prime,
                alpha,
                l,
                rounds,
                model,
            } => vec![
                format!("prime {}", prime),
                format!("alpha {}", alpha),
                format!("l {}", l),
                format!("rounds {}", rounds),
                // The line that keeps two systems for one primitive apart.
                format!("model {}", model.tag()),
            ],
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

/// A published measurement for this problem, made on somebody else's machine.
///
/// The field [`ExternalStatus`] cannot carry. That type records *whether and when* a problem was
/// solved elsewhere and nothing about what it cost, so
///
/// > "Six Worlds reports 22 057 s of FGLM at `N = 5` on an Intel Xeon E5-2630 v3 @ 2.40 GHz with
/// > 378 GB under Debian 11, Magma V2.26-2"
///
/// had nowhere to live: it is not an instance property, not a zeebra measurement, and not a
/// status. Every accepted candidate in `docs/research/additional-benchmarks.md` §1 is a candidate
/// *because* it has such a figure, and §6.2 records this as the one schema gap that mattered.
///
/// # Outside the identity, deliberately
///
/// [`ChallengeManifest::canonical`] does not cover these, for the same reason it does not cover a
/// bounty or a URL: a corrected extrapolation must not change which mathematical problem a row is.
/// `test_a_reference_point_does_not_change_identity` asserts it.
///
/// # No bare number
///
/// Every field that carries a figure carries its conditions beside it. A time without its hardware
/// and its software is not comparable to anything, and a type that let one be recorded without the
/// other would invite exactly the head-to-head `docs/research/anemoi.md` §8 declines to make.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReferencePoint {
    /// The publication, precisely enough to find the figure in it.
    pub source: &'static str,

    /// The parameters the figure is for, in the source's own terms.
    pub parameters: &'static str,

    /// Which step was measured — a whole solve is not a stage split.
    pub step: &'static str,

    /// The time, as the source reports it, including its units.
    pub reported_time: &'static str,

    /// The peak memory, as the source reports it, or `None` when the source does not report one
    /// *for this row*.
    ///
    /// `None` is a real answer and not a placeholder. The Six Worlds logs report peak resident set
    /// size once per sweep rather than per round count — 227 MB for the whole `FCICO` run over
    /// `N = 1…8`, 225 MB for `PCICO` over `N = 1…7` — so attributing either to a single row would
    /// be inventing a measurement.
    pub reported_memory: Option<&'static str>,

    /// The machine, named, because a 2015-era Xeon and a 2026 workstation are not a head-to-head.
    pub hardware: &'static str,

    /// The software that produced the figure, with its version.
    pub software: &'static str,
}

impl Display for ReferencePoint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} at {} — {}, {}; {}, {} [{}]",
            self.step,
            self.parameters,
            self.reported_time,
            self.reported_memory
                .unwrap_or("memory not reported for this row"),
            self.hardware,
            self.software,
            self.source
        )
    }
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

/// What attack method has been publicly disclosed for a problem, if any.
///
/// Deliberately separate from [`ExternalStatus`]. A program can verify a submission without naming
/// the submitter, and a paper can describe an attack at the same parameters without being that
/// submission — so "verified on this date" and "this is how it was done" are two different claims.
/// Folding them into one field would attribute a method to a submission on no evidence, which is
/// exactly the mistake [`Self::Published::attributed_to_submission`] exists to prevent.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DisclosedMethod {
    /// Solved externally, and nobody has published how.
    ///
    /// The honest state for a solved problem with no technical report, and not a synonym for
    /// "brute force" or for any other guess.
    Unknown,

    /// There is no external solution whose method could be disclosed.
    ///
    /// For a problem derived here, or one published with its answer.
    NotApplicable,

    /// A method published at these parameters.
    Published {
        /// What the method is, in a few words.
        method: &'static str,

        /// Where it is written down.
        source: &'static str,

        /// The cost the source reports, including the hardware it reports it on.
        ///
        /// Carried as prose because a figure without its hardware is not comparable to anything.
        reported_cost: &'static str,

        /// Whether this publication is *known* to be the submission the program verified.
        ///
        /// False wherever the program does not name first submitters, which is the usual case.
        /// A reader must not infer attribution from the mere coincidence of parameters.
        attributed_to_submission: bool,
    },
}

impl Display for DisclosedMethod {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unknown => write!(f, "no public method"),
            Self::NotApplicable => write!(f, "no external solution"),
            // The source is part of the line, not only of the JSON record: a cost figure a
            // reader cannot trace is not checkable, and this string is what the scoreboard's
            // markdown prints.
            Self::Published {
                method,
                source,
                reported_cost,
                attributed_to_submission,
            } => write!(
                f,
                "{} — {} [{}]{}",
                method,
                reported_cost,
                source,
                if *attributed_to_submission {
                    ""
                } else {
                    ", not attributed to the verified submission"
                }
            ),
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

    /// What attack method has been publicly disclosed, if any.
    ///
    /// Outside [`Self::canonical`], so disclosing a method never changes a problem's identity.
    pub method: DisclosedMethod,

    /// Published measurements for this problem, from elsewhere.
    ///
    /// Empty for a row nobody has published a cost for, which is most of them. Outside
    /// [`Self::canonical`]: see [`ReferencePoint`].
    pub reference_points: &'static [ReferencePoint],

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

    /// The state width, for either Poseidon variant.
    pub fn parameters_t(&self) -> usize {
        match &self.parameters {
            ChallengeParameters::PoseidonCico { t, .. }
            | ChallengeParameters::PoseidonCicoUnregisterable { t, .. } => *t,
            // Anemoi's state is 2l words, l of them constrained at each end.
            ChallengeParameters::AnemoiCico { l, .. } => 2 * l,
            ChallengeParameters::MqSystem { .. } => 0,
        }
    }

    /// The Anemoi parameters, for an Anemoi CICO problem.
    pub fn anemoi_parameters(&self) -> Option<AnemoiParameters> {
        match &self.parameters {
            ChallengeParameters::AnemoiCico {
                prime,
                alpha,
                l,
                rounds,
                ..
            } => Some(AnemoiParameters {
                prime: *prime,
                alpha: *alpha,
                l: *l,
                rounds: *rounds,
            }),
            _ => None,
        }
    }

    /// Which algebraic model this problem names, for an Anemoi CICO problem.
    pub fn anemoi_model(&self) -> Option<AnemoiModel> {
        match &self.parameters {
            ChallengeParameters::AnemoiCico { model, .. } => Some(*model),
            _ => None,
        }
    }

    /// The Anemoi CICO instance this problem names, built from its own parameters.
    ///
    /// The registry is executable rather than descriptive, for the reason
    /// [`Self::cico_instance`] is: a runner takes the instance from here, so there is no second
    /// copy of the constants to drift from these.
    ///
    /// # Errors
    /// [`AnemoiError::UnsupportedColumns`] with `l = 0` if the manifest is not an Anemoi CICO
    /// problem — reported rather than panicked because a caller iterating the registry will hit
    /// it. Otherwise whatever [`Anemoi::new`] reports, including
    /// [`AnemoiError::FieldMismatch`] when `F` is not the field the parameters name.
    pub fn anemoi_cico_instance<F: KnownOrder>(&self) -> Result<AnemoiCico<F>, AnemoiError> {
        let (Some(parameters), Some(model)) = (self.anemoi_parameters(), self.anemoi_model())
        else {
            return Err(AnemoiError::UnsupportedColumns { l: 0 });
        };
        Ok(AnemoiCico::new(Anemoi::<F>::new(parameters)?, model))
    }

    /// A digest of the Anemoi generator and derived round constants.
    ///
    /// The Anemoi counterpart of [`Self::derived_digest`], and it carries more weight: Poseidon's
    /// constants come out of a seeded LFSR, while Anemoi's depend on `g`, which the specification
    /// does not fix. See [`anemoi`](super::anemoi)'s module docs.
    ///
    /// # Errors
    /// As [`Self::anemoi_cico_instance`].
    pub fn anemoi_derived_digest<F: KnownOrder>(&self) -> Result<String, AnemoiError> {
        Ok(self.anemoi_cico_instance::<F>()?.anemoi.derived_digest())
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
            // The same count, computed from the program's parameters rather than from a system
            // this crate can build. A size is a fact about the problem either way.
            ChallengeParameters::PoseidonCicoUnregisterable { t, k, r_f, r_p, .. } => {
                Some(t - k + t * r_f + r_p)
            }
            ChallengeParameters::AnemoiCico {
                l, rounds, model, ..
            } => Some(model.variables(*rounds, *l)),
            ChallengeParameters::MqSystem { n, .. } => Some(*n),
        }
    }

    /// Equations the generated system has, for a CICO problem: `t·R_F + R_P + k`.
    pub fn equations(&self) -> Option<usize> {
        match &self.parameters {
            ChallengeParameters::PoseidonCico { k, .. } => {
                Some(self.poseidon_parameters()?.sboxes() + k)
            }
            ChallengeParameters::PoseidonCicoUnregisterable { t, k, r_f, r_p, .. } => {
                Some(t * r_f + r_p + k)
            }
            ChallengeParameters::AnemoiCico {
                l, rounds, model, ..
            } => Some(model.equations(*rounds, *l)),
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
        // A row whose objective this crate does not generate must not be built as the objective it
        // does generate: the constrained positions interact with the MDS layer differently, and
        // the result would be a different problem wearing this row's identity.
        if self.objective != Objective::CicoExact {
            return Err(PoseidonError::WrongStateWidth {
                expected: 0,
                found: 0,
            });
        }
        let (k, target) = match &self.parameters {
            ChallengeParameters::PoseidonCico { k, target, .. } => (*k, target),
            ChallengeParameters::MqSystem { n, .. } => {
                return Err(PoseidonError::WrongStateWidth {
                    expected: 0,
                    found: *n,
                })
            }
            ChallengeParameters::PoseidonCicoUnregisterable { t, .. } => {
                return Err(PoseidonError::WrongStateWidth {
                    expected: 0,
                    found: *t,
                })
            }
            // A CICO problem of another family. `anemoi_cico_instance` is its constructor.
            ChallengeParameters::AnemoiCico { l, .. } => {
                return Err(PoseidonError::WrongStateWidth {
                    expected: 0,
                    found: 2 * l,
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
            "disclosed_method",
            Json::object(match self.method {
                DisclosedMethod::Unknown => vec![("state", Json::string("unknown"))],
                DisclosedMethod::NotApplicable => {
                    vec![("state", Json::string("not_applicable"))]
                }
                DisclosedMethod::Published {
                    method,
                    source,
                    reported_cost,
                    attributed_to_submission,
                } => vec![
                    ("state", Json::string("published")),
                    ("method", Json::string(method)),
                    ("source", Json::string(source)),
                    ("reported_cost", Json::string(reported_cost)),
                    // A boolean, not the string "true"/"false": a nonempty string is truthy in
                    // several languages a consumer might be written in, so a string here would
                    // make every row read as attributed.
                    (
                        "attributed_to_submission",
                        Json::Bool(attributed_to_submission),
                    ),
                ],
            }),
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
        fields.push((
            "reference_points",
            Json::Array(
                self.reference_points
                    .iter()
                    .map(|point| {
                        Json::object([
                            ("source", Json::string(point.source)),
                            ("parameters", Json::string(point.parameters)),
                            ("step", Json::string(point.step)),
                            ("reported_time", Json::string(point.reported_time)),
                            (
                                "reported_memory",
                                match point.reported_memory {
                                    Some(memory) => Json::string(memory),
                                    None => Json::Null,
                                },
                            ),
                            ("hardware", Json::string(point.hardware)),
                            ("software", Json::string(point.software)),
                        ])
                    })
                    .collect(),
            ),
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
        writeln!(f, "method          {}", self.method)?;
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
        for point in self.reference_points {
            writeln!(f, "published       {}", point)?;
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

    /// A CICO problem of a family this dispatcher does not build.
    ///
    /// Distinct from [`Self::NotCico`], which is a statement about the objective. An Anemoi row
    /// *is* a CICO problem, and saying otherwise would be false; it is simply not a Poseidon one.
    OtherCicoFamily {
        /// The family it is.
        family: &'static str,
    },

    /// A registered CICO problem over a field this crate has no coefficient type for.
    NotGeneratable {
        /// The field, as the program names it.
        field: &'static str,
    },

    /// The objective is one this crate does not generate.
    ///
    /// Registered problems may name an objective the generator cannot express — the 2025 bounty
    /// program constrains the *trailing* words — and a runner iterating the registry will reach
    /// one. Refused by name rather than approximated.
    UnsupportedObjective {
        /// The objective's tag.
        objective: &'static str,
    },

    /// The instance could not be built.
    Poseidon(PoseidonError),
}

impl Display for ChallengeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotCico { family } => write!(f, "not a CICO problem: family {}", family),
            Self::OtherCicoFamily { family } => write!(
                f,
                "a CICO problem of family {}, which this dispatcher does not build",
                family
            ),
            Self::NotGeneratable { field } => {
                write!(f, "this crate has no coefficient type for {}", field)
            }
            Self::UnsupportedObjective { objective } => {
                write!(
                    f,
                    "this crate does not generate the {} objective",
                    objective
                )
            }
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
    // Family, then objective, then field: each refusal names the first reason that applies, and
    // "not a CICO problem: family poseidon-cico" would be a self-contradictory thing to say about
    // a 2025-program row, which is why the family check is about the family alone.
    if let ChallengeParameters::MqSystem { .. } = manifest.parameters {
        return Err(ChallengeError::NotCico {
            family: manifest.parameters.family(),
        });
    }
    // A CICO problem of a family this dispatcher does not generate. Refused by family rather than
    // reported as "not a CICO problem", which would be a false statement about an Anemoi row:
    // `dispatch_anemoi_cico` is its dispatcher.
    if let ChallengeParameters::AnemoiCico { .. } = manifest.parameters {
        return Err(ChallengeError::OtherCicoFamily {
            family: manifest.parameters.family(),
        });
    }
    if manifest.objective != Objective::CicoExact {
        return Err(ChallengeError::UnsupportedObjective {
            objective: manifest.objective.tag(),
        });
    }
    if let ChallengeParameters::PoseidonCicoUnregisterable { field, .. } = manifest.parameters {
        return Err(ChallengeError::NotGeneratable { field });
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
    version:
        "toy examples retrieved 2026-11-05; type VI m = 16 challenge file retrieved 2026-11-07",
    url: "https://www.mqchallenge.org/",
    reward: None,
    redistribution: "COPYRIGHT © 2015 FUKUOKA MQ CHALLENGE All Right Reserved; instance files are \
                     not redistributed here and are fetched by tools/fetch-mq-challenge.sh",
};

/// No published figure for this row, which is not the same as none having been looked for.
const NO_REFERENCE_POINTS: &[ReferencePoint] = &[];

/// The challenge's own recorded solves at the three sizes this crate imports and a solver reached.
///
/// Transcribed from `research/fukuoka-mq/solved-instances.tsv`, which names the detail page each
/// figure came from. Every one of the three is tagged `wall-total` in that fixture; five figures on
/// the site are per-subsystem costs of a hybrid attack rather than campaign totals, and none of
/// these three is one of them. See `docs/research/fukuoka-mq.md` §8.2 and §8.4.
const HUANG_2015_III_N20: &[ReferencePoint] = &[ReferencePoint {
    source: "Fukuoka MQ Challenge submission details, details/details_III_cs.html, accessed \
             2026-11-07",
    parameters: "type III, n = 20, m = 40, seed 0",
    step: "whole solve, wall-clock total",
    reported_time: "259.27 seconds",
    reported_memory: None,
    hardware: "Intel Xeon E5-4617 @ 2.90 GHz, 1 TB RAM",
    software: "Magma V2.19-9, F4",
}];

const HUANG_2015_VI_N15: &[ReferencePoint] = &[ReferencePoint {
    source: "Fukuoka MQ Challenge submission details, details/details_VI_cs.html, accessed \
             2026-11-07",
    parameters: "type VI, m = 10, n = 15, seed 0",
    step: "whole solve, wall-clock total",
    reported_time: "2764.41 seconds",
    reported_memory: None,
    hardware: "Intel Xeon E5-4617 @ 2.90 GHz, 1 TB RAM",
    software: "Magma V2.19-9, F4",
}];

/// The recorded solve of the smallest *type III* challenge, which is not a size this crate reaches.
///
/// `wall-total` in the fixture, and the detail page's own "32 days 18 hours 26 minutes" agrees with
/// the seconds to the minute. It is here so the row that exists to show the gap also says what
/// crossing it has cost somebody: 33 days of four Opterons, by XL with block Wiedemann rather than
/// by F4.
const CHOU_2015_III_N34: &[ReferencePoint] = &[ReferencePoint {
    source: "Fukuoka MQ Challenge submission details, details/details_III_20150804.html, accessed \
             2026-11-07",
    parameters: "type III, n = 34, m = 68, seed 0",
    step: "whole solve, wall-clock total",
    reported_time: "2831160 seconds (32 days 18 hours 26 minutes)",
    reported_memory: None,
    hardware: "4 x AMD Opteron 6282 SE",
    software: "XL with block Wiedemann",
}];

/// The recorded solve of type V at `m = 16` seed 0 — the same size, the same solver, the other
/// field.
///
/// `wall-total`, and **not** the 2023 figure the same size carries at seed 2: that one is
/// `370 cpu seconds for each subsystem` of a hybrid attack, one of the five per-subsystem rows
/// `docs/research/fukuoka-mq.md` §8.4 names, and quoting it as a total would understate the cost
/// by the subsystem count. Seed 0 is this row's seed and its figure is a campaign total.
const FAUGERE_2015_V_N24: &[ReferencePoint] = &[ReferencePoint {
    source: "Fukuoka MQ Challenge submission details, details/details_V_20150403.html, accessed \
             2026-11-07",
    parameters: "type V, m = 16, n = 24, seed 0",
    step: "whole solve, wall-clock total",
    reported_time: "24648.2 seconds",
    reported_memory: None,
    hardware: "Intel Xeon E5-2670 v2 @ 2.50 GHz",
    software: "F5 - FGb",
}];

const FAUGERE_2015_VI_N24: &[ReferencePoint] = &[ReferencePoint {
    source: "Fukuoka MQ Challenge submission details, details/details_VI_20150401.html, accessed \
             2026-11-07",
    parameters: "type VI, m = 16, n = 24, seed 0",
    step: "whole solve, wall-clock total",
    reported_time: "5280 seconds",
    reported_memory: None,
    hardware: "Intel Xeon E5-2670 v2 @ 2.50 GHz",
    software: "F5 - FGb",
}];

/// How a CICO answer is checked without trusting anything that produced it.
const CICO_VERIFIER: &str = "CicoInstance::is_solution rebuilds the input state and runs \
                             permutation_plus_linear, so the check goes through the permutation \
                             rather than through the polynomial system — independent of the \
                             generator and of every transformation applied to it. The program's \
                             own verifier is verify_cico_solution in poseidon-tools.";

/// How an MQ answer is checked.
const MQ_VERIFIER: &str = "evaluate the imported coefficient vectors of the original published \
                           file at the candidate, inverting any specialization first";

/// The Six Worlds Anemoi work, as this registry read it.
const SIX_WORLDS: ChallengeProgram = ChallengeProgram {
    name: "Six Worlds of Gröbner Basis Cryptanalysis: Application to Anemoi",
    version: "ToSC 2024 no. 4, pp. 138-190, DOI 10.46586/tosc.v2024.i4.138-190; experimental \
              output at github.com/IAIK/six-worlds-anemoi commit fa056e6f, read 2026-11-06",
    url: "https://tosc.iacr.org/index.php/ToSC/article/view/11953",
    reward: None,
    redistribution: "the paper is open access and the experimental output is MIT, so its data may \
                     be redistributed; the committed CICO witnesses cite the results file they \
                     were extracted from",
};

/// How an Anemoi CICO answer is checked without trusting anything that produced it.
const ANEMOI_VERIFIER: &str =
    "Anemoi::is_cico_solution runs the permutation on (0, y) and checks that the first output \
     word is zero, so the check goes through the permutation rather than through the polynomial \
     system - independent of the model and of every transformation applied to it. The reference's \
     own check_polynomial_verification is the designers' equivalent and needs Sage; \
     docs/research/anemoi.md section 4 records what was used instead.";

/// The machine every Six Worlds figure was measured on.
const SIX_WORLDS_HARDWARE: &str = "Intel Xeon E5-2630 v3 @ 2.40 GHz, 378 GB, Debian 11";

/// The software every Six Worlds figure was measured with.
const SIX_WORLDS_SOFTWARE: &str = "Magma V2.26-2";

/// The published Gröbner-basis and FGLM times at `p = 2^64 - 353`, `N = 1..6`.
///
/// Returns both steps, in that order, because the whole reason this family was chosen is that the
/// two are 2 400x apart at `N = 5` — a single combined figure would hide the finding.
///
/// `N = 1` and `N = 2` are recorded as below the log's resolution rather than as zero: the logs
/// print `0.000` for both steps there, which is a statement about the timer and not about the work.
///
/// The `N = 1..5` figures are the paper's own table; `N = 6` is read from the log, where the basis
/// step is published and the conversion step is not. [`NOT_REPORTED`] is why that distinction
/// survives into the registry.
static ANEMOI_64_POINTS: [[ReferencePoint; 2]; 6] = [
    six_worlds_row(
        ANEMOI_64_SOURCE,
        "N = 1, FCICO",
        BELOW_RESOLUTION,
        BELOW_RESOLUTION,
    ),
    six_worlds_row(
        ANEMOI_64_SOURCE,
        "N = 1, PCICO",
        BELOW_RESOLUTION,
        BELOW_RESOLUTION,
    ),
    six_worlds_row(
        ANEMOI_64_SOURCE,
        "N = 2, FCICO",
        BELOW_RESOLUTION,
        BELOW_RESOLUTION,
    ),
    six_worlds_row(
        ANEMOI_64_SOURCE,
        "N = 2, PCICO",
        BELOW_RESOLUTION,
        BELOW_RESOLUTION,
    ),
    six_worlds_row(ANEMOI_64_SOURCE, "N = 3, FCICO", "0.017 s", "0.199 s"),
    six_worlds_row(ANEMOI_64_SOURCE, "N = 3, PCICO", "0.010 s", "0.320 s"),
];

/// The second half of [`ANEMOI_64_POINTS`], split only because a `const fn` array initializer of
/// twelve rows exceeds what one `static` reads comfortably.
static ANEMOI_64_POINTS_HIGH: [[ReferencePoint; 2]; 6] = [
    six_worlds_row(ANEMOI_64_SOURCE, "N = 4, FCICO", "0.280 s", "67.760 s"),
    six_worlds_row(ANEMOI_64_SOURCE, "N = 4, PCICO", "0.199 s", "56.439 s"),
    six_worlds_row(ANEMOI_64_SOURCE, "N = 5, FCICO", "9.320 s", "22057.080 s"),
    six_worlds_row(ANEMOI_64_SOURCE, "N = 5, PCICO", "5.700 s", "15569.549 s"),
    six_worlds_row(ANEMOI_64_SOURCE, "N = 6, FCICO", "132.520 s", NOT_REPORTED),
    six_worlds_row(ANEMOI_64_SOURCE, "N = 6, PCICO", "372.200 s", NOT_REPORTED),
];

/// The published figures at `p = 2^32 - 209`, `N = 1..6`.
///
/// The sweep stops after the basis step at `N = 5`, so four rows of this table are
/// [`NOT_REPORTED`] on the conversion. That is the point of the row rather than a defect in it: the
/// `N = 4` conversion here, 63.2 s, is within 7% of the 67.8 s at `2^64 - 353` and 39x the 1.6 s at
/// `65537` — which is where the published gap actually comes from.
static ANEMOI_32_POINTS: [[ReferencePoint; 2]; 6] = [
    six_worlds_row(
        ANEMOI_32_SOURCE,
        "N = 1, FCICO",
        BELOW_RESOLUTION,
        BELOW_RESOLUTION,
    ),
    six_worlds_row(
        ANEMOI_32_SOURCE,
        "N = 1, PCICO",
        BELOW_RESOLUTION,
        BELOW_RESOLUTION,
    ),
    six_worlds_row(
        ANEMOI_32_SOURCE,
        "N = 2, FCICO",
        BELOW_RESOLUTION,
        BELOW_RESOLUTION,
    ),
    six_worlds_row(
        ANEMOI_32_SOURCE,
        "N = 2, PCICO",
        BELOW_RESOLUTION,
        BELOW_RESOLUTION,
    ),
    six_worlds_row(ANEMOI_32_SOURCE, "N = 3, FCICO", "0.019 s", "0.390 s"),
    six_worlds_row(ANEMOI_32_SOURCE, "N = 3, PCICO", "0.009 s", "0.300 s"),
];

/// The second half of [`ANEMOI_32_POINTS`].
static ANEMOI_32_POINTS_HIGH: [[ReferencePoint; 2]; 6] = [
    six_worlds_row(ANEMOI_32_SOURCE, "N = 4, FCICO", "0.439 s", "63.229 s"),
    six_worlds_row(ANEMOI_32_SOURCE, "N = 4, PCICO", "0.159 s", "50.279 s"),
    six_worlds_row(ANEMOI_32_SOURCE, "N = 5, FCICO", "6.049 s", NOT_REPORTED),
    six_worlds_row(ANEMOI_32_SOURCE, "N = 5, PCICO", "3.579 s", NOT_REPORTED),
    six_worlds_row(ANEMOI_32_SOURCE, "N = 6, FCICO", NOT_REPORTED, NOT_REPORTED),
    six_worlds_row(ANEMOI_32_SOURCE, "N = 6, PCICO", NOT_REPORTED, NOT_REPORTED),
];

/// The published figures at `p = 65537`, `N = 1..6`.
///
/// The only prime of the sweep whose logs carry an `N = 6` conversion figure, in **both** models —
/// 23 340 s and 11 775 s, at the quotient dimension `5^6 = 15 625` the logs also print. That makes
/// `N = 6` a reproduction target here and a produced figure at the other two primes; see
/// `docs/research/anemoi.md` section 8a.3.
static ANEMOI_17_POINTS: [[ReferencePoint; 2]; 6] = [
    six_worlds_row(
        ANEMOI_17_SOURCE,
        "N = 1, FCICO",
        BELOW_RESOLUTION,
        BELOW_RESOLUTION,
    ),
    six_worlds_row(
        ANEMOI_17_SOURCE,
        "N = 1, PCICO",
        BELOW_RESOLUTION,
        BELOW_RESOLUTION,
    ),
    six_worlds_row(
        ANEMOI_17_SOURCE,
        "N = 2, FCICO",
        "0.003 s",
        BELOW_RESOLUTION,
    ),
    six_worlds_row(
        ANEMOI_17_SOURCE,
        "N = 2, PCICO",
        BELOW_RESOLUTION,
        BELOW_RESOLUTION,
    ),
    six_worlds_row(ANEMOI_17_SOURCE, "N = 3, FCICO", "0.007 s", "0.060 s"),
    six_worlds_row(
        ANEMOI_17_SOURCE,
        "N = 3, PCICO",
        BELOW_RESOLUTION,
        "0.050 s",
    ),
];

/// The second half of [`ANEMOI_17_POINTS`].
static ANEMOI_17_POINTS_HIGH: [[ReferencePoint; 2]; 6] = [
    six_worlds_row(ANEMOI_17_SOURCE, "N = 4, FCICO", "0.049 s", "1.620 s"),
    six_worlds_row(ANEMOI_17_SOURCE, "N = 4, PCICO", "0.020 s", "1.420 s"),
    six_worlds_row(ANEMOI_17_SOURCE, "N = 5, FCICO", "1.089 s", "135.640 s"),
    six_worlds_row(ANEMOI_17_SOURCE, "N = 5, PCICO", "0.129 s", "75.750 s"),
    six_worlds_row(ANEMOI_17_SOURCE, "N = 6, FCICO", "45.930 s", "23340.220 s"),
    six_worlds_row(ANEMOI_17_SOURCE, "N = 6, PCICO", "1.560 s", "11775.430 s"),
];

/// What the logs print at `N = 1` and `N = 2`, which is a statement about the timer.
const BELOW_RESOLUTION: &str = "0.000 s, below the log's resolution";

/// What the registry records where the sweep ran the basis step and stopped.
///
/// Distinct from an empty `reference_points` list, which says "this registry has not looked". A row
/// carrying this has been looked at and the reference does not have the figure, so a measurement
/// against it is a **produced** number rather than a reproduced one — and
/// [`ReferencePoint::reported_time`] being prose rather than a quantity is what stops a comparison
/// tool from parsing it as a time. [`BELOW_RESOLUTION`] is the existing precedent for that.
const NOT_REPORTED: &str = "not reported; the sweep ran this round's basis step and stopped";

/// The results file at `p = 2^64 - 353`.
const ANEMOI_64_SOURCE: &str =
    "Six Worlds, results/anemoi_p18446744073709551263_n1_l1_a3_m<MODEL>_o1.txt";

/// The results file at `p = 2^32 - 209`.
const ANEMOI_32_SOURCE: &str = "Six Worlds, results/anemoi_p4294967087_n1_l1_a3_m<MODEL>_o1.txt";

/// The results file at `p = 65537`.
const ANEMOI_17_SOURCE: &str = "Six Worlds, results/anemoi_p65537_n1_l1_a3_m<MODEL>_o1.txt";

/// One row's two figures, in the order the solve takes them.
///
/// Both steps, never one combined figure: the whole reason this family was chosen is that they are
/// 2 400x apart at `N = 5`, and a single number would hide the finding.
const fn six_worlds_row(
    source: &'static str,
    parameters: &'static str,
    basis: &'static str,
    conversion: &'static str,
) -> [ReferencePoint; 2] {
    const fn point(
        source: &'static str,
        parameters: &'static str,
        step: &'static str,
        reported_time: &'static str,
    ) -> ReferencePoint {
        ReferencePoint {
            source,
            parameters,
            step,
            reported_time,
            // The logs report peak resident set size once per sweep, not per row.
            reported_memory: None,
            hardware: SIX_WORLDS_HARDWARE,
            software: SIX_WORLDS_SOFTWARE,
        }
    }
    [
        point(source, parameters, "Groebner basis (Magma F4)", basis),
        point(source, parameters, "FGLM order change", conversion),
    ]
}

/// The published Groebner-basis and FGLM times for one registered Anemoi row.
///
/// Empty for a prime the sweep covers but this registry does not register, and for `N > 6`: the
/// logs continue to `N = 8` on the basis step alone. Inside `N = 1..6` the figure is always
/// present, and a step the sweep did not run is [`NOT_REPORTED`] rather than missing — the
/// distinction between "not published" and "not looked for" is the whole reason #286 exists.
fn six_worlds_points(prime: u64, rounds: usize, model: AnemoiModel) -> &'static [ReferencePoint] {
    if rounds == 0 || rounds > 6 {
        return &[];
    }
    let (low, high) = match prime {
        ANEMOI_64_PRIME => (&ANEMOI_64_POINTS, &ANEMOI_64_POINTS_HIGH),
        ANEMOI_32_PRIME => (&ANEMOI_32_POINTS, &ANEMOI_32_POINTS_HIGH),
        ANEMOI_17_PRIME => (&ANEMOI_17_POINTS, &ANEMOI_17_POINTS_HIGH),
        _ => return &[],
    };
    let column = match model {
        AnemoiModel::Fcico => 0,
        AnemoiModel::Pcico => 1,
    };
    let index = 2 * (rounds - 1) + column;
    if index < low.len() {
        &low[index]
    } else {
        &high[index - low.len()]
    }
}

/// The published quotient dimension for `α = 3` at `N` rounds: `(α + 2)^N`, as measured.
///
/// `Claim::Observed` and **not** `Claim::Proved` at every call site: these are measurements from
/// one implementation, and the designers' corresponding statement is a conjecture.
pub fn published_quotient_dimension(alpha: u32, rounds: usize) -> Claim<u128> {
    Claim::Observed(u128::from(alpha + 2).pow(rounds as u32))
}

/// The input constants every KoalaBear CICO row shares: `C_1 = 0xc09de4`, `C_2 = 0xee6282`.
const C1: u64 = 0xC0_9DE4;
const C2: u64 = 0xEE_6282;

/// The official 2026 CICO targets: `(R_P, reward, the date the program verified a solution)`.
const OFFICIAL_ROUNDS: [(usize, &str, &str); 3] = [
    (6, "$6,000", "2026-04-10"),
    (8, "$10,000", "2026-05-06"),
    (10, "$15,000", "2026-07-06"),
];

/// The method to record when nothing has been published, derived from the external status.
///
/// A problem solved externally with no located report is [`DisclosedMethod::Unknown`] — the one
/// state that must not be guessed at. Everything else has no external solution whose method could
/// be disclosed.
fn default_method(external: ExternalStatus) -> DisclosedMethod {
    match external {
        // Solved by somebody, and no report located. The one state that must not be guessed at.
        ExternalStatus::SolvedExternally { .. } => DisclosedMethod::Unknown,
        // Nothing has been solved externally, so there is no method to disclose.
        ExternalStatus::NoneRecorded { .. }
        | ExternalStatus::PublishedWithAnswer
        | ExternalStatus::NotAPublicProblem => DisclosedMethod::NotApplicable,
    }
}

/// The attack method published for an official target, by its partial-round count.
///
/// None is attributed to the submission the program verified: the program does not name first
/// submitters, so a paper at the same parameters is evidence that the parameters fall, not that
/// this is how they fell. `R_P = 10` is solved and has no public method, and the program allows a
/// report to stay private until 2027-01-01. See `docs/research/elimination-beyond-grobner.md` §2.
fn official_method(r_p: usize) -> DisclosedMethod {
    match r_p {
        6 => DisclosedMethod::Published {
            method: "Villard-style bivariate resultant, one full round skipped",
            source: "eprint 2026/1905, Bak and Hostettler, Table 4",
            reported_cost: "1 d 17 h on 128 CPU cores",
            attributed_to_submission: false,
        },
        8 => DisclosedMethod::Published {
            method: "round skip, interpolation, Graeffe root finding; no resultant",
            source: "eprint 2026/1254, Sanso and Vitto, Section 4.2 and Table 1",
            reported_cost: "7 h on 96 RTX 5090 GPUs",
            attributed_to_submission: false,
        },
        _ => DisclosedMethod::Unknown,
    }
}

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
            method: official_method(r_p),
            // No published cost figure for this row; see ReferencePoint.
            reference_points: &[],
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
            method: default_method(ExternalStatus::NotAPublicProblem),
            // No published cost figure for this row; see ReferencePoint.
            reference_points: &[],
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
            method: default_method(ExternalStatus::NotAPublicProblem),
            // No published cost figure for this row; see ReferencePoint.
            reference_points: &[],
            verifier: CICO_VERIFIER,
            notes: "A planted target, so a solution is known to exist and \"found nothing\" is \
                    distinguishable from \"is broken\". Regression and profiling only.",
        });
    }

    // The 2025 bounty program's tiers that the program itself still lists as unsolved. A
    // different objective from the 2026 CICO program — the zeros are the *trailing* words, not the
    // leading ones — and two of the three are over fields this crate has no coefficient type for.
    // Registered and refused by the constructor, because a scoreboard that lists only what it can
    // run hides exactly the problems that are open.
    //
    // Unsolved and unclaimable are both true here, and they are different facts (#200). The
    // program's window closed 2025-12-01, so the `reward` figures are EXPIRED — said in `version`,
    // because `ExternalStatus` answers "has anyone solved this" and nothing about a funding
    // program's calendar. These rows stay the most interesting in the registry on the strength of
    // the first fact alone.
    for (id, program_field, prime, alpha, t, r_f, r_p, reward, notes) in [
        (
            "poseidon256-cico-2025-rf6-rp11",
            "BLS12-381 scalar field",
            "52435875175126190479447740508185965837690552500527637822603658699938581184513",
            5u32,
            3usize,
            6usize,
            11usize,
            "$10,000",
            "Perm(X_1, X_2, 0) = (Y_1, Y_2, 0), a 32-bit tier of the 2025 program, listed as \
             unsolved on 2026-11-08. A 255-bit field, which this generator is not wired for.",
        ),
        (
            "poseidon256-cico-2025-rf6-rp16",
            "BLS12-381 scalar field",
            "52435875175126190479447740508185965837690552500527637822603658699938581184513",
            5,
            3,
            6,
            16,
            "$15,000",
            "The 40-bit tier of the same family, listed as unsolved on 2026-11-08 and the hardest \
             offered there.",
        ),
        (
            "poseidon64-cico-2025-rf6-rp13",
            "Goldilocks",
            "18446744069414584321",
            7,
            8,
            6,
            13,
            "$15,000",
            "Perm(X_1..X_7, 0) = (Y_1..Y_7, 0) over 2^64 - 2^32 + 1 with a degree-7 S-box, the \
             40-bit tier, listed as unsolved on 2026-11-08. The lower tiers of this family were \
             claimed in April and May 2025.",
        ),
    ] {
        // Bound once so the status and the method it implies cannot drift apart: these are the
        // *unsolved* tiers of the 2025 program, so there is no external solution whose method
        // could be disclosed.
        let external = ExternalStatus::NoneRecorded {
            as_of: "2026-11-08",
        };
        challenges.push(ChallengeManifest {
            id,
            schema: ChallengeManifest::SCHEMA,
            class: BenchmarkClass::Official,
            parameters: ChallengeParameters::PoseidonCicoUnregisterable {
                field: program_field,
                prime,
                alpha,
                t,
                k: 1,
                r_f,
                r_p,
            },
            objective: Objective::CicoExactTrailing,
            program: ChallengeProgram {
                version: "2025 bounty program, ran till 2025-12-01, read 2026-11-08; the reward \
                          is EXPIRED — the window closed and the tier is still listed as \
                          unclaimed. See docs/research/prize-ledger.md",
                reward: Some(reward),
                ..INITIATIVE
            },
            external,
            method: default_method(external),
            // No published cost figure for this row; see ReferencePoint.
            reference_points: &[],
            verifier: "the program's own verifier; this crate generates no system for this \
                       objective and so has nothing to check",
            notes,
        });
    }

    // The Six Worlds Anemoi ladder: N = 1..6 at alpha = 3, l = 1, both models, at the three prime
    // fields the sweep covers that fit a u64. Frozen before anything is run, like the Poseidon
    // ladder above it.
    //
    // N = 6 is the rung the ladder originally stopped short of, and the three primes do not agree
    // on what it is. At 2^64 - 353 and 2^32 - 209 the sweep publishes a basis figure and no
    // conversion, so a measurement there is a PRODUCED number: there is nothing to reproduce and
    // no comparable modern Magma run exists on this machine. At 65537 the logs publish both steps
    // -- 45.93 s and 23 340.22 s for FCICO, 1.56 s and 11 775.43 s for PCICO -- at the quotient
    // dimension 5^6 = 15 625 they also print, so that row is a reproduction target. Registering
    // all six at once keeps the distinction in the data rather than in a reader's memory.
    //
    // Three characteristics because that is the experiment #283 needs. The published conversion
    // cost at N = 4 is 1.6 s at 65537, 63.2 s at 2^32 - 209 and 67.8 s at 2^64 - 353, and Magma's
    // own logs name the mechanism: `Matrix kind: Modular FP` at the first prime and
    // `Generic finite field` at the other two. Zeebra's `PrimeFieldElement64<P>` is one Montgomery
    // path at all three, so the within-implementation ratio is comparable down the column and the
    // reference's is not.
    for prime in [ANEMOI_64_PRIME, ANEMOI_32_PRIME, ANEMOI_17_PRIME] {
        for rounds in 1..=6 {
            for model in [AnemoiModel::Fcico, AnemoiModel::Pcico] {
                challenges.push(ChallengeManifest {
                    id: anemoi_id(prime, rounds, model),
                    schema: ChallengeManifest::SCHEMA,
                    // Official rather than FaithfulReduction: see the module docs.
                    class: BenchmarkClass::Official,
                    parameters: ChallengeParameters::AnemoiCico {
                        prime,
                        alpha: 3,
                        l: 1,
                        rounds,
                        model,
                    },
                    objective: Objective::CicoExact,
                    program: SIX_WORLDS,
                    external: ExternalStatus::PublishedWithAnswer,
                    method: default_method(ExternalStatus::PublishedWithAnswer),
                    reference_points: six_worlds_points(prime, rounds, model),
                    verifier: ANEMOI_VERIFIER,
                    notes: anemoi_notes(prime),
                });
            }
        }
    }

    // The field is per row rather than per loop: it is in the identity digest, and types II and V
    // are GF(2^8) where III and VI are GF(31). Hardcoding it was invisible while the registry held
    // one field (#510).
    for (id, field, kind, n, m, sha256, external, reference_points, notes) in [
        (
            "fukuoka-mq-III-n10-seed0",
            "GF(31)",
            "III",
            10usize,
            20usize,
            "9436e45dbd4247f152681e954f1db19d92e8cf5e76b2bc35530bed74aae522ba",
            ExternalStatus::PublishedWithAnswer,
            NO_REFERENCE_POINTS,
            "The overdetermined encryption family. Published with its answer so an \
             implementation can check itself; 24 variables short of the smallest type III \
             challenge and 14 short of the smallest importable one.",
        ),
        (
            "fukuoka-mq-III-n15-seed0",
            "GF(31)",
            "III",
            15,
            30,
            "1dcee7e5e1a5dad4885471fed133158d6bce7a61822ed4aa39a1f91c9264b97b",
            ExternalStatus::PublishedWithAnswer,
            NO_REFERENCE_POINTS,
            "The next published type III size up from n = 10.",
        ),
        (
            "fukuoka-mq-III-n20-seed0",
            "GF(31)",
            "III",
            20,
            40,
            "ecb087b4128d490dd0931b877f7827786d3f49fa27facabde629d9e1f057e072",
            ExternalStatus::PublishedWithAnswer,
            HUANG_2015_III_N20,
            "The largest published type III toy example.",
        ),
        (
            "fukuoka-mq-VI-n10-seed0",
            "GF(31)",
            "VI",
            10,
            7,
            "9512b6032be415ae8391b72ed8ad4f43357bafa4f0058d60b06dba3537a41af3",
            ExternalStatus::PublishedWithAnswer,
            NO_REFERENCE_POINTS,
            "The signature family: n > m, so positive-dimensional as published. A specialized \
             slice is a different problem and is registered as its own instance when run.",
        ),
        (
            "fukuoka-mq-VI-n15-seed0",
            "GF(31)",
            "VI",
            15,
            10,
            "ad22fe9a065688453b481fe8cb0e2990f3207920dc83e8c64f8dea2651b5e888",
            ExternalStatus::PublishedWithAnswer,
            HUANG_2015_VI_N15,
            "Five surplus variables rather than three, so a specialization campaign has a larger \
             slice space.",
        ),
        (
            // The smallest *type III* challenge: the download index lists challenge-3-34-0
            // through challenge-3-53-0, so the range is n = 34..=53. The row was at n = 55 until
            // #501, which is type I's lower bound and an instance type III does not publish.
            "fukuoka-mq-III-n34-seed0",
            "GF(31)",
            "III",
            34,
            68,
            "",
            // Solved externally, not open: the fixture records type III n = 34 seeds 0 and 1, so
            // the row the n = 55 one claimed to be — "the smallest real size, with no public
            // solution" — does not exist. The smallest type III size with no recorded solve is
            // n = 39 (docs/research/fukuoka-mq.md §8.1), and §8.3 is why that is not a claim about
            // hardness.
            ExternalStatus::SolvedExternally {
                verified: "2015-08-04",
            },
            CHOU_2015_III_N34,
            "Registered to show the gap in the family this crate has actually measured, and \
             deliberately not implemented: 14 variables past the largest toy example, with no \
             dispatch arm and no bytes held here, so its file checksum is empty. The smallest \
             real instance this crate can import is fukuoka-mq-VI-n24-seed0, in a different \
             type.",
        ),
        (
            // The first row in this family that is challenge data rather than a toy example.
            // Type VI publishes m = 16..=35 and the generator computes n = m * 1.5, so the
            // smallest of them is n = 24.
            "fukuoka-mq-VI-n24-seed0",
            "GF(31)",
            "VI",
            24,
            16,
            "354de307fa5524d01c8a6ece3c712c27119cf3388bdd7a3e1c84095ed6cc43de",
            // Solved externally rather than open: the hall of fame records m = 16..=24 for type VI,
            // and seed 0 at m = 16 is Faugère's 2015 F5-FGb submission. A witness here would be a
            // reproduction, which is the honest reading and the weaker one.
            ExternalStatus::SolvedExternally {
                verified: "2015-04-01",
            },
            FAUGERE_2015_VI_N24,
            "The smallest real challenge in a type this crate can import: type VI at m = 16, so \
             n = 24 and eight surplus variables. Underdetermined and therefore \
             positive-dimensional as published — a run of it is a run of slice(8 fixed, seed s), \
             which is a result about that slice. No instance bytes and no answer vector are \
             committed; the checksum names the file tools/fetch-mq-challenge.sh fetches.",
        ),
        (
            // The other half of the same arm: type V publishes m = 16..=35 over GF(2^8), so its
            // smallest real instance is the same n = 24 as type VI's. The field is the
            // challenge's own GF(2^8) — x^8 + x^4 + x^3 + x^2 + 1, not the AES modulus — and the
            // importer checks the header's modulus rather than assuming it (#510).
            "fukuoka-mq-V-n24-seed0",
            "GF(2^8)",
            "V",
            24,
            16,
            "fb4b6a3d27fb8263b1a9883745691f3836ad747a6a4052d28919ea5b1a213cc7",
            // Solved externally: the hall of fame records type V m = 16..=21, and seed 0 at
            // m = 16 is Faugère's 2015 F5-FGb submission three days after his type VI one. A
            // witness here would be a reproduction.
            ExternalStatus::SolvedExternally {
                verified: "2015-04-03",
            },
            FAUGERE_2015_V_N24,
            "Type V at m = 16: the smallest real challenge over GF(2^8), at the same n = 24 as \
             the type VI row and therefore served by the same compiled dimension. \
             Underdetermined and so positive-dimensional as published, like type VI. The \
             published figure at this size and seed is a wall-clock total; the 370-second figure \
             the same size carries at seed 2 is per subsystem of a hybrid attack and must never \
             be quoted as a total (docs/research/fukuoka-mq.md section 8.4). No instance bytes \
             and no answer vector are committed; a real challenge publishes no answer at all.",
        ),
    ] {
        challenges.push(ChallengeManifest {
            id,
            schema: ChallengeManifest::SCHEMA,
            class: BenchmarkClass::Official,
            parameters: ChallengeParameters::MqSystem {
                field,
                kind,
                n,
                m,
                seed: 0,
                sha256,
            },
            objective: Objective::MqRoot,
            program: FUKUOKA,
            external,
            method: default_method(external),
            reference_points,
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

/// What an Anemoi row at this prime is, and what a result on it does and does not say.
///
/// Per prime rather than one string because the characteristic is the only thing that differs
/// between the three ladders, and because the two smaller primes exist for a stated purpose — #283
/// — that a reader of the row should not have to reconstruct.
fn anemoi_notes(prime: u64) -> &'static str {
    match prime {
        ANEMOI_64_PRIME => {
            "Anemoi(0, y) = (0, *) over 2^64 - 353 with alpha = 3 and l = 1, at the round count \
             the Six Worlds experiments ran. The round constants are derived from the digits of pi \
             and depend on g, the smallest primitive root, which the specification does not fix; \
             ChallengeManifest::anemoi_derived_digest pins them. A result here reproduces a \
             published measurement on a reduced-round primitive and says nothing about full-round \
             Anemoi, which is 21 rounds at 128-bit security and is not registered anywhere."
        }
        ANEMOI_32_PRIME => {
            "The same system over 2^32 - 209, the sweep's 32-bit prime. Registered for #283, to \
             separate field arithmetic from conversion algorithmics: the reference's published \
             conversion cost here is within 7% of its cost at 2^64 - 353 while its basis step is \
             comparable, so a within-implementation ratio that moves between these two primes is \
             about arithmetic and not about N. The sweep stops after the basis step at N = 5, so \
             N = 6 here has no published figure for either step. As at 2^64 - 353, a result here \
             says nothing about full-round Anemoi."
        }
        ANEMOI_17_PRIME => {
            "The same system over 65537, the smallest prime of the sweep and the control for #283. \
             Magma takes its Modular FP matrix path here and its generic finite-field path at the \
             two larger primes, which is the reference-side mechanism the published gap has to be \
             read against. This is also the only prime whose logs publish an N = 6 conversion \
             figure in both models. As at 2^64 - 353, a result here says nothing about full-round \
             Anemoi."
        }
        _ => unreachable!("three primes are registered"),
    }
}

/// An Anemoi row's id. `&'static str` because an id is part of a frozen registry, not a format.
///
/// The leading number is the prime's bit width, as `poseidon31` and `poseidon256` already use it.
/// The `anemoi64` ids predate the other two characteristics and are kept byte-identical, so #283's
/// additions are additions in `test_the_registry_is_frozen` rather than redefinitions.
fn anemoi_id(prime: u64, rounds: usize, model: AnemoiModel) -> &'static str {
    match (prime, rounds, model) {
        (ANEMOI_64_PRIME, 1, AnemoiModel::Fcico) => "anemoi64-cico-n1-fcico",
        (ANEMOI_64_PRIME, 1, AnemoiModel::Pcico) => "anemoi64-cico-n1-pcico",
        (ANEMOI_64_PRIME, 2, AnemoiModel::Fcico) => "anemoi64-cico-n2-fcico",
        (ANEMOI_64_PRIME, 2, AnemoiModel::Pcico) => "anemoi64-cico-n2-pcico",
        (ANEMOI_64_PRIME, 3, AnemoiModel::Fcico) => "anemoi64-cico-n3-fcico",
        (ANEMOI_64_PRIME, 3, AnemoiModel::Pcico) => "anemoi64-cico-n3-pcico",
        (ANEMOI_64_PRIME, 4, AnemoiModel::Fcico) => "anemoi64-cico-n4-fcico",
        (ANEMOI_64_PRIME, 4, AnemoiModel::Pcico) => "anemoi64-cico-n4-pcico",
        (ANEMOI_64_PRIME, 5, AnemoiModel::Fcico) => "anemoi64-cico-n5-fcico",
        (ANEMOI_64_PRIME, 5, AnemoiModel::Pcico) => "anemoi64-cico-n5-pcico",
        (ANEMOI_64_PRIME, 6, AnemoiModel::Fcico) => "anemoi64-cico-n6-fcico",
        (ANEMOI_64_PRIME, 6, AnemoiModel::Pcico) => "anemoi64-cico-n6-pcico",
        (ANEMOI_32_PRIME, 1, AnemoiModel::Fcico) => "anemoi32-cico-n1-fcico",
        (ANEMOI_32_PRIME, 1, AnemoiModel::Pcico) => "anemoi32-cico-n1-pcico",
        (ANEMOI_32_PRIME, 2, AnemoiModel::Fcico) => "anemoi32-cico-n2-fcico",
        (ANEMOI_32_PRIME, 2, AnemoiModel::Pcico) => "anemoi32-cico-n2-pcico",
        (ANEMOI_32_PRIME, 3, AnemoiModel::Fcico) => "anemoi32-cico-n3-fcico",
        (ANEMOI_32_PRIME, 3, AnemoiModel::Pcico) => "anemoi32-cico-n3-pcico",
        (ANEMOI_32_PRIME, 4, AnemoiModel::Fcico) => "anemoi32-cico-n4-fcico",
        (ANEMOI_32_PRIME, 4, AnemoiModel::Pcico) => "anemoi32-cico-n4-pcico",
        (ANEMOI_32_PRIME, 5, AnemoiModel::Fcico) => "anemoi32-cico-n5-fcico",
        (ANEMOI_32_PRIME, 5, AnemoiModel::Pcico) => "anemoi32-cico-n5-pcico",
        (ANEMOI_32_PRIME, 6, AnemoiModel::Fcico) => "anemoi32-cico-n6-fcico",
        (ANEMOI_32_PRIME, 6, AnemoiModel::Pcico) => "anemoi32-cico-n6-pcico",
        (ANEMOI_17_PRIME, 1, AnemoiModel::Fcico) => "anemoi17-cico-n1-fcico",
        (ANEMOI_17_PRIME, 1, AnemoiModel::Pcico) => "anemoi17-cico-n1-pcico",
        (ANEMOI_17_PRIME, 2, AnemoiModel::Fcico) => "anemoi17-cico-n2-fcico",
        (ANEMOI_17_PRIME, 2, AnemoiModel::Pcico) => "anemoi17-cico-n2-pcico",
        (ANEMOI_17_PRIME, 3, AnemoiModel::Fcico) => "anemoi17-cico-n3-fcico",
        (ANEMOI_17_PRIME, 3, AnemoiModel::Pcico) => "anemoi17-cico-n3-pcico",
        (ANEMOI_17_PRIME, 4, AnemoiModel::Fcico) => "anemoi17-cico-n4-fcico",
        (ANEMOI_17_PRIME, 4, AnemoiModel::Pcico) => "anemoi17-cico-n4-pcico",
        (ANEMOI_17_PRIME, 5, AnemoiModel::Fcico) => "anemoi17-cico-n5-fcico",
        (ANEMOI_17_PRIME, 5, AnemoiModel::Pcico) => "anemoi17-cico-n5-pcico",
        (ANEMOI_17_PRIME, 6, AnemoiModel::Fcico) => "anemoi17-cico-n6-fcico",
        (ANEMOI_17_PRIME, 6, AnemoiModel::Pcico) => "anemoi17-cico-n6-pcico",
        _ => unreachable!("the ladder is N = 1..6 in both models at three primes"),
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
        challenge, dispatch_cico, published_quotient_dimension, registry, AnemoiCico, AnemoiModel,
        BenchmarkClass, ChallengeError, ChallengeManifest, ChallengeParameters, CicoTarget,
        CicoVisitor, DisclosedMethod, ExternalStatus, Json, Objective, ReferencePoint,
        Significance,
    };
    use crate::{
        fields::{PrimeFieldElement64, Zp18446744073709551263},
        grobner::research::{
            anemoi_cico::{dispatch_anemoi_cico, verify_against_anemoi_trace, AnemoiCicoVisitor},
            verify_against_trace, KOALABEAR_PRIME, SUPPORTED_DIMENSIONS,
        },
        FiniteField, KnownOrder, MultivariatePolynomial,
    };

    type K = PrimeFieldElement64<KOALABEAR_PRIME>;

    /// `2^64 - 353`, the field the published Anemoi ladder is over.
    type A = Zp18446744073709551263;

    /// `2^32 - 209`. No alias in `fields`: `PrimeFieldElement64` is const-generic, so a prime of
    /// this width needs no new code and the ladder at a third characteristic needs no new field.
    type A32 = PrimeFieldElement64<{ super::ANEMOI_32_PRIME }>;

    /// `65537`, the control characteristic for #283.
    type A17 = PrimeFieldElement64<{ super::ANEMOI_17_PRIME }>;

    /// The disclosed method reaches the JSON record with `attributed_to_submission` as a boolean.
    ///
    /// Typed on purpose. A nonempty string is truthy in several languages a consumer might be
    /// written in, so serializing `"false"` would make every row read as attributed to the
    /// verified submission — the one inference this field exists to prevent. The digest test
    /// cannot catch this, because the method is deliberately outside the digest.
    #[test]
    fn test_json_types_the_attribution_flag_as_a_boolean() {
        // Rendered and parsed back, so the assertion is on the type in the document rather than
        // on the Rust value that produced it.
        let text = challenge("poseidon31-cico-rf6-rp8")
            .expect("registered")
            .to_json()
            .to_json();
        let parsed = Json::parse(&text).expect("the record is valid JSON");
        let method = parsed
            .get("disclosed_method")
            .expect("disclosed_method is recorded");

        assert_eq!(
            method.get("attributed_to_submission"),
            Some(&Json::Bool(false)),
            "the flag must be a JSON boolean, not a string: {text}"
        );
        // The source and its hardware travel with the method, so a reader can check the figure.
        assert_eq!(
            method.get("source").and_then(Json::as_str),
            Some("eprint 2026/1254, Sanso and Vitto, Section 4.2 and Table 1")
        );
        assert_eq!(
            method.get("reported_cost").and_then(Json::as_str),
            Some("7 h on 96 RTX 5090 GPUs")
        );

        // An unknown method says so, and carries no flag that could be misread.
        let unknown = Json::parse(
            &challenge("poseidon31-cico-rf6-rp10")
                .expect("registered")
                .to_json()
                .to_json(),
        )
        .expect("valid JSON");
        let unknown = unknown.get("disclosed_method").expect("recorded");
        assert_eq!(unknown.get("state").and_then(Json::as_str), Some("unknown"));
        assert_eq!(unknown.get("attributed_to_submission"), None);
    }

    /// Each official target records the attack method publicly disclosed for it, or `Unknown`.
    ///
    /// `R_P = 10` is the one that matters: it is solved and verified externally, and no method has
    /// been published, so anything other than `Unknown` would be an invention.
    #[test]
    fn test_the_official_targets_record_their_disclosed_method() {
        let registry = registry();
        let method_of = |id: &str| {
            registry
                .iter()
                .find(|c| c.id == id)
                .expect("registered")
                .method
        };

        match method_of("poseidon31-cico-rf6-rp6") {
            DisclosedMethod::Published { method, .. } => {
                assert!(method.contains("Villard"), "{method}")
            }
            other => panic!("R_P = 6 has a published resultant attack, got {other:?}"),
        }
        match method_of("poseidon31-cico-rf6-rp8") {
            DisclosedMethod::Published { method, .. } => {
                assert!(method.contains("Graeffe"), "{method}")
            }
            other => panic!("R_P = 8 has a published univariate attack, got {other:?}"),
        }
        assert_eq!(
            method_of("poseidon31-cico-rf6-rp10"),
            DisclosedMethod::Unknown,
            "no method is published for R_P = 10"
        );
    }

    /// No disclosed method claims to be the submission the program verified.
    ///
    /// The program does not name first submitters, so a paper describing an attack at the same
    /// parameters is not thereby the verified submission. This asserts the registry never says it
    /// is on the present evidence — the field exists so that it *can* be set when it is known.
    #[test]
    fn test_no_disclosed_method_is_attributed_to_a_verified_submission() {
        for challenge in registry() {
            if let DisclosedMethod::Published {
                attributed_to_submission,
                source,
                ..
            } = challenge.method
            {
                assert!(
                    !attributed_to_submission,
                    "{} attributes {} to the verified submission",
                    challenge.id, source
                );
            }
        }
    }

    /// Disclosing a method does not change a problem's identity.
    ///
    /// The invariant the whole design rests on: the digest covers the mathematics, and a method is
    /// paperwork. Checked by digesting a row and then digesting it again under every variant,
    /// rather than by trusting that `canonical` happens not to mention the field.
    #[test]
    fn test_disclosing_a_method_does_not_change_identity() {
        let original = registry()
            .into_iter()
            .find(|c| c.id == "poseidon31-cico-rf6-rp10")
            .expect("registered");
        let expected = original.digest();

        for method in [
            DisclosedMethod::Unknown,
            DisclosedMethod::NotApplicable,
            DisclosedMethod::Published {
                method: "something else entirely",
                source: "nowhere",
                reported_cost: "no time at all",
                attributed_to_submission: true,
            },
        ] {
            let mut altered = original.clone();
            altered.method = method;
            assert_eq!(
                altered.digest(),
                expected,
                "{method:?} changed the identity"
            );
        }
    }

    /// A problem nobody posed has no external method to disclose.
    #[test]
    fn test_a_derived_problem_reports_no_applicable_method() {
        for challenge in registry() {
            if challenge.external == ExternalStatus::NotAPublicProblem {
                assert_eq!(
                    challenge.method,
                    DisclosedMethod::NotApplicable,
                    "{} is derived here",
                    challenge.id
                );
            }
        }
    }

    /// Every row carrying a reward figure states the program's claimability and the date it was
    /// read, so no dollar amount in the registry can be read as a live opportunity on its own.
    #[test]
    fn test_a_reward_is_never_recorded_without_its_claimability_and_a_read_date() {
        // The prize-ledger vocabulary of `docs/research/prize-ledger.md` §1. A reward figure is
        // meaningless without one of these beside it: `ExternalStatus` says whether anyone solved
        // the problem, which is a different fact and moves on a different schedule.
        let states = ["open", "paused", "finished", "expired", "unverified"];

        let mut checked = 0;
        for challenge in registry() {
            let Some(reward) = challenge.program.reward else {
                continue;
            };
            checked += 1;
            let version = challenge.program.version.to_ascii_lowercase();

            assert!(
                states.iter().any(|state| version.contains(state)),
                "{}: reward {} names none of the claimability states {:?} in {:?}",
                challenge.id,
                reward,
                states,
                challenge.program.version
            );

            let read = version
                .split_once("read ")
                .map(|(_, rest)| rest)
                .unwrap_or_else(|| panic!("{}: reward {} has no read date", challenge.id, reward));
            let date: String = read.chars().take(10).collect();
            assert!(
                date.len() == 10
                    && date.as_bytes()[4] == b'-'
                    && date.as_bytes()[7] == b'-'
                    && date.chars().filter(char::is_ascii_digit).count() == 8,
                "{}: reward {} is read as of {:?}, which is not an ISO date",
                challenge.id,
                reward,
                date
            );
        }

        assert_eq!(checked, 6, "the six registered rows that carry a reward");
    }

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
            ("poseidon256-cico-2025-rf6-rp11", "341728ee0a3d"),
            ("poseidon256-cico-2025-rf6-rp16", "d63ef953e886"),
            ("poseidon64-cico-2025-rf6-rp13", "442f473600ad"),
            ("anemoi64-cico-n1-fcico", "8228cbc3d18e"),
            ("anemoi64-cico-n1-pcico", "ce10ff6c5750"),
            ("anemoi64-cico-n2-fcico", "ef9b02569e32"),
            ("anemoi64-cico-n2-pcico", "4d31f9c78de0"),
            ("anemoi64-cico-n3-fcico", "b9868196b3ef"),
            ("anemoi64-cico-n3-pcico", "504c96c59a37"),
            ("anemoi64-cico-n4-fcico", "95bc61726779"),
            ("anemoi64-cico-n4-pcico", "b61cd0a62722"),
            ("anemoi64-cico-n5-fcico", "a56639921520"),
            ("anemoi64-cico-n5-pcico", "d285b0cf43aa"),
            ("anemoi64-cico-n6-fcico", "981fd5554d29"),
            ("anemoi64-cico-n6-pcico", "251e04c1ff09"),
            // #283's two added characteristics. Appended after the 2^64 - 353 ladder so the
            // frozen prefix above keeps both its order and its digests.
            ("anemoi32-cico-n1-fcico", "d80be905379a"),
            ("anemoi32-cico-n1-pcico", "29d5929e63ef"),
            ("anemoi32-cico-n2-fcico", "83b9ba3e22d1"),
            ("anemoi32-cico-n2-pcico", "c2270ee63ae0"),
            ("anemoi32-cico-n3-fcico", "89380648f042"),
            ("anemoi32-cico-n3-pcico", "1f4b9bc83e29"),
            ("anemoi32-cico-n4-fcico", "2fa7c1697b07"),
            ("anemoi32-cico-n4-pcico", "3b63b01e4100"),
            ("anemoi32-cico-n5-fcico", "4d27b32c7ab0"),
            ("anemoi32-cico-n5-pcico", "98887225a4ed"),
            ("anemoi32-cico-n6-fcico", "b84a0c55fcb7"),
            ("anemoi32-cico-n6-pcico", "afce463aadb0"),
            ("anemoi17-cico-n1-fcico", "99d6301147c1"),
            ("anemoi17-cico-n1-pcico", "e1d49467499d"),
            ("anemoi17-cico-n2-fcico", "25033fe92545"),
            ("anemoi17-cico-n2-pcico", "a141ec7980da"),
            ("anemoi17-cico-n3-fcico", "4a68dbe1e5ca"),
            ("anemoi17-cico-n3-pcico", "6001cba36737"),
            ("anemoi17-cico-n4-fcico", "518762ead134"),
            ("anemoi17-cico-n4-pcico", "5a8388253ebf"),
            ("anemoi17-cico-n5-fcico", "f7cf58903c69"),
            ("anemoi17-cico-n5-pcico", "204e51b602ae"),
            ("anemoi17-cico-n6-fcico", "db25820df213"),
            ("anemoi17-cico-n6-pcico", "35142599ae39"),
            ("fukuoka-mq-III-n10-seed0", "ae24edf8efc8"),
            ("fukuoka-mq-III-n15-seed0", "0552d3b51070"),
            ("fukuoka-mq-III-n20-seed0", "434135c809f6"),
            ("fukuoka-mq-VI-n10-seed0", "2558f4bccd7d"),
            ("fukuoka-mq-VI-n15-seed0", "0345980a26d8"),
            // #501 redefined this row: it was ("fukuoka-mq-III-n55-seed0", "f3ac89821637") at a
            // size type III does not publish. Corrected in place rather than appended, because
            // nothing was ever measured against the old id — its checksum was empty and
            // `dispatch` had no arm at 55 — so there is no history keyed on the old digest.
            ("fukuoka-mq-III-n34-seed0", "9c2033d49ecb"),
            // #454. Appended, so the six frozen digests above keep both their order and their
            // values — and they did: notes and reference points are paperwork, not identity.
            ("fukuoka-mq-VI-n24-seed0", "e97e852ee8f0"),
            // #510. Appended for the same reason, and the digest it would have had under the
            // hardcoded "GF(31)" is not this one: the field is in the identity.
            ("fukuoka-mq-V-n24-seed0", "540475b13ba8"),
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
        // public solution was recorded", and it still says it is not a priority claim. This was
        // the MQ gap row until #501 found that the size it named does not exist and the size it
        // meant is solved; an unsolved tier of the 2025 Poseidon program is the honest stand-in.
        let open = challenge("poseidon256-cico-2025-rf6-rp11").expect("registered");
        assert_eq!(
            open.significance(true),
            Significance::NoPublicSolutionRecorded {
                as_of: "2026-11-08"
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

    /// A registered problem this crate cannot generate is refused, not approximated.
    ///
    /// The 2025 program constrains the **trailing** words, and `CicoInstance` constrains the
    /// leading ones. Building one as the other would produce a different problem wearing this
    /// row's identity — the constrained positions interact with the MDS layer differently — and
    /// nothing about the result would look wrong. So both paths refuse by name.
    #[test]
    fn test_an_objective_this_crate_cannot_generate_is_refused() {
        struct Nothing;
        impl CicoVisitor<K> for Nothing {
            type Output = ();
            fn visit<const N: usize>(self, _: &[MultivariatePolynomial<N, K>]) {}
        }

        let rows: Vec<ChallengeManifest> = registry()
            .into_iter()
            .filter(|c| c.objective == Objective::CicoExactTrailing)
            .collect();
        assert_eq!(rows.len(), 3, "the three unsolved 2025 tiers");

        for row in rows {
            assert!(
                row.cico_instance::<K>().is_err(),
                "{} must not be built as the leading-constraint objective",
                row.id
            );
            assert_eq!(
                dispatch_cico::<K, _>(&row, Nothing),
                Err(ChallengeError::UnsupportedObjective {
                    objective: "cico-exact-trailing"
                }),
                "{}",
                row.id
            );
            // And its size is still a fact about the problem, reported from the program's
            // parameters rather than from a system nobody can build.
            assert!(row.variables().expect("a size") > 0);
            // Every 2025 tier constrains one word at each end.
            let k = 1;
            assert_eq!(
                row.variables().expect("a size") - row.equations().expect("a size"),
                row.parameters_t() - 2 * k,
                "{}: N - E = t - 2k",
                row.id
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
            if manifest.id == "fukuoka-mq-III-n34-seed0" {
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

    /// Every signature row's shape is the one the generator computes, truncation included.
    ///
    /// `generateCoef_sig.h` assigns `m * 1.5` to an `int`, so `m = 17` is `n = 25` rather than 26.
    /// A row that wrote the rounded value, or that transposed `n` and `m`, would name an instance
    /// the challenge does not publish while still passing every other check here. Both signature
    /// families, because the generator is the same one: type V is the GF(2^8) half of it.
    #[test]
    fn test_the_signature_rows_use_the_generators_truncated_shape() {
        for manifest in registry() {
            let ChallengeParameters::MqSystem { kind, n, m, .. } = manifest.parameters else {
                continue;
            };
            if kind != "V" && kind != "VI" {
                continue;
            }
            assert_eq!(n, 3 * m / 2, "{} is not floor(3m/2)", manifest.id);
        }
    }

    /// Every type III row names a size the challenge actually publishes for type III.
    ///
    /// Type III publishes the toy examples `n = 10, 15, 20` and the real range `n = 34..=53`;
    /// `n = 55` is type I's lower bound, and a row there names an instance that does not exist
    /// (#501). The shape checks above cannot catch it: `m = 2n` holds at any `n`.
    #[test]
    fn test_the_type_iii_rows_name_published_sizes() {
        for manifest in registry() {
            let ChallengeParameters::MqSystem { kind, n, .. } = manifest.parameters else {
                continue;
            };
            if kind != "III" {
                continue;
            }
            assert!(
                matches!(n, 10 | 15 | 20 | 34..=53),
                "{} is at n = {}, which type III does not publish",
                manifest.id,
                n
            );
        }
    }

    /// Every MQ row names the field its own challenge type is published over.
    ///
    /// The field is in the identity digest, and it was written `"GF(31)"` at every call site while
    /// the registry held only types III and VI — so the first GF(2^8) row would have been a
    /// GF(31) row that happened to carry type V's `kind` (#510). Types I and IV are GF(2) and
    /// types II and V are GF(2^8); the tuple in the loop is what decides, not the family.
    #[test]
    fn test_every_mq_row_names_its_types_field() {
        for manifest in registry() {
            let ChallengeParameters::MqSystem { field, kind, .. } = manifest.parameters else {
                continue;
            };
            let published = match kind {
                "I" | "IV" => "GF(2)",
                "II" | "V" => "GF(2^8)",
                "III" | "VI" => "GF(31)",
                other => panic!("{} is not a challenge type", other),
            };
            assert_eq!(field, published, "{} is type {}", manifest.id, kind);
        }
    }

    /// Both `n = 24` rows are registered: one per signature family, one per field.
    ///
    /// `m = 16` is `n = 24` in types V and VI alike, so the single compiled dimension serves two
    /// fields — and until #510 only the GF(31) half of it had a row, because the scoreboard could
    /// not run the other.
    #[test]
    fn test_both_signature_families_are_registered_at_the_smallest_real_size() {
        for (id, kind, field) in [
            ("fukuoka-mq-V-n24-seed0", "V", "GF(2^8)"),
            ("fukuoka-mq-VI-n24-seed0", "VI", "GF(31)"),
        ] {
            let row = challenge(id).unwrap_or_else(|| panic!("{} is registered", id));
            assert_eq!(row.class, BenchmarkClass::Official);
            assert_eq!(row.objective, Objective::MqRoot);
            let ChallengeParameters::MqSystem {
                field: recorded,
                kind: recorded_kind,
                n,
                m,
                sha256,
                ..
            } = row.parameters
            else {
                panic!("{} is an MQ row", id)
            };
            assert_eq!((recorded, recorded_kind, n, m), (field, kind, 24, 16));
            assert_eq!(sha256.len(), 64, "{} names real challenge bytes", id);
            assert!(
                matches!(row.external, ExternalStatus::SolvedExternally { .. }),
                "{}: the hall of fame records m = 16 seed 0 in both families",
                id
            );
            assert!(
                crate::grobner::research::SUPPORTED_DIMENSIONS.contains(&n),
                "{} names a dimension dispatch cannot reach",
                id
            );
        }
    }

    /// The `n = 24` row is a real challenge instance, importable, and a reproduction if solved.
    ///
    /// Type VI at `m = 16` is the smallest published instance in any type this crate can import,
    /// and the row only means anything if `dispatch` actually reaches its dimension — the two were
    /// out of step for as long as `SUPPORTED_DIMENSIONS` stopped at 20 (#454).
    #[test]
    fn test_the_smallest_real_challenge_row_is_importable() {
        let row = challenge("fukuoka-mq-VI-n24-seed0").expect("registered");
        let ChallengeParameters::MqSystem {
            kind, n, m, sha256, ..
        } = row.parameters
        else {
            panic!("an MQ row");
        };
        assert_eq!((kind, n, m), ("VI", 24, 16));
        assert_eq!(sha256.len(), 64, "the fetched file's bytes are named");
        assert!(
            SUPPORTED_DIMENSIONS.contains(&n),
            "registered at a dimension dispatch cannot reach"
        );
        // Faugère solved this instance in 2015, so a witness here reproduces rather than opens.
        assert_eq!(
            row.significance(true),
            Significance::Reproduction {
                externally_verified: "2015-04-01"
            }
        );
        assert_eq!(row.reference_points.len(), 1, "the published comparand");
    }

    /// `FCICO` and `PCICO` at the same round count have **different** identities.
    ///
    /// The whole reason the model is a parameter. Ten generators of degree three and six of
    /// degrees up to ten are two problems a solver meets completely differently; if the digest did
    /// not separate them, a comparison tool keyed on it would compare them and say nothing was
    /// wrong.
    #[test]
    fn test_the_two_anemoi_models_are_different_problems() {
        for rounds in 1..=5 {
            let f = challenge(&format!("anemoi64-cico-n{rounds}-fcico")).expect("registered");
            let p = challenge(&format!("anemoi64-cico-n{rounds}-pcico")).expect("registered");
            assert_ne!(
                f.digest(),
                p.digest(),
                "N = {rounds}: the model is not in the identity"
            );
            // And the canonical form says which, in a line a reader can check by hand.
            assert!(
                f.canonical().contains("\nmodel fcico\n"),
                "{}",
                f.canonical()
            );
            assert!(
                p.canonical().contains("\nmodel pcico\n"),
                "{}",
                p.canonical()
            );
            // The same primitive, though: everything but the model agrees.
            let ChallengeParameters::AnemoiCico {
                prime, alpha, l, ..
            } = f.parameters
            else {
                panic!("an Anemoi row");
            };
            assert_eq!((prime, alpha, l), (super::ANEMOI_64_PRIME, 3, 1));
        }
    }

    /// Changing a reference point does not change a problem's identity.
    ///
    /// A published figure is paperwork in exactly the sense a bounty is: a corrected extrapolation,
    /// a re-read log or a second publication at the same parameters must not change which
    /// mathematical problem a row names, or every historical comparison keyed on the digest breaks.
    #[test]
    fn test_a_reference_point_does_not_change_identity() {
        let original = challenge("anemoi64-cico-n5-fcico").expect("registered");
        let expected = original.digest();
        assert_eq!(
            original.reference_points.len(),
            2,
            "F4 and FGLM, separately"
        );

        for points in [
            &[][..],
            &[ReferencePoint {
                source: "somewhere else entirely",
                parameters: "different parameters",
                step: "the whole solve",
                reported_time: "no time at all",
                reported_memory: Some("no memory at all"),
                hardware: "a different machine",
                software: "different software",
            }][..],
        ] {
            let mut altered = original.clone();
            altered.reference_points = points;
            assert_eq!(
                altered.digest(),
                expected,
                "a published cost figure changed the identity"
            );
        }
    }

    /// Every Anemoi row carries the published `F4` and `FGLM` figures separately, with its machine.
    ///
    /// Separately on purpose: the finding this family was chosen for is that the two are 2 400x
    /// apart at `N = 5`, which a single combined figure would hide. And every figure names its
    /// hardware, because a time without its machine is not comparable to anything.
    #[test]
    fn test_the_anemoi_rows_carry_their_published_figures() {
        let rows: Vec<ChallengeManifest> = registry()
            .into_iter()
            .filter(|c| c.parameters.family() == "anemoi-cico")
            .collect();
        assert_eq!(rows.len(), 36, "N = 1..6 in both models at three primes");

        for row in &rows {
            assert_eq!(row.reference_points.len(), 2, "{}", row.id);
            assert!(row.reference_points[0].step.contains("basis"), "{}", row.id);
            assert_eq!(row.reference_points[1].step, "FGLM order change");
            for point in row.reference_points {
                assert!(point.hardware.contains("Xeon E5-2630 v3"), "{}", row.id);
                assert_eq!(point.software, "Magma V2.26-2");
                // The logs report peak resident for a whole sweep, so no row claims a memory
                // figure. A fabricated one is the failure this asserts against.
                assert_eq!(point.reported_memory, None, "{}", row.id);
            }
        }

        // The row the family was chosen for: 9.32 s of basis against 22 057 s of conversion.
        let wall = challenge("anemoi64-cico-n5-fcico").expect("registered");
        assert_eq!(wall.reference_points[0].reported_time, "9.320 s");
        assert_eq!(wall.reference_points[1].reported_time, "22057.080 s");

        // And the row that says what that 22 057 s is: the same system, the same machine, the same
        // Magma, one round count, 17 bits of characteristic instead of 64 — 135.6 s. Within the
        // reference the conversion step is 163x cheaper at the small prime while its basis step is
        // only 8.6x cheaper, which is what #283's attribution rests on.
        let control = challenge("anemoi17-cico-n5-fcico").expect("registered");
        assert_eq!(control.reference_points[0].reported_time, "1.089 s");
        assert_eq!(control.reference_points[1].reported_time, "135.640 s");

        // A step the sweep did not run is prose rather than a quantity, so a tool that parses
        // reported_time as a time cannot read it as zero.
        let stopped = challenge("anemoi32-cico-n5-pcico").expect("registered");
        assert_eq!(stopped.reference_points[0].reported_time, "3.579 s");
        assert_eq!(
            stopped.reference_points[1].reported_time,
            super::NOT_REPORTED
        );
        assert!(stopped.reference_points[1]
            .reported_time
            .parse::<f64>()
            .is_err());
    }

    /// Every Anemoi row builds, has the published size, and both models vanish at a trace.
    ///
    /// Over the field each row's own parameters name, which since #283 is three different types.
    /// `anemoi_cico_instance` refuses a mismatch, so a row checked against the wrong field would
    /// not be checked weakly — it would not build at all.
    #[test]
    fn test_every_anemoi_row_builds_and_is_faithful() {
        struct Faithful<'a, F: KnownOrder>(&'a AnemoiCico<F>, F);
        impl<F: KnownOrder> AnemoiCicoVisitor<F> for Faithful<'_, F> {
            type Output = Vec<usize>;
            fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> Vec<usize> {
                verify_against_anemoi_trace(self.0, system, self.1)
            }
        }

        fn check<F: KnownOrder>(manifest: &ChallengeManifest) {
            let instance = manifest
                .anemoi_cico_instance::<F>()
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

            let rounds = manifest.anemoi_parameters().expect("an Anemoi row").rounds;
            let failures = dispatch_anemoi_cico::<F, _>(&instance, Faithful(&instance, F::new(31)))
                .expect("a compiled dimension");
            // Both models express the output CICO condition in generators that an arbitrary input
            // does not satisfy, and only those: FCICO folds it into its last round's two
            // equations, PCICO keeps it as one trailing constraint.
            let expected: Vec<usize> = match manifest.anemoi_model().expect("an Anemoi row") {
                AnemoiModel::Fcico => vec![2 * rounds - 2, 2 * rounds - 1],
                AnemoiModel::Pcico => vec![rounds],
            };
            assert_eq!(failures, expected, "{}", manifest.id);
        }

        let mut seen = 0;
        for manifest in registry() {
            let Some(parameters) = manifest.anemoi_parameters() else {
                continue;
            };
            match parameters.prime {
                super::ANEMOI_64_PRIME => check::<A>(&manifest),
                super::ANEMOI_32_PRIME => check::<A32>(&manifest),
                super::ANEMOI_17_PRIME => check::<A17>(&manifest),
                prime => panic!("{} is over an unhandled prime {prime}", manifest.id),
            }
            seen += 1;
        }
        assert_eq!(seen, 36, "every registered Anemoi row was checked");
    }

    /// An Anemoi row is refused by the Poseidon dispatcher, and told apart from a non-CICO row.
    ///
    /// An Anemoi row *is* a CICO problem, so reporting it as "not a CICO problem" would be false.
    #[test]
    fn test_an_anemoi_row_is_refused_by_the_poseidon_dispatcher() {
        struct Nothing;
        impl CicoVisitor<K> for Nothing {
            type Output = ();
            fn visit<const N: usize>(self, _: &[MultivariatePolynomial<N, K>]) {}
        }
        let row = challenge("anemoi64-cico-n3-fcico").expect("registered");
        assert_eq!(
            dispatch_cico::<K, _>(&row, Nothing),
            Err(ChallengeError::OtherCicoFamily {
                family: "anemoi-cico"
            })
        );
        assert!(row.cico_instance::<K>().is_err(), "nor as a Poseidon one");
        // And a Poseidon row is not an Anemoi one.
        assert!(challenge("poseidon31-cico-rf6-rp8")
            .expect("registered")
            .anemoi_cico_instance::<A>()
            .is_err());
    }

    /// A witness on an Anemoi row is a reproduction of a published result, not a first solution.
    #[test]
    fn test_an_anemoi_witness_is_a_reproduction() {
        let row = challenge("anemoi64-cico-n5-pcico").expect("registered");
        assert_eq!(row.class, BenchmarkClass::Official);
        assert_eq!(row.external, ExternalStatus::PublishedWithAnswer);
        assert_eq!(
            row.significance(true),
            Significance::Reproduction {
                externally_verified: "publication"
            }
        );
        assert_eq!(row.significance(false), Significance::NoWitness);
        // The caveat FaithfulReduction would have carried structurally is carried in the notes.
        assert!(row.notes.contains("says nothing about full-round Anemoi"));
    }

    /// The Anemoi derived constants are pinned, so a changed generator cannot pass as the same row.
    ///
    /// The Anemoi counterpart of `test_the_derived_constants_are_pinned`, and it carries more
    /// weight: Poseidon's constants come out of a seeded LFSR this crate controls, while Anemoi's
    /// depend on `g`, which the specification does not fix. Two rows at the same round count share
    /// a digest because they share a permutation — the model is not a property of the constants.
    #[test]
    fn test_the_anemoi_derived_constants_are_pinned() {
        for (id, digest) in [
            ("anemoi64-cico-n1-fcico", "3f2d4387eb09c4a9"),
            ("anemoi64-cico-n3-pcico", "d8c8c56669d10e61"),
            ("anemoi64-cico-n5-fcico", "2273108e11bbbeae"),
            ("anemoi64-cico-n5-pcico", "2273108e11bbbeae"),
        ] {
            let manifest = challenge(id).expect("registered");
            assert_eq!(
                manifest.anemoi_derived_digest::<A>().expect("builds"),
                digest,
                "{}'s derived constants changed",
                id
            );
        }
        // A Poseidon row has no Anemoi constants to digest.
        assert!(challenge("poseidon31-cico-rf6-rp8")
            .expect("registered")
            .anemoi_derived_digest::<A>()
            .is_err());
    }

    /// The published quotient dimension is `(alpha + 2)^N`, tagged as an observation.
    ///
    /// `Claim::Observed` and not `Claim::Proved`: the Six Worlds figures are measurements from one
    /// implementation, and the designers' corresponding statement is a conjecture. The distinction
    /// is the one `manifest::Claim` exists for.
    #[test]
    fn test_the_published_quotient_dimension_is_an_observation() {
        for (rounds, expected) in [(1, 5u128), (2, 25), (3, 125), (4, 625), (5, 3125)] {
            let claim = published_quotient_dimension(3, rounds);
            assert_eq!(*claim.value(), expected, "N = {rounds}");
            assert!(!claim.is_proved(), "N = {rounds} is measured, not proved");
        }
        // The other exponents the same logs cover, for the same reason.
        assert_eq!(*published_quotient_dimension(5, 4).value(), 2401);
        assert_eq!(*published_quotient_dimension(11, 3).value(), 2197);
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
