//! The cross-library corpus: the same ideal, named the same way, for every engine.
//!
//! A cross-library comparison is meaningful only on **the same mathematical input**, and the two
//! families everyone benchmarks on both have a naming hazard that produces a different ideal
//! without producing an error. Both are resolved here by construction rather than by convention,
//! and the resolutions are pinned by tests against another engine's own distributed input files.
//!
//! # Hazard 1: Katsura indexing
//!
//! The literature's "Katsura-n" has **n + 1 variables** `u_0 … u_n`, so the name and the variable
//! count differ by one — and benchmark suites split on which number they use. Zeebra's
//! [`katsura`](crate::grobner::benchmark_systems::katsura) is const-generic in the **variable
//! count**: `katsura::<6>` is six variables, which the literature calls Katsura-5.
//!
//! **Resolved empirically.** msolve's distributed `input_files/kat6-31.ms` declares six variables
//! `x1 … x6` and six equations, and is `katsura::<6>` generator for generator —
//! `test_katsura_6_is_msolves_kat6` pins it against msolve's own literal. So msolve names by
//! variable count and agrees with Zeebra's type parameter. **Every instance here is therefore
//! named by variable count**, and the literature's `n` appears nowhere: an instance called
//! `katsura-6` has six variables in every engine, and the digest is the real arbiter either way.
//!
//! # Hazard 2: affine versus homogenized Cyclic
//!
//! The cyclic-n roots system comes in two forms. The **affine** one closes with
//! `x_1 ⋯ x_n − 1`, which is inhomogeneous and zero-dimensional for squarefree n. The
//! **homogenized** one replaces that with `x_1 ⋯ x_n − h^n` in n + 1 variables, or drops the
//! constant entirely; it is positive-dimensional, its Gröbner basis is a different object, and its
//! cost is not comparable. Benchmark tables rarely say which they used.
//!
//! **Resolved empirically.** msolve's `input_files/cyclic5-16.ms` is the affine form, identical to
//! [`cyclic`](crate::grobner::benchmark_systems::cyclic)`::<5>`, pinned by
//! `test_cyclic_5_is_msolves_cyclic5`. The corpus is affine throughout. A homogenized instance
//! would be a **different problem** with a different digest, and
//! [`Instance::transformation`](super::Instance) is where that would be recorded.
//!
//! # Not every square system is zero-dimensional
//!
//! `cyclic::<4>` is **positive-dimensional** — its grevlex leading-term ideal contains no power of
//! the last variable. It is in the corpus deliberately, as the easy rung that exercises the
//! positive-dimensional path, and its entry says so. A task like
//! [`Task::LexBasisByConversion`](super::Task) does not apply to it, which is a fact about the
//! ideal and not a failure of any engine.
//!
//! # Hazard 3: a declared field that was not the generated one
//!
//! An instance carries a [`FieldSpec`] and a system, and nothing in the text ties them together:
//! coefficients render as **residues**, so `−1` over `2^31 − 1` is the numeral `2147483646`, which
//! is a perfectly well-formed element of a smaller prime field and a different one. A
//! `characteristic` that reached only the label therefore produced a valid input file describing a
//! different ideal from the one named, with a digest and a name both claiming otherwise (#425).
//!
//! **Resolved by construction.** The const-generic families are generated over the declared field
//! via `over_prime!`, whose arms are [`GENERATED_CHARACTERISTICS`]; a prime with no compiled field
//! yields `None`. `test_every_rendered_coefficient_is_a_residue_of_the_declared_characteristic` is
//! the property, asserted on the rendered text rather than on the polynomials.
//!
//! # The ladder
//!
//! Rungs are chosen to be easy, intermediate and genuinely challenging rather than uniformly
//! large: a family represented only by instances every engine times out on measures nothing, and a
//! family represented only by instances every engine finishes in a millisecond measures startup
//! cost. [`ladder`] is that selection, and [`manifest`] freezes each rung's digest.

use crate::{
    fields::PrimeFieldElement64,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        differential::{polynomial_to_string, GeneratedSystem, SystemShape},
        research::{
            challenge, dispatch_anemoi_cico, dispatch_cico, AnemoiCicoVisitor, CicoVisitor,
            ANEMOI_64_PRIME, KOALABEAR_PRIME,
        },
    },
    FiniteField, KnownOrder, MonomialOrder, MultivariatePolynomial,
};

use super::{FieldSpec, Instance};

/// The corpus's reference characteristic.
///
/// `2^31 − 1`, chosen because **every engine in the comparison accepts it**: Singular and msolve
/// both stop below `2^31`, so a corpus keyed on a wider prime would make most of the table
/// `Unsupported` and measure nothing. Zeebra's own behaviour at Goldilocks and above is covered by
/// its cryptanalysis scoreboard, where there is no comparand to lose.
pub const REFERENCE_CHARACTERISTIC: u64 = 2_147_483_647;

/// A second prime the const-generic families are compiled over: `2^30 + 3`.
///
/// **Not a second corpus identity.** The manifest, every frozen digest and every published row
/// remain at [`REFERENCE_CHARACTERISTIC`].
///
/// This prime rather than an arbitrary one for two independent reasons. It is the characteristic
/// msolve's own distributed `input_files/kat6-31.ms` declares, so it is the field the Katsura
/// equivalence evidence was shipped over. And it is **below**
/// [`ceilings::MSOLVE_ELIMINANT`](ceilings::MSOLVE_ELIMINANT) where the reference prime is above
/// it, which is why `msolve.rs`'s eliminant tests ask the corpus for rungs here — those tests were
/// the live victims of this label-only `characteristic`, having been handed systems reduced mod
/// `2^31 − 1` and declared mod this prime.
pub const ALTERNATE_CHARACTERISTIC: u64 = 1_073_741_827;

/// The primes the const-generic families have a compiled field for.
///
/// Katsura, Cyclic and planted MQ are const-generic in the field, so a prime known only at run
/// time cannot be turned into a type and the compiled instantiations **are** the available primes.
/// [`instance`] returns `None` outside this list rather than generating over the reference prime
/// and labelling the result with the prime that was asked for.
///
/// Random MQ is not listed here because it does not need to be: its generator reduces at run time
/// through [`CaseField`](crate::grobner::differential::CaseField), so every prime is available to
/// it. Poseidon and Anemoi carry the registry's own field and ignore the argument entirely.
pub const GENERATED_CHARACTERISTICS: [u64; 2] =
    [ALTERNATE_CHARACTERISTIC, REFERENCE_CHARACTERISTIC];

/// Run `$body` with `$field` bound to the compiled field for `$characteristic`, or yield `None`.
///
/// The families are const-generic in the field, so a prime known only at run time cannot be turned
/// into a type: the match below is what picks the instantiation, and its arms are exactly
/// [`GENERATED_CHARACTERISTICS`] — `test_every_compiled_characteristic_builds_every_rung` pins the
/// two together.
///
/// **Why a dispatch and not a characteristic-independent renderer.** Coefficients could be rendered
/// from signed integers instead, which would make these families' text the same at every prime —
/// and would change every frozen digest in [`ladder`], retroactively making every published figure
/// a figure about a differently-identified problem. Generating over the declared field leaves the
/// reference-prime text byte-identical.
macro_rules! over_prime {
    ($characteristic:expr, |$field:ident| $body:block) => {
        match $characteristic {
            ALTERNATE_CHARACTERISTIC => {
                type $field = PrimeFieldElement64<ALTERNATE_CHARACTERISTIC>;
                Some($body)
            }
            REFERENCE_CHARACTERISTIC => {
                type $field = PrimeFieldElement64<REFERENCE_CHARACTERISTIC>;
                Some($body)
            }
            _ => None,
        }
    };
}

/// How hard a rung is meant to be.
///
/// A judgement about the rung's role in the ladder, not a measurement. The point of recording it
/// is that a table whose every row is one difficulty says less than its row count suggests.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Rung {
    /// Finishes everywhere in well under a second. Exercises the path, not the engine.
    Easy,

    /// Seconds to a minute somewhere in the comparison. Where the engines separate.
    Intermediate,

    /// Expected to exhaust at least one engine's limits. The interesting end, and the one that
    /// needs `StoppedByLimit` to be a first-class outcome.
    Challenging,
}

impl Rung {
    /// The stable tag used in the manifest.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::Easy => "easy",
            Self::Intermediate => "intermediate",
            Self::Challenging => "challenging",
        }
    }
}

/// One corpus instance: what it is, how hard, and what its identity is.
#[derive(Clone, Debug)]
pub struct CorpusEntry {
    /// The instance name. **Named by variable count**, never by the literature's family index.
    pub name: &'static str,

    /// The family, for grouping.
    pub family: &'static str,

    /// Where it sits on the ladder.
    pub rung: Rung,

    /// Whether the ideal is zero-dimensional.
    ///
    /// `false` is not a defect: `cyclic-4` is genuinely positive-dimensional, and a task that
    /// needs a finite quotient does not apply to it.
    pub zero_dimensional: bool,

    /// How this family's ideal equivalence was established. **The gate on publishing a timing.**
    pub equivalence: Equivalence,

    /// The frozen identity digest at [`REFERENCE_CHARACTERISTIC`] under grevlex.
    ///
    /// Pinned by `test_the_manifest_is_frozen`. A change here means the generated system changed,
    /// which means every figure taken against the old digest is a figure about a different
    /// problem — so the test failing is the point of the field.
    pub digest: &'static str,
}

/// Build one corpus instance by name, at `characteristic`, under `order`.
///
/// # Errors
/// `None` for a name not in [`ladder`], for a name whose variable count has no compiled
/// instantiation, or — for the const-generic families — for a characteristic outside
/// [`GENERATED_CHARACTERISTICS`]. The families are const-generic in both the size and the field, so
/// the available sizes are exactly those listed here — adding a rung means adding a match arm,
/// which is deliberate: a size nobody wrote down is a size nobody checked the equivalence of.
pub fn instance(name: &str, characteristic: u64, order: MonomialOrder) -> Option<Instance> {
    match name {
        "katsura-4" => katsura_instance::<4>(characteristic, order),
        "katsura-5" => katsura_instance::<5>(characteristic, order),
        "katsura-6" => katsura_instance::<6>(characteristic, order),
        "katsura-7" => katsura_instance::<7>(characteristic, order),
        "cyclic-4" => cyclic_instance::<4>(characteristic, order),
        "cyclic-5" => cyclic_instance::<5>(characteristic, order),
        "cyclic-6" => cyclic_instance::<6>(characteristic, order),
        // Seeds are part of the name, so a rung is reproducible from the name alone.
        "mq-random-6" => Some(random_mq_instance(6, 6, characteristic, order)),
        "mq-random-10" => Some(random_mq_instance(10, 10, characteristic, order)),
        "mq-random-14" => Some(random_mq_instance(14, 14, characteristic, order)),
        "mq-planted-6" => planted_mq_instance::<6>(characteristic, order),
        "mq-planted-10" => planted_mq_instance::<10>(characteristic, order),
        "mq-planted-14" => planted_mq_instance::<14>(characteristic, order),
        // Poseidon and Anemoi carry the registry's own field, not `characteristic`: their round
        // constants are derived from the prime, so the same row over another prime is another
        // problem. The argument is unused for them by design, and the digest records the field
        // that was actually used.
        "poseidon-t2-rf2-rp0-planted"
        | "poseidon-t2-rf2-rp2-planted"
        | "poseidon-t2-rf4-rp0-planted" => poseidon_instance(name, order),
        "anemoi64-cico-n1-fcico" | "anemoi64-cico-n2-fcico" => anemoi_instance(name, order),
        _ => None,
    }
}

/// The Katsura instance in `N` variables — the literature's Katsura-`(N-1)`.
///
/// # Errors
/// `None` for a characteristic outside [`GENERATED_CHARACTERISTICS`]. The system is generated over
/// the declared field, so a prime with no compiled instantiation has no instance rather than a
/// mislabeled one.
pub fn katsura_instance<const N: usize>(
    characteristic: u64,
    order: MonomialOrder,
) -> Option<Instance> {
    over_prime!(characteristic, |F| {
        text_instance(
            format!("katsura-{}", N),
            "katsura",
            &katsura::<N, F>(),
            characteristic,
            order,
        )
    })
}

/// The affine cyclic-`N` roots instance in `N` variables.
///
/// # Errors
/// As [`katsura_instance`].
pub fn cyclic_instance<const N: usize>(
    characteristic: u64,
    order: MonomialOrder,
) -> Option<Instance> {
    over_prime!(characteristic, |F| {
        text_instance(
            format!("cyclic-{}", N),
            "cyclic",
            &cyclic::<N, F>(),
            characteristic,
            order,
        )
    })
}

/// Render a system to the text form every engine parses, and wrap it as an [`Instance`].
///
/// Variables are `x1 … xN`, which is what msolve's and Singular's own files use, and the order they
/// are declared in **is** the monomial order's variable order. `characteristic` must be `F`'s, which
/// is why every caller goes through [`over_prime`] rather than passing the two independently.
fn text_instance<const N: usize, F: FiniteField>(
    name: String,
    family: &str,
    system: &[MultivariatePolynomial<N, F>],
    characteristic: u64,
    order: MonomialOrder,
) -> Instance {
    let names: Vec<String> = (1..=N).map(|i| format!("x{}", i)).collect();
    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let generators: Vec<String> = system
        .iter()
        .map(|polynomial| polynomial_to_string(polynomial, &refs, order))
        .collect();
    Instance::new(
        name,
        family,
        FieldSpec::prime(characteristic),
        names,
        generators,
        order,
    )
}

/// How a family's ideal equivalence was established.
///
/// **The gate on publishing a timing.** A family with no evidence here may appear in the corpus —
/// several must, since the gap is itself a result — but no cross-library figure may be quoted for
/// it. Recorded per family rather than per rung because the evidence is about the *construction*,
/// which every rung of a family shares.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Equivalence {
    /// Agrees with a comparand's own distributed input file, generator for generator.
    ///
    /// The strongest form, because it compares against bytes somebody else shipped rather than
    /// against this crate's reading of a paper. Katsura and Cyclic, against msolve 0.11.0's
    /// `input_files/`.
    ComparandFile {
        tool: &'static str,
        file: &'static str,
    },

    /// A **known solution** must satisfy the system as handed to every engine.
    ///
    /// Stronger than it sounds for cross-library purposes, and in one respect stronger than a
    /// digest: an engine whose parser read the text differently will not vanish at the point, and
    /// that is detectable without the engine computing anything. Planted MQ and the planted
    /// Poseidon rows.
    KnownSolution,

    /// Checked against live Singular's invariants, which needs an installation.
    ///
    /// For a family with neither a distributed file nor a known solution. The weakest of the three
    /// that still licenses a timing.
    LiveOracle { tool: &'static str },

    /// Exactly **one** external engine can represent the field, so nothing corroborates it.
    ///
    /// **The limit is corroboration, not representability**, and the distinction decides what to
    /// do about it: representability needs a *new* tool, corroboration needs a *second* tool at
    /// the same field. Agreement here is two-way, Zeebra against the one engine, and cannot be
    /// triangulated — so a disagreement says one of the two is wrong without saying which, where a
    /// three-way disagreement usually names the odd one out.
    ///
    /// A timing **is** publishable: the ratio is taken on one machine at one task under one limit,
    /// and the invariants can still be checked between the two engines. What is unavailable is
    /// independent confirmation that both are not wrong the same way. [`Self::is_corroborated`]
    /// is the check a renderer should mark the row on.
    SoleComparand {
        tool: &'static str,
        reason: &'static str,
    },

    /// No external engine can represent the field, so no cross-library check is possible at all.
    ///
    /// **Not a gap in the work**, and now a narrower claim than it was: it applies to Zeebra's
    /// 254/255-bit fields, where no surveyed engine reaches. No timing is publishable.
    NoComparand { reason: &'static str },
}

impl Equivalence {
    /// Whether a cross-library timing may be published for a family with this evidence.
    ///
    /// True for [`Self::SoleComparand`]: one engine at one field on one machine still gives a
    /// valid ratio and a checkable invariant. What it does not give is corroboration, which is
    /// [`Self::is_corroborated`]'s question and a separate one.
    pub fn licenses_timing(&self) -> bool {
        !matches!(self, Self::NoComparand { .. })
    }

    /// Whether a **third** opinion exists, so that a disagreement could name the odd one out.
    ///
    /// False for [`Self::SoleComparand`] and [`Self::NoComparand`]. A row that licenses a timing
    /// but is not corroborated is publishable **with the fact stated** — this is the method a
    /// renderer marks it on.
    pub fn is_corroborated(&self) -> bool {
        matches!(
            self,
            Self::ComparandFile { .. } | Self::KnownSolution | Self::LiveOracle { .. }
        )
    }

    /// The stable tag used in the manifest.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::ComparandFile { .. } => "comparand-file",
            Self::KnownSolution => "known-solution",
            Self::LiveOracle { .. } => "live-oracle",
            Self::SoleComparand { .. } => "sole-comparand",
            Self::NoComparand { .. } => "no-comparand",
        }
    }
}

/// The highest characteristic each surveyed engine accepts, each from the engine's own gate.
///
/// Named constants rather than prose because the **capability boundary is a general fact** and
/// every per-family statement about it should be a consequence of these four numbers rather than
/// an independent claim. [`corroboration`] is that consequence.
pub mod ceilings {
    /// msolve's prime-field bound for a basis, `iofiles.c:564`.
    pub use crate::grobner::external::msolve::MAX_CHARACTERISTIC as MSOLVE;

    /// msolve's **much lower** bound on the univariate eliminant, `linalg-fglm.c:38`. Above it the
    /// sparse-FGLM failure is laundered into a retry loop with no exit.
    pub use crate::grobner::external::msolve::MAX_CHARACTERISTIC_ELIMINANT as MSOLVE_ELIMINANT;

    /// Singular's prime-field bound, which is also its `fglm` bound.
    pub use crate::grobner::differential::MAX_CHARACTERISTIC as SINGULAR;

    /// Sagebrush's own gate at `lib.rs:1552`. Its *basis* bound — `fglm.rs:329` caps the FGLM
    /// route an eighth lower, which is moot while the driver exposes no FGLM at all.
    pub use crate::grobner::external::sagebrush::MAX_CHARACTERISTIC as SAGEBRUSH;

    /// Groebner.jl accepts `< typemax(UInt64)`, measured computing correctly at `2^31 - 1`,
    /// `2^32 - 5`, Goldilocks, `2^64 - 353` and `2^64 - 59`, with **no** task-specific ceiling.
    pub use crate::grobner::external::groebner_jl::MAX_CHARACTERISTIC as GROEBNER_JL;
}

/// How many **external** engines can check a result at `characteristic`.
///
/// The capability boundary, as a function rather than a table in a document. Derived entirely from
/// [`ceilings`], so a corrected ceiling corrects every statement that depends on it.
///
/// This is the fact that makes Anemoi's row a consequence rather than a special case: its field is
/// `2^64 - 353`, which only Groebner.jl reaches, so it has one engine and no corroborator — while
/// the band below `2^62` has two and the band below `2^31` has four.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Corroboration {
    /// Four engines. Only the basis task below `2^31` reaches this.
    FourWay,

    /// Three engines.
    ThreeWay,

    /// Two engines, **neither checkable against a third**.
    TwoWay,

    /// One engine. A timing is publishable; nothing corroborates it.
    SoleEngine,

    /// No surveyed engine performs this task at this field.
    None,
}

impl Corroboration {
    /// The band for a count of engines.
    pub fn from_engines(engines: usize) -> Self {
        match engines {
            0 => Self::None,
            1 => Self::SoleEngine,
            2 => Self::TwoWay,
            3 => Self::ThreeWay,
            _ => Self::FourWay,
        }
    }

    /// How many external engines perform the task at the field.
    pub fn engines(&self) -> usize {
        match self {
            Self::FourWay => 4,
            Self::ThreeWay => 3,
            Self::TwoWay => 2,
            Self::SoleEngine => 1,
            Self::None => 0,
        }
    }

    /// Whether a third opinion exists, so a disagreement could name the odd engine out.
    ///
    /// Two engines plus Zeebra is three implementations, but **two of them are the comparison**:
    /// a Zeebra-against-Groebner.jl disagreement at `2^40` can be adjudicated by Sagebrush, where
    /// at `2^63` it cannot be adjudicated at all.
    pub fn can_triangulate(&self) -> bool {
        self.engines() >= 2
    }
}

/// The highest characteristic at which `engine` performs `task`, or `None` if it has no route.
///
/// **Ceilings are task-specific, and the differences are large.** msolve's eliminant bound is
/// below a tenth of its basis bound; Sagebrush exposes no conversion route at all. Declaring only
/// a basis bound is what lets a sweep run a worker into its wall limit and record a limit stop
/// where the truth is a capability gap.
fn ceiling_for(engine: &str, task: super::Task) -> Option<u64> {
    use super::Task::*;
    match (engine, task) {
        // Basis routes: each engine's own prime-field bound.
        ("msolve", ReducedGrobnerBasis | LexBasis) => Some(ceilings::MSOLVE),
        ("singular", ReducedGrobnerBasis | LexBasis) => Some(ceilings::SINGULAR),
        ("sagebrush", ReducedGrobnerBasis | LexBasis) => Some(ceilings::SAGEBRUSH),
        ("groebner.jl", ReducedGrobnerBasis | LexBasis) => Some(ceilings::GROEBNER_JL),

        // Conversion. **Sagebrush is absent, not merely limited** — its driver exposes no FGLM,
        // so this is a missing task rather than a field ceiling.
        ("msolve", LexBasisByConversion) => Some(ceilings::MSOLVE),
        ("singular", LexBasisByConversion) => Some(ceilings::SINGULAR),
        ("groebner.jl", LexBasisByConversion) => Some(ceilings::GROEBNER_JL),

        // Eliminant: msolve's own far-lower bound.
        ("msolve", UnivariateEliminant) => Some(ceilings::MSOLVE_ELIMINANT),
        ("singular", UnivariateEliminant) => Some(ceilings::SINGULAR),
        ("groebner.jl", UnivariateEliminant) => Some(ceilings::GROEBNER_JL),

        // Nothing offers the solution tasks or the witness task at any field.
        _ => None,
    }
}

/// Every engine the corpus compares against.
pub const ENGINES: [&str; 4] = ["msolve", "singular", "sagebrush", "groebner.jl"];

/// The corroboration available for `task` at `characteristic`.
///
/// Task-aware, because the ceilings are. The case that matters most for #263: the **conversion**
/// task, where Zeebra's only measured cross-library deficit lies, has Sagebrush missing entirely
/// — so above `2^31` it has **one** corroborator where the basis task has two.
pub fn corroboration_for(task: super::Task, characteristic: u64) -> Corroboration {
    let engines = ENGINES
        .iter()
        .filter(|engine| ceiling_for(engine, task).is_some_and(|ceiling| characteristic < ceiling))
        .count();
    Corroboration::from_engines(engines)
}

/// The corroboration available at `characteristic` for a **basis**, the task every engine offers.
///
/// Shorthand for [`corroboration_for`] at [`Task::ReducedGrobnerBasis`](super::Task). Use the
/// task-aware form for anything else: a basis band over-states what is available for conversion.
pub fn corroboration(characteristic: u64) -> Corroboration {
    corroboration_for(super::Task::ReducedGrobnerBasis, characteristic)
}

/// The seeded point the planted family plants, and the planted Poseidon rows echo.
///
/// Derived from the instance's variable count by a fixed rule rather than drawn from an RNG, so
/// the corpus needs no seed to reproduce it and the digest is stable without one. Values are small
/// and non-zero, and distinct per coordinate so a system that confused two variables does not
/// accidentally still vanish.
fn planted_point<const N: usize, F: FiniteField>() -> [F; N] {
    let mut point = [F::zero(); N];
    for (i, slot) in point.iter_mut().enumerate() {
        *slot = F::new(3 + 2 * i as u64);
    }
    point
}

/// A seeded random multivariate-quadratic instance in `n` variables.
///
/// `GeneratedSystem` is the differential harness's generator: entirely determined by the seed, the
/// shape and the field, and it **round-trips through text**, which is what makes it usable as a
/// cross-library instance at all. `max_degree: 2` is what makes it MQ.
pub fn random_mq_instance(
    n: usize,
    seed: u64,
    characteristic: u64,
    order: MonomialOrder,
) -> Instance {
    let shape = SystemShape {
        variables: n,
        max_degree: 2,
        // Dense enough that the quadratic part matters, bounded so the text stays readable and the
        // generated system does not become an accidental linear system after cancellation.
        max_terms: 4 * n,
    };
    let generated = GeneratedSystem::generate(
        seed,
        shape,
        crate::grobner::differential::CaseField::prime(characteristic),
    );
    Instance::new(
        format!("mq-random-{}", n),
        "mq-random",
        FieldSpec::prime(characteristic),
        generated.variables.clone(),
        generated.render(),
        order,
    )
    .transformed(format!(
        "seeded generation: seed {}, max_degree 2, max_terms {}",
        seed, shape.max_terms
    ))
}

/// A planted multivariate-quadratic instance in `N` variables, with a known solution.
///
/// Zero-dimensional by construction and the planted point is among the solutions, so **every
/// engine must find it** — an oracle no digest provides. See
/// [`planted`](crate::grobner::benchmark_systems::planted) on why the equations are nonlinear: a
/// system of `x_i - a_i` is already a Gröbner basis under every order and measures nothing.
/// # Errors
/// As [`katsura_instance`].
pub fn planted_mq_instance<const N: usize>(
    characteristic: u64,
    order: MonomialOrder,
) -> Option<Instance> {
    over_prime!(characteristic, |F| {
        let point = planted_point::<N, F>();
        text_instance(
            format!("mq-planted-{}", N),
            "mq-planted",
            &planted::<N, F>(&point),
            characteristic,
            order,
        )
        .transformed("planted at (3, 5, 7, ...), one value per variable".to_string())
    })
}

/// Render a const-generic system at an unknown dimension to `(variables, generators)`.
///
/// The visitor both CICO dispatchers want. `self` is consumed, so the order is carried in.
struct AsText {
    order: MonomialOrder,
}

impl AsText {
    fn render<const N: usize, F: FiniteField>(
        &self,
        system: &[MultivariatePolynomial<N, F>],
    ) -> (Vec<String>, Vec<String>) {
        let names: Vec<String> = (1..=N).map(|i| format!("x{}", i)).collect();
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        let generators = system
            .iter()
            .map(|polynomial| polynomial_to_string(polynomial, &refs, self.order))
            .collect();
        (names, generators)
    }
}

impl<F: KnownOrder> CicoVisitor<F> for AsText {
    type Output = (Vec<String>, Vec<String>);

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> Self::Output {
        self.render(system)
    }
}

impl<F: KnownOrder> AnemoiCicoVisitor<F> for AsText {
    type Output = (Vec<String>, Vec<String>);

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> Self::Output {
        self.render(system)
    }
}

/// A registered Poseidon CICO instance, as a corpus instance.
///
/// **The field is the registry's, not the corpus's.** Poseidon's round constants come out of a
/// seeded LFSR keyed on the prime, so a Poseidon system over a different prime is a different
/// problem — the characteristic cannot be varied the way it can for Katsura. KoalaBear
/// (`2^31 - 2^24 + 1 = 2130706433`) happens to be **below every comparand's ceiling**, so these
/// rows are comparable; that is luck rather than design, and it does not extend to Anemoi.
///
/// # Errors
/// `None` if `id` is not a registered Poseidon CICO row, or is at a dimension the dispatcher does
/// not compile.
pub fn poseidon_instance(id: &str, order: MonomialOrder) -> Option<Instance> {
    type K = PrimeFieldElement64<KOALABEAR_PRIME>;
    let manifest = challenge(id)?;
    let (variables, generators) = dispatch_cico::<K, _>(&manifest, AsText { order }).ok()?;
    Some(
        Instance::new(
            id.to_string(),
            "poseidon",
            FieldSpec::prime(KOALABEAR_PRIME).named("KoalaBear"),
            variables,
            generators,
            order,
        )
        .transformed(format!(
            "CICO constraints from registry row {} (digest {})",
            id,
            manifest.short_digest()
        )),
    )
}

/// A registered Anemoi CICO instance, as a corpus instance.
///
/// Over `2^64 - 353`. **Groebner.jl reaches this field** — its ceiling is `typemax(UInt64)` and it
/// was measured computing correctly at this prime — so the family is representable, and the limit
/// is **corroboration**: Sagebrush stops at `2^62` and msolve and Singular at `2^31`, leaving one
/// external engine and nothing to check it against. [`Equivalence::SoleComparand`] records that,
/// and [`corroboration`] derives it from the engine ceilings rather than asserting it here.
///
/// A timing is therefore publishable **with the fact stated**, which is a different disposition
/// from the 254/255-bit fields, where no engine reaches at all.
///
/// # Errors
/// `None` if `id` is not a registered Anemoi CICO row, or is at a dimension the dispatcher does
/// not compile.
pub fn anemoi_instance(id: &str, order: MonomialOrder) -> Option<Instance> {
    type A = PrimeFieldElement64<ANEMOI_64_PRIME>;
    let manifest = challenge(id)?;
    let instance = manifest.anemoi_cico_instance::<A>().ok()?;
    let (variables, generators) = dispatch_anemoi_cico::<A, _>(&instance, AsText { order }).ok()?;
    Some(
        Instance::new(
            id.to_string(),
            "anemoi",
            FieldSpec::prime(ANEMOI_64_PRIME).named("2^64 - 353"),
            variables,
            generators,
            order,
        )
        .transformed(format!(
            "CICO constraints from registry row {} (digest {})",
            id,
            manifest.short_digest()
        )),
    )
}

/// The corpus ladder: every rung, with its frozen digest.
///
/// A constant function rather than a data file, for the same reason
/// [`research::registry`](crate::grobner::research::registry) is one: the systems are generated by
/// code, so the authority on what they are is the code, and the digests here are the pin that says
/// the code has not changed under the figures.
///
/// **Katsura and Cyclic only, for now.** Poseidon and Anemoi instances already exist in the
/// cryptanalysis registry and need a conversion to this `Instance` form; Fukuoka MQ instances are
/// not redistributable and must be referenced from `ZEEBRA_MQ_DIR` rather than generated;
/// characteristic-two workloads need the extension-field convention settled first, since two
/// engines' default `GF(2^8)` need not be the same ring. Each is listed in
/// `docs/research/cross-library-corpus.md` with what remains to do, rather than half-added here.
pub fn ladder() -> Vec<CorpusEntry> {
    vec![
        CorpusEntry {
            name: "katsura-4",
            family: "katsura",
            rung: Rung::Easy,
            zero_dimensional: true,
            equivalence: Equivalence::ComparandFile {
                tool: "msolve 0.11.0",
                file: "input_files/kat6-31.ms",
            },
            digest: "825a3aa54e152da5f2abac4a0b863430addacb4d8920aab3dac571cc681853fd",
        },
        CorpusEntry {
            name: "katsura-5",
            family: "katsura",
            rung: Rung::Easy,
            zero_dimensional: true,
            equivalence: Equivalence::ComparandFile {
                tool: "msolve 0.11.0",
                file: "input_files/kat6-31.ms",
            },
            digest: "6f305e37b2cc4ade59370c27a0bc6ac8e4ebd78030d13795f91f0e345a29ab58",
        },
        CorpusEntry {
            name: "katsura-6",
            family: "katsura",
            rung: Rung::Intermediate,
            zero_dimensional: true,
            equivalence: Equivalence::ComparandFile {
                tool: "msolve 0.11.0",
                file: "input_files/kat6-31.ms",
            },
            digest: "aa992992dfe29a23237fe2cfbbb83ad2822313dbde1b19363b9476bd92109e8d",
        },
        CorpusEntry {
            name: "katsura-7",
            family: "katsura",
            rung: Rung::Challenging,
            zero_dimensional: true,
            equivalence: Equivalence::ComparandFile {
                tool: "msolve 0.11.0",
                file: "input_files/kat6-31.ms",
            },
            digest: "545cef6185ed10e413141585464f8f72e8d3a1783d3a66a441f1dcb7d1edb4e6",
        },
        CorpusEntry {
            name: "cyclic-4",
            family: "cyclic",
            rung: Rung::Easy,
            // Positive-dimensional, and in the corpus deliberately for that reason.
            zero_dimensional: false,
            equivalence: Equivalence::ComparandFile {
                tool: "msolve 0.11.0",
                file: "input_files/cyclic5-16.ms",
            },
            digest: "e1d8d59448b3d648fdb8fb730dc4451c59979453749f9e4f11cf47900336770e",
        },
        CorpusEntry {
            name: "cyclic-5",
            family: "cyclic",
            rung: Rung::Easy,
            zero_dimensional: true,
            equivalence: Equivalence::ComparandFile {
                tool: "msolve 0.11.0",
                file: "input_files/cyclic5-16.ms",
            },
            digest: "3274d14b224664ae83dc6fb5381a4e476e7d5aed2368fae4bfa436c4b5eaf037",
        },
        CorpusEntry {
            name: "cyclic-6",
            family: "cyclic",
            rung: Rung::Intermediate,
            zero_dimensional: true,
            equivalence: Equivalence::ComparandFile {
                tool: "msolve 0.11.0",
                file: "input_files/cyclic5-16.ms",
            },
            digest: "ed89afe173d160244138c66448351e7c002bafc27df18981ba09674a6d801354",
        },
        CorpusEntry {
            name: "mq-random-6",
            family: "mq-random",
            rung: Rung::Easy,
            // Square and random, so zero-dimensional with high probability but not by
            // construction. Asserted per rung rather than assumed; see
            // `test_every_zero_dimensional_claim_is_checked`.
            zero_dimensional: true,
            equivalence: Equivalence::LiveOracle { tool: "Singular" },
            digest: "d98e5e5bf82b46187967148b54ada7884376faf5c0f88926524b625e9f21987d",
        },
        CorpusEntry {
            name: "mq-random-10",
            family: "mq-random",
            rung: Rung::Intermediate,
            zero_dimensional: true,
            equivalence: Equivalence::LiveOracle { tool: "Singular" },
            digest: "72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2",
        },
        CorpusEntry {
            name: "mq-random-14",
            family: "mq-random",
            rung: Rung::Challenging,
            zero_dimensional: true,
            equivalence: Equivalence::LiveOracle { tool: "Singular" },
            digest: "029def705543e29b9f0648d3fa21a87be32358b79c3e64bb6dd222fa432c439d",
        },
        CorpusEntry {
            name: "mq-planted-6",
            family: "mq-planted",
            rung: Rung::Easy,
            zero_dimensional: true,
            equivalence: Equivalence::KnownSolution,
            digest: "55fb9b0622b6217a40d9b3918b59caf25b303c19db0d229827ad092ffefa8ccf",
        },
        CorpusEntry {
            name: "mq-planted-10",
            family: "mq-planted",
            rung: Rung::Intermediate,
            zero_dimensional: true,
            equivalence: Equivalence::KnownSolution,
            digest: "0eef4b55bce6fdc6e909f9bbd211ec5c8074ceadc77b45fea76b9fcff2b6c2cc",
        },
        CorpusEntry {
            name: "mq-planted-14",
            family: "mq-planted",
            rung: Rung::Challenging,
            zero_dimensional: true,
            equivalence: Equivalence::KnownSolution,
            digest: "063f5b1ddbab6ef1651507e069d2796f2db1d3edff6f0ae31b8cdcc210749912",
        },
        CorpusEntry {
            name: "poseidon-t2-rf2-rp0-planted",
            family: "poseidon",
            rung: Rung::Easy,
            zero_dimensional: true,
            equivalence: Equivalence::KnownSolution,
            digest: "f4cf6699cee835a673d3ae77ea0b8a4545bd31411215371b3f4b61d4573ffe94",
        },
        CorpusEntry {
            name: "poseidon-t2-rf2-rp2-planted",
            family: "poseidon",
            rung: Rung::Intermediate,
            zero_dimensional: true,
            equivalence: Equivalence::KnownSolution,
            digest: "3b3bfb037ceb32deab1eb043fcba3d7c3fc7322eede81747a8a3ab1138fb466b",
        },
        CorpusEntry {
            name: "poseidon-t2-rf4-rp0-planted",
            family: "poseidon",
            rung: Rung::Challenging,
            zero_dimensional: true,
            equivalence: Equivalence::KnownSolution,
            digest: "95cec79371a8751a37d0a639a81ea3d7a8f5ca927d523f9e46af2492c5753ffb",
        },
        CorpusEntry {
            name: "anemoi64-cico-n1-fcico",
            family: "anemoi",
            rung: Rung::Easy,
            zero_dimensional: true,
            // Over 2^64 - 353. **Groebner.jl can represent and compute this ring** — its
            // ceiling is typemax(UInt64) and it was measured correct at this very prime. What is
            // missing is a *second* external engine: Sagebrush stops at 2^62 and msolve and
            // Singular at 2^31, so there is one comparand and nothing to triangulate against.
            equivalence: Equivalence::SoleComparand {
                tool: "Groebner.jl",
                reason: "2^64 - 353 is above Sagebrush's 2^62 gate and msolve's and Singular's \
                         2^31, so Groebner.jl is the only external engine that reaches it",
            },
            digest: "c053c6ff0186e3b48a17699c1e244ed173218571b42dd64ad4acd13fea02f299",
        },
        CorpusEntry {
            name: "anemoi64-cico-n2-fcico",
            family: "anemoi",
            rung: Rung::Intermediate,
            zero_dimensional: true,
            equivalence: Equivalence::SoleComparand {
                tool: "Groebner.jl",
                reason: "2^64 - 353 is above Sagebrush's 2^62 gate and msolve's and Singular's \
                         2^31, so Groebner.jl is the only external engine that reaches it",
            },
            digest: "e3a6312e85c486b046e062a8da1c6335934415efa10de54d55186c67409d1e94",
        },
    ]
}

/// The ladder as a machine-checkable manifest: one line per rung.
///
/// `name family rung zero-dimensional variables digest`, space-separated ASCII, sorted by name.
/// Line-oriented so that another language's harness can read it, and so that a digest can be
/// reproduced by hand — the same reason
/// [`Instance::canonical`](super::Instance::canonical) is line-oriented.
pub fn manifest() -> String {
    let mut lines: Vec<String> = ladder()
        .into_iter()
        .map(|entry| {
            let built = instance(
                entry.name,
                REFERENCE_CHARACTERISTIC,
                MonomialOrder::GradedReverseLexicographic,
            )
            .expect("every ladder entry is buildable");
            format!(
                "{} {} {} {} {} {} {}",
                entry.name,
                entry.family,
                entry.rung.tag(),
                entry.equivalence.tag(),
                if entry.zero_dimensional {
                    "zero-dimensional"
                } else {
                    "positive-dimensional"
                },
                built.variable_count(),
                built.digest()
            )
        })
        .collect();
    lines.sort();
    let mut text = format!(
        "# zeebra cross-library corpus, characteristic {} order grevlex\n\
         # name family rung equivalence dimension variables digest\n",
        REFERENCE_CHARACTERISTIC
    );
    for line in lines {
        text.push_str(&line);
        text.push('\n');
    }
    text
}

#[cfg(test)]
mod tests {
    use super::{
        ceilings, corroboration, corroboration_for, instance, ladder, manifest, CorpusEntry,
        Corroboration, Equivalence, Rung, ALTERNATE_CHARACTERISTIC, REFERENCE_CHARACTERISTIC,
    };
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura},
            external::Task,
            research::{satisfies, ANEMOI_64_PRIME, KOALABEAR_PRIME},
        },
        MonomialOrder, MultivariatePolynomial, One, Zero,
    };
    use std::collections::BTreeSet;

    type F = Zp2147483647;

    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    /// `["x1", ..., "xN"]`, which is what `parse` wants and what every engine's files use.
    fn names<const N: usize>() -> [&'static str; N] {
        // Sixteen is enough for every rung in the ladder; a wider one must extend this rather
        // than silently truncate, which `copy_from_slice` enforces by panicking.
        const ALL: [&str; 16] = [
            "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13",
            "x14", "x15", "x16",
        ];
        let mut out = [""; N];
        out.copy_from_slice(&ALL[..N]);
        out
    }

    /// Parse a set of generator strings over the reference field, canonicalized by Zeebra's own
    /// renderer so the comparison is between polynomials rather than between two spellings of one.
    fn parse_set<const N: usize>(generators: &[&str]) -> BTreeSet<String> {
        let names = names::<N>();
        generators
            .iter()
            .map(|text| {
                let polynomial: MultivariatePolynomial<N, F> =
                    MultivariatePolynomial::parse(text, names).expect("parses");
                crate::grobner::differential::polynomial_to_string(&polynomial, &names, GREVLEX)
            })
            .collect()
    }

    /// `katsura::<6>` is msolve's distributed `kat6`, generator for generator.
    ///
    /// **Resolves the Katsura indexing hazard empirically.** The literature's "Katsura-n" has
    /// n + 1 variables, so a name can mean either number; msolve's own `input_files/kat6-31.ms`
    /// declares six variables and is this system, which fixes msolve as naming by variable count
    /// and agreeing with Zeebra's const-generic parameter. Generator *order* differs — msolve puts
    /// the linear equation first and Zeebra last — so the comparison is between sets, which is
    /// right: a generating set is a set.
    #[test]
    fn test_katsura_6_is_msolves_kat6() {
        // Verbatim from msolve 0.11.0 `input_files/kat6-31.ms`, variables x1..x6.
        let msolve = [
            "x1+2*x2+2*x3+2*x4+2*x5+2*x6-1",
            "x1^2+2*x2^2+2*x3^2+2*x4^2+2*x5^2+2*x6^2-x1",
            "2*x1*x2+2*x2*x3+2*x3*x4+2*x4*x5+2*x5*x6-x2",
            "x2^2+2*x1*x3+2*x2*x4+2*x3*x5+2*x4*x6-x3",
            "2*x2*x3+2*x1*x4+2*x2*x5+2*x3*x6-x4",
            "x3^2+2*x2*x4+2*x1*x5+2*x2*x6-x5",
        ];
        let theirs = parse_set::<6>(&msolve);

        let built =
            instance("katsura-6", REFERENCE_CHARACTERISTIC, GREVLEX).expect("in the ladder");
        let ours: BTreeSet<String> = built.system.iter().cloned().collect();

        assert_eq!(built.variable_count(), 6, "named by variable count");
        assert_eq!(
            ours, theirs,
            "katsura::<6> is not msolve's kat6, so the indexing conventions differ"
        );
    }

    /// `cyclic::<5>` is msolve's distributed `cyclic5`, and is the **affine** form.
    ///
    /// **Resolves the affine-versus-homogenized hazard empirically.** The homogenized cyclic
    /// system replaces `x1⋯xn − 1` with `x1⋯xn − h^n` in one more variable and is
    /// positive-dimensional, so the two are different problems with different costs and benchmark
    /// tables rarely say which they used. msolve's own file closes with `x1*x2*x3*x4*x5-1`, so the
    /// corpus is affine and says so.
    #[test]
    fn test_cyclic_5_is_msolves_cyclic5_and_is_affine() {
        // Verbatim from msolve 0.11.0 `input_files/cyclic5-16.ms`, variables x1..x5.
        let msolve = [
            "x1+x2+x3+x4+x5",
            "x1*x2+x1*x5+x2*x3+x3*x4+x4*x5",
            "x1*x2*x3+x1*x2*x5+x1*x4*x5+x2*x3*x4+x3*x4*x5",
            "x1*x2*x3*x4+x1*x2*x3*x5+x1*x2*x4*x5+x1*x3*x4*x5+x2*x3*x4*x5",
            "x1*x2*x3*x4*x5-1",
        ];
        let theirs = parse_set::<5>(&msolve);

        let built = instance("cyclic-5", REFERENCE_CHARACTERISTIC, GREVLEX).expect("in the ladder");
        let ours: BTreeSet<String> = built.system.iter().cloned().collect();

        assert_eq!(built.variable_count(), 5);
        assert_eq!(
            ours, theirs,
            "cyclic::<5> is not msolve's cyclic5, so one of them is homogenized"
        );
        // The affine closure is what makes it zero-dimensional, so it is asserted directly rather
        // than left to the set comparison above.
        assert!(
            built
                .system
                .iter()
                .any(|g| g.contains("-1") || g.ends_with("+2147483646")),
            "the affine closing equation is absent: {:?}",
            built.system
        );
    }

    /// Every ladder entry builds, has a distinct digest, and the generated families are named by
    /// their variable count.
    ///
    /// The naming rule is what closes the Katsura hazard, so it is asserted rather than trusted —
    /// but it applies only to the families this module *generates*. Poseidon and Anemoi rows carry
    /// their **registry id**, which is their identity elsewhere in the crate and must not be
    /// renamed to suit a convention local to the corpus; their variable count is a consequence of
    /// the round count and is recorded in the manifest instead.
    #[test]
    fn test_every_ladder_entry_builds_and_the_generated_families_are_named_by_variable_count() {
        let mut digests: BTreeSet<String> = BTreeSet::new();
        for entry in ladder() {
            let built = instance(entry.name, REFERENCE_CHARACTERISTIC, GREVLEX)
                .unwrap_or_else(|| panic!("{} is in the ladder but not buildable", entry.name));
            assert_eq!(built.family, entry.family);
            assert!(
                digests.insert(built.digest()),
                "{} collides with another entry's digest",
                entry.name
            );

            if matches!(entry.family, "poseidon" | "anemoi") {
                assert_eq!(
                    built.name, entry.name,
                    "a registry row must keep its registry id"
                );
                continue;
            }
            let expected: usize = entry
                .name
                .rsplit('-')
                .next()
                .expect("a trailing number")
                .parse()
                .expect("a trailing number");
            assert_eq!(
                built.variable_count(),
                expected,
                "{} is not named by its variable count",
                entry.name
            );
        }
    }

    /// Every **coefficient** numeral in `generator`, with exponents and variable indices skipped.
    ///
    /// A digit run is a coefficient only where it does not continue an identifier (`x10`) and is
    /// not an exponent (`x1^2`), so the preceding character decides it.
    fn coefficient_numerals(generator: &str) -> Vec<u64> {
        let bytes: Vec<char> = generator.chars().collect();
        let mut out = Vec::new();
        let mut index = 0;
        while index < bytes.len() {
            if !bytes[index].is_ascii_digit() {
                index += 1;
                continue;
            }
            let start = index;
            while index < bytes.len() && bytes[index].is_ascii_digit() {
                index += 1;
            }
            let continues_identifier =
                start > 0 && (bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == '_');
            let is_exponent = start > 0 && bytes[start - 1] == '^';
            if continues_identifier || is_exponent {
                continue;
            }
            out.push(
                bytes[start..index]
                    .iter()
                    .collect::<String>()
                    .parse()
                    .expect("a digit run"),
            );
        }
        out
    }

    /// Every coefficient an instance renders is a residue of the characteristic it declares.
    ///
    /// The defect #425 names: generation was over the compile-time reference field whatever
    /// `characteristic` said, so `katsura-4` at 32003 rendered `−1` as `2147483646` and handed
    /// every engine a different ideal from the one its `FieldSpec` claimed. Coefficients are
    /// rendered as residues, so "is a residue of the declared prime" is exactly the property the
    /// text must have.
    #[test]
    fn test_every_rendered_coefficient_is_a_residue_of_the_declared_characteristic() {
        for name in ["katsura-4", "cyclic-5", "mq-planted-6", "mq-random-6"] {
            for characteristic in [
                REFERENCE_CHARACTERISTIC,
                ALTERNATE_CHARACTERISTIC,
                32003,
                101,
            ] {
                let Some(built) = instance(name, characteristic, GREVLEX) else {
                    continue;
                };
                assert_eq!(
                    built.field.characteristic, characteristic,
                    "{} declared a characteristic it was not asked for",
                    name
                );
                for generator in &built.system {
                    for numeral in coefficient_numerals(generator) {
                        assert!(
                            numeral < characteristic,
                            "{} at {} renders {} in {:?}, which is not a residue",
                            name,
                            characteristic,
                            numeral,
                            generator
                        );
                    }
                }
            }
        }
    }

    /// The characteristic is a parameter of generation: two compiled primes render differently.
    ///
    /// The observable half of #425. Katsura's `−1` is `p − 1`, so the two renderings cannot
    /// coincide, and a generator that ignored the argument would make them identical.
    #[test]
    fn test_the_characteristic_changes_the_rendered_generators() {
        let reference = instance("katsura-4", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        let alternate = instance("katsura-4", ALTERNATE_CHARACTERISTIC, GREVLEX).expect("builds");
        assert_ne!(
            reference.system, alternate.system,
            "the generators are identical at two primes, so the field is only a label"
        );
        assert_ne!(reference.digest(), alternate.digest());
    }

    /// A characteristic with no compiled field makes a const-generic family refuse, not mislabel.
    ///
    /// `None` is already [`instance`]'s idiom for a size nobody compiled, and a prime nobody
    /// compiled is the same kind of absence. The three dispositions in the corpus differ for
    /// stated reasons, so each is pinned: const-generic families refuse, the runtime-field MQ
    /// generator accepts any prime, and a registry row keeps its own field.
    #[test]
    fn test_an_uncompiled_characteristic_is_refused_rather_than_mislabeled() {
        for name in ["katsura-4", "cyclic-5", "mq-planted-6"] {
            assert!(
                instance(name, 101, GREVLEX).is_none(),
                "{} claims to be buildable over an uncompiled prime",
                name
            );
        }
        assert!(
            instance("mq-random-6", 101, GREVLEX).is_some(),
            "the random MQ generator reduces at run time, so every prime is available to it"
        );
        assert!(
            instance("poseidon-t2-rf2-rp0-planted", 101, GREVLEX).is_some(),
            "a registry row carries its own field and ignores the argument"
        );
    }

    /// Every compiled characteristic builds every ladder rung.
    ///
    /// Pins [`GENERATED_CHARACTERISTICS`] against the dispatch itself: the list is what a caller
    /// reads and the match is what runs, and a prime in one and not the other is the drift this
    /// catches.
    #[test]
    fn test_every_compiled_characteristic_builds_every_rung() {
        for characteristic in super::GENERATED_CHARACTERISTICS {
            for entry in ladder() {
                assert!(
                    instance(entry.name, characteristic, GREVLEX).is_some(),
                    "{} does not build at {}, which GENERATED_CHARACTERISTICS lists",
                    entry.name,
                    characteristic
                );
            }
        }
    }

    /// The digest changes with the monomial order and with the characteristic.
    ///
    /// Both change the answer, so both must be part of the problem's identity — otherwise a figure
    /// taken under grevlex could be compared with one taken under lex.
    #[test]
    fn test_the_digest_separates_orders_and_characteristics() {
        let grevlex = instance("katsura-5", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        let lex = instance(
            "katsura-5",
            REFERENCE_CHARACTERISTIC,
            MonomialOrder::Lexicographic,
        )
        .expect("builds");
        assert_ne!(grevlex.digest(), lex.digest());

        // A **compiled** second prime, so the difference is in the generated coefficients and not
        // only in the `FieldSpec` line of the canonical form.
        let other_field = instance("katsura-5", ALTERNATE_CHARACTERISTIC, GREVLEX).expect("builds");
        assert_ne!(grevlex.digest(), other_field.digest());
    }

    /// The ladder spans all three difficulties in each family, rather than one size repeated.
    ///
    /// A family represented only by instances every engine times out on measures nothing, and one
    /// represented only by millisecond instances measures startup cost.
    #[test]
    fn test_the_ladder_spans_its_difficulties() {
        for family in ["katsura", "cyclic", "mq-random", "mq-planted", "poseidon"] {
            let rungs: BTreeSet<Rung> = ladder()
                .into_iter()
                .filter(|entry| entry.family == family)
                .map(|entry| entry.rung)
                .collect();
            assert!(
                rungs.contains(&Rung::Easy) && rungs.contains(&Rung::Intermediate),
                "{} has only {:?}",
                family,
                rungs
            );
        }
        assert!(
            ladder().iter().any(|entry| entry.rung == Rung::Challenging),
            "the ladder has no challenging rung, so nothing exercises StoppedByLimit"
        );
    }

    /// `cyclic-4` is recorded as positive-dimensional, which is a fact about the ideal.
    ///
    /// A square system is not zero-dimensional merely for being square, and a task needing a
    /// finite quotient does not apply here — which is an `Unsupported`-shaped fact, not a failure
    /// of whichever engine was asked.
    #[test]
    fn test_cyclic_4_is_recorded_as_positive_dimensional() {
        let entry = ladder()
            .into_iter()
            .find(|entry| entry.name == "cyclic-4")
            .expect("in the ladder");
        assert!(!entry.zero_dimensional);
        assert!(
            ladder()
                .iter()
                .filter(|entry| entry.family == "cyclic")
                .any(|entry| entry.zero_dimensional),
            "the cyclic family must also carry a zero-dimensional rung"
        );
        // `LexBasisByConversion` is the task this excludes, and the corpus document says so.
        assert_eq!(Task::LexBasisByConversion.tag(), "lex-basis-by-conversion");
    }

    /// Every identifier in every rung's generators is a **declared** variable.
    ///
    /// Not a hypothetical. msolve's reader (`iofiles.c:57-62`) has no `else` branch for an
    /// identifier it does not recognise, so a generator naming an undeclared variable has that
    /// factor **silently dropped**: `x*z-1` with only `x,y` declared reads as `x-1`, msolve exits
    /// 0, and reports `#invalid equations 0`. The result is a well-formed answer to a *different*
    /// ideal, with nothing anywhere to indicate it.
    ///
    /// This corpus renders its variable list from the same `Instance`, so it is not at risk by
    /// construction — which is exactly why the property is worth asserting rather than assuming.
    /// Same family as the `x1`/`x10` collision above: a malformed render that produces a
    /// well-formed different problem.
    #[test]
    fn test_every_identifier_in_every_rung_is_a_declared_variable() {
        for entry in ladder() {
            let built = instance(entry.name, REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
            let declared: BTreeSet<&str> = built.variables.iter().map(String::as_str).collect();
            for generator in &built.system {
                // Identifiers are maximal runs of letters, digits and underscores that start with
                // a letter; everything else in the syntax is an operator or a numeral.
                let mut identifier = String::new();
                for character in generator.chars().chain(std::iter::once('+')) {
                    if character.is_ascii_alphanumeric() || character == '_' {
                        identifier.push(character);
                        continue;
                    }
                    if identifier
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_ascii_alphabetic())
                    {
                        assert!(
                            declared.contains(identifier.as_str()),
                            "{} names undeclared {:?} in {:?}; declared are {:?}",
                            entry.name,
                            identifier,
                            generator,
                            declared
                        );
                    }
                    identifier.clear();
                }
            }
        }
    }

    /// A rung with ten or more variables round-trips, so `x1` and `x10` are not confused.
    ///
    /// A genuine hazard of a text interface rather than a hypothetical one: `x1*x10` contains `x1`
    /// as a prefix twice, and a greedy tokenizer reads it as `x1 * x1 * 0` or drops the `0`. Every
    /// engine in the comparison is handed these bytes, so a prefix collision here would be a
    /// silently different ideal in every one of them. Checked as a set equality against the
    /// library's own generators at the widest rung.
    #[test]
    fn test_a_wide_rung_round_trips_without_confusing_x1_and_x10() {
        let built = instance("mq-planted-14", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        assert!(
            built.variables.contains(&"x14".to_string()),
            "the premise: this rung has a two-digit variable"
        );
        assert!(
            built.system.iter().any(|g| g.contains("x1")),
            "and generators mentioning x1, whose name is a prefix of x14's"
        );

        let parsed: BTreeSet<String> = built
            .system
            .iter()
            .map(|text| {
                let polynomial: MultivariatePolynomial<14, F> =
                    MultivariatePolynomial::parse(text, names::<14>()).expect("parses");
                crate::grobner::differential::polynomial_to_string(
                    &polynomial,
                    &names::<14>(),
                    GREVLEX,
                )
            })
            .collect();
        let point = super::planted_point::<14, F>();
        let direct: BTreeSet<String> = crate::grobner::benchmark_systems::planted::<14, F>(&point)
            .iter()
            .map(|p| crate::grobner::differential::polynomial_to_string(p, &names::<14>(), GREVLEX))
            .collect();
        assert_eq!(
            parsed, direct,
            "a fourteen-variable rung does not survive the text round trip"
        );
    }

    /// Every planted rung's known solution satisfies the system **as text**, after a round trip.
    ///
    /// The `KnownSolution` evidence, and the reason it is strong for a cross-library corpus: an
    /// engine whose parser read the text differently will not vanish at the point, and that is
    /// detectable without the engine computing a basis. Checking it after re-parsing the rendered
    /// generators is what makes it a statement about the bytes every engine is handed, rather than
    /// about the polynomials this crate holds in memory.
    #[test]
    fn test_every_planted_rungs_known_solution_satisfies_the_rendered_text() {
        fn check<const N: usize>(name: &str) {
            let built = instance(name, REFERENCE_CHARACTERISTIC, GREVLEX).expect("in the ladder");
            let parsed: Vec<MultivariatePolynomial<N, F>> = built
                .system
                .iter()
                .map(|text| MultivariatePolynomial::parse(text, names::<N>()).expect("parses"))
                .collect();
            let point = super::planted_point::<N, F>();
            assert!(
                satisfies(&parsed, &point),
                "{}'s planted point does not satisfy its own rendered system",
                name
            );
        }
        check::<6>("mq-planted-6");
        check::<10>("mq-planted-10");
        check::<14>("mq-planted-14");
    }

    /// A planted rung's point is **not** a solution of a different rung's system.
    ///
    /// Guards the check above being vacuous. A system that vanished everywhere, or a point of all
    /// zeros against a system with no constant term, would satisfy the test without the
    /// construction meaning anything.
    #[test]
    fn test_a_planted_point_is_specific_to_its_own_system() {
        let six = instance("mq-planted-6", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        let parsed: Vec<MultivariatePolynomial<6, F>> = six
            .system
            .iter()
            .map(|text| MultivariatePolynomial::parse(text, names::<6>()).expect("parses"))
            .collect();

        let mut wrong = super::planted_point::<6, F>();
        wrong[0] += F::one();
        assert!(
            !satisfies(&parsed, &wrong),
            "a perturbed point still satisfies the system, so the check proves nothing"
        );

        let zeros = [F::zero(); 6];
        assert!(
            !satisfies(&parsed, &zeros),
            "the all-zero point satisfies the system, so it has no constant terms"
        );
    }

    /// Every family licenses a timing, and only the corroborated ones claim corroboration.
    ///
    /// The gate, and the distinction it now draws. Anemoi is over `2^64 - 353`, which
    /// **Groebner.jl does reach** — so the family is representable and its timing is publishable.
    /// What it lacks is a *second* external engine, so its agreement cannot be triangulated. Those
    /// two limits have different fixes, which is why they are different variants.
    #[test]
    fn test_every_family_licenses_a_timing_and_only_some_are_corroborated() {
        for entry in ladder() {
            assert!(
                entry.equivalence.licenses_timing(),
                "{} should license a timing",
                entry.name
            );
            match entry.family {
                "anemoi" => assert!(
                    !entry.equivalence.is_corroborated(),
                    "{} has one external engine, so nothing can triangulate it",
                    entry.name
                ),
                _ => assert!(
                    entry.equivalence.is_corroborated(),
                    "{} should be corroborated",
                    entry.name
                ),
            }
        }

        // The two field facts the table above rests on. `const` assertions rather than runtime
        // ones because both are compile-time constants, so a change to either prime should fail
        // the build rather than wait for this test to be run.
        const {
            assert!(
                KOALABEAR_PRIME < REFERENCE_CHARACTERISTIC,
                "KoalaBear must sit below the comparands' ceiling for the Poseidon rows to be \
                 comparable at all"
            )
        };
        const {
            assert!(
                ANEMOI_64_PRIME > REFERENCE_CHARACTERISTIC,
                "the Anemoi rows' weaker corroboration rests on their prime being above the \
                 four-way band"
            )
        };
    }

    /// The corroboration bands follow from the engine ceilings, not from prose.
    ///
    /// The capability boundary as arithmetic, checked at each real field Zeebra uses. A corrected
    /// ceiling then corrects every statement depending on it, which is the point of deriving this
    /// rather than writing it down. The error being guarded is the one that reached a draft of the
    /// report: asserting that *no* engine reaches `2^64 - 353` when Groebner.jl does, which
    /// confuses representability with corroboration.
    #[test]
    fn test_the_corroboration_bands_follow_from_the_engine_ceilings() {
        // Four-way: every engine reaches it.
        assert_eq!(corroboration(KOALABEAR_PRIME), Corroboration::FourWay);
        assert_eq!(
            corroboration(REFERENCE_CHARACTERISTIC),
            Corroboration::FourWay
        );
        assert_eq!(corroboration(ceilings::MSOLVE - 1), Corroboration::FourWay);

        // Two-way: Groebner.jl and Sagebrush, neither checkable against a third.
        assert_eq!(corroboration(ceilings::MSOLVE), Corroboration::TwoWay);
        assert_eq!(corroboration(1 << 40), Corroboration::TwoWay);
        assert_eq!(
            corroboration(ceilings::SAGEBRUSH - 1),
            Corroboration::TwoWay
        );

        // Sole engine: Groebner.jl alone. Goldilocks and Anemoi's 2^64 - 353 are both here.
        assert_eq!(
            corroboration(ceilings::SAGEBRUSH),
            Corroboration::SoleEngine
        );
        assert_eq!(corroboration(ANEMOI_64_PRIME), Corroboration::SoleEngine);
        assert_eq!(
            corroboration(0xFFFF_FFFF_0000_0001),
            Corroboration::SoleEngine,
            "Goldilocks"
        );

        // Triangulable only where at least two external engines reach the field.
        assert!(corroboration(REFERENCE_CHARACTERISTIC).can_triangulate());
        assert!(corroboration(1 << 40).can_triangulate());
        assert!(!corroboration(ANEMOI_64_PRIME).can_triangulate());

        assert_eq!(corroboration(REFERENCE_CHARACTERISTIC).engines(), 4);
        assert_eq!(corroboration(ANEMOI_64_PRIME).engines(), 1);
    }

    /// Corroboration is **task-specific**, and the conversion task is the narrowest.
    ///
    /// The case that matters most for #263: the conversion stage is where Zeebra's only measured
    /// cross-library deficit lies, and **Sagebrush exposes no FGLM route at all** — a missing task
    /// rather than a field ceiling. So above `2^31` conversion has one corroborator where a basis
    /// has two, and reading a basis band as a conversion band would overstate what can check a
    /// future Anemoi conversion row.
    #[test]
    fn test_corroboration_is_task_specific_and_conversion_is_narrowest() {
        // Below 2^31 every engine does a basis; only three do a conversion.
        assert_eq!(
            corroboration_for(Task::ReducedGrobnerBasis, REFERENCE_CHARACTERISTIC),
            Corroboration::FourWay
        );
        assert_eq!(
            corroboration_for(Task::LexBasisByConversion, REFERENCE_CHARACTERISTIC),
            Corroboration::ThreeWay,
            "Sagebrush exposes no FGLM route"
        );

        // Above 2^31 a basis keeps two engines; a conversion drops to one.
        assert_eq!(
            corroboration_for(Task::ReducedGrobnerBasis, 1 << 40),
            Corroboration::TwoWay
        );
        assert_eq!(
            corroboration_for(Task::LexBasisByConversion, 1 << 40),
            Corroboration::SoleEngine,
            "only Groebner.jl converts above msolve's and Singular's 2^31"
        );
        assert!(!corroboration_for(Task::LexBasisByConversion, 1 << 40).can_triangulate());

        // At Anemoi's field both tasks are sole-engine, for two different reasons.
        assert_eq!(
            corroboration_for(Task::ReducedGrobnerBasis, ANEMOI_64_PRIME),
            Corroboration::SoleEngine
        );
        assert_eq!(
            corroboration_for(Task::LexBasisByConversion, ANEMOI_64_PRIME),
            Corroboration::SoleEngine
        );

        // The eliminant collapses earlier still: msolve's bound is below a tenth of its basis one,
        // and the corpus reference prime is already above it.
        const {
            assert!(
                ceilings::MSOLVE_ELIMINANT < ceilings::MSOLVE,
                "the eliminant collapse rests on msolve's two bounds differing"
            )
        };
        assert_eq!(
            corroboration_for(Task::UnivariateEliminant, REFERENCE_CHARACTERISTIC),
            Corroboration::TwoWay,
            "msolve is out at 2^31 - 1; Singular and Groebner.jl remain"
        );

        // Nothing offers the solution tasks at any field — the unanimous gap #263 reports.
        for task in [
            Task::OneFiniteFieldSolution,
            Task::AllFiniteFieldSolutions,
            Task::CryptanalyticWitness,
        ] {
            assert_eq!(
                corroboration_for(task, REFERENCE_CHARACTERISTIC),
                Corroboration::None,
                "{} should have no comparand at any field",
                task.tag()
            );
        }
    }

    /// Anemoi's recorded reason names **corroboration**, not representability.
    ///
    /// A wording correction with teeth: the two limits have different fixes. Representability
    /// needs a new tool; corroboration needs a second tool at the same field. A reader deciding
    /// whether to trust an Anemoi row has to be told which one applies.
    #[test]
    fn test_anemois_reason_names_corroboration_and_not_representability() {
        let anemoi: Vec<CorpusEntry> = ladder()
            .into_iter()
            .filter(|entry| entry.family == "anemoi")
            .collect();
        assert!(!anemoi.is_empty());
        for entry in anemoi {
            match entry.equivalence {
                Equivalence::SoleComparand { tool, reason } => {
                    assert_eq!(tool, "Groebner.jl", "the one engine that reaches the field");
                    assert!(
                        reason.contains("only external engine"),
                        "the reason must say one engine reaches it, not that none does: {}",
                        reason
                    );
                }
                other => panic!(
                    "{} should be SoleComparand, not {:?} — Groebner.jl reaches 2^64 - 353",
                    entry.name, other
                ),
            }
        }
    }

    /// Six families, which is the milestone's minimum, each with its evidence recorded.
    #[test]
    fn test_the_corpus_covers_six_families_each_with_recorded_evidence() {
        let families: BTreeSet<&str> = ladder().iter().map(|entry| entry.family).collect();
        assert!(
            families.len() >= 6,
            "the corpus has {} families, below the minimum of six: {:?}",
            families.len(),
            families
        );
        // Each kind of evidence is actually exercised, so none of the vocabulary is dead.
        let kinds: BTreeSet<&str> = ladder()
            .iter()
            .map(|entry| entry.equivalence.tag())
            .collect();
        for expected in [
            "comparand-file",
            "known-solution",
            "live-oracle",
            "sole-comparand",
        ] {
            assert!(kinds.contains(expected), "no family uses {}", expected);
        }
        // `no-comparand` is deliberately unused by the ladder: it is for Zeebra's 254/255-bit
        // fields, where no surveyed engine reaches, and no rung sits at one of those.
        assert!(
            !kinds.contains("no-comparand"),
            "a ladder rung claims no comparand; check it is not really a sole-comparand row"
        );
    }

    /// A Poseidon rung is built from the registry at the registry's own field, not the corpus's.
    ///
    /// Poseidon's round constants come out of a seeded LFSR keyed on the prime, so the same row
    /// over another prime is another problem. The `characteristic` argument is therefore ignored
    /// for these rows, and this pins that rather than leaving it to a doc comment.
    #[test]
    fn test_a_poseidon_rung_keeps_the_registrys_field_whatever_is_asked_for() {
        let asked = instance("poseidon-t2-rf2-rp0-planted", 65521, GREVLEX).expect("builds");
        assert_eq!(asked.field.characteristic, KOALABEAR_PRIME);
        assert_eq!(asked.field.name, "KoalaBear");

        let other = instance(
            "poseidon-t2-rf2-rp0-planted",
            REFERENCE_CHARACTERISTIC,
            GREVLEX,
        )
        .expect("builds");
        assert_eq!(
            asked.digest(),
            other.digest(),
            "the characteristic argument must not change a registry row's identity"
        );

        // And the transformation names the registry row it came from, so the provenance is in the
        // instance rather than only in this module.
        assert!(
            asked
                .transformation
                .as_deref()
                .unwrap_or_default()
                .contains("poseidon-t2-rf2-rp0-planted"),
            "{:?}",
            asked.transformation
        );
    }

    /// An Anemoi rung is built from the registry over `2^64 - 353`.
    #[test]
    fn test_an_anemoi_rung_is_built_over_the_published_prime() {
        let built =
            instance("anemoi64-cico-n1-fcico", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        assert_eq!(built.field.characteristic, ANEMOI_64_PRIME);
        assert_eq!(built.family, "anemoi");
        assert!(!built.system.is_empty());
    }

    /// A random MQ rung is reproducible from its name alone, and is genuinely quadratic.
    ///
    /// The seed is part of the dispatcher, so two calls agree; and the generated system has to be
    /// degree two or it is not an MQ instance, which cancellation could in principle undo.
    #[test]
    fn test_a_random_mq_rung_is_reproducible_and_quadratic() {
        let once = instance("mq-random-6", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        let twice = instance("mq-random-6", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        assert_eq!(once.digest(), twice.digest(), "the seed is not pinned");
        assert_eq!(once.variable_count(), 6);
        assert_eq!(once.system.len(), 6, "square, which is what MQ means here");

        let parsed: Vec<MultivariatePolynomial<6, F>> = once
            .system
            .iter()
            .map(|text| MultivariatePolynomial::parse(text, names::<6>()).expect("parses"))
            .collect();
        let degree = parsed
            .iter()
            .flat_map(|p| p.terms().keys())
            .map(|m| m.exponents().iter().sum::<u32>())
            .max()
            .expect("a nonzero system");
        assert_eq!(degree, 2, "a random MQ rung must be quadratic, not linear");

        // The transformation records the seed, so a reader can reproduce it outside this module.
        assert!(
            once.transformation
                .as_deref()
                .unwrap_or_default()
                .contains("seed 6"),
            "{:?}",
            once.transformation
        );
    }

    /// Every ladder entry's frozen digest is the digest the generator actually produces.
    ///
    /// The pin. A failure here means the generated system changed, which means every figure ever
    /// taken against the old digest is a figure about a different problem — so this test failing
    /// is the point of the `digest` field, and the fix is to decide whether the change was
    /// intended before updating the constant.
    #[test]
    fn test_the_manifest_is_frozen() {
        for entry in ladder() {
            let built = instance(entry.name, REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
            assert_eq!(
                built.digest(),
                entry.digest,
                "{}'s generated system no longer matches its frozen digest",
                entry.name
            );
        }
    }

    /// The manifest is line-oriented ASCII, one line per rung, with the digests it claims.
    #[test]
    fn test_the_manifest_lists_every_rung_with_its_digest() {
        let text = manifest();
        assert!(text.starts_with("# zeebra cross-library corpus"));
        let rows: Vec<&str> = text
            .lines()
            .filter(|line| !line.starts_with('#'))
            .filter(|line| !line.is_empty())
            .collect();
        assert_eq!(rows.len(), ladder().len());
        for row in &rows {
            let columns: Vec<&str> = row.split(' ').collect();
            assert_eq!(columns.len(), 7, "{}", row);
            assert_eq!(columns[6].len(), 64, "a full sha256 digest: {}", row);
            assert!(columns[6].chars().all(|c| c.is_ascii_hexdigit()));
        }
        // Sorted, so the file is diffable across runs.
        let mut sorted = rows.clone();
        sorted.sort();
        assert_eq!(rows, sorted);
    }

    /// The generated systems are the ones `benchmark_systems` defines, not a copy.
    ///
    /// Guards the corpus becoming a second definition that drifts: the text is rendered from the
    /// library's own generators, and this checks the round trip back through the parser.
    #[test]
    fn test_the_corpus_text_round_trips_to_the_library_system() {
        let built = instance("cyclic-5", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        let parsed: BTreeSet<String> = built
            .system
            .iter()
            .map(|text| {
                let polynomial: MultivariatePolynomial<5, F> =
                    MultivariatePolynomial::parse(text, names::<5>()).expect("parses");
                // The renderer and not `Debug`: a term map's iteration order is not canonical,
                // so two equal polynomials can format differently.
                crate::grobner::differential::polynomial_to_string(
                    &polynomial,
                    &names::<5>(),
                    GREVLEX,
                )
            })
            .collect();
        let direct: BTreeSet<String> = cyclic::<5, F>()
            .iter()
            .map(|p| crate::grobner::differential::polynomial_to_string(p, &names::<5>(), GREVLEX))
            .collect();
        assert_eq!(parsed, direct);

        let built = instance("katsura-5", REFERENCE_CHARACTERISTIC, GREVLEX).expect("builds");
        let parsed: BTreeSet<String> = built
            .system
            .iter()
            .map(|text| {
                let polynomial: MultivariatePolynomial<5, F> =
                    MultivariatePolynomial::parse(text, names::<5>()).expect("parses");
                // The renderer and not `Debug`: a term map's iteration order is not canonical,
                // so two equal polynomials can format differently.
                crate::grobner::differential::polynomial_to_string(
                    &polynomial,
                    &names::<5>(),
                    GREVLEX,
                )
            })
            .collect();
        let direct: BTreeSet<String> = katsura::<5, F>()
            .iter()
            .map(|p| crate::grobner::differential::polynomial_to_string(p, &names::<5>(), GREVLEX))
            .collect();
        assert_eq!(parsed, direct);
    }
}
