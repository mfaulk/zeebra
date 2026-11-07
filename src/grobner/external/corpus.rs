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
//! # The ladder
//!
//! Rungs are chosen to be easy, intermediate and genuinely challenging rather than uniformly
//! large: a family represented only by instances every engine times out on measures nothing, and a
//! family represented only by instances every engine finishes in a millisecond measures startup
//! cost. [`ladder`] is that selection, and [`manifest`] freezes each rung's digest.

use crate::{
    fields::PrimeFieldElement64,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        differential::polynomial_to_string,
    },
    MonomialOrder, MultivariatePolynomial,
};

use super::{FieldSpec, Instance};

/// The corpus's reference characteristic.
///
/// `2^31 − 1`, chosen because **every engine in the comparison accepts it**: Singular and msolve
/// both stop below `2^31`, so a corpus keyed on a wider prime would make most of the table
/// `Unsupported` and measure nothing. Zeebra's own behaviour at Goldilocks and above is covered by
/// its cryptanalysis scoreboard, where there is no comparand to lose.
pub const REFERENCE_CHARACTERISTIC: u64 = 2_147_483_647;

/// The corpus's reference field.
type Reference = PrimeFieldElement64<REFERENCE_CHARACTERISTIC>;

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
/// `None` for a name not in [`ladder`], or for a name whose variable count has no compiled
/// instantiation. The families are const-generic, so the available sizes are exactly those listed
/// here — adding a rung means adding a match arm, which is deliberate: a size nobody wrote down is
/// a size nobody checked the equivalence of.
pub fn instance(name: &str, characteristic: u64, order: MonomialOrder) -> Option<Instance> {
    match name {
        "katsura-4" => Some(katsura_instance::<4>(characteristic, order)),
        "katsura-5" => Some(katsura_instance::<5>(characteristic, order)),
        "katsura-6" => Some(katsura_instance::<6>(characteristic, order)),
        "katsura-7" => Some(katsura_instance::<7>(characteristic, order)),
        "cyclic-4" => Some(cyclic_instance::<4>(characteristic, order)),
        "cyclic-5" => Some(cyclic_instance::<5>(characteristic, order)),
        "cyclic-6" => Some(cyclic_instance::<6>(characteristic, order)),
        _ => None,
    }
}

/// The Katsura instance in `N` variables — the literature's Katsura-`(N-1)`.
pub fn katsura_instance<const N: usize>(characteristic: u64, order: MonomialOrder) -> Instance {
    let system = katsura::<N, Reference>();
    text_instance(
        format!("katsura-{}", N),
        "katsura",
        &system,
        characteristic,
        order,
    )
}

/// The affine cyclic-`N` roots instance in `N` variables.
pub fn cyclic_instance<const N: usize>(characteristic: u64, order: MonomialOrder) -> Instance {
    let system = cyclic::<N, Reference>();
    text_instance(
        format!("cyclic-{}", N),
        "cyclic",
        &system,
        characteristic,
        order,
    )
}

/// Render a system to the text form every engine parses, and wrap it as an [`Instance`].
///
/// Variables are `x1 … xN`, which is what msolve's and Singular's own files use, and the order they
/// are declared in **is** the monomial order's variable order.
fn text_instance<const N: usize>(
    name: String,
    family: &str,
    system: &[MultivariatePolynomial<N, Reference>],
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
            digest: "825a3aa54e152da5f2abac4a0b863430addacb4d8920aab3dac571cc681853fd",
        },
        CorpusEntry {
            name: "katsura-5",
            family: "katsura",
            rung: Rung::Easy,
            zero_dimensional: true,
            digest: "6f305e37b2cc4ade59370c27a0bc6ac8e4ebd78030d13795f91f0e345a29ab58",
        },
        CorpusEntry {
            name: "katsura-6",
            family: "katsura",
            rung: Rung::Intermediate,
            zero_dimensional: true,
            digest: "aa992992dfe29a23237fe2cfbbb83ad2822313dbde1b19363b9476bd92109e8d",
        },
        CorpusEntry {
            name: "katsura-7",
            family: "katsura",
            rung: Rung::Challenging,
            zero_dimensional: true,
            digest: "545cef6185ed10e413141585464f8f72e8d3a1783d3a66a441f1dcb7d1edb4e6",
        },
        CorpusEntry {
            name: "cyclic-4",
            family: "cyclic",
            rung: Rung::Easy,
            // Positive-dimensional, and in the corpus deliberately for that reason.
            zero_dimensional: false,
            digest: "e1d8d59448b3d648fdb8fb730dc4451c59979453749f9e4f11cf47900336770e",
        },
        CorpusEntry {
            name: "cyclic-5",
            family: "cyclic",
            rung: Rung::Easy,
            zero_dimensional: true,
            digest: "3274d14b224664ae83dc6fb5381a4e476e7d5aed2368fae4bfa436c4b5eaf037",
        },
        CorpusEntry {
            name: "cyclic-6",
            family: "cyclic",
            rung: Rung::Intermediate,
            zero_dimensional: true,
            digest: "ed89afe173d160244138c66448351e7c002bafc27df18981ba09674a6d801354",
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
                "{} {} {} {} {} {}",
                entry.name,
                entry.family,
                entry.rung.tag(),
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
         # name family rung dimension variables digest\n",
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
    use super::{instance, ladder, manifest, Rung, REFERENCE_CHARACTERISTIC};
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura},
            external::Task,
        },
        MonomialOrder, MultivariatePolynomial,
    };
    use std::collections::BTreeSet;

    type F = Zp2147483647;

    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    /// `["x1", ..., "xN"]`, which is what `parse` wants and what every engine's files use.
    fn names<const N: usize>() -> [&'static str; N] {
        const ALL: [&str; 8] = ["x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8"];
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

    /// Every ladder entry builds, is named by its variable count, and has a distinct digest.
    #[test]
    fn test_every_ladder_entry_builds_and_is_named_by_its_variable_count() {
        let mut digests: BTreeSet<String> = BTreeSet::new();
        for entry in ladder() {
            let built = instance(entry.name, REFERENCE_CHARACTERISTIC, GREVLEX)
                .unwrap_or_else(|| panic!("{} is in the ladder but not buildable", entry.name));
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
            assert_eq!(built.family, entry.family);
            assert!(
                digests.insert(built.digest()),
                "{} collides with another entry's digest",
                entry.name
            );
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

        let other_field = instance("katsura-5", 65521, GREVLEX).expect("builds");
        assert_ne!(grevlex.digest(), other_field.digest());
    }

    /// The ladder spans all three difficulties in each family, rather than one size repeated.
    ///
    /// A family represented only by instances every engine times out on measures nothing, and one
    /// represented only by millisecond instances measures startup cost.
    #[test]
    fn test_the_ladder_spans_its_difficulties() {
        for family in ["katsura", "cyclic"] {
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
            assert_eq!(columns.len(), 6, "{}", row);
            assert_eq!(columns[5].len(), 64, "a full sha256 digest: {}", row);
            assert!(columns[5].chars().all(|c| c.is_ascii_hexdigit()));
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
