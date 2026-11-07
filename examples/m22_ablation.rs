//! M22's strategies, one table, every configuration asserted to return the same basis.
//!
//! M22-I. The plan's §11.1 ablation, with two departures that the earlier workstreams forced and
//! that are stated rather than quietly made:
//!
//! - **There is no mutant configuration**, because M22-D added no mutant mode. Its configurations D
//!   and Combined would be byte-identical to A and C. Inventing a mode to fill a row would be worse
//!   than the gap: see `docs/research/mutants.md` for why degree-first selection already gives
//!   lower-degree relations immediate priority.
//! - **A fixed batch cap is included**, because M22-A and M22-C established that it, not the
//!   uncapped baseline, is the reference a Hilbert-driven cap has to beat. §11.1 permits
//!   configurations "needed to isolate interaction effects", and without this one the strongest
//!   result in the milestone is attributed to the wrong cause.
//!
//! Every row reports **solve and certification separately and their total**, and the total is the
//! only figure a production decision may use — §11.1's "complete end-to-end computation time".
//!
//! ```text
//! tools/fetch-mq-challenge.sh
//! cargo run --release --example m22_ablation
//! cargo run --release --example m22_ablation -- list
//! cargo run --release --example m22_ablation -- katsura-7
//! ```
//!
//! Variable order is held fixed at the generated layout throughout. M22-E measured it at 1.6x–1.7x
//! on the Poseidon systems, which would otherwise be attributed to whichever F4 strategy happened
//! to vary alongside it.

use std::{path::PathBuf, time::Instant};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        certify_f4_output, classify_ideal, f4_reported,
        research::{
            CicoInstance, MqInstance, Poseidon, PoseidonParameters, Specialization, KOALABEAR_PRIME,
        },
        F4Options, F4Statistics, HilbertSelection, IdealClass, PairSchedule,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type Q = PrimeFieldElement64<31>;
type K = PrimeFieldElement64<KOALABEAR_PRIME>;
type P = PrimeFieldElement64<2_147_483_647>;

const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const C1: u64 = 0xC0_9DE4;

/// The ablation matrix.
///
/// Named as §11.1 names them, with the two departures the module docs explain.
fn configurations() -> Vec<(&'static str, F4Options)> {
    let base = || F4Options {
        profile_degrees: true,
        max_matrix_columns: 60_000,
        max_live_bytes: 400_000_000,
        max_batches: Some(20_000),
        ..F4Options::default()
    };
    vec![
        ("Baseline", base()),
        (
            "A  small-mult monomial",
            F4Options {
                schedule: PairSchedule::SmallMultiplierMonomial,
                ..base()
            },
        ),
        (
            "A' small-mult degree",
            F4Options {
                schedule: PairSchedule::SmallMultiplierDegree,
                ..base()
            },
        ),
        (
            "B  hilbert observe",
            F4Options {
                hilbert: HilbertSelection::Observe,
                ..base()
            },
        ),
        (
            "C  A + hilbert+16",
            F4Options {
                schedule: PairSchedule::SmallMultiplierMonomial,
                hilbert: HilbertSelection::CertifiedLimited { slack: 16 },
                ..base()
            },
        ),
        (
            "Cap  fixed cap 64",
            F4Options {
                max_pairs_per_batch: Some(64),
                ..base()
            },
        ),
        (
            "A+Cap",
            F4Options {
                schedule: PairSchedule::SmallMultiplierMonomial,
                max_pairs_per_batch: Some(64),
                ..base()
            },
        ),
        (
            "D  = A (no mutant mode)",
            F4Options {
                schedule: PairSchedule::SmallMultiplierMonomial,
                ..base()
            },
        ),
    ]
}

/// One measured configuration.
struct Row {
    label: String,
    pairs: usize,
    batches: usize,
    degree: u64,
    columns: usize,
    peak_bytes: usize,
    solve: f64,
    certify: f64,
    elements: usize,
    note: String,
}

fn header() {
    println!(
        "| {:<24} | {:>6} | {:>5} | {:>3} | {:>7} | {:>8} | {:>9} | {:>8} | {:>9} | {:>4} |",
        "configuration",
        "pairs",
        "batch",
        "deg",
        "cols",
        "peak MB",
        "solve ms",
        "cert ms",
        "total ms",
        "|G|"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(26),
        "-".repeat(8),
        "-".repeat(7),
        "-".repeat(5),
        "-".repeat(9),
        "-".repeat(10),
        "-".repeat(11),
        "-".repeat(10),
        "-".repeat(11),
        "-".repeat(6),
    );
}

fn print_row(row: &Row) {
    if !row.note.is_empty() {
        println!("| {:<24} | {} |", truncate(&row.label, 24), row.note);
        return;
    }
    println!(
        "| {:<24} | {:>6} | {:>5} | {:>3} | {:>7} | {:>8} | {:>9} | {:>8} | {:>9} | {:>4} |",
        truncate(&row.label, 24),
        row.pairs,
        row.batches,
        row.degree,
        row.columns,
        format!("{:.1}", row.peak_bytes as f64 / 1e6),
        format!("{:.1}", row.solve),
        format!("{:.1}", row.certify),
        format!("{:.1}", row.solve + row.certify),
        row.elements,
    );
}

fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        format!("{}…", s.chars().take(width - 1).collect::<String>())
    }
}

fn measure(
    label: &str,
    statistics: &F4Statistics,
    solve: f64,
    certify: f64,
    elements: usize,
) -> Row {
    Row {
        label: label.to_string(),
        pairs: statistics.pairs_reduced,
        batches: statistics.batches,
        degree: statistics.max_pair_degree,
        columns: statistics.max_matrix_columns,
        peak_bytes: statistics.max_estimated_bytes,
        solve,
        certify,
        elements,
        note: String::new(),
    }
}

/// §11.4's verification, in full, on one computed basis.
///
/// Five checks. Buchberger's criterion; every original generator reduces to zero; the result
/// generates nothing outside the input ideal; the basis is reduced; and exact comparison against
/// the reference.
///
/// The first, second and fourth are `certify_f4_output`. The third and fifth are both the equality
/// assertion: a reduced Gröbner basis is unique for an ideal and an order, so equality with the
/// baseline's *is* the statement that the ideal did not change. That is why it is an assertion and
/// not a column — a differing basis is a defect, and reporting it in a table would bury it.
fn verify<const N: usize, F: FiniteField>(
    label: &str,
    generators: &[MultivariatePolynomial<N, F>],
    basis: &[MultivariatePolynomial<N, F>],
    reference: Option<&[MultivariatePolynomial<N, F>]>,
) -> f64 {
    if let Some(reference) = reference {
        assert_eq!(
            basis, reference,
            "{}: the reduced Gröbner basis is not the baseline's — a strategy changed the answer",
            label
        );
    }
    let report = certify_f4_output(generators, basis, GREVLEX);
    assert!(
        report.is_complete(),
        "{}: certification failed — {:?}",
        label,
        report.first_failure()
    );
    report.elapsed.as_secs_f64() * 1e3
}

/// Run the whole ablation on one system.
fn ablate<const N: usize, F: FiniteField>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    note: &str,
) {
    println!("### {}", name);
    println!();
    if !note.is_empty() {
        println!("{}", note);
        println!();
    }

    let mut reference: Option<Vec<MultivariatePolynomial<N, F>>> = None;
    let mut rows: Vec<Row> = Vec::new();
    let mut dimension: Option<IdealClass> = None;

    for (label, options) in configurations() {
        let at = Instant::now();
        let (result, statistics) = f4_reported(system, GREVLEX, &options);
        let solve = at.elapsed().as_secs_f64() * 1e3;

        match result {
            Err(e) => rows.push(Row {
                label: label.to_string(),
                note: e.to_string(),
                pairs: 0,
                batches: 0,
                degree: 0,
                columns: 0,
                peak_bytes: 0,
                solve,
                certify: 0.0,
                elements: 0,
            }),
            Ok(basis) => {
                let certify = verify(label, system, &basis, reference.as_deref());
                if dimension.is_none() {
                    dimension = Some(classify_ideal(&basis, GREVLEX));
                }
                let elements = basis.len();
                if reference.is_none() {
                    reference = Some(basis);
                }
                rows.push(measure(label, &statistics, solve, certify, elements));
            }
        }
    }

    println!(
        "- {} variables, {} generators; the ideal is {}",
        N,
        system.len(),
        match dimension {
            Some(IdealClass::ZeroDimensional) => "zero-dimensional",
            Some(IdealClass::PositiveDimensional) => "positive-dimensional",
            Some(IdealClass::Unit) => "the whole ring — inconsistent",
            None => "of undetermined dimension (nothing finished)",
        }
    );
    println!();
    header();
    for row in &rows {
        print_row(row);
    }
    println!();
}

fn mq_directory() -> PathBuf {
    std::env::var("ZEEBRA_MQ_DIR")
        .unwrap_or_else(|_| "research/instances/mq".to_string())
        .into()
}

fn load_mq(stem: &str) -> Option<(MqInstance, Vec<u64>)> {
    let text = std::fs::read_to_string(mq_directory().join(stem)).ok()?;
    let instance = MqInstance::parse(&text).ok()?;
    // A missing answer file is ordinary: not every instance publishes one. A present one that does
    // not parse is not ordinary at all — it is the check the import is verified against, so it is
    // loud rather than an empty vector (#415).
    let answer = match std::fs::read_to_string(mq_directory().join(format!("{}-answer", stem))) {
        Ok(text) => instance
            .parse_answer(&text)
            .unwrap_or_else(|e| panic!("{}-answer: {}", stem, e)),
        Err(_) => Vec::new(),
    };
    Some((instance, answer))
}

fn cico<const N: usize>(t: usize, r_f: usize, r_p: usize) -> Vec<MultivariatePolynomial<N, K>> {
    let poseidon = Poseidon::<K>::new(PoseidonParameters {
        prime: KOALABEAR_PRIME,
        alpha: 3,
        t,
        r_f,
        r_p,
    })
    .expect("R_F is even");
    let free: Vec<K> = (0..t - 1).map(|i| K::new(1_000 + i as u64)).collect();
    CicoInstance::planted(
        poseidon,
        1,
        &[K::new(C1)],
        &free,
        Some(PoseidonParameters::bounty_cico()),
    )
    .expect("the right widths")
    .system::<N>()
    .expect("the right dimension")
}

/// A nonradical ideal: `<x^2, y^2>` has the origin as its only point, with multiplicity.
fn nonradical() -> Vec<MultivariatePolynomial<3, P>> {
    ["x^2", "y^2", "z^2 - z"]
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, ["x", "y", "z"]).expect("parses"))
        .collect()
}

/// A positive-dimensional ideal: `z` appears in no generator.
fn positive_dimensional() -> Vec<MultivariatePolynomial<3, P>> {
    ["x^2 - y", "x*y - 1"]
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, ["x", "y", "z"]).expect("parses"))
        .collect()
}

fn instances() -> Vec<&'static str> {
    vec![
        "katsura-5",
        "katsura-6",
        "katsura-7",
        "cyclic-5",
        "cyclic-6",
        "planted-6",
        "nonradical",
        "positive-dimensional",
        "poseidon-t2-rf2-rp2",
        "poseidon-t2-rf4",
        "poseidon-t3-pinned",
        "mq3-n10",
        "mq6-n10-specialized",
    ]
}

fn run_instance(name: &str) {
    match name {
        "katsura-5" => ablate("katsura-5", &katsura::<5, P>(), "Regression against M16."),
        "katsura-6" => ablate("katsura-6", &katsura::<6, P>(), "Regression against M16."),
        "katsura-7" => ablate(
            "katsura-7",
            &katsura::<7, P>(),
            "The largest classical instance in the corpus; M16's hardest grevlex case.",
        ),
        "cyclic-5" => ablate(
            "cyclic-5",
            &cyclic::<5, P>(),
            "Different Gröbner geometry from katsura.",
        ),
        "cyclic-6" => ablate("cyclic-6", &cyclic::<6, P>(), ""),
        "planted-6" => {
            let point: Vec<P> = (0..6).map(|i| P::new(7 + 11 * i as u64)).collect();
            ablate(
                "planted-6",
                &planted::<6, P>(&point),
                "An easy-lex counterexample: the lex basis is triangular by construction.",
            )
        }
        "nonradical" => ablate(
            "nonradical",
            &nonradical(),
            "`<x^2, y^2, z^2 - z>` — the origin with multiplicity, so radical membership is not \
             the same question as ideal membership.",
        ),
        "positive-dimensional" => ablate(
            "positive-dimensional",
            &positive_dimensional(),
            "`z` appears in no generator, so the ideal is positive-dimensional and every \
             configuration has to terminate on it anyway.",
        ),
        "poseidon-t2-rf2-rp2" => ablate("poseidon t=2 R_F=2 R_P=2", &cico::<7>(2, 2, 2), ""),
        "poseidon-t2-rf4" => ablate("poseidon t=2 R_F=4", &cico::<9>(2, 4, 0), ""),
        "poseidon-t3-pinned" => {
            let system = cico::<9>(3, 2, 1);
            let pinned = Specialization::<9, K>::new(&[(0, K::new(1_000))]).expect("one");
            ablate(
                "poseidon t=3, input pinned",
                &pinned.apply(&system),
                "M22-E's controlled row: the `t = 3` system with one free input pinned, which \
                 matches the equation count without touching the round structure.",
            )
        }
        "mq3-n10" => match load_mq("ToyExample-type3-n10-seed0") {
            Some((instance, _)) => ablate(
                "Fukuoka III n=10 seed 0",
                &instance.system::<10, Q>().expect("ten variables"),
                "The main overdetermined MQ benchmark, and the instance where capping pays.",
            ),
            None => {
                println!("`mq3-n10`: instance data absent; run `tools/fetch-mq-challenge.sh`.\n")
            }
        },
        "mq6-n10-specialized" => match load_mq("ToyExample-type6-n10-seed0") {
            Some((instance, answer)) => {
                let system = instance.system::<10, Q>().expect("ten variables");
                let surplus = instance.variables - instance.polynomials;
                if answer.len() < surplus {
                    println!("`mq6-n10-specialized`: no published answer to specialize at.\n");
                    return;
                }
                let assignments: Vec<(usize, Q)> =
                    (0..surplus).map(|i| (i, Q::new(answer[i]))).collect();
                let at_answer =
                    Specialization::<10, Q>::new(&assignments).expect("distinct indices");
                ablate(
                    "Fukuoka VI n=10, specialized",
                    &at_answer.apply(&system),
                    "A *different problem* from the published type VI instance, which is \
                     underdetermined — and not an overdetermined semiregular system, so nothing \
                     in HDF4's justification transfers to it.",
                )
            }
            None => println!(
                "`mq6-n10-specialized`: instance data absent; run `tools/fetch-mq-challenge.sh`.\n"
            ),
        },
        other => println!("unknown instance `{}`; `-- list` names them.\n", other),
    }
}

fn main() {
    let argument = std::env::args().nth(1);
    if argument.as_deref() == Some("list") {
        println!("instances:");
        for name in instances() {
            println!("  {}", name);
        }
        return;
    }

    println!("# M22 ablation");
    println!();
    println!(
        "Configuration: `F4Options::recommended()` as the baseline, with `profile_degrees`, \
         `max_matrix_columns = 60_000`, `max_live_bytes = 400 MB`, `max_batches = 20_000`, grevlex \
         throughout. Variable order is the generated layout on every row — M22-E measured it at \
         1.6x-1.7x, which would otherwise be attributed to whichever F4 strategy varied alongside \
         it. Reproduce with `cargo run --release --example m22_ablation`."
    );
    println!();
    println!(
        "**`total ms` is solve plus certification, and it is the only column a production decision \
         may use.** Every row's basis is asserted equal to the baseline's and certified: every \
         original generator reduces to zero modulo it, Buchberger's criterion holds, and it is \
         reduced. A differing basis would be a defect, so it is an assertion rather than a column."
    );
    println!();
    println!(
        "There is **no mutant row**: M22-D added no mutant mode, so §11.1's D and Combined would be \
         identical to A and C. `D = A` is printed to make the gap explicit rather than silent."
    );
    println!();

    match argument {
        Some(name) => run_instance(&name),
        None => {
            for name in instances() {
                run_instance(name);
            }
        }
    }
}
