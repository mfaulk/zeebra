//! Every M21 category in one run, with a machine-readable record per experiment.
//!
//! M21-I. Three categories, three different things they establish:
//!
//! | category | instances | what a result means |
//! |---|---|---|
//! | classical algebra | katsura, cyclic, planted | regression, and route selection |
//! | public MQ | Fukuoka type III and VI | external reproducibility |
//! | cryptographic | reduced-round Poseidon CICO | real structure, independent verification |
//!
//! Every record carries whether its answer was verified **independently of the solver**, and how.
//! For the classical systems that is evaluating the original generators; for MQ it is the imported
//! coefficient vectors and the published answer; for Poseidon it is running the permutation.
//!
//! ```text
//! cargo run --release --example cryptanalysis_experiment            # the table
//! cargo run --release --example cryptanalysis_experiment -- --json  # the records
//! ```
//!
//! The MQ rows need `tools/fetch-mq-challenge.sh`; without the data they are skipped and the run
//! says so rather than failing.

use std::{path::PathBuf, time::Duration};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::{PrimeFieldElement64, Zp2147483647},
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        research::{
            solve_slice, CicoInstance, ExperimentRecord, Json, MqInstance, Poseidon,
            PoseidonParameters, Specialization, KOALABEAR_PRIME,
        },
        solve_one_planned, F4Options, PlannedSolveOptions, SolveOptions, SolveOutcome, SolvePolicy,
    },
    util::peak_resident_bytes,
    FiniteField, KnownOrder, MultivariatePolynomial, Zero,
};

type F = Zp2147483647;
type G = PrimeFieldElement64<31>;
type K = PrimeFieldElement64<KOALABEAR_PRIME>;

fn options() -> PlannedSolveOptions {
    PlannedSolveOptions {
        policy: SolvePolicy::AutoWithFallback,
        budget: Default::default(),
        attempt: SolveOptions {
            // Bounded by shape rather than by the clock, so a failure is reproducible on another
            // machine. "It took too long here" is not a result.
            f4: F4Options {
                max_matrix_columns: 60_000,
                max_live_bytes: 400_000_000,
                ..F4Options::default()
            },
            ..SolveOptions::default()
        },
    }
}

/// Solve a system under the automatic policy and record what happened.
///
/// `verify` is handed any point found and must check it **without** the solver — that is the
/// column the whole run exists to fill.
fn run<const N: usize, FF: KnownOrder>(
    instance: &str,
    system: &[MultivariatePolynomial<N, FF>],
    transformations: Vec<String>,
    verification: &str,
    reproduce: &str,
    verify: impl Fn(&[FF; N]) -> bool,
) -> ExperimentRecord {
    let (outcome, plan) =
        solve_one_planned(system, &mut StdRng::seed_from_u64(20_260_104), &options());

    let mut record = ExperimentRecord::new(instance, "AutoWithFallback").with_plan(&plan);
    record.transformations = transformations;
    record.verification = verification.to_string();
    record.reproduce = reproduce.to_string();
    record.peak_resident_bytes = peak_resident_bytes();

    match outcome {
        Ok(SolveOutcome::Point(point)) => {
            record.outcome = Some(zeebra::grobner::OutcomeClass::Point);
            record.verified = Some(verify(&point));
        }
        Ok(SolveOutcome::NoBaseFieldPoint) => {
            record.outcome = Some(zeebra::grobner::OutcomeClass::NoBaseFieldPoint);
            // No answer to verify independently, which is `None` rather than `false`.
        }
        Ok(SolveOutcome::Inconsistent) => {
            record.outcome = Some(zeebra::grobner::OutcomeClass::Inconsistent);
        }
        Err(e) => record.failure = Some(e.to_string()),
    }
    record
}

/// Evaluating the original generators: independent of every basis and conversion between them.
fn satisfies<const N: usize, FF: FiniteField>(
    system: &[MultivariatePolynomial<N, FF>],
) -> impl Fn(&[FF; N]) -> bool + '_ {
    move |point| system.iter().all(|p| p.eval(point).is_zero())
}

fn classical(records: &mut Vec<ExperimentRecord>) {
    let point = |n: usize| -> Vec<F> { (0..n).map(|i| F::new(2 * i as u64 + 3)).collect() };

    let katsura6 = katsura::<6, F>();
    records.push(run(
        "katsura-6",
        &katsura6,
        vec![],
        "evaluate the original generators at the returned point",
        "cargo run --release --example cryptanalysis_experiment",
        satisfies(&katsura6),
    ));

    let katsura7 = katsura::<7, F>();
    records.push(run(
        "katsura-7",
        &katsura7,
        vec![],
        "evaluate the original generators at the returned point",
        "cargo run --release --example cryptanalysis_experiment",
        satisfies(&katsura7),
    ));

    let cyclic6 = cyclic::<6, F>();
    records.push(run(
        "cyclic-6",
        &cyclic6,
        vec![],
        "no base-field point, so nothing to verify",
        "cargo run --release --example cryptanalysis_experiment",
        satisfies(&cyclic6),
    ));

    let planted12 = planted::<12, F>(&point(12));
    records.push(run(
        "planted-12",
        &planted12,
        vec![],
        "evaluate the original generators at the returned point",
        "cargo run --release --example cryptanalysis_experiment",
        satisfies(&planted12),
    ));

    let cyclic4 = cyclic::<4, F>();
    records.push(run(
        "cyclic-4",
        &cyclic4,
        vec![],
        "positive-dimensional, so the zero-dimensional route does not apply",
        "cargo run --release --example cryptanalysis_experiment",
        satisfies(&cyclic4),
    ));
}

fn mq_directory() -> PathBuf {
    std::env::var("ZEEBRA_MQ_DIR")
        .unwrap_or_else(|_| "research/instances/mq".to_string())
        .into()
}

fn public_mq(records: &mut Vec<ExperimentRecord>) -> bool {
    let stem = mq_directory().join("ToyExample-type3-n10-seed0");
    let Ok(text) = std::fs::read_to_string(&stem) else {
        return false;
    };
    let answer = std::fs::read_to_string(format!("{}-answer", stem.display()))
        .map(|t| MqInstance::parse_answer(&t))
        .unwrap_or_default();
    let instance = MqInstance::parse(&text).expect("a published instance parses");
    let system = instance.system::<10, G>().expect("GF(31) at n = 10");
    let published: Vec<G> = answer.iter().copied().map(G::new).collect();

    records.push(
        run(
            "fukuoka-mq-III-n10-seed0",
            &system,
            vec![],
            "evaluate the imported coefficient vectors, and compare against the published answer",
            "tools/fetch-mq-challenge.sh && cargo run --release --example cryptanalysis_experiment",
            |point| system.iter().all(|p| p.eval(point).is_zero()) && point.to_vec() == published,
        )
        // The checksum, not the name: two runs can agree on the name and disagree on the file.
        .with_manifest_sha256("9436e45dbd4247f152681e954f1db19d92e8cf5e76b2bc35530bed74aae522ba"),
    );

    // Type VI is underdetermined, so it reaches an answer only through a specialization — and the
    // record says which one.
    let stem = mq_directory().join("ToyExample-type6-n10-seed0");
    if let Ok(text) = std::fs::read_to_string(&stem) {
        let instance = MqInstance::parse(&text).expect("parses");
        let system = instance.system::<10, G>().expect("GF(31) at n = 10");
        let free: Vec<usize> = (0..instance.variables - instance.polynomials).collect();
        let mut rng = StdRng::seed_from_u64(31);
        let slice = Specialization::<10, G>::seeded(&free, 0).expect("valid indices");
        let (outcome, plan) = solve_slice(&system, &slice, &options(), &mut rng);

        let mut record =
            ExperimentRecord::new("fukuoka-mq-VI-n10-seed0", "AutoWithFallback").with_plan(&plan);
        record.transformations = vec![format!(
            "specialize {} variables, seed 0: {}",
            free.len(),
            slice
        )];
        record.verification =
            "evaluate the imported coefficient vectors at the lifted point".to_string();
        record.reproduce =
            "tools/fetch-mq-challenge.sh && cargo run --release --example cryptanalysis_experiment"
                .to_string();
        record.peak_resident_bytes = peak_resident_bytes();
        match outcome {
            Ok(o) => match o.witness() {
                Some(w) => {
                    record.outcome = Some(zeebra::grobner::OutcomeClass::Point);
                    record.verified = Some(system.iter().all(|p| p.eval(&w).is_zero()));
                }
                None => {
                    // A dead slice. Recorded as a failure of *this slice*, not as an outcome for
                    // the system — which is the distinction M21-E exists for.
                    record.failure = Some(format!("{} (not evidence about the instance)", o));
                }
            },
            Err(e) => record.failure = Some(e.to_string()),
        }
        records.push(record);
    }

    true
}

fn cryptographic(records: &mut Vec<ExperimentRecord>) {
    // t = 2, R_F = 4, R_P = 0 is the largest reduced CICO instance that solves; see
    // docs/research/poseidon.md §4.
    let parameters = PoseidonParameters {
        prime: KOALABEAR_PRIME,
        alpha: 3,
        t: 2,
        r_f: 4,
        r_p: 0,
    };
    let poseidon = Poseidon::<K>::new(parameters).expect("R_F is even");
    let free = [K::new(1_000)];
    let instance = CicoInstance::planted(
        poseidon,
        1,
        &[K::new(0xC0_9DE4)],
        &free,
        Some(PoseidonParameters::bounty_cico()),
    )
    .expect("the right widths");
    let system = instance.system::<9>().expect("nine variables");

    let mut record = run(
        "poseidon-cico-t2-rf4-rp0-planted",
        &system,
        vec![format!(
            "reduced from {} to {}; planted target",
            PoseidonParameters::bounty_cico(),
            parameters
        )],
        "run the Poseidon permutation on the recovered input and compare its output to the target",
        "cargo run --release --example cryptanalysis_experiment",
        |point| {
            // Through the permutation, not the system: a generator bug cannot make this pass.
            instance
                .is_solution(&point[..instance.free_inputs()])
                .unwrap_or(false)
        },
    );
    record.configuration = "AutoWithFallback (reduced instance)".to_string();
    records.push(record);
}

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        format!("{}…", s.chars().take(width - 1).collect::<String>())
    }
}

fn print_table(records: &[ExperimentRecord]) {
    println!(
        "| {:<34} | {:>3} | {:>9} | {:>8} | {:<9} | {:<36} |",
        "instance", "att", "total ms", "est MB", "verified", "outcome"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|",
        "-".repeat(36),
        "-".repeat(5),
        "-".repeat(11),
        "-".repeat(10),
        "-".repeat(11),
        "-".repeat(38)
    );
    for r in records {
        let outcome = match (&r.outcome, &r.failure) {
            (Some(class), _) => format!("{:?}", class),
            (None, Some(failure)) => failure.clone(),
            (None, None) => "—".to_string(),
        };
        println!(
            "| {:<34} | {:>3} | {:>9} | {:>8} | {:<9} | {:<36} |",
            truncate(&r.instance, 34),
            r.attempts.len(),
            format!("{:.1}", millis(r.elapsed)),
            format!("{:.1}", r.estimated_peak_bytes as f64 / 1e6),
            match r.verified {
                Some(true) => "yes",
                Some(false) => "NO",
                None => "n/a",
            },
            truncate(&outcome, 36),
        );
    }
}

fn main() {
    let json = std::env::args().any(|a| a == "--json");
    let mut records: Vec<ExperimentRecord> = Vec::new();

    classical(&mut records);
    let have_mq = public_mq(&mut records);
    cryptographic(&mut records);

    if json {
        // One array, so the output is a single JSON document.
        let document = Json::Array(records.iter().map(|r| r.to_json()).collect());
        println!("{}", document.to_json());
        return;
    }

    println!("# M21-I: every category, one run");
    println!();
    print_table(&records);
    println!();

    if !have_mq {
        println!(
            "The public-MQ rows were skipped: no instance data in {}.",
            mq_directory().display()
        );
        println!("The Fukuoka files are \"All Rights Reserved\" and are not redistributed here;");
        println!("fetch them with tools/fetch-mq-challenge.sh.");
        println!();
    }

    let answered = records.iter().filter(|r| r.outcome.is_some()).count();
    let verified = records.iter().filter(|r| r.verified == Some(true)).count();
    let unverified = records.iter().filter(|r| r.verified == Some(false)).count();
    println!(
        "{} of {} experiments reached a mathematical outcome; {} points were verified \
         independently of the solver and {} failed verification.",
        answered,
        records.len(),
        verified,
        unverified
    );
    assert_eq!(unverified, 0, "a point failed independent verification");
    println!();
    println!("`verified = n/a` is not a gap: those rows reached an answer with no point to check");
    println!("(no base-field point, positive-dimensional, inconsistent), or reached no answer at");
    println!("all. A point that failed verification would print NO and abort the run.");
    println!();
    println!(
        "`est MB` is an estimate of the representation. The measured process figure is in the"
    );
    println!("JSON as `measured_peak_resident_bytes` — a separate key, because on katsura-7 under");
    println!("lex the two differ by 4.1x.");
    println!();
    println!("Records: cargo run --release --example cryptanalysis_experiment -- --json");
}
