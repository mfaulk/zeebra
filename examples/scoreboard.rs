//! The scoreboard runner: one record per registered problem attempted, with the stages apart.
//!
//! M23-A. Three tiers, because a scoreboard that runs everything on every change stops being run:
//!
//! ```text
//! cargo run --release --example scoreboard                 # smoke: three surrogates, under 1 s
//! cargo run --release --example scoreboard -- stable       # adds the MQ instances and the row
//!                                                         # that crosses the column budget
//! cargo run --release --example scoreboard -- frontier     # adds the full-width rows (M23-B)
//! cargo run --release --example scoreboard -- smoke --write
//! ```
//!
//! Without `--write` nothing is written and the tables go to standard output; with it,
//! `research/scoreboard/` is updated — `challenges/` emitted from the registry, one record per run
//! under `runs/`, the accumulated `results/history.json`, and the rendered `SCOREBOARD.md`.
//!
//! **Every stage is timed separately.** The pipeline is run as F4, then the conversion, then the
//! univariate search, rather than through `solve_one_planned`, precisely so that the cost can be
//! attributed: the EF program's Gröbner request is for per-stage cost and memory, and M20 measured
//! that on a wide field the cost is not in the matrices. The price is that the planner's route
//! choice is not exercised here; `solve_baseline` and `cryptanalysis_ladder` cover that.
//!
//! Every Poseidon witness is verified by **running the permutation**, and every MQ witness by
//! evaluating the published coefficient vectors — never by re-evaluating the system that was
//! solved, so no bug in a generator or a transformation can make a verification pass.

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        classify_ideal, f4_reported, fglm_to_lex_with_options,
        research::{
            challenge, dispatch_cico, registry, ChallengeManifest, ChallengeParameters,
            CicoVisitor, Environment, GrobnerFrontier, Json, Limit, MqInstance, MqVisitor,
            RunOutcome, RunRecord, Scoreboard, Stage, StageCost, KOALABEAR_PRIME,
        },
        solve_from_lex_basis, F4Options, FglmOptions, IdealClass, SolveOptions, SolveOutcome,
    },
    MonomialOrder, MultivariatePolynomial, Zero,
};

type K = PrimeFieldElement64<KOALABEAR_PRIME>;
type Q = PrimeFieldElement64<31>;

const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// The resource policy, stated once. Column- and byte-bounded rather than time-bounded, so that a
/// failure is reproducible rather than "it took too long on this machine".
fn f4_options() -> F4Options {
    F4Options {
        profile_degrees: true,
        max_matrix_columns: 60_000,
        max_live_bytes: 400_000_000,
        ..F4Options::default()
    }
}

fn policy() -> String {
    "grevlex F4 then FGLM then univariate search; 60000 columns, 400 MB live, degree profiling on"
        .to_string()
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let write = arguments.iter().any(|a| a == "--write");
    let tier = arguments
        .iter()
        .find(|a| !a.starts_with("--"))
        .cloned()
        .unwrap_or_else(|| "smoke".to_string());

    let registry = registry();
    let environment = detect_environment();
    let mut board = Scoreboard::new();

    println!("# Scoreboard run: tier {}\n", tier);
    println!("- machine: {}", environment.machine);
    println!("- build:   {}", environment.build);
    println!("- commit:  {}", environment.commit);
    println!("- policy:  {}\n", environment.policy);

    // Tier 1: the three surrogates that finish. Under a second together, and every one of them
    // has a witness known to exist, so a failure here is a defect rather than a hard instance.
    for id in [
        "poseidon-t2-rf2-rp0-planted",
        "poseidon-t2-rf2-rp2-planted",
        "poseidon-t2-rf4-rp0-planted",
    ] {
        let manifest = challenge(id).expect("registered");
        let record = run_cico(&manifest, &environment);
        report(&record);
        board.add(record, &registry).expect("a registered problem");
    }

    if tier == "stable" || tier == "frontier" {
        // The row that crosses the column budget, which takes ~19 s and is the only coverage of
        // the stopped-at-a-limit path outside the unit tests. Not in the smoke tier for exactly
        // that reason: a known-failing row should not dominate the check that runs on every
        // change.
        let manifest = challenge("poseidon-t3-rf2-rp1-planted").expect("registered");
        let record = run_cico(&manifest, &environment);
        report(&record);
        board.add(record, &registry).expect("a registered problem");

        for id in ["fukuoka-mq-III-n10-seed0", "fukuoka-mq-III-n15-seed0"] {
            let manifest = challenge(id).expect("registered");
            match run_mq(&manifest, &environment) {
                Some(record) => {
                    report(&record);
                    board.add(record, &registry).expect("a registered problem");
                }
                None => println!(
                    "- {} skipped: run tools/fetch-mq-challenge.sh for the instance files",
                    id
                ),
            }
        }
    }

    if tier == "frontier" {
        println!(
            "\nThe full-width rows are M23-B's; this runner has the harness for them and does not \
             yet drive it.\n"
        );
    }

    println!("\n{}", board.to_markdown(&registry));

    if write {
        let root = PathBuf::from("research/scoreboard");
        write_tree(&root, &board, &registry);
        println!("written to {}", root.display());
    } else {
        println!("(nothing written; pass --write to update research/scoreboard/)");
    }
}

/// One line per run, so an interrupted session is still legible.
fn report(record: &RunRecord) {
    println!(
        "- {:<32} {:<18} {:>9.1} ms  {}",
        record.challenge,
        record.formulation,
        record.elapsed().as_secs_f64() * 1e3,
        record.outcome
    );
}

/// Run one registered CICO problem through the staged pipeline.
fn run_cico(manifest: &ChallengeManifest, environment: &Environment) -> RunRecord {
    let at = Instant::now();
    let instance = manifest.cico_instance::<K>().expect("a registered problem");
    let generation = at.elapsed();

    let mut record = dispatch_cico::<K, _>(
        manifest,
        Solve {
            manifest,
            instance: &instance,
            generation,
        },
    )
    .expect("a compiled dimension");
    record.environment = environment.clone();
    record.reproduce = format!(
        "cargo run --release --example scoreboard -- smoke  # {}",
        manifest.id
    );
    record
}

/// The staged pipeline at one compiled dimension.
struct Solve<'a> {
    manifest: &'a ChallengeManifest,
    instance: &'a zeebra::grobner::research::CicoInstance<K>,
    generation: Duration,
}

impl CicoVisitor<K> for Solve<'_> {
    type Output = RunRecord;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, K>]) -> RunRecord {
        let mut record = RunRecord::new(self.manifest, "as generated");
        record.stages.push(
            StageCost::new(Stage::Generation, self.generation)
                .with("variables", N as i64)
                .with("equations", system.len() as i64),
        );

        let (outcome, stages, frontier) = staged_solve(system, |point| {
            // The verification that matters: rebuild the input state and run the permutation.
            let free: Vec<K> = point[..self.instance.free_inputs()].to_vec();
            self.instance.is_solution(&free).unwrap_or(false)
        });
        record.outcome = outcome;
        record.stages.extend(stages);
        record.frontier = Some(frontier);
        record.verification =
            "CicoInstance::is_solution, which runs permutation_plus_linear on the recovered inputs"
                .to_string();
        record
    }
}

/// Run one registered MQ problem, if its file is present.
fn run_mq(manifest: &ChallengeManifest, environment: &Environment) -> Option<RunRecord> {
    let ChallengeParameters::MqSystem { kind, n, .. } = manifest.parameters else {
        return None;
    };
    let directory = std::env::var("ZEEBRA_MQ_DIR").unwrap_or("research/instances/mq".to_string());
    let name = format!(
        "ToyExample-type{}-n{}-seed0",
        if kind == "III" { 3 } else { 6 },
        n
    );
    let text = fs::read_to_string(Path::new(&directory).join(&name)).ok()?;
    let answer = fs::read_to_string(Path::new(&directory).join(format!("{}-answer", name))).ok()?;

    let at = Instant::now();
    let instance = MqInstance::parse(&text).expect("a published instance");
    let published = MqInstance::parse_answer(&answer);
    let generation = at.elapsed();

    let mut record = instance
        .dispatch::<Q, _>(SolveMq {
            manifest,
            instance: &instance,
            published: &published,
            generation,
        })
        .expect("a supported dimension");
    record.environment = environment.clone();
    record.reproduce = format!(
        "tools/fetch-mq-challenge.sh && cargo run --release --example scoreboard -- stable  # {}",
        manifest.id
    );
    Some(record)
}

/// The staged pipeline for an MQ instance.
struct SolveMq<'a> {
    manifest: &'a ChallengeManifest,
    instance: &'a MqInstance,
    published: &'a [u64],
    generation: Duration,
}

impl MqVisitor<Q> for SolveMq<'_> {
    type Output = RunRecord;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, Q>]) -> RunRecord {
        let mut record = RunRecord::new(self.manifest, "as published");
        record.stages.push(
            StageCost::new(Stage::Generation, self.generation)
                .with("variables", N as i64)
                .with("equations", system.len() as i64),
        );

        // The independent check is against the *published* coefficient vectors, reconstructed from
        // the file rather than from the system that was solved.
        let reconstructed = self
            .instance
            .system::<N, Q>()
            .expect("the same instance parses twice");
        let (outcome, stages, frontier) = staged_solve(system, |point| {
            reconstructed
                .iter()
                .all(|polynomial| polynomial.eval(point) == Q::zero())
        });
        record.outcome = outcome;
        record.stages.extend(stages);
        record.frontier = Some(frontier);
        record.verification = format!(
            "evaluated against the published coefficient vectors; the published answer is {:?}",
            &self.published[..self.published.len().min(4)]
        );
        record
    }
}

/// F4, then the conversion, then the univariate search, each timed.
///
/// `verify` is the problem's own independent check, which is what decides between a witness and a
/// defect. A candidate that fails it is [`RunOutcome::WitnessRejected`] — an absence and a defect
/// are different facts.
fn staged_solve<const N: usize, F: zeebra::KnownOrder>(
    system: &[MultivariatePolynomial<N, F>],
    verify: impl Fn(&[F; N]) -> bool,
) -> (RunOutcome, Vec<StageCost>, GrobnerFrontier) {
    let mut stages = Vec::new();

    let at = Instant::now();
    let (basis, statistics) = f4_reported(system, GREVLEX, &f4_options());
    let grobner_elapsed = at.elapsed();
    let completed = basis.is_ok();
    let mut frontier =
        GrobnerFrontier::of(&statistics, completed).with_profile(&statistics.degrees);
    stages.push(
        StageCost::new(Stage::Grobner, grobner_elapsed)
            .with("max_matrix_rows", statistics.max_matrix_rows as i64)
            .with("max_matrix_columns", statistics.max_matrix_columns as i64)
            .with("max_pair_degree", statistics.max_pair_degree as i64)
            .with("pairs_reduced", statistics.pairs_reduced as i64)
            .with_estimated_bytes(statistics.max_estimated_bytes),
    );

    let basis = match basis {
        Ok(basis) => basis,
        Err(error) => {
            return (
                RunOutcome::StoppedAtLimit(Limit {
                    resource: resource_of(&error),
                    detail: error.to_string(),
                    degree: Some(statistics.max_pair_degree),
                    last_completed_stage: Stage::Generation,
                }),
                stages,
                frontier,
            )
        }
    };

    if classify_ideal(&basis, GREVLEX) != IdealClass::ZeroDimensional {
        // Not a limit and not a witness: the ideal is positive-dimensional, so the zero-dimensional
        // route does not apply and saying "no solution" would be wrong.
        return (RunOutcome::BasisOnly, stages, frontier);
    }

    let at = Instant::now();
    let converted = fglm_to_lex_with_options(&basis, GREVLEX, &FglmOptions::default());
    let conversion_elapsed = at.elapsed();
    let (lex, conversion) = match converted {
        Ok(pair) => pair,
        Err(error) => {
            stages.push(StageCost::new(Stage::Conversion, conversion_elapsed));
            return (
                RunOutcome::StoppedAtLimit(Limit {
                    resource: "conversion".to_string(),
                    detail: error.to_string(),
                    degree: Some(statistics.max_pair_degree),
                    last_completed_stage: Stage::Grobner,
                }),
                stages,
                frontier,
            );
        }
    };
    frontier = frontier.with_quotient_dimension(conversion.quotient_dimension);
    stages.push(
        StageCost::new(Stage::Conversion, conversion_elapsed)
            .with("quotient_dimension", conversion.quotient_dimension as i64)
            .with_estimated_bytes(conversion.estimated_bytes()),
    );

    let at = Instant::now();
    let searched = solve_from_lex_basis(
        &lex,
        system,
        &SolveOptions::default(),
        &mut StdRng::seed_from_u64(1),
    );
    let search_elapsed = at.elapsed();
    stages.push(
        StageCost::new(Stage::Univariate, search_elapsed)
            .with("lex_basis_elements", lex.len() as i64),
    );

    let outcome = match searched {
        Ok((SolveOutcome::Point(point), _)) => {
            let at = Instant::now();
            let verified = verify(&point);
            stages.push(StageCost::new(Stage::Verification, at.elapsed()));
            if verified {
                RunOutcome::VerifiedWitness
            } else {
                RunOutcome::WitnessRejected
            }
        }
        Ok((SolveOutcome::NoBaseFieldPoint, _)) => RunOutcome::NoBaseFieldPoint,
        Ok((SolveOutcome::Inconsistent, _)) => RunOutcome::Inconsistent,
        Err(error) => RunOutcome::StoppedAtLimit(Limit {
            resource: "univariate search".to_string(),
            detail: error.to_string(),
            degree: None,
            last_completed_stage: Stage::Conversion,
        }),
    };
    (outcome, stages, frontier)
}

/// Which bound bound, as a stable name a consumer can key on.
fn resource_of(error: &zeebra::grobner::F4Error) -> String {
    use zeebra::grobner::F4Error::*;
    match error {
        TooManyRows { .. } => "max_matrix_rows",
        TooManyColumns { .. } => "max_matrix_columns",
        TooManyNonzeros { .. } => "max_live_nonzeros",
        TooManyLiveBytes { .. } => "max_live_bytes",
        TooManyBatches { .. } => "max_batches",
        TooManyBasisElements { .. } => "max_basis_elements",
        InvalidOptions { .. } => "invalid_options",
        _ => "other",
    }
    .to_string()
}

/// The machine and build this measurement came from.
///
/// `git rev-parse` rather than a build-time constant: this is an example, and a comparison needs
/// to know which tree produced the number more than it needs to avoid a subprocess.
fn detect_environment() -> Environment {
    let commit = Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());
    let machine = std::env::var("ZEEBRA_MACHINE").unwrap_or_else(|_| {
        Command::new("hostname")
            .output()
            .ok()
            .and_then(|out| String::from_utf8(out.stdout).ok())
            .map(|s| s.trim().to_string())
            .unwrap_or_else(|| "unknown".to_string())
    });
    Environment {
        commit,
        machine,
        cpu: format!(
            "{} logical, affinity {}",
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(0),
            std::env::var("ZEEBRA_AFFINITY").unwrap_or_else(|_| "unpinned".to_string())
        ),
        build: format!(
            "{}, RUSTFLAGS={}",
            if cfg!(debug_assertions) {
                "debug"
            } else {
                "release"
            },
            std::env::var("RUSTFLAGS").unwrap_or_else(|_| "default".to_string())
        ),
        policy: policy(),
    }
}

/// Write the scoreboard tree: the registry, the runs, the accumulated history, the Markdown.
fn write_tree(root: &Path, board: &Scoreboard, registry: &[ChallengeManifest]) {
    fs::create_dir_all(root.join("challenges")).expect("a writable directory");
    fs::create_dir_all(root.join("runs")).expect("a writable directory");
    fs::create_dir_all(root.join("results")).expect("a writable directory");

    // The registry, emitted rather than hand-maintained, so the JSON cannot drift from the code.
    for manifest in registry {
        fs::write(
            root.join("challenges")
                .join(format!("{}.json", manifest.id)),
            manifest.to_json().to_json() + "\n",
        )
        .expect("a writable file");
    }

    let runs = board.to_json(registry).expect("every run is registered");
    for run in board.runs() {
        let name = format!(
            "{}--{}--{}.json",
            run.challenge,
            run.formulation.replace(' ', "-"),
            run.environment.commit
        );
        let manifest = registry
            .iter()
            .find(|c| c.id == run.challenge)
            .expect("checked on add");
        fs::write(
            root.join("runs").join(name),
            run.to_json(manifest).to_json() + "\n",
        )
        .expect("a writable file");
    }

    // History accumulates: read what is there, append, write it back. A writer with no reader
    // would mean losing every earlier milestone's results on each run.
    let history_path = root.join("results").join("history.json");
    let mut entries: Vec<Json> = match fs::read_to_string(&history_path) {
        Ok(text) => Json::parse(&text)
            .expect("the history this program wrote")
            .get("runs")
            .map(|runs| runs.items().to_vec())
            .unwrap_or_default(),
        Err(_) => Vec::new(),
    };
    entries.extend(
        runs.get("runs")
            .map(|r| r.items().to_vec())
            .unwrap_or_default(),
    );
    fs::write(
        &history_path,
        Json::object([
            ("schema", Json::int(RunRecord::SCHEMA)),
            ("run_count", Json::size(entries.len())),
            ("runs", Json::Array(entries)),
        ])
        .to_json()
            + "\n",
    )
    .expect("a writable file");

    fs::write(
        root.join("results").join("best.json"),
        Json::object([(
            "best",
            Json::Array(
                board
                    .best()
                    .values()
                    .map(|run| {
                        let manifest = registry
                            .iter()
                            .find(|c| c.id == run.challenge)
                            .expect("checked on add");
                        run.to_json(manifest)
                    })
                    .collect(),
            ),
        )])
        .to_json()
            + "\n",
    )
    .expect("a writable file");

    fs::write(root.join("SCOREBOARD.md"), board.to_markdown(registry)).expect("a writable file");
}
