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
//! cargo run --release --example scoreboard -- render --write   # re-render, measure nothing
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
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::{
        atomic::{AtomicU64, AtomicUsize, Ordering},
        mpsc, Arc,
    },
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::{Gf256Mq, PrimeFieldElement64},
    grobner::{
        classify_ideal,
        f4::symbolic::MonicBasis,
        f4_observed_reported, f4_reported, fglm_to_lex_with_options,
        research::{
            challenge, colliding_run_file, dispatch_cico, eliminate_affine, registry, Campaign,
            ChallengeManifest, ChallengeParameters, CicoVisitor, Comparison, Environment,
            GrobnerFrontier, Json, Limit, MqField, MqInstance, MqVisitor, RoundLayout, RunOutcome,
            RunRecord, Scoreboard, Specialization, Stage, StageCost, BEST_CONTRACT,
            HISTORY_CONTRACT, KOALABEAR_PRIME, SOLVED_CONTRACT,
        },
        solve_from_lex_basis, BatchObserver, CriticalPair, F4Options, FglmOptions, IdealClass,
        SolveOptions, SolveOutcome,
    },
    util::peak_resident_bytes,
    MonomialOrder, MultivariatePolynomial,
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

/// Every row this runner records is over a `PrimeFieldElement64`, so the live allowance is one
/// number for the whole board and [`policy`] can be a single string.
///
/// Only honest while that holds: the effective live budget is `min(max_live_nonzeros,
/// max_live_bytes / size_of::<(usize, F)>())`, so a wider field on the board would have a
/// *smaller* allowance than the one the policy quotes. The assertion below is a compile error
/// rather than a test, because a stale policy string is exactly the defect #469 records and it
/// must not be skippable.
type PolicyField = Q;

const _: () = assert!(
    size_of::<(usize, K)>() == size_of::<(usize, PolicyField)>(),
    "every field on this board must have the entry width `policy()` is rendered at"
);

// And GF(2^8), since #510 put a type V row on the board: an extension field is a *narrower*
// element than either prime field, so a sparse entry pads to the same 16 bytes and the live
// allowance `policy()` quotes is the one that binds. If a field ever lands here that does not,
// this stops the build rather than letting every record carry the wrong policy string.
const _: () = assert!(
    size_of::<(usize, Gf256Mq)>() == size_of::<(usize, PolicyField)>(),
    "every field on this board must have the entry width `policy()` is rendered at"
);

/// The resource policy as prose, **derived from [`f4_options`]** rather than written beside it.
///
/// It used to be written out, and said "400 MB live" where the effective cap was 320 MB — the byte
/// budget was set and the entry budget left at its default, and the limit is the `min` of the two
/// (#322), so the 400 MB was slack that never bound. Every record carried the overstatement, and a
/// reader reconciling a `stopped_at_limit` row against it got the wrong number to compare with
/// (#469). Deriving it is what stops that recurring.
fn policy() -> String {
    let options = f4_options();
    format!(
        "grevlex F4 then FGLM then univariate search; {} columns, {}, degree profiling on",
        options.max_matrix_columns,
        options.live_budget_policy::<PolicyField>()
    )
}

/// How many rows this process has recorded, so that a measured peak says what it covers.
///
/// `VmHWM` is a **process** high-water mark. The `row`, `mq` and `campaign` tiers run one row per
/// process — `tools/scoreboard.sh`'s ladder does so deliberately — and only there is the figure
/// attributable to the row it is recorded against. The multi-row tiers get the same figure on
/// every row, and it is a ceiling over all of them; the count is what lets a reader tell the two
/// apart instead of having to know which tier produced the file.
static ROWS_RECORDED: AtomicUsize = AtomicUsize::new(0);

/// Attach the measured process peak to `record`, then add it to `board`.
///
/// Called at every point a row is recorded, so that no tier can acquire a row without a
/// measurement or without the count that qualifies it. The estimate it is read against is already
/// in `record.frontier.peak_estimated_bytes`, which is what makes
/// `RunRecord::measured_to_estimated_ratio` recoverable from one record — the whole point of
/// populating both.
fn add_measured(board: &mut Scoreboard, mut record: RunRecord, registry: &[ChallengeManifest]) {
    let rows = ROWS_RECORDED.fetch_add(1, Ordering::Relaxed) + 1;
    // Both fields or neither: the count is a property of the measurement, and a count without one
    // would qualify nothing.
    record.measured_peak_resident_bytes = peak_resident_bytes().map(|bytes| bytes as usize);
    record.measured_peak_rows_in_process = record
        .measured_peak_resident_bytes
        .is_some()
        .then_some(rows);
    board.add(record, registry).expect("a registered problem");
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let write = arguments.iter().any(|a| a == "--write");
    let positional: Vec<&String> = arguments.iter().filter(|a| !a.starts_with("--")).collect();
    let tier = positional
        .first()
        .map(|s| s.to_string())
        .unwrap_or_else(|| "smoke".to_string());

    let registry = registry();
    let environment = detect_environment();
    let mut board = Scoreboard::new();

    // Re-render the tables from the accumulated history, measuring nothing.
    //
    // `SCOREBOARD.md` and `best.json` are rendered from the history rather than from the current
    // process's board, so any writer that appends a record leaves them stale — and
    // `examples/resultant_cico --write` is one: it appends a run and tells the operator to "rerun
    // tools/scoreboard.sh to re-render the tables", which until now meant re-measuring rows to
    // refresh a table that is a pure function of a file already on disk.
    //
    // An **empty** board is the whole mechanism: `write_tree` appends `board.runs()` to the
    // history and then renders from the accumulation, so contributing no runs preserves the
    // append-only contract exactly — nothing is added, no position changes, and
    // `Scoreboard::verified_somehow`'s tie-break on recording order still reads what it read
    // before.
    if tier == "render" {
        if !write {
            println!("`render` only writes; pass --write to re-render research/scoreboard/");
            return;
        }
        write_tree(
            &PathBuf::from("research/scoreboard"),
            &Scoreboard::new(),
            &registry,
        );
        println!("re-rendered research/scoreboard/ from the accumulated history; no runs added");
        return;
    }

    // One registered problem, with the frontier budget and a wall-clock supervisor, then exit.
    //
    // Its own process on purpose. F4 has no cooperative time check, so a run that outlasts the
    // supervisor can only be stopped by leaving its thread behind and exiting — which is fine once
    // per process and unacceptable nine times in one.
    if tier == "row" {
        let id = positional
            .get(1)
            .expect("usage: scoreboard row <challenge-id> [--slice <seed>] [--write]");
        let slice = arguments
            .iter()
            .position(|a| a == "--slice")
            .and_then(|at| arguments.get(at + 1))
            .map(|seed| seed.parse::<u64>().expect("a seed"));
        let manifest = challenge(id).unwrap_or_else(|| panic!("{} is not registered", id));
        let formulation = arguments
            .iter()
            .position(|a| a == "--layout")
            .and_then(|at| arguments.get(at + 1))
            .map(|name| {
                Formulation::named(name).unwrap_or_else(|| panic!("no formulation named {}", name))
            })
            .unwrap_or(Formulation::AsGenerated);
        let wall = wall_clock();
        println!("# {} ({}), wall clock {:?}", id, manifest.class, wall);
        println!("- policy: {}\n", frontier_policy());
        let record = run_frontier_formulation(&manifest, &environment, slice, wall, formulation);
        report(&record);
        add_measured(&mut board, record, &registry);
        if write {
            write_tree(&PathBuf::from("research/scoreboard"), &board, &registry);
            println!("appended to research/scoreboard/");
        }
        // The supervisor may have left a thread running; nothing else is pending, so stop here
        // rather than waiting for it.
        std::process::exit(0);
    }

    // One published MQ instance, with a slice campaign when it is underdetermined.
    if tier == "mq" {
        let id = positional
            .get(1)
            .expect("usage: scoreboard mq <challenge-id> [--seeds N] [--write]");
        let seeds: u64 = arguments
            .iter()
            .position(|a| a == "--seeds")
            .and_then(|at| arguments.get(at + 1))
            .and_then(|n| n.parse().ok())
            .unwrap_or(8);
        let manifest = challenge(id).unwrap_or_else(|| panic!("{} is not registered", id));
        let wall = wall_clock();
        println!("# {} ({})", id, manifest.class);
        println!("- policy: {}\n", frontier_policy());

        let records = run_mq_rows(&manifest, &environment, seeds, wall);
        if records.is_empty() {
            println!("skipped: run tools/fetch-mq-challenge.sh for the instance files");
            std::process::exit(0);
        }
        for record in records {
            report(&record);
            add_measured(&mut board, record, &registry);
        }
        if write {
            write_tree(&PathBuf::from("research/scoreboard"), &board, &registry);
            println!("\nappended to research/scoreboard/");
        }
        std::process::exit(0);
    }

    // Every formulation of one problem, compared. The identity digest is the same for all of
    // them — a relabelling is a ring isomorphism and an affine elimination generates the same
    // ideal — which is exactly why `Comparison::of` agrees to compare them.
    if tier == "formulations" {
        let id = positional
            .get(1)
            .expect("usage: scoreboard formulations <challenge-id> [--slice seed] [--write]");
        let slice = arguments
            .iter()
            .position(|a| a == "--slice")
            .and_then(|at| arguments.get(at + 1))
            .map(|seed| seed.parse::<u64>().expect("a seed"));
        let manifest = challenge(id).unwrap_or_else(|| panic!("{} is not registered", id));
        let wall = wall_clock();
        println!("# formulations of {} ({})", id, manifest.class);
        println!("- policy: {}\n", frontier_policy());

        let mut records = Vec::new();
        for formulation in [
            Formulation::AsGenerated,
            Formulation::LastRoundFirst,
            Formulation::FreeInputsLast,
            Formulation::AffineProjected,
        ] {
            let record =
                run_frontier_formulation(&manifest, &environment, slice, wall, formulation);
            report(&record);
            records.push(record);
        }

        println!("\n## Against the generated layout\n");
        let baseline = records[0].clone();
        for candidate in records.iter().skip(1) {
            match Comparison::of(&baseline, candidate) {
                Ok(comparison) => {
                    println!("- {}", comparison);
                    for caveat in &comparison.caveats {
                        println!("  - caveat: {}", caveat);
                    }
                }
                Err(error) => println!("- refused: {}", error),
            }
        }

        for record in records {
            add_measured(&mut board, record, &registry);
        }
        if write {
            write_tree(&PathBuf::from("research/scoreboard"), &board, &registry);
            println!("\nappended to research/scoreboard/");
        }
        std::process::exit(0);
    }

    // A specialization campaign over one problem: several slices from precommitted seeds, each
    // recorded, plus a summary that reports the slices which found nothing.
    if tier == "campaign" {
        let id = positional
            .get(1)
            .expect("usage: scoreboard campaign <challenge-id> [--seeds N] [--write]");
        let seeds: u64 = arguments
            .iter()
            .position(|a| a == "--seeds")
            .and_then(|at| arguments.get(at + 1))
            .and_then(|n| n.parse().ok())
            .unwrap_or(8);
        let manifest = challenge(id).unwrap_or_else(|| panic!("{} is not registered", id));
        let wall = wall_clock();
        println!("# campaign on {} ({})", id, manifest.class);
        println!("- {} slices, seeds 0..{}", seeds, seeds);
        println!("- policy: {}\n", frontier_policy());

        let mut campaign = Campaign {
            fixed: manifest
                .cico_instance::<K>()
                .expect("a registered problem")
                .free_inputs()
                - 2,
            ..Campaign::default()
        };
        let at = Instant::now();
        for seed in 0..seeds {
            let record = run_frontier_row(&manifest, &environment, Some(seed), wall);
            report(&record);
            tally(&mut campaign, seed, &record.outcome);
            add_measured(&mut board, record, &registry);
        }
        campaign.total = at.elapsed();

        // The summary. Its outcome is a witness only if some slice produced one, and the campaign
        // beside it carries the trials that did not — which is what stops a lucky slice from being
        // quoted as the cost of a solution.
        let mut summary = RunRecord::new(&manifest, format!("campaign over {} slices", seeds));
        summary.environment = Environment {
            policy: frontier_policy(),
            ..environment.clone()
        };
        summary.outcome = campaign_outcome(&campaign);
        summary.verification =
            "every witness checked by running permutation_plus_linear on the recovered inputs"
                .to_string();
        summary.transformations = vec![format!(
            "{} slices, each fixing {} free inputs at a seeded value",
            seeds, campaign.fixed
        )];
        summary.stages = vec![StageCost::new(Stage::Grobner, campaign.total)];
        summary.reproduce = format!(
            "ZEEBRA_WALL_SECONDS={} tools/scoreboard.sh campaign {} --seeds {}",
            wall.as_secs(),
            manifest.id,
            seeds
        );
        report_campaign(&campaign);
        summary.campaign = Some(campaign);
        report(&summary);
        add_measured(&mut board, summary, &registry);

        if write {
            write_tree(&PathBuf::from("research/scoreboard"), &board, &registry);
            println!("appended to research/scoreboard/");
        }
        std::process::exit(0);
    }

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
        add_measured(&mut board, record, &registry);
    }

    if tier == "stable" || tier == "frontier" {
        // The row that crosses the column budget, which takes ~19 s and is the only coverage of
        // the stopped-at-a-limit path outside the unit tests. Not in the smoke tier for exactly
        // that reason: a known-failing row should not dominate the check that runs on every
        // change.
        let manifest = challenge("poseidon-t3-rf2-rp1-planted").expect("registered");
        let record = run_cico(&manifest, &environment);
        report(&record);
        add_measured(&mut board, record, &registry);

        for id in ["fukuoka-mq-III-n10-seed0", "fukuoka-mq-III-n15-seed0"] {
            let manifest = challenge(id).expect("registered");
            match run_mq(&manifest, &environment) {
                Some(record) => {
                    report(&record);
                    add_measured(&mut board, record, &registry);
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
            "\nThe full-width rows run one per process, so that a wall-clock supervisor can stop \
             one without leaving nine threads behind: `tools/scoreboard.sh ladder --write`, or \
             `scoreboard row <id> [--slice <seed>]` for one of them.\n"
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

        let (outcome, stages, frontier) = staged_solve(system, false, |point| {
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

/// The frontier budget: wider than the stable one, and stated.
///
/// Ten times the columns, a byte cap set high enough not to bind, and a batch cap so that a
/// computation staying under both still stops. The bound that **actually binds** on these rows is
/// the default live-entry cap of 20,000,000 — about 320 MB at this field's 16 bytes an entry — and
/// that is deliberate: an entry count is reproducible on any machine, where a wall-clock stop is a
/// fact about this one. The supervisor below is a backstop, not the budget.
fn frontier_options() -> F4Options {
    F4Options {
        profile_degrees: true,
        // The cooperative time budget, set from `ZEEBRA_WALL_SECONDS` like the supervisor's
        // backstop but deliberately **shorter**, so the cooperative check wins the race. Losing it
        // costs the whole frontier: the `recv_timeout` arm cannot reach the `(Result,
        // F4Statistics)` tuple the abandoned thread still owns, so it emits an empty frontier with
        // every group-B counter zeroed. The cooperative stop *returns*, and a return carries the
        // statistics.
        //
        // One batch of margin is what the gap buys. The check runs between batches, so a stop
        // overshoots by however much the batch in progress still needed; the backstop has to allow
        // for that or it fires first and the statistics are lost anyway.
        max_wall_time: Some(cooperative_budget()),
        max_matrix_columns: 200_000,
        // `ZEEBRA_MAX_ENTRIES` raises the bound that binds, for the one question a fixed budget
        // cannot answer: whether a row is out of reach or merely out of *this* budget. The default
        // is what every reported figure uses.
        max_live_nonzeros: std::env::var("ZEEBRA_MAX_ENTRIES")
            .ok()
            .and_then(|n| n.parse().ok())
            .unwrap_or(20_000_000),
        max_live_bytes: 64_000_000_000,
        max_batches: Some(10_000),
        ..F4Options::default()
    }
}

/// The per-row wall clock, from the environment. The supervisor's **backstop**, not the budget.
///
/// Two clocks govern a frontier row and the order they fire in matters. [`cooperative_budget`] is
/// F4's own `max_wall_time`, which **returns** and so carries its statistics out; this is the
/// `recv_timeout` that abandons the worker thread, which cannot. The cooperative one is set
/// shorter so that it is the one that normally fires, and this stays what it should always have
/// been: the thing that catches a single batch running long enough that the cooperative check
/// never gets a turn.
fn wall_clock() -> Duration {
    Duration::from_secs(
        std::env::var("ZEEBRA_WALL_SECONDS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(600),
    )
}

/// How much of [`wall_clock`] F4's own cooperative check is given.
///
/// Nine tenths, with a floor of one second. A fraction rather than a fixed subtraction so the
/// margin scales: a 60 s row and a 6 h row need different slack for the batch in progress, and the
/// overshoot is roughly proportional to how large the matrices have grown by then.
fn cooperative_budget() -> Duration {
    let wall = wall_clock();
    (wall * 9 / 10).max(Duration::from_secs(1)).min(wall)
}

fn frontier_policy() -> String {
    format!(
        "grevlex F4 only; 200000 columns, {} live entries (the binding bound), 10000 batches, \
         F4 max_wall_time {} s cooperative, supervisor wall clock {} s as a backstop",
        std::env::var("ZEEBRA_MAX_ENTRIES").unwrap_or_else(|_| "20000000".to_string()),
        cooperative_budget().as_secs(),
        wall_clock().as_secs()
    )
}

/// Which equivalent presentation of the same problem to solve.
///
/// Every one of these is the **same mathematical problem** — a relabelling is a ring isomorphism,
/// and an affine elimination generates the same ideal — which is why they share the registry's
/// identity digest and why `Comparison::of` will compare them. What differs is the cost, which is
/// the thing M23-C is about.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Formulation {
    /// Free inputs, then S-box variables in round order: what the generator produces.
    AsGenerated,

    /// Free inputs, then the round blocks reversed. M22-E's winner on the `t = 2` surrogates.
    LastRoundFirst,

    /// S-box variables first, free inputs last.
    FreeInputsLast,

    /// Eliminate every affine generator and project the determined variables out of the ring.
    AffineProjected,
}

impl Formulation {
    fn name(&self) -> &'static str {
        match self {
            Self::AsGenerated => "as generated",
            Self::LastRoundFirst => "last-round-first",
            Self::FreeInputsLast => "free-inputs-last",
            Self::AffineProjected => "affine-projected",
        }
    }

    fn named(name: &str) -> Option<Self> {
        [
            Self::AsGenerated,
            Self::LastRoundFirst,
            Self::FreeInputsLast,
            Self::AffineProjected,
        ]
        .into_iter()
        .find(|f| f.name() == name)
    }

    /// The variable layout this formulation uses, where it is a relabelling.
    fn layout(&self) -> Option<RoundLayout> {
        match self {
            Self::AsGenerated => Some(RoundLayout::Generated),
            Self::LastRoundFirst => Some(RoundLayout::LastRoundFirst),
            Self::FreeInputsLast => Some(RoundLayout::FreeInputsLast),
            Self::AffineProjected => None,
        }
    }
}

/// The per-round S-box variable counts of a schedule, for [`RoundLayout`].
///
/// A full round introduces `t` S-box variables and a partial round one, and the schedule is
/// `R_F/2` full, then `R_P` partial, then `R_F/2` full. A single width would mis-group every
/// instance with `R_P > 0`.
fn block_sizes(t: usize, r_f: usize, r_p: usize) -> Vec<usize> {
    let half = r_f / 2;
    let mut sizes = vec![t; half];
    sizes.extend(std::iter::repeat_n(1, r_p));
    sizes.extend(std::iter::repeat_n(t, half));
    sizes
}

/// How far a computation had got when the supervisor stopped it.
///
/// Written by the observer from inside the worker thread and read from outside it, because F4 has
/// no cooperative check: when the wall clock expires the only thing that knows anything about the
/// state of the computation is whatever was watching the batches go past.
#[derive(Default)]
struct Progress {
    batches: AtomicUsize,
    degree: AtomicU64,
    basis: AtomicUsize,
}

/// Records each batch's selection degree and the basis size, for the supervisor to read.
struct Watch(Arc<Progress>);

impl<const N: usize, F: zeebra::KnownOrder> BatchObserver<N, F> for Watch {
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]) {
        self.0.batches.fetch_add(1, Ordering::Relaxed);
        self.0.basis.store(basis.len(), Ordering::Relaxed);
        let degree = pairs.iter().map(|p| p.lcm.degree()).max().unwrap_or(0);
        self.0.degree.fetch_max(degree, Ordering::Relaxed);
    }
}

/// One full-width row: build it, optionally slice it, run F4 under the frontier budget, and record
/// where it stopped.
///
/// The Gröbner stage only. At this size the question is not which route recovers a point but
/// whether a basis exists within the budget at all, and a conversion that never gets a basis is a
/// stage that did not run rather than one that cost nothing.
fn run_frontier_row(
    manifest: &ChallengeManifest,
    environment: &Environment,
    slice: Option<u64>,
    wall: Duration,
) -> RunRecord {
    run_frontier_formulation(manifest, environment, slice, wall, Formulation::AsGenerated)
}

/// One full-width row under one formulation of the same problem.
fn run_frontier_formulation(
    manifest: &ChallengeManifest,
    environment: &Environment,
    slice: Option<u64>,
    wall: Duration,
    formulation: Formulation,
) -> RunRecord {
    let at = Instant::now();
    let instance = manifest.cico_instance::<K>().expect("a registered problem");
    let generation = at.elapsed();

    let mut record = dispatch_cico::<K, _>(
        manifest,
        Frontier {
            manifest,
            instance: &instance,
            generation,
            slice,
            wall,
            formulation,
        },
    )
    .expect("a compiled dimension");
    record.environment = Environment {
        policy: frontier_policy(),
        ..environment.clone()
    };
    record.reproduce = format!(
        "ZEEBRA_WALL_SECONDS={} tools/scoreboard.sh row {}{} --layout {}",
        wall.as_secs(),
        manifest.id,
        match slice {
            Some(seed) => format!(" --slice {}", seed),
            None => String::new(),
        },
        formulation.name()
    );
    record
}

/// The frontier attempt at one compiled dimension.
struct Frontier<'a> {
    manifest: &'a ChallengeManifest,
    instance: &'a zeebra::grobner::research::CicoInstance<K>,
    generation: Duration,
    slice: Option<u64>,
    wall: Duration,
    formulation: Formulation,
}

impl CicoVisitor<K> for Frontier<'_> {
    type Output = RunRecord;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, K>]) -> RunRecord {
        let free = self.instance.free_inputs();
        let mut record = RunRecord::new(
            self.manifest,
            match (self.slice, self.formulation) {
                (None, Formulation::AsGenerated) => "as generated".to_string(),
                (None, formulation) => formulation.name().to_string(),
                (Some(seed), Formulation::AsGenerated) => {
                    format!("slice({} fixed, seed {})", free - 2, seed)
                }
                (Some(seed), formulation) => format!(
                    "slice({} fixed, seed {}) + {}",
                    free - 2,
                    seed,
                    formulation.name()
                ),
            },
        );

        // The slice fixes all but two free inputs, leaving two unknowns against the two output
        // constraints. The seed is precommitted and recorded: `Specialization::seeded` promises
        // that the same seed reconstructs the same slice.
        let at = Instant::now();
        let system: Vec<MultivariatePolynomial<N, K>> = match self.slice {
            None => system.to_vec(),
            Some(seed) => {
                let variables: Vec<usize> = (2..free).collect();
                let specialization =
                    Specialization::<N, K>::seeded(&variables, seed).expect("distinct indices");
                record.transformations.push(format!(
                    "specialize free inputs {}..{} at seed {} ({} values)",
                    2,
                    free,
                    seed,
                    specialization.len()
                ));
                specialization.apply(system)
            }
        };

        // Then the formulation, which is the axis M23-C compares along. Every one of these is the
        // same ideal presented differently, and each carries its own inverse so a recovered
        // witness is checked against the *original* permutation either way.
        let sliced = self.slice.is_some();
        let instance = self.instance;
        let outcome = match self.formulation.layout() {
            Some(layout) => {
                let parameters = self.manifest.poseidon_parameters().expect("a CICO row");
                let order = layout
                    .order::<N>(
                        free,
                        &block_sizes(parameters.t, parameters.r_f, parameters.r_p),
                    )
                    .expect("the block sizes account for every variable");
                let relabelled = order.apply(&system);
                if !order.is_identity() {
                    record
                        .transformations
                        .push(format!("relabel variables: {}", order.name()));
                }
                let generation = self.generation + at.elapsed();
                record.stages.push(
                    StageCost::new(Stage::Generation, generation)
                        .with("variables", N as i64)
                        .with("equations", relabelled.len() as i64)
                        .with("free_inputs", free as i64),
                );
                supervised_solve(relabelled, self.wall, sliced, |point| {
                    // Back through the relabelling, then through the permutation.
                    let original = order.recover(point);
                    let inputs: Vec<K> = original[..free].to_vec();
                    instance.is_solution(&inputs).unwrap_or(false)
                })
            }
            None => {
                let (reduced, elimination) = eliminate_affine(&system);
                let kept = elimination.kept().len();
                record.transformations.push(format!(
                    "eliminate {} affine generators and project to {} variables",
                    elimination.len(),
                    kept
                ));
                let generation = self.generation + at.elapsed();
                record.stages.push(
                    StageCost::new(Stage::Generation, generation)
                        .with("variables", kept as i64)
                        .with("equations", reduced.len() as i64)
                        .with("eliminated", elimination.len() as i64)
                        .with("free_inputs", free as i64),
                );

                // The projected dimension is a compile-time constant and the survivor count is
                // not, so only the dimensions this experiment needs are compiled. An uncompiled
                // one is a fact about the harness and is recorded as one rather than guessed at.
                macro_rules! project_and_solve {
                    ($($m:literal),+ $(,)?) => {
                        match kept {
                            $($m => {
                                let projected = elimination
                                    .project::<$m>(&reduced)
                                    .expect("the survivor count is M");
                                supervised_solve(projected, self.wall, sliced, |point| {
                                    let lifted = elimination
                                        .lift::<$m>(point)
                                        .expect("the survivor count is M");
                                    let inputs: Vec<K> = lifted[..free].to_vec();
                                    instance.is_solution(&inputs).unwrap_or(false)
                                })
                            })+
                            other => (
                                RunOutcome::StoppedAtLimit(Limit {
                                    resource: "compiled_dimension".to_string(),
                                    detail: format!(
                                        "no projected dimension {} is compiled; add it to \
                                         project_and_solve! to measure this row",
                                        other
                                    ),
                                    degree: None,
                                    last_completed_stage: Stage::Generation,
                                }),
                                Vec::new(),
                                GrobnerFrontier::default(),
                            ),
                        }
                    };
                }
                // 32 is the sliced `R_F = 2, R_P = 0` row and 44 is the same row unsliced.
                project_and_solve!(32, 44)
            }
        };

        let (result, stages, frontier) = outcome;
        record.outcome = result;
        record.stages.extend(stages);
        record.frontier = Some(frontier);
        record.verification =
            "CicoInstance::is_solution, which runs permutation_plus_linear on the recovered \
             inputs, after inverting every transformation applied here"
                .to_string();
        record
    }
}

/// F4 under a wall-clock supervisor, then the rest of the pipeline if a basis came back.
///
/// Two clocks, and which one fires decides whether the row has a frontier. F4's own
/// `max_wall_time` is set shorter (see [`cooperative_budget`]) and **returns**, so its stop
/// carries the matrix statistics out through the channel. This `recv_timeout` is the backstop for
/// the case the cooperative check cannot cover — a single batch running past the margin — and it
/// can only abandon the worker thread, which is why the system is taken by value: a thread that
/// owns its data can be abandoned safely, and the process exits after the record is written.
fn supervised_solve<const D: usize, F: zeebra::KnownOrder + Send + 'static>(
    system: Vec<MultivariatePolynomial<D, F>>,
    wall: Duration,
    sliced: bool,
    verify: impl Fn(&[F; D]) -> bool,
) -> (RunOutcome, Vec<StageCost>, GrobnerFrontier) {
    let mut stages = Vec::new();
    let retained = system.clone();

    let progress = Arc::new(Progress::default());
    let observed = Arc::clone(&progress);
    let (sender, receiver) = mpsc::channel();
    let at = Instant::now();
    std::thread::spawn(move || {
        let mut watch = Watch(observed);
        let outcome = f4_observed_reported(&system, GREVLEX, &frontier_options(), &mut watch);
        // A send failure means the supervisor has already given up, which is not an error here.
        let _ = sender.send(outcome);
    });

    match receiver.recv_timeout(wall) {
        Ok((result, statistics)) => {
            let elapsed = at.elapsed();
            let completed = result.is_ok();
            let mut frontier =
                GrobnerFrontier::of(&statistics, completed).with_profile(&statistics.degrees);
            stages.push(
                StageCost::new(Stage::Grobner, elapsed)
                    .with("max_matrix_rows", statistics.max_matrix_rows as i64)
                    .with("max_matrix_columns", statistics.max_matrix_columns as i64)
                    .with("max_pair_degree", statistics.max_pair_degree as i64)
                    .with("pairs_considered", statistics.pairs_considered as i64)
                    .with("pairs_reduced", statistics.pairs_reduced as i64)
                    .with("elements_added", statistics.elements_added as i64)
                    .with_estimated_bytes(statistics.max_estimated_bytes),
            );

            match result {
                // A basis at this size is the newsworthy case, and it is not yet a witness. Carry
                // on through the conversion and the search, which is where one would come from.
                Ok(basis) => {
                    let (outcome, tail, dimension) =
                        finish_from_basis(&basis, &retained, sliced, verify);
                    stages.extend(tail);
                    if let Some(dimension) = dimension {
                        frontier = frontier.with_quotient_dimension(dimension);
                    }
                    (outcome, stages, frontier)
                }
                // A stop that **returned**, so `statistics` and therefore `frontier` are real.
                // This now includes the cooperative time stop, which is the whole point of #284:
                // before it, a run that ran long could only be abandoned, and an abandoned run
                // reports nothing.
                //
                // `resource` is `F4Error::limit_name()`, which separates the kinds without a
                // second field: `max_wall_time` is a `StopKind::Time` and every other name here
                // is a `StopKind::Resource`. The distinction has to survive into the record
                // because a wall clock is a fact about one machine and an entry count is not, so
                // the two must never be ranked against each other. Nothing ranks them today —
                // `Scoreboard::best` and `verified_somehow` both admit only verified witnesses,
                // and `unfinished` preserves insertion order without comparing — and a renderer
                // that starts ranking stops has to read this field first.
                Err(error) => (
                    RunOutcome::StoppedAtLimit(Limit {
                        resource: resource_of(&error),
                        detail: error.to_string(),
                        degree: Some(statistics.max_pair_degree),
                        last_completed_stage: Stage::Generation,
                    }),
                    stages,
                    frontier,
                ),
            }
        }
        Err(_) => {
            // The backstop fired, which means F4's own cooperative check never got a turn — a
            // single batch ran longer than the margin between the two clocks. Nothing came back
            // from the worker, so no statistics exist and the only account of the state is the
            // observer's. Reported as `wall_clock` and not as `max_wall_time`, because those are
            // two different stops: one is a fact about this supervisor, the other a fact about the
            // budget F4 was given.
            let batches = progress.batches.load(Ordering::Relaxed);
            let degree = progress.degree.load(Ordering::Relaxed);
            stages.push(
                StageCost::new(Stage::Grobner, wall)
                    .with("batches_started", batches as i64)
                    .with("highest_selection_degree", degree as i64)
                    .with(
                        "basis_elements",
                        progress.basis.load(Ordering::Relaxed) as i64,
                    ),
            );
            (
                RunOutcome::StoppedAtLimit(Limit {
                    resource: "wall_clock".to_string(),
                    detail: format!(
                        "the supervisor's backstop fired after {} s with {} batches started, so \
                         F4's cooperative {} s budget never reached a batch boundary; the worker \
                         was abandoned and no matrix statistics exist for a run stopped this way",
                        wall.as_secs(),
                        batches,
                        cooperative_budget().as_secs()
                    ),
                    degree: (degree > 0).then_some(degree),
                    last_completed_stage: Stage::Generation,
                }),
                stages,
                GrobnerFrontier::default(),
            )
        }
    }
}

/// Run a registered MQ problem under the frontier budget, slicing it if it is underdetermined.
///
/// Returns one record for an overdetermined instance, or one per slice plus a campaign summary for
/// an underdetermined one. Empty if the instance file is absent.
fn run_mq_rows(
    manifest: &ChallengeManifest,
    environment: &Environment,
    seeds: u64,
    wall: Duration,
) -> Vec<RunRecord> {
    let ChallengeParameters::MqSystem {
        kind, n, m, seed, ..
    } = manifest.parameters
    else {
        return Vec::new();
    };
    let Some((instance, published)) = read_mq(kind, n, m, seed) else {
        return Vec::new();
    };

    let underdetermined = m < n;
    let mut records = Vec::new();
    let mut campaign = Campaign {
        fixed: n.saturating_sub(m),
        ..Campaign::default()
    };
    let at = Instant::now();

    for seed in 0..if underdetermined { seeds } else { 1 } {
        let solve = || SolveMqSliced {
            manifest,
            instance: &instance,
            published: &published,
            slice: underdetermined.then_some(seed),
            fixed: campaign.fixed,
            wall,
        };
        // On the instance's own field rather than on one chosen here. Type V and type VI publish
        // the same n = 24 at m = 16 and differ only in the field, so a runner hardwired to GF(31)
        // could import the type V challenge and not run it (#510).
        let mut record = match instance.field {
            MqField::Gf31 => instance.dispatch::<Q, _>(solve()),
            MqField::Gf256 => instance.dispatch::<Gf256Mq, _>(solve()),
            MqField::Gf2 => return Vec::new(),
        }
        .expect("a supported dimension");
        record.environment = Environment {
            policy: frontier_policy(),
            ..environment.clone()
        };
        record.reproduce = format!(
            "tools/fetch-mq-challenge.sh && tools/scoreboard.sh mq {} --seeds {}",
            manifest.id, seeds
        );
        if underdetermined {
            tally(&mut campaign, seed, &record.outcome);
        }
        records.push(record);
    }

    if underdetermined {
        campaign.total = at.elapsed();
        let mut summary = RunRecord::new(manifest, format!("campaign over {} slices", seeds));
        summary.environment = Environment {
            policy: frontier_policy(),
            ..environment.clone()
        };
        summary.outcome = campaign_outcome(&campaign);
        summary.verification =
            "every witness evaluated against the original published coefficient vectors"
                .to_string();
        summary.transformations = vec![format!(
            "{} slices, each fixing {} of {} variables at a seeded value",
            seeds, campaign.fixed, n
        )];
        summary.stages = vec![StageCost::new(Stage::Grobner, campaign.total)];
        summary.reproduce = format!("tools/scoreboard.sh mq {} --seeds {}", manifest.id, seeds);
        report_campaign(&campaign);
        summary.campaign = Some(campaign);
        records.push(summary);
    }
    records
}

/// Tally one slice into a campaign: a witness, a decided-but-empty slice, or no verdict at all.
fn tally(campaign: &mut Campaign, seed: u64, outcome: &RunOutcome) {
    campaign.trials += 1;
    campaign.seeds.push(seed);
    match outcome {
        RunOutcome::VerifiedWitness => campaign.witnesses += 1,
        // A slice that ran out of budget did not test whether it contains a solution. Counting it
        // as a failure would turn "nothing was established" into "the rate is zero".
        RunOutcome::StoppedAtLimit(_) | RunOutcome::WitnessRejected => campaign.stopped += 1,
        _ => {}
    }
}

/// What a campaign as a whole established.
fn campaign_outcome(campaign: &Campaign) -> RunOutcome {
    if campaign.witnesses > 0 {
        RunOutcome::VerifiedWitness
    } else if campaign.decided() == 0 {
        RunOutcome::StoppedAtLimit(Limit {
            resource: "campaign reached no verdict".to_string(),
            detail: format!(
                "all {} slices stopped at a resource limit, so none of them tested whether it \
                 contains a solution",
                campaign.trials
            ),
            degree: None,
            last_completed_stage: Stage::Generation,
        })
    } else {
        RunOutcome::SliceEstablishedNothing
    }
}

/// Print a campaign's summary lines, with no rate where there is no rate.
fn report_campaign(campaign: &Campaign) {
    match campaign.work_per_witness() {
        Some((nanos, witnesses)) => println!(
            "\n{} witnesses in {} slices ({} decided); {:.1} s per witness including the failures",
            witnesses,
            campaign.trials,
            campaign.decided(),
            nanos as f64 / 1e9 / witnesses as f64
        ),
        None if campaign.decided() == 0 => println!(
            "\nno witness, and **no rate**: all {} slices stopped at a resource limit, so none of \
             them tested whether it contains a solution",
            campaign.trials
        ),
        None => println!(
            "\nno witness in {} decided slices of {}, which is a fact about those slices and not \
             about the problem",
            campaign.decided(),
            campaign.trials
        ),
    }
    if let Some((low, high)) = campaign.success_rate_basis_points() {
        println!(
            "success rate {}.{:02}% to {}.{:02}% over the {} decided slices (Wilson, 95%)",
            low / 100,
            low % 100,
            high / 100,
            high % 100,
            campaign.decided()
        );
    }
}

/// Read a published instance and its answer, if the instance is on disk.
///
/// Two naming schemes, because the site has two. A toy example is `ToyExample-typeT-nN-seedS` and
/// ships an answer file; a real challenge is `challenge-T-S-SEED`, indexed by `n` for the
/// encryption types and by `m` for the signature ones, and ships **no answer** — nobody publishes
/// the solution to an instance that is still a challenge. So a missing answer is ordinary here and
/// returns an empty vector rather than `None`; a present answer that does not parse is not
/// ordinary and still panics.
fn read_mq(kind: &str, n: usize, m: usize, seed: u64) -> Option<(MqInstance, Vec<u64>)> {
    let directory = std::env::var("ZEEBRA_MQ_DIR").unwrap_or("research/instances/mq".to_string());
    let encryption = kind == "II" || kind == "III";
    let type_number = match kind {
        "I" => 1,
        "II" => 2,
        "III" => 3,
        "IV" => 4,
        "V" => 5,
        _ => 6,
    };
    let names = [
        format!("ToyExample-type{}-n{}-seed{}", type_number, n, seed),
        format!(
            "challenge-{}-{}-{}",
            type_number,
            if encryption { n } else { m },
            seed
        ),
    ];
    let (name, text) = names.iter().find_map(|name| {
        let text = fs::read_to_string(Path::new(&directory).join(name)).ok()?;
        Some((name, text))
    })?;
    let instance = MqInstance::parse(&text).expect("a published instance");
    let published = match fs::read_to_string(Path::new(&directory).join(format!("{}-answer", name)))
    {
        Ok(answer) => instance
            .parse_answer(&answer)
            .expect("the published answer parses"),
        Err(_) => Vec::new(),
    };
    Some((instance, published))
}

/// One MQ instance, optionally sliced, under the supervisor.
struct SolveMqSliced<'a> {
    manifest: &'a ChallengeManifest,
    instance: &'a MqInstance,
    published: &'a [u64],
    slice: Option<u64>,
    fixed: usize,
    wall: Duration,
}

/// Generic over the coefficient type, so one visitor serves both signature families: type VI is
/// GF(31) and type V is GF(2^8) at the very same `n = 24` (#510). The field comes from the
/// instance's own header, not from this file.
impl<F: zeebra::KnownOrder + Send + 'static> MqVisitor<F> for SolveMqSliced<'_> {
    type Output = RunRecord;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> RunRecord {
        let mut record = RunRecord::new(
            self.manifest,
            match self.slice {
                None => "as published".to_string(),
                Some(seed) => format!("slice({} fixed, seed {})", self.fixed, seed),
            },
        );

        let at = Instant::now();
        // The slice fixes the surplus variables — the ones that make a signature instance
        // positive-dimensional — at values drawn from a precommitted seed.
        let system: Vec<MultivariatePolynomial<N, F>> = match self.slice {
            Some(seed) => {
                let variables: Vec<usize> = (N - self.fixed..N).collect();
                let specialization =
                    Specialization::<N, F>::seeded(&variables, seed).expect("distinct indices");
                record.transformations.push(format!(
                    "specialize variables {}..{} at seed {}",
                    N - self.fixed,
                    N,
                    seed
                ));
                specialization.apply(system)
            }
            None => system.to_vec(),
        };
        record.stages.push(
            StageCost::new(Stage::Generation, at.elapsed())
                .with("variables", N as i64)
                .with("equations", system.len() as i64),
        );

        // The check is against the *published* coefficient vectors, reconstructed from the file
        // rather than from the system that was solved — and, where the instance has a published
        // answer and a unique solution, against that answer too.
        let reconstructed = self
            .instance
            .system::<N, F>()
            .expect("the same instance parses twice");
        // Through the instance's own conversion, not `F::new`: over GF(2^8) the file's token is a
        // bit pattern and `new` is the prime-subfield embedding, which would collapse it to a bit.
        let published: Vec<F> = self
            .published
            .iter()
            .map(|v| {
                self.instance
                    .element::<F>(*v)
                    .expect("the published answer is in the field")
            })
            .collect();
        let (outcome, stages, frontier) =
            supervised_solve(system, self.wall, self.slice.is_some(), |point| {
                let vanishes = reconstructed
                    .iter()
                    .all(|polynomial| polynomial.eval(point) == F::zero());
                if vanishes && published.len() == N {
                    let matches: Vec<bool> = (0..N).map(|i| point[i] == published[i]).collect();
                    println!(
                        "    recovered point {} the published answer",
                        if matches.iter().all(|m| *m) {
                            "is"
                        } else {
                            "is a different root from"
                        }
                    );
                }
                vanishes
            });
        record.outcome = outcome;
        record.stages.extend(stages);
        record.frontier = Some(frontier);
        // A real challenge publishes no answer, so there is nothing to start with and saying so is
        // not the same claim as having checked against one.
        record.verification = if self.published.is_empty() {
            "evaluated against the published coefficient vectors; this instance publishes no \
             answer vector, so the witness check is the only check"
                .to_string()
        } else {
            format!(
                "evaluated against the published coefficient vectors; the published answer starts \
                 {:?}",
                &self.published[..self.published.len().min(4)]
            )
        };
        record
    }
}

/// Run one registered MQ problem, if its file is present.
fn run_mq(manifest: &ChallengeManifest, environment: &Environment) -> Option<RunRecord> {
    let ChallengeParameters::MqSystem {
        kind, n, m, seed, ..
    } = manifest.parameters
    else {
        return None;
    };
    let at = Instant::now();
    let (instance, published) = read_mq(kind, n, m, seed)?;
    let generation = at.elapsed();

    let solve = || SolveMq {
        manifest,
        instance: &instance,
        published: &published,
        generation,
    };
    let mut record = match instance.field {
        MqField::Gf31 => instance.dispatch::<Q, _>(solve()),
        MqField::Gf256 => instance.dispatch::<Gf256Mq, _>(solve()),
        // GF(2) is types I and IV, which the importer itself refuses: the field exists two ways
        // here and which one to read these files under is #197's decision, not this runner's.
        MqField::Gf2 => return None,
    }
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

impl<F: zeebra::KnownOrder> MqVisitor<F> for SolveMq<'_> {
    type Output = RunRecord;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> RunRecord {
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
            .system::<N, F>()
            .expect("the same instance parses twice");
        let (outcome, stages, frontier) = staged_solve(system, false, |point| {
            reconstructed
                .iter()
                .all(|polynomial| polynomial.eval(point) == F::zero())
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
    sliced: bool,
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

    let (outcome, tail, dimension) = finish_from_basis(&basis, system, sliced, verify);
    stages.extend(tail);
    if let Some(dimension) = dimension {
        frontier = frontier.with_quotient_dimension(dimension);
    }
    (outcome, stages, frontier)
}

/// The conversion, the univariate search and the independent check, each timed.
///
/// Split out of [`staged_solve`] because the frontier rows reach a basis by a different route —
/// through a wall-clock supervisor — and a second copy of the stage accounting would be a second
/// place for the slice rule to be forgotten.
///
/// `verify` is the problem's own independent check, which is what decides between a witness and a
/// defect. A candidate that fails it is [`RunOutcome::WitnessRejected`]: an absence and a defect
/// are different facts.
fn finish_from_basis<const N: usize, F: zeebra::KnownOrder>(
    basis: &[MultivariatePolynomial<N, F>],
    system: &[MultivariatePolynomial<N, F>],
    sliced: bool,
    verify: impl Fn(&[F; N]) -> bool,
) -> (RunOutcome, Vec<StageCost>, Option<usize>) {
    let mut stages = Vec::new();

    if classify_ideal(basis, GREVLEX) != IdealClass::ZeroDimensional {
        // Not a limit and not a witness: the ideal is positive-dimensional, so the
        // zero-dimensional route does not apply and saying "no solution" would be wrong.
        return (RunOutcome::BasisOnly, stages, None);
    }

    let at = Instant::now();
    let converted = fglm_to_lex_with_options(basis, GREVLEX, &FglmOptions::default());
    let conversion_elapsed = at.elapsed();
    let (lex, conversion) = match converted {
        Ok(pair) => pair,
        Err(error) => {
            stages.push(StageCost::new(Stage::Conversion, conversion_elapsed));
            return (
                RunOutcome::StoppedAtLimit(Limit {
                    resource: "conversion".to_string(),
                    detail: error.to_string(),
                    degree: None,
                    last_completed_stage: Stage::Grobner,
                }),
                stages,
                None,
            );
        }
    };
    let dimension = conversion.quotient_dimension;
    stages.push(
        StageCost::new(Stage::Conversion, conversion_elapsed)
            .with("quotient_dimension", dimension as i64)
            .with_estimated_bytes(conversion.estimated_bytes()),
    );

    let at = Instant::now();
    let searched = solve_from_lex_basis(
        &lex,
        system,
        &SolveOptions::default(),
        &mut StdRng::seed_from_u64(1),
    );
    stages.push(
        StageCost::new(Stage::Univariate, at.elapsed())
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
        // An empty *slice* is a fact about the slice: a witness on it would be a witness for the
        // original system, but its absence says nothing. M21-E's rule, at the record level.
        Ok((SolveOutcome::NoBaseFieldPoint, _)) if sliced => RunOutcome::SliceEstablishedNothing,
        Ok((SolveOutcome::Inconsistent, _)) if sliced => RunOutcome::SliceEstablishedNothing,
        Ok((SolveOutcome::NoBaseFieldPoint, _)) => RunOutcome::NoBaseFieldPoint,
        Ok((SolveOutcome::Inconsistent, _)) => RunOutcome::Inconsistent,
        Err(error) => RunOutcome::StoppedAtLimit(Limit {
            resource: "univariate search".to_string(),
            detail: error.to_string(),
            degree: None,
            last_completed_stage: Stage::Conversion,
        }),
    };
    (outcome, stages, Some(dimension))
}

/// Which bound bound, as a stable name a consumer can key on.
/// The stable name of whatever limit stopped a run.
///
/// Delegated to `F4Error::limit_name` rather than matched here. The hand-rolled match this
/// replaces ended in a `_ => "other"` catch-all, so `max_wall_time` would have been recorded as
/// `other` — a new stop reason silently losing its name is exactly what a catch-all buys. The
/// library's version is exhaustive, so a variant added there stops compiling until it is named.
fn resource_of(error: &zeebra::grobner::F4Error) -> String {
    error.limit_name().to_string()
}

/// The machine and build this measurement came from.
///
/// `git rev-parse` rather than a build-time constant: this is an example, and a comparison needs
/// to know which tree produced the number more than it needs to avoid a subprocess.
fn detect_environment() -> Environment {
    let machine = std::env::var("ZEEBRA_MACHINE").unwrap_or_else(|_| {
        Command::new("hostname")
            .output()
            .ok()
            .and_then(|out| String::from_utf8(out.stdout).ok())
            .map(|s| s.trim().to_string())
            .unwrap_or_else(|| "unknown".to_string())
    });
    Environment {
        machine,
        cpu: format!(
            "{} logical, affinity {}",
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(0),
            std::env::var("ZEEBRA_AFFINITY").unwrap_or_else(|_| "unpinned".to_string())
        ),
        // Every solver this runner drives is single-threaded. The field exists so that a row which
        // is not cannot be compared against one of these by accident.
        concurrency: 1,
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
        // The commit, the merge base it was cut from and the patch id of the delta between them,
        // so the stamp outlives a merge that rewrites this branch's history (#505).
        ..Environment::from_git()
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
    // Checked before anything is written. The per-run filename's uniqueness rests on the
    // formulation string — nothing in the name carries the slice or the seed — so two runs can
    // silently map to one file and the directory ends up with fewer records than there were runs,
    // with nothing to notice. Stopping is the right response: a lost record is worse than a
    // failed write, and the message names both formulations so the fix is obvious.
    // History accumulates: read what is there, append, write it back. A writer with no reader
    // would mean losing every earlier milestone's results on each run.
    //
    // **Append-only, and that is load-bearing rather than incidental.** Position in the `runs`
    // array is the only record of *when* a run was recorded, and
    // `Scoreboard::verified_somehow`'s tie-break reads it: among witnesses tied on worker count
    // it keeps the last one, because the later record is the one later code wrote and therefore
    // the more complete. Sorting, deduplicating or regenerating this file would leave every
    // record present and make that choice arbitrary. The contract is written into the file
    // below, because a consumer cannot read a Rust doc comment.
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
    let entries_for_history = entries.clone();

    // One record file per run in the **accumulated** history, not per run added this pass (#540).
    //
    // Before, the loop wrote only the new runs and relied on every earlier file still being
    // correct. That holds exactly as long as `run_file_stem` never changes — and it had changed,
    // leaving seven committed files whose names no stem produced and seven stems with no file.
    // Writing from the accumulation makes `runs/` a function of the history, so a stem change
    // migrates the whole directory instead of stranding the part of it nobody re-ran.
    let accumulated: Vec<RunRecord> = entries_for_history
        .iter()
        .map(|entry| {
            let challenge = entry
                .get("challenge")
                .and_then(Json::as_str)
                .expect("a retained run names its challenge");
            let manifest = registry
                .iter()
                .find(|c| c.id == challenge)
                .expect("a retained run's challenge is registered");
            RunRecord::from_json(entry, manifest).expect("the history this program wrote")
        })
        .collect();
    // Checked over the accumulated history, which is what gets written, and before any of it is.
    // A shared stem now means two records of identical content, so a collision here is a digest
    // collision or a bug in `RunRecord::canonical`; either way stopping beats losing a record.
    if let Some(collision) = colliding_run_file(&accumulated) {
        panic!("two runs would share a per-run filename: {}", collision);
    }
    let mut written: BTreeSet<String> = BTreeSet::new();
    for run in &accumulated {
        let manifest = registry
            .iter()
            .find(|c| c.id == run.challenge)
            .expect("a retained run's challenge is registered");
        let name = format!("{}.json", run.run_file_stem());
        fs::write(
            root.join("runs").join(&name),
            run.to_json(manifest).to_json() + "\n",
        )
        .expect("a writable file");
        written.insert(name);
    }
    // A `runs/` entry this pass did not write is a record of nothing: a file left behind when the
    // stem that named it changed. Removing it is what keeps the directory equal to the history
    // rather than a superset of every naming scheme the tree has had.
    //
    // Safe only because the loop above covers the whole accumulated history. It must stay that
    // way: pruning against the runs *added* this pass would delete every earlier milestone's
    // records, and `render` adds none at all.
    for entry in fs::read_dir(root.join("runs")).expect("a readable directory") {
        let path = entry.expect("a readable entry").path();
        let is_orphan = path
            .extension()
            .is_some_and(|extension| extension == "json")
            && path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| !written.contains(name));
        if is_orphan {
            fs::remove_file(&path).expect("a removable file");
            println!("- removed {}, which no retained run names", path.display());
        }
    }
    fs::write(
        &history_path,
        Json::object([
            ("schema", Json::int(RunRecord::SCHEMA)),
            ("contract", Json::string(HISTORY_CONTRACT)),
            ("run_count", Json::size(entries_for_history.len())),
            ("runs", Json::Array(entries_for_history)),
        ])
        .to_json()
            + "\n",
    )
    .expect("a writable file");

    // `best.json` and the Markdown are rendered from the **accumulated history**, not from this
    // process's board. The frontier rows run one per process, and a renderer that used only what
    // the current process measured would overwrite the table with a single row each time.
    let accumulated = Json::object([("runs", Json::Array(entries))]);
    let all = Scoreboard::load(&accumulated, registry).expect("the history this program wrote");

    // Two files, and the split is the contract.
    //
    // `best.json` is the **serial performance ranking**: `Scoreboard::best` is `best_at(1)`, so a
    // parallel wall clock cannot displace a figure it is not comparable with. That makes it the
    // wrong file to ask "is this problem solved?" of — a problem whose only witness is parallel is
    // absent from it, by design and not by oversight.
    //
    // `solved.json` answers that question instead: one entry per problem with a verified witness at
    // any worker count, carrying the concurrency so nothing in it can be read as a serial timing.
    // Keeping them apart is what lets `best.json` stay a like-for-like ranking while a consumer can
    // still discover solved status without parsing the whole history.
    let json_for = |run: &RunRecord| {
        let manifest = registry
            .iter()
            .find(|c| c.id == run.challenge)
            .expect("checked on load");
        run.to_json(manifest)
    };

    fs::write(
        root.join("results").join("best.json"),
        Json::object([
            ("contract", Json::string(BEST_CONTRACT)),
            (
                "best",
                Json::Array(all.best().values().map(|run| json_for(run)).collect()),
            ),
        ])
        .to_json()
            + "\n",
    )
    .expect("a writable file");

    fs::write(
        root.join("results").join("solved.json"),
        Json::object([
            ("contract", Json::string(SOLVED_CONTRACT)),
            (
                "solved",
                Json::Array(
                    all.verified_somehow()
                        .values()
                        .map(|run| json_for(run))
                        .collect(),
                ),
            ),
        ])
        .to_json()
            + "\n",
    )
    .expect("a writable file");

    fs::write(root.join("SCOREBOARD.md"), all.to_markdown(registry)).expect("a writable file");
}
