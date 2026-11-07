//! The competitive sweep: corpus × engines × tasks into the competitive board.
//!
//! ```text
//! cargo run --release --example competitive_sweep                    # every rung, exploratory
//! cargo run --release --example competitive_sweep -- --list          # what would run
//! cargo run --release --example competitive_sweep -- \
//!     --engines zeebra,singular --write                              # populate the board in parts
//! tools/benchlock.sh runner cargo run --release --example competitive_sweep -- \
//!     --row katsura-6 --task reduced-grobner-basis --measure --write
//! ```
//!
//! # Two modes, and only one of them produces a publishable figure
//!
//! **Exploratory** (the default) runs many rows in one process. It is for discovering which rows
//! finish and which refuse, and it reports **no memory figure at all** — `VmHWM` is process-wide,
//! so in a multi-row process it is a ceiling over every row and over whatever built their inputs.
//!
//! **Measured** (`--row <name> --measure`) runs exactly one row in its own process, which is what
//! makes a peak-RSS figure attributable to it. This is the mode `tools/benchlock.sh` should wrap,
//! and the only one whose rows belong in `research/competitive/`.
//!
//! The split is the same discipline `tools/scoreboard.sh`'s ladder tier already applies, and the
//! reasoning is `docs/research/external-comparison-protocol.md` §4.
//!
//! # What this program does not do
//!
//! It takes no ratios. `CompetitiveBoard::speedups` is the only place a ratio is computed, and
//! `examples/competitive` renders them. A sweep that also ranked would be a sweep that could
//! publish a ratio between two rows taken under different limits.

use std::{fs, path::Path, time::Duration};

use zeebra::grobner::{
    external::{
        corpus::{instance, ladder},
        CompetitiveBoard, CompetitiveRecord, ExternalSolver, GroebnerJlSolver, Instance, Limits,
        Measurement, MsolveSolver, RunFailure, RunReport, RunStatus, SagebrushSolver,
        SingularSolver, Task, ZeebraSolver,
    },
    research::{Environment, Json},
    F4Options,
};

const ROOT: &str = "research/competitive";

/// The tasks the sweep asks for, in the order a report reads them.
///
/// `ReducedGrobnerBasis` is the one every engine offers, so it is the column the comparison rests
/// on. `LexBasisByConversion` is where Zeebra's measured deficit lives (#283), so it is worth its
/// own column even though the three engines reach it by three different algorithms — which is a
/// finding, not a nuisance, and the report says so.
const TASKS: [Task; 2] = [Task::ReducedGrobnerBasis, Task::LexBasisByConversion];

/// The highest characteristic at which msolve's univariate eliminant is safe to ask for.
///
/// **A non-termination bound, not a performance one.** msolve's sparse-FGLM refuses
/// `p >= 1518500213` (`fglm_core.c:1385`), but the `NULL` it returns is laundered into the
/// genericity signal (`msolve.c:1740-1752`), which reaches a `goto restart` loop with no exit:
/// `add_linear_form_to_input_system` has no failure path and `undo_variable_order_change`
/// permanently returns 0 once a linear form exists. Measured on katsura-5 over `GF(2^31 − 1)`:
/// **25 353 retries and 1.37 M lines of output in 8 s, never exiting.**
///
/// The documented ceiling is `1515531529` (`linalg-fglm.c:38`) rather than msolve's own guard,
/// because the 2 968 684-wide window between them runs with no accumulation guarantee.
///
/// This matters here because `corpus::REFERENCE_CHARACTERISTIC` is `2^31 − 1`, which is **above**
/// it. So msolve is a *basis* comparand on the corpus field and **not an eliminant one**, and a
/// sweep that asked anyway would hang a worker until the wall limit killed it — producing a
/// `StoppedByLimit` row, which is timing-adjacent and wrong. The honest outcome is `Unsupported`,
/// and the cheapest way to guarantee it is never to ask.
const MSOLVE_ELIMINANT_CEILING: u64 = 1_515_531_529;

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let flag = |name: &str| arguments.iter().any(|a| a == name);
    let value = |name: &str| {
        arguments
            .iter()
            .position(|a| a == name)
            .and_then(|at| arguments.get(at + 1))
            .cloned()
    };

    let write = flag("--write");
    let measure = flag("--measure");
    let only_row = value("--row");
    let only_task = value("--task");
    // Which engines to run, so a board can be populated incrementally. An empty board is worse
    // than a two-library board, and a ten-minute lock hold is cheaper than a forty-minute one.
    let only_engines: Option<Vec<String>> =
        value("--engines").map(|list| list.split(',').map(|e| e.trim().to_string()).collect());
    let wall = Duration::from_secs(value("--wall").and_then(|s| s.parse().ok()).unwrap_or(600));

    let rows: Vec<String> = match &only_row {
        Some(name) => vec![name.clone()],
        None => ladder().into_iter().map(|e| e.name.to_string()).collect(),
    };
    let tasks: Vec<Task> = match &only_task {
        Some(tag) => vec![Task::from_tag(tag).unwrap_or_else(|| {
            panic!(
                "no task tagged {}; one of {:?}",
                tag,
                Task::all().map(|t| t.tag())
            )
        })],
        None => TASKS.to_vec(),
    };

    if flag("--list") {
        for name in &rows {
            for task in &tasks {
                println!("{} {}", name, task.tag());
            }
        }
        return;
    }

    // A measured run is one row in one process, or the memory figure means nothing. Refused rather
    // than silently downgraded: a harness that quietly dropped the figure would make a sweep look
    // like a measurement.
    if measure && only_row.is_none() {
        eprintln!(
            "--measure needs --row: a peak-RSS figure is only attributable in a process that \
             runs one row. See docs/research/external-comparison-protocol.md section 4."
        );
        std::process::exit(2);
    }

    let environment = detect_environment(wall, measure);
    println!("# Competitive sweep");
    println!("- machine: {}", environment.machine);
    println!("- cpu:     {}", environment.cpu);
    println!("- commit:  {}", environment.commit);
    println!("- build:   {}", environment.build);
    println!("- policy:  {}", environment.policy);
    println!(
        "- mode:    {}\n",
        if measure {
            "MEASURED (one row, this process, memory attributable)"
        } else {
            "exploratory (many rows per process, NO memory figure)"
        }
    );

    let mut board = CompetitiveBoard::new();
    let limits = Limits::wall(wall).with_workers(1);

    for name in &rows {
        // The characteristic argument is the corpus reference; Poseidon and Anemoi rows override
        // it with the registry's own field, because their constants are derived from the prime.
        let built = match instance(
            name,
            zeebra::grobner::external::corpus::REFERENCE_CHARACTERISTIC,
            zeebra::MonomialOrder::GradedReverseLexicographic,
        ) {
            Some(built) => built,
            None => {
                eprintln!("- {} is not in the corpus ladder", name);
                continue;
            }
        };

        for task in &tasks {
            // Refused rather than asked and timed out. See `MSOLVE_ELIMINANT_CEILING`: above it
            // msolve does not terminate, so the row would read as a limit stop where the truth is
            // a capability gap.
            if *task == Task::UnivariateEliminant
                && built.field.characteristic > MSOLVE_ELIMINANT_CEILING
            {
                eprintln!(
                    "- {} {}: skipped, GF({}) is above msolve's eliminant ceiling of {} where it \
                     does not terminate; this is Unsupported, not a limit stop",
                    built.name,
                    task.tag(),
                    built.field.characteristic,
                    MSOLVE_ELIMINANT_CEILING
                );
                continue;
            }
            run_one(
                &mut board,
                &built,
                *task,
                &limits,
                &environment,
                measure,
                only_engines.as_deref(),
            );
        }
    }

    println!();
    for row in board.rows() {
        println!(
            "- {:<30} {:<24} {:<12} {}",
            row.problem,
            row.task.to_string(),
            row.library,
            describe(row)
        );
    }

    if !write {
        println!(
            "\n({} rows; nothing written, pass --write to append to {}/)",
            board.rows().len(),
            ROOT
        );
        return;
    }
    append(&board);
}

/// Run one (instance, task) across every engine, recording every outcome.
///
/// Engines are constructed per row so that a measured run's scratch state cannot leak between
/// rows, and so an absent binary is reported once per row rather than aborting the sweep.
#[allow(clippy::too_many_arguments)]
fn run_one(
    board: &mut CompetitiveBoard,
    built: &Instance,
    task: Task,
    limits: &Limits,
    environment: &Environment,
    measure: bool,
    only: Option<&[String]>,
) {
    let wanted = |engine: &str| only.is_none_or(|list| list.iter().any(|e| e == engine));

    // Zeebra, with the wall limit pushed into F4's own cooperative budget so that a stop
    // *returns* and carries its statistics, rather than being abandoned.
    if wanted("zeebra") {
        let mut zeebra = ZeebraSolver::new().with_f4_options(F4Options {
            max_wall_time: Some(limits.wall),
            ..F4Options::default()
        });
        if measure {
            zeebra = zeebra.measuring_one_row();
        }
        let report = zeebra.run(built, task, limits);
        board.add(CompetitiveRecord::of(&report, built, environment));
    }

    // The four external engines. The scratch directory is per process and per row, which is what
    // keeps two concurrent sweeps from handing one filename to two processes.
    //
    // Every engine is probed once per row rather than once per sweep. That costs a process per
    // row and buys a version string on **every** record, including the rows of a sweep that was
    // interrupted — and a figure without a version is not reproducible.
    let scratch = std::env::temp_dir().join(format!(
        "zeebra-competitive-{}-{}",
        std::process::id(),
        built.name.replace('/', "-")
    ));

    if wanted("singular") {
        match SingularSolver::with_binary("Singular", scratch.join("singular"), limits.wall) {
            Ok(mut solver) => drive(board, &mut solver, built, task, limits, environment),
            Err(failure) => {
                unreachable_engine(board, "singular", built, task, limits, environment, failure)
            }
        }
    }

    if wanted("msolve") {
        let mut msolve = MsolveSolver::new(
            std::env::var("ZEEBRA_MSOLVE").unwrap_or_else(|_| "msolve".to_string()),
            scratch.join("msolve"),
        );
        drive(board, &mut msolve, built, task, limits, environment);
    }

    if wanted("groebner.jl") {
        match GroebnerJlSolver::from_env(scratch.join("groebner-jl")) {
            Ok(mut solver) => drive(board, &mut solver, built, task, limits, environment),
            Err(failure) => {
                unreachable_engine(board, "groebner.jl", built, task, limits, environment, failure)
            }
        }
    }

    if wanted("sagebrush") {
        match SagebrushSolver::from_env(scratch.join("sagebrush")) {
            Ok(mut solver) => drive(board, &mut solver, built, task, limits, environment),
            Err(failure) => {
                unreachable_engine(board, "sagebrush", built, task, limits, environment, failure)
            }
        }
    }

    let _ = fs::remove_dir_all(&scratch);
}

/// Record an engine that could not be started, instead of only mentioning it on stderr.
///
/// `RunFailure::Unavailable`'s own contract is that "a sweep must continue, the board must show
/// the row as not attempted, and nothing about Zeebra may be concluded from it". Printing and
/// dropping the row satisfied the first clause and broke the second: a board taken where an engine
/// was unreachable rendered identically to a board taken where it was never asked for, and the
/// generated artifact is what a reader has a year later.
#[allow(clippy::too_many_arguments)]
fn unreachable_engine(
    board: &mut CompetitiveBoard,
    id: &str,
    built: &Instance,
    task: Task,
    limits: &Limits,
    environment: &Environment,
    failure: RunFailure,
) {
    eprintln!("- {} unavailable: {}", id, failure);
    let report = RunReport::new(
        id,
        built,
        task,
        limits,
        RunStatus::Failed(failure),
        Measurement::unmeasured(),
    );
    board.add(CompetitiveRecord::of(&report, built, environment));
}

/// Probe one engine, run it, and record whatever came back.
///
/// Every outcome is recorded, including the ones with no answer: a board that kept only its
/// successes would report each engine's best cases as its behaviour. **Sagebrush is recorded but
/// must never be a speedup denominator** — five weeks old, nothing versioned, six F4 tests, and no
/// oracle in its own repository exercising the elimination. That is a maturity judgement and it is
/// enforced by the report rather than here, since the row itself is worth having.
fn drive(
    board: &mut CompetitiveBoard,
    solver: &mut dyn ExternalSolver,
    built: &Instance,
    task: Task,
    limits: &Limits,
    environment: &Environment,
) {
    let _ = solver.probe_version();
    let report = solver.run(built, task, limits);
    board.add(CompetitiveRecord::of(&report, built, environment));
}

/// One line describing a row's outcome, with the figure or the reason there is none.
fn describe(row: &CompetitiveRecord) -> String {
    match (&row.outcome.instead_of_a_time(), row.wall) {
        // No time, and the cell says why rather than showing a zero.
        (Some(reason), _) => reason.clone(),
        (None, Some(wall)) => {
            let memory = match row.peak_rss_bytes {
                Some(bytes) => format!(", {:.1} MB", bytes as f64 / (1u64 << 20) as f64),
                None => String::new(),
            };
            let dimension = match row.invariants.quotient_dimension {
                Some(dimension) => format!(", dim {}", dimension),
                None => String::new(),
            };
            format!(
                "{:>9.2} ms{}{}",
                wall.as_secs_f64() * 1e3,
                memory,
                dimension
            )
        }
        (None, None) => "answered, but no wall time recorded".to_string(),
    }
}

/// Append the board's rows to the accumulated history.
///
/// Append-only, like the cryptanalysis history and for the same reason: array position is the only
/// record of when a row was taken. See `COMPETITIVE_HISTORY_CONTRACT`.
fn append(board: &CompetitiveBoard) {
    let root = Path::new(ROOT);
    fs::create_dir_all(root.join("results")).expect("a writable directory");
    let path = root.join("results").join("history.json");

    let mut existing: Vec<Json> = match fs::read_to_string(&path) {
        Ok(text) => Json::parse(&text)
            .expect("the history this program wrote")
            .get("rows")
            .map(|rows| rows.items().to_vec())
            .unwrap_or_default(),
        Err(_) => Vec::new(),
    };
    existing.extend(board.rows().iter().map(CompetitiveRecord::to_json));

    let accumulated = Json::object([("rows", Json::Array(existing))]);
    let all = CompetitiveBoard::load(&accumulated).expect("the history this program wrote");
    fs::write(&path, all.to_json().to_json() + "\n").expect("a writable file");
    fs::write(root.join("COMPETITIVE.md"), all.to_markdown()).expect("a writable file");
    println!(
        "\nappended {} rows to {}/ ({} total)",
        board.rows().len(),
        ROOT,
        all.rows().len()
    );
}

/// The machine, build and commit this sweep ran on.
///
/// `Environment::policy` carries the limits summary, which is what makes two rows comparable or
/// not: `Environment::comparable` is half of `CompetitiveRecord::comparable_with`.
fn detect_environment(wall: Duration, measure: bool) -> Environment {
    let commit = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());
    let machine = std::env::var("ZEEBRA_MACHINE").unwrap_or_else(|_| {
        std::process::Command::new("hostname")
            .output()
            .ok()
            .and_then(|out| String::from_utf8(out.stdout).ok())
            .map(|s| s.trim().to_string())
            .unwrap_or_else(|| "unknown".to_string())
    });
    let cpu = fs::read_to_string("/proc/cpuinfo")
        .ok()
        .and_then(|text| {
            text.lines()
                .find(|line| line.starts_with("model name"))
                .and_then(|line| line.split_once(':'))
                .map(|(_, model)| model.trim().to_string())
        })
        .unwrap_or_else(|| "unknown".to_string());
    let affinity = std::env::var("ZEEBRA_AFFINITY").unwrap_or_else(|_| "unset".to_string());

    Environment {
        commit,
        machine,
        cpu: format!("{}, affinity {}", cpu, affinity),
        // One worker throughout. A cross-concurrency ratio is refused by the board, so a sweep
        // that varied this would produce rows that cannot be compared with each other.
        concurrency: 1,
        build: format!(
            "release, rustc {}",
            std::process::Command::new("rustc")
                .arg("--version")
                .output()
                .ok()
                .and_then(|out| String::from_utf8(out.stdout).ok())
                .map(|s| s.trim().to_string())
                .unwrap_or_else(|| "unknown".to_string())
        ),
        policy: format!(
            "{} s wall, 1 worker, {}",
            wall.as_secs(),
            if measure {
                "one row per process"
            } else {
                "many rows per process (no memory figure)"
            }
        ),
    }
}
