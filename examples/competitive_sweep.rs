//! Measured sweeps require one row and task per process so peak RSS belongs to that computation.
//! Exploratory sweeps report no memory; only the board applies comparison and publication gates.
//! See `docs/guide/external-engines.md` for commands and the field-dependent task defaults.

use std::{fs, path::Path, time::Duration};

use zeebra::{
    grobner::{
        external::{
            corpus::{instance, ladder, PUBLISHED_CHARACTERISTICS, REFERENCE_CHARACTERISTIC},
            msolve::{MAX_CHARACTERISTIC_ELIMINANT, MIN_CHARACTERISTIC_ELIMINANT},
            CompetitiveBoard, CompetitiveRecord, ExternalSolver, GiacSolver, GrobxSolver,
            GroebnerJlSolver, GroebnerRsSolver, Instance, Limits, Measurement, MsolveSolver,
            RunFailure, RunReport, RunStatus, SagebrushSolver, SingularSolver, Task, ZeebraSolver,
        },
        record::Environment,
        F4Options, InterreductionRoute,
    },
    util::Json,
};

const ROOT: &str = "research/competitive";

/// The tasks the sweep asks for, in the order a report reads them.
///
/// `ReducedGrobnerBasis` is the one every engine offers, so it is the column the comparison rests
/// on. `LexBasisByConversion` is where Zeebra's measured deficit lives (#283), so it is worth its
/// own column even though the three engines reach it by three different algorithms — which is a
/// finding, not a nuisance, and the report says so.
const TASKS: [Task; 2] = [Task::ReducedGrobnerBasis, Task::LexBasisByConversion];

// Default comparisons need an msolve operand; explicit tasks retain every adapter refusal.
fn sweep_tasks(characteristic: u64) -> Vec<Task> {
    let mut tasks = TASKS.to_vec();
    if (MIN_CHARACTERISTIC_ELIMINANT..MAX_CHARACTERISTIC_ELIMINANT).contains(&characteristic) {
        tasks.push(Task::UnivariateEliminant);
    }
    tasks
}

fn worker_count(value: Option<&str>) -> Result<usize, String> {
    match value {
        None => Ok(1),
        Some(raw) => raw
            .parse::<usize>()
            .ok()
            .filter(|n| (1..=1024).contains(n))
            .ok_or_else(|| "--workers requires an integer in 1..=1024".into()),
    }
}

fn memory_limit(value: Option<&str>) -> Result<Option<u64>, String> {
    value
        .map(|raw| {
            raw.parse::<u64>()
                .ok()
                .filter(|n| *n > 0)
                .and_then(|n| n.checked_mul(1024 * 1024))
                .ok_or_else(|| "--rss-mib requires a positive, representable byte ceiling".into())
        })
        .transpose()
}

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

    let workers = worker_count(value("--workers").as_deref()).unwrap_or_else(|error| {
        eprintln!("{error}");
        std::process::exit(2);
    });
    let max_rss = memory_limit(value("--rss-mib").as_deref()).unwrap_or_else(|error| {
        eprintln!("{error}");
        std::process::exit(2);
    });
    let write = flag("--write");
    let measure = flag("--measure");
    let only_row = value("--row");
    let only_task = value("--task");
    // Which engines to run, so a board can be populated incrementally. An empty board is worse
    // than a two-library board, and a ten-minute lock hold is cheaper than a forty-minute one.
    let only_engines: Option<Vec<String>> =
        value("--engines").map(|list| list.split(',').map(|e| e.trim().to_string()).collect());
    let wall = Duration::from_secs(value("--wall").and_then(|s| s.parse().ok()).unwrap_or(600));
    // Override F4's interreduction route for the Zeebra side. Named for the option rather than
    // for one of its values, so the request stays legible as the default moves: `division` is how
    // the pre-#478 route stays reachable now that `by-order` ships, and a bare presence flag could
    // not ask for it at all. Absent, the row is taken at `F4Options::default()`.
    let interreduction: Option<InterreductionRoute> =
        value("--interreduction").map(|v| match v.as_str() {
            "by-order" => InterreductionRoute::ByOrder,
            "division" => InterreductionRoute::Division,
            "matrix" => InterreductionRoute::Matrix,
            other => {
                eprintln!(
                    "--interreduction wants `by-order`, `division` or `matrix`, got {:?}",
                    other
                );
                std::process::exit(2);
            }
        });
    // Pay the main loop's interreduction debt where it is incurred (#477). Its own default is
    // also #507's to move, and the two flags interact: with batches left reduced the autoreduce
    // matrix falls from 7 642 x 7 996 to 252 x 606, which is the closure whose construction is
    // where `interreduction=matrix`'s memory goes. So the decision needs the 2x2, not two 1x2s.
    let reduce_batch_rows: Option<bool> = value("--reduce-batch-rows").map(|v| match v.as_str() {
        "on" => true,
        "off" => false,
        other => {
            eprintln!("--reduce-batch-rows wants `on` or `off`, got {:?}", other);
            std::process::exit(2);
        }
    });

    // Which corpus identity to sweep. A *published* characteristic only: a row at a field with no
    // frozen digest would be a figure whose problem nothing pins. See `PUBLISHED_CHARACTERISTICS`.
    let characteristic: u64 = value("--characteristic")
        .map(|s| {
            s.parse()
                .unwrap_or_else(|_| panic!("--characteristic wants an integer, got {:?}", s))
        })
        .unwrap_or(REFERENCE_CHARACTERISTIC);
    if !PUBLISHED_CHARACTERISTICS.contains(&characteristic) {
        eprintln!(
            "GF({}) is not a published corpus characteristic; one of {:?}. A row at an \
             unfrozen field is a figure whose identity nothing pins.",
            characteristic, PUBLISHED_CHARACTERISTICS
        );
        std::process::exit(2);
    }

    let rows = sweep_rows(characteristic, only_row.as_deref());
    if rows.is_empty() {
        eprintln!(
            "No published corpus rung matches {} over GF({})",
            only_row.as_deref().unwrap_or("the ladder"),
            characteristic
        );
        std::process::exit(2);
    }
    let tasks: Vec<Task> = match &only_task {
        Some(tag) => vec![Task::from_tag(tag).unwrap_or_else(|| {
            panic!(
                "no task tagged {}; one of {:?}",
                tag,
                Task::all().map(|t| t.tag())
            )
        })],
        None => sweep_tasks(characteristic),
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

    let environment = detect_environment(wall, measure, workers);
    println!("# Competitive sweep");
    println!("- machine: {}", environment.machine);
    println!("- cpu:     {}", environment.cpu);
    println!("- commit:  {}", environment.commit);
    println!("- build:   {}", environment.build);
    println!("- policy:  {}", environment.policy);
    println!("- field:   GF({})", characteristic);
    println!(
        "- mode:    {}\n",
        if measure {
            "MEASURED (one row, this process, memory attributable)"
        } else {
            "exploratory (many rows per process, NO memory figure)"
        }
    );

    let mut board = CompetitiveBoard::new();
    let mut limits = Limits::wall(wall).with_workers(workers);
    limits.max_rss_bytes = max_rss;

    for name in rows {
        let built = instance(
            name,
            characteristic,
            zeebra::MonomialOrder::GradedReverseLexicographic,
        )
        .expect("published rungs have a corpus instance");

        for task in &tasks {
            // Each adapter checks its own capability before execution, including msolve's
            // non-termination bounds. Keep its refusal without skipping other engines' answers.
            run_one(
                &mut board,
                &built,
                *task,
                &limits,
                &environment,
                measure,
                only_engines.as_deref(),
                interreduction,
                reduce_batch_rows,
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

fn sweep_rows(characteristic: u64, only_row: Option<&str>) -> Vec<&'static str> {
    ladder()
        .into_iter()
        .filter(|entry| only_row.is_none_or(|name| entry.name == name))
        .filter(|entry| entry.digest_at(characteristic).is_some())
        .map(|entry| entry.name)
        .collect()
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
    interreduction: Option<InterreductionRoute>,
    reduce_batch_rows: Option<bool>,
) {
    let wanted = |engine: &str| only.is_none_or(|list| list.iter().any(|e| e == engine));

    // Zeebra, with the wall limit pushed into F4's own cooperative budget so that a stop
    // *returns* and carries its statistics, rather than being abandoned.
    if wanted("zeebra") {
        let mut options = F4Options {
            max_wall_time: Some(limits.wall),
            ..F4Options::default()
        };
        if let Some(route) = interreduction {
            options.interreduction = route;
        }
        if let Some(reduced) = reduce_batch_rows {
            options.reduce_batch_rows = reduced;
        }
        let mut zeebra = ZeebraSolver::new().with_f4_options(options);
        if measure {
            zeebra = zeebra.measuring_one_row();
        }
        let report = zeebra.run(built, task, limits);
        board.add(CompetitiveRecord::of(&report, built, environment));
    }

    // The external engines. The scratch directory is per process and per row, which is what
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
            Err(failure) => unreachable_engine(
                board,
                "groebner.jl",
                built,
                task,
                limits,
                environment,
                failure,
            ),
        }
    }

    if wanted("groebner-rs") {
        match GroebnerRsSolver::from_env(scratch.join("groebner-rs")) {
            Ok(mut solver) => drive(board, &mut solver, built, task, limits, environment),
            Err(failure) => unreachable_engine(
                board,
                "groebner-rs",
                built,
                task,
                limits,
                environment,
                failure,
            ),
        }
    }

    if wanted("grobx") {
        match GrobxSolver::from_env(
            scratch.join("grobx"),
            zeebra::grobner::external::grobx::Mode::Raw,
        ) {
            Ok(mut solver) => drive(board, &mut solver, built, task, limits, environment),
            Err(failure) => {
                unreachable_engine(board, "grobx", built, task, limits, environment, failure)
            }
        }
    }

    if wanted("giac") {
        match GiacSolver::from_env(scratch.join("giac")) {
            Ok(mut solver) => drive(board, &mut solver, built, task, limits, environment),
            Err(failure) => {
                unreachable_engine(board, "giac", built, task, limits, environment, failure)
            }
        }
    }

    if wanted("sagebrush") {
        match SagebrushSolver::from_env(scratch.join("sagebrush")) {
            Ok(mut solver) => drive(board, &mut solver, built, task, limits, environment),
            Err(failure) => unreachable_engine(
                board,
                "sagebrush",
                built,
                task,
                limits,
                environment,
                failure,
            ),
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
fn detect_environment(wall: Duration, measure: bool, workers: usize) -> Environment {
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
        machine,
        cpu: format!("{}, affinity {}", cpu, affinity),
        concurrency: workers,
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
            "{} s wall, {workers} workers, {}",
            wall.as_secs(),
            if measure {
                "one row per process"
            } else {
                "many rows per process (no memory figure)"
            }
        ),
        // The commit, the merge base it was cut from and the patch id of the delta between them.
        // A sweep is run on a branch and merged, so the commit alone dangles — which is exactly
        // what happened to three of this board's four cohorts (#505).
        ..Environment::from_git()
    }
}

#[cfg(test)]
mod tests {
    use super::sweep_rows;
    use zeebra::grobner::external::corpus::BINARY_CHARACTERISTIC;

    // Worker counts default to one and accept positive bounded explicit cohorts.
    #[test]
    fn test_worker_cohort_argument() {
        assert_eq!(super::worker_count(None).unwrap(), 1);
        assert_eq!(super::worker_count(Some("4")).unwrap(), 4);
        for invalid in ["0", "-1", "many", "1025", "--measure"] {
            assert!(super::worker_count(Some(invalid)).is_err());
        }
    }

    // Explicit resident-memory ceilings are positive and cannot overflow bytes.
    #[test]
    fn test_memory_ceiling_argument() {
        assert_eq!(super::memory_limit(None).unwrap(), None);
        assert_eq!(
            super::memory_limit(Some("2048")).unwrap(),
            Some(2 * 1024 * 1024 * 1024)
        );
        for invalid in ["0", "-1", "all", "18446744073709551615"] {
            assert!(super::memory_limit(Some(invalid)).is_err());
        }
    }

    // The default small-prime sweep includes the eliminant comparison task.
    #[test]
    fn test_small_prime_sweep_includes_eliminants() {
        assert!(super::sweep_tasks(32003).contains(&super::Task::UnivariateEliminant));
    }

    // Default sweeps omit eliminants where msolve cannot safely compute them.
    #[test]
    fn test_default_tasks_respect_eliminant_characteristic_bounds() {
        for characteristic in [2, super::REFERENCE_CHARACTERISTIC] {
            assert!(!super::sweep_tasks(characteristic).contains(&super::Task::UnivariateEliminant));
        }
    }

    // The wide sweep selects only the three frozen wide planted identities.
    #[test]
    fn test_wide_sweep_selects_only_published_wide_rungs() {
        assert_eq!(
            sweep_rows(
                zeebra::grobner::external::corpus::WIDE_64_CHARACTERISTIC,
                None
            ),
            [
                "mq-planted-wide-6",
                "mq-planted-wide-10",
                "mq-planted-wide-14"
            ]
        );
        assert!(sweep_rows(super::REFERENCE_CHARACTERISTIC, Some("mq-planted-wide-6")).is_empty());
    }

    // The binary sweep lists seven Cyclic rungs and refuses an unpublished Katsura row.
    #[test]
    fn test_binary_sweep_only_selects_published_rows() {
        assert_eq!(
            sweep_rows(BINARY_CHARACTERISTIC, None),
            [
                "cyclic-4",
                "cyclic-5",
                "cyclic-6",
                "cyclic-7",
                "cyclic-8",
                "cyclic-9",
                "cyclic-10"
            ]
        );
        assert!(sweep_rows(BINARY_CHARACTERISTIC, Some("katsura-4")).is_empty());
    }
}
