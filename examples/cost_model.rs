//! The cost-model register's renderer: read the accumulated history, regenerate the Markdown.
//!
//! ```text
//! cargo run --release --example cost_model             # render to standard output
//! cargo run --release --example cost_model -- --write  # update research/cost-model/
//! cargo run --release --example cost_model -- --write --seed
//! cargo run --release --example cost_model -- --list-runs
//! cargo run --release --example cost_model -- --write --from-runs <run-file-stem>
//! ```
//!
//! **This program takes no measurements.** `research/cost-model/COST-MODEL.md` is generated from
//! `research/cost-model/results/history.json` and can never drift from it — the same reason
//! `SCOREBOARD.md` and `COMPETITIVE.md` are generated.
//!
//! `--from-runs` appends a row for each **named** retained scoreboard run that the register does
//! not already carry, through [`CostRow::from_run`]. That adapter is #334: the register used to
//! get a figure only when somebody remembered to transcribe one, and an emitted row carries the
//! measured half and nothing else — no prediction, and no limiting stage guessed from whichever
//! budget was crossed. Like `--seed` it is idempotent and append-only, matched on
//! [`CostRow::key`] **and** the source, which for an emitted row is the run's own record file.
//!
//! **The register is curated, and `--from-runs` has no sweep** (#532). It takes one or more
//! record-file stems and refuses to run without one, so the dozens of prediction-less rows the
//! retained history would yield cannot be appended by somebody passing the flag to see what it
//! does.
//! [`select_runs_by_stem`] holds the reasoning and the refusal; `--list-runs` is the read-only way
//! to find a stem.
//!
//! `--seed` appends any of
//! [`transcribed_rows`](zeebra::grobner::research::cost_model::transcribed_rows) that the history
//! does not already carry, matched on [`CostRow::key`] **and** the source. It is idempotent and it
//! is not an update path: the history is **append-only**, so a row already present is left exactly
//! as it was recorded. A re-measurement is a new row with a new commit.

use std::{fs, path::Path};

use zeebra::grobner::research::{
    cost_model::transcribed_rows, registry, retained_run_stems, select_runs_by_stem,
    CostModelBoard, CostRow, Json, RunRecord, Scoreboard, Stage, COST_MODEL_HISTORY_CONTRACT,
};

const ROOT: &str = "research/cost-model";

/// Where the retained cryptanalysis runs are, which `--from-runs` reads and never writes.
const SCOREBOARD_HISTORY: &str = "research/scoreboard/results/history.json";

/// The algorithm label for a retained run, read off which stages it reported.
///
/// Exact for every run in the retained history: the F4 route reports a `grobner` stage, the
/// resultant route reports an `elimination` stage, and **no run reports both**. Asserted rather
/// than assumed, so that a third route cannot be quietly labelled as one of these two — the
/// register groups by this field, so a wrong label puts a figure under the wrong algorithm.
fn algorithm_of(run: &RunRecord) -> Option<&'static str> {
    match (
        run.stage(Stage::Grobner).is_some(),
        run.stage(Stage::Elimination).is_some(),
    ) {
        (true, false) => Some("f4"),
        (false, true) => Some("resultant-elimination"),
        (true, true) => panic!(
            "{} reports both a grobner and an elimination stage; the algorithm label this \
             program derives no longer distinguishes the routes",
            run.challenge
        ),
        // A campaign summary is a tally over its slices and ran no algorithm of its own. Skipped
        // rather than labelled, because "unclassified" in a register grouped by algorithm is worse
        // than absent.
        (false, false) => None,
    }
}

/// What the command line asked for.
struct Request {
    write: bool,
    seed: bool,
    list_runs: bool,
    /// `Some` if `--from-runs` appeared at all, holding the stems it named — **which may be
    /// empty**, and is the case [`select_runs_by_stem`] refuses. Kept separate from an empty
    /// vector so that a bare `--from-runs` is an error rather than a no-op.
    from_runs: Option<Vec<String>>,
}

/// Parse the arguments, refusing anything unrecognized.
///
/// Refusing rather than ignoring, because the argument this program must not mis-read is the one
/// naming a run: `--from-run poseidon...` silently rendering the register unchanged is how an
/// operator concludes the emission found nothing to do.
fn request(arguments: impl Iterator<Item = String>) -> Request {
    let mut request = Request {
        write: false,
        seed: false,
        list_runs: false,
        from_runs: None,
    };
    let mut arguments = arguments.peekable();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--write" => request.write = true,
            "--seed" => request.seed = true,
            "--list-runs" => request.list_runs = true,
            "--from-runs" => {
                let stems = request.from_runs.get_or_insert_with(Vec::new);
                // The stem is the next argument unless that is another flag; a bare `--from-runs`
                // leaves the selector empty on purpose.
                if let Some(stem) = arguments.next_if(|next| !next.starts_with("--")) {
                    stems.push(stem);
                }
            }
            other => match other.strip_prefix("--from-runs=") {
                Some(stem) => request
                    .from_runs
                    .get_or_insert_with(Vec::new)
                    .push(stem.to_string()),
                None => {
                    eprintln!("unrecognized argument {:?}", other);
                    eprintln!(
                        "usage: cost_model [--write] [--seed] [--list-runs] \
                         [--from-runs <run-file-stem>]..."
                    );
                    std::process::exit(2);
                }
            },
        }
    }
    request
}

/// The retained runs, which this program reads and never writes.
fn retained_runs() -> Scoreboard {
    let text = fs::read_to_string(SCOREBOARD_HISTORY).expect(SCOREBOARD_HISTORY);
    let history = Json::parse(&text).expect("the scoreboard history parses");
    Scoreboard::load(&history, &registry()).expect("every retained run is readable")
}

/// Print the stems `--from-runs` accepts, which replaces the sweep as the way to see the field.
///
/// Writes nothing. The census line is the one the sweep used to print, and it is the honest form
/// of it: the retained runs outnumber the addressable records, and the sixteen that share a stem
/// with another are named as runs no row can cite rather than as rows that happened not to be
/// emitted.
fn list_runs(board: &CostModelBoard) {
    let scoreboard = retained_runs();
    let runs = scoreboard.runs();
    let stems = retained_run_stems(runs);
    let (mut held, mut unclassified, mut repeats) = (0usize, 0usize, 0usize);
    for (stem, count) in &stems {
        let run = runs
            .iter()
            .rev()
            .find(|run| &run.run_file_stem() == stem)
            .expect("the stem came from these runs");
        let algorithm = algorithm_of(run);
        if algorithm.is_none() {
            unclassified += 1;
        }
        let source = format!("research/scoreboard/runs/{}.json", stem);
        let on_register = board.rows().iter().any(|row| row.source == source);
        if on_register {
            held += 1;
        }
        repeats += count - 1;
        println!(
            "{}\t{}{}{}",
            stem,
            algorithm.unwrap_or("no algorithm of its own"),
            if on_register {
                "\talready on the register"
            } else {
                ""
            },
            if *count > 1 {
                format!(
                    "\t{} runs share this stem; {} cannot be cited",
                    count,
                    count - 1
                )
            } else {
                String::new()
            }
        );
    }
    println!(
        "\n{} addressable stems over {} retained runs ({} runs share a stem with another and have \
         no record file to cite, see #540; {} already on the register, {} ran no algorithm of \
         their own)",
        stems.len(),
        runs.len(),
        repeats,
        held,
        unclassified
    );
}

/// Append a row for each named run the register does not already carry.
fn emit_named_rows(board: &mut CostModelBoard, stems: &[String]) {
    let scoreboard = retained_runs();
    let selection = match select_runs_by_stem(scoreboard.runs(), stems) {
        Ok(selection) => selection,
        Err(error) => {
            eprintln!("--from-runs: {}", error);
            eprintln!("name a run's record-file stem; `--list-runs` prints the candidates");
            std::process::exit(2);
        }
    };
    // Printed rather than swallowed. Only the last run written under a stem is in the record tree,
    // so the earlier ones have no source to cite and no row is emitted for them -- the operator
    // must see that a named stem covered more runs than it produced rows.
    for (stem, count) in &selection.shadowed {
        eprintln!(
            "{}: {} retained runs share this stem and the record file holds only the last, so {} \
             of them get no row (#540)",
            stem,
            count,
            count - 1
        );
    }
    let (mut appended, mut unclassified, mut already_present) = (0usize, 0usize, 0usize);
    for run in &selection.runs {
        let Some(algorithm) = algorithm_of(run) else {
            unclassified += 1;
            continue;
        };
        let row = CostRow::from_run(run, algorithm);
        let already = board
            .rows()
            .iter()
            .any(|stored| stored.key() == row.key() && stored.source == row.source);
        if already {
            already_present += 1;
            continue;
        }
        board.add(row).expect("an emitted row is a legal row");
        appended += 1;
    }
    println!(
        "emitted {} rows from {} named runs ({} already on the register, {} ran no algorithm of \
         their own)",
        appended,
        selection.runs.len(),
        already_present,
        unclassified
    );
}

fn main() {
    let Request {
        write,
        seed,
        list_runs: list,
        from_runs,
    } = request(std::env::args().skip(1));
    let root = Path::new(ROOT);
    let history_path = root.join("results").join("history.json");

    let mut board = match fs::read_to_string(&history_path) {
        Ok(text) => {
            let history = Json::parse(&text).expect("the history this program wrote");
            CostModelBoard::load(&history).expect("every row is readable and self-consistent")
        }
        // No history yet renders as an empty register rather than as a failure.
        Err(_) => CostModelBoard::new(),
    };

    if seed {
        let mut appended = 0usize;
        for row in transcribed_rows() {
            let already = board
                .rows()
                .iter()
                .any(|stored| stored.key() == row.key() && stored.source == row.source);
            if already {
                continue;
            }
            board.add(row).expect("a transcribed row is a legal row");
            appended += 1;
        }
        println!("seeded {} transcribed rows", appended);
    }

    if list {
        list_runs(&board);
        return;
    }

    if let Some(stems) = &from_runs {
        emit_named_rows(&mut board, stems);
    }

    let markdown = board.to_markdown();
    if !write {
        print!("{}", markdown);
        println!(
            "\n({} rows, {} with a prediction nobody has checked; nothing written, pass --write \
             to update {}/)",
            board.rows().len(),
            board.open_predictions().len(),
            ROOT
        );
        return;
    }

    fs::create_dir_all(root.join("results")).expect("a writable directory");
    fs::write(&history_path, board.to_json().to_json() + "\n").expect("a writable file");
    fs::write(root.join("COST-MODEL.md"), &markdown).expect("a writable file");
    println!(
        "wrote {} rows to {}/ (contract: {})",
        board.rows().len(),
        ROOT,
        COST_MODEL_HISTORY_CONTRACT
    );
}
