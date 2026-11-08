//! The cost-model register's renderer: read the accumulated history, regenerate the Markdown.
//!
//! ```text
//! cargo run --release --example cost_model             # render to standard output
//! cargo run --release --example cost_model -- --write  # update research/cost-model/
//! cargo run --release --example cost_model -- --write --seed
//! cargo run --release --example cost_model -- --write --from-runs
//! ```
//!
//! **This program takes no measurements.** `research/cost-model/COST-MODEL.md` is generated from
//! `research/cost-model/results/history.json` and can never drift from it — the same reason
//! `SCOREBOARD.md` and `COMPETITIVE.md` are generated.
//!
//! `--from-runs` appends a row per **retained scoreboard run** that the register does not already
//! carry, through [`CostRow::from_run`]. That adapter is #334: the register used to get a figure
//! only when somebody remembered to transcribe one, and an emitted row carries the measured half
//! and nothing else — no prediction, and no limiting stage guessed from whichever budget was
//! crossed. Like `--seed` it is idempotent and append-only, matched on
//! [`CostRow::key`] **and** the source, which for an emitted row is the run's own record file.
//!
//! `--seed` appends any of
//! [`transcribed_rows`](zeebra::grobner::research::cost_model::transcribed_rows) that the history
//! does not already carry, matched on [`CostRow::key`] **and** the source. It is idempotent and it
//! is not an update path: the history is **append-only**, so a row already present is left exactly
//! as it was recorded. A re-measurement is a new row with a new commit.

use std::{fs, path::Path};

use zeebra::grobner::research::{
    cost_model::transcribed_rows, registry, CostModelBoard, CostRow, Json, RunRecord, Scoreboard,
    Stage, COST_MODEL_HISTORY_CONTRACT,
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

fn main() {
    let write = std::env::args().any(|argument| argument == "--write");
    let seed = std::env::args().any(|argument| argument == "--seed");
    let from_runs = std::env::args().any(|argument| argument == "--from-runs");
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

    if from_runs {
        let text = fs::read_to_string(SCOREBOARD_HISTORY).expect(SCOREBOARD_HISTORY);
        let history = Json::parse(&text).expect("the scoreboard history parses");
        let runs = Scoreboard::load(&history, &registry()).expect("every retained run is readable");
        let (mut appended, mut unclassified, mut already_present) = (0usize, 0usize, 0usize);
        for run in runs.runs() {
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
        // The skipped count is printed rather than swallowed. Two runs of one problem at one
        // commit are indistinguishable in the record -- the same limitation `run_file_stem` has,
        // and `RunRecord` deliberately carries no timestamp -- so the second cannot be told from
        // a re-run of this program, and 96 runs becoming 80 rows must be visible to the operator
        // rather than inferred.
        println!(
            "emitted {} rows from {} retained runs ({} already on the register or \
             indistinguishable from a row that is, {} ran no algorithm of their own)",
            appended,
            runs.runs().len(),
            already_present,
            unclassified
        );
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
