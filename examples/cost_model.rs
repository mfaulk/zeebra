//! The cost-model register's renderer: read the accumulated history, regenerate the Markdown.
//!
//! ```text
//! cargo run --release --example cost_model             # render to standard output
//! cargo run --release --example cost_model -- --write  # update research/cost-model/
//! cargo run --release --example cost_model -- --write --seed
//! ```
//!
//! **This program takes no measurements.** `research/cost-model/COST-MODEL.md` is generated from
//! `research/cost-model/results/history.json` and can never drift from it — the same reason
//! `SCOREBOARD.md` and `COMPETITIVE.md` are generated.
//!
//! `--seed` appends any of
//! [`transcribed_rows`](zeebra::grobner::research::cost_model::transcribed_rows) that the history
//! does not already carry, matched on [`CostRow::key`] **and** the source. It is idempotent and it
//! is not an update path: the history is **append-only**, so a row already present is left exactly
//! as it was recorded. A re-measurement is a new row with a new commit.

use std::{fs, path::Path};

use zeebra::grobner::research::{
    cost_model::transcribed_rows, CostModelBoard, Json, COST_MODEL_HISTORY_CONTRACT,
};

const ROOT: &str = "research/cost-model";

fn main() {
    let write = std::env::args().any(|argument| argument == "--write");
    let seed = std::env::args().any(|argument| argument == "--seed");
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
