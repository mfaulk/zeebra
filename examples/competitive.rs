//! The competitive board's renderer: read the accumulated history, regenerate the Markdown.
//!
//! ```text
//! cargo run --release --example competitive            # render to standard output
//! cargo run --release --example competitive -- --write # update research/competitive/
//! ```
//!
//! **This program takes no measurements.** It exists so that `research/competitive/COMPETITIVE.md`
//! is generated from `research/competitive/results/history.json` and can never drift from it.
//! The rows arrive from the
//! per-library adapters, each of which appends to the history through
//! [`CompetitiveBoard`](zeebra::grobner::external::CompetitiveBoard).
//!
//! The history is **append-only**; see its `contract` field. An adapter appends its rows and
//! rewrites the file; nothing sorts or deduplicates it.

use std::{fs, path::Path};

use zeebra::{
    grobner::external::{CompetitiveBoard, COMPETITIVE_HISTORY_CONTRACT},
    util::Json,
};

const ROOT: &str = "research/competitive";

fn main() {
    let write = std::env::args().any(|argument| argument == "--write");
    let root = Path::new(ROOT);
    let history_path = root.join("results").join("history.json");

    let board = match fs::read_to_string(&history_path) {
        Ok(text) => {
            let history = Json::parse(&text).expect("the history this program wrote");
            CompetitiveBoard::load(&history).expect("every row is readable")
        }
        // No history yet is the normal state until the first adapter lands, and it renders as an
        // empty board rather than as a failure.
        Err(_) => CompetitiveBoard::new(),
    };

    let markdown = board.to_markdown();
    if !write {
        print!("{}", markdown);
        println!(
            "\n({} rows; nothing written, pass --write to update {}/)",
            board.rows().len(),
            ROOT
        );
        return;
    }

    fs::create_dir_all(root.join("results")).expect("a writable directory");
    // Rewritten rather than appended to, because this program adds no rows: what it writes back is
    // what it read, plus the contract if the file predated it.
    fs::write(&history_path, board.to_json().to_json() + "\n").expect("a writable file");
    fs::write(root.join("COMPETITIVE.md"), &markdown).expect("a writable file");
    println!(
        "wrote {} rows to {}/ (contract: {})",
        board.rows().len(),
        ROOT,
        &COMPETITIVE_HISTORY_CONTRACT[..40]
    );
}
