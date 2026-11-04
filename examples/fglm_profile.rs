//! Where an FGLM conversion's time and memory go, and how much of the border work repeats.
//!
//! M17 established that operator construction is almost all of a katsura conversion. It could not
//! say what inside it to attack, because one counter covered the monomial lookup, the reduction,
//! and the coordinate-vector assembly together. This reports them separately, alongside the
//! structure of the border — the number of nonstandard products against the number of *distinct*
//! nonstandard monomials, whose gap is the duplicated reduction M18-1 removes.
//!
//! Three tables, because they answer different questions:
//!
//! * **Border structure** bounds what deduplication can remove. Counts only, so it is exact and
//!   does not depend on the machine.
//! * **Stages** says where the time actually goes. Needs `FglmOptions::measure_stages`, which this
//!   sets.
//! * **Storage** says what the representations hold, and in particular how the operators compare
//!   against the dense blocks the dependence test needs. The answer is not uniform: on katsura the
//!   operators dominate and on the planted family the blocks are nearly forty times larger.
//!
//! A high duplication rate is evidence for deduplication and not proof of a speedup: the saving is
//! bounded by the `nf ms` column, not by the duplication rate. Nor do border monomials cost the
//! same to reduce — a repeated one is low in the order, which correlates with being cheap.
//!
//! ```text
//! cargo run --release --example fglm_profile
//! cargo run --release --example fglm_profile -- katsura-7 planted-8
//! ```

use std::{
    io::Write,
    time::{Duration, Instant},
};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        f4,
        fglm::{fglm_to_lex_with_options, FglmOptions, FglmStatistics},
    },
    util::peak_resident_bytes,
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

fn kilobytes(bytes: usize) -> f64 {
    bytes as f64 / 1024.0
}

/// One system's measurement, kept so both tables can be printed from one run of the conversion.
struct Row {
    name: &'static str,
    variables: usize,
    statistics: FglmStatistics,
    wall: Duration,
    peak_bytes: Option<u64>,
}

/// The conversion, measured. The fastest of three, since interference can only make a run slower.
fn measure<const N: usize>(name: &'static str, system: &[MultivariatePolynomial<N, F>]) -> Row {
    let source_order = MonomialOrder::GradedReverseLexicographic;
    let source = f4(system, source_order).expect("within limits");

    let mut options = FglmOptions::unbounded();
    options.measure_stages = true;

    let mut best: Option<(Duration, FglmStatistics)> = None;
    for _ in 0..3 {
        let at = Instant::now();
        let (_, statistics) =
            fglm_to_lex_with_options(&source, source_order, &options).expect("convertible");
        let wall = at.elapsed();
        if best.as_ref().is_none_or(|(previous, _)| wall < *previous) {
            best = Some((wall, statistics));
        }
    }
    let (wall, statistics) = best.expect("a round");

    Row {
        name,
        variables: N,
        statistics,
        wall,
        // Read after the conversion, and process-wide: it includes F4's peak and every earlier
        // system in this run. It is a ceiling on what the conversion used, not an attribution.
        peak_bytes: peak_resident_bytes(),
    }
}

fn border_header() {
    println!(
        "| {:<11} | {:>2} | {:>5} | {:>6} | {:>8} | {:>8} | {:>7} | {:>8} | {:>7} |",
        "system", "N", "D", "N*D", "standard", "border", "|∂B|", "repeated", "dup %",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(4),
        "-".repeat(7),
        "-".repeat(8),
        "-".repeat(10),
        "-".repeat(10),
        "-".repeat(9),
        "-".repeat(10),
        "-".repeat(9),
    );
}

fn border_row(row: &Row) {
    let b = row.statistics.border;
    println!(
        "| {:<11} | {:>2} | {:>5} | {:>6} | {:>8} | {:>8} | {:>7} | {:>8} | {:>7.1} |",
        row.name,
        row.variables,
        row.statistics.quotient_dimension,
        b.operator_columns,
        b.standard_columns,
        b.border_columns,
        b.distinct_border_monomials,
        b.repeated_border_columns(),
        100.0 * b.duplication_rate().unwrap_or(0.0),
    );
}

fn stage_header() {
    println!(
        "| {:<11} | {:>8} | {:>7} | {:>8} | {:>8} | {:>8} | {:>8} | {:>8} |",
        "system", "total ms", "basis", "classify", "nf ms", "assembly", "walk", "nf share",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(10),
        "-".repeat(9),
        "-".repeat(10),
        "-".repeat(10),
        "-".repeat(10),
        "-".repeat(10),
        "-".repeat(10),
    );
}

fn stage_row(row: &Row) {
    let t = row.statistics.timings;
    println!(
        "| {:<11} | {:>8.2} | {:>7.2} | {:>8.2} | {:>8.2} | {:>8.2} | {:>8.2} | {:>7.0}% |",
        row.name,
        millis(row.wall),
        millis(t.quotient_basis),
        millis(t.border_classification),
        millis(t.normal_forms),
        millis(t.column_assembly),
        millis(t.dependence),
        100.0 * t.normal_forms.as_secs_f64() / row.wall.as_secs_f64(),
    );
}

fn storage_header() {
    println!(
        "| {:<11} | {:>5} | {:>9} | {:>11} | {:>11} | {:>11} |",
        "system", "D", "entries", "operator kB", "blocks kB", "blocks/ops",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(7),
        "-".repeat(11),
        "-".repeat(13),
        "-".repeat(13),
        "-".repeat(13),
    );
}

fn storage_row(row: &Row) {
    let m = row.statistics.memory;
    println!(
        "| {:<11} | {:>5} | {:>9} | {:>11.1} | {:>11.1} | {:>10.1}x |",
        row.name,
        row.statistics.quotient_dimension,
        m.operator_entries,
        kilobytes(m.operator_bytes),
        kilobytes(m.dense_block_bytes),
        m.dense_block_bytes as f64 / m.operator_bytes as f64,
    );
}

fn planted_point<const N: usize>() -> Vec<F> {
    (0..N).map(|i| F::new(2 * i as u64 + 3)).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let wanted = |name: &str| args.is_empty() || args.iter().any(|a| a == name);

    let mut rows: Vec<Row> = Vec::new();
    if wanted("katsura-5") {
        rows.push(measure("katsura-5", &katsura::<5, F>()));
    }
    if wanted("katsura-6") {
        rows.push(measure("katsura-6", &katsura::<6, F>()));
    }
    if wanted("katsura-7") {
        rows.push(measure("katsura-7", &katsura::<7, F>()));
    }
    if wanted("cyclic-5") {
        rows.push(measure("cyclic-5", &cyclic::<5, F>()));
    }
    if wanted("cyclic-6") {
        rows.push(measure("cyclic-6", &cyclic::<6, F>()));
    }
    if wanted("planted-6") {
        rows.push(measure(
            "planted-6",
            &planted::<6, F>(&planted_point::<6>()),
        ));
    }
    if wanted("planted-8") {
        rows.push(measure(
            "planted-8",
            &planted::<8, F>(&planted_point::<8>()),
        ));
    }
    if wanted("planted-10") {
        rows.push(measure(
            "planted-10",
            &planted::<10, F>(&planted_point::<10>()),
        ));
    }

    println!("# FGLM border structure, GF(2^31 - 1), grevlex source");
    println!();
    border_header();
    for row in &rows {
        border_row(row);
    }
    println!();
    println!("`border` is the columns whose product left the staircase; `|∂B|` is how many");
    println!("*distinct* monomials those were. `dup %` is `repeated / border`, an upper bound on");
    println!("the reductions deduplication can remove — not on the time it can save.");

    println!();
    println!("# FGLM stages, fastest of three, measure_stages on");
    println!();
    stage_header();
    for row in &rows {
        stage_row(row);
    }

    println!();
    println!("`basis`, `classify`, `nf ms`, `assembly` and `walk` partition the conversion and");
    println!("are in milliseconds. `total ms` is its wall clock, which exceeds their sum by the");
    println!(
        "bookkeeping outside every stage. `nf share` is the reduction against that total: the"
    );
    println!("fraction of a conversion that deduplicating and batching the border could reach.");

    println!();
    println!("# FGLM storage");
    println!();
    storage_header();
    for row in &rows {
        storage_row(row);
    }

    println!();
    println!("`entries` is the operators' mathematical nonzeros; `operator kB` is what their");
    println!("columns actually hold, each Vec's spare capacity and the per-column spine included.");
    println!("`blocks kB` is the three dense D x D blocks the conversion needs at full rank — the");
    println!("dependence test's two and the retained accepted vectors, which no budget covers.");
    println!("Both are estimates of representations, not measurements of the process.");

    match peak_resident_bytes() {
        Some(peak) => {
            println!();
            println!(
                "Peak resident set for this whole process: {:.1} MB. Process-wide, so it covers",
                peak as f64 / (1024.0 * 1024.0)
            );
            println!("F4, every system above, and the allocator — not any one conversion.");
        }
        None => {
            println!();
            println!("Peak resident set is unavailable on this platform.");
        }
    }

    // The reading taken after each system. It is not a per-system attribution and the kernel does
    // not guarantee it rises monotonically, so it is printed as a sequence of readings rather than
    // differenced.
    if rows.iter().any(|row| row.peak_bytes.is_some()) {
        println!();
        print!("Peak after each system, MB:");
        for row in &rows {
            if let Some(peak) = row.peak_bytes {
                print!(" {} {:.0};", row.name, peak as f64 / (1024.0 * 1024.0));
            }
        }
        println!();
    }
    std::io::stdout().flush().expect("stdout");
}
