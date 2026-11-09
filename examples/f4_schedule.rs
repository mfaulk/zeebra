//! What reordering the critical pairs of one degree is worth, and what it costs.
//!
//! M22-A. Three deterministic schedules, each of which discards nothing and therefore returns the
//! identical reduced Gröbner basis — asserted here on every row, not reported. What they change is
//! the matrix:
//!
//! - `degree-then-lcm` — the baseline, the order every earlier milestone measured.
//! - `small-multiplier` — within a degree, the smallest larger multiplier first. Sakata–Takagi's
//!   refined ordering.
//! - `large-multiplier` — the reverse, as a control. If small-multiplier-first narrows the matrix,
//!   large-multiplier-first should widen it; a heuristic that beats the baseline in both directions
//!   is measuring noise.
//!
//! **Ordering and batch sizing are measured separately**, because combining a new sort with a new
//! cap and attributing the whole difference to the sort is the easiest way to get a wrong answer
//! here. The first table varies the schedule at a fixed cap; the second varies the cap at a fixed
//! schedule; the third is the cross product on one instance.
//!
//! ```text
//! cargo run --release --example f4_schedule
//! cargo run --release --example f4_schedule -- list
//! cargo run --release --example f4_schedule -- katsura-6
//! ```
//!
//! Peak resident memory is read from the OS, so it is a high-water mark for the whole process and
//! not an attribution to one run. It is printed because the entry budget deliberately does not
//! cover the dense buffer, the column map, or allocator overhead — and a figure the budget omits
//! should at least be visible.

use std::time::Instant;

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4_with_options, F4Options, F4Statistics, PairSchedule,
    },
    util::peak_resident_bytes,
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type P = PrimeFieldElement64<2_147_483_647>;

const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// The batch caps compared. `None` is the default — every pair of the lowest degree.
const CAPS: [Option<usize>; 4] = [None, Some(64), Some(16), Some(4)];

/// The resource policy, stated once.
///
/// `max_batches` is here because a small cap multiplies the batch count: the same work is split
/// into many more matrices, and a configuration that would take an hour has to fail reproducibly
/// rather than being killed by whoever is watching. F4 has no cooperative time check, so a batch
/// count is the bound that can be enforced from inside.
fn options(schedule: PairSchedule, cap: Option<usize>) -> F4Options {
    F4Options {
        schedule,
        max_pairs_per_batch: cap,
        profile_degrees: true,
        max_matrix_columns: 60_000,
        max_live_bytes: 400_000_000,
        max_batches: Some(20_000),
        ..F4Options::default()
    }
}

/// One measured run.
struct Row {
    label: String,
    pairs_reduced: usize,
    batches: usize,
    max_columns: usize,
    peak_entries: usize,
    row_operations: usize,
    elements: usize,
    rank_contribution: usize,
    dependent: usize,
    millis: f64,
    estimated_bytes: usize,
    resident_bytes: Option<u64>,
}

fn measure(label: String, statistics: &F4Statistics, millis: f64) -> Row {
    Row {
        label,
        pairs_reduced: statistics.pairs_reduced,
        batches: statistics.batches,
        max_columns: statistics.max_matrix_columns,
        peak_entries: statistics.max_live_nonzeros,
        row_operations: statistics.row_operations,
        elements: statistics.elements_added,
        rank_contribution: statistics.candidate_rank_contribution,
        dependent: statistics.dependent_candidate_rows,
        millis,
        estimated_bytes: statistics.max_estimated_bytes,
        resident_bytes: peak_resident_bytes(),
    }
}

fn header(first: &str) {
    println!(
        "| {:<22} | {:>6} | {:>5} | {:>7} | {:>9} | {:>10} | {:>4} | {:>6} | {:>6} | {:>8} | {:>7} |",
        first,
        "pairs",
        "batch",
        "cols",
        "peak",
        "row ops",
        "new",
        "rank+",
        "dep",
        "ms",
        "RSS MB"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(24),
        "-".repeat(8),
        "-".repeat(7),
        "-".repeat(9),
        "-".repeat(11),
        "-".repeat(12),
        "-".repeat(6),
        "-".repeat(8),
        "-".repeat(8),
        "-".repeat(10),
        "-".repeat(9),
    );
}

fn print_row(row: &Row) {
    println!(
        "| {:<22} | {:>6} | {:>5} | {:>7} | {:>9} | {:>10} | {:>4} | {:>6} | {:>6} | {:>8} | {:>7} |",
        truncate(&row.label, 22),
        row.pairs_reduced,
        row.batches,
        row.max_columns,
        row.peak_entries,
        row.row_operations,
        row.elements,
        row.rank_contribution,
        row.dependent,
        format!("{:.1}", row.millis),
        row.resident_bytes
            .map(|b| format!("{:.0}", b as f64 / 1e6))
            .unwrap_or_else(|| "-".to_string()),
    );
    let _ = row.estimated_bytes;
}

fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        format!("{}…", s.chars().take(width - 1).collect::<String>())
    }
}

/// Run one configuration, asserting the basis is the one the baseline computes.
///
/// The assertion is the point of the program. A schedule discards nothing, so a reduced Gröbner
/// basis — which is unique for an ideal and an order — cannot move; a row that differed would be a
/// defect, and reporting it in a column rather than failing would bury it.
fn attempt<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    schedule: PairSchedule,
    cap: Option<usize>,
    reference: Option<&[MultivariatePolynomial<N, F>]>,
    label: String,
) -> Option<(Row, Vec<MultivariatePolynomial<N, F>>)> {
    let at = Instant::now();
    let result = f4_with_options(system, order, &options(schedule, cap));
    let millis = at.elapsed().as_secs_f64() * 1e3;

    match result {
        Ok((basis, statistics)) => {
            if let Some(reference) = reference {
                assert_eq!(
                    basis, reference,
                    "{}: a schedule changed the reduced Gröbner basis",
                    label
                );
            }
            Some((measure(label, &statistics, millis), basis))
        }
        Err(e) => {
            println!("| {:<22} | {} |", truncate(&label, 22), e);
            None
        }
    }
}

/// The instances, by name: each is built at its own compile-time dimension, so there is no one
/// type to hold them in.
fn instances() -> Vec<&'static str> {
    vec![
        "katsura-4",
        "katsura-5",
        "katsura-6",
        "cyclic-4",
        "cyclic-5",
        "cyclic-6",
    ]
}

/// Every schedule on one instance at one cap, with the bases asserted equal.
macro_rules! schedule_sweep {
    ($system:expr, $order:expr, $cap:expr, $prefix:expr) => {{
        let system = $system;
        let mut reference: Option<Vec<_>> = None;
        let mut rows = Vec::new();
        for schedule in PairSchedule::ALL {
            let label = format!("{}{}", $prefix, schedule.name());
            let outcome = attempt(&system, $order, schedule, $cap, reference.as_deref(), label);
            if let Some((row, basis)) = outcome {
                if reference.is_none() {
                    reference = Some(basis);
                }
                rows.push(row);
            }
        }
        rows
    }};
}

/// Every cap on one instance under one schedule, with the bases asserted equal.
macro_rules! cap_sweep {
    ($system:expr, $order:expr, $schedule:expr) => {{
        let system = $system;
        let mut reference: Option<Vec<_>> = None;
        let mut rows = Vec::new();
        for cap in CAPS {
            let label = match cap {
                None => "uncapped".to_string(),
                Some(cap) => format!("cap {}", cap),
            };
            let outcome = attempt(&system, $order, $schedule, cap, reference.as_deref(), label);
            if let Some((row, basis)) = outcome {
                if reference.is_none() {
                    reference = Some(basis);
                }
                rows.push(row);
            }
        }
        rows
    }};
}

/// Run one named instance through both sweeps.
fn run_instance(name: &str) {
    println!("### {}", name);
    println!();

    let schedule_rows = match name {
        "katsura-4" => schedule_sweep!(katsura::<4, P>(), GREVLEX, None, ""),
        "katsura-5" => schedule_sweep!(katsura::<5, P>(), GREVLEX, None, ""),
        "katsura-6" => schedule_sweep!(katsura::<6, P>(), GREVLEX, None, ""),
        "cyclic-4" => schedule_sweep!(cyclic::<4, P>(), GREVLEX, None, ""),
        "cyclic-5" => schedule_sweep!(cyclic::<5, P>(), GREVLEX, None, ""),
        "cyclic-6" => schedule_sweep!(cyclic::<6, P>(), GREVLEX, None, ""),
        other => {
            println!("unknown instance `{}`; `-- list` names them.\n", other);
            return;
        }
    };

    println!("Schedule, uncapped. Every row returned the same basis.");
    println!();
    header("schedule");
    for row in &schedule_rows {
        print_row(row);
    }
    println!();

    let cap_rows = match name {
        "katsura-4" => cap_sweep!(katsura::<4, P>(), GREVLEX, PairSchedule::DegreeThenLcm),
        "katsura-5" => cap_sweep!(katsura::<5, P>(), GREVLEX, PairSchedule::DegreeThenLcm),
        "katsura-6" => cap_sweep!(katsura::<6, P>(), GREVLEX, PairSchedule::DegreeThenLcm),
        "cyclic-4" => cap_sweep!(cyclic::<4, P>(), GREVLEX, PairSchedule::DegreeThenLcm),
        "cyclic-5" => cap_sweep!(cyclic::<5, P>(), GREVLEX, PairSchedule::DegreeThenLcm),
        "cyclic-6" => cap_sweep!(cyclic::<6, P>(), GREVLEX, PairSchedule::DegreeThenLcm),
        _ => Vec::new(),
    };

    println!("Batch cap, at the baseline schedule. Every row returned the same basis.");
    println!();
    header("cap");
    for row in &cap_rows {
        print_row(row);
    }
    println!();
}

/// The cross product, on one instance, so the two effects can be seen not to compose additively.
fn cross_product() {
    println!("## Schedule against cap, on katsura-5 grevlex");
    println!();
    println!(
        "The two are varied together here only to check whether the schedule's effect depends on \
         the cap. Each row still returned the baseline's basis."
    );
    println!();
    header("schedule / cap");
    let mut reference: Option<Vec<_>> = None;
    for schedule in PairSchedule::ALL {
        for cap in CAPS {
            let label = match cap {
                None => format!("{} / -", schedule.name()),
                Some(cap) => format!("{} / {}", schedule.name(), cap),
            };
            let outcome = attempt(
                &katsura::<5, P>(),
                GREVLEX,
                schedule,
                cap,
                reference.as_deref(),
                label,
            );
            if let Some((row, basis)) = outcome {
                if reference.is_none() {
                    reference = Some(basis);
                }
                print_row(&row);
            }
        }
    }
    println!();
}

fn main() {
    let argument = std::env::args().nth(1);
    if argument.as_deref() == Some("list") {
        println!("instances:");
        for name in instances() {
            println!("  {}", name);
        }
        return;
    }

    println!("# Critical-pair scheduling");
    println!();
    println!(
        "Configuration: `F4Options::recommended()` with `profile_degrees`, \
         `max_matrix_columns = 60_000`, `max_live_bytes = 400 MB`, grevlex throughout. \
         `cols` is the widest matrix, `peak` its live entries, `rank+` the rank the pair rows \
         added over the reducer block and `dep` the pair rows that added none. `RSS MB` is the \
         **process** high-water mark, so it only ever rises within one invocation."
    );
    println!();
    println!(
        "A schedule discards nothing, so every row below returned the identical reduced Gröbner \
         basis. That is asserted on each row rather than reported."
    );
    println!();

    println!("## Per instance");
    println!();
    match argument {
        Some(name) => run_instance(&name),
        None => {
            for name in instances() {
                run_instance(name);
            }
            cross_product();
        }
    }
}
