//! Whether the batched border reduction's independent target loop is worth parallelizing.
//!
//! §6.4 of `docs/MILESTONE-SIMD-PARALLELISM.md` closed three parallelism sub-milestones on one
//! argument — what matters is a stage's size **per batch**, not its share of the total — and asked
//! anyone revisiting the question to start from that measurement rather than from the block
//! structure. This is that measurement for the one loop in the project whose iterations are
//! genuinely independent: the pivots of a border batch are fixed before any target is touched, so
//! `NF(u_1)` cannot involve `u_2` and the targets may be split anywhere.
//!
//! Four tables, in the order the decision needs them:
//!
//! 1. **Per batch.** The batch clock split between the symbolic closure and the target loop, so the
//!    parallelizable half is separated from the half that is not. Only the target loop is a
//!    candidate; the closure is a sequential discovery.
//! 2. **The floor.** What dispatching work to `W` scoped threads costs on this machine, measured
//!    with the same `std::thread::scope` pattern the project's two shipped parallel paths use. A
//!    per-batch reduction below this is not parallelizable at any thread count.
//! 3. **The carry.** `reduce_targets` carries `dirty_from` — the previous target's leading column —
//!    across iterations, and a split gives that up at each group boundary. Measured as the cells
//!    zeroed and the wall clock of the *sequential* grouped reduction, so the carry's cost is
//!    separated from any thread-dispatch cost rather than tangled with it.
//! 4. **The sweep.** The reduction actually run on `W` scoped threads, with its speedup and its
//!    parallel efficiency, and every row's remainders asserted bit-identical to the one-worker
//!    row's. This is what the first three tables predict and what the decision is made on.
//!
//! A table name selects one; the rest of the arguments select systems. The three single-threaded
//! tables want one pinned core and the floor and the sweep want every core idle, which is why they
//! are not printed together.
//!
//! ```text
//! cargo run --release --example fglm_parallel -- per-batch
//! cargo run --release --example fglm_parallel -- sweep katsura-7 planted-10
//! ```

use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        f4,
        fglm::{
            fglm_to_lex_with_options, measure_border_reduction, BorderBatch, BorderBatchSize,
            BorderReduction, FglmOptions, FglmStatistics, OperatorConstruction,
        },
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

const SOURCE: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// Worker counts the sweep reports, up to this machine's 128 hardware threads.
const WORKERS: [usize; 8] = [1, 2, 4, 8, 16, 32, 64, 128];

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

fn planted_point<const N: usize>() -> Vec<F> {
    (0..N).map(|i| F::new(2 * i as u64 + 3)).collect()
}

/// The batch geometry under measurement, with the budgets lifted so none of them fires.
fn options(size: BorderBatchSize, groups: usize) -> FglmOptions {
    let mut options = FglmOptions::unbounded()
        .with_operator_construction(OperatorConstruction::BatchedBorder)
        .with_border_batch(
            BorderBatch::unbounded()
                .with_size(size)
                .with_reduction(BorderReduction::Grouped(groups)),
        );
    options.measure_stages = true;
    options
}

/// One conversion, fastest of three: interference can only make a run slower.
fn convert<const N: usize>(
    source: &[MultivariatePolynomial<N, F>],
    size: BorderBatchSize,
    groups: usize,
) -> (Duration, FglmStatistics) {
    let options = options(size, groups);
    let mut best: Option<(Duration, FglmStatistics)> = None;
    for _ in 0..3 {
        let at = Instant::now();
        let (_, statistics) =
            fglm_to_lex_with_options(source, SOURCE, &options).expect("convertible");
        let wall = at.elapsed();
        if best.as_ref().is_none_or(|(previous, _)| wall < *previous) {
            best = Some((wall, statistics));
        }
    }
    best.expect("a round")
}

fn per_batch_header() {
    println!(
        "| {:<11} | {:>9} | {:>7} | {:>9} | {:>9} | {:>10} | {:>9} | {:>7} |",
        "system", "size", "batches", "closure", "reduce", "reduce/bat", "peak bat", "conv"
    );
    println!(
        "|{:-<13}|{:->11}|{:->9}|{:->11}|{:->11}|{:->12}|{:->11}|{:->9}|",
        "", "", "", "", "", "", "", ""
    );
}

/// A system's batch clock at one batch size, split between the closure and the target loop.
fn per_batch_row<const N: usize>(
    name: &str,
    source: &[MultivariatePolynomial<N, F>],
    size: BorderBatchSize,
    label: &str,
) {
    let (wall, statistics) = convert(source, size, 1);
    let batches = statistics.batches;
    let per_batch = millis(batches.reduction_time) / (batches.batches.max(1) as f64);
    println!(
        "| {:<11} | {:>9} | {:>7} | {:>9.3} | {:>9.3} | {:>10.4} | {:>9.4} | {:>7.2} |",
        name,
        label,
        batches.batches,
        millis(batches.closure_time),
        millis(batches.reduction_time),
        per_batch,
        millis(batches.peak_reduction_time),
        millis(wall),
    );
}

/// What handing work to `workers` scoped threads costs, with no work in it.
///
/// The same `std::thread::scope` over contiguous blocks that `sample_determinants` and the
/// differential sweep use, so the figure is this project's dispatch cost and not a thread pool's.
/// Each worker writes its own block of a pre-sized vector, which is the shape the reduction would
/// take; the write is there so the spawn cannot be optimized away.
fn dispatch_cost(workers: usize, rounds: usize) -> Duration {
    let mut slots = vec![0u64; workers.max(1)];
    let mut best = Duration::MAX;
    for _ in 0..rounds {
        let at = Instant::now();
        if workers <= 1 {
            for (index, slot) in slots.iter_mut().enumerate() {
                *slot = index as u64;
            }
        } else {
            std::thread::scope(|scope| {
                for (index, slot) in slots.iter_mut().enumerate() {
                    scope.spawn(move || {
                        *slot = index as u64;
                    });
                }
            });
        }
        best = best.min(at.elapsed());
        std::hint::black_box(&slots);
    }
    best
}

fn dispatch_table() {
    println!(
        "| {:>7} | {:>12} | {:>14} |",
        "workers", "dispatch/ms", "per worker/µs"
    );
    println!("|{:->9}|{:->14}|{:->16}|", "", "", "");
    for workers in WORKERS {
        let cost = dispatch_cost(workers, 200);
        println!(
            "| {:>7} | {:>12.4} | {:>14.2} |",
            workers,
            millis(cost),
            cost.as_secs_f64() * 1e6 / (workers as f64)
        );
    }
}

fn carry_header() {
    println!(
        "| {:<11} | {:>9} | {:>7} | {:>13} | {:>9} | {:>9} | {:>7} |",
        "system", "size", "groups", "cells zeroed", "x cells", "reduce", "x time"
    );
    println!(
        "|{:-<13}|{:->11}|{:->9}|{:->15}|{:->11}|{:->11}|{:->9}|",
        "", "", "", "", "", "", ""
    );
}

/// The `dirty_from` carry's cost, as the groups it is given up at.
///
/// Sequential throughout: the groups run one after another, so the only difference between the rows
/// is the carry. A parallel reduction at `W` workers would compute exactly the `W`-group row and
/// then divide its wall clock by the workers that actually ran.
fn carry_row<const N: usize>(
    name: &str,
    source: &[MultivariatePolynomial<N, F>],
    size: BorderBatchSize,
    label: &str,
) {
    let (_, one) = convert(source, size, 1);
    let base_cells = one.batches.buffer_cells_zeroed.max(1) as f64;
    let base_time = millis(one.batches.reduction_time).max(f64::MIN_POSITIVE);

    for groups in WORKERS {
        let (_, statistics) = convert(source, size, groups);
        let cells = statistics.batches.buffer_cells_zeroed;
        let time = millis(statistics.batches.reduction_time);
        assert_eq!(
            statistics.batches.reducer_entries, one.batches.reducer_entries,
            "{}: grouping changed the closure",
            name
        );
        println!(
            "| {:<11} | {:>9} | {:>7} | {:>13} | {:>9.3} | {:>9.3} | {:>7.3} |",
            name,
            label,
            groups,
            cells,
            cells as f64 / base_cells,
            time,
            time / base_time,
        );
    }
}

fn sweep_header() {
    println!(
        "| {:<11} | {:>9} | {:>7} | {:>9} | {:>9} | {:>7} | {:>10} | {:>13} |",
        "system", "size", "workers", "reduce", "peak bat", "speedup", "efficiency", "cells zeroed"
    );
    println!(
        "|{:-<13}|{:->11}|{:->9}|{:->11}|{:->11}|{:->9}|{:->12}|{:->15}|",
        "", "", "", "", "", "", "", ""
    );
}

/// The parallel reduction's wall clock and efficiency against one worker.
///
/// The whole border, batched at `size`, with the target loop on `W` scoped threads. The digest of
/// every remainder is asserted equal to the one-worker digest on every row, so a speedup printed
/// here is a speedup at the right answer.
fn sweep_row<const N: usize>(
    name: &str,
    source: &[MultivariatePolynomial<N, F>],
    size: BorderBatchSize,
    label: &str,
) {
    let limits = BorderBatch::unbounded().with_size(size);
    let run = |workers: usize| {
        let mut best: Option<(Duration, Duration, usize)> = None;
        let mut digest = None;
        for _ in 0..3 {
            let (statistics, got) =
                measure_border_reduction(source, SOURCE, &limits, workers).expect("within limits");
            assert!(
                digest.is_none_or(|d| d == got),
                "{}: a repeat at {} workers changed the remainders",
                name,
                workers
            );
            digest = Some(got);
            let round = (
                statistics.reduction_time,
                statistics.peak_reduction_time,
                statistics.buffer_cells_zeroed,
            );
            if best
                .as_ref()
                .is_none_or(|(previous, _, _)| round.0 < *previous)
            {
                best = Some(round);
            }
        }
        (best.expect("a round"), digest.expect("a round"))
    };

    let ((base, _, _), reference) = run(1);
    for workers in WORKERS {
        let ((total, peak, cells), digest) = run(workers);
        assert_eq!(
            digest, reference,
            "{}: {} workers computed different remainders",
            name, workers
        );
        let speedup = millis(base) / millis(total).max(f64::MIN_POSITIVE);
        println!(
            "| {:<11} | {:>9} | {:>7} | {:>9.3} | {:>9.4} | {:>6.2}x | {:>9.1}% | {:>13} |",
            name,
            label,
            workers,
            millis(total),
            millis(peak),
            speedup,
            100.0 * speedup / (workers as f64),
            cells,
        );
    }
}

/// Every table for one system, at the recommended batch size and unbounded.
///
/// The source Gröbner basis is computed once, outside every timed region: this measures the
/// conversion and not F4.
fn measure<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>], which: Table) {
    let source = &f4(system, SOURCE).expect("within limits");
    match which {
        Table::PerBatch => {
            per_batch_row(name, source, BorderBatchSize::Fixed(64), "64");
            per_batch_row(name, source, BorderBatchSize::Unbounded, "unbounded");
        }
        Table::Carry => {
            carry_row(name, source, BorderBatchSize::Unbounded, "unbounded");
        }
        Table::Sweep => {
            sweep_row(name, source, BorderBatchSize::Fixed(64), "64");
            sweep_row(name, source, BorderBatchSize::Unbounded, "unbounded");
        }
    }
}

#[derive(Clone, Copy)]
enum Table {
    PerBatch,
    Carry,
    Sweep,
}

/// Every system in the corpus, filtered by the names on the command line.
fn for_each_system(which: Table, wanted: &dyn Fn(&str) -> bool) {
    if wanted("katsura-5") {
        measure("katsura-5", &katsura::<5, F>(), which);
    }
    if wanted("katsura-6") {
        measure("katsura-6", &katsura::<6, F>(), which);
    }
    if wanted("katsura-7") {
        measure("katsura-7", &katsura::<7, F>(), which);
    }
    if wanted("cyclic-5") {
        measure("cyclic-5", &cyclic::<5, F>(), which);
    }
    if wanted("cyclic-6") {
        measure("cyclic-6", &cyclic::<6, F>(), which);
    }
    if wanted("planted-6") {
        measure("planted-6", &planted::<6, F>(&planted_point::<6>()), which);
    }
    if wanted("planted-8") {
        measure("planted-8", &planted::<8, F>(&planted_point::<8>()), which);
    }
    if wanted("planted-10") {
        measure(
            "planted-10",
            &planted::<10, F>(&planted_point::<10>()),
            which,
        );
    }
}

fn main() {
    // The three tables want different machine conditions — two are single-threaded and the floor
    // needs every core idle — so each is selectable rather than always printed together.
    const TABLES: [&str; 4] = ["per-batch", "floor", "carry", "sweep"];
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (tables, systems): (Vec<String>, Vec<String>) =
        args.into_iter().partition(|a| TABLES.contains(&a.as_str()));
    let table = |name: &str| tables.is_empty() || tables.iter().any(|t| t == name);
    let wanted = move |name: &str| systems.is_empty() || systems.iter().any(|a| a == name);

    if table("per-batch") {
        println!("# Border reduction, per batch — GF(2^31 - 1), grevlex source, fastest of three");
        println!();
        println!(
            "Milliseconds. `closure` and `reduce` are the two halves of the batch clock summed"
        );
        println!("over the batches; `reduce/bat` is the mean and `peak bat` the largest single");
        println!("batch. **`peak bat` is the figure that decides this**: a parallel reduction");
        println!("dispatches once per batch, so what it has to beat is one batch's target loop.");
        println!();
        per_batch_header();
        for_each_system(Table::PerBatch, &wanted);
        println!();
    }

    if table("floor") {
        println!("# The floor: `std::thread::scope` dispatch on this machine, best of 200");
        println!();
        println!("No work in it, so this is the cost of the spawn and the join alone. A per-batch");
        println!("reduction below the row for `W` workers cannot be made faster by `W` of them.");
        println!();
        dispatch_table();
        println!();
    }

    if table("carry") {
        println!("# The `dirty_from` carry, given up at each group boundary");
        println!();
        println!(
            "Sequential: the groups run one after another, so the only difference between rows"
        );
        println!(
            "is the carry. `cells zeroed` counts the buffers' allocation and the clear before"
        );
        println!(
            "each target — a group's first target starts from a fresh buffer, which is already"
        );
        println!("zero, so a group costs one full width and its members cost their dirty tails.");
        println!();
        carry_header();
        for_each_system(Table::Carry, &wanted);
        println!();
    }

    if table("sweep") {
        println!("# The parallel reduction, swept over workers — best of three per cell");
        println!();
        println!("The target loop on `W` scoped threads, contiguous blocks, remainders in target");
        println!("order. `reduce` is the whole border's reduction and `peak bat` the largest");
        println!("single batch; `efficiency` is the speedup over the worker count. Every row's");
        println!("remainders are asserted bit-identical to the one-worker row's.");
        println!();
        sweep_header();
        for_each_system(Table::Sweep, &wanted);
    }
}
