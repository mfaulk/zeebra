//! The M18 ablation study: every strategy combination, every system, one table.
//!
//! Each of M18-1, M18-2 and M18-3 was measured on its own against the M17 baseline. This measures
//! them **together**, because independent wins need not compose: M18-1 and M18-2 touch the same
//! quantity — the reductions the border needs — and M18-3 changes what every one of their columns
//! is stored as. The combination is what `FglmOptions::recommended()` has to be chosen from.
//!
//! Two of the milestone's changes cannot be ablated, and saying so is part of the result:
//!
//! * **M18-3's compact sparse representation** — `Box<[_]>` built with an exact capacity instead of
//!   a `Vec` grown by `collect` — is unconditional. It is 1.68x of the planted family's operator
//!   bytes and it is present in every row below, baseline included.
//! * **M18-4's triangular combination block** is unconditional too, so every row's `dense kB`
//!   already has it. §8.1 of `docs/MILESTONE-FGLM-SCALABILITY.md` measures it against the M17
//!   square block.
//!
//! So the `baseline` row is the M17 *strategies* at M18's representations, which is the comparison
//! a caller choosing a strategy today needs. §3.5 of the milestone has the M17 figures.
//!
//! Timings are taken with `measure_stages` off, which is what a caller runs: the stage clock reads
//! the clock several times per operator column and is itself a measurable fraction of a conversion
//! whose columns are unit vectors. The counters below are collected either way, so the memory
//! figures are exact.
//!
//! ```text
//! cargo run --release --example fglm_ablation            # every configuration
//! cargo run --release --example fglm_ablation -- fast    # skip planted-10
//! cargo run --release --example fglm_ablation -- list
//! ```
//!
//! Every configuration converts the identical source basis under the identical limits, with the lex
//! basis and the operators' nonzero count asserted equal to the baseline's — a configuration that
//! changes the answer is a defect, not a trade-off.

use std::{
    io::Write,
    time::{Duration, Instant},
};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        f4,
        fglm::{
            fglm_to_lex_with_options, BorderBatch, BorderBatchSize, FglmOptions, FglmStatistics,
            OperatorConstruction, OperatorStorage,
        },
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

const SOURCE: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// A configuration of the ablation, and what it turns on relative to the baseline.
struct Configuration {
    name: &'static str,
    purpose: &'static str,
    options: fn(FglmOptions) -> FglmOptions,
}

/// The unbounded batch size, with the closure limits lifted as well.
///
/// One batch for the whole border crosses `BorderBatch::recommended()`'s limits on the larger
/// instances, and refusing to measure it would hide the regression it is here to show.
fn unbounded_batch() -> BorderBatch {
    BorderBatch::unbounded().with_size(BorderBatchSize::Unbounded)
}

const CONFIGURATIONS: &[Configuration] = &[
    Configuration {
        name: "baseline",
        purpose: "M17's strategies: one normal form per column, sparse columns",
        options: |base| base,
    },
    Configuration {
        name: "1-dedup",
        purpose: "M18-1: one normal form per distinct border monomial",
        options: |base| base.with_operator_construction(OperatorConstruction::DeduplicatedBorder),
    },
    Configuration {
        name: "2-batch64",
        purpose: "M18-2: batched border reduction at the recommended size",
        options: |base| base.with_operator_construction(OperatorConstruction::BatchedBorder),
    },
    Configuration {
        name: "2-batch-inf",
        purpose: "M18-2's rejected size: one batch for the whole border",
        options: |base| {
            base.with_operator_construction(OperatorConstruction::BatchedBorder)
                .with_border_batch(unbounded_batch())
        },
    },
    Configuration {
        name: "3-adaptive",
        purpose: "M18-3: the per-column representation, on the baseline's reductions",
        options: |base| base.with_operator_storage(OperatorStorage::Adaptive),
    },
    Configuration {
        name: "3-dense",
        purpose: "M18-3's control: every reduced column dense, to show adaptive beating it",
        options: |base| base.with_operator_storage(OperatorStorage::Dense),
    },
    Configuration {
        name: "1+3",
        purpose: "does the compact representation cost the deduplicated path anything?",
        options: |base| {
            base.with_operator_construction(OperatorConstruction::DeduplicatedBorder)
                .with_operator_storage(OperatorStorage::Adaptive)
        },
    },
    Configuration {
        name: "2+3",
        purpose: "the recommended configuration: batched reduction, adaptive storage",
        options: |base| {
            base.with_operator_construction(OperatorConstruction::BatchedBorder)
                .with_operator_storage(OperatorStorage::Adaptive)
        },
    },
    Configuration {
        name: "2-inf+3-dense",
        purpose: "everything, including both rejections",
        options: |base| {
            base.with_operator_construction(OperatorConstruction::BatchedBorder)
                .with_border_batch(unbounded_batch())
                .with_operator_storage(OperatorStorage::Dense)
        },
    },
];

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

fn kilobytes(bytes: usize) -> f64 {
    bytes as f64 / 1024.0
}

/// One measured conversion: the fastest of `rounds` runs, and the basis it produced.
///
/// The minimum is the least noisy estimator under contention, since interference can only ever
/// make a run slower.
fn measure<const N: usize>(
    source: &[MultivariatePolynomial<N, F>],
    options: &FglmOptions,
    rounds: usize,
) -> Result<(Duration, FglmStatistics, Vec<MultivariatePolynomial<N, F>>), String> {
    let mut best: Option<(Duration, FglmStatistics)> = None;
    let mut basis = Vec::new();
    for _ in 0..rounds {
        let at = Instant::now();
        let (lex, statistics) =
            fglm_to_lex_with_options(source, SOURCE, options).map_err(|e| e.to_string())?;
        let wall = at.elapsed();
        if best.as_ref().is_none_or(|(previous, _)| wall < *previous) {
            best = Some((wall, statistics));
        }
        basis = lex;
    }
    let (wall, statistics) = best.expect("at least one round");
    Ok((wall, statistics, basis))
}

fn header() {
    println!(
        "{:<14} {:>9} {:>8} {:>10} {:>10} {:>10} {:>11} {:>8} {:>8} {:>8}",
        "configuration",
        "total/ms",
        "speedup",
        "oper kB",
        "dense kB",
        "total kB",
        "mem saved",
        "nf calls",
        "cells",
        "dense col",
    );
}

fn run<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>], rounds: usize) {
    let source = f4(system, SOURCE).expect("within F4's limits");
    let base = FglmOptions::baseline();

    println!();
    println!("=== {} / grevlex source ===", name);
    header();

    let mut reference: Option<(f64, f64, Vec<MultivariatePolynomial<N, F>>, usize)> = None;

    for configuration in CONFIGURATIONS {
        let options = (configuration.options)(base);
        match measure(&source, &options, rounds) {
            Ok((wall, statistics, basis)) => {
                let total = millis(wall);
                let bytes = kilobytes(statistics.estimated_bytes());
                let (speedup, saved) = match &reference {
                    Some((base_total, base_bytes, base_basis, base_entries)) => {
                        assert_eq!(
                            &basis, base_basis,
                            "{} / {}: the configuration changed the lex basis",
                            name, configuration.name
                        );
                        assert_eq!(
                            statistics.operator_entries, *base_entries,
                            "{} / {}: the configuration changed the operators' nonzero count",
                            name, configuration.name
                        );
                        (base_total / total, base_bytes / bytes)
                    }
                    None => {
                        reference = Some((total, bytes, basis, statistics.operator_entries));
                        (1.0, 1.0)
                    }
                };
                let memory = &statistics.memory;
                println!(
                    "{:<14} {:>9.2} {:>7.2}x {:>10.1} {:>10.1} {:>10.1} {:>10.2}x {:>8} {:>8} {:>8}",
                    configuration.name,
                    total,
                    speedup,
                    kilobytes(memory.operator_bytes),
                    kilobytes(memory.dense_block_bytes),
                    bytes,
                    saved,
                    statistics.border.normal_form_calls,
                    memory.operator_cells,
                    memory.dense_columns,
                );
            }
            Err(error) => println!("{:<14} {}", configuration.name, error),
        }
        std::io::stdout().flush().expect("stdout");
    }
}

fn planted_point<const N: usize>() -> Vec<F> {
    (0..N).map(|i| F::new(2 * i as u64 + 3)).collect()
}

fn main() {
    let argument = std::env::args().nth(1).unwrap_or_default();

    if argument == "list" {
        for configuration in CONFIGURATIONS {
            println!("{:<14} {}", configuration.name, configuration.purpose);
        }
        return;
    }
    let fast = argument == "fast";

    println!("# M18 ablation, GF(2^31 - 1), grevlex source, fastest of three");
    println!();
    println!("Every configuration converts the identical source basis at identical limits, with");
    println!("the lex basis and the operators' nonzero count asserted equal to the baseline's.");
    println!(
        "`speedup` and `mem saved` are against the `baseline` row, which is M17's strategies."
    );
    println!();
    println!("M18-3's compact sparse columns and M18-4's triangular combination block are not");
    println!(
        "option-gated, so they are in every row including the baseline and cannot be ablated;"
    );
    println!("§3.5 and §8.1 of docs/MILESTONE-FGLM-SCALABILITY.md hold the M17 figures they are");
    println!("measured against.");
    println!();
    println!("`oper kB` is the operators, `dense kB` the dependence test's three blocks, and");
    println!("`total kB` their sum — the whole of what a conversion of this dimension stores.");

    run::<5>("katsura-5", &katsura::<5, F>(), 3);
    run::<6>("katsura-6", &katsura::<6, F>(), 3);
    run::<7>("katsura-7", &katsura::<7, F>(), 3);
    run::<5>("cyclic-5", &cyclic::<5, F>(), 3);
    run::<6>("cyclic-6", &cyclic::<6, F>(), 3);
    run::<6>("planted-6", &planted::<6, F>(&planted_point::<6>()), 3);
    run::<8>("planted-8", &planted::<8, F>(&planted_point::<8>()), 3);

    if !fast {
        // The instance where a dense representation would need 51 MB and an unbounded batch is
        // slower than the scalar path: the two rejections are both visible here or nowhere.
        run::<10>("planted-10", &planted::<10, F>(&planted_point::<10>()), 3);
    }
}
