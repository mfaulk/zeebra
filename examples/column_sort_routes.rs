//! Construction's column sort, stable against unstable, on one build in one process (#583).
//!
//! #330's column handout replaced a vector in first-appearance order with one drained from a hash
//! set, and `slice::sort_by` is an adaptive merge sort that had runs to exploit in the first and
//! none in the second. The question this answers is whether `sort_unstable_by` — pdqsort, with
//! different adaptivity and no stability to maintain — is simply faster on the input construction
//! actually hands it, which would make the ordering question moot.
//!
//! Construction does not need stability: each monomial order returns `Equal` only for equal
//! monomials (`test_orders_are_total`) and the columns are distinct
//! (`test_columns_are_distinct_and_descending`), so the sorted sequence is unique and the unstable
//! sort cannot reorder anything. The arms assert equal output as well as timing it, because a
//! timing for two different column orders would mean nothing.

use std::hint::black_box;
use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4::symbolic_preprocessing,
        trace_batches, F4Options, PairCriteria, ReductionStrategy,
    },
    linalg::Backend,
    Monomial, MonomialOrder,
};

type F = Zp2147483647;

const REPETITIONS: usize = 9;

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

/// `configuration("recommended")` from `examples/f4_profile.rs`, mirrored so the batches replayed
/// here are the batches §8.5 and #582's tables were taken over. Keep the two in step.
fn recommended() -> F4Options {
    F4Options {
        reduction: ReductionStrategy::Structured,
        criteria: PairCriteria::ALL,
        elimination: Backend::Adaptive,
        measure_stages: true,
        ..F4Options::baseline()
    }
}

fn main() {
    println!(
        "{:<12} {:<8} {:>7} {:>9} {:>11} {:>9} {:>9}",
        "system", "order", "batches", "cols", "stable/ms", "unstab/ms", "ratio"
    );

    macro_rules! arm {
        ($name:expr, $order:expr, $system:expr) => {'arm: {
            let order: MonomialOrder = $order;
            let system = $system;
            let options = recommended();
            let trace = match trace_batches(&system, order, &options) {
                Ok((_, _, trace)) => trace,
                Err(_) => {
                    println!("{:<12} {:<8} did not finish", $name, order.name());
                    break 'arm;
                }
            };

            // The column vector each batch hands the sort: `preprocessed.monomials` drained in
            // hash-set order, exactly as `MacaulayMatrix::build_measured` collects it. Snapshotted
            // outside every arm, so both arms sort the same input in the same input order.
            let inputs: Vec<Vec<Monomial<_>>> = trace
                .batches()
                .iter()
                .map(|batch| {
                    let preprocessed = symbolic_preprocessing(&batch.basis, &batch.pairs);
                    preprocessed.monomials.iter().copied().collect()
                })
                .collect();
            let columns: usize = inputs.iter().map(|v| v.len()).sum();

            let mut floor = [Duration::MAX; 2];
            let mut reference: Option<Vec<Vec<Monomial<_>>>> = None;
            for repetition in 0..REPETITIONS {
                let mut elapsed = [Duration::ZERO; 2];
                for slot in 0..2 {
                    let which = (slot + repetition) % 2;
                    let mut sorted: Vec<Vec<Monomial<_>>> = Vec::with_capacity(inputs.len());
                    for input in &inputs {
                        let mut scratch = input.clone();
                        let started = Instant::now();
                        if which == 0 {
                            scratch.sort_by(|a, b| order.cmp(b, a));
                        } else {
                            scratch.sort_unstable_by(|a, b| order.cmp(b, a));
                        }
                        elapsed[which] += started.elapsed();
                        sorted.push(black_box(scratch));
                    }
                    // Both arms must produce the same column order, or the unstable sort is not
                    // sound here and no timing figure matters.
                    match &reference {
                        None => reference = Some(sorted),
                        Some(expected) => assert_eq!(
                            expected, &sorted,
                            "the two sorts disagree on the column order"
                        ),
                    }
                }
                for which in 0..2 {
                    floor[which] = floor[which].min(elapsed[which]);
                }
            }

            println!(
                "{:<12} {:<8} {:>7} {:>9} {:>11.3} {:>9.3} {:>8.2}x",
                $name,
                order.name(),
                inputs.len(),
                columns,
                millis(floor[0]),
                millis(floor[1]),
                millis(floor[0]) / millis(floor[1])
            );
        }};
    }

    {
        arm!("cyclic-5", MonomialOrder::Lexicographic, cyclic::<5, F>());
        arm!("katsura-5", MonomialOrder::Lexicographic, katsura::<5, F>());
        arm!("katsura-6", MonomialOrder::Lexicographic, katsura::<6, F>());
        arm!(
            "katsura-6",
            MonomialOrder::GradedReverseLexicographic,
            katsura::<6, F>()
        );
        arm!(
            "katsura-7",
            MonomialOrder::GradedLexicographic,
            katsura::<7, F>()
        );
    }
}
