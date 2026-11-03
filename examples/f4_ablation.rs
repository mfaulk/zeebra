//! The M16 ablation study: every configuration, every system, one table.
//!
//! Independent wins do not compose into a combined win, and three of M16's interactions were
//! predicted in advance to be adverse: stronger pair criteria eliminate matrices that structured
//! elimination would otherwise have optimized, a different reducer choice changes matrix density
//! and so moves the sparse/dense crossover, and a smaller reducer block changes the shape
//! structured elimination depends on. This is what measures them.
//!
//! One thing cannot be ablated, and saying so is part of the result: **M16-B's merged contribution
//! is not option-gated.** What B shipped is a cheaper monomial hash inside symbolic preprocessing;
//! it is unconditional and therefore present in every row below, baseline included. B's two
//! *optional* strategies — `LargestLeadingMonomial` and `CacheMode::Store` — were both measured
//! and rejected, and appear here only as the `b-rejected` row, which exists to show the rejection
//! rather than to be chosen.
//!
//! ```text
//! cargo run --release --example f4_ablation            # every configuration
//! cargo run --release --example f4_ablation -- fast    # skip the instances over a second
//! cargo run --release --example f4_ablation -- list
//! ```
//!
//! Every configuration runs on the identical system under the identical order at the identical
//! limits, and the basis is asserted equal to the baseline's on every row — a configuration that
//! changes the answer is a defect, not a trade-off.

use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        f4_with_options, CacheMode, F4Options, F4Statistics, PairCriteria, ReducerSelection,
        ReductionStrategy,
    },
    linalg::Backend,
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

/// A configuration of the ablation, and what it turns on relative to the baseline.
struct Configuration {
    name: &'static str,
    purpose: &'static str,
    options: fn(F4Options) -> F4Options,
}

const CONFIGURATIONS: &[Configuration] = &[
    Configuration {
        name: "baseline",
        purpose: "reference (M16-B's hashing is unconditional and is already in here)",
        options: |base| base,
    },
    Configuration {
        name: "A",
        purpose: "structured elimination",
        options: |base| F4Options {
            reduction: ReductionStrategy::Structured,
            ..base
        },
    },
    Configuration {
        name: "b-rejected",
        purpose: "M16-B's rejected options, kept to show the rejection",
        options: |base| F4Options {
            reducer_selection: ReducerSelection::LargestLeadingMonomial,
            reducer_cache: CacheMode::Store,
            ..base
        },
    },
    Configuration {
        name: "C",
        purpose: "chain criterion and Gebauer-Moller",
        options: |base| F4Options {
            criteria: PairCriteria::ALL,
            ..base
        },
    },
    Configuration {
        name: "D",
        purpose: "dense accumulator",
        options: |base| F4Options {
            elimination: Backend::Adaptive,
            ..base
        },
    },
    Configuration {
        name: "d-dense",
        purpose: "fully dense rows, the control D is compared against",
        options: |base| F4Options {
            elimination: Backend::Dense,
            ..base
        },
    },
    Configuration {
        name: "A+b-rej",
        purpose: "does a different reducer choice help structured elimination?",
        options: |base| F4Options {
            reduction: ReductionStrategy::Structured,
            reducer_selection: ReducerSelection::LargestLeadingMonomial,
            reducer_cache: CacheMode::Store,
            ..base
        },
    },
    Configuration {
        name: "A+C",
        purpose: "do the criteria remove the matrices A optimizes?",
        options: |base| F4Options {
            reduction: ReductionStrategy::Structured,
            criteria: PairCriteria::ALL,
            ..base
        },
    },
    Configuration {
        name: "A+D",
        purpose: "does a sparser matrix leave the accumulator anything to win?",
        options: |base| F4Options {
            reduction: ReductionStrategy::Structured,
            elimination: Backend::Adaptive,
            ..base
        },
    },
    Configuration {
        name: "C+D",
        purpose: "fewer matrices against faster elimination",
        options: |base| F4Options {
            criteria: PairCriteria::ALL,
            elimination: Backend::Adaptive,
            ..base
        },
    },
    Configuration {
        name: "A+C+D",
        purpose: "the complete optimized engine",
        options: |base| F4Options {
            reduction: ReductionStrategy::Structured,
            criteria: PairCriteria::ALL,
            elimination: Backend::Adaptive,
            ..base
        },
    },
    Configuration {
        name: "A+b-rej+C+D",
        purpose: "everything, including what was rejected",
        options: |base| F4Options {
            reduction: ReductionStrategy::Structured,
            reducer_selection: ReducerSelection::LargestLeadingMonomial,
            reducer_cache: CacheMode::Store,
            criteria: PairCriteria::ALL,
            elimination: Backend::Adaptive,
            ..base
        },
    },
];

/// One measured run.
struct Measurement {
    statistics: F4Statistics,
    wall: Duration,
    basis: usize,
}

/// `rounds` runs, keeping the fastest: the minimum is the least noisy estimator under contention,
/// since interference can only ever make a run slower.
fn measure<const N: usize>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
    rounds: usize,
) -> Result<(Measurement, Vec<MultivariatePolynomial<N, F>>), String> {
    let mut best: Option<Measurement> = None;
    let mut basis = Vec::new();
    for _ in 0..rounds {
        let at = Instant::now();
        let (b, s) = f4_with_options(system, order, options).map_err(|e| e.to_string())?;
        let wall = at.elapsed();
        if best.as_ref().is_none_or(|m| wall < m.wall) {
            best = Some(Measurement {
                statistics: s,
                wall,
                basis: b.len(),
            });
        }
        basis = b;
    }
    Ok((best.expect("at least one round"), basis))
}

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

fn header() {
    println!(
        "{:<14} {:>9} {:>7} {:>8} {:>8} {:>8} {:>9} {:>7} {:>7} {:>10} {:>6}",
        "configuration",
        "total/ms",
        "speedup",
        "symb/ms",
        "elim/ms",
        "inter/ms",
        "pairs",
        "batches",
        "maxrows",
        "peak nz",
        "basis"
    );
}

fn run<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    rounds: usize,
) {
    println!("\n=== {} / {} ===", name, order.name());
    header();

    let base_options = F4Options {
        measure_stages: true,
        ..F4Options::baseline()
    };
    let mut reference: Option<(f64, Vec<MultivariatePolynomial<N, F>>)> = None;

    for configuration in CONFIGURATIONS {
        let options = (configuration.options)(base_options.clone());
        match measure(system, order, &options, rounds) {
            Ok((m, basis)) => {
                let total = millis(m.wall);
                let speedup = match &reference {
                    Some((base_total, base_basis)) => {
                        assert_eq!(
                            &basis,
                            base_basis,
                            "{} / {} / {}: the configuration changed the basis",
                            name,
                            order.name(),
                            configuration.name
                        );
                        base_total / total
                    }
                    None => {
                        reference = Some((total, basis));
                        1.0
                    }
                };
                let s = &m.statistics;
                println!(
                    "{:<14} {:>9.2} {:>6.2}x {:>8.2} {:>8.2} {:>8.2} {:>9} {:>7} {:>7} {:>10} {:>6}",
                    configuration.name,
                    total,
                    speedup,
                    millis(s.stages.symbolic),
                    millis(s.stages.elimination),
                    millis(s.stages.interreduction),
                    s.pairs_reduced,
                    s.batches,
                    s.max_matrix_rows,
                    s.max_live_nonzeros,
                    m.basis
                );
            }
            Err(error) => println!("{:<14} {}", configuration.name, error),
        }
    }
}

fn planted_point<const N: usize>(seed: u64) -> Vec<F> {
    use rand::{prelude::StdRng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(seed);
    (0..N).map(|_| F::random(&mut rng)).collect()
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

    println!("M16 ablation. Every configuration on the identical system, order, and limits, with");
    println!("the basis asserted equal to the baseline's. `speedup` is against the baseline row.");
    println!();
    println!(
        "M16-B's merged contribution — a cheaper monomial hash in symbolic preprocessing — is"
    );
    println!("unconditional, so it is present in every row including the baseline and cannot be");
    println!(
        "ablated. `b-rejected` holds B's two *optional* strategies, both of which measurement"
    );
    println!("rejected; it is here to show the rejection, not as a candidate.");
    println!();
    println!(
        "Each figure is the fastest of several runs: interference can only make a run slower,"
    );
    println!("so the minimum is the least noisy estimate of the cost.");

    use MonomialOrder::Lexicographic as LEX;
    use MonomialOrder::{GradedLexicographic as GRLEX, GradedReverseLexicographic as GREVLEX};

    run::<4>("cyclic-4", &cyclic::<4, F>(), LEX, 5);
    run::<5>("cyclic-5", &cyclic::<5, F>(), LEX, 3);
    run::<5>("cyclic-5", &cyclic::<5, F>(), GREVLEX, 3);
    run::<5>("katsura-5", &katsura::<5, F>(), LEX, 3);
    run::<5>("katsura-5", &katsura::<5, F>(), GREVLEX, 5);
    run::<6>("katsura-6", &katsura::<6, F>(), GRLEX, 3);
    run::<6>("katsura-6", &katsura::<6, F>(), GREVLEX, 3);
    let point = planted_point::<6>(9);
    run::<6>("planted-6", &planted::<6, F>(&point), LEX, 5);

    if !fast {
        // The three instances the preceding milestone could not pair against Buchberger at all.
        run::<6>("katsura-6", &katsura::<6, F>(), LEX, 2);
        run::<7>("katsura-7", &katsura::<7, F>(), GRLEX, 2);
        run::<7>("katsura-7", &katsura::<7, F>(), GREVLEX, 2);
    }
}
