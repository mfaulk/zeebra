//! Where an F4 computation's time goes, per stage, for a named configuration.
//!
//! `examples/f4_statistics.rs` reports what the algorithm *did* — matrices, rows, fill-in. This
//! reports what it *cost*, broken down by stage, which is the measurement an optimization has to
//! move. The two are complementary: a change that halves the row count and does not shorten the
//! computation is visible here and not there.
//!
//! The stage columns come from `F4Options::measure_stages`, which reads a clock four times per
//! batch, plus once for the final interreduction. `other` is the total less every stage: pair
//! selection and basis bookkeeping. A large `other` means the breakdown is looking in the wrong
//! place.
//!
//! ```text
//! cargo run --release --example f4_profile                 # the baseline, every system
//! cargo run --release --example f4_profile -- baseline     # the same, named
//! cargo run --release --example f4_profile -- list         # the configurations available
//! ```
//!
//! Each configuration is one row of the milestone's ablation table. They are named here rather
//! than assembled at each call site so that every workstream reports the same thing.

use std::time::Duration;

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

const ALL: [(&str, MonomialOrder); 3] = [
    ("lex", MonomialOrder::Lexicographic),
    ("grlex", MonomialOrder::GradedLexicographic),
    ("grevlex", MonomialOrder::GradedReverseLexicographic),
];

const GRADED: [(&str, MonomialOrder); 2] = [
    ("grlex", MonomialOrder::GradedLexicographic),
    ("grevlex", MonomialOrder::GradedReverseLexicographic),
];

/// The configurations of the ablation study, by name.
///
/// Every one starts from `F4Options::baseline()` and turns on exactly what its name says, so the
/// difference between two rows of the table is the difference between two configurations and
/// nothing else. `measure_stages` is on throughout, including in the baseline, so the overhead of
/// measuring is common to every row.
fn configuration(name: &str) -> Option<F4Options> {
    let base = F4Options {
        measure_stages: true,
        ..F4Options::baseline()
    };
    let options = match name {
        "baseline" => base,
        // A only: structured elimination.
        "a" => F4Options {
            reduction: ReductionStrategy::Structured,
            ..base
        },
        // B only: preprocessing. Two sub-configurations, because the reducer cache has to be
        // measured before it is used, and `count` is how that is done.
        "b" => F4Options {
            reducer_selection: ReducerSelection::LargestLeadingMonomial,
            reducer_cache: CacheMode::Count,
            ..base
        },
        "b-count" => F4Options {
            reducer_cache: CacheMode::Count,
            ..base
        },
        // C only: pair criteria.
        "c" => F4Options {
            criteria: PairCriteria::ALL,
            ..base
        },
        // D only: the linear-algebra backend.
        "d" => F4Options {
            elimination: Backend::Adaptive,
            ..base
        },
        "d-dense" => F4Options {
            elimination: Backend::Dense,
            ..base
        },
        "ab" => F4Options {
            reduction: ReductionStrategy::Structured,
            reducer_selection: ReducerSelection::LargestLeadingMonomial,
            reducer_cache: CacheMode::Count,
            ..base
        },
        "ad" => F4Options {
            reduction: ReductionStrategy::Structured,
            elimination: Backend::Adaptive,
            ..base
        },
        // What the milestone recommends. M16-B's merged contribution is a cheaper monomial hash,
        // which is unconditional and so already in every configuration including `baseline`; its
        // two *optional* strategies were measured and rejected, which is why they are not here.
        "recommended" | "acd" => F4Options {
            reduction: ReductionStrategy::Structured,
            criteria: PairCriteria::ALL,
            elimination: Backend::Adaptive,
            ..base
        },
        // Everything, including what measurement rejected, for the ablation's sake.
        "abcd" => F4Options {
            reduction: ReductionStrategy::Structured,
            reducer_selection: ReducerSelection::LargestLeadingMonomial,
            reducer_cache: CacheMode::Count,
            criteria: PairCriteria::ALL,
            elimination: Backend::Adaptive,
            ..base
        },
        _ => return None,
    };
    Some(options)
}

const CONFIGURATIONS: [&str; 12] = [
    "baseline",
    "a",
    "b",
    "b-count",
    "c",
    "d",
    "d-dense",
    "ab",
    "ad",
    "acd",
    "recommended",
    "abcd",
];

/// A deterministic random system: N quadratics in N variables. Same construction as the benchmark.
fn random_system<const N: usize>(seed: u64) -> Vec<MultivariatePolynomial<N, F>> {
    use rand::{prelude::StdRng, Rng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(seed);
    (0..N)
        .map(|_| {
            let terms: Vec<(zeebra::Monomial<N>, F)> = (0..2 * N)
                .map(|_| {
                    let mut exponents = [0u32; N];
                    exponents[rng.gen_range(0..N)] += 1;
                    if rng.gen_bool(0.5) {
                        exponents[rng.gen_range(0..N)] += 1;
                    }
                    (zeebra::Monomial::new(&exponents), F::random(&mut rng))
                })
                .collect();
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

fn planted_point<const N: usize>(seed: u64) -> Vec<F> {
    use rand::{prelude::StdRng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(seed);
    (0..N).map(|_| F::random(&mut rng)).collect()
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e3
}

fn header() {
    println!(
        "{:<12} {:<8} {:>9} {:>8} {:>8} {:>9} {:>7} {:>8} {:>8} {:>7} {:>7} {:>6}",
        "system",
        "order",
        "total/ms",
        "symb/ms",
        "cons/ms",
        "elim/ms",
        "ext/ms",
        "inter/ms",
        "other/ms",
        "batches",
        "pairs",
        "basis"
    );
}

fn row<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    orders: &[(&str, MonomialOrder)],
    options: &F4Options,
) {
    for &(order_name, order) in orders {
        let (basis, s): (Vec<_>, F4Statistics) = match f4_with_options(system, order, options) {
            Ok(result) => result,
            Err(error) => {
                println!("{:<12} {:<8} {}", name, order_name, error);
                continue;
            }
        };

        let stages = s.stages;
        let other = s.total.saturating_sub(stages.sum());
        println!(
            "{:<12} {:<8} {:>9.2} {:>8.2} {:>8.2} {:>9.2} {:>7.2} {:>8.2} {:>8.2} {:>7} {:>7} {:>6}",
            name,
            order_name,
            millis(s.total),
            millis(stages.symbolic),
            millis(stages.construction),
            millis(stages.elimination),
            millis(stages.extraction),
            millis(stages.interreduction),
            millis(other),
            s.batches,
            s.pairs_reduced,
            basis.len()
        );
    }
}

/// The counters an optimization is judged on, beside the stage times.
fn diagnostics<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    orders: &[(&str, MonomialOrder)],
    options: &F4Options,
) {
    for &(order_name, order) in orders {
        let Ok((_, s)) = f4_with_options(system, order, options) else {
            continue;
        };
        println!(
            "{:<12} {:<8} {:>8} {:>8} {:>8} {:>9.1} {:>8} {:>9.3} {:>8} {:>8} {:>8.2}",
            name,
            order_name,
            s.reducer_rows,
            s.reducer_rows_reused,
            s.divisor_queries,
            s.divisor_scan_steps_per_query(),
            s.criteria.total(),
            s.criteria.chain as f64 / s.pairs_considered.max(1) as f64,
            s.structured_batches,
            s.free_pivots,
            s.stage_coverage()
        );
    }
}

/// Every system of the comparison corpus, under the configuration given.
///
/// A system is labelled by its variable count, which is the convention the preceding milestone's
/// tables use: "katsura-5" is `katsura::<5, F>()`, five variables.
fn each_system(options: &F4Options, stage_times: bool) {
    macro_rules! go {
        ($n:literal, $label:expr, $system:expr, $orders:expr) => {{
            let system: Vec<MultivariatePolynomial<$n, F>> = $system;
            if stage_times {
                row::<$n>($label, &system, $orders, options);
            } else {
                diagnostics::<$n>($label, &system, $orders, options);
            }
        }};
    }

    go!(4, "cyclic-4", cyclic::<4, F>(), &ALL);
    go!(5, "cyclic-5", cyclic::<5, F>(), &ALL);
    go!(4, "katsura-4", katsura::<4, F>(), &ALL);
    go!(5, "katsura-5", katsura::<5, F>(), &ALL);
    go!(6, "katsura-6", katsura::<6, F>(), &ALL);
    go!(7, "katsura-7", katsura::<7, F>(), &GRADED);
    go!(4, "random-4", random_system::<4>(5), &ALL);
    go!(
        6,
        "planted-6",
        planted::<6, F>(&planted_point::<6>(9)),
        &ALL
    );
}

fn main() {
    let argument = std::env::args().nth(1).unwrap_or_else(|| "baseline".into());

    if argument == "list" {
        println!("configurations: {}", CONFIGURATIONS.join(", "));
        return;
    }

    let Some(options) = configuration(&argument) else {
        eprintln!(
            "unknown configuration {:?}; one of {}",
            argument,
            CONFIGURATIONS.join(", ")
        );
        std::process::exit(2);
    };

    println!("configuration: {}", argument);
    println!();
    println!(
        "Stage times. `inter` is the final interreduction, which happens once rather than per"
    );
    println!("batch. `other` is the total less every stage: pair selection and basis bookkeeping.");
    println!();
    header();
    each_system(&options, true);

    println!();
    println!(
        "Diagnostics. `reused` is reducer multiples that had been built before, which is zero"
    );
    println!(
        "unless the reducer cache is counting or storing. `scan/q` is basis elements examined"
    );
    println!("per divisor lookup: the basis size for a linear scan, one for a perfect index.");
    println!("`cov` is the share of the total the four stages account for.");
    println!();
    println!(
        "{:<12} {:<8} {:>8} {:>8} {:>8} {:>9} {:>8} {:>9} {:>8} {:>8} {:>8}",
        "system",
        "order",
        "reducers",
        "reused",
        "div/q",
        "scan/q",
        "elim'd",
        "chain%",
        "struct",
        "free_piv",
        "cov"
    );
    each_system(&options, false);
}
