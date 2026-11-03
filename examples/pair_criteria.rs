//! What the pair-elimination criteria discard, and what that saves, in both engines.
//!
//! The criteria are judged on deterministic counters rather than on wall clock: a criterion earns
//! its complexity by preventing matrices from being built, and `batches`, `pairs_reduced` and
//! `max_matrix_rows` say whether it did. Wall clock is reported alongside but is the weaker
//! evidence, since several agents may be building on this machine at once.
//!
//! ```text
//! cargo run --release --example pair_criteria          # F4, every configuration
//! cargo run --release --example pair_criteria -- f4
//! cargo run --release --example pair_criteria -- buchberger
//! ```
//!
//! Columns. `considered` is pairs selected; `reduced` is pairs that reached a matrix (F4) or an
//! S-polynomial (Buchberger); `prod`, `chain` and `gm` are the pairs each criterion discarded.
//! Gebauer–Möller's are never selected, so they are not in `considered`.

use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        buchberger_with_criteria, f4_with_options, F4Options, PairCriteria,
    },
    MonomialOrder, MultivariatePolynomial,
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

/// The configurations compared, each named by the criteria it turns on.
const CONFIGURATIONS: [(&str, PairCriteria); 5] = [
    (
        "none",
        PairCriteria {
            product: false,
            chain: false,
            gebauer_moller: false,
        },
    ),
    ("product", PairCriteria::PRODUCT_ONLY),
    (
        "chain",
        PairCriteria {
            product: true,
            chain: true,
            gebauer_moller: false,
        },
    ),
    (
        "gebauer-moller",
        PairCriteria {
            product: true,
            chain: false,
            gebauer_moller: true,
        },
    ),
    ("all", PairCriteria::ALL),
];

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e3
}

fn f4_row<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    orders: &[(&str, MonomialOrder)],
) {
    for &(order_name, order) in orders {
        for (configuration, criteria) in CONFIGURATIONS {
            let options = F4Options {
                criteria,
                ..F4Options::baseline()
            };
            let start = Instant::now();
            let Ok((basis, s)) = f4_with_options(system, order, &options) else {
                println!(
                    "{:<11} {:<8} {:<15} limits exceeded",
                    name, order_name, configuration
                );
                continue;
            };
            println!(
                "{:<11} {:<8} {:<15} {:>8} {:>10} {:>8} {:>7} {:>7} {:>7} {:>9} {:>9.2} {:>6}",
                name,
                order_name,
                configuration,
                s.batches,
                s.pairs_considered,
                s.pairs_reduced,
                s.criteria.product,
                s.criteria.chain,
                s.criteria.gebauer_moller,
                s.max_matrix_rows,
                millis(start.elapsed()),
                basis.len()
            );
        }
    }
}

fn buchberger_row<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    orders: &[(&str, MonomialOrder)],
) {
    for &(order_name, order) in orders {
        for (configuration, criteria) in CONFIGURATIONS {
            let start = Instant::now();
            let (basis, s) = buchberger_with_criteria(system, order, &criteria);
            println!(
                "{:<11} {:<8} {:<15} {:>10} {:>8} {:>8} {:>7} {:>7} {:>7} {:>9.2} {:>6}",
                name,
                order_name,
                configuration,
                s.pairs_considered,
                s.pairs_reduced,
                s.zero_reductions,
                s.criteria.product,
                s.criteria.chain,
                s.criteria.gebauer_moller,
                millis(start.elapsed()),
                basis.len()
            );
        }
    }
}

fn main() {
    let engine = std::env::args().nth(1).unwrap_or_else(|| "f4".into());

    match engine.as_str() {
        "f4" => {
            println!(
                "{:<11} {:<8} {:<15} {:>8} {:>10} {:>8} {:>7} {:>7} {:>7} {:>9} {:>9} {:>6}",
                "system",
                "order",
                "criteria",
                "batches",
                "considered",
                "reduced",
                "prod",
                "chain",
                "gm",
                "max_rows",
                "ms",
                "basis"
            );
            f4_row("cyclic-4", &cyclic::<4, F>(), &ALL);
            f4_row("cyclic-5", &cyclic::<5, F>(), &ALL);
            f4_row("katsura-4", &katsura::<4, F>(), &ALL);
            f4_row("katsura-5", &katsura::<5, F>(), &ALL);
            f4_row("katsura-6", &katsura::<6, F>(), &ALL);
            f4_row("katsura-7", &katsura::<7, F>(), &GRADED);
        }
        "buchberger" => {
            println!(
                "{:<11} {:<8} {:<15} {:>10} {:>8} {:>8} {:>7} {:>7} {:>7} {:>9} {:>6}",
                "system",
                "order",
                "criteria",
                "considered",
                "reduced",
                "zero",
                "prod",
                "chain",
                "gm",
                "ms",
                "basis"
            );
            buchberger_row("cyclic-4", &cyclic::<4, F>(), &ALL);
            buchberger_row("katsura-4", &katsura::<4, F>(), &ALL);
            buchberger_row("katsura-5", &katsura::<5, F>(), &ALL);
            buchberger_row("cyclic-5", &cyclic::<5, F>(), &GRADED);
            buchberger_row("katsura-6", &katsura::<6, F>(), &GRADED);
        }
        other => {
            eprintln!("unknown engine {:?}; one of f4, buchberger", other);
            std::process::exit(2);
        }
    }
}
