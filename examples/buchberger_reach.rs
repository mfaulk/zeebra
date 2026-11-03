//! Does classical Buchberger reach the instances it could not, now that it has the criteria?
//!
//! The preceding milestone reported katsura-6 under lex as out of Buchberger's reach: it exhausted
//! a thirty-minute budget. That was with Buchberger's first criterion alone. The chain criterion
//! and Gebauer–Möller are shared machinery, so the honest question for the M16 comparison is
//! whether the classical engine now finishes those instances at all — a `—` in a results table
//! should mean "does not finish", not "was not tried".
//!
//! One instance per invocation, so an external timeout can bound it. Nothing inside a single
//! `buchberger_with_criteria` call can be interrupted, which is exactly why this is a separate
//! binary rather than a row in `examples/f4_milestone.rs`:
//!
//! ```text
//! timeout 900 cargo run --release --example buchberger_reach -- katsura-6 lex all
//! ```
//!
//! Exits 0 having printed the time, or is killed by the timeout, which is the answer.

use std::time::Instant;

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::katsura, buchberger_with_criteria, f4_with_options, F4Options,
        PairCriteria,
    },
    MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

fn run<const N: usize>(
    label: &str,
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    criteria: &PairCriteria,
) {
    // F4 first, so the run also establishes that the two engines agree on this instance — the
    // whole point of reaching it with the classical engine is to have an oracle here.
    let (expected, _) =
        f4_with_options(system, order, &F4Options::recommended()).expect("within limits");

    let at = Instant::now();
    let (basis, statistics) = buchberger_with_criteria(system, order, criteria);
    let elapsed = at.elapsed();

    assert_eq!(
        basis,
        expected,
        "{} / {}: the engines disagree",
        label,
        order.name()
    );
    println!(
        "{} / {} / {:?}: buchberger finished in {:.2} s — {} pairs considered, {} reduced, \
         {} zero reductions, {} eliminated, basis {}",
        label,
        order.name(),
        criteria,
        elapsed.as_secs_f64(),
        statistics.pairs_considered,
        statistics.pairs_reduced,
        statistics.zero_reductions,
        statistics.criteria.total(),
        basis.len()
    );
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [system, order_name, criteria_name] = args.as_slice() else {
        eprintln!(
            "usage: buchberger_reach <katsura-6|katsura-7> <lex|grlex|grevlex> <product|all>"
        );
        std::process::exit(2);
    };

    let order = match order_name.as_str() {
        "lex" => MonomialOrder::Lexicographic,
        "grlex" => MonomialOrder::GradedLexicographic,
        "grevlex" => MonomialOrder::GradedReverseLexicographic,
        other => {
            eprintln!("unknown order {}", other);
            std::process::exit(2);
        }
    };
    let criteria = match criteria_name.as_str() {
        "product" => PairCriteria::PRODUCT_ONLY,
        "all" => PairCriteria::ALL,
        other => {
            eprintln!("unknown criteria {}", other);
            std::process::exit(2);
        }
    };

    match system.as_str() {
        "katsura-6" => run::<6>("katsura-6", &katsura::<6, F>(), order, &criteria),
        "katsura-7" => run::<7>("katsura-7", &katsura::<7, F>(), order, &criteria),
        other => {
            eprintln!("unknown system {}", other);
            std::process::exit(2);
        }
    }
}
