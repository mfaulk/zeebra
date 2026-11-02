//! Prints Buchberger's algorithmic counters for the standard benchmark systems.
//!
//! Wall-clock time says that a change helped; these counters say why. Pair counts and elimination
//! rates attribute a speedup to the selection strategy or to a criterion rather than to faster
//! arithmetic, which matters when deciding what to work on next.
//!
//! `cargo run --release --example grobner_statistics`

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        buchberger_with_statistics, Statistics,
    },
    MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

const ORDERS: [(&str, MonomialOrder); 3] = [
    ("lex", MonomialOrder::Lexicographic),
    ("grlex", MonomialOrder::GradedLexicographic),
    ("grevlex", MonomialOrder::GradedReverseLexicographic),
];

fn report<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
    for (order_name, order) in ORDERS {
        let (basis, s) = buchberger_with_statistics(system, order);
        let Statistics {
            pairs_considered,
            pairs_eliminated_by_product_criterion: eliminated,
            pairs_reduced,
            zero_reductions,
            elements_added,
            max_pair_degree,
            max_terms,
        } = s;
        // Share of pairs skipped without any reduction, the payoff of the product criterion.
        let share = if pairs_considered == 0 {
            0.0
        } else {
            100.0 * eliminated as f64 / pairs_considered as f64
        };
        println!(
            "{:<12} {:<8} {:>7} {:>7} {:>6.1}% {:>7} {:>7} {:>7} {:>6} {:>7} {:>6}",
            name,
            order_name,
            pairs_considered,
            eliminated,
            share,
            pairs_reduced,
            zero_reductions,
            elements_added,
            basis.len(),
            max_terms,
            max_pair_degree,
        );
    }
}

fn main() {
    println!(
        "{:<12} {:<8} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>6} {:>7} {:>6}",
        "system",
        "order",
        "pairs",
        "elim",
        "elim%",
        "reduced",
        "zero",
        "added",
        "basis",
        "terms",
        "deg"
    );
    report("cyclic-3", &cyclic::<3, F>());
    report("cyclic-4", &cyclic::<4, F>());
    report("katsura-3", &katsura::<3, F>());
    report("katsura-4", &katsura::<4, F>());
    report("katsura-5", &katsura::<5, F>());
}
