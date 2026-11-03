//! What reducer selection and the divisor index do to the whole computation.
//!
//! `examples/f4_profile.rs` reports one configuration at a time. This reports the two
//! reducer-selection policies side by side on the counters the hypothesis is stated in: the
//! closure size (`reducers`), the matrix shape, the peak live entries, the row operations
//! elimination performed, and the stage times. The hypothesis is that the smaller multiplier gives
//! a smaller closure and therefore a smaller matrix; the point of putting elimination and the
//! total next to it is that a smaller matrix is only worth having if the computation gets shorter.
//!
//! ```text
//! cargo run --release --example f4_selection
//! ```

use std::time::Duration;

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4_with_options, F4Options, F4Statistics, ReducerSelection,
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

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e3
}

fn header() {
    println!(
        "{:<12} {:<8} {:<9} {:>9} {:>7} {:>7} {:>10} {:>11} {:>8} {:>8} {:>9} {:>7}",
        "system",
        "order",
        "selection",
        "reducers",
        "rows",
        "cols",
        "peak nz",
        "row ops",
        "symb/ms",
        "elim/ms",
        "total/ms",
        "scan/q"
    );
}

fn row<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    orders: &[(&str, MonomialOrder)],
) {
    for &(order_name, order) in orders {
        for (label, selection) in [
            ("first", ReducerSelection::FirstApplicable),
            ("largest", ReducerSelection::LargestLeadingMonomial),
        ] {
            let options = F4Options {
                reducer_selection: selection,
                measure_stages: true,
                ..F4Options::baseline()
            };
            let (_, s): (Vec<_>, F4Statistics) = match f4_with_options(system, order, &options) {
                Ok(result) => result,
                Err(error) => {
                    println!("{:<12} {:<8} {:<9} {}", name, order_name, label, error);
                    continue;
                }
            };
            println!(
                "{:<12} {:<8} {:<9} {:>9} {:>7} {:>7} {:>10} {:>11} {:>8.2} {:>8.2} {:>9.2} {:>7.1}",
                name,
                order_name,
                label,
                s.reducer_rows,
                s.max_matrix_rows,
                s.max_matrix_columns,
                s.max_live_nonzeros,
                s.row_operations,
                millis(s.stages.symbolic),
                millis(s.stages.elimination),
                millis(s.total),
                s.divisor_scan_steps_per_query()
            );
        }
    }
}

fn main() {
    println!("Reducer selection, both policies, on the counters the hypothesis is stated in.");
    println!("`reducers` is the closure size; `rows`/`cols` the largest matrix; `scan/q` basis");
    println!("elements examined per divisor lookup.");
    println!();
    header();
    row("cyclic-4", &cyclic::<4, F>(), &ALL);
    row("cyclic-5", &cyclic::<5, F>(), &ALL);
    row("katsura-4", &katsura::<4, F>(), &ALL);
    row("katsura-5", &katsura::<5, F>(), &ALL);
    row("katsura-6", &katsura::<6, F>(), &ALL);
    row("katsura-7", &katsura::<7, F>(), &GRADED);
}
