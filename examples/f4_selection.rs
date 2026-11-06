//! What reducer selection and the reducer cache do to the whole computation.
//!
//! `examples/f4_profile.rs` reports one configuration at a time, and its `b` row turns on reducer
//! selection and the cache together. This separates them, on the counters the two hypotheses are
//! stated in: the closure size (`reducers`), the matrix shape, the peak live entries, the row
//! operations elimination performed, the share of reducer multiples that had been built before,
//! and the stage times.
//!
//! The selection hypothesis is that the smaller multiplier gives a smaller closure and therefore a
//! smaller matrix; elimination and the total are next to it because a smaller matrix is only worth
//! having if the computation gets shorter. The cache hypothesis is that the same multiple recurs
//! often enough across batches to be worth remembering; `reuse` is that rate and `symb/ms` is what
//! acting on it costs.
//!
//! `fewest-terms` and its control `most-terms` test a second, orthogonal hypothesis: the reducer
//! chosen *is* the row added, so the sparsest divisor is the sparsest row. Every row of every table
//! returns the identical reduced Gröbner basis, which is asserted here and not reported.
//!
//! ```text
//! cargo run --release --example f4_selection
//! ```

use std::time::Duration;

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4_with_options, CacheMode, F4Options, F4Statistics, ReducerSelection,
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
        "{:<12} {:<8} {:<14} {:>9} {:>7} {:>7} {:>10} {:>11} {:>8} {:>8} {:>9} {:>7} {:>6}",
        "system",
        "order",
        "configuration",
        "reducers",
        "rows",
        "cols",
        "peak nz",
        "row ops",
        "symb/ms",
        "elim/ms",
        "total/ms",
        "scan/q",
        "reuse"
    );
}

/// The configurations compared: every policy with the cache off, and the baseline with it on.
///
/// Derived from [`ReducerSelection::ALL`], so a policy added to the enum is measured here without
/// this program being edited — which is what that constant is for.
fn configurations() -> Vec<(String, ReducerSelection, CacheMode)> {
    let mut rows: Vec<(String, ReducerSelection, CacheMode)> = ReducerSelection::ALL
        .iter()
        .map(|&selection| (selection.name().to_string(), selection, CacheMode::Off))
        .collect();
    rows.push((
        "first+count".to_string(),
        ReducerSelection::FirstApplicable,
        CacheMode::Count,
    ));
    rows
}

fn row<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    orders: &[(&str, MonomialOrder)],
) {
    for &(order_name, order) in orders {
        // The basis the first configuration returned, which every later one must match. A
        // selection policy decides which divisor reduces a monomial and nothing else, so a
        // reduced Gröbner basis — unique for an ideal and an order — cannot move; a row that
        // differed would be a defect, and reporting it in a column rather than failing would bury
        // it.
        let mut reference: Option<Vec<MultivariatePolynomial<N, F>>> = None;
        for (label, selection, cache) in configurations() {
            let options = F4Options {
                reducer_selection: selection,
                reducer_cache: cache,
                measure_stages: true,
                ..F4Options::baseline()
            };
            let (basis, s): (Vec<_>, F4Statistics) = match f4_with_options(system, order, &options)
            {
                Ok(result) => result,
                Err(error) => {
                    println!("{:<12} {:<8} {:<14} {}", name, order_name, label, error);
                    continue;
                }
            };
            match &reference {
                Some(reference) => assert_eq!(
                    &basis, reference,
                    "{} {} {}: a reducer policy changed the reduced Gröbner basis",
                    name, order_name, label
                ),
                None => reference = Some(basis),
            }
            println!(
                "{:<12} {:<8} {:<14} {:>9} {:>7} {:>7} {:>10} {:>11} {:>8.2} {:>8.2} {:>9.2} {:>7.1} {:>6.2}",
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
                s.divisor_scan_steps_per_query(),
                s.reducer_reuse_fraction()
            );
        }
    }
}

fn main() {
    println!("Reducer selection and the reducer cache, separately, on the counters the two");
    println!("hypotheses are stated in. `reducers` is the closure size; `rows`/`cols` the largest");
    println!("matrix; `scan/q` basis elements examined per divisor lookup; `reuse` the share of");
    println!("reducer multiples that had been needed in an earlier batch.");
    println!();
    header();
    row("cyclic-4", &cyclic::<4, F>(), &ALL);
    row("cyclic-5", &cyclic::<5, F>(), &ALL);
    row("katsura-4", &katsura::<4, F>(), &ALL);
    row("katsura-5", &katsura::<5, F>(), &ALL);
    row("katsura-6", &katsura::<6, F>(), &ALL);
    row("katsura-7", &katsura::<7, F>(), &GRADED);
}
