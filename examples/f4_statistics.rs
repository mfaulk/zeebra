//! Prints F4's matrix and elimination counters beside Buchberger's, for the benchmark systems.
//!
//! Wall-clock time says which engine was faster; these counters say what it did differently. The
//! pair of columns to read together is Buchberger's `bb:red` against F4's `batches`: both engines
//! cover the same critical pairs, and the ratio is how many reductions F4 folded into each matrix.
//! `bb:0` against `empty` is the same comparison for the work that produced nothing.
//!
//! Where Buchberger cannot finish in reasonable time its columns are blank rather than omitted —
//! katsura-6 under lex is the case F4 makes newly tractable, and it is worth seeing as a gap.
//!
//! `cargo run --release --example f4_statistics`

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        buchberger_with_statistics, f4_with_options, F4Options,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

const LEX: (&str, MonomialOrder) = ("lex", MonomialOrder::Lexicographic);
const GRADED: [(&str, MonomialOrder); 2] = [
    ("grlex", MonomialOrder::GradedLexicographic),
    ("grevlex", MonomialOrder::GradedReverseLexicographic),
];
const ALL: [(&str, MonomialOrder); 3] = [
    LEX,
    ("grlex", MonomialOrder::GradedLexicographic),
    ("grevlex", MonomialOrder::GradedReverseLexicographic),
];

/// Report F4's counters for one system, optionally beside Buchberger's.
///
/// `compare` is false where Buchberger is impractically slow. It is not a licence to skip the
/// agreement check anywhere it can be made: where both run, the two bases must be equal.
fn report<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    orders: &[(&str, MonomialOrder)],
    compare: bool,
) {
    for &(order_name, order) in orders {
        let (basis, s) = match f4_with_options(system, order, &F4Options::default()) {
            Ok(result) => result,
            Err(error) => {
                println!("{:<12} {:<8} {}", name, order_name, error);
                continue;
            }
        };

        let (reduced, zero) = if compare {
            let (classical_basis, classical) = buchberger_with_statistics(system, order);
            assert_eq!(
                basis, classical_basis,
                "{} under {}: the two engines disagree",
                name, order_name
            );
            (
                classical.pairs_reduced.to_string(),
                classical.zero_reductions.to_string(),
            )
        } else {
            ("-".to_string(), "-".to_string())
        };

        // Share of matrix rows that were reducer multiples rather than halves of a critical pair:
        // the cost of making the reduction possible at all.
        let scaffolding = 100.0 * s.reducer_row_fraction();
        // How much denser elimination made the worst matrix: peak against as built.
        let fill_in = s.worst_fill_in();

        println!(
            "{:<12} {:<8} {:>7} {:>7} {:>7} {:>6} {:>6} {:>6}x{:<6} {:>6.1}% {:>8} {:>6.2} {:>6}",
            name,
            order_name,
            reduced,
            s.batches,
            s.max_pairs_per_batch,
            zero,
            s.empty_batches,
            s.max_matrix_rows,
            s.max_matrix_columns,
            scaffolding,
            s.max_live_nonzeros,
            fill_in,
            basis.len(),
        );
    }
}

fn main() {
    println!(
        "{:<12} {:<8} {:>7} {:>7} {:>7} {:>6} {:>6} {:>13} {:>7} {:>8} {:>6} {:>6}",
        "system",
        "order",
        "bb:red",
        "batches",
        "max/bat",
        "bb:0",
        "empty",
        "max matrix",
        "scaffld",
        "peak nz",
        "fill",
        "basis"
    );

    report("cyclic-3", &cyclic::<3, F>(), &ALL, true);
    report("cyclic-4", &cyclic::<4, F>(), &ALL, true);
    report("cyclic-5", &cyclic::<5, F>(), &ALL, true);
    report("katsura-3", &katsura::<3, F>(), &ALL, true);
    report("katsura-4", &katsura::<4, F>(), &ALL, true);
    report("katsura-5", &katsura::<5, F>(), &ALL, true);
    // katsura-6 under lex, and all of katsura-7, are beyond Buchberger here.
    report("katsura-6", &katsura::<6, F>(), &GRADED, true);
    report("katsura-6", &katsura::<6, F>(), &[LEX], false);
    report("katsura-7", &katsura::<7, F>(), &GRADED, false);

    let point: Vec<F> = [3u64, 5, 7, 11, 13, 17]
        .iter()
        .map(|v| F::new(*v))
        .collect();
    report("planted-6", &planted::<6, F>(&point), &ALL, true);

    println!();
    println!("bb:red  critical pairs Buchberger reduced one at a time; - where it is too slow");
    println!("batches matrices F4 built to cover the same pairs");
    println!("bb:0    of those reductions, how many produced zero");
    println!("empty   of those matrices, how many produced no new basis element");
    println!("scaffld share of matrix rows added by symbolic preprocessing to enable reduction");
    println!("fill    peak live nonzeros over that same matrix's nonzeros as built");
}
