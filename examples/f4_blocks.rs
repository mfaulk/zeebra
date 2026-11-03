//! What the row arrangement of a Macaulay matrix costs, measured on the batches F4 really builds.
//!
//! Four arrangements of the same rows, replayed through the identical matrix per batch, so the
//! comparison is of eliminations and not of computations: a change of arrangement changes the
//! intermediate candidates, hence the pairs the next batch sees, hence everything downstream. That
//! is a real effect and `examples/f4_profile.rs` measures it; here it is held fixed.
//!
//! - `base` — rows as symbolic preprocessing produced them: pair halves first, then the reducer
//!   multiples in discovery order. One full echelon pass.
//! - `rf` — reducer multiples first, ascending by leading column. Still one full echelon pass, so
//!   this column isolates the *arrangement* from the elimination function.
//! - `blk` — the same arrangement, with the reducer block taken as a set of established pivots.
//! - `int` — as `blk`, with the reducer block interreduced against itself first.
//!
//! `ops` is row operations summed over every batch, `peak` the largest live nonzero count any one
//! batch reached, `fin` the entries left when elimination finished, summed, and `ms` the time the
//! eliminations took. `red%` is the share of rows that are reducer multiples, which bounds what
//! any of this can save.
//!
//! `lm` is whether the structured path produced the baseline's new leading monomials on every
//! batch, which it must. `poly` is whether the candidate polynomials coincided, which it need not:
//! a row echelon form depends on the row order, so a pivot row can differ in the pivot columns to
//! the right of its own without the span or the pivot set changing.
//!
//! ```text
//! cargo run --release --example f4_blocks
//! ```

use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        f4::{
            macaulay::MacaulayMatrix,
            reduce_batch,
            structured::{eliminate, reducer_rows, BlockPlan},
            symbolic::symbolic_preprocessing,
        },
        trace_batches, F4Options, ReductionStrategy,
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

const PLANS: [BlockPlan; 4] = [
    BlockPlan::Baseline,
    BlockPlan::ReducersFirstEchelon,
    BlockPlan::ReducersFirstBlock,
    BlockPlan::InterreducedBlock,
];

/// What one plan cost over a whole computation's worth of batches.
#[derive(Clone, Copy, Debug, Default)]
struct Totals {
    row_operations: usize,
    peak_nonzeros: usize,
    final_nonzeros: usize,
    rank: usize,
    elapsed: Duration,
}

/// One instance's numbers, kept so the two tables can be printed separately.
struct Report {
    system: String,
    order: String,
    batches: usize,
    reducer_share: f64,
    totals: [Totals; 4],
    leading_monomials_agree: bool,
    polynomials_agree: bool,
}

fn measure<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    orders: &[(&str, MonomialOrder)],
    into: &mut Vec<Report>,
) {
    let baseline = F4Options::baseline();
    let structured = F4Options {
        reduction: ReductionStrategy::Structured,
        ..F4Options::baseline()
    };

    for &(order_name, order) in orders {
        let Ok((_, _, trace)) = trace_batches(system, order, &baseline) else {
            eprintln!(
                "{} under {} did not finish within the budgets",
                name, order_name
            );
            continue;
        };

        let mut totals = [Totals::default(); 4];
        let mut rows = 0usize;
        let mut reducer_row_count = 0usize;
        let mut leading_monomials_agree = true;
        let mut polynomials_agree = true;

        for batch in trace.batches() {
            let preprocessed = symbolic_preprocessing(&batch.basis, &batch.pairs);
            let built = MacaulayMatrix::build(&batch.basis, &preprocessed, order);
            rows += built.num_rows();
            reducer_row_count += reducer_rows(&built);

            for (slot, plan) in PLANS.iter().enumerate() {
                let mut matrix = built.clone();
                let started = Instant::now();
                let outcome = eliminate(*plan, Backend::Sparse, &mut matrix, usize::MAX)
                    .expect("unbounded cannot fail");
                let elapsed = started.elapsed();
                let total = &mut totals[slot];
                total.elapsed += elapsed;
                total.row_operations += outcome.statistics.row_operations;
                total.peak_nonzeros = total.peak_nonzeros.max(outcome.statistics.peak_nonzeros);
                total.final_nonzeros += outcome.statistics.final_nonzeros;
                total.rank += outcome.statistics.rank;
            }

            let reference =
                reduce_batch(&batch.basis, &batch.pairs, order, &baseline).expect("within limits");
            let actual = reduce_batch(&batch.basis, &batch.pairs, order, &structured)
                .expect("within limits");
            let leads = |candidates: &[MultivariatePolynomial<N, F>]| -> Vec<_> {
                candidates
                    .iter()
                    .map(|p| p.leading_monomial(order))
                    .collect()
            };
            leading_monomials_agree &= leads(&actual.candidates) == leads(&reference.candidates);
            polynomials_agree &= actual.candidates == reference.candidates;
        }

        assert!(
            totals.iter().all(|total| total.rank == totals[0].rank),
            "{} under {}: the plans disagreed on rank",
            name,
            order_name
        );

        into.push(Report {
            system: name.to_string(),
            order: order_name.to_string(),
            batches: trace.len(),
            reducer_share: if rows == 0 {
                0.0
            } else {
                100.0 * reducer_row_count as f64 / rows as f64
            },
            totals,
            leading_monomials_agree,
            polynomials_agree,
        });
    }
}

fn ratio(value: usize, reference: usize) -> f64 {
    if reference == 0 {
        1.0
    } else {
        value as f64 / reference as f64
    }
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e3
}

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

fn main() {
    let mut reports: Vec<Report> = Vec::new();
    measure("cyclic-4", &cyclic::<4, F>(), &ALL, &mut reports);
    measure("cyclic-5", &cyclic::<5, F>(), &ALL, &mut reports);
    measure("katsura-4", &katsura::<4, F>(), &ALL, &mut reports);
    measure("katsura-5", &katsura::<5, F>(), &ALL, &mut reports);
    measure("katsura-6", &katsura::<6, F>(), &ALL, &mut reports);
    measure("katsura-7", &katsura::<7, F>(), &GRADED, &mut reports);
    measure("random-4", &random_system::<4>(5), &ALL, &mut reports);
    measure(
        "planted-6",
        &planted::<6, F>(&planted_point::<6>(9)),
        &ALL,
        &mut reports,
    );

    println!("Row operations and peak live nonzeros, on replayed batches. Ratios are against");
    println!("`base`, so below 1.00 is cheaper. `rf` is the arrangement alone, `blk` adds the");
    println!("split-aware elimination, `int` interreduces the reducer block first.");
    println!();
    println!(
        "{:<11} {:<8} {:>7} {:>6} {:>10} {:>7} {:>7} {:>7} {:>10} {:>7} {:>7} {:>7}",
        "system",
        "order",
        "batches",
        "red%",
        "ops:base",
        "ops:rf",
        "ops:blk",
        "ops:int",
        "peak:base",
        "pk:rf",
        "pk:blk",
        "pk:int",
    );
    for report in &reports {
        let base = report.totals[0];
        println!(
            "{:<11} {:<8} {:>7} {:>6.1} {:>10} {:>7.2} {:>7.2} {:>7.2} {:>10} {:>7.2} {:>7.2} {:>7.2}",
            report.system,
            report.order,
            report.batches,
            report.reducer_share,
            base.row_operations,
            ratio(report.totals[1].row_operations, base.row_operations),
            ratio(report.totals[2].row_operations, base.row_operations),
            ratio(report.totals[3].row_operations, base.row_operations),
            base.peak_nonzeros,
            ratio(report.totals[1].peak_nonzeros, base.peak_nonzeros),
            ratio(report.totals[2].peak_nonzeros, base.peak_nonzeros),
            ratio(report.totals[3].peak_nonzeros, base.peak_nonzeros),
        );
    }

    println!();
    println!("Final nonzeros and elimination time over the same replayed batches. `lm` is whether");
    println!("the structured path produced the baseline's new leading monomials, which it must;");
    println!("`poly` is whether the candidate polynomials coincided, which it need not.");
    println!();
    println!(
        "{:<11} {:<8} {:>10} {:>7} {:>7} {:>9} {:>7} {:>7} {:>7} {:>5} {:>5}",
        "system",
        "order",
        "fin:base",
        "fin:blk",
        "fin:int",
        "ms:base",
        "ms:rf",
        "ms:blk",
        "ms:int",
        "lm",
        "poly",
    );
    for report in &reports {
        let base = report.totals[0];
        println!(
            "{:<11} {:<8} {:>10} {:>7.2} {:>7.2} {:>9.2} {:>7.2} {:>7.2} {:>7.2} {:>5} {:>5}",
            report.system,
            report.order,
            base.final_nonzeros,
            ratio(report.totals[2].final_nonzeros, base.final_nonzeros),
            ratio(report.totals[3].final_nonzeros, base.final_nonzeros),
            millis(base.elapsed),
            millis(report.totals[1].elapsed),
            millis(report.totals[2].elapsed),
            millis(report.totals[3].elapsed),
            if report.leading_monomials_agree {
                "yes"
            } else {
                "NO"
            },
            if report.polynomials_agree {
                "yes"
            } else {
                "no"
            },
        );
    }
}
