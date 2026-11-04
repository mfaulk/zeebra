//! What deduplicating the border's normal forms is worth, and what it is not worth.
//!
//! The same border monomial is reached by several operator columns — `x*y` from both `x * y` and
//! `y * x` — and M17 reduced it once per column. Reducing it once per *monomial* removes between a
//! fifth and a third of the reductions. Whether that removes a fifth to a third of the **time** is
//! a different question, because border monomials do not cost the same to reduce: a repeated one is
//! reached from two directions, which happens low in the order, which correlates with being cheap.
//!
//! So this measures both, and prints them side by side. It also answers the question §5.3 of the
//! milestone proposal asks — whether the one-term `MultivariatePolynomial` built per reduction is
//! worth a specialized entry point — by timing those constructions on their own against the
//! reductions that follow them.
//!
//! ```text
//! cargo run --release --example fglm_border
//! cargo run --release --example fglm_border -- katsura-7
//! ```

use std::{
    io::Write,
    time::{Duration, Instant},
};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        f4,
        fglm::{
            fglm_to_lex_with_options, BorderIndex, FglmOptions, FglmStatistics,
            OperatorConstruction, QuotientBasis,
        },
    },
    FiniteField, MonomialOrder, MultivariatePolynomial, One,
};

type F = Zp2147483647;

const SOURCE: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// The fastest of three runs: interference can only make a run slower.
fn fastest(mut run: impl FnMut() -> Duration) -> Duration {
    (0..3).map(|_| run()).min().expect("a round")
}

/// One conversion under one strategy, measured.
fn convert<const N: usize>(
    source: &[MultivariatePolynomial<N, F>],
    construction: OperatorConstruction,
) -> (Duration, FglmStatistics) {
    let mut options = FglmOptions::unbounded().with_operator_construction(construction);
    options.measure_stages = true;

    let mut best: Option<(Duration, FglmStatistics)> = None;
    for _ in 0..3 {
        let at = Instant::now();
        let (_, statistics) =
            fglm_to_lex_with_options(source, SOURCE, &options).expect("convertible");
        let wall = at.elapsed();
        if best.as_ref().is_none_or(|(previous, _)| wall < *previous) {
            best = Some((wall, statistics));
        }
    }
    best.expect("a round")
}

/// What the one-term polynomials cost, against the reductions they precede.
///
/// Both loops walk the same border monomials in the same order. The first stops at the polynomial;
/// the second reduces it. The difference is the reduction, and the first is the thing §5.3 asks
/// about — which is why it is timed as itself rather than inferred from a stage total.
fn term_construction_share<const N: usize>(source: &[MultivariatePolynomial<N, F>]) -> (f64, f64) {
    let quotient = QuotientBasis::new(source, SOURCE, usize::MAX).expect("finite");
    let border = BorderIndex::new(&quotient).monomials().to_vec();

    let construction = fastest(|| {
        let at = Instant::now();
        for monomial in &border {
            let term: MultivariatePolynomial<N, F> =
                MultivariatePolynomial::new(&[(*monomial, F::one())]);
            // Consumed so the construction cannot be optimized away as dead.
            std::hint::black_box(term.is_zero());
        }
        at.elapsed()
    });

    let with_reduction = fastest(|| {
        let at = Instant::now();
        for monomial in &border {
            let term: MultivariatePolynomial<N, F> =
                MultivariatePolynomial::new(&[(*monomial, F::one())]);
            std::hint::black_box(term.normal_form(source, SOURCE).is_zero());
        }
        at.elapsed()
    });

    (millis(construction), millis(with_reduction))
}

fn header() {
    println!(
        "| {:<11} | {:>5} | {:>7} | {:>6} | {:>9} | {:>9} | {:>8} | {:>10} | {:>9} | {:>9} |",
        "system",
        "D",
        "|∂B|",
        "dup %",
        "nf/column",
        "nf/border",
        "nf won",
        "per-column",
        "dedup",
        "total won",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(7),
        "-".repeat(9),
        "-".repeat(8),
        "-".repeat(11),
        "-".repeat(11),
        "-".repeat(10),
        "-".repeat(12),
        "-".repeat(11),
        "-".repeat(11),
    );
}

fn measure<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
    let source = f4(system, SOURCE).expect("within limits");

    let (reference_wall, reference) = convert(&source, OperatorConstruction::PerColumn);
    let (optimized_wall, optimized) = convert(&source, OperatorConstruction::DeduplicatedBorder);

    // The strategies are asserted equal by the test suite; asserted again here so a table printed
    // from a broken build cannot be mistaken for a measurement.
    assert_eq!(
        reference.operator_entries, optimized.operator_entries,
        "{}: the strategies stored different amounts",
        name
    );
    assert_eq!(
        reference.border.border_columns, reference.border.normal_form_calls,
        "{}: the reference path did not reduce once per column",
        name
    );
    assert_eq!(
        optimized.border.distinct_border_monomials, optimized.border.normal_form_calls,
        "{}: the deduplicated path did not reduce once per border monomial",
        name
    );

    let reference_nf = millis(reference.timings.normal_forms);
    let optimized_nf = millis(optimized.timings.normal_forms);

    println!(
        "| {:<11} | {:>5} | {:>7} | {:>6.1} | {:>9.2} | {:>9.2} | {:>7.2}x | {:>10.2} | {:>9.2} | {:>8.2}x |",
        name,
        reference.quotient_dimension,
        reference.border.distinct_border_monomials,
        100.0 * reference.border.duplication_rate().unwrap_or(0.0),
        reference_nf,
        optimized_nf,
        reference_nf / optimized_nf.max(f64::MIN_POSITIVE),
        millis(reference_wall),
        millis(optimized_wall),
        millis(reference_wall) / millis(optimized_wall).max(f64::MIN_POSITIVE),
    );
    std::io::stdout().flush().expect("stdout");
}

fn allocation_row<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
    let source = f4(system, SOURCE).expect("within limits");
    let (construction, with_reduction) = term_construction_share(&source);
    println!(
        "| {:<11} | {:>13.3} | {:>13.3} | {:>9.2}% |",
        name,
        construction,
        with_reduction,
        100.0 * construction / with_reduction.max(f64::MIN_POSITIVE),
    );
    std::io::stdout().flush().expect("stdout");
}

fn planted_point<const N: usize>() -> Vec<F> {
    (0..N).map(|i| F::new(2 * i as u64 + 3)).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let wanted = |name: &str| args.is_empty() || args.iter().any(|a| a == name);

    println!("# Border deduplication, GF(2^31 - 1), grevlex source, fastest of three");
    println!();
    header();

    if wanted("katsura-5") {
        measure("katsura-5", &katsura::<5, F>());
    }
    if wanted("katsura-6") {
        measure("katsura-6", &katsura::<6, F>());
    }
    if wanted("katsura-7") {
        measure("katsura-7", &katsura::<7, F>());
    }
    if wanted("cyclic-5") {
        measure("cyclic-5", &cyclic::<5, F>());
    }
    if wanted("cyclic-6") {
        measure("cyclic-6", &cyclic::<6, F>());
    }
    if wanted("planted-6") {
        measure("planted-6", &planted::<6, F>(&planted_point::<6>()));
    }
    if wanted("planted-8") {
        measure("planted-8", &planted::<8, F>(&planted_point::<8>()));
    }
    if wanted("planted-10") {
        measure("planted-10", &planted::<10, F>(&planted_point::<10>()));
    }

    println!();
    println!("`nf/column` and `nf/border` are the normal-form stage under each strategy, in");
    println!("milliseconds; `nf won` is the first over the second. `per-column` and `dedup` are");
    println!("the whole conversion's wall clock. **`nf won` is the ceiling and `total won` is the");
    println!(
        "result**: the reduction is only part of a conversion, and on the planted family it is"
    );
    println!("a quarter of it.");

    println!();
    println!("# What the one-term polynomial per reduction costs (milestone proposal §5.3)");
    println!();
    println!(
        "| {:<11} | {:>13} | {:>13} | {:>10} |",
        "system", "construct ms", "and reduce ms", "construct %"
    );
    println!(
        "|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(15),
        "-".repeat(15),
        "-".repeat(12)
    );
    if wanted("katsura-6") {
        allocation_row("katsura-6", &katsura::<6, F>());
    }
    if wanted("katsura-7") {
        allocation_row("katsura-7", &katsura::<7, F>());
    }
    if wanted("cyclic-6") {
        allocation_row("cyclic-6", &cyclic::<6, F>());
    }
    if wanted("planted-8") {
        allocation_row("planted-8", &planted::<8, F>(&planted_point::<8>()));
    }
    if wanted("planted-10") {
        allocation_row("planted-10", &planted::<10, F>(&planted_point::<10>()));
    }

    println!();
    println!("Both columns walk the same border monomials; the first stops at the polynomial and");
    println!("the second reduces it. `construct %` is therefore the share of a reduction that is");
    println!("the allocation preceding it — the figure §5.3 asks for, measured rather than");
    println!("inferred from a stage total that contains both.");
}
