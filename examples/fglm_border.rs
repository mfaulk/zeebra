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
//! The third strategy, `BatchedBorder`, reduces the distinct border monomials in batches against a
//! shared symbolic closure, with the arithmetic over integer column indices rather than through a
//! polynomial's hash map. A fourth table varies the batch size, which is the trade §6.5 of the
//! proposal asks to be measured rather than guessed.
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
            fglm_to_lex_with_options, BorderBatch, BorderBatchSize, BorderIndex, FglmOptions,
            FglmStatistics, OperatorConstruction, QuotientBasis,
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
    size: BorderBatchSize,
) -> (Duration, FglmStatistics) {
    let mut options = FglmOptions::unbounded()
        .with_operator_construction(construction)
        .with_border_batch(BorderBatch::unbounded().with_size(size));
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
        "| {:<11} | {:>5} | {:>7} | {:>6} | {:>10} | {:>9} | {:>8} | {:>9} | {:>8} | {:>8} |",
        "system",
        "D",
        "|∂B|",
        "dup %",
        "per-column",
        "dedup",
        "batch 64",
        "batch inf",
        "dedup x",
        "batch x",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(7),
        "-".repeat(9),
        "-".repeat(8),
        "-".repeat(12),
        "-".repeat(11),
        "-".repeat(10),
        "-".repeat(11),
        "-".repeat(10),
        "-".repeat(10),
    );
}

fn measure<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
    let source = f4(system, SOURCE).expect("within limits");

    let unbounded = BorderBatchSize::Unbounded;
    let (reference_wall, reference) = convert(&source, OperatorConstruction::PerColumn, unbounded);
    let (dedup_wall, dedup) = convert(&source, OperatorConstruction::DeduplicatedBorder, unbounded);
    let (batch_wall, batched) = convert(
        &source,
        OperatorConstruction::BatchedBorder,
        BorderBatchSize::Fixed(64),
    );
    let (unbounded_wall, _) = convert(&source, OperatorConstruction::BatchedBorder, unbounded);

    // The strategies are asserted equal by the test suite; asserted again here so a table printed
    // from a broken build cannot be mistaken for a measurement.
    for (label, other) in [("dedup", &dedup), ("batched", &batched)] {
        assert_eq!(
            reference.operator_entries, other.operator_entries,
            "{}: {} stored a different amount",
            name, label
        );
    }
    assert_eq!(
        reference.border.border_columns, reference.border.normal_form_calls,
        "{}: the reference path did not reduce once per column",
        name
    );
    assert_eq!(
        dedup.border.distinct_border_monomials, dedup.border.normal_form_calls,
        "{}: the deduplicated path did not reduce once per border monomial",
        name
    );
    assert_eq!(
        batched.batches.fallbacks, 0,
        "{}: a batch fell back to the scalar path",
        name
    );

    println!(
        "| {:<11} | {:>5} | {:>7} | {:>6.1} | {:>10.2} | {:>9.2} | {:>8.2} | {:>9.2} | {:>7.2}x | {:>7.2}x |",
        name,
        reference.quotient_dimension,
        reference.border.distinct_border_monomials,
        100.0 * reference.border.duplication_rate().unwrap_or(0.0),
        millis(reference_wall),
        millis(dedup_wall),
        millis(batch_wall),
        millis(unbounded_wall),
        millis(reference_wall) / millis(dedup_wall).max(f64::MIN_POSITIVE),
        millis(reference_wall) / millis(batch_wall).max(f64::MIN_POSITIVE),
    );
    std::io::stdout().flush().expect("stdout");
}

fn batch_size_header() {
    println!(
        "| {:<11} | {:>5} | {:>7} | {:>8} | {:>8} | {:>8} | {:>8} | {:>9} | {:>9} | {:>11} |",
        "system",
        "D",
        "|∂B|",
        "size 1",
        "size 4",
        "size 16",
        "size 64",
        "unbounded",
        "batches",
        "peak entries",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(7),
        "-".repeat(9),
        "-".repeat(10),
        "-".repeat(10),
        "-".repeat(10),
        "-".repeat(10),
        "-".repeat(11),
        "-".repeat(11),
        "-".repeat(13),
    );
}

/// The whole conversion at each batch size the milestone names.
fn batch_size_row<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
    let source = f4(system, SOURCE).expect("within limits");

    let mut times = Vec::new();
    let mut reference: Option<FglmStatistics> = None;
    for size in [
        BorderBatchSize::Fixed(1),
        BorderBatchSize::Fixed(4),
        BorderBatchSize::Fixed(16),
        BorderBatchSize::Fixed(64),
        BorderBatchSize::Unbounded,
    ] {
        let options = FglmOptions::unbounded()
            .with_operator_construction(OperatorConstruction::BatchedBorder)
            .with_border_batch(BorderBatch::unbounded().with_size(size));

        let mut best: Option<(Duration, FglmStatistics)> = None;
        for _ in 0..3 {
            let at = Instant::now();
            let (_, statistics) =
                fglm_to_lex_with_options(&source, SOURCE, &options).expect("convertible");
            let wall = at.elapsed();
            if best.as_ref().is_none_or(|(previous, _)| wall < *previous) {
                best = Some((wall, statistics));
            }
        }
        let (wall, statistics) = best.expect("a round");
        // Every size must give the same operators, which the test suite asserts and this
        // re-asserts so a printed table cannot come from a broken build.
        if let Some(expected) = &reference {
            assert_eq!(
                statistics.operator_entries, expected.operator_entries,
                "{}: batch size {:?} stored a different amount",
                name, size
            );
        }
        // Overwritten each time, so what is reported is the **last** size's — the unbounded one,
        // whose batch count and closure are the figures the footnote names.
        reference = Some(statistics);
        times.push(millis(wall));
    }

    let unbounded = reference.expect("a round");
    println!(
        "| {:<11} | {:>5} | {:>7} | {:>8.2} | {:>8.2} | {:>8.2} | {:>8.2} | {:>9.2} | {:>9} | {:>11} |",
        name,
        unbounded.quotient_dimension,
        unbounded.border.distinct_border_monomials,
        times[0],
        times[1],
        times[2],
        times[3],
        times[4],
        unbounded.batches.batches,
        unbounded.batches.peak_reducer_entries,
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
    println!("Milliseconds for the whole conversion. `batch 64` is the size");
    println!(
        "`BorderBatch::recommended()` uses and `batch inf` is one batch for the whole border;"
    );
    println!(
        "`dedup x` and `batch x` are `per-column` over each of those two. The duplication rate"
    );
    println!("bounds what `dedup` can remove and says nothing about batching, which removes the");
    println!("polynomial arithmetic instead.");
    println!();
    println!(
        "**An unbounded batch loses on the planted family** — a reduction there is one step, so"
    );
    println!("the closure and the per-target column scan are most of the work — and a batch of 64");
    println!("does not: it is faster than the scalar path on every system above.");

    println!();
    println!("# Batch size, whole conversion, fastest of three");
    println!();
    batch_size_header();
    if wanted("katsura-6") {
        batch_size_row("katsura-6", &katsura::<6, F>());
    }
    if wanted("katsura-7") {
        batch_size_row("katsura-7", &katsura::<7, F>());
    }
    if wanted("cyclic-6") {
        batch_size_row("cyclic-6", &cyclic::<6, F>());
    }
    if wanted("planted-8") {
        batch_size_row("planted-8", &planted::<8, F>(&planted_point::<8>()));
    }
    if wanted("planted-10") {
        batch_size_row("planted-10", &planted::<10, F>(&planted_point::<10>()));
    }
    println!();
    println!("`batches` and `peak entries` are for the unbounded size. A smaller batch builds a");
    println!("smaller closure and shares less of it, so the sizes say which way that trade goes");
    println!("rather than leaving it to be guessed.");

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
