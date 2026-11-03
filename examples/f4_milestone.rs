//! The milestone figure: F4 against classical Buchberger, at matched and at default criteria.
//!
//! **Two comparisons, because they answer different questions, and reporting only the first
//! overstates what F4's matrix algorithm contributes.**
//!
//! The pair criteria are *shared machinery*: `PairCriteria` is applied by both engines, and
//! `buchberger_with_criteria` exists precisely so the classical engine can use them too. But the
//! two defaults differ — `F4Options::recommended()` enables `PairCriteria::ALL`, while
//! `buchberger()` uses `PairCriteria::default()`, which is `PRODUCT_ONLY`. So:
//!
//! - **`vs default`** compares what a caller gets from `f4(..)` against what they get from
//!   `buchberger(..)`. It answers "which function should I call", and it credits F4 with the
//!   criteria.
//! - **`vs matched`** gives both engines `PairCriteria::ALL`. It isolates the **matrix algorithm**
//!   — batching, symbolic preprocessing, structured elimination, the dense accumulator — from the
//!   critical-pair selection that either engine can use.
//!
//! The second is the controlled comparison. Where the two disagree, the difference is the
//! criteria's contribution and not F4's.
//!
//! ```text
//! cargo run --release --example f4_milestone
//! cargo run --release --example f4_milestone -- all   # also try Buchberger on the hard instances
//! ```
//!
//! The ablation in `examples/f4_ablation.rs` is the other half: it compares configurations of this
//! build to each other. Two of M16's changes are unconditional — a cheaper monomial hash and the
//! rewritten interreduction — so they are in every ablation row including its baseline, which is
//! why that table cannot measure what the milestone contributed in total.

use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        buchberger_with_criteria, f4_with_options, F4Options, PairCriteria,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

/// How long one Buchberger run may take before the instance is reported as unfinished.
const BUCHBERGER_BUDGET: Duration = Duration::from_secs(120);

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// The fastest of `rounds` runs: interference can only make a run slower.
fn fastest(rounds: usize, mut run: impl FnMut() -> Duration) -> Duration {
    (0..rounds).map(|_| run()).min().expect("a round")
}

/// Time `buchberger_with_criteria`, abandoning the instance if the first run exceeds the budget.
///
/// Timed once first, so an instance that takes minutes costs one such run rather than `rounds` of
/// them.
fn time_buchberger<const N: usize>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    criteria: &PairCriteria,
    rounds: usize,
) -> Option<(Duration, Vec<MultivariatePolynomial<N, F>>)> {
    let at = Instant::now();
    let basis = buchberger_with_criteria(system, order, criteria).0;
    let first = at.elapsed();
    if first > BUCHBERGER_BUDGET {
        return None;
    }
    let best = fastest(rounds.saturating_sub(1).max(1), || {
        let at = Instant::now();
        let _ = buchberger_with_criteria(system, order, criteria);
        at.elapsed()
    })
    .min(first);
    Some((best, basis))
}

struct Row {
    name: String,
    order: &'static str,
    bb_product: Option<f64>,
    bb_all: Option<f64>,
    f4_base: f64,
    f4_best: f64,
    basis: usize,
}

fn measure<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    rounds: usize,
    try_buchberger: bool,
) -> Row {
    let recommended = F4Options::recommended();
    let baseline = F4Options::baseline();

    let f4_best = fastest(rounds, || {
        let at = Instant::now();
        let _ = f4_with_options(system, order, &recommended).expect("within limits");
        at.elapsed()
    });
    let f4_base = fastest(rounds, || {
        let at = Instant::now();
        let _ = f4_with_options(system, order, &baseline).expect("within limits");
        at.elapsed()
    });
    let (basis, _) = f4_with_options(system, order, &recommended).expect("within limits");

    let (bb_product, bb_all) = if try_buchberger {
        let product = time_buchberger(system, order, &PairCriteria::PRODUCT_ONLY, rounds);
        let all = time_buchberger(system, order, &PairCriteria::ALL, rounds);
        // Both engines must return the same basis under either criteria setting: a criterion that
        // changed the answer would be a defect, so this is asserted rather than assumed.
        for (label, result) in [("product", &product), ("all", &all)] {
            if let Some((_, bb)) = result {
                assert_eq!(
                    bb,
                    &basis,
                    "{} / {} / buchberger {}: the engines disagree",
                    name,
                    order.name(),
                    label
                );
            }
        }
        (product.map(|(t, _)| millis(t)), all.map(|(t, _)| millis(t)))
    } else {
        (None, None)
    };

    Row {
        name: name.to_string(),
        order: order.name(),
        bb_product,
        bb_all,
        f4_base: millis(f4_base),
        f4_best: millis(f4_best),
        basis: basis.len(),
    }
}

fn print_row(r: &Row) {
    let cell = |v: Option<f64>| match v {
        Some(t) => format!("{:.2}", t),
        None => "-".to_string(),
    };
    let ratio = |n: Option<f64>| match n {
        Some(t) => format!("{:.2}x", t / r.f4_best),
        None => "-".to_string(),
    };
    println!(
        "{:<12} {:<8} {:>11} {:>11} {:>10} {:>10} {:>11} {:>11} {:>6}",
        r.name,
        r.order,
        cell(r.bb_product),
        cell(r.bb_all),
        format!("{:.2}", r.f4_base),
        format!("{:.2}", r.f4_best),
        ratio(r.bb_product),
        ratio(r.bb_all),
        r.basis
    );
}

fn planted_point<const N: usize>(seed: u64) -> Vec<F> {
    use rand::{prelude::StdRng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(seed);
    (0..N).map(|_| F::random(&mut rng)).collect()
}

fn header() {
    println!(
        "{:<12} {:<8} {:>11} {:>11} {:>10} {:>10} {:>11} {:>11} {:>6}",
        "system",
        "order",
        "bb product",
        "bb all",
        "f4 base",
        "f4 best",
        "vs default",
        "vs matched",
        "basis"
    );
}

fn main() {
    let hard = std::env::args().nth(1).as_deref() == Some("all");

    println!("Classical Buchberger and F4 on identical inputs in one process, GF(2^31 - 1).");
    println!("Each figure is the fastest of several runs; a dash means the engine did not finish");
    println!(
        "within {} s. Bases are asserted equal between engines.",
        BUCHBERGER_BUDGET.as_secs()
    );
    println!();
    println!("`bb product` is `buchberger()`, which uses PairCriteria::PRODUCT_ONLY.");
    println!(
        "`bb all` is `buchberger_with_criteria(.., PairCriteria::ALL)` — the SAME criteria F4"
    );
    println!("    uses by default, so `vs matched` isolates F4's matrix algorithm from the");
    println!("    critical-pair selection that either engine can use.");
    println!(
        "`f4 base` is F4Options::baseline(); `f4 best` is F4Options::recommended() = default."
    );
    println!();
    header();

    use MonomialOrder::Lexicographic as LEX;
    use MonomialOrder::{GradedLexicographic as GRLEX, GradedReverseLexicographic as GREVLEX};

    let mut rows = Vec::new();
    for order in [LEX, GRLEX, GREVLEX] {
        rows.push(measure::<4>("cyclic-4", &cyclic::<4, F>(), order, 5, true));
    }
    for order in [LEX, GRLEX, GREVLEX] {
        rows.push(measure::<5>("cyclic-5", &cyclic::<5, F>(), order, 3, true));
    }
    for order in [LEX, GRLEX, GREVLEX] {
        rows.push(measure::<5>(
            "katsura-5",
            &katsura::<5, F>(),
            order,
            3,
            true,
        ));
    }
    for order in [GRLEX, GREVLEX] {
        rows.push(measure::<6>(
            "katsura-6",
            &katsura::<6, F>(),
            order,
            3,
            true,
        ));
    }
    let point = planted_point::<6>(9);
    for order in [LEX, GRLEX, GREVLEX] {
        rows.push(measure::<6>(
            "planted-6",
            &planted::<6, F>(&point),
            order,
            5,
            true,
        ));
    }
    for r in &rows {
        print_row(r);
    }

    // The three instances the preceding milestone could not pair against Buchberger at all. With
    // the criteria enabled the classical engine may now reach them, which would itself be a
    // result, so they are attempted rather than assumed hopeless.
    println!();
    println!("Instances the preceding milestone reported as out of Buchberger's reach:");
    header();
    let hard_rows = vec![
        measure::<6>("katsura-6", &katsura::<6, F>(), LEX, 2, hard),
        measure::<7>("katsura-7", &katsura::<7, F>(), GRLEX, 2, hard),
        measure::<7>("katsura-7", &katsura::<7, F>(), GREVLEX, 2, hard),
    ];
    for r in &hard_rows {
        print_row(r);
    }
    if !hard {
        println!();
        println!("(Buchberger not attempted on those three; pass `all` to try it under both");
        println!(
            "criteria settings, with a {} s budget per run.)",
            BUCHBERGER_BUDGET.as_secs()
        );
    }
}
