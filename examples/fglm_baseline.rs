//! The M17-0 baseline: what the FGLM pipeline has to beat, and which systems it may be run on.
//!
//! Two questions, measured together because the second decides which rows of the first are
//! relevant.
//!
//! 1. **Which benchmark systems are zero-dimensional?** FGLM applies to no others. A square
//!    system is not zero-dimensional merely for being square — cyclic-n is zero-dimensional only
//!    for squarefree n — so each candidate is classified from the leading monomials of a computed
//!    grevlex basis rather than assumed.
//! 2. **What does a lex basis cost today?** `grobner::solve` computes one with classical
//!    Buchberger. The FGLM pipeline computes a grevlex basis instead and converts, so the
//!    comparison is `lex direct` against `grevlex + conversion`, and this example measures every
//!    column of that except the conversion, which does not exist yet.
//!
//! The quotient dimension D is also reported, through `grobner::fglm`. It is the quantity that
//! controls FGLM's cost — n * D^3 arithmetic with dense linear algebra, and D^2 field elements per
//! multiplication operator — so it belongs beside the timings rather than in a later report.
//!
//! ```text
//! cargo run --release --example fglm_baseline
//! cargo run --release --example fglm_baseline -- cyclic-6         # one system
//! cargo run --release --example fglm_baseline -- all              # every system, hard ones too
//! cargo run --release --example fglm_baseline -- katsura-10        # an upper rung, by name
//! ```
//!
//! Rows print as they are measured and each names its system, so the hard instances can be run
//! one per process and the table assembled from the pieces.

use std::{
    io::Write,
    time::{Duration, Instant},
};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        buchberger_with_criteria, classify_ideal, f4_with_options, F4Error, F4Options, FglmError,
        IdealClass, PairCriteria, QuotientBasis,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

/// Whether to run classical Buchberger under lex on an instance.
///
/// Decided per instance rather than from a time budget, because a budget can only be checked
/// after the run it was meant to bound has already finished. M16 §8.3 established which instances
/// the classical engine cannot complete, and those are named here with that as the reason.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Classical {
    Attempt,
    /// Not attempted. [`OUT_OF_REACH`] is the reason, reported with the table.
    OutOfReach,
}

/// The largest quotient dimension this example will enumerate.
///
/// A zero-dimensional ideal can have a standard monomial basis far larger than any machine will
/// hold, so the walk is bounded and reports that it stopped rather than running out of memory.
const MAX_QUOTIENT_DIMENSION: usize = 1 << 20;

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// The fastest of `rounds` runs: interference can only make a run slower.
fn fastest(rounds: usize, mut run: impl FnMut() -> Duration) -> Duration {
    (0..rounds).map(|_| run()).min().expect("a round")
}

/// What timing one engine on one order produced.
enum Timed<const N: usize> {
    Ran {
        millis: f64,
        basis: Vec<MultivariatePolynomial<N, F>>,
    },
    /// A limit in `F4Options` was crossed.
    Limited(F4Error),
    /// Not attempted.
    Skipped,
}

impl<const N: usize> Timed<N> {
    fn millis(&self) -> String {
        match self {
            Self::Ran { millis, .. } => format!("{:.2}", millis),
            Self::Limited(e) => format!("{:?}", e),
            Self::Skipped => "—".to_string(),
        }
    }

    fn size(&self) -> String {
        match self {
            Self::Ran { basis, .. } => basis.len().to_string(),
            _ => "—".to_string(),
        }
    }

    fn basis(&self) -> Option<&[MultivariatePolynomial<N, F>]> {
        match self {
            Self::Ran { basis, .. } => Some(basis),
            _ => None,
        }
    }
}

/// Time F4 on one order, reporting a crossed limit rather than panicking on it.
fn time_f4<const N: usize>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    rounds: usize,
) -> Timed<N> {
    let options = F4Options::default();
    let (basis, _) = match f4_with_options(system, order, &options) {
        Ok(result) => result,
        Err(e) => return Timed::Limited(e),
    };
    let best = fastest(rounds, || {
        let at = Instant::now();
        let _ = f4_with_options(system, order, &options);
        at.elapsed()
    });
    Timed::Ran {
        millis: millis(best),
        basis,
    }
}

/// Time classical Buchberger under lex, at every pair criterion.
///
/// Timed once first, so an instance that takes minutes costs one such run rather than `rounds`.
fn time_buchberger<const N: usize>(
    system: &[MultivariatePolynomial<N, F>],
    rounds: usize,
) -> Timed<N> {
    let lex = MonomialOrder::Lexicographic;
    let at = Instant::now();
    let basis = buchberger_with_criteria(system, lex, &PairCriteria::ALL).0;
    let first = at.elapsed();
    let best = if first > Duration::from_millis(500) {
        first
    } else {
        fastest(rounds.saturating_sub(1).max(1), || {
            let at = Instant::now();
            let _ = buchberger_with_criteria(system, lex, &PairCriteria::ALL);
            at.elapsed()
        })
        .min(first)
    };
    Timed::Ran {
        millis: millis(best),
        basis,
    }
}

/// Measure one system and print its row: classification and D from grevlex, then both engines
/// under lex.
fn measure<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    rounds: usize,
    classical: Classical,
) -> Option<IdealClass> {
    let grevlex_order = MonomialOrder::GradedReverseLexicographic;
    let grevlex = time_f4(system, grevlex_order, rounds);

    // No basis means no classification: the ideal's dimension is not in question, it is simply
    // unknown here.
    let (class, quotient_dimension, walk) = match grevlex.basis() {
        None => (None, "—".to_string(), "—".to_string()),
        Some(basis) => {
            let class = classify_ideal(basis, grevlex_order);
            let at = Instant::now();
            let enumerated = QuotientBasis::new(basis, grevlex_order, MAX_QUOTIENT_DIMENSION);
            let elapsed = at.elapsed();
            let (d, walk) = match enumerated {
                Ok(quotient) => (
                    quotient.dimension().to_string(),
                    format!("{:.2}", millis(elapsed)),
                ),
                Err(FglmError::QuotientDimensionExceeded { .. }) => {
                    ("over".to_string(), format!("{:.2}", millis(elapsed)))
                }
                Err(FglmError::PositiveDimensional) => ("—".to_string(), "—".to_string()),
                // The enumeration builds no operators, so no other limit can fire here.
                Err(other) => (format!("{:?}", other), "—".to_string()),
            };
            (Some(class), d, walk)
        }
    };

    let lex_f4 = time_f4(system, MonomialOrder::Lexicographic, rounds);
    let lex_bb = match classical {
        Classical::Attempt => time_buchberger(system, rounds),
        Classical::OutOfReach => Timed::Skipped,
    };

    // Both engines return *the* reduced basis of the ideal under the order, so disagreement is a
    // bug in one of them rather than a difference of method. Checked wherever both ran.
    if let (Some(f4_basis), Some(bb_basis)) = (lex_f4.basis(), lex_bb.basis()) {
        assert_eq!(
            f4_basis, bb_basis,
            "{}: the two engines disagree on the lex basis",
            name
        );
    }

    println!(
        "| {:<11} | {:<8} | {:>6} | {:>10} | {:>5} | {:>8} | {:>10} | {:>5} | {:>10} |",
        name,
        class_name(class),
        quotient_dimension,
        grevlex.millis(),
        grevlex.size(),
        walk,
        lex_f4.millis(),
        lex_f4.size(),
        lex_bb.millis(),
    );
    std::io::stdout().flush().expect("stdout");
    class
}

/// The table's label for an ideal class.
fn class_name(class: Option<IdealClass>) -> &'static str {
    match class {
        Some(IdealClass::Unit) => "unit",
        Some(IdealClass::ZeroDimensional) => "zero-dim",
        Some(IdealClass::PositiveDimensional) => "positive",
        None => "unknown",
    }
}

fn header() {
    println!(
        "| {:<11} | {:<8} | {:>6} | {:>10} | {:>5} | {:>8} | {:>10} | {:>5} | {:>10} |",
        "system", "ideal", "D", "grevlex ms", "|G|", "walk ms", "lex f4 ms", "|G|", "lex bb ms",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(10),
        "-".repeat(8),
        "-".repeat(12),
        "-".repeat(7),
        "-".repeat(10),
        "-".repeat(12),
        "-".repeat(7),
        "-".repeat(12),
    );
}

/// A planted point, distinct values so no pair collapses.
fn planted_point<const N: usize>(seed: u64) -> Vec<F> {
    (0..N).map(|i| F::new(seed + 2 * i as u64 + 1)).collect()
}

/// The systems measured, each with whether classical Buchberger is attempted on it under lex.
///
/// `OutOfReach` is a published measurement, not a guess: M16 §8.3 reports katsura-6 under lex as
/// not finishing in 900 s with every critical-pair criterion enabled, and katsura-7 is strictly
/// larger. `all` attempts them regardless, and will then run for as long as they take.
const SYSTEMS: &[(&str, bool)] = &[
    ("cyclic-3", true),
    ("cyclic-4", true),
    ("cyclic-5", true),
    ("cyclic-6", true),
    ("katsura-3", true),
    ("katsura-4", true),
    ("katsura-5", true),
    ("katsura-6", false),
    ("katsura-7", false),
    ("planted-4", true),
    ("planted-6", true),
    ("planted-8", true),
];

/// #424's upper rungs, **excluded from a bare run** and reached by name or by `all`.
///
/// Not in [`SYSTEMS`] because a bare `fglm_baseline` should stay a few minutes: `katsura-11`'s
/// grevlex basis alone is about 280 s, and its lex F4 burns a budget before refusing. Classical
/// Buchberger is `OutOfReach` on every one — it already does not finish `katsura-6` under lex in
/// 900 s and these are strictly larger.
///
/// `cyclic-9` and `cyclic-10` are the **measured ceiling**: F4's grevlex basis crosses the
/// live-entry budget, which is a reproducible bound rather than a clock. They are listed so that
/// the refusal is a row rather than an omission — see `corpus`'s module header.
const UPPER_RUNGS: &[(&str, bool)] = &[
    ("katsura-8", false),
    ("katsura-9", false),
    ("katsura-10", false),
    ("katsura-11", false),
    ("cyclic-7", false),
    ("cyclic-8", false),
    ("cyclic-9", false),
    ("cyclic-10", false),
];

/// Why an instance's classical run is not attempted.
const OUT_OF_REACH: &str =
    "classical Buchberger does not finish it in 900 s at ALL criteria (M16 §8.3)";

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let force_all = args.iter().any(|a| a == "all");
    let wanted = |name: &str| args.is_empty() || force_all || args.iter().any(|a| a == name);
    let plan = |attempt: bool| {
        if attempt || force_all {
            Classical::Attempt
        } else {
            Classical::OutOfReach
        }
    };
    let rounds = 5;

    println!(
        "# M17-0 baseline: GF(2^31 - 1), F4Options::default(), lex Buchberger at ALL criteria"
    );
    println!();
    header();

    let mut classes: Vec<(&str, Option<IdealClass>)> = Vec::new();
    let point4 = planted_point::<4>(3);
    let point6 = planted_point::<6>(3);
    let point8 = planted_point::<8>(3);

    for (name, attempt) in SYSTEMS.iter().chain(UPPER_RUNGS) {
        // An upper rung needs its name, or `all`: a bare run must not become a
        // twenty-minute one by growth of the ladder.
        if UPPER_RUNGS.iter().any(|(upper, _)| upper == name)
            && !force_all
            && !args.iter().any(|a| a == name)
        {
            continue;
        }
        if !wanted(name) {
            continue;
        }
        let classical = plan(*attempt);
        let class = match *name {
            "cyclic-3" => measure(name, &cyclic::<3, F>(), rounds, classical),
            "cyclic-4" => measure(name, &cyclic::<4, F>(), rounds, classical),
            "cyclic-5" => measure(name, &cyclic::<5, F>(), rounds, classical),
            "cyclic-6" => measure(name, &cyclic::<6, F>(), rounds, classical),
            "cyclic-7" => measure(name, &cyclic::<7, F>(), rounds, classical),
            "cyclic-8" => measure(name, &cyclic::<8, F>(), rounds, classical),
            "cyclic-9" => measure(name, &cyclic::<9, F>(), rounds, classical),
            "cyclic-10" => measure(name, &cyclic::<10, F>(), rounds, classical),
            "katsura-3" => measure(name, &katsura::<3, F>(), rounds, classical),
            "katsura-4" => measure(name, &katsura::<4, F>(), rounds, classical),
            "katsura-5" => measure(name, &katsura::<5, F>(), rounds, classical),
            "katsura-6" => measure(name, &katsura::<6, F>(), rounds, classical),
            "katsura-7" => measure(name, &katsura::<7, F>(), rounds, classical),
            "katsura-8" => measure(name, &katsura::<8, F>(), rounds, classical),
            "katsura-9" => measure(name, &katsura::<9, F>(), rounds, classical),
            "katsura-10" => measure(name, &katsura::<10, F>(), rounds, classical),
            "katsura-11" => measure(name, &katsura::<11, F>(), rounds, classical),
            "planted-4" => measure(name, &planted::<4, F>(&point4), rounds, classical),
            "planted-6" => measure(name, &planted::<6, F>(&point6), rounds, classical),
            "planted-8" => measure(name, &planted::<8, F>(&point8), rounds, classical),
            other => panic!("no system named {}", other),
        };
        classes.push((name, class));
    }

    println!();
    let named = |which: IdealClass| {
        classes
            .iter()
            .filter(|(_, c)| *c == Some(which))
            .map(|(name, _)| *name)
            .collect::<Vec<_>>()
    };
    let zero_dimensional = named(IdealClass::ZeroDimensional);
    println!(
        "{} of {} systems are zero-dimensional, so FGLM applies to those: {}",
        zero_dimensional.len(),
        classes.len(),
        zero_dimensional.join(", ")
    );
    let positive = named(IdealClass::PositiveDimensional);
    if !positive.is_empty() {
        println!(
            "Positive-dimensional, so rejection cases rather than FGLM timings: {}",
            positive.join(", ")
        );
    }
    println!();
    println!("D is the dimension of R/I as an F-vector space, not the Krull dimension.");
    println!("`walk ms` is the frontier enumeration of the standard monomials, after the basis.");
    println!("A dash under `lex bb ms` means {}.", OUT_OF_REACH);
}
