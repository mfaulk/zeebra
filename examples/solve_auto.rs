//! Four policies on the corpus, against an offline best-of-two the planner was not allowed to see.
//!
//! M21-D's comparison, and M21-I's harness. The question is not which policy is fastest — an
//! oracle that always picked the winning route would be, and no policy can be an oracle — but
//! whether the conservative policy **completes what the explicit routes complete**, and what it
//! pays in discarded work to do so.
//!
//! The best-of-two column is a *reference*, computed by running both explicit routes and taking
//! the better. A planner that had that information would not need a policy.
//!
//! ```text
//! cargo run --release --example solve_auto
//! ```
//! Takes about 35 seconds, nearly all of it explicit direct lex on katsura-7 — which is the
//! measurement, not an inconvenience.

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        solve_one_planned, solve_one_with_outcome, PlannedSolveOptions, SolveOptions, SolveOutcome,
        SolvePolicy, SolveStrategy,
    },
    FiniteField, KnownOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// What one configuration did with one system.
struct Result_ {
    /// Whether it established a mathematical fact at all.
    completed: bool,
    /// Wall clock, including every attempt a policy made.
    total: f64,
    /// Of that, time spent on attempts that established nothing.
    discarded: f64,
    /// Routes run. One for an explicit strategy, one or two for a policy.
    attempts: usize,
    /// What it established, or the limit it hit.
    verdict: String,
}

/// An explicit route, which is one attempt by definition.
fn explicit<const N: usize, FF: KnownOrder>(
    system: &[MultivariatePolynomial<N, FF>],
    strategy: SolveStrategy,
    seed: u64,
) -> Result_ {
    let mut rng = StdRng::seed_from_u64(seed);
    let at = Instant::now();
    let outcome = solve_one_with_outcome(system, &mut rng, &SolveOptions::with_strategy(strategy));
    let total = millis(at.elapsed());

    let (completed, verdict) = match outcome {
        Ok((outcome, _)) => (true, describe(&outcome, system)),
        Err(e) => (false, e.to_string()),
    };
    Result_ {
        completed,
        total,
        discarded: if completed { 0.0 } else { total },
        attempts: 1,
        verdict,
    }
}

/// A policy, which may make two attempts and must account for both.
fn planned<const N: usize, FF: KnownOrder>(
    system: &[MultivariatePolynomial<N, FF>],
    policy: SolvePolicy,
    seed: u64,
) -> Result_ {
    let mut rng = StdRng::seed_from_u64(seed);
    let (outcome, plan) =
        solve_one_planned(system, &mut rng, &PlannedSolveOptions::with_policy(policy));

    let (completed, verdict) = match outcome {
        Ok(outcome) => (true, describe(&outcome, system)),
        Err(e) => (false, e.to_string()),
    };
    Result_ {
        completed,
        total: millis(plan.total_elapsed()),
        discarded: millis(plan.discarded_elapsed()),
        attempts: plan.attempts.len(),
        verdict,
    }
}

/// Describe an outcome, verifying a point against the original generators first.
fn describe<const N: usize, FF: KnownOrder>(
    outcome: &SolveOutcome<N, FF>,
    system: &[MultivariatePolynomial<N, FF>],
) -> String {
    match outcome {
        SolveOutcome::Point(point) => {
            for p in system {
                assert!(p.eval(point).is_zero(), "the point does not satisfy {}", p);
            }
            "verified point".to_string()
        }
        SolveOutcome::NoBaseFieldPoint => "no F-point".to_string(),
        SolveOutcome::Inconsistent => "inconsistent".to_string(),
    }
}

fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        format!("{}…", s.chars().take(width - 1).collect::<String>())
    }
}

fn report<const N: usize, FF: KnownOrder>(
    name: &str,
    system: &[MultivariatePolynomial<N, FF>],
    seed: u64,
) {
    let direct = explicit(system, SolveStrategy::DirectLexF4, seed);
    let fglm = explicit(system, SolveStrategy::GrevlexF4ThenFglm, seed);
    let conservative = planned(system, SolvePolicy::ConservativeAuto, seed);
    let fallback = planned(system, SolvePolicy::AutoWithFallback, seed);

    // The reference: run both explicit routes, keep the better. Information no policy has.
    let best = match (direct.completed, fglm.completed) {
        (true, true) => format!("{:.1}", direct.total.min(fglm.total)),
        (true, false) => format!("{:.1}", direct.total),
        (false, true) => format!("{:.1}", fglm.total),
        (false, false) => "—".to_string(),
    };

    for (label, r) in [
        ("direct", &direct),
        ("fglm", &fglm),
        ("conservative", &conservative),
        ("fallback", &fallback),
    ] {
        println!(
            "| {:<12} | {:<12} | {:>3} | {:>9} | {:>9} | {:>9} | {:<38} |",
            name,
            label,
            r.attempts,
            format!("{:.1}", r.total),
            if r.discarded > 0.0 {
                format!("{:.1}", r.discarded)
            } else {
                "—".to_string()
            },
            if label == "fallback" { &best } else { "" },
            truncate(&r.verdict, 38),
        );
    }
}

fn header() {
    println!(
        "| {:<12} | {:<12} | {:>3} | {:>9} | {:>9} | {:>9} | {:<38} |",
        "system", "policy", "att", "total ms", "wasted ms", "best-of-2", "outcome"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(14),
        "-".repeat(14),
        "-".repeat(5),
        "-".repeat(11),
        "-".repeat(11),
        "-".repeat(11),
        "-".repeat(40)
    );
}

fn point(n: usize) -> Vec<F> {
    (0..n).map(|i| F::new(2 * i as u64 + 3)).collect()
}

fn parse<const N: usize>(strings: &[&str], vars: [&str; N]) -> Vec<MultivariatePolynomial<N, F>> {
    strings
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, vars).expect("parses"))
        .collect()
}

fn main() {
    println!("# Four policies against an offline best-of-two");
    println!();
    println!("Field GF(2^31 - 1), default budgets. `att` is routes run; `wasted ms` is time on");
    println!("attempts that established nothing. `best-of-2` is printed once per system and is a");
    println!("reference the planner did not have.");
    println!();
    header();

    report("katsura-6", &katsura::<6, F>(), 1);
    report("katsura-7", &katsura::<7, F>(), 2);
    report("cyclic-5", &cyclic::<5, F>(), 3);
    report("cyclic-6", &cyclic::<6, F>(), 4);
    report("planted-8", &planted::<8, F>(&point(8)), 5);
    report("planted-10", &planted::<10, F>(&point(10)), 6);
    report("planted-12", &planted::<12, F>(&point(12)), 7);
    report("cyclic-4", &cyclic::<4, F>(), 8);
    report("inconsistent", &parse(&["x - 1", "x - 2"], ["x", "y"]), 9);
    report("no-F-point", &parse(&["x^2 + 1", "y"], ["x", "y"]), 10);

    println!();
    println!("## One plan in full");
    println!();
    let system = planted::<12, F>(&point(12));
    let (_, plan) = solve_one_planned(
        &system,
        &mut StdRng::seed_from_u64(99),
        &PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback),
    );
    println!("{}", plan);
    println!();
    println!("planted-12 is the case the policy exists for. The conversion is ruled out from a");
    println!("*counted* quotient dimension before a single operator column is built — not from an");
    println!(
        "estimate, and not after a budget was crossed — and the direct route then finishes in"
    );
    println!("about a millisecond. The grevlex basis is discarded, and the plan says so.");
}
