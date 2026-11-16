//! The route-selection table of `docs/research/strategy-selection.md`: every route on every
//! instance, repeated and interleaved, with the time and memory winners and their margins.
//!
//! ```text
//! tools/benchlock.sh strategy-selection \
//!     cargo run --release --example strategy_selection -- [repetitions]
//! ```
//!
//! A row is "within noise" when the winner's slowest repetition is no faster than the runner-up's
//! fastest — the ranges overlap, so the ordering is not established by this run.

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::Zp2147483647,
    grobner::{
        analyze,
        benchmark_systems::{cyclic, eco, katsura, noon, planted, reimer},
        solve_one_planned, PlanObjective, PlannedSolveOptions, SolvePolicy, SolveStrategy,
    },
    FiniteField, KnownOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

/// F4's cooperative time limit per basis computation, so a route that cannot finish is a bounded
/// refusal rather than a half-minute row. Every route runs under it.
const ROUTE_BUDGET: Duration = Duration::from_secs(2);

/// A route is a strategy plus the F4 batch cap it runs under.
#[derive(Clone, Copy)]
struct Route {
    name: &'static str,
    strategy: SolveStrategy,
    pair_cap: Option<usize>,
}

const ROUTES: [Route; 4] = [
    Route {
        name: "grevlex+FGLM",
        strategy: SolveStrategy::GrevlexF4ThenFglm,
        pair_cap: None,
    },
    Route {
        name: "direct lex",
        strategy: SolveStrategy::DirectLexF4,
        pair_cap: None,
    },
    Route {
        name: "grevlex/cap+FGLM",
        strategy: SolveStrategy::GrevlexF4ThenFglm,
        pair_cap: Some(PlanObjective::MEMORY_PAIR_CAP),
    },
    Route {
        name: "direct lex/cap",
        strategy: SolveStrategy::DirectLexF4,
        pair_cap: Some(PlanObjective::MEMORY_PAIR_CAP),
    },
];

/// One repetition of one route: wall clock, estimated peak bytes, quotient dimension if counted.
struct Run {
    elapsed: Duration,
    peak: usize,
    batches: usize,
    dimension: Option<usize>,
    completed: bool,
}

fn run<const N: usize, FF: KnownOrder>(
    system: &[MultivariatePolynomial<N, FF>],
    route: Route,
) -> Run {
    let mut options = PlannedSolveOptions::with_policy(SolvePolicy::Explicit(route.strategy));
    options.attempt.f4.max_pairs_per_batch = route.pair_cap;
    options.attempt.f4.max_wall_time = Some(ROUTE_BUDGET);
    let at = Instant::now();
    let (outcome, plan) = solve_one_planned(system, &mut StdRng::seed_from_u64(273), &options);
    let elapsed = at.elapsed();
    if let Ok(outcome) = &outcome {
        if let Some(point) = outcome.point() {
            assert!(system.iter().all(|p| p.eval(&point).is_zero()));
        }
    }
    Run {
        elapsed,
        peak: plan.peak_estimated_bytes(),
        batches: plan.total_batches(),
        dimension: plan
            .attempts
            .iter()
            .find_map(|a| a.statistics.fglm.as_ref().map(|s| s.quotient_dimension)),
        completed: outcome.is_ok(),
    }
}

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// What each objective's plan chose, by the route name it ran.
fn chosen<const N: usize, FF: KnownOrder>(
    system: &[MultivariatePolynomial<N, FF>],
    objective: PlanObjective,
) -> String {
    let mut options = PlannedSolveOptions::with_policy(SolvePolicy::ConservativeAuto);
    options.objective = objective;
    let (_, plan) = solve_one_planned(system, &mut StdRng::seed_from_u64(273), &options);
    plan.attempts
        .iter()
        .map(|a| match (a.strategy, a.pair_cap.is_some()) {
            (SolveStrategy::GrevlexF4ThenFglm, false) => "grevlex+FGLM",
            (SolveStrategy::DirectLexF4, false) => "direct lex",
            (SolveStrategy::GrevlexF4ThenFglm, true) => "grevlex/cap+FGLM",
            (SolveStrategy::DirectLexF4, true) => "direct lex/cap",
        })
        .collect::<Vec<_>>()
        .join(" → ")
}

fn table<const N: usize, FF: KnownOrder>(
    name: &str,
    system: &[MultivariatePolynomial<N, FF>],
    repetitions: usize,
) {
    let shape = analyze(system);
    // Interleaved: repetition r runs every route before repetition r + 1 starts, so a drift in
    // ambient load lands on every arm alike. The arm order rotates with r.
    let mut runs: Vec<Vec<Run>> = ROUTES.iter().map(|_| Vec::new()).collect();
    for r in 0..repetitions {
        for k in 0..ROUTES.len() {
            let index = (k + r) % ROUTES.len();
            runs[index].push(run(system, ROUTES[index]));
        }
    }

    let dimension = runs
        .iter()
        .flatten()
        .find_map(|r| r.dimension)
        .map_or("—".to_string(), |d| d.to_string());
    println!();
    println!(
        "### {} — N = {}, {} generators, max degree {}, interaction density {:.2}, D = {}",
        name,
        shape.variables,
        shape.generators,
        shape.max_degree,
        shape.interaction_density(),
        dimension
    );
    println!();
    println!("| route | median ms | min ms | max ms | peak est. bytes | batches | completed |");
    println!("|---|---:|---:|---:|---:|---:|---|");
    let mut summary = Vec::new();
    for (route, runs) in ROUTES.iter().zip(&runs) {
        let mut times: Vec<f64> = runs.iter().map(|r| millis(r.elapsed)).collect();
        times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let median = times[times.len() / 2];
        let completed = runs.iter().all(|r| r.completed);
        let peak = runs[0].peak;
        println!(
            "| {} | {:.3} | {:.3} | {:.3} | {} | {} | {} |",
            route.name,
            median,
            times[0],
            times[times.len() - 1],
            peak,
            runs[0].batches,
            if completed {
                "yes"
            } else {
                "no (2 s F4 budget)"
            }
        );
        if completed {
            summary.push((route.name, median, times[0], times[times.len() - 1], peak));
        }
    }

    let mut by_time = summary.clone();
    by_time.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
    let mut by_memory = summary.clone();
    by_memory.sort_by_key(|s| s.4);
    if by_time.len() >= 2 {
        let (w, r) = (by_time[0], by_time[1]);
        println!();
        println!(
            "time winner: {} by {:.2}x over {}{}",
            w.0,
            r.1 / w.1,
            r.0,
            if w.3 >= r.2 { " (within noise)" } else { "" }
        );
        let (w, r) = (by_memory[0], by_memory[1]);
        println!(
            "memory winner: {} by {:.2}x over {}{}",
            w.0,
            r.4 as f64 / w.4.max(1) as f64,
            r.0,
            if w.4 == r.4 { " (tie)" } else { "" }
        );
    }
    for objective in [
        PlanObjective::Time,
        PlanObjective::PeakMemory,
        PlanObjective::CompletionWithinBudget,
    ] {
        println!(
            "planner under {:?}: {}",
            objective,
            chosen(system, objective)
        );
    }
}

fn point(n: usize) -> Vec<F> {
    (0..n).map(|i| F::new(2 * i as u64 + 3)).collect()
}

fn main() {
    let repetitions: usize = std::env::args()
        .nth(1)
        .map(|s| s.parse().expect("repetitions is a count"))
        .unwrap_or(5);
    println!("# Route selection, GF(2^31 - 1), {repetitions} interleaved repetitions per route");
    println!();
    println!(
        "Pair cap for the capped routes: {} pairs per batch. Peak bytes are the planner's payload \
         estimate (`SolvePlan::peak_estimated_bytes`), not RSS. Every F4 computation runs under \
         a {:?} wall-time budget.",
        PlanObjective::MEMORY_PAIR_CAP,
        ROUTE_BUDGET
    );

    table("katsura-5", &katsura::<5, F>(), repetitions);
    table("katsura-6", &katsura::<6, F>(), repetitions);
    table("cyclic-5", &cyclic::<5, F>(), repetitions);
    table("eco-6", &eco::<6, F>(), repetitions);
    table("eco-7", &eco::<7, F>(), repetitions);
    table("noon-4", &noon::<4, F>(), repetitions);
    table("noon-5", &noon::<5, F>(), repetitions);
    table("reimer-4", &reimer::<4, F>(), repetitions);
    table("planted-8", &planted::<8, F>(&point(8)), repetitions);
    table("planted-10", &planted::<10, F>(&point(10)), repetitions);
}
