//! From a polynomial system with a known solution to that solution, by both routes.
//!
//! The milestone's end-to-end demonstration: build a nontrivial zero-dimensional system, compute a
//! Gröbner basis, reach the lex basis either directly or by conversion, find a point by
//! back-substitution and univariate root finding, and verify it against the original equations.
//!
//! **Each route has a system the other cannot do**, which is why the strategy is the caller's and
//! why no heuristic picks it. katsura-7's lex basis is beyond F4's default limits, so the direct
//! route cannot solve it at all while the conversion does in 81 ms. planted-12 and planted-14 go
//! the other way: their quotient algebras have dimension 4096 and 16384, past what the conversion
//! will build, and the direct route solves both in under 2 ms.
//!
//! ```text
//! cargo run --release --example solve_one
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        solve_one_with_options, solve_zero_dimensional_with_options, SolveOptions, SolveStrategy,
    },
    FiniteField, MultivariatePolynomial, Zero,
};

type F = Zp2147483647;

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// What one strategy did with one system.
enum Outcome {
    /// Timings, the point count, and the branches each search charged.
    Solved {
        first: f64,
        all: f64,
        count: usize,
        first_branches: usize,
        all_branches: usize,
    },
    /// No point over the base field. Not a failure — the ideal can still be zero-dimensional.
    NoBaseFieldPoint { millis: f64 },
    /// A limit was crossed, or the system is out of scope.
    Failed(String),
}

impl Outcome {
    fn first(&self) -> String {
        match self {
            Self::Solved { first, .. } => format!("{:.2}", first),
            Self::NoBaseFieldPoint { millis } => format!("{:.2}", millis),
            Self::Failed(_) => "—".to_string(),
        }
    }

    fn all(&self) -> String {
        match self {
            Self::Solved { all, .. } => format!("{:.2}", all),
            Self::NoBaseFieldPoint { .. } => "—".to_string(),
            Self::Failed(_) => "—".to_string(),
        }
    }

    /// Branches charged finding one point, against finding all of them.
    fn branches(&self) -> String {
        match self {
            Self::Solved {
                first_branches,
                all_branches,
                ..
            } => format!("{} / {}", first_branches, all_branches),
            _ => "—".to_string(),
        }
    }

    fn verdict(&self) -> String {
        match self {
            Self::Solved { count, .. } => format!("{} points", count),
            Self::NoBaseFieldPoint { .. } => "no F-point".to_string(),
            Self::Failed(why) => why.clone(),
        }
    }
}

/// Solve one system under one strategy, timing the first point and then all of them.
fn attempt<const N: usize>(
    system: &[MultivariatePolynomial<N, F>],
    strategy: SolveStrategy,
    seed: u64,
) -> Outcome {
    let options = SolveOptions::with_strategy(strategy);
    let mut rng = StdRng::seed_from_u64(seed);

    let at = Instant::now();
    let (one, one_statistics) = match solve_one_with_options(system, &mut rng, &options) {
        Ok(result) => result,
        Err(e) => return Outcome::Failed(e.to_string()),
    };
    let first = millis(at.elapsed());

    let Some(point) = one else {
        return Outcome::NoBaseFieldPoint { millis: first };
    };

    // The point is checked against the polynomials as given, not against any basis derived from
    // them. The solver asserts this too; doing it here as well is the demonstration's whole claim.
    for p in system {
        assert!(
            p.eval(&point).is_zero(),
            "the returned point does not satisfy {}",
            p
        );
    }

    let at = Instant::now();
    let (all, all_statistics) =
        match solve_zero_dimensional_with_options(system, &mut rng, &options) {
            Ok(result) => result,
            Err(e) => return Outcome::Failed(e.to_string()),
        };
    let every = millis(at.elapsed());

    Outcome::Solved {
        first,
        all: every,
        count: all.len(),
        first_branches: one_statistics.branches,
        all_branches: all_statistics.branches,
    }
}

fn report<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>], seed: u64) {
    for (label, strategy) in [
        ("direct", SolveStrategy::DirectLexF4),
        ("fglm", SolveStrategy::GrevlexF4ThenFglm),
    ] {
        let outcome = attempt(system, strategy, seed);
        println!(
            "| {:<11} | {:<6} | {:>11} | {:>11} | {:>15} | {:<34} |",
            name,
            label,
            outcome.first(),
            outcome.all(),
            outcome.branches(),
            outcome.verdict(),
        );
    }
}

fn header() {
    println!(
        "| {:<11} | {:<6} | {:>11} | {:>11} | {:>15} | {:<34} |",
        "system", "route", "first ms", "all ms", "branches 1/all", "result"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(8),
        "-".repeat(13),
        "-".repeat(13),
        "-".repeat(17),
        "-".repeat(36)
    );
}

fn main() {
    println!("# Solving zero-dimensional systems over GF(2^31 - 1), by both routes");
    println!();
    header();

    // A planted point, recovered from equations that do not state it.
    let point: Vec<F> = (0..6).map(|i| F::new(2 * i as u64 + 3)).collect();
    report("planted-6", &planted::<6, F>(&point), 1);

    report("cyclic-3", &cyclic::<3, F>(), 2);
    report("katsura-3", &katsura::<3, F>(), 3);
    report("katsura-4", &katsura::<4, F>(), 4);
    report("katsura-5", &katsura::<5, F>(), 5);
    report("katsura-6", &katsura::<6, F>(), 6);
    report("katsura-7", &katsura::<7, F>(), 7);

    // The failure in the other direction. The planted family's quotient dimension is 4^(N/2), so
    // it outgrows the conversion while its lex basis stays trivial.
    let point: Vec<F> = (0..10).map(|i| F::new(2 * i as u64 + 3)).collect();
    report("planted-10", &planted::<10, F>(&point), 8);
    let point: Vec<F> = (0..12).map(|i| F::new(2 * i as u64 + 3)).collect();
    report("planted-12", &planted::<12, F>(&point), 9);
    let point: Vec<F> = (0..14).map(|i| F::new(2 * i as u64 + 3)).collect();
    report("planted-14", &planted::<14, F>(&point), 10);

    println!();
    println!("`branches 1/all` is candidate assignments charged, which separates the search's");
    println!("own cost from the Gröbner basis in front of it.");
    println!();
    println!("`first ms` is time to one point, `all ms` to every distinct point. The two are");
    println!("close on most rows because the Gröbner basis dominates and the search is almost");
    println!("free; planted-6 is where they part, at 64 points.");
    println!();
    println!("The planted point for planted-6 is (3, 5, 7, 9, 11, 13), which appears nowhere in");
    println!("the equations; every returned point is verified against them.");
    println!();
    println!("Neither route dominates. The conversion is the only one that solves katsura-7, and");
    println!("the only one that fails on planted-12 and planted-14. It is also faster on");
    println!("katsura-6. `DirectLexF4` is the default because it is the conservative choice, not");
    println!("because it is uniformly better.");
}
