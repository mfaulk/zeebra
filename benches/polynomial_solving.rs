//! Solving zero-dimensional systems: one solution against all of them, by both routes.
//!
//! Two groups.
//!
//! `time_to_first` times `solve_one`, which stops at the first complete point. `time_to_all` times
//! `solve_zero_dimensional`, which enumerates every distinct one. The gap is the whole case for
//! having two entry points, and it grows with the solution count rather than with the system:
//! §10.3 of `docs/MILESTONE-FGLM-SOLVING.md` measures it at 830x on a system with 16384 solutions,
//! where time to the first point barely moves.
//!
//! Both groups run under both strategies wherever both can finish, which is not everywhere.
//! katsura-7 is solvable only by conversion — its lex basis crosses F4's default limits — and
//! planted-12 is solvable only directly, since its quotient algebra is too large to build. Each
//! instance is registered under the strategies that can do it, so an absent bar is a capability
//! difference rather than an omission.
//!
//! The RNG is seeded per iteration, so a run is reproducible: `roots` is randomized, and which
//! solution `solve_one` reaches depends on it.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        solve_one_with_options, solve_zero_dimensional_with_options, SolveOptions, SolveStrategy,
    },
    FiniteField, MultivariatePolynomial,
};

type F = Zp2147483647;

/// The seed every iteration starts from, so the search explores the same tree each time.
const SEED: u64 = 20_250_101;

fn planted_point<const N: usize>() -> Vec<F> {
    (0..N).map(|i| F::new(2 * i as u64 + 3)).collect()
}

fn label(strategy: SolveStrategy) -> &'static str {
    match strategy {
        SolveStrategy::DirectLexF4 => "direct",
        SolveStrategy::GrevlexF4ThenFglm => "fglm",
    }
}

/// Register one instance under one strategy, in both groups, if that strategy can solve it.
///
/// Checked once outside the timed region. A strategy that cannot finish the instance at the
/// default limits is skipped rather than timed as a failure.
fn bench_instance<const N: usize>(
    c: &mut Criterion,
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    strategy: SolveStrategy,
) {
    let options = SolveOptions::with_strategy(strategy);
    let mut probe = StdRng::seed_from_u64(SEED);
    if solve_one_with_options(system, &mut probe, &options).is_err() {
        return;
    }

    let id = BenchmarkId::new(label(strategy), name);

    let mut group = c.benchmark_group("time_to_first");
    group.bench_with_input(id.clone(), system, |b, s| {
        b.iter(|| {
            let mut rng = StdRng::seed_from_u64(SEED);
            solve_one_with_options(black_box(s), &mut rng, &options).expect("solvable");
        })
    });
    group.finish();

    let mut group = c.benchmark_group("time_to_all");
    group.bench_with_input(id, system, |b, s| {
        b.iter(|| {
            let mut rng = StdRng::seed_from_u64(SEED);
            solve_zero_dimensional_with_options(black_box(s), &mut rng, &options)
                .expect("solvable");
        })
    });
    group.finish();
}

fn both<const N: usize>(c: &mut Criterion, name: &str, system: &[MultivariatePolynomial<N, F>]) {
    bench_instance(c, name, system, SolveStrategy::DirectLexF4);
    bench_instance(c, name, system, SolveStrategy::GrevlexF4ThenFglm);
}

fn solving(c: &mut Criterion) {
    both(c, "cyclic-3", &cyclic::<3, F>());
    both(c, "katsura-4", &katsura::<4, F>());
    both(c, "katsura-5", &katsura::<5, F>());
    both(c, "katsura-6", &katsura::<6, F>());
    // Only the conversion reaches this one.
    both(c, "katsura-7", &katsura::<7, F>());

    // The planted family: the solution count is its quotient dimension, 4^(N/2), so this is where
    // one solution and all of them come apart. Only the direct route reaches planted-12.
    both(c, "planted-6", &planted::<6, F>(&planted_point::<6>()));
    both(c, "planted-8", &planted::<8, F>(&planted_point::<8>()));
    both(c, "planted-10", &planted::<10, F>(&planted_point::<10>()));
    both(c, "planted-12", &planted::<12, F>(&planted_point::<12>()));
}

criterion_group!(polynomial_solving, solving);
criterion_main!(polynomial_solving);
