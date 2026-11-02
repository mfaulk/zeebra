//! Gröbner basis computation.
//!
//! The cyclic and Katsura families from `zeebra::grobner::benchmark_systems`, plus deterministic
//! random and planted-solution systems. Instances are chosen to finish in seconds: the purpose is
//! a reliable baseline, not a record.
//!
//! `N` is a const generic, so each instance size is a separate instantiation.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        buchberger,
    },
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

const ORDERS: [MonomialOrder; 3] = [
    MonomialOrder::Lexicographic,
    MonomialOrder::GradedLexicographic,
    MonomialOrder::GradedReverseLexicographic,
];

/// A deterministic random system: N quadratics in N variables.
fn random_system<const N: usize>(seed: u64) -> Vec<MultivariatePolynomial<N, F>> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..N)
        .map(|_| {
            let terms: Vec<(Monomial<N>, F)> = (0..2 * N)
                .map(|_| {
                    let mut exponents = [0u32; N];
                    // Degree at most two, so the system stays tractable.
                    exponents[rng.gen_range(0..N)] += 1;
                    if rng.gen_bool(0.5) {
                        exponents[rng.gen_range(0..N)] += 1;
                    }
                    (Monomial::new(&exponents), F::random(&mut rng))
                })
                .collect();
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

/// A deterministic point to plant a solution at.
fn planted_point<const N: usize>(seed: u64) -> Vec<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..N).map(|_| F::random(&mut rng)).collect()
}

fn bench_family<const N: usize>(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    label: &str,
    system: Vec<MultivariatePolynomial<N, F>>,
) {
    for order in ORDERS {
        group.bench_with_input(
            BenchmarkId::new(format!("{}/{}", label, order.name()), N),
            &system,
            |bencher, system| bencher.iter(|| black_box(buchberger(black_box(system), order))),
        );
    }
}

fn benches(c: &mut Criterion) {
    let mut group = c.benchmark_group("grobner");
    // Buchberger on these systems is slow enough that the default sample size would take minutes.
    group.sample_size(10);

    bench_family::<3>(&mut group, "cyclic", cyclic::<3, F>());
    bench_family::<4>(&mut group, "cyclic", cyclic::<4, F>());
    bench_family::<3>(&mut group, "katsura", katsura::<3, F>());
    bench_family::<4>(&mut group, "katsura", katsura::<4, F>());
    bench_family::<5>(&mut group, "katsura", katsura::<5, F>());
    bench_family::<3>(&mut group, "random", random_system::<3>(5));
    bench_family::<4>(&mut group, "random", random_system::<4>(5));
    let point = planted_point::<6>(9);
    bench_family::<6>(&mut group, "planted", planted::<6, F>(&point));

    group.finish();
}

criterion_group!(grobner, benches);
criterion_main!(grobner);
