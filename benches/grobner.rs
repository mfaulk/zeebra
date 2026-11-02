//! Gröbner basis computation: Buchberger against F4 on identical inputs.
//!
//! The cyclic and Katsura families from `zeebra::grobner::benchmark_systems`, plus deterministic
//! random and planted-solution systems. Every instance is run through both engines under the same
//! monomial order, so the two figures are directly comparable; a reduced Gröbner basis is unique,
//! so they are computing the same answer.
//!
//! The `paired` group holds the instances both engines finish in seconds. The `f4_only` group
//! holds instances Buchberger cannot: they are the point of the milestone, and leaving them out
//! would understate it while putting Buchberger in them would hang the suite.
//!
//! `N` is a const generic, so each instance size is a separate instantiation.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        buchberger, f4,
    },
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

const ORDERS: [MonomialOrder; 3] = [
    MonomialOrder::Lexicographic,
    MonomialOrder::GradedLexicographic,
    MonomialOrder::GradedReverseLexicographic,
];

const GRADED: [MonomialOrder; 2] = [
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

/// Both engines on the same system, under each of `orders`.
fn bench_paired<const N: usize>(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    label: &str,
    system: Vec<MultivariatePolynomial<N, F>>,
    orders: &[MonomialOrder],
) {
    for &order in orders {
        group.bench_with_input(
            BenchmarkId::new(format!("buchberger/{}/{}", label, order.name()), N),
            &system,
            |bencher, system| bencher.iter(|| black_box(buchberger(black_box(system), order))),
        );
        group.bench_with_input(
            BenchmarkId::new(format!("f4/{}/{}", label, order.name()), N),
            &system,
            |bencher, system| {
                bencher.iter(|| black_box(f4(black_box(system), order).expect("within limits")))
            },
        );
    }
}

/// F4 alone, on instances Buchberger cannot finish here.
fn bench_f4_only<const N: usize>(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    label: &str,
    system: Vec<MultivariatePolynomial<N, F>>,
    orders: &[MonomialOrder],
) {
    for &order in orders {
        group.bench_with_input(
            BenchmarkId::new(format!("f4/{}/{}", label, order.name()), N),
            &system,
            |bencher, system| {
                bencher.iter(|| black_box(f4(black_box(system), order).expect("within limits")))
            },
        );
    }
}

fn paired(c: &mut Criterion) {
    let mut group = c.benchmark_group("grobner");
    // Buchberger on these systems is slow enough that the default sample size would take minutes.
    group.sample_size(10);

    bench_paired::<3>(&mut group, "cyclic", cyclic::<3, F>(), &ORDERS);
    bench_paired::<4>(&mut group, "cyclic", cyclic::<4, F>(), &ORDERS);
    bench_paired::<5>(&mut group, "cyclic", cyclic::<5, F>(), &ORDERS);
    bench_paired::<3>(&mut group, "katsura", katsura::<3, F>(), &ORDERS);
    bench_paired::<4>(&mut group, "katsura", katsura::<4, F>(), &ORDERS);
    bench_paired::<5>(&mut group, "katsura", katsura::<5, F>(), &ORDERS);
    // katsura-6 under lex is in `f4_only`: Buchberger does not finish it here.
    bench_paired::<6>(&mut group, "katsura", katsura::<6, F>(), &GRADED);
    bench_paired::<3>(&mut group, "random", random_system::<3>(5), &ORDERS);
    bench_paired::<4>(&mut group, "random", random_system::<4>(5), &ORDERS);
    let point = planted_point::<6>(9);
    bench_paired::<6>(&mut group, "planted", planted::<6, F>(&point), &ORDERS);
    let point = planted_point::<8>(9);
    bench_paired::<8>(&mut group, "planted", planted::<8, F>(&point), &ORDERS);

    group.finish();
}

fn f4_only(c: &mut Criterion) {
    let mut group = c.benchmark_group("grobner_f4_only");
    group.sample_size(10);

    bench_f4_only::<6>(
        &mut group,
        "katsura",
        katsura::<6, F>(),
        &[MonomialOrder::Lexicographic],
    );
    bench_f4_only::<7>(&mut group, "katsura", katsura::<7, F>(), &GRADED);

    group.finish();
}

criterion_group!(grobner, paired, f4_only);
criterion_main!(grobner);
