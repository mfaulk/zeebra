//! Sparse multivariate polynomial arithmetic.
//!
//! Addition, multiplication, multiplication by a monomial, and reduction to normal form against a
//! set of reducers. These are the operations inside Gröbner reduction, so their constant factors
//! set the floor on Buchberger performance.
//!
//! `N` is a const generic, so each variable count needs its own instantiation.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{fields::Zp2147483647, FiniteField, Monomial, MonomialOrder, MultivariatePolynomial};

type F = Zp2147483647;
const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// A polynomial with roughly `terms` terms, exponents bounded by `max_exponent`.
fn random_poly<const N: usize>(
    terms: usize,
    max_exponent: u32,
    rng: &mut StdRng,
) -> MultivariatePolynomial<N, F> {
    let drawn: Vec<(Monomial<N>, F)> = (0..terms)
        .map(|_| {
            let exponents: Vec<u32> = (0..N).map(|_| rng.gen_range(0..=max_exponent)).collect();
            (Monomial::new(&exponents), F::random(rng))
        })
        .collect();
    MultivariatePolynomial::new(&drawn)
}

fn bench_arity<const N: usize>(c: &mut Criterion, arity: &str) {
    let mut group = c.benchmark_group("sparse_poly");

    for terms in [16usize, 64, 256] {
        let mut rng = StdRng::seed_from_u64(11);
        let a = random_poly::<N>(terms, 4, &mut rng);
        let b = random_poly::<N>(terms, 4, &mut rng);

        group.bench_with_input(
            BenchmarkId::new(format!("add/{}", arity), terms),
            &(&a, &b),
            |bencher, (a, b)| bencher.iter(|| black_box(black_box(*a) + black_box(*b))),
        );

        group.bench_with_input(
            BenchmarkId::new(format!("mul/{}", arity), terms),
            &(&a, &b),
            |bencher, (a, b)| bencher.iter(|| black_box(black_box(*a) * black_box(*b))),
        );

        // Multiplication by a single term is the inner operation of every reduction step.
        let exponents: Vec<u32> = (0..N).map(|i| (i as u32) % 3).collect();
        let single: MultivariatePolynomial<N, F> =
            MultivariatePolynomial::new(&[(Monomial::<N>::new(&exponents), F::new(7))]);
        group.bench_with_input(
            BenchmarkId::new(format!("mul_by_term/{}", arity), terms),
            &(&a, &single),
            |bencher, (a, t)| bencher.iter(|| black_box(black_box(*a) * black_box(*t))),
        );
    }

    // Normal form against a set of reducers, which is what Gröbner reduction spends its time on.
    for reducer_count in [2usize, 4, 8] {
        let mut rng = StdRng::seed_from_u64(23);
        let dividend = random_poly::<N>(48, 4, &mut rng);
        let reducers: Vec<MultivariatePolynomial<N, F>> = (0..reducer_count)
            .map(|_| random_poly::<N>(8, 3, &mut rng))
            .filter(|p| !p.is_zero())
            .collect();

        // Reduction is far slower than the other operations, so it gets fewer samples.
        group.sample_size(20);
        group.bench_with_input(
            BenchmarkId::new(format!("normal_form/{}", arity), reducer_count),
            &(&dividend, &reducers),
            |bencher, (dividend, reducers)| {
                bencher.iter(|| black_box(black_box(*dividend).multi_div_rem(reducers, ORDER).1))
            },
        );
    }

    group.finish();
}

fn benches(c: &mut Criterion) {
    bench_arity::<3>(c, "n3");
    bench_arity::<6>(c, "n6");
    bench_arity::<10>(c, "n10");
}

criterion_group!(sparse_polynomial, benches);
criterion_main!(sparse_polynomial);
