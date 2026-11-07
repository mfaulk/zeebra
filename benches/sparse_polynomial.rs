//! Sparse multivariate polynomial arithmetic.
//!
//! Addition, multiplication, multiplication by a monomial, and reduction to normal form against a
//! set of reducers. These are the operations inside Gröbner reduction, so their constant factors
//! set the floor on Buchberger performance.
//!
//! `N` is a const generic, so each variable count needs its own instantiation.

use std::collections::HashMap;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::Zp2147483647, FiniteField, Monomial, MonomialOrder, MultivariatePolynomial, Zero,
};

type F = Zp2147483647;
const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// A polynomial with exactly `terms` distinct monomials, exponents bounded by `max_exponent`.
///
/// Sampling monomials independently and letting duplicates merge makes the term count a function
/// of the arity: with N = 3 and exponents bounded by 4 there are only 5^3 = 125 monomials to draw
/// from, so asking for 256 terms yielded 116 and the benchmark label overstated the input by more
/// than a factor of two. Drawing until the target number of *distinct* monomials is reached keeps
/// the label honest and the arities comparable to each other.
fn random_poly<const N: usize>(
    terms: usize,
    max_exponent: u32,
    rng: &mut StdRng,
) -> MultivariatePolynomial<N, F> {
    let available = (max_exponent as u64 + 1).pow(N as u32);
    assert!(
        (terms as u64) <= available,
        "{terms} distinct monomials requested but only {available} exist for {N} variables with \
         exponents at most {max_exponent}"
    );

    let mut drawn: HashMap<Monomial<N>, F> = HashMap::with_capacity(terms);
    while drawn.len() < terms {
        let exponents: Vec<u32> = (0..N).map(|_| rng.gen_range(0..=max_exponent)).collect();
        // A repeat draw is discarded rather than merged, so the count is exact.
        drawn.entry(Monomial::new(&exponents)).or_insert_with(|| {
            let mut coefficient = F::random(rng);
            // A zero coefficient would be dropped on construction, undoing the exact count.
            while coefficient.is_zero() {
                coefficient = F::random(rng);
            }
            coefficient
        });
    }

    let terms: Vec<(Monomial<N>, F)> = drawn.into_iter().collect();
    MultivariatePolynomial::new(&terms)
}

/// The smallest exponent bound admitting `terms` distinct monomials in N variables, at least 4.
///
/// Fixed per arity rather than per size, so that the exponent distribution does not vary between
/// the sizes being compared. Only the low arities need more than 4: N = 3 has just 5^3 = 125
/// monomials within that bound, fewer than the largest size benchmarked.
fn exponent_bound<const N: usize>(terms: usize) -> u32 {
    let mut bound = 4u32;
    while (bound as u64 + 1).pow(N as u32) < terms as u64 {
        bound += 1;
    }
    bound
}

/// The dense total-degree simplex of `degree` in N variables, every coefficient nonzero.
///
/// The shape the symbolic Groebner build actually produces, and the one the specialised
/// bivariate route is selected for: `cico_bivariate`'s six-round outputs are the dense triangle
/// `(729+1)(729+2)/2` with no cancellation anywhere. [`random_poly`]'s independent monomial draws
/// are sparse in the total-degree sense at every size, so a benchmark built only out of them never
/// reaches that route.
fn dense_simplex<const N: usize>(degree: u32, rng: &mut StdRng) -> MultivariatePolynomial<N, F> {
    let mut exponents = [0u32; N];
    let mut terms: Vec<(Monomial<N>, F)> = Vec::new();
    fill_simplex::<N>(0, degree, &mut exponents, &mut terms, rng);
    MultivariatePolynomial::new(&terms)
}

/// The largest total degree whose dense N-variable simplex has at most `terms` terms.
///
/// At least 1, so that an arity too large for the target still produces something to multiply.
fn simplex_degree<const N: usize>(terms: usize) -> u32 {
    let mut degree = 1u32;
    while simplex_len::<N>(degree + 1) <= terms as u128 {
        degree += 1;
    }
    degree
}

/// `C(degree + N, N)`, the number of monomials of total degree at most `degree` in N variables.
fn simplex_len<const N: usize>(degree: u32) -> u128 {
    let mut count: u128 = 1;
    for i in 1..=(N as u128) {
        count = count * (degree as u128 + i) / i;
    }
    count
}

/// Enumerate the exponent vectors of total degree at most `remaining` over variables `index..N`.
fn fill_simplex<const N: usize>(
    index: usize,
    remaining: u32,
    exponents: &mut [u32; N],
    terms: &mut Vec<(Monomial<N>, F)>,
    rng: &mut StdRng,
) {
    if index == N {
        let mut coefficient = F::random(rng);
        // A zero coefficient would be dropped on construction, undoing the density.
        while coefficient.is_zero() {
            coefficient = F::random(rng);
        }
        terms.push((Monomial::new(exponents), coefficient));
        return;
    }
    for e in 0..=remaining {
        exponents[index] = e;
        fill_simplex::<N>(index + 1, remaining - e, exponents, terms, rng);
    }
    exponents[index] = 0;
}

fn bench_arity<const N: usize>(c: &mut Criterion, arity: &str) {
    let mut group = c.benchmark_group("sparse_poly");

    const SIZES: [usize; 3] = [16, 64, 256];
    let max_exponent = exponent_bound::<N>(SIZES[SIZES.len() - 1]);

    for terms in SIZES {
        let mut rng = StdRng::seed_from_u64(11);
        let a = random_poly::<N>(terms, max_exponent, &mut rng);
        let b = random_poly::<N>(terms, max_exponent, &mut rng);

        group.bench_with_input(
            BenchmarkId::new(format!("add/{}", arity), terms),
            &(&a, &b),
            |bencher, (a, b)| bencher.iter(|| black_box(black_box(*a) + black_box(*b))),
        );

        group.bench_with_input(
            BenchmarkId::new(format!("sub/{}", arity), terms),
            &(&a, &b),
            |bencher, (a, b)| bencher.iter(|| black_box(black_box(*a) - black_box(*b))),
        );

        // The in-place spellings, which #361 made genuinely mutate rather than assign a freshly
        // built sum. Benchmarked beside `add` and `sub` rather than instead of them: the borrowed
        // operator still has to clone one side, so the two are different operations and the gap
        // between them is the whole of what the in-place form buys a caller that owns its
        // accumulator — `div_rem`'s `working -= &q * divisor` and the symbolic MDS fold.
        group.bench_with_input(
            BenchmarkId::new(format!("add_assign/{}", arity), terms),
            &(&a, &b),
            |bencher, (a, b)| {
                bencher.iter_batched_ref(
                    || (*a).clone(),
                    |accumulator| *accumulator += black_box(*b),
                    criterion::BatchSize::SmallInput,
                )
            },
        );

        group.bench_with_input(
            BenchmarkId::new(format!("sub_assign/{}", arity), terms),
            &(&a, &b),
            |bencher, (a, b)| {
                bencher.iter_batched_ref(
                    || (*a).clone(),
                    |accumulator| *accumulator -= black_box(*b),
                    criterion::BatchSize::SmallInput,
                )
            },
        );

        // Scaling is the MDS layer's other operation, once per word per round.
        let factor = F::new(7);
        group.bench_with_input(
            BenchmarkId::new(format!("scale/{}", arity), terms),
            &(&a, &factor),
            |bencher, (a, factor)| bencher.iter(|| black_box(black_box(*a).scale(factor))),
        );

        group.bench_with_input(
            BenchmarkId::new(format!("scale_assign/{}", arity), terms),
            &(&a, &factor),
            |bencher, (a, factor)| {
                bencher.iter_batched_ref(
                    || (*a).clone(),
                    |scaled| scaled.scale_assign(factor),
                    criterion::BatchSize::SmallInput,
                )
            },
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

    // Two sizes past the arms above, which top out at 256 x 256 = 65 536 term-products — about a
    // megabyte of transient, four orders below the regime #243 is about. The dense-output shape is
    // also what selects the specialised bivariate route, so this is the arm that regresses if that
    // route's dispatch predicate is wrong.
    //
    // Sized by term count rather than by degree, because a fixed degree is a wildly different size
    // at each arity: the simplex of degree 16 is 153 terms at N = 2 and 5.3 million at N = 10.
    for target in [1024usize, 4096] {
        let mut rng = StdRng::seed_from_u64(29);
        let degree = simplex_degree::<N>(target);
        let a = dense_simplex::<N>(degree, &mut rng);
        let b = dense_simplex::<N>(degree, &mut rng);
        let products = a.terms().len() * b.terms().len();
        // Hundreds of milliseconds a sample; the point of the arm is the shape and the size, not a
        // tight interval.
        group.sample_size(10);
        group.bench_with_input(
            BenchmarkId::new(format!("mul_dense/{}", arity), products),
            &(&a, &b),
            |bencher, (a, b)| bencher.iter(|| black_box(black_box(*a) * black_box(*b))),
        );
    }

    // The symbolic permutation's MDS layer: fold the scaled state words into one accumulator. The
    // shape #361 is about, and the one where the in-place forms compound rather than each saving a
    // constant — the allocating `Add` rebuilt the whole accumulator at every one of the steps, and
    // `scale` round-tripped each word through a `Vec`.
    {
        const WORDS: usize = 8;
        let mut rng = StdRng::seed_from_u64(37);
        let degree = simplex_degree::<N>(512);
        let state: Vec<MultivariatePolynomial<N, F>> = (0..WORDS)
            .map(|_| dense_simplex::<N>(degree, &mut rng))
            .collect();
        let row: Vec<F> = (0..WORDS).map(|w| F::new(3 + w as u64)).collect();

        group.sample_size(20);
        group.bench_with_input(
            BenchmarkId::new(format!("mds_fold/{}", arity), WORDS),
            &(&row, &state),
            |bencher, (row, state)| {
                bencher.iter(|| {
                    black_box(
                        row.iter()
                            .zip(state.iter())
                            .fold(MultivariatePolynomial::<N, F>::zero(), |acc, (m, word)| {
                                acc + word.scale(m)
                            }),
                    )
                })
            },
        );
    }

    // Normal form against a set of reducers, which is what Gröbner reduction spends its time on.
    for reducer_count in [2usize, 4, 8] {
        let mut rng = StdRng::seed_from_u64(23);
        // `exponent_bound` rather than a literal 4: at N = 2 only 5^2 = 25 monomials fit within
        // that bound and this asks for 48, so the literal made `random_poly`'s own assert fire.
        // The bound is unchanged at N = 3, where 5^3 = 125 already admits 48, so no recorded
        // figure moves — N = 2 is the arity that had no figure because it panicked.
        let dividend = random_poly::<N>(48, exponent_bound::<N>(48), &mut rng);
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
                bencher.iter(|| black_box(black_box(*dividend).normal_form(reducers, ORDER)))
            },
        );

        // The same reduction through `multi_div_rem`, which also returns quotients. Kept as a
        // measured comparison: `normal_form` exists because this path is quadratic in the number
        // of reduction steps, and the gap widens with the size of the dividend.
        group.bench_with_input(
            BenchmarkId::new(format!("multi_div_rem/{}", arity), reducer_count),
            &(&dividend, &reducers),
            |bencher, (dividend, reducers)| {
                bencher.iter(|| black_box(black_box(*dividend).multi_div_rem(reducers, ORDER).1))
            },
        );
    }

    group.finish();
}

fn benches(c: &mut Criterion) {
    // N = 2 because it is the arity the symbolic resultant build runs at and the one the
    // dense-triangle route is written for; the file had no bivariate arm before #243.
    bench_arity::<2>(c, "n2");
    bench_arity::<3>(c, "n3");
    bench_arity::<6>(c, "n6");
    bench_arity::<10>(c, "n10");
}

criterion_group!(sparse_polynomial, benches);
criterion_main!(sparse_polynomial);
