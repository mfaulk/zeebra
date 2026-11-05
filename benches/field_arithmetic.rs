//! Prime field arithmetic.
//!
//! Four widths spanning the sizes the project cares about: a 31-bit Mersenne prime held in a
//! `u32` and in a `u64`, the largest 64-bit prime, and a 68-bit prime held in a `u128`. The
//! middle two share an implementation and differ only in operand size; `p31_u32` is the same
//! modulus as `p31` over a separate 4-byte type, so the pair isolates storage width at a fixed
//! field; the last exercises the separate 128-bit type.
//!
//! Operands are drawn in advance and the loop consumes them in order, so the measurement covers
//! the arithmetic and not the generation.
//!
//! Each operation is measured two ways, because neither alone is sufficient:
//!
//! - `<op>` accumulates into a running total, which creates a dependency chain and so reports
//!   latency — but each sample also includes one addition, so it measures a fused `acc += x op y`
//!   rather than the named operation. Improvements to addition show up in every one of these.
//! - `isolated/<op>` discards each result through `black_box`, so the operation is measured on its
//!   own at the cost of including the `black_box` barrier and loop overhead. Successive iterations
//!   are independent, so this reports throughput rather than latency.
//!
//! Compare like with like across runs; do not read a change in one as a change in the other.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{
        Bls12_381Fr, Bn254Fr, Mersenne31, PrimeFieldElement128, Zp18446744073709551557,
        Zp2147483647,
    },
    FiniteField,
};

/// Enough operands that the sequence does not sit in a single cache line, few enough to stay hot.
const OPERANDS: usize = 256;

fn operands<F: FiniteField>(seed: u64) -> Vec<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..OPERANDS).map(|_| F::random(&mut rng)).collect()
}

/// Nonzero operands, for the inversion benchmark.
fn nonzero_operands<F: FiniteField>(seed: u64) -> Vec<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut values = Vec::with_capacity(OPERANDS);
    while values.len() < OPERANDS {
        let candidate = F::random(&mut rng);
        if !candidate.is_zero() {
            values.push(candidate);
        }
    }
    values
}

fn bench_field<F: FiniteField>(c: &mut Criterion, name: &str) {
    let a = operands::<F>(1);
    let b = operands::<F>(2);
    let nonzero = nonzero_operands::<F>(3);

    let mut group = c.benchmark_group("field");

    group.bench_with_input(
        BenchmarkId::new("mul", name),
        &(&a, &b),
        |bencher, (a, b)| {
            bencher.iter(|| {
                let mut acc = F::zero();
                for (x, y) in a.iter().zip(b.iter()) {
                    acc += *black_box(x) * *black_box(y);
                }
                black_box(acc)
            })
        },
    );

    group.bench_with_input(
        BenchmarkId::new("add", name),
        &(&a, &b),
        |bencher, (a, b)| {
            bencher.iter(|| {
                let mut acc = F::zero();
                for (x, y) in a.iter().zip(b.iter()) {
                    acc += *black_box(x) + *black_box(y);
                }
                black_box(acc)
            })
        },
    );

    group.bench_with_input(
        BenchmarkId::new("sub", name),
        &(&a, &b),
        |bencher, (a, b)| {
            bencher.iter(|| {
                let mut acc = F::zero();
                for (x, y) in a.iter().zip(b.iter()) {
                    acc += *black_box(x) - *black_box(y);
                }
                black_box(acc)
            })
        },
    );

    group.bench_with_input(
        BenchmarkId::new("inverse", name),
        &nonzero,
        |bencher, values| {
            bencher.iter(|| {
                let mut acc = F::zero();
                for x in values.iter() {
                    acc += black_box(x).inverse();
                }
                black_box(acc)
            })
        },
    );

    // Isolated variants: one operation per sample, no accumulating addition.
    group.bench_with_input(
        BenchmarkId::new("isolated/mul", name),
        &(&a, &b),
        |bencher, (a, b)| {
            bencher.iter(|| {
                for (x, y) in a.iter().zip(b.iter()) {
                    black_box(*black_box(x) * *black_box(y));
                }
            })
        },
    );

    group.bench_with_input(
        BenchmarkId::new("isolated/add", name),
        &(&a, &b),
        |bencher, (a, b)| {
            bencher.iter(|| {
                for (x, y) in a.iter().zip(b.iter()) {
                    black_box(*black_box(x) + *black_box(y));
                }
            })
        },
    );

    group.bench_with_input(
        BenchmarkId::new("isolated/sub", name),
        &(&a, &b),
        |bencher, (a, b)| {
            bencher.iter(|| {
                for (x, y) in a.iter().zip(b.iter()) {
                    black_box(*black_box(x) - *black_box(y));
                }
            })
        },
    );

    group.bench_with_input(
        BenchmarkId::new("isolated/inverse", name),
        &nonzero,
        |bencher, values| {
            bencher.iter(|| {
                for x in values.iter() {
                    black_box(black_box(x).inverse());
                }
            })
        },
    );

    group.finish();
}

/// 3 * 2^66 + 1, a 68-bit Proth prime.
type Zp128 = PrimeFieldElement128<221360928884514619393>;

fn benches(c: &mut Criterion) {
    bench_field::<Zp2147483647>(c, "p31");
    // The same modulus in four bytes rather than eight: `p31` against `p31_u32` is the storage
    // width alone, with the field held fixed.
    bench_field::<Mersenne31>(c, "p31_u32");
    bench_field::<Zp18446744073709551557>(c, "p64");
    bench_field::<Zp128>(c, "p68");
    // The cryptographic scalar fields. Named by width so the ordering in the report matches the
    // ordering of the moduli.
    bench_field::<Bn254Fr>(c, "p254_bn254");
    bench_field::<Bls12_381Fr>(c, "p255_bls12_381");
}

criterion_group!(field_arithmetic, benches);
criterion_main!(field_arithmetic);
