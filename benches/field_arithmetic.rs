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
        batch_invert, Bls12_381Fr, Bn254Fr, Mersenne31, PrimeFieldElement64, Proth68Fr,
        Zp18446744073709551557, Zp2147483647,
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

    // Montgomery's trick over the same operands as `isolated/inverse`: one inversion and
    // `3(n-1)` multiplications against n inversions. The two are directly comparable because the
    // operand set is identical, and the ratio between them is the whole case for `batch_inverse`.
    // The clone is inside the measurement because the in-place routine needs to own its input;
    // `isolated/inverse` does not clone, so this is charged the copy and still has to win.
    group.bench_with_input(
        BenchmarkId::new("batch/inverse", name),
        &nonzero,
        |bencher, values| {
            bencher.iter(|| {
                let mut owned = values.to_vec();
                batch_invert(black_box(&mut owned));
                black_box(owned);
            })
        },
    );

    group.finish();
}

/// 3 * 2^66 + 1, a 68-bit Proth prime, over the deprecated 128-bit field.
///
/// Kept after that type's deprecation (#163) so the cost of its dividing multiply stays visible
/// next to `p68_mont`, which is the same field over `PrimeFieldElement256`.
#[allow(deprecated)]
type Zp128 = zeebra::fields::PrimeFieldElement128<221360928884514619393>;

/// KoalaBear, `2^31 - 2^24 + 1`, in a `u64` — the NTT sweep's own storage width.
///
/// `examples/ntt_access.rs` measures its own multiply rate in-run and quotes this arm beside it, so
/// the two have to be the same field in the same number of bytes or the comparison is of two
/// different things. `docs/research/graeffe-root-finding.md` §6.3.
type KoalaBearIn64 = PrimeFieldElement64<2_130_706_433>;

/// Goldilocks, `2^64 - 2^32 + 1`.
///
/// The one field in the NTT sweep whose two-adicity lets a radix-2 coefficient array leave this
/// box's 256 MB L3 at a reachable size, which is why the access-bound question is asked over it
/// (`docs/research/graeffe-root-finding.md` §6.2). `p64` is a *different* 64-bit prime with a
/// two-adicity of 2, so it cannot stand in for this one.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

fn benches(c: &mut Criterion) {
    bench_field::<Zp2147483647>(c, "p31");
    // The same modulus in four bytes rather than eight: `p31` against `p31_u32` is the storage
    // width alone, with the field held fixed.
    bench_field::<Mersenne31>(c, "p31_u32");
    bench_field::<Zp18446744073709551557>(c, "p64");
    // The two NTT-friendly fields `examples/ntt_access.rs` sweeps. Neither was measurable here
    // before: `p31`/`p31_u32` are the Mersenne-31 modulus and `p64` is a 64-bit prime with
    // two-adicity 2, so an NTT comparand had to come from outside this bench.
    bench_field::<KoalaBearIn64>(c, "p31_koalabear");
    bench_field::<Goldilocks>(c, "p64_goldilocks");
    bench_field::<Zp128>(c, "p68");
    // The same 68-bit modulus as two limbs of a `PrimeModulus256`. `p68` against `p68_mont` is
    // the representation alone, with the field held fixed — the measurement #163 turns on.
    bench_field::<Proth68Fr>(c, "p68_mont");
    // The cryptographic scalar fields. Named by width so the ordering in the report matches the
    // ordering of the moduli.
    bench_field::<Bn254Fr>(c, "p254_bn254");
    bench_field::<Bls12_381Fr>(c, "p255_bls12_381");
}

criterion_group!(field_arithmetic, benches);
criterion_main!(field_arithmetic);
