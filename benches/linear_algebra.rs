//! Dense finite-field linear algebra.
//!
//! Gaussian elimination and Gauss–Jordan elimination at several sizes, over a 31-bit prime at two
//! storage widths and a 64-bit prime. These drive the pivot-normalization path, which is the clearest arithmetic bottleneck
//! identified in the milestone review: one modular inverse per entry rather than per row.
//!
//! Also the matrix product, at square sizes and at a family of rectangular shapes that holds the
//! multiplication count fixed while sweeping the right operand's footprint across the cache
//! hierarchy — the product's loop order decides how that operand is walked.
//!
//! Matrices are generated in advance from a fixed seed, so the same matrices are reused across
//! runs and sizes are comparable between before and after measurements.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Mersenne31, Zp18446744073709551557, Zp2147483647},
    linalg::{gauss_jordan_elimination, Matrix},
    FiniteField,
};

const SIZES: [usize; 4] = [8, 16, 32, 64];

/// Square products, the shape `Matrix::pow` produces.
const PRODUCT_SIZES: [usize; 4] = [32, 64, 128, 256];

/// `m x k` times `k x n` with `m * k * n` held at 2^26, so the times are directly comparable and
/// the only thing that varies is the right operand's footprint: 16 KiB, 256 KiB, 8 MiB, 128 MiB at
/// 8 bytes per element.
///
/// This machine reports 256 MiB of L3 as 8 instances of 32 MiB, and which of those a
/// single-threaded run actually has is the thing §8.2 of `MILESTONE-SIMD-PARALLELISM.md` warns is
/// easy to get wrong. The 128 MiB shape is out of cache under either reading, and the 8 MiB one is
/// in under both, so the sweep does not depend on settling it.
const FOOTPRINT_SHAPES: [(usize, usize, usize); 4] = [
    (32768, 32, 64),
    (2048, 128, 256),
    (64, 512, 2048),
    (4, 2048, 8192),
];

fn random_rect<F: FiniteField>(rows: usize, columns: usize, seed: u64) -> Matrix<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    let elements: Vec<F> = (0..rows * columns).map(|_| F::random(&mut rng)).collect();
    Matrix::new(rows, columns, &elements)
}

fn random_matrix<F: FiniteField>(n: usize, seed: u64) -> Matrix<F> {
    random_rect(n, n, seed)
}

fn bench_product<F: FiniteField + 'static>(c: &mut Criterion, name: &str) {
    let mut group = c.benchmark_group("linalg");

    for n in PRODUCT_SIZES {
        let a = random_matrix::<F>(n, 11);
        let b = random_matrix::<F>(n, 13);

        group.bench_with_input(
            BenchmarkId::new(format!("matmul_square/{}", name), n),
            &(a, b),
            |bencher, (a, b)| bencher.iter(|| black_box(black_box(a) * black_box(b))),
        );
    }

    // The 128 MiB shape is a single iteration of ~67 M multiplications over a right operand that
    // cannot be cached, so ten samples rather than a hundred.
    group.sample_size(10);

    for (m, k, n) in FOOTPRINT_SHAPES {
        let a = random_rect::<F>(m, k, 11);
        let b = random_rect::<F>(k, n, 13);
        let rhs_bytes = k * n * std::mem::size_of::<F>();

        group.bench_with_input(
            BenchmarkId::new(
                format!("matmul_rhs/{}", name),
                format!("{}KiB/{}x{}x{}", rhs_bytes / 1024, m, k, n),
            ),
            &(a, b),
            |bencher, (a, b)| bencher.iter(|| black_box(black_box(a) * black_box(b))),
        );
    }

    group.finish();
}

fn bench_field<F: FiniteField + 'static>(c: &mut Criterion, name: &str) {
    let mut group = c.benchmark_group("linalg");

    for n in SIZES {
        let m = random_matrix::<F>(n, 7);

        group.bench_with_input(
            BenchmarkId::new(format!("gauss_jordan/{}", name), n),
            &m,
            |bencher, m| bencher.iter(|| black_box(gauss_jordan_elimination(black_box(m)))),
        );

        // Inversion runs elimination on an n x 2n augmented matrix, so it isolates the same
        // pivot-normalization path at twice the row length.
        group.bench_with_input(
            BenchmarkId::new(format!("inverse/{}", name), n),
            &m,
            |bencher, m| bencher.iter(|| black_box(black_box(m).inverse())),
        );
    }

    group.finish();
}

fn benches(c: &mut Criterion) {
    bench_field::<Zp2147483647>(c, "p31");
    // The same modulus in a 4-byte cell. A dense matrix is cells and nothing else, so this is
    // where halving the storage width is expected to show, and `p31` is the control.
    bench_field::<Mersenne31>(c, "p31_u32");
    bench_field::<Zp18446744073709551557>(c, "p64");
    // One field for the product: the loop order under test is the same code for every `Ring`, and
    // the benchmark lock is machine-wide.
    bench_product::<Zp2147483647>(c, "p31");
}

criterion_group!(linear_algebra, benches);
criterion_main!(linear_algebra);
