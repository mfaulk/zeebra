//! Dense finite-field linear algebra.
//!
//! Gaussian elimination and Gauss–Jordan elimination at several sizes, over a 31-bit prime at two
//! storage widths and a 64-bit prime. These drive the pivot-normalization path, which is the clearest arithmetic bottleneck
//! identified in the milestone review: one modular inverse per entry rather than per row.
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

fn random_matrix<F: FiniteField>(n: usize, seed: u64) -> Matrix<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    let elements: Vec<F> = (0..n * n).map(|_| F::random(&mut rng)).collect();
    Matrix::new(n, n, &elements)
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
}

criterion_group!(linear_algebra, benches);
criterion_main!(linear_algebra);
