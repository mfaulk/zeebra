//! #272: bit-packed `GF(2)` elimination against the generic sparse kernel.
//!
//! Two modes. `f4` runs F4 (default options, stage timing on) over characteristic-two instance
//! families, collects every Macaulay matrix it eliminates, and times the generic
//! `reduced_row_echelon` over `Zp2` against the packed kernels on exactly those matrices, asserting
//! that every packed RREF equals the generic one. `square` sweeps dense random square matrices to
//! locate the Four Russians crossover against plain packed Gauss-Jordan.
//!
//! Arms are interleaved with a rotating order and the minimum over repetitions is kept, per the
//! repository's A/B method; run pinned and under `tools/benchlock.sh`:
//!
//! ```text
//! taskset -c 5 tools/benchlock.sh 272 target/release/examples/gf2_packed_elimination f4 5
//! taskset -c 5 tools/benchlock.sh 272 target/release/examples/gf2_packed_elimination square 5
//! ```

use std::time::{Duration, Instant};

use rand::{rngs::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::Zp2,
    grobner::{
        benchmark_systems::cyclic,
        f4::{
            f4_observed, options::F4Options, symbolic::MonicBasis, BatchObserver, MacaulayMatrix,
        },
        field_equations::with_field_equations,
        pairs::CriticalPair,
    },
    linalg::{
        gf2::{reduced_row_echelon_four_russians, reduced_row_echelon_packed, BitMatrix},
        sparse::{reduced_row_echelon, SparseMatrix, SparseRow},
    },
    Monomial, MonomialOrder, MultivariatePolynomial, One, Zero,
};

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

struct Collect(Vec<SparseMatrix<Zp2>>);

impl<const N: usize> BatchObserver<N, Zp2> for Collect {
    fn batch(&mut self, _: &MonicBasis<N, Zp2>, _: &[CriticalPair<N>]) {}
    fn matrix(&mut self, matrix: &MacaulayMatrix<N, Zp2>) {
        self.0.push(matrix.matrix().clone());
    }
}

/// `equations` random quadratics in `N` variables, each quadratic monomial present with probability
/// `density`, with a planted root — the construction `examples/boolean_density.rs` uses — before
/// the field equations are adjoined.
fn random_mq<const N: usize>(
    seed: u64,
    equations: usize,
    density: f64,
) -> Vec<MultivariatePolynomial<N, Zp2>> {
    let mut rng = StdRng::seed_from_u64(seed);
    let plant: [Zp2; N] = std::array::from_fn(|_| {
        if rng.gen_bool(0.5) {
            Zp2::one()
        } else {
            Zp2::zero()
        }
    });
    (0..equations)
        .map(|_| {
            let mut terms = Vec::new();
            for i in 0..N {
                for j in i..N {
                    if rng.gen_bool(density) {
                        let mut exponents = [0u32; N];
                        exponents[i] += 1;
                        exponents[j] += 1;
                        terms.push((Monomial::new(&exponents), Zp2::one()));
                    }
                }
            }
            let mut polynomial = MultivariatePolynomial::new(&terms);
            let value = polynomial.eval(&plant);
            polynomial += MultivariatePolynomial::new(&[(Monomial::one(), Zp2::zero() - value)]);
            polynomial
        })
        .collect()
}

/// The generic kernel's RREF as its nonzero rows in pivot order.
fn canonical_generic(mut matrix: SparseMatrix<Zp2>) -> Vec<SparseRow<Zp2>> {
    matrix.sort_rows_by_leading_column();
    matrix
        .rows()
        .iter()
        .filter(|row| !row.is_zero())
        .cloned()
        .collect()
}

fn canonical_packed(matrix: &SparseMatrix<Zp2>, rank: usize) -> Vec<SparseRow<Zp2>> {
    matrix.rows()[..rank].to_vec()
}

#[derive(Clone, Copy)]
enum Arm {
    Generic,
    Plain,
    Russians(usize),
}

const F4_ARMS: [Arm; 4] = [Arm::Generic, Arm::Plain, Arm::Russians(4), Arm::Russians(8)];

/// Per arm: minimum wall including pack/unpack, and minimum kernel-only wall.
#[derive(Clone, Copy, Default)]
struct Timing {
    whole: Duration,
    kernel: Duration,
}

fn time_arm(arm: Arm, matrix: &SparseMatrix<Zp2>, expected: &[SparseRow<Zp2>]) -> Timing {
    match arm {
        Arm::Generic => {
            let mut working = matrix.clone();
            let start = Instant::now();
            reduced_row_echelon(&mut working);
            let elapsed = start.elapsed();
            Timing {
                whole: elapsed,
                kernel: elapsed,
            }
        }
        Arm::Plain | Arm::Russians(_) => {
            let start = Instant::now();
            let mut packed = BitMatrix::from_sparse(matrix);
            let kernel_start = Instant::now();
            let statistics = match arm {
                Arm::Plain => reduced_row_echelon_packed(&mut packed),
                Arm::Russians(k) => reduced_row_echelon_four_russians(&mut packed, k),
                Arm::Generic => unreachable!(),
            };
            let kernel = kernel_start.elapsed();
            let unpacked = packed.to_sparse();
            let whole = start.elapsed();
            assert_eq!(
                canonical_packed(&unpacked, statistics.rank),
                expected,
                "a packed RREF disagreed with the generic kernel's"
            );
            Timing { whole, kernel }
        }
    }
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e3
}

fn f4_instance<const N: usize>(
    label: &str,
    system: &[MultivariatePolynomial<N, Zp2>],
    reps: usize,
) {
    let system = with_field_equations(system).expect("GF(2) has an order");
    let options = F4Options {
        measure_stages: true,
        ..F4Options::default()
    };
    let mut collect = Collect(Vec::new());
    let (basis, statistics) =
        f4_observed(&system, ORDER, &options, &mut collect).expect("instance solves");

    let mut totals = [Timing::default(); F4_ARMS.len()];
    let (mut widest, mut nonzeros, mut sparse_peak_bytes, mut packed_peak_bytes) =
        ((0, 0), 0, 0usize, 0usize);
    let mut row_operations = 0;
    for matrix in &collect.0 {
        let mut reference = matrix.clone();
        let generic_statistics = reduced_row_echelon(&mut reference);
        let expected = canonical_generic(reference);
        row_operations += generic_statistics.row_operations;
        nonzeros += matrix.nonzeros();
        if matrix.num_rows() * matrix.num_columns() > widest.0 * widest.1 {
            widest = (matrix.num_rows(), matrix.num_columns());
        }
        sparse_peak_bytes =
            sparse_peak_bytes.max(generic_statistics.peak_nonzeros * size_of::<(usize, Zp2)>());
        packed_peak_bytes =
            packed_peak_bytes.max(BitMatrix::zero(matrix.num_rows(), matrix.num_columns()).bytes());

        let mut best = [Timing {
            whole: Duration::MAX,
            kernel: Duration::MAX,
        }; F4_ARMS.len()];
        for rep in 0..reps {
            for offset in 0..F4_ARMS.len() {
                let slot = (rep + offset) % F4_ARMS.len();
                let timing = time_arm(F4_ARMS[slot], matrix, &expected);
                best[slot].whole = best[slot].whole.min(timing.whole);
                best[slot].kernel = best[slot].kernel.min(timing.kernel);
            }
        }
        for (total, best) in totals.iter_mut().zip(best) {
            total.whole += best.whole;
            total.kernel += best.kernel;
        }
    }

    let generic = totals[0].whole.as_secs_f64();
    let best_packed = totals[1..]
        .iter()
        .map(|t| t.whole.as_secs_f64())
        .fold(f64::INFINITY, f64::min);
    let speedup = generic / best_packed;
    let total = statistics.total.as_secs_f64();
    let elimination = statistics.stages.elimination.as_secs_f64();
    let share = elimination / total;
    // F4's own elimination is structured and does less than a full RREF, so the generic RREF time
    // above overstates what F4 pays. The end-to-end figure replaces F4's measured elimination stage
    // with the packed full RREF of the same matrices — conservative, since F4 needs less than that.
    let ceiling = total / (total - elimination + best_packed);
    println!(
        "| {label} | {} | {} | {}x{} | {} | {} | {:.0} | {:.2} | {:.2} ({:.2}) | {:.2} ({:.2}) | {:.2} ({:.2}) | **{:.1}x** | {:.1} | {:.2} | {:.0}% | {:.2}x | {:.1} | {:.1} |",
        basis.len(),
        collect.0.len(),
        widest.0,
        widest.1,
        nonzeros,
        row_operations,
        totals[0].whole.as_secs_f64() * 1e9 / row_operations.max(1) as f64,
        millis(totals[0].whole),
        millis(totals[1].whole),
        millis(totals[1].kernel),
        millis(totals[2].whole),
        millis(totals[2].kernel),
        millis(totals[3].whole),
        millis(totals[3].kernel),
        speedup,
        millis(statistics.total),
        millis(statistics.stages.elimination),
        share * 100.0,
        ceiling,
        sparse_peak_bytes as f64 / 1024.0,
        packed_peak_bytes as f64 / 1024.0,
    );
}

fn f4_mode(reps: usize) {
    println!("| instance | basis | matrices | widest | entries | generic row ops | generic ns/op | generic ms | plain ms (kernel) | 4R k=4 ms (kernel) | 4R k=8 ms (kernel) | best speedup | F4 total ms | F4 elim ms | F4 elim share | e2e estimate | generic peak KiB | packed widest KiB |");
    println!("| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |");
    f4_instance::<8>("mq-8", &random_mq::<8>(272, 8, 0.3), reps);
    f4_instance::<10>("mq-10", &random_mq::<10>(272, 10, 0.3), reps);
    f4_instance::<12>("mq-12", &random_mq::<12>(272, 12, 0.3), reps);
    f4_instance::<13>("mq-13", &random_mq::<13>(272, 13, 0.3), reps);
    f4_instance::<12>("sparse-mq-12", &random_mq::<12>(272, 12, 0.05), reps);
    f4_instance::<14>("overdetermined-mq-14", &random_mq::<14>(272, 28, 0.3), reps);
    f4_instance::<16>("overdetermined-mq-16", &random_mq::<16>(272, 32, 0.3), reps);
    f4_instance::<8>("cyclic-8", &cyclic::<8, Zp2>(), reps);
    f4_instance::<9>("cyclic-9", &cyclic::<9, Zp2>(), reps);
}

fn square_mode(reps: usize) {
    const ARMS: [Arm; 5] = [
        Arm::Plain,
        Arm::Russians(4),
        Arm::Russians(6),
        Arm::Russians(8),
        Arm::Russians(10),
    ];
    println!("| n | plain ms | k=4 ms | k=6 ms | k=8 ms | k=10 ms | best k | plain / best |");
    println!("| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |");
    let mut rng = StdRng::seed_from_u64(272);
    for n in [64, 128, 256, 512, 1024, 2048, 4096, 8192] {
        let mut matrix = BitMatrix::zero(n, n);
        for row in 0..n {
            for column in 0..n {
                if rng.gen_bool(0.5) {
                    matrix.set(row, column, true);
                }
            }
        }
        let mut best = [Duration::MAX; ARMS.len()];
        let mut rank = None;
        let reps = if n >= 4096 { reps.min(3) } else { reps };
        for rep in 0..reps {
            for offset in 0..ARMS.len() {
                let slot = (rep + offset) % ARMS.len();
                let mut working = matrix.clone();
                let start = Instant::now();
                let statistics = match ARMS[slot] {
                    Arm::Plain => reduced_row_echelon_packed(&mut working),
                    Arm::Russians(k) => reduced_row_echelon_four_russians(&mut working, k),
                    Arm::Generic => unreachable!(),
                };
                best[slot] = best[slot].min(start.elapsed());
                assert_eq!(*rank.get_or_insert(statistics.rank), statistics.rank);
            }
        }
        let (fastest, _) = best
            .iter()
            .enumerate()
            .skip(1)
            .min_by_key(|(_, d)| **d)
            .expect("arms");
        let k = match ARMS[fastest] {
            Arm::Russians(k) => k,
            _ => unreachable!(),
        };
        println!(
            "| {n} | {:.3} | {:.3} | {:.3} | {:.3} | {:.3} | {k} | {:.2}x |",
            millis(best[0]),
            millis(best[1]),
            millis(best[2]),
            millis(best[3]),
            millis(best[4]),
            best[0].as_secs_f64() / best[fastest].as_secs_f64(),
        );
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let reps = args
        .get(1)
        .map_or(5, |r| r.parse().expect("a repetition count"));
    match args.first().map(String::as_str) {
        Some("f4") => f4_mode(reps),
        Some("square") => square_mode(reps),
        _ => {
            eprintln!("usage: gf2_packed_elimination <f4|square> [reps]");
            std::process::exit(64);
        }
    }
}
