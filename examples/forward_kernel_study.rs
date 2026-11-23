//! The serial and concurrent forward kernels on the same batch matrices (#894).
//!
//! Runs one complete F4 call with the forward pass serial. Every batch matrix is handed over
//! before elimination, and each arm eliminates its own copy: the serial kernel, the concurrent
//! kernel at one worker, and the concurrent kernel at `--workers=P`. The F4 call itself is not
//! timed. Per batch it prints the row operations and coefficient products of each arm, whether the
//! one-worker concurrent result equals the serial one entry for entry, and the best of `--reps`
//! timings of the two single-threaded arms, taken in alternating order.
//!
//! `--slices=S1,S2,…` adds a deterministic model of `--sim-workers=K` workers time-sliced on one
//! CPU: the concurrent kernel's dynamic schedule, run round-robin, each worker spending up to `S`
//! coefficient products per turn before the next worker runs. A preempted row is overtaken by every
//! row the other workers finish meanwhile, which is the reordering real threads on one CPU see and
//! real threads on many CPUs mostly do not. `K = 1`, or a slice longer than any row, is the serial
//! kernel.
use std::{sync::atomic::AtomicBool, time::Instant};
use zeebra::{
    fields::{Zp2147483647, Zp32003},
    grobner::{
        external::corpus,
        f4::{
            macaulay::MacaulayMatrix,
            structured::{eliminate_to, BlockPlan, RowForm},
            symbolic::MonicBasis,
            BatchObserver,
        },
        f4_observed_reported,
        pairs::CriticalPair,
        F4Options, ParallelForward, ParallelSymbolic,
    },
    linalg::{concurrent, sparse::SparseRow, Backend, DenseAccumulator},
    util::Json,
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

#[derive(Default)]
struct Totals {
    batches: usize,
    serial_ns: u64,
    concurrent_ns: u64,
    serial_operations: usize,
    concurrent_operations: usize,
    products: usize,
    parallel_operations: usize,
    parallel_products: usize,
    parallel_lost: usize,
    mismatched_batches: usize,
    /// Per slice: row operations and products of the time-sliced model.
    simulated: Vec<(usize, usize)>,
}

struct Study {
    workers: usize,
    reps: usize,
    sim_workers: usize,
    slices: Vec<usize>,
    batch: usize,
    totals: Totals,
}

/// The forward pass under `workers` round-robin workers with a `slice` of products per turn: the
/// row operations, the coefficient products and the rank.
fn time_sliced<const N: usize, F: FiniteField>(
    matrix: &MacaulayMatrix<N, F>,
    workers: usize,
    slice: usize,
) -> (usize, usize, usize) {
    let mut copy = matrix.clone();
    let split = copy.partition_reducers_first();
    let rows = copy.matrix().rows();
    let columns = copy.num_columns();
    let mut known = vec![None; columns];
    let mut rank = 0;
    for (index, row) in rows[..split].iter().enumerate() {
        if let Some(column) = row.leading_column() {
            known[column] = Some(index);
            rank += 1;
        }
    }
    let mut published: Vec<Option<SparseRow<F>>> = vec![None; columns];
    let mut accumulators: Vec<DenseAccumulator<F>> = (0..workers)
        .map(|_| DenseAccumulator::new(columns))
        .collect();
    let mut busy = vec![false; workers];
    let (mut next, mut operations, mut products) = (split, 0, 0);
    loop {
        let mut progressed = false;
        for worker in 0..workers {
            let accumulator = &mut accumulators[worker];
            let mut budget = slice;
            loop {
                if !busy[worker] {
                    if next == rows.len() {
                        break;
                    }
                    accumulator.load(&rows[next]);
                    next += 1;
                    busy[worker] = true;
                }
                if budget == 0 {
                    break;
                }
                progressed = true;
                let Some(column) = accumulator.leading_column() else {
                    accumulator.take();
                    busy[worker] = false;
                    continue;
                };
                let pivot = known[column]
                    .map(|index| &rows[index])
                    .or(published[column].as_ref());
                match pivot {
                    Some(pivot) => {
                        let factor = accumulator.leading_coefficient().unwrap();
                        accumulator.subtract_scaled(pivot, factor);
                        operations += 1;
                        products += pivot.nonzeros();
                        budget = budget.saturating_sub(pivot.nonzeros());
                    }
                    None => {
                        accumulator.normalize();
                        published[column] = Some(accumulator.take());
                        rank += 1;
                        busy[worker] = false;
                    }
                }
            }
        }
        if !progressed {
            break;
        }
    }
    (operations, products, rank)
}

fn concurrent_config(workers: usize, measure_work: bool) -> concurrent::Config {
    concurrent::Config {
        workers,
        schedule: concurrent::Schedule::Dynamic,
        max_entries: usize::MAX,
        max_workspace_bytes: usize::MAX,
        measure_work,
    }
}

fn concurrent_arm<const N: usize, F: FiniteField>(
    matrix: &MacaulayMatrix<N, F>,
    config: &concurrent::Config,
) -> (MacaulayMatrix<N, F>, concurrent::Report, u64) {
    let mut copy = matrix.clone();
    let split = copy.partition_reducers_first();
    let dispatch = F::concurrent_elimination().expect("field has a concurrent handle");
    let started = Instant::now();
    let report = dispatch
        .reduce(copy.matrix_mut(), split, config, &AtomicBool::new(false))
        .expect("unbounded concurrent arm");
    (copy, report, started.elapsed().as_nanos() as u64)
}

fn serial_arm<const N: usize, F: FiniteField>(
    matrix: &MacaulayMatrix<N, F>,
) -> (MacaulayMatrix<N, F>, usize, u64) {
    let mut copy = matrix.clone();
    let started = Instant::now();
    let outcome = eliminate_to(
        BlockPlan::ReducersFirstBlock,
        RowForm::Echelon,
        Backend::Adaptive,
        &mut copy,
        usize::MAX,
    )
    .expect("unbounded serial arm");
    let ns = started.elapsed().as_nanos() as u64;
    (copy, outcome.statistics.row_operations, ns)
}

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for Study {
    fn batch(&mut self, _: &MonicBasis<N, F>, _: &[CriticalPair<N>]) {}

    fn matrix(&mut self, matrix: &MacaulayMatrix<N, F>) {
        self.batch += 1;
        let (serial, serial_operations, _) = serial_arm(matrix);
        let (one, measured, _) = concurrent_arm(matrix, &concurrent_config(1, true));
        let (_, parallel, _) = concurrent_arm(matrix, &concurrent_config(self.workers, true));
        let identical = serial.matrix() == one.matrix();
        let rank = serial.matrix().nonzero_rows();
        let simulated: Vec<(usize, usize)> = self
            .slices
            .iter()
            .map(|&slice| {
                let (operations, products, simulated_rank) =
                    time_sliced(matrix, self.sim_workers, slice);
                assert_eq!(simulated_rank, rank, "the time-sliced model lost rank");
                (operations, products)
            })
            .collect();
        let (mut serial_ns, mut concurrent_ns) = (u64::MAX, u64::MAX);
        for rep in 0..self.reps {
            let timed_concurrent = || concurrent_arm(matrix, &concurrent_config(1, false)).2;
            let timed_serial = || serial_arm(matrix).2;
            let (s, c) = if rep % 2 == 0 {
                let s = timed_serial();
                (s, timed_concurrent())
            } else {
                let c = timed_concurrent();
                (timed_serial(), c)
            };
            serial_ns = serial_ns.min(s);
            concurrent_ns = concurrent_ns.min(c);
        }
        let lower_rows = matrix.num_rows() - matrix.clone().partition_reducers_first();
        println!(
            "{}",
            Json::object([
                ("batch", Json::size(self.batch)),
                ("rows", Json::size(matrix.num_rows())),
                ("lower_rows", Json::size(lower_rows)),
                ("columns", Json::size(matrix.num_columns())),
                ("nonzeros", Json::size(matrix.nonzeros())),
                ("identical", Json::Bool(identical)),
                ("serial_ns", Json::int(serial_ns)),
                ("concurrent_ns", Json::int(concurrent_ns)),
                ("serial_operations", Json::size(serial_operations)),
                (
                    "concurrent_operations",
                    Json::size(measured.statistics.row_operations)
                ),
                ("products", Json::size(measured.products)),
                (
                    "parallel_operations",
                    Json::size(parallel.statistics.row_operations)
                ),
                ("parallel_products", Json::size(parallel.products)),
                ("parallel_lost", Json::size(parallel.failed_publications)),
                (
                    "simulated_products",
                    Json::Array(simulated.iter().map(|s| Json::size(s.1)).collect())
                ),
            ])
            .to_json()
            .replace('\n', "")
        );
        let t = &mut self.totals;
        t.batches += 1;
        t.serial_ns += serial_ns;
        t.concurrent_ns += concurrent_ns;
        t.serial_operations += serial_operations;
        t.concurrent_operations += measured.statistics.row_operations;
        t.products += measured.products;
        t.parallel_operations += parallel.statistics.row_operations;
        t.parallel_products += parallel.products;
        t.parallel_lost += parallel.failed_publications;
        t.mismatched_batches += usize::from(!identical);
        t.simulated.resize(simulated.len(), (0, 0));
        for (total, s) in t.simulated.iter_mut().zip(&simulated) {
            total.0 += s.0;
            total.1 += s.1;
        }
    }
}

fn run<const N: usize, F: FiniteField>(problem: &str, modulus: u64, mut study: Study) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let input = corpus::instance(problem, modulus, order).expect("corpus problem");
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    let options = F4Options {
        parallel_forward: ParallelForward::Serial,
        parallel_symbolic: ParallelSymbolic::Serial,
        ..F4Options::default()
    };
    let (basis, _) = f4_observed_reported(&system, order, &options, &mut study);
    basis.expect("F4 completes");
    let t = &study.totals;
    println!(
        "{}",
        Json::object([
            ("problem", Json::string(problem)),
            ("modulus", Json::int(modulus)),
            ("input_digest", Json::string(input.digest())),
            ("workers", Json::size(study.workers)),
            ("reps", Json::size(study.reps)),
            ("sim_workers", Json::size(study.sim_workers)),
            ("batches", Json::size(t.batches)),
            ("mismatched_batches", Json::size(t.mismatched_batches)),
            ("serial_ns", Json::int(t.serial_ns)),
            ("concurrent_ns", Json::int(t.concurrent_ns)),
            ("serial_operations", Json::size(t.serial_operations)),
            ("concurrent_operations", Json::size(t.concurrent_operations)),
            ("products", Json::size(t.products)),
            ("parallel_operations", Json::size(t.parallel_operations)),
            ("parallel_products", Json::size(t.parallel_products)),
            ("parallel_lost", Json::size(t.parallel_lost)),
            (
                "simulated",
                Json::Array(
                    study
                        .slices
                        .iter()
                        .zip(&t.simulated)
                        .map(|(slice, s)| {
                            Json::object([
                                ("slice_products", Json::size(*slice)),
                                ("operations", Json::size(s.0)),
                                ("products", Json::size(s.1)),
                            ])
                        })
                        .collect()
                )
            ),
        ])
        .to_json()
        .replace('\n', "")
    );
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let get = |key: &str| {
        args.iter()
            .find_map(|a| a.strip_prefix(key).map(str::to_string))
    };
    let problem = get("--problem=").expect("--problem=NAME");
    let modulus: u64 = get("--modulus=").map_or(2147483647, |m| m.parse().unwrap());
    let workers: usize = get("--workers=").map_or(16, |w| w.parse().unwrap());
    let reps: usize = get("--reps=").map_or(3, |r| r.parse().unwrap());
    let sim_workers: usize = get("--sim-workers=").map_or(16, |w| w.parse().unwrap());
    let slices: Vec<usize> = get("--slices=").map_or(Vec::new(), |s| {
        s.split(',')
            .map(|x| x.parse::<f64>().expect("slice in products") as usize)
            .collect()
    });
    let study = || Study {
        workers,
        reps,
        sim_workers,
        slices: slices.clone(),
        batch: 0,
        totals: Totals::default(),
    };
    macro_rules! go {
        ($n:literal) => {
            match modulus {
                32003 => run::<$n, Zp32003>(&problem, modulus, study()),
                2147483647 => run::<$n, Zp2147483647>(&problem, modulus, study()),
                _ => panic!("moduli: 32003, 2147483647"),
            }
        };
    }
    let n: usize = problem
        .rsplit('-')
        .next()
        .and_then(|s| s.parse().ok())
        .expect("size suffix");
    match n {
        6 => go!(6),
        7 => go!(7),
        8 => go!(8),
        9 => go!(9),
        10 => go!(10),
        11 => go!(11),
        _ => panic!("unsupported size {n}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Matrices(Vec<MacaulayMatrix<6, Zp32003>>);

    impl BatchObserver<6, Zp32003> for Matrices {
        fn batch(&mut self, _: &MonicBasis<6, Zp32003>, _: &[CriticalPair<6>]) {}

        fn matrix(&mut self, matrix: &MacaulayMatrix<6, Zp32003>) {
            self.0.push(matrix.clone());
        }
    }

    fn katsura6() -> Vec<MacaulayMatrix<6, Zp32003>> {
        let order = MonomialOrder::GradedReverseLexicographic;
        let input = corpus::instance("katsura-6", 32003, order).unwrap();
        let names: [&str; 6] = std::array::from_fn(|i| input.variables[i].as_str());
        let system: Vec<MultivariatePolynomial<6, Zp32003>> = input
            .system
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
            .collect();
        let mut matrices = Matrices(Vec::new());
        f4_observed_reported(&system, order, &F4Options::default(), &mut matrices)
            .0
            .unwrap();
        assert!(matrices.0.len() > 3);
        matrices.0
    }

    // One worker, or a slice no row exhausts, is the serial kernel: the same operations and the
    // same products as the one-worker concurrent kernel, whose result equals the serial one.
    #[test]
    fn the_model_without_preemption_is_the_serial_kernel() {
        for matrix in katsura6() {
            let (serial, operations, _) = serial_arm(&matrix);
            let (one, report, _) = concurrent_arm(&matrix, &concurrent_config(1, true));
            assert_eq!(serial.matrix(), one.matrix());
            assert_eq!(operations, report.statistics.row_operations);
            let rank = serial.matrix().nonzero_rows();
            for (workers, slice) in [(1, 1), (16, usize::MAX)] {
                assert_eq!(
                    time_sliced(&matrix, workers, slice),
                    (operations, report.products, rank)
                );
            }
        }
    }

    // Preemption reorders publication but cannot change the rank.
    #[test]
    fn preemption_keeps_the_rank() {
        for matrix in katsura6() {
            let rank = serial_arm(&matrix).0.matrix().nonzero_rows();
            for slice in [1, 10, 1000] {
                assert_eq!(time_sliced(&matrix, 16, slice).2, rank);
            }
        }
    }
}
