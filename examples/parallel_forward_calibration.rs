//! Per-batch serial vs concurrent forward elimination on the matrices default F4 actually builds (#752).
//!
//! Each batch matrix is cloned before elimination, then replayed after the computation finishes:
//! the serial reducer-block kernel and `linalg::concurrent` at each worker count, interleaved,
//! on identical copies. Output is one JSON line per batch; pre-elimination shape features are what
//! a dispatch gate can see, the timings are what it is calibrated against.
use std::time::Instant;
use zeebra::{
    fields::{PrimeFieldElement64, Zp2147483647, Zp32003},
    grobner::{
        external::corpus,
        f4::{macaulay::MacaulayMatrix, symbolic::MonicBasis, BatchObserver},
        f4_observed,
        pairs::CriticalPair,
        F4Options,
    },
    linalg::{concurrent, reduce_rows_against_pivots_with, Backend},
    util::Json,
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

struct Capture<const N: usize, F: FiniteField>(Vec<MacaulayMatrix<N, F>>);

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for Capture<N, F> {
    fn batch(&mut self, _: &MonicBasis<N, F>, _: &[CriticalPair<N>]) {}
    fn matrix(&mut self, matrix: &MacaulayMatrix<N, F>) {
        self.0.push(matrix.clone());
    }
}

fn median(mut v: Vec<u64>) -> u64 {
    v.sort_unstable();
    v[v.len() / 2]
}

fn run<const N: usize, F: FiniteField + Send + Sync>(
    problem: &str,
    modulus: u64,
    workers: &[usize],
    repeats: usize,
) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let input = corpus::instance(problem, modulus, order).expect("corpus problem");
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    let mut capture = Capture(Vec::new());
    let options = F4Options::default();
    f4_observed(&system, order, &options, &mut capture).expect("F4 completes");
    for (index, mut matrix) in capture.0.into_iter().enumerate() {
        let split = matrix.partition_reducers_first();
        let base = matrix.matrix().clone();
        let rows = base.num_rows();
        let lower_nnz: usize = base.rows()[split..].iter().map(|r| r.nonzeros()).sum();
        let mut serial = Vec::new();
        let mut parallel: Vec<Vec<u64>> = vec![Vec::new(); workers.len()];
        let mut serial_ops = 0;
        for _ in 0..repeats {
            let mut m = base.clone();
            let t = Instant::now();
            let s = reduce_rows_against_pivots_with(Backend::Adaptive, &mut m, split, usize::MAX)
                .unwrap();
            serial.push(t.elapsed().as_nanos() as u64);
            serial_ops = s.row_operations;
            for (slot, &p) in workers.iter().enumerate() {
                let mut m = base.clone();
                let config = concurrent::Config {
                    workers: p,
                    measure_work: false,
                    ..Default::default()
                };
                let t = Instant::now();
                concurrent::reduce(&mut m, split, &config, &Default::default()).unwrap();
                parallel[slot].push(t.elapsed().as_nanos() as u64);
            }
        }
        println!(
            "{}",
            Json::object([
                ("problem", Json::string(problem)),
                ("modulus", Json::int(modulus)),
                ("batch", Json::size(index)),
                ("rows", Json::size(rows)),
                ("split", Json::size(split)),
                ("lower_rows", Json::size(rows - split)),
                ("columns", Json::size(base.num_columns())),
                ("nonzeros", Json::size(base.nonzeros())),
                ("lower_nonzeros", Json::size(lower_nnz)),
                ("serial_row_operations", Json::size(serial_ops)),
                ("serial_ns", Json::int(median(serial))),
                (
                    "parallel_ns",
                    Json::object(
                        workers
                            .iter()
                            .zip(parallel)
                            .map(|(p, v)| (p.to_string(), Json::int(median(v)))),
                    ),
                ),
            ])
            .to_json()
            .replace('\n', "")
        );
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let get = |key: &str| {
        args.iter()
            .find_map(|a| a.strip_prefix(key).map(str::to_string))
    };
    let problem = get("--problem=").expect("--problem=NAME");
    let modulus: u64 = get("--modulus=").map_or(32003, |m| m.parse().unwrap());
    let workers: Vec<usize> = get("--workers=").map_or(vec![2, 4, 8, 16], |w| {
        w.split(',').map(|x| x.parse().unwrap()).collect()
    });
    let repeats: usize = get("--repeats=").map_or(3, |r| r.parse().unwrap());
    type Wide = PrimeFieldElement64<{ corpus::WIDE_64_CHARACTERISTIC }>;
    macro_rules! go {
        ($n:literal) => {
            if problem.starts_with("mq-planted-wide") {
                run::<$n, Wide>(&problem, corpus::WIDE_64_CHARACTERISTIC, &workers, repeats)
            } else {
                match modulus {
                    32003 => run::<$n, Zp32003>(&problem, modulus, &workers, repeats),
                    2147483647 => run::<$n, Zp2147483647>(&problem, modulus, &workers, repeats),
                    _ => panic!("moduli: 32003, 2147483647"),
                }
            }
        };
    }
    let n: usize = problem
        .rsplit('-')
        .next()
        .and_then(|s| s.parse().ok())
        .expect("size suffix");
    match n {
        5 => go!(5),
        6 => go!(6),
        7 => go!(7),
        8 => go!(8),
        9 => go!(9),
        10 => go!(10),
        11 => go!(11),
        12 => go!(12),
        14 => go!(14),
        _ => panic!("unsupported size {n}"),
    }
}
