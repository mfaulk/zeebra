//! #827: per-batch price of level-parallel symbolic preprocessing on a live F4 trajectory.
//!
//! Each batch's closure is replayed serially and level-parallel on the live basis and pairs, in
//! alternating order, and the two are asserted equal before either time is kept. Production F4
//! then runs the batch unchanged, so the replays see the clock and cache state the live stage sees.
use std::time::{Duration, Instant};
use zeebra::{
    fields::{Zp2147483647, Zp32003},
    grobner::{
        external::corpus,
        f4::{
            f4_observed,
            symbolic::{
                symbolic_preprocessing_level_parallel, symbolic_preprocessing_with, MonicBasis,
                ReducerCache,
            },
            BatchObserver,
        },
        pairs::CriticalPair,
        F4Options, ParallelForward, ReducerSelection,
    },
    util::Json,
    FiniteField, KnownOrder, MonomialOrder, MultivariatePolynomial,
};

struct Replay {
    selection: ReducerSelection,
    workers: usize,
    min_frontier: usize,
    batches: Vec<Json>,
    serial: Duration,
    parallel: Duration,
}

impl<const N: usize, F: FiniteField + Sync> BatchObserver<N, F> for Replay {
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]) {
        let serial = || {
            let started = Instant::now();
            let closure = symbolic_preprocessing_with(
                basis,
                pairs,
                usize::MAX,
                self.selection,
                &mut ReducerCache::disabled(),
            )
            .unwrap();
            (closure, started.elapsed())
        };
        let parallel = || {
            let started = Instant::now();
            let closure = symbolic_preprocessing_level_parallel(
                basis,
                pairs,
                self.selection,
                self.workers,
                self.min_frontier,
            );
            (closure, started.elapsed())
        };
        let ((s, serial_time), (p, parallel_time)) = if self.batches.len().is_multiple_of(2) {
            let s = serial();
            (s, parallel())
        } else {
            let p = parallel();
            (serial(), p)
        };
        assert_eq!(s, p, "batch {}: closures differ", self.batches.len());
        self.serial += serial_time;
        self.parallel += parallel_time;
        self.batches.push(Json::object([
            ("pairs", Json::size(pairs.len())),
            ("rows", Json::size(s.rows.len())),
            ("columns", Json::size(s.monomials.len())),
            ("terms", Json::size(s.term_handles.len())),
            ("divisor_scan_steps", Json::size(s.counts.divisor_scan_steps)),
            ("serial_ns", Json::nanos(serial_time)),
            ("parallel_ns", Json::nanos(parallel_time)),
        ]));
    }
}

fn run<const N: usize, F: KnownOrder + Send + Sync>(
    problem: &str,
    modulus: u64,
    workers: usize,
    min_frontier: usize,
    forward_workers: usize,
) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let input = corpus::instance(problem, modulus, order).expect("ladder problem");
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    let options = F4Options {
        measure_stages: true,
        parallel_forward: if forward_workers == 1 {
            ParallelForward::Serial
        } else {
            ParallelForward::Auto {
                max_workers: forward_workers,
            }
        },
        ..F4Options::default()
    };
    let mut replay = Replay {
        selection: options.reducer_selection,
        workers,
        min_frontier,
        batches: Vec::new(),
        serial: Duration::ZERO,
        parallel: Duration::ZERO,
    };
    let started = Instant::now();
    let (_, statistics) = f4_observed(&system, order, &options, &mut replay).expect("F4");
    let elapsed = started.elapsed();
    println!(
        "{}",
        Json::object([
            ("problem", Json::string(problem)),
            ("modulus", Json::int(modulus)),
            ("digest", Json::string(input.digest())),
            ("workers", Json::size(workers)),
            ("min_frontier", Json::size(min_frontier)),
            ("forward_workers", Json::size(forward_workers)),
            ("live_symbolic_ns", Json::nanos(statistics.stages.symbolic)),
            ("live_total_ns", Json::nanos(statistics.total)),
            ("observed_call_ns", Json::nanos(elapsed)),
            ("replay_serial_ns", Json::nanos(replay.serial)),
            ("replay_parallel_ns", Json::nanos(replay.parallel)),
            ("batches", Json::Array(replay.batches)),
        ])
        .to_json()
        .replace('\n', "")
    );
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: symbolic_parallel_price PROBLEM MODULUS WORKERS [MIN_FRONTIER] [FORWARD_WORKERS]";
    let problem = args.get(1).expect(usage).as_str();
    let modulus: u64 = args.get(2).expect(usage).parse().expect(usage);
    let workers: usize = args.get(3).expect(usage).parse().expect(usage);
    let min_frontier: usize = args.get(4).map_or(256, |s| s.parse().expect(usage));
    let forward_workers: usize = args.get(5).map_or(16, |s| s.parse().expect(usage));
    assert!(workers > 0 && forward_workers > 0, "{usage}");
    macro_rules! field {
        ($field:ty) => {
            match problem {
                "mq-random-10" => {
                    run::<10, $field>(problem, modulus, workers, min_frontier, forward_workers)
                }
                "katsura-11" => {
                    run::<11, $field>(problem, modulus, workers, min_frontier, forward_workers)
                }
                "katsura-6" => {
                    run::<6, $field>(problem, modulus, workers, min_frontier, forward_workers)
                }
                _ => panic!("supported problems: mq-random-10, katsura-11, katsura-6"),
            }
        };
    }
    match modulus {
        32003 => field!(Zp32003),
        2147483647 => field!(Zp2147483647),
        _ => panic!("supported moduli: 32003, 2147483647"),
    }
}
