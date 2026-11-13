//! Research executors use owned jobs; no borrowed reference outlives a dispatched batch.
#[path = "support/worker_pool.rs"]
mod worker_pool;

use rayon::prelude::*;
use std::{
    hint::black_box,
    sync::{atomic::AtomicBool, Arc, Mutex},
    time::{Duration, Instant},
};
use worker_pool::WorkerPool;
use zeebra::{
    fields::Zp2147483647 as F,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        differential::polynomial_to_string,
        f4,
        fglm::{
            measure_border_reduction, measure_border_reduction_with, BorderBatch, BorderBatchSize,
        },
    },
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const SCRATCH_CELLS: usize = 8 * 1024 * 1024;

enum Runtime<S> {
    Scoped {
        workers: usize,
    },
    Parked(WorkerPool<S>),
    Rayon {
        pool: rayon::ThreadPool,
        scratch: Vec<Mutex<S>>,
    },
}

impl<S: Default + Send + 'static> Runtime<S> {
    fn new(name: &str, workers: usize) -> Self {
        match name {
            "scoped" => Self::Scoped { workers },
            "parked" => Self::Parked(WorkerPool::new(workers, 128).unwrap()),
            "rayon" => Self::Rayon {
                pool: rayon::ThreadPoolBuilder::new()
                    .num_threads(workers)
                    .build()
                    .unwrap(),
                scratch: (0..workers).map(|_| Mutex::new(S::default())).collect(),
            },
            _ => panic!("backend must be scoped, parked or rayon"),
        }
    }

    fn dispatch<T: Send + 'static>(
        &mut self,
        tasks: Vec<impl FnOnce(&mut S) -> T + Send + 'static>,
    ) -> Vec<T> {
        match self {
            Self::Scoped { workers: 1 } => tasks
                .into_iter()
                .map(|job| job(&mut S::default()))
                .collect(),
            Self::Scoped { .. } => std::thread::scope(|scope| {
                let handles: Vec<_> = tasks
                    .into_iter()
                    .map(|job| scope.spawn(move || job(&mut S::default())))
                    .collect();
                handles.into_iter().map(|h| h.join().unwrap()).collect()
            }),
            Self::Parked(pool) => pool.run(tasks, Arc::new(AtomicBool::new(false))).unwrap(),
            Self::Rayon { pool, scratch } => pool.install(|| {
                tasks
                    .into_par_iter()
                    .map(|job| {
                        let index = rayon::current_thread_index().unwrap();
                        job(&mut scratch[index].lock().unwrap())
                    })
                    .collect()
            }),
        }
    }
}

fn nanos(d: Duration) -> Json {
    Json::nanos(d)
}

fn floor(backend: &str, workers: usize, work: usize) -> Json {
    let at = Instant::now();
    let mut runtime = Runtime::<Vec<u64>>::new(backend, workers);
    let build = at.elapsed();
    let mut samples = Vec::new();
    let mut cold = Duration::ZERO;
    let mut active = Vec::new();
    for round in 0..33 {
        let at = Instant::now();
        let tasks = (0..workers)
            .map(|i| {
                move |scratch: &mut Vec<u64>| {
                    scratch.resize(1, 0);
                    let mut answer = 0u64;
                    for j in (i..work).step_by(workers) {
                        answer =
                            answer.wrapping_add(black_box(j as u64).wrapping_mul(black_box(32003)));
                    }
                    scratch[0] = answer;
                    (i, answer, std::thread::current().id())
                }
            })
            .collect();
        let answers = runtime.dispatch(tasks);
        let elapsed = at.elapsed();
        assert!(answers.iter().enumerate().all(|(i, a)| i == a.0));
        assert_eq!(
            answers.iter().map(|a| a.1).fold(0u64, u64::wrapping_add),
            (0..work)
                .map(|j| (j as u64).wrapping_mul(32003))
                .fold(0u64, u64::wrapping_add)
        );
        if round > 0 {
            active.push(Json::size(
                answers
                    .iter()
                    .map(|a| a.2)
                    .collect::<std::collections::HashSet<_>>()
                    .len(),
            ));
        }
        black_box(answers);
        if round == 0 {
            cold = elapsed;
        } else {
            samples.push(nanos(elapsed));
        }
    }
    Json::object([
        ("build_ns", nanos(build)),
        ("cold_ns", nanos(cold)),
        ("samples_ns", Json::Array(samples)),
        ("active_workers", Json::Array(active)),
        ("work", Json::size(work)),
    ])
}

fn border<const N: usize>(
    backend: &str,
    workers: usize,
    name: &str,
    size: BorderBatchSize,
    system: &[MultivariatePolynomial<N, F>],
) -> Json {
    let source = f4(system, ORDER).expect("source F4 budget");
    let variables: [String; N] = std::array::from_fn(|i| format!("x{i}"));
    let names: [&str; N] = std::array::from_fn(|i| variables[i].as_str());
    let encode = |polys: &[MultivariatePolynomial<N, F>]| {
        let mut rows: Vec<_> = polys
            .iter()
            .map(|p| polynomial_to_string(p, &names, ORDER))
            .collect();
        rows.sort();
        rows.join("\n")
    };
    let input = encode(system);
    let source_text = encode(&source);
    let limits = BorderBatch::recommended().with_size(size);
    let reference_at = Instant::now();
    let reference = measure_border_reduction(&source, ORDER, &limits, 1).unwrap();
    let scalar_whole_border = reference_at.elapsed();
    let at = Instant::now();
    let mut runtime = Runtime::<Vec<F>>::new(backend, workers);
    let build = at.elapsed();
    let mut runs = Vec::new();
    let mut capacities = vec![0usize; workers];
    let mut retained = std::collections::HashMap::<std::thread::ThreadId, usize>::new();
    for _ in 0..2 {
        let at = Instant::now();
        let mut dispatches = 0usize;
        let mut jobs = 0usize;
        let (stats, digest) = measure_border_reduction_with(
            &source,
            ORDER,
            &limits,
            workers,
            SCRATCH_CELLS,
            |tasks| {
                dispatches += 1;
                jobs += tasks.len();
                let results = runtime.dispatch(
                    tasks
                        .into_iter()
                        .map(|task| {
                            move |scratch: &mut Vec<F>| {
                                let result = task.run(scratch);
                                (result, scratch.capacity(), std::thread::current().id())
                            }
                        })
                        .collect(),
                );
                results
                    .into_iter()
                    .enumerate()
                    .map(|(i, (result, capacity, worker))| {
                        capacities[i] = capacities[i].max(capacity);
                        if backend != "scoped" {
                            retained
                                .entry(worker)
                                .and_modify(|c| *c = (*c).max(capacity))
                                .or_insert(capacity);
                        }
                        result
                    })
                    .collect()
            },
        )
        .unwrap();
        let elapsed = at.elapsed();
        assert_eq!(
            digest, reference.1,
            "every remainder agrees with the scalar reference"
        );
        assert_eq!(stats.reducer_entries, reference.0.reducer_entries);
        runs.push(Json::object([
            ("whole_border_ns", nanos(elapsed)),
            ("closure_ns", nanos(stats.closure_time)),
            ("reduction_ns", nanos(stats.reduction_time)),
            ("peak_batch_ns", nanos(stats.peak_reduction_time)),
            ("zeroed_cells", Json::size(stats.buffer_cells_zeroed)),
            ("dispatches", Json::size(dispatches)),
            ("jobs", Json::size(jobs)),
            ("reducer_entries", Json::size(stats.reducer_entries)),
            ("peak_entries", Json::size(stats.peak_reducer_entries)),
            ("columns", Json::size(stats.columns)),
            ("digest", Json::string(format!("{digest:016x}"))),
        ]));
    }
    // Slots represent group capacities, not Rayon worker residency or simultaneous allocator usage.
    Json::object([
        ("system", Json::string(name)),
        ("build_ns", nanos(build)),
        ("input_sha256", Json::string(sha256_hex(input.as_bytes()))),
        (
            "source_sha256",
            Json::string(sha256_hex(source_text.as_bytes())),
        ),
        ("input", Json::string(input)),
        ("source_basis", Json::string(source_text)),
        (
            "reference_digest",
            Json::string(format!("{:016x}", reference.1)),
        ),
        (
            "scalar_border_reduction_ns",
            nanos(reference.0.reduction_time),
        ),
        (
            "scratch_group_capacity_cells",
            Json::Array(capacities.into_iter().map(Json::size).collect()),
        ),
        ("scalar_whole_border_ns", nanos(scalar_whole_border)),
        (
            "retained_scratch_capacity_cells",
            Json::size(retained.values().sum()),
        ),
        ("runs", Json::Array(runs)),
    ])
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    assert!(
        args.len() >= 3,
        "floor BACKEND WORKERS [total-work] | border BACKEND WORKERS SYSTEM 64|all"
    );
    let backend = &args[1];
    let workers: usize = args[2].parse().unwrap();
    assert!((1..=128).contains(&workers));
    let result = match args[0].as_str() {
        "floor" => floor(
            backend,
            workers,
            args.get(3).map_or(0, |s| s.parse().unwrap()),
        ),
        "border" => {
            assert_eq!(args.len(), 5);
            let size = match args[4].as_str() {
                "64" => BorderBatchSize::Fixed(64),
                "all" => BorderBatchSize::Unbounded,
                _ => panic!("size must be 64 or all"),
            };
            match args[3].as_str() {
                "katsura-5" => border(backend, workers, "katsura-5", size, &katsura::<5, F>()),
                "katsura-6" => border(backend, workers, "katsura-6", size, &katsura::<6, F>()),
                "cyclic-5" => border(backend, workers, "cyclic-5", size, &cyclic::<5, F>()),
                "planted-8" => border(
                    backend,
                    workers,
                    "planted-8",
                    size,
                    &planted::<8, F>(&(0..8).map(|i| F::new(2 * i + 3)).collect::<Vec<_>>()),
                ),
                "katsura-7" => border(backend, workers, "katsura-7", size, &katsura::<7, F>()),
                "cyclic-6" => border(backend, workers, "cyclic-6", size, &cyclic::<6, F>()),
                "planted-6" => border(
                    backend,
                    workers,
                    "planted-6",
                    size,
                    &planted::<6, F>(&(0..6).map(|i| F::new(2 * i + 3)).collect::<Vec<_>>()),
                ),
                "planted-10" => border(
                    backend,
                    workers,
                    "planted-10",
                    size,
                    &planted::<10, F>(&(0..10).map(|i| F::new(2 * i + 3)).collect::<Vec<_>>()),
                ),
                _ => panic!("unknown system"),
            }
        }
        _ => panic!("unknown mode"),
    };
    println!(
        "{}",
        Json::object([
            ("backend", Json::string(backend)),
            ("workers", Json::size(workers)),
            (
                "peak_rss_bytes",
                peak_resident_bytes().map_or(Json::Null, Json::int)
            ),
            ("result", result),
        ])
        .to_json()
    );
}
