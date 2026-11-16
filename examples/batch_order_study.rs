//! One complete F4 call per process under a named batch order × forward-worker arm (#816).
//!
//! Every arm prints its basis digest, so a runner checks that the orders computed the same reduced
//! basis; `max_live_nonzeros` is the peak a budget would be charged.
use std::time::Instant;
use zeebra::{
    fields::{PrimeFieldElement64, Zp2147483647, Zp32003},
    grobner::{external::corpus, f4_reported, BatchOrder, F4Options, ParallelForward},
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

fn run<const N: usize, F: FiniteField>(
    problem: &str,
    modulus: u64,
    arm: &str,
    live_entries: Option<usize>,
    started: Instant,
) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let input = corpus::instance(problem, modulus, order).expect("corpus problem");
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    let (batch_order, forward) = arm.split_once('/').expect("ARM is ORDER/FORWARD");
    let batch_order = match batch_order {
        "forward" => BatchOrder::Forward,
        "fl" => BatchOrder::FaugereLachartre,
        _ => panic!("order: forward | fl"),
    };
    let parallel_forward = match forward.split_once(':') {
        None if forward == "serial" => ParallelForward::Serial,
        Some(("auto", w)) => ParallelForward::Auto {
            max_workers: w.parse().unwrap(),
        },
        Some(("forced", w)) => ParallelForward::Forced {
            workers: w.parse().unwrap(),
        },
        _ => panic!("forward: serial | auto:MAX | forced:WORKERS"),
    };
    let mut options = F4Options {
        batch_order,
        parallel_forward,
        measure_stages: true,
        ..F4Options::default()
    };
    if let Some(entries) = live_entries {
        options = options.with_live_entries::<F>(entries);
    }
    let f4_started = Instant::now();
    let (basis, statistics) = f4_reported(&system, order, &options);
    let f4_ns = f4_started.elapsed().as_nanos();
    let basis = basis.expect("F4 completes");
    let rendered: Vec<String> = basis.iter().map(|p| p.to_string()).collect();
    let digest = sha256_hex(rendered.join("\n").as_bytes());
    let stages = statistics.stages;
    println!(
        "{}",
        Json::object([
            ("problem", Json::string(problem)),
            ("modulus", Json::int(modulus)),
            ("arm", Json::string(arm)),
            ("live_entries_budget", Json::size(options.max_live_nonzeros)),
            ("f4_ns", Json::int(f4_ns as u64)),
            ("process_ns", Json::int(started.elapsed().as_nanos() as u64)),
            ("forward_ns", Json::int(stages.forward.as_nanos() as u64)),
            ("backward_ns", Json::int(stages.backward.as_nanos() as u64)),
            (
                "peak_rss_bytes",
                peak_resident_bytes().map_or(Json::Null, Json::int)
            ),
            ("basis_elements", Json::size(basis.len())),
            ("basis_sha256", Json::string(digest)),
            ("batches", Json::size(statistics.batches)),
            (
                "max_live_nonzeros",
                Json::size(statistics.max_live_nonzeros)
            ),
            (
                "parallel_batches",
                Json::size(statistics.parallel_forward.batches)
            ),
            (
                "parallel_fallbacks",
                Json::size(statistics.parallel_forward.fallback_batches)
            ),
            (
                "reserved_entries",
                Json::size(statistics.parallel_forward.reserved_entries)
            ),
        ])
        .to_json()
        .replace('\n', "")
    );
}

fn main() {
    let started = Instant::now();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let get = |key: &str| {
        args.iter()
            .find_map(|a| a.strip_prefix(key).map(str::to_string))
    };
    let problem = get("--problem=").expect("--problem=NAME");
    let modulus: u64 = get("--modulus=").map_or(32003, |m| m.parse().unwrap());
    let arm = get("--arm=").expect("--arm=ORDER/FORWARD");
    // Raises both live budgets, stated in entries; the default refuses `mq-random-14`.
    let live_entries: Option<usize> = get("--live-entries=").map(|n| n.parse().unwrap());
    type Wide = PrimeFieldElement64<{ corpus::WIDE_64_CHARACTERISTIC }>;
    macro_rules! go {
        ($n:literal) => {
            if problem.starts_with("mq-planted-wide") {
                run::<$n, Wide>(
                    &problem,
                    corpus::WIDE_64_CHARACTERISTIC,
                    &arm,
                    live_entries,
                    started,
                )
            } else {
                match modulus {
                    32003 => run::<$n, Zp32003>(&problem, modulus, &arm, live_entries, started),
                    2147483647 => {
                        run::<$n, Zp2147483647>(&problem, modulus, &arm, live_entries, started)
                    }
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
