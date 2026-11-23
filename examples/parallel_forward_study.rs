//! One complete F4 call per process under a named forward × backward arm (#752).
//!
//! Selected-backward arms are the shipping route with `F4Options::parallel_forward` set; full-backward
//! arms replace each batch's elimination through the research observer hook with the same forward
//! kernel followed by full back-substitution. Every arm prints its basis digest so a runner checks
//! that all arms computed the same reduced basis.
use std::time::Instant;
use zeebra::{
    fields::{PrimeFieldElement64, Zp2147483647, Zp32003},
    grobner::{
        external::corpus,
        f4::{
            macaulay::MacaulayMatrix,
            structured::{check_reducer_block, eliminate_to, BlockOutcome, BlockPlan, RowForm},
            symbolic::MonicBasis,
            BatchObserver,
        },
        f4_observed_reported, f4_reported,
        pairs::CriticalPair,
        F4Options, ParallelForward,
    },
    linalg::{concurrent, sparse::back_substitute_pivots_within},
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

/// Full back-substitution after a serial (`workers == 0`) or concurrent forward pass.
struct FullBackward {
    workers: usize,
}

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for FullBackward {
    fn batch(&mut self, _: &MonicBasis<N, F>, _: &[CriticalPair<N>]) {}

    fn eliminate(
        &mut self,
        matrix: &mut MacaulayMatrix<N, F>,
        options: &F4Options,
    ) -> Option<Result<BlockOutcome, usize>> {
        let allowance = options.live_entry_allowance::<F>();
        let mut block = if self.workers == 0 {
            match eliminate_to(
                BlockPlan::ReducersFirstBlock,
                RowForm::Echelon,
                options.elimination,
                matrix,
                allowance,
            ) {
                Ok(block) => block,
                Err(n) => return Some(Err(n)),
            }
        } else {
            let split = matrix.partition_reducers_first();
            check_reducer_block(matrix.matrix(), split).expect("reducer block");
            let config = concurrent::Config {
                workers: self.workers,
                max_entries: allowance,
                max_workspace_bytes: 64 * 1024 * 1024,
                measure_work: false,
                ..Default::default()
            };
            let dispatch = F::concurrent_elimination().expect("field has a concurrent handle");
            match dispatch.reduce(matrix.matrix_mut(), split, &config, &Default::default()) {
                Ok(report) => BlockOutcome {
                    statistics: report.statistics,
                    free_pivots: split,
                    back_substituted_rows: None,
                },
                Err(error) => panic!("full-backward concurrent arm refused: {error:?}"),
            }
        };
        match back_substitute_pivots_within(matrix.matrix_mut(), allowance, &mut block.statistics) {
            Ok(rows) => block.back_substituted_rows = Some(rows),
            Err(n) => return Some(Err(n)),
        }
        Some(Ok(block))
    }
}

fn cpu_us() -> u64 {
    let stat = std::fs::read_to_string("/proc/self/stat").unwrap();
    let fields: Vec<&str> = stat
        .rsplit(')')
        .next()
        .unwrap()
        .split_whitespace()
        .collect();
    let ticks: u64 = fields[11].parse::<u64>().unwrap() + fields[12].parse::<u64>().unwrap();
    ticks * 10_000
}

#[path = "support/symbolic_team.rs"]
mod symbolic_team;

fn options(forward: &str) -> F4Options {
    let setting = match forward.split_once(':') {
        None if forward == "serial" => ParallelForward::Serial,
        Some(("forced", w)) => ParallelForward::Forced {
            workers: w.parse().unwrap(),
        },
        Some(("auto", w)) => ParallelForward::Auto {
            max_workers: w.parse().unwrap(),
        },
        _ => panic!("forward: serial | forced:P | auto:MAX"),
    };
    F4Options {
        parallel_forward: setting,
        parallel_symbolic: symbolic_team::capped_to(setting),
        ..F4Options::default()
    }
}

fn run<const N: usize, F: FiniteField>(problem: &str, modulus: u64, arm: &str, started: Instant) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let input = corpus::instance(problem, modulus, order).expect("corpus problem");
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    let (forward, backward) = arm.split_once('/').expect("ARM is FORWARD/BACKWARD");
    let options = options(forward);
    let setting = options.parallel_forward;
    let f4_started = Instant::now();
    let (basis, statistics) = match backward {
        "selected" => f4_reported(&system, order, &options),
        "full" => {
            let workers = match setting {
                ParallelForward::Serial => 0,
                ParallelForward::Forced { workers } => workers,
                ParallelForward::Auto { .. } => panic!("full backward takes serial or forced:P"),
            };
            f4_observed_reported(&system, order, &options, &mut FullBackward { workers })
        }
        _ => panic!("backward: selected | full"),
    };
    let f4_ns = f4_started.elapsed().as_nanos();
    let basis = basis.expect("F4 completes");
    let rendered: Vec<String> = basis.iter().map(|p| p.to_string()).collect();
    let digest = sha256_hex(rendered.join("\n").as_bytes());
    let p = statistics.parallel_forward;
    println!(
        "{}",
        Json::object([
            ("problem", Json::string(problem)),
            ("modulus", Json::int(modulus)),
            ("input_digest", Json::string(input.digest())),
            ("arm", Json::string(arm)),
            ("f4_ns", Json::int(f4_ns as u64)),
            ("process_ns", Json::int(started.elapsed().as_nanos() as u64)),
            ("process_cpu_us", Json::int(cpu_us())),
            (
                "peak_rss_bytes",
                peak_resident_bytes().map_or(Json::Null, Json::int)
            ),
            ("basis_elements", Json::size(basis.len())),
            ("basis_sha256", Json::string(digest)),
            ("batches", Json::size(statistics.batches)),
            ("parallel_batches", Json::size(p.batches)),
            ("parallel_fallback_batches", Json::size(p.fallback_batches)),
            ("parallel_retained_batches", Json::size(p.retained_batches)),
            ("parallel_retained_rows", Json::size(p.retained_rows)),
            ("parallel_max_workers", Json::size(p.max_workers)),
            ("lost_publications", Json::size(p.lost_publications)),
            ("reserved_entries", Json::size(p.reserved_entries)),
            ("parallel_workspace_bytes", Json::size(p.workspace_bytes)),
            (
                "max_live_nonzeros",
                Json::size(statistics.max_live_nonzeros)
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
    let arm = get("--arm=").expect("--arm=FORWARD/BACKWARD");
    type Wide = PrimeFieldElement64<{ corpus::WIDE_64_CHARACTERISTIC }>;
    macro_rules! go {
        ($n:literal) => {
            if problem.starts_with("mq-planted-wide") {
                run::<$n, Wide>(&problem, corpus::WIDE_64_CHARACTERISTIC, &arm, started)
            } else {
                match modulus {
                    32003 => run::<$n, Zp32003>(&problem, modulus, &arm, started),
                    2147483647 => run::<$n, Zp2147483647>(&problem, modulus, &arm, started),
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
        14 => go!(14),
        _ => panic!("unsupported size {n}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zeebra::grobner::ParallelSymbolic;

    // A P-worker forward arm caps the symbolic team at P, and a serial arm runs it serially (#891).
    #[test]
    fn forward_arm_caps_the_symbolic_team() {
        assert_eq!(
            options("serial").parallel_symbolic,
            ParallelSymbolic::Serial
        );
        assert_eq!(
            options("forced:4").parallel_symbolic,
            ParallelSymbolic::Auto { max_workers: 4 }
        );
        assert_eq!(
            options("auto:8").parallel_symbolic,
            ParallelSymbolic::Auto { max_workers: 8 }
        );
    }
}
