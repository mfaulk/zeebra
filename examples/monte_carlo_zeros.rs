//! #1184: exact F4 against Monte Carlo zero skipping on one frozen target, one worker.
//!
//! cargo run --release --example monte_carlo_zeros -- --target mq11-goldilocks \
//!     [--seeds 1,2,3] [--tests 2] [--block N] [--reps 1] [--certify]
//!
//! Prints one JSON line per run: wall, basis digest, whether the basis equals the exact one, the
//! exact route's zero rows and row operations, and the Monte Carlo screening counts. Walls are
//! unpinned development figures unless taken under the bench host's protocol.
use std::time::Instant;
use zeebra::{
    fields::{PrimeFieldElement64, Zp2147483647, Zp32003},
    grobner::{
        differential::polynomial_to_string, external::corpus, f4_monte_carlo, f4_reported,
        F4Options, F4Statistics, MonteCarloZeros, ParallelForward, ParallelSymbolic,
    },
    util::{sha256_hex, Json},
    KnownOrder, MonomialOrder, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
type Wide = PrimeFieldElement64<18446744073709551263>;
const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const WIDE_CATALOG: &str = include_str!("../research/wide-corpus/cases.json");

struct Args {
    target: String,
    seeds: Vec<u64>,
    tests: u32,
    block: Option<usize>,
    reps: usize,
    certify: bool,
}

fn parse_args() -> Args {
    let mut args = Args {
        target: String::new(),
        seeds: vec![1, 2, 3],
        tests: 2,
        block: None,
        reps: 1,
        certify: false,
    };
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let mut it = raw.iter();
    while let Some(flag) = it.next() {
        let mut value = || it.next().expect("flag needs a value").clone();
        match flag.as_str() {
            "--target" => args.target = value(),
            "--seeds" => args.seeds = value().split(',').map(|s| s.parse().unwrap()).collect(),
            "--tests" => args.tests = value().parse().unwrap(),
            "--block" => args.block = Some(value().parse().unwrap()),
            "--reps" => args.reps = value().parse().unwrap(),
            "--certify" => args.certify = true,
            other => panic!("unexpected argument {other}"),
        }
    }
    args
}

/// Variables and generators of a published ladder entry or a frozen #738 wide row.
fn input(source: &str, field: &str, name: &str) -> (Vec<String>, Vec<String>) {
    if source == "ladder" {
        let instance = corpus::instance(name, field.parse().unwrap(), ORDER).expect("ladder");
        return (instance.variables.clone(), instance.system.clone());
    }
    let cases = Json::parse(WIDE_CATALOG).unwrap();
    let case = cases
        .items()
        .iter()
        .find(|c| {
            c.get("field").and_then(Json::as_str) == Some(field)
                && c.get("name").and_then(Json::as_str) == Some(name)
        })
        .expect("frozen wide row");
    let text = |key| case.get(key).and_then(Json::as_str).unwrap().to_string();
    assert_eq!(sha256_hex(text("canonical").as_bytes()), text("digest"));
    let strings = |key| -> Vec<String> {
        case.get(key)
            .unwrap()
            .items()
            .iter()
            .map(|s| s.as_str().unwrap().to_string())
            .collect()
    };
    (strings("variables"), strings("generators"))
}

fn counts(s: &F4Statistics) -> Json {
    let m = s.monte_carlo;
    Json::object([
        ("batches", Json::size(s.batches)),
        ("zero_rows", Json::size(s.zero_rows)),
        ("row_operations", Json::size(s.row_operations)),
        ("mc_screened_rows", Json::size(m.screened_rows)),
        ("mc_unscreened_rows", Json::size(m.unscreened_rows)),
        ("mc_blocks", Json::size(m.blocks)),
        ("mc_discarded_blocks", Json::size(m.discarded_blocks)),
        ("mc_exhausted_blocks", Json::size(m.exhausted_blocks)),
        ("mc_combinations", Json::size(m.combinations)),
        ("mc_zero_combinations", Json::size(m.zero_combinations)),
        ("mc_rows_ruled_zero", Json::size(m.rows_ruled_zero)),
        ("mc_pivots", Json::size(m.pivots)),
        ("mc_products", Json::size(m.products)),
    ])
}

fn run<const N: usize, F: KnownOrder>(variables: &[String], generators: &[String], args: &Args) {
    let names: [&str; N] = std::array::from_fn(|i| variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = generators
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    let exact_options = F4Options {
        parallel_forward: ParallelForward::Serial,
        parallel_symbolic: ParallelSymbolic::Serial,
        certify: args.certify,
        ..F4Options::default()
    };
    let digest = |basis: &[MultivariatePolynomial<N, F>]| {
        let mut text: Vec<_> = basis
            .iter()
            .map(|p| polynomial_to_string(p, &names, ORDER))
            .collect();
        text.sort();
        sha256_hex(text.join("\n").as_bytes())
    };
    let emit = |route: &str, seed: Option<u64>, wall: f64, basis: &str, equal: bool, json| {
        let line = Json::object([
            ("target", Json::string(&args.target)),
            ("route", Json::string(route)),
            (
                "seed",
                seed.map_or(Json::Null, |s| Json::string(s.to_string())),
            ),
            ("wall_s", Json::string(format!("{wall:.3}"))),
            ("basis_sha256", Json::string(basis)),
            ("equals_exact", Json::Bool(equal)),
            ("counts", json),
        ]);
        println!("{}", line.to_json().replace('\n', ""));
    };
    let mut exact = None;
    for _ in 0..args.reps {
        let started = Instant::now();
        let (basis, statistics) = f4_reported(&system, ORDER, &exact_options);
        let wall = started.elapsed().as_secs_f64();
        let basis = basis.expect("exact route completes");
        emit(
            "exact",
            None,
            wall,
            &digest(&basis),
            true,
            counts(&statistics),
        );
        exact = Some(basis);
    }
    let exact = exact.expect("--reps is at least one");
    for &seed in &args.seeds {
        let options = F4Options {
            monte_carlo: Some(MonteCarloZeros {
                zero_tests: args.tests,
                block_rows: args.block,
                ..MonteCarloZeros::new(seed)
            }),
            ..exact_options.clone()
        };
        for _ in 0..args.reps {
            let started = Instant::now();
            let result = f4_monte_carlo(&system, ORDER, &options).expect("Monte Carlo completes");
            let wall = started.elapsed().as_secs_f64();
            let equal = result.basis == exact;
            emit(
                "monte-carlo",
                Some(seed),
                wall,
                &digest(&result.basis),
                equal,
                counts(&result.statistics),
            );
            eprintln!(
                "seed {seed}: per-block bound {:.3e}, whole-call bound {:.3e}",
                result.guarantee.per_block_bound, result.guarantee.whole_call_bound
            );
        }
    }
}

fn main() {
    let args = parse_args();
    let (source, field, name) = match args.target.as_str() {
        "mq10-32003" => ("ladder", "32003", "mq-random-10"),
        "mq10-m31" => ("ladder", "2147483647", "mq-random-10"),
        "katsura9-m31" => ("ladder", "2147483647", "katsura-9"),
        "katsura11-m31" => ("ladder", "2147483647", "katsura-11"),
        "cyclic7-m31" => ("ladder", "2147483647", "cyclic-7"),
        "mq11-goldilocks" => ("wide", "goldilocks", "mq-random-11"),
        "eco12-wide64" => ("wide", "wide64", "eco-12"),
        other => panic!("unknown target {other}"),
    };
    let (variables, generators) = input(source, field, name);
    match args.target.as_str() {
        "mq10-32003" => run::<10, Zp32003>(&variables, &generators, &args),
        "mq10-m31" => run::<10, Zp2147483647>(&variables, &generators, &args),
        "katsura9-m31" => run::<9, Zp2147483647>(&variables, &generators, &args),
        "katsura11-m31" => run::<11, Zp2147483647>(&variables, &generators, &args),
        "cyclic7-m31" => run::<7, Zp2147483647>(&variables, &generators, &args),
        "mq11-goldilocks" => run::<11, Goldilocks>(&variables, &generators, &args),
        "eco12-wide64" => run::<12, Wide>(&variables, &generators, &args),
        _ => unreachable!(),
    }
}
