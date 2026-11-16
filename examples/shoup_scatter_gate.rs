//! #779's full-solve gate: one F4 call per problem over a 62-bit Montgomery prime, where
//! `PrimeFieldElement64::mul_prepared` takes Shoup's path. Prints the in-process minimum and a
//! SHA-256 over the sorted reduced basis, so two builds can be compared for time and identity.

use std::time::Instant;

use zeebra::{
    fields::Zp4611624995532046337,
    grobner::{
        benchmark_systems::{cyclic, eco, katsura, noon, reimer},
        differential::polynomial_to_string,
        external::corpus,
        f4_with_options, F4Options,
    },
    util::sha256_hex,
    MonomialOrder, MultivariatePolynomial,
};

type F = Zp4611624995532046337;
const MODULUS: u64 = 4611624995532046337;

fn names<const N: usize>() -> [String; N] {
    std::array::from_fn(|i| format!("x{i}"))
}

fn run<const N: usize>(problem: &str, system: Vec<MultivariatePolynomial<N, F>>, reps: usize) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let options = F4Options::default();
    let mut best = f64::INFINITY;
    let mut digest = String::new();
    let mut size = 0;
    for _ in 0..reps {
        let started = Instant::now();
        let (basis, _) = f4_with_options(&system, order, &options).expect("F4 failed");
        best = best.min(started.elapsed().as_secs_f64() * 1e3);
        let owned = names::<N>();
        let names: [&str; N] = std::array::from_fn(|i| owned[i].as_str());
        let mut text: Vec<String> = basis
            .iter()
            .map(|p| polynomial_to_string(p, &names, order))
            .collect();
        text.sort();
        let this = sha256_hex(text.join("\n").as_bytes());
        assert!(
            digest.is_empty() || digest == this,
            "basis changed between repetitions"
        );
        digest = this;
        size = basis.len();
    }
    println!(
        "{{\"problem\":\"{problem}\",\"modulus\":{MODULUS},\"f4_ms\":{best:.3},\"basis\":{size},\"sha256\":\"{digest}\"}}"
    );
}

fn mq10(reps: usize) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let input = corpus::instance("mq-random-10", MODULUS, order).expect("random MQ at any prime");
    let names: [&str; 10] = std::array::from_fn(|i| input.variables[i].as_str());
    let system = input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::<10, F>::parse(s, names).unwrap())
        .collect::<Vec<_>>();
    // The corpus names its variables; the generic runner renames them, which the digest absorbs.
    run::<10>("mq-random-10", system, reps);
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let reps = args
        .iter()
        .find_map(|a| a.strip_prefix("--reps="))
        .map_or(3, |r| r.parse().expect("--reps=N"));
    let problem = args
        .iter()
        .find(|a| !a.starts_with("--"))
        .expect("usage: shoup_scatter_gate PROBLEM [--reps=N]");
    match problem.as_str() {
        "mq-random-10" => mq10(reps),
        "katsura-8" => run::<9>(problem, katsura::<9, F>(), reps),
        "cyclic-7" => run::<7>(problem, cyclic::<7, F>(), reps),
        "eco-10" => run::<10>(problem, eco::<10, F>(), reps),
        "noon-7" => run::<7>(problem, noon::<7, F>(), reps),
        "reimer-6" => run::<6>(problem, reimer::<6, F>(), reps),
        _ => panic!("problems: mq-random-10, katsura-8, cyclic-7, eco-10, noon-7, reimer-6"),
    }
}
