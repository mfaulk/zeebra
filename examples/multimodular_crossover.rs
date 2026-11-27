//! Karatsuba against the multi-modular product (#1226), over fields with no usable two-adic root,
//! and so what `multimodular_multiplication_crossover` should be.
//!
//! Two arms per size, interleaved within each repetition and the minimum taken:
//!
//! 1. **dense** — `multiply_above(a, b, u32::MAX, rng)`, which is exactly `multiply_dense`
//! 2. **crt** — `try_multiply_multimodular(a, b)`
//!
//! The arms are checked against each other once per size, outside the timing. Unpinned figures
//! from this binary are development figures only; `taskset` pinning is the caller's job.
//!
//! ```text
//! cargo run --release --example multimodular_crossover
//! cargo run --release --example multimodular_crossover -- 2^64-59 max_log=17
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Mersenne31, PrimeFieldElement64},
    multiply_above, try_multiply_multimodular, FiniteField, KnownOrder, UnivariatePolynomial,
};

/// `2^64 - 59`, the largest 64-bit prime, two-adicity 2.
type P64 = PrimeFieldElement64<18_446_744_073_709_551_557>;

/// `2^31 - 1` held in a `u64`, two-adicity 1: two auxiliary primes rather than three.
type P31Wide = PrimeFieldElement64<2_147_483_647>;

const FIRST_LOG: u32 = 5;
const DEFAULT_MAX_LOG: u32 = 15;
const MAX_REPETITIONS: usize = 7;
const SIZE_BUDGET: Duration = Duration::from_millis(400);

fn polynomial<F: FiniteField>(len: usize, seed: u64) -> UnivariatePolynomial<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut coefficients: Vec<F> = (0..len).map(|_| F::random(&mut rng)).collect();
    while coefficients[len - 1].is_zero() {
        coefficients[len - 1] = F::random(&mut rng);
    }
    UnivariatePolynomial::new(&coefficients)
}

/// The fastest of the interleaved repetitions of each arm, as `[dense, crt]`.
fn measure<F: KnownOrder>(len: usize) -> [Duration; 2] {
    let a = polynomial::<F>(len, len as u64 * 31 + 5);
    let b = polynomial::<F>(len, len as u64 * 37 + 7);
    let mut rng = StdRng::seed_from_u64(0x1226);
    assert_eq!(
        multiply_above(&a, &b, u32::MAX, &mut rng),
        try_multiply_multimodular(&a, &b).expect("a word-size prime field"),
        "the arms disagree at length {len}"
    );

    let mut best = [Duration::MAX; 2];
    let mut spent = Duration::ZERO;
    let mut taken = 0;
    while taken < MAX_REPETITIONS && spent < SIZE_BUDGET {
        for (index, slot) in best.iter_mut().enumerate() {
            let start = Instant::now();
            match index {
                0 => drop(multiply_above(&a, &b, u32::MAX, &mut rng)),
                _ => drop(try_multiply_multimodular(&a, &b)),
            }
            let elapsed = start.elapsed();
            *slot = (*slot).min(elapsed);
            spent += elapsed;
        }
        taken += 1;
    }
    best
}

fn sweep<F: KnownOrder>(name: &str, max_log: u32) {
    println!(
        "\n## {name} — {} B element, two-adicity {}",
        std::mem::size_of::<F>(),
        F::two_adicity()
    );
    println!("| operand len | product deg | dense us | crt us | dense/crt |");
    println!("|---:|---:|---:|---:|---:|");
    let mut lengths = Vec::new();
    for log in FIRST_LOG..=max_log {
        lengths.push(1usize << log);
        if log < max_log {
            lengths.push(3usize << (log - 1));
        }
    }
    let mut crossing = None;
    let mut previous: Option<(usize, bool)> = None;
    for len in lengths {
        let [dense, crt] = measure::<F>(len);
        let degree = 2 * len - 2;
        println!(
            "| {len} | {degree} | {:.1} | {:.1} | {:.2}x |",
            dense.as_secs_f64() * 1e6,
            crt.as_secs_f64() * 1e6,
            dense.as_secs_f64() / crt.as_secs_f64()
        );
        let faster = crt < dense;
        if let Some((below, false)) = previous {
            if faster && crossing.is_none() {
                crossing = Some((below, degree));
            }
        }
        previous = Some((degree, faster));
    }
    match crossing {
        Some((below, above)) => {
            println!("\n**Karatsuba-vs-CRT crossing is in ({below}, {above}] product degree.**")
        }
        None => println!("\n**No crossing in the sweep.**"),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let max_log = args
        .iter()
        .find_map(|arg| arg.strip_prefix("max_log="))
        .map(|v| v.parse().expect("max_log=<integer>"))
        .unwrap_or(DEFAULT_MAX_LOG);
    let wanted = |name: &str| {
        args.iter().all(|a| a.starts_with("max_log=")) || args.iter().any(|a| a == name)
    };
    if wanted("2^64-59") {
        sweep::<P64>("2^64-59", max_log);
    }
    if wanted("2^31-1-u64") {
        sweep::<P31Wide>("2^31-1-u64", max_log);
    }
    if wanted("mersenne31") {
        sweep::<Mersenne31>("mersenne31", max_log);
    }
}
