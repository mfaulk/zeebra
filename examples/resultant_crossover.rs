//! Times the Euclidean scalar resultant against the half-GCD one on seeded random pairs of degree
//! `(n, n - 1)`, after checking they agree. Arm order alternates per repetition (#1207).
//!
//! Both arms take coefficient slices, as `bivariate_resultant`'s per-sample kernel does: Euclidean
//! is `resultant_from_coefficients`, half-GCD is `resultant_from_coefficients_half_gcd_unstable`.

use std::{
    hint::black_box,
    process::ExitCode,
    time::{Duration, Instant},
};

use rand::{rngs::StdRng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, KoalaBear, Zp18446744069414584321},
    resultant_from_coefficients, resultant_from_coefficients_half_gcd_unstable, FiniteField,
};

const DEGREES: [usize; 17] = [
    32, 64, 96, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048, 3072, 4096, 6144, 8192, 16384,
];
const MAX_REPETITIONS: usize = 7;
const BUDGET: Duration = Duration::from_millis(2000);

/// Best-of times of two arms, order alternated per repetition: `(euclidean, half, repetitions)`.
fn race<T>(mut euclidean: impl FnMut() -> T, mut half: impl FnMut() -> T) -> (f64, f64, usize) {
    let mut best = [Duration::MAX; 2];
    let mut spent = Duration::ZERO;
    let mut repetitions = 0;
    while repetitions < MAX_REPETITIONS && spent < BUDGET {
        for arm in [repetitions % 2, (repetitions + 1) % 2] {
            let start = Instant::now();
            if arm == 0 {
                black_box(euclidean());
            } else {
                black_box(half());
            }
            let elapsed = start.elapsed();
            best[arm] = best[arm].min(elapsed);
            spent += elapsed;
        }
        repetitions += 1;
    }
    (best[0].as_secs_f64(), best[1].as_secs_f64(), repetitions)
}

fn measure<F: FiniteField>(name: &str, seed: u64, max_degree: usize) {
    println!("\n## {name}\n");
    println!("| n | Euclidean (ms) | half-GCD (ms) | Euclidean / half-GCD | reps |");
    println!("|--:|--:|--:|--:|--:|");
    let mut rng = StdRng::seed_from_u64(seed);
    for n in DEGREES.into_iter().filter(|&n| n <= max_degree) {
        let a: Vec<F> = (0..=n).map(|_| F::random(&mut rng)).collect();
        let b: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
        assert_eq!(
            resultant_from_coefficients(&a, &b),
            resultant_from_coefficients_half_gcd_unstable(&a, &b),
            "the kernels disagree at n = {n}"
        );
        let (euclidean, half, repetitions) = race(
            || resultant_from_coefficients(black_box(&a), black_box(&b)),
            || resultant_from_coefficients_half_gcd_unstable(black_box(&a), black_box(&b)),
        );
        println!(
            "| {n} | {:.3} | {:.3} | {:.3} | {repetitions} |",
            euclidean * 1e3,
            half * 1e3,
            euclidean / half
        );
    }
}

const USAGE: &str = "usage: resultant_crossover [all|koalabear|goldilocks|bn254]";

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let which = args.next().unwrap_or_else(|| "all".into());
    if args.next().is_some() {
        eprintln!("{USAGE}");
        return ExitCode::FAILURE;
    }
    let koalabear = || measure::<KoalaBear>("KoalaBear", 0x1207_0001, 16384);
    let goldilocks = || measure::<Zp18446744069414584321>("Goldilocks", 0x1207_0002, 16384);
    let bn254 = || measure::<Bn254Fr>("BN254 Fr", 0x1207_0003, 8192);
    match which.as_str() {
        "all" => {
            koalabear();
            goldilocks();
            bn254();
        }
        "koalabear" => koalabear(),
        "goldilocks" => goldilocks(),
        "bn254" => bn254(),
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}
