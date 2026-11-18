//! Times classical against half-GCD for `xgcd`, `partial_bezout` and Berlekamp–Massey on seeded
//! inputs, after checking the two routes agree. Arm order alternates per repetition.

use std::{
    hint::black_box,
    process::ExitCode,
    time::{Duration, Instant},
};

use rand::{rngs::StdRng, SeedableRng};
use zeebra::{
    berlekamp_massey_classical_unstable, berlekamp_massey_euclid_unstable,
    fields::{Bn254Fr, KoalaBear, Zp18446744069414584321, Zp65537},
    partial_bezout_classical_unstable, partial_bezout_half_unstable, xgcd_classical_unstable,
    xgcd_half_unstable, FiniteField, Polynomial, UnivariatePolynomial,
};

const DEGREES: [u64; 13] = [
    256, 512, 768, 1024, 1536, 2048, 3072, 4096, 6144, 8192, 12288, 16384, 32768,
];
const MAX_REPETITIONS: usize = 5;
const BUDGET: Duration = Duration::from_millis(1500);

/// Best-of times of two arms, order alternated per repetition: `(classical, half, repetitions)`.
fn race<T>(mut classical: impl FnMut() -> T, mut half: impl FnMut() -> T) -> (f64, f64, usize) {
    let mut best = [Duration::MAX; 2];
    let mut spent = Duration::ZERO;
    let mut repetitions = 0;
    while repetitions < MAX_REPETITIONS && spent < BUDGET {
        for arm in [repetitions % 2, (repetitions + 1) % 2] {
            let start = Instant::now();
            if arm == 0 {
                black_box(classical());
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

fn measure<F: FiniteField>(name: &str, seed: u64, max_degree: u64) {
    println!("\n## {name}: classical / half-GCD\n");
    println!("| n | xgcd(n, n-1) | partial_bezout(x^2n, S, n) | Berlekamp-Massey(2n) |");
    println!("|--:|--:|--:|--:|");
    let mut rng = StdRng::seed_from_u64(seed);
    for n in DEGREES.into_iter().filter(|&n| n <= max_degree) {
        let a = UnivariatePolynomial::<F>::rand(n, &mut rng);
        let b = UnivariatePolynomial::<F>::rand(n - 1, &mut rng);
        assert_eq!(xgcd_classical_unstable(&a, &b), xgcd_half_unstable(&a, &b));
        let (xc, xh, _) = race(
            || xgcd_classical_unstable(black_box(&a), black_box(&b)),
            || xgcd_half_unstable(black_box(&a), black_box(&b)),
        );

        let sequence: Vec<F> = (0..2 * n).map(|_| F::random(&mut rng)).collect();
        let mut power = vec![F::zero(); 2 * n as usize + 1];
        power[2 * n as usize] = F::one();
        let power = UnivariatePolynomial::new(&power);
        let s = UnivariatePolynomial::new(&sequence);
        let bound = n as u32;
        assert_eq!(
            partial_bezout_classical_unstable(&power, &s, bound),
            partial_bezout_half_unstable(&power, &s, bound)
        );
        let (pc, ph, _) = race(
            || partial_bezout_classical_unstable(black_box(&power), black_box(&s), bound),
            || partial_bezout_half_unstable(black_box(&power), black_box(&s), bound),
        );

        let classical = berlekamp_massey_classical_unstable(&sequence);
        assert_eq!(
            berlekamp_massey_euclid_unstable(&sequence).as_ref(),
            Some(&classical)
        );
        let (bc, bh, _) = race(
            || Some(berlekamp_massey_classical_unstable(black_box(&sequence))),
            || berlekamp_massey_euclid_unstable(black_box(&sequence)),
        );
        println!("| {n} | {:.3} | {:.3} | {:.3} |", xc / xh, pc / ph, bc / bh);
    }
}

const USAGE: &str = "usage: bezout_crossover [all|koalabear|goldilocks|zp65537|bn254]";

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let which = args.next().unwrap_or_else(|| "all".into());
    if args.next().is_some() {
        eprintln!("{USAGE}");
        return ExitCode::FAILURE;
    }
    let koalabear = || measure::<KoalaBear>("KoalaBear", 0x0815_0001, 32768);
    let goldilocks = || measure::<Zp18446744069414584321>("Goldilocks", 0x0815_0002, 16384);
    let zp65537 = || measure::<Zp65537>("Zp65537", 0x0815_0003, 16384);
    let bn254 = || measure::<Bn254Fr>("BN254 Fr", 0x0815_0004, 8192);
    match which.as_str() {
        "all" => {
            koalabear();
            goldilocks();
            zp65537();
            bn254();
        }
        "koalabear" => koalabear(),
        "goldilocks" => goldilocks(),
        "zp65537" => zp65537(),
        "bn254" => bn254(),
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}
