//! Compares monic GCD routes on seeded polynomial pairs and checks their outputs before timing.

use std::{
    hint::black_box,
    process::ExitCode,
    time::{Duration, Instant},
};

use rand::{rngs::StdRng, SeedableRng};
use zeebra::{
    factorize,
    fields::{Bn254Fr, KoalaBear, Zp18446744069414584321},
    gcd_classical_unstable, gcd_half_with_base_case_unstable, is_irreducible, roots, FiniteField,
    KnownOrder, Polynomial, UnivariatePolynomial,
};

const DEGREES: [u64; 20] = [
    32, 48, 64, 65, 96, 128, 129, 256, 257, 512, 1024, 1025, 1536, 2048, 3072, 4096, 6144, 8192,
    12288, 16384,
];
const BASE_CASES: [u32; 7] = [16, 24, 32, 48, 64, 96, 128];
const BASE_CASE_DEGREES: [u64; 3] = [1024, 4096, 16384];
/// The half-GCD base case `gcd_half_unstable` ships with; `field` sweeps use it.
const SHIPPED_BASE_CASE: u32 = 64;
const MAX_REPETITIONS: usize = 5;
const DEGREE_BUDGET: Duration = Duration::from_millis(900);

fn timed<T>(operation: impl FnOnce() -> T) -> (T, Duration) {
    let start = Instant::now();
    let result = black_box(operation());
    (result, start.elapsed())
}

/// Best-of times for classical Euclid and half-GCD at `base_case` on one seeded coprime pair,
/// arm order alternated per repetition. Returns `(classical, half, repetitions)`.
fn compare<F: FiniteField>(
    name: &str,
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    base_case: u32,
) -> (f64, f64, usize) {
    let classical = || gcd_classical_unstable(black_box(a), black_box(b));
    let half = || gcd_half_with_base_case_unstable(black_box(a), black_box(b), base_case);
    let expected = classical();
    assert_eq!(expected, UnivariatePolynomial::one(), "{name}: not coprime");
    assert_eq!(half(), expected, "{name}: half-GCD disagrees");

    let mut best = [Duration::MAX; 2];
    let mut spent = Duration::ZERO;
    let mut repetitions = 0;
    while repetitions < MAX_REPETITIONS && spent < DEGREE_BUDGET {
        for arm in [repetitions % 2, (repetitions + 1) % 2] {
            let (_, elapsed) = if arm == 0 {
                timed(classical)
            } else {
                timed(half)
            };
            best[arm] = best[arm].min(elapsed);
            spent += elapsed;
        }
        repetitions += 1;
    }
    (best[0].as_secs_f64(), best[1].as_secs_f64(), repetitions)
}

fn measure_field<F: FiniteField>(name: &str, seed: u64) {
    println!("\n## {name}\n");
    println!("| Degree | Classical (s) | Half-GCD (s) | Classical / half-GCD | Reps |");
    println!("|-------:|--------------:|-------------:|---------------------:|-----:|");

    let mut rng = StdRng::seed_from_u64(seed);
    for degree in DEGREES {
        let a = UnivariatePolynomial::<F>::rand(degree, &mut rng);
        let b = UnivariatePolynomial::<F>::rand(degree - 1, &mut rng);
        let label = format!("{name}, degree {degree}");
        let (classical, half, repetitions) = compare(&label, &a, &b, SHIPPED_BASE_CASE);
        println!(
            "| {degree} | {classical:.8} | {half:.8} | {:.3} | {repetitions} |",
            classical / half
        );
    }
}

fn measure_base_cases<F: FiniteField>(name: &str, seed: u64) {
    println!("\n## {name}: classical / half-GCD by base case\n");
    print!("| Degree |");
    for base_case in BASE_CASES {
        print!(" {base_case} |");
    }
    println!();
    print!("|-------:|");
    for _ in BASE_CASES {
        print!("----:|");
    }
    println!();

    let mut rng = StdRng::seed_from_u64(seed);
    for degree in BASE_CASE_DEGREES {
        let a = UnivariatePolynomial::<F>::rand(degree, &mut rng);
        let b = UnivariatePolynomial::<F>::rand(degree - 1, &mut rng);
        print!("| {degree} |");
        for base_case in BASE_CASES {
            let label = format!("{name}, degree {degree}, base case {base_case}");
            let (classical, half, _) = compare(&label, &a, &b, base_case);
            print!(" {:.3} |", classical / half);
        }
        println!();
    }
}

fn measure_callers<F: KnownOrder>(name: &str, degree: u64) {
    let planted: Vec<_> = (1..degree - 1).map(F::new).collect();
    let linears = UnivariatePolynomial::from_zeros(&planted);
    let quadratic = (1..)
        .map(|n| UnivariatePolynomial::new(&[-F::new(n), F::zero(), F::one()]))
        .find(is_irreducible)
        .expect("the field has a nonsquare");
    let f = &linears * &quadratic;
    assert_eq!(u64::from(f.degree()), degree);

    let mut rng = StdRng::seed_from_u64(0x0194_5001);
    let (found, roots_time) = timed(|| roots(black_box(&f), &mut rng));
    assert_eq!(found.len(), planted.len());
    assert!(planted.iter().all(|root| found.contains(root)));

    let mut rng = StdRng::seed_from_u64(0x0194_5002);
    let (factors, factorize_time) = timed(|| factorize(black_box(&f), &mut rng));
    assert_eq!(factors.len(), planted.len() + 1);
    assert!(factors.contains(&(quadratic, 1)));
    assert!(planted
        .iter()
        .all(|root| factors.contains(&(UnivariatePolynomial::new(&[-*root, F::one()]), 1))));
    println!(
        "{name},{degree},{},{}",
        roots_time.as_nanos(),
        factorize_time.as_nanos()
    );
}

const USAGE: &str = "usage: gcd_crossover [all|koalabear|goldilocks|bn254|base|callers]";

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let which = args.next().unwrap_or_else(|| "all".into());
    if args.next().is_some() {
        eprintln!("{USAGE}");
        return ExitCode::FAILURE;
    }
    match which.as_str() {
        "all" => {
            measure_field::<KoalaBear>("KoalaBear", 0x0194_1001);
            measure_field::<Zp18446744069414584321>("Goldilocks", 0x0194_1002);
            measure_field::<Bn254Fr>("BN254 Fr", 0x0194_1003);
        }
        "koalabear" => measure_field::<KoalaBear>("KoalaBear", 0x0194_1001),
        "goldilocks" => measure_field::<Zp18446744069414584321>("Goldilocks", 0x0194_1002),
        "bn254" => measure_field::<Bn254Fr>("BN254 Fr", 0x0194_1003),
        "base" => {
            measure_base_cases::<KoalaBear>("KoalaBear", 0x0194_2001);
            measure_base_cases::<Zp18446744069414584321>("Goldilocks", 0x0194_2002);
            measure_base_cases::<Bn254Fr>("BN254 Fr", 0x0194_2003);
        }
        "callers" => {
            println!("field,degree,roots_ns,factorize_ns");
            for degree in [64, 256, 1024] {
                measure_callers::<KoalaBear>("koalabear", degree);
            }
            for degree in [64, 256] {
                measure_callers::<Bn254Fr>("bn254", degree);
            }
        }
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}
