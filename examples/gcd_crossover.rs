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
    gcd_classical_unstable, gcd_half_with_base_case_unstable, is_irreducible,
    pow_mod_limbs_unstable, roots, FiniteField, KnownOrder, Polynomial, UnivariatePolynomial,
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

/// Best-of times for classical Euclid and half-GCD at `base_case` on one seeded pair whose monic
/// GCD is `expected`, arm order alternated per repetition. Returns `(classical, half, repetitions)`.
fn compare<F: FiniteField>(
    name: &str,
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    base_case: u32,
    expected: &UnivariatePolynomial<F>,
) -> (f64, f64, usize) {
    let classical = || gcd_classical_unstable(black_box(a), black_box(b));
    let half = || gcd_half_with_base_case_unstable(black_box(a), black_box(b), base_case);
    assert_eq!(&classical(), expected, "{name}: classical Euclid disagrees");
    assert_eq!(&half(), expected, "{name}: half-GCD disagrees");

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

    let one = UnivariatePolynomial::one();
    let mut rng = StdRng::seed_from_u64(seed);
    for degree in DEGREES {
        let a = UnivariatePolynomial::<F>::rand(degree, &mut rng);
        let b = UnivariatePolynomial::<F>::rand(degree - 1, &mut rng);
        let label = format!("{name}, degree {degree}");
        let (classical, half, repetitions) = compare(&label, &a, &b, SHIPPED_BASE_CASE, &one);
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

    let one = UnivariatePolynomial::one();
    let mut rng = StdRng::seed_from_u64(seed);
    for degree in BASE_CASE_DEGREES {
        let a = UnivariatePolynomial::<F>::rand(degree, &mut rng);
        let b = UnivariatePolynomial::<F>::rand(degree - 1, &mut rng);
        print!("| {degree} |");
        for base_case in BASE_CASES {
            let label = format!("{name}, degree {degree}, base case {base_case}");
            let (classical, half, _) = compare(&label, &a, &b, base_case, &one);
            print!(" {:.3} |", classical / half);
        }
        println!();
    }
}

/// Pairs of degree `d` and `d - 1` sharing a monic factor of degree `d / 4`, `d / 2`, `3d / 4` and
/// `d - 2`: the shapes `roots` and `factorize` hand `gcd`, where Euclid halts early at the common
/// factor. `d - 2` is `roots`'s first gcd on the `callers` input, two steps for Euclid.
fn measure_planted<F: FiniteField>(name: &str, seed: u64, degrees: &[u64]) {
    println!("\n## {name}: classical / half-GCD with a planted common factor\n");
    println!("| Degree | gcd d/4 | gcd d/2 | gcd 3d/4 | gcd d-2 |");
    println!("|-------:|--------:|--------:|---------:|--------:|");
    let mut rng = StdRng::seed_from_u64(seed);
    for &degree in degrees {
        print!("| {degree} |");
        for shared_degree in [degree / 4, degree / 2, 3 * degree / 4, degree - 2] {
            let mut shared = UnivariatePolynomial::<F>::rand(shared_degree, &mut rng);
            let lead = shared.coefficients().last().copied().expect("nonzero");
            shared = shared.scale(&lead.inverse());
            let a = &shared * &UnivariatePolynomial::rand(degree - shared_degree, &mut rng);
            let b = &shared * &UnivariatePolynomial::rand(degree - 1 - shared_degree, &mut rng);
            let label = format!("{name}, degree {degree}, shared {shared_degree}");
            // Random cofactors are coprime with overwhelming probability over these fields, and
            // the assertion inside `compare` says so if not.
            let (classical, half, _) = compare(&label, &a, &b, SHIPPED_BASE_CASE, &shared);
            print!(" {:.3} |", classical / half);
        }
        println!();
    }
}

/// `callers`' input `f`: `d - 2` distinct linear factors times one irreducible quadratic. Returns
/// `(roots, product of the linear factors, quadratic, f)`.
type CallerInput<F> = (
    Vec<F>,
    UnivariatePolynomial<F>,
    UnivariatePolynomial<F>,
    UnivariatePolynomial<F>,
);

fn caller_input<F: KnownOrder>(degree: u64) -> CallerInput<F> {
    let planted: Vec<_> = (1..degree - 1).map(F::new).collect();
    let linears = UnivariatePolynomial::from_zeros(&planted);
    let quadratic = (1..)
        .map(|n| UnivariatePolynomial::new(&[-F::new(n), F::zero(), F::one()]))
        .find(is_irreducible)
        .expect("the field has a nonsquare");
    let f = &linears * &quadratic;
    assert_eq!(u64::from(f.degree()), degree);
    (planted, linears, quadratic, f)
}

/// The two gcds at the top of `roots` on the `callers` input, timed by both routes:
/// `gcd(f, x^q - x mod f)`, whose answer has degree `d - 2`, and the first equal-degree split,
/// `gcd(g, h^((q-1)/2) - 1 mod g)` for a random `h`, whose answer has degree near `deg g / 2`.
fn measure_roots_shapes<F: KnownOrder>(name: &str, degree: u64, seed: u64) {
    let (_, linears, _, f) = caller_input::<F>(degree);
    let x = UnivariatePolynomial::new(&[F::zero(), F::one()]);
    let x_to_the_q = pow_mod_limbs_unstable(&x, F::order_limbs(), &f);
    let label = format!("{name}, degree {degree}, gcd(f, x^q - x)");
    let image = &x_to_the_q - &x;
    let (classical, half, _) = compare(&label, &f, &image, SHIPPED_BASE_CASE, &linears);
    println!(
        "| {name} | {degree} | x^q - x | {} | {classical:.6} | {half:.6} | {:.3} |",
        linears.degree(),
        classical / half
    );

    // (q - 1) / 2 from the order's limbs: q is odd, so halving it drops exactly the one.
    let limbs = F::order_limbs();
    let half_order: Vec<u64> = (0..limbs.len())
        .map(|i| (limbs[i] >> 1) | limbs.get(i + 1).map_or(0, |next| next << 63))
        .collect();
    let mut rng = StdRng::seed_from_u64(seed);
    let g = &linears;
    let h = UnivariatePolynomial::<F>::rand(u64::from(g.degree()) - 1, &mut rng);
    let candidate = &pow_mod_limbs_unstable(&h, &half_order, g) - &UnivariatePolynomial::one();
    let expected = gcd_classical_unstable(g, &candidate);
    let label = format!("{name}, degree {degree}, first split");
    let (classical, half, _) = compare(&label, g, &candidate, SHIPPED_BASE_CASE, &expected);
    println!(
        "| {name} | {} | first split | {} | {classical:.6} | {half:.6} | {:.3} |",
        g.degree(),
        expected.degree(),
        classical / half
    );
}

fn measure_callers<F: KnownOrder>(name: &str, degree: u64) {
    let (planted, _, quadratic, f) = caller_input::<F>(degree);

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

const USAGE: &str =
    "usage: gcd_crossover [all|koalabear|goldilocks|bn254|base|planted|roots-shapes|callers|callers-high]";

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
        "planted" => {
            measure_planted::<KoalaBear>("KoalaBear", 0x0194_3001, &[4096, 8192, 16384]);
            measure_planted::<Zp18446744069414584321>(
                "Goldilocks",
                0x0194_3002,
                &[2048, 4096, 8192],
            );
            measure_planted::<Bn254Fr>("BN254 Fr", 0x0194_3003, &[1024, 2048, 4096]);
        }
        "roots-shapes" => {
            println!(
                "| Field | Degree | gcd | Answer degree | Classical (s) | Half-GCD (s) | Ratio |"
            );
            println!("|:--|--:|:--|--:|--:|--:|--:|");
            measure_roots_shapes::<KoalaBear>("KoalaBear", 8192, 0x0850_0001);
            measure_roots_shapes::<Zp18446744069414584321>("Goldilocks", 4096, 0x0850_0002);
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
        // Above the 4- and 8-byte dispatch, where the route changes. BN254 is left out: its
        // `roots` alone takes over a minute at degree 2048.
        "callers-high" => {
            println!("field,degree,roots_ns,factorize_ns");
            measure_callers::<KoalaBear>("koalabear", 8192);
            measure_callers::<Zp18446744069414584321>("goldilocks", 4096);
        }
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}
