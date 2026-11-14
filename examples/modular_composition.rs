//! Brent–Kung modular composition against repeated `pow_mod`, for the Frobenius step (#271).
//!
//! The degrees are the resultant degrees recorded in `docs/research/resultant-elimination.md` §6.3
//! (81, 729, 6 561), not chosen for the benchmark. Two tables:
//!
//! - `steps`: one Frobenius application `ξ ↦ ξ^q mod h` with `ξ = x^q mod h` and `h` random monic
//!   of degree n — by `pow_mod` with exponent q, by a prebuilt [`ModularComposer`] (the amortized
//!   cost inside a distinct-degree loop) at the default `m = ceil(sqrt n)` baby steps and at `4m`,
//!   by one-shot `compose_mod`, and by Horner (n ≤ 729). The default composer's construction is
//!   reported separately.
//! - `factor`: whole `factorize`, each `FrobeniusRoute` forced, on a random polynomial of degree n
//!   (many Frobenius applications) and on `n - 2` linear factors times an irreducible quadratic
//!   (one application). The routes' factorizations are compared and the run aborts if they differ.
//!
//! Arms are interleaved within each repetition, with the order rotated per repetition; the figure
//! is the median over repetitions, with the minimum beside it.
//!
//! ```text
//! cargo run --release --example modular_composition -- steps
//! cargo run --release --example modular_composition -- factor
//! cargo run --release --example modular_composition -- steps max_n=729 reps=5
//! cargo run --release --example modular_composition -- steps min_n=6561 field=koala reps=3
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    compose_mod, compose_mod_horner, factorize_with_route_unstable,
    fields::{Bn254Fr, KoalaBear, PrimeFieldElement64},
    is_irreducible, pow_mod_limbs_unstable, FrobeniusRoute, KnownOrder, ModularComposer,
    Polynomial, UnivariatePolynomial,
};

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// The resultant degrees recorded in `resultant-elimination.md` §6.3.
const DEGREES: [usize; 3] = [81, 729, 6561];

struct Options {
    min_n: usize,
    max_n: usize,
    reps: usize,
    /// Run only the field whose name contains this, when set.
    field: Option<String>,
}

impl Options {
    fn wants(&self, field: &str) -> bool {
        self.field
            .as_ref()
            .is_none_or(|f| field.to_lowercase().contains(&f.to_lowercase()))
    }
}

fn monic<F: KnownOrder>(n: usize, rng: &mut StdRng) -> UnivariatePolynomial<F> {
    let mut coefficients: Vec<F> = (0..n).map(|_| F::random(rng)).collect();
    coefficients.push(F::one());
    UnivariatePolynomial::new(&coefficients)
}

fn x<F: KnownOrder>() -> UnivariatePolynomial<F> {
    UnivariatePolynomial::new(&[F::zero(), F::one()])
}

/// Median and minimum of `samples`.
fn summary(samples: &mut [Duration]) -> (Duration, Duration) {
    samples.sort();
    (samples[samples.len() / 2], samples[0])
}

fn ms(d: Duration) -> String {
    format!("{:.3}", d.as_secs_f64() * 1e3)
}

/// Time each arm once per repetition, rotating the order, and return per-arm samples.
fn interleaved(arms: &mut [&mut dyn FnMut()], reps: usize) -> Vec<Vec<Duration>> {
    let mut samples = vec![Vec::with_capacity(reps); arms.len()];
    for rep in 0..reps {
        for offset in 0..arms.len() {
            let arm = (rep + offset) % arms.len();
            let start = Instant::now();
            (arms[arm])();
            samples[arm].push(start.elapsed());
        }
    }
    samples
}

fn steps<F: KnownOrder>(field: &str, options: &Options) {
    if !options.wants(field) {
        return;
    }
    for &n in DEGREES
        .iter()
        .filter(|&&n| n >= options.min_n && n <= options.max_n)
    {
        let mut rng = StdRng::seed_from_u64(n as u64);
        let h = monic::<F>(n, &mut rng);
        let q = F::order_limbs();
        let xi = pow_mod_limbs_unstable(&x::<F>(), q, &h);
        let expected = pow_mod_limbs_unstable(&xi, q, &h);
        let composer = ModularComposer::new(&xi, &h);
        // The block the distinct-degree loop grows to after a few dozen uses.
        let mut wide = composer.clone();
        wide.grow_to(4 * composer.block());
        assert_eq!(
            wide.compose(&xi),
            expected,
            "wide composer disagrees at n={n}"
        );
        assert_eq!(
            composer.compose(&xi),
            expected,
            "composer disagrees at n={n}"
        );
        assert_eq!(
            compose_mod(&xi, &xi, &h),
            expected,
            "compose_mod disagrees at n={n}"
        );

        let horner = n <= 729;
        let reps = if n > 729 {
            options.reps.min(3)
        } else {
            options.reps
        };
        let mut sink = 0usize;
        let mut by_pow_mod = || sink ^= pow_mod_limbs_unstable(&xi, q, &h).degree() as usize;
        let mut sink2 = 0usize;
        let mut by_composer = || sink2 ^= composer.compose(&xi).degree() as usize;
        let mut sink3 = 0usize;
        let mut build = || sink3 ^= ModularComposer::new(&xi, &h).modulus().degree() as usize;
        let mut sink4 = 0usize;
        let mut one_shot = || sink4 ^= compose_mod(&xi, &xi, &h).degree() as usize;
        let mut sink6 = 0usize;
        let mut by_wide = || sink6 ^= wide.compose(&xi).degree() as usize;
        let mut sink5 = 0usize;
        let mut by_horner = || sink5 ^= compose_mod_horner(&xi, &xi, &h).degree() as usize;
        let mut arms: Vec<&mut dyn FnMut()> = vec![
            &mut by_pow_mod,
            &mut by_composer,
            &mut build,
            &mut one_shot,
            &mut by_wide,
        ];
        if horner {
            arms.push(&mut by_horner);
        }
        let mut samples = interleaved(&mut arms, reps);
        let row: Vec<(Duration, Duration)> = samples.iter_mut().map(|s| summary(s)).collect();
        let horner_cell = if horner {
            format!("{} ({})", ms(row[5].0), ms(row[5].1))
        } else {
            "—".to_string()
        };
        println!(
            "| {field} | {n} | {reps} | {} ({}) | {} ({}) | {} ({}) | {} ({}) | {} ({}) | {horner_cell} | {:.2}x | {:.2}x |",
            ms(row[0].0),
            ms(row[0].1),
            ms(row[1].0),
            ms(row[1].1),
            ms(row[2].0),
            ms(row[2].1),
            ms(row[3].0),
            ms(row[3].1),
            ms(row[4].0),
            ms(row[4].1),
            row[0].0.as_secs_f64() / row[1].0.as_secs_f64(),
            row[0].0.as_secs_f64() / row[4].0.as_secs_f64(),
        );
    }
}

/// A random polynomial of degree n: the distinct-degree loop runs to about its largest factor.
fn random_polynomial<F: KnownOrder>(n: usize) -> UnivariatePolynomial<F> {
    let mut rng = StdRng::seed_from_u64(1000 + n as u64);
    UnivariatePolynomial::<F>::rand(n as u64, &mut rng)
}

/// `n - 2` linear factors times an irreducible quadratic: the distinct-degree loop applies the
/// Frobenius map once and stops, so a composer built for it is never repaid.
fn few_applications<F: KnownOrder>(n: usize) -> UnivariatePolynomial<F> {
    let mut rng = StdRng::seed_from_u64(2000 + n as u64);
    let zeros: Vec<F> = (0..n - 2).map(|_| F::random(&mut rng)).collect();
    let quadratic = (2u64..)
        .map(|c| UnivariatePolynomial::new(&[F::zero() - F::new(c), F::zero(), F::one()]))
        .find(is_irreducible)
        .expect("some x^2 - c is irreducible in odd characteristic");
    &UnivariatePolynomial::from_zeros(&zeros) * &quadratic
}

const ROUTES: [FrobeniusRoute; 3] = [
    FrobeniusRoute::PowMod,
    FrobeniusRoute::Composition,
    FrobeniusRoute::Auto,
];

fn factor<F: KnownOrder>(
    field: &str,
    label: &str,
    n: usize,
    make: fn(usize) -> UnivariatePolynomial<F>,
    options: &Options,
) {
    if !options.wants(field) || n < options.min_n || n > options.max_n {
        return;
    }
    let f = make(n);

    let key = |factors: Vec<(UnivariatePolynomial<F>, usize)>| {
        let mut keyed: Vec<(u32, String, usize)> = factors
            .into_iter()
            .map(|(p, m)| (p.degree(), format!("{p:?}"), m))
            .collect();
        keyed.sort();
        keyed
    };
    let reference = key(factorize_with_route_unstable(
        &f,
        &mut StdRng::seed_from_u64(1),
        FrobeniusRoute::PowMod,
    ));
    for (seed, route) in ROUTES.iter().enumerate().skip(1) {
        let other = key(factorize_with_route_unstable(
            &f,
            &mut StdRng::seed_from_u64(2 + seed as u64),
            *route,
        ));
        assert_eq!(reference, other, "{route:?} disagrees at n={n}");
    }
    let mut degrees: Vec<u32> = reference.iter().map(|(d, _, _)| *d).collect();
    degrees.dedup();
    let largest = degrees.last().copied().unwrap_or(0);

    let mut sinks = [0usize; 3];
    let [s0, s1, s2] = &mut sinks;
    let run = |route: FrobeniusRoute, sink: &mut usize| {
        let mut rng = StdRng::seed_from_u64(3);
        *sink ^= factorize_with_route_unstable(&f, &mut rng, route).len();
    };
    let mut a = || run(ROUTES[0], s0);
    let mut b = || run(ROUTES[1], s1);
    let mut c = || run(ROUTES[2], s2);
    let reps = if n > 100 {
        options.reps.min(3)
    } else {
        options.reps
    };
    let mut samples = interleaved(&mut [&mut a, &mut b, &mut c], reps);
    let row: Vec<(Duration, Duration)> = samples.iter_mut().map(|s| summary(s)).collect();
    println!(
        "| {field} | {label} | {n} | {} | {largest} | {reps} | {} ({}) | {} ({}) | {} ({}) | {:.2}x | {:.2}x |",
        reference.len(),
        ms(row[0].0),
        ms(row[0].1),
        ms(row[1].0),
        ms(row[1].1),
        ms(row[2].0),
        ms(row[2].1),
        row[0].0.as_secs_f64() / row[1].0.as_secs_f64(),
        row[0].0.as_secs_f64() / row[2].0.as_secs_f64(),
    );
}

fn main() {
    let mut mode = "steps".to_string();
    let mut options = Options {
        min_n: 0,
        max_n: 6561,
        reps: 7,
        field: None,
    };
    for arg in std::env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("max_n=") {
            options.max_n = v.parse().expect("max_n=<usize>");
        } else if let Some(v) = arg.strip_prefix("min_n=") {
            options.min_n = v.parse().expect("min_n=<usize>");
        } else if let Some(v) = arg.strip_prefix("field=") {
            options.field = Some(v.to_string());
        } else if let Some(v) = arg.strip_prefix("reps=") {
            options.reps = v.parse().expect("reps=<usize>");
        } else {
            mode = arg;
        }
    }

    match mode.as_str() {
        "steps" => {
            println!("one Frobenius application ξ ↦ ξ^q mod h, ms: median (min)");
            println!(
                "| field | n | reps | pow_mod | compose, m=√n | build, m=√n | compose_mod | compose, m=4√n | Horner | pow_mod / compose √n | pow_mod / compose 4√n |"
            );
            println!("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|");
            steps::<KoalaBear>("KoalaBear", &options);
            steps::<Goldilocks>("Goldilocks", &options);
            steps::<Bn254Fr>("BN254 Fr", &options);
        }
        "factor" => {
            println!("whole factorize per Frobenius route, ms: median (min)");
            println!(
                "| field | input | n | distinct factors | largest factor degree | reps | PowMod | Composition | Auto | PowMod / Composition | PowMod / Auto |"
            );
            println!("|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|");
            for n in [81, 729] {
                factor::<KoalaBear>("KoalaBear", "random", n, random_polynomial, &options);
            }
            factor::<Goldilocks>("Goldilocks", "random", 81, random_polynomial, &options);
            factor::<Bn254Fr>("BN254 Fr", "random", 81, random_polynomial, &options);
            for n in [729, 6561] {
                factor::<KoalaBear>(
                    "KoalaBear",
                    "n-2 linear x quadratic",
                    n,
                    few_applications,
                    &options,
                );
            }
        }
        other => panic!("unknown mode {other}; expected steps or factor"),
    }
}
