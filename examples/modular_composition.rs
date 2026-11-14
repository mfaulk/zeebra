//! Brent–Kung modular composition against repeated `pow_mod`, for the Frobenius step (#271).
//!
//! The degrees are the resultant degrees recorded in `docs/research/resultant-elimination.md` §6.3
//! (81, 729, 6 561), not chosen for the benchmark. Two tables:
//!
//! - `steps`: one Frobenius application `ξ ↦ ξ^q mod h` with `ξ = x^q mod h` and `h` random monic
//!   of degree n — by `pow_mod` with exponent q, by a prebuilt [`ModularComposer`] (the amortized
//!   cost inside a distinct-degree loop), by one-shot `compose_mod`, and by Horner (n ≤ 729). The
//!   composer's construction is reported separately.
//! - `factor`: whole `factorize` on a random polynomial of degree n, each `FrobeniusRoute` forced.
//!   The two routes' factorizations are compared and the run aborts if they differ.
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
    pow_mod_limbs_unstable, FrobeniusRoute, KnownOrder, ModularComposer, Polynomial,
    UnivariatePolynomial,
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
        let mut sink5 = 0usize;
        let mut by_horner = || sink5 ^= compose_mod_horner(&xi, &xi, &h).degree() as usize;
        let mut arms: Vec<&mut dyn FnMut()> =
            vec![&mut by_pow_mod, &mut by_composer, &mut build, &mut one_shot];
        if horner {
            arms.push(&mut by_horner);
        }
        let mut samples = interleaved(&mut arms, reps);
        let row: Vec<(Duration, Duration)> = samples.iter_mut().map(|s| summary(s)).collect();
        let horner_cell = if horner {
            format!("{} ({})", ms(row[4].0), ms(row[4].1))
        } else {
            "—".to_string()
        };
        println!(
            "| {field} | {n} | {reps} | {} ({}) | {} ({}) | {} ({}) | {} ({}) | {horner_cell} | {:.2}x |",
            ms(row[0].0),
            ms(row[0].1),
            ms(row[1].0),
            ms(row[1].1),
            ms(row[2].0),
            ms(row[2].1),
            ms(row[3].0),
            ms(row[3].1),
            row[0].0.as_secs_f64() / row[1].0.as_secs_f64(),
        );
    }
}

fn factor<F: KnownOrder>(field: &str, n: usize, options: &Options) {
    if !options.wants(field) || n < options.min_n || n > options.max_n {
        return;
    }
    let mut rng = StdRng::seed_from_u64(1000 + n as u64);
    let f = UnivariatePolynomial::<F>::rand(n as u64, &mut rng);

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
    let other = key(factorize_with_route_unstable(
        &f,
        &mut StdRng::seed_from_u64(2),
        FrobeniusRoute::Composition,
    ));
    assert_eq!(reference, other, "routes disagree at n={n}");
    let degrees: Vec<u32> = reference.iter().map(|(d, _, _)| *d).collect();

    let mut sink = 0usize;
    let mut by_pow_mod = || {
        let mut rng = StdRng::seed_from_u64(3);
        sink ^= factorize_with_route_unstable(&f, &mut rng, FrobeniusRoute::PowMod).len();
    };
    let mut sink2 = 0usize;
    let mut by_composition = || {
        let mut rng = StdRng::seed_from_u64(3);
        sink2 ^= factorize_with_route_unstable(&f, &mut rng, FrobeniusRoute::Composition).len();
    };
    let reps = if n > 100 {
        options.reps.min(3)
    } else {
        options.reps
    };
    let mut samples = interleaved(&mut [&mut by_pow_mod, &mut by_composition], reps);
    let (pow_mod_median, pow_mod_min) = summary(&mut samples[0]);
    let (composition_median, composition_min) = summary(&mut samples[1]);
    println!(
        "| {field} | {n} | {degrees:?} | {reps} | {} ({}) | {} ({}) | {:.2}x |",
        ms(pow_mod_median),
        ms(pow_mod_min),
        ms(composition_median),
        ms(composition_min),
        pow_mod_median.as_secs_f64() / composition_median.as_secs_f64(),
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
                "| field | n | reps | pow_mod | composer.compose | composer build | compose_mod | Horner | pow_mod / compose |"
            );
            println!("|---|---:|---:|---:|---:|---:|---:|---:|---:|");
            steps::<KoalaBear>("KoalaBear", &options);
            steps::<Goldilocks>("Goldilocks", &options);
            steps::<Bn254Fr>("BN254 Fr", &options);
        }
        "factor" => {
            println!("factorize on a random polynomial, ms: median (min)");
            println!(
                "| field | n | factor degrees | reps | PowMod route | Composition route | PowMod / Composition |"
            );
            println!("|---|---:|---|---:|---:|---:|---:|");
            for n in [81, 729] {
                factor::<KoalaBear>("KoalaBear", n, &options);
            }
            factor::<Goldilocks>("Goldilocks", 81, &options);
            factor::<Bn254Fr>("BN254 Fr", 81, &options);
        }
        other => panic!("unknown mode {other}; expected steps or factor"),
    }
}
