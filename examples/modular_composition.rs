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
//! Two more modes serve the same-machine FLINT comparison (#784), which has to run each side as a
//! separate process: `export` writes the `factor` inputs as `.poly` files, and `factor-file`
//! factors one such file with the default route, timing `factorize` alone, and writes the monic
//! factors in the format `tools/external/flint-factor-driver` writes. The file format and the
//! harness are in `tools/external/flint-factor-driver/README.md`.
//!
//! ```text
//! cargo run --release --example modular_composition -- steps
//! cargo run --release --example modular_composition -- factor
//! cargo run --release --example modular_composition -- steps max_n=729 reps=5
//! cargo run --release --example modular_composition -- steps min_n=6561 field=koala reps=3
//! cargo run --release --example modular_composition -- export dir=/path/to/inputs
//! cargo run --release --example modular_composition -- factor-file path=in.poly out=in.factors
//! ```

use std::{
    fmt::Write as _,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    compose_mod, compose_mod_horner, factorize, factorize_with_route_unstable,
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

/// Decimal moduli of the three fields, checked against `order_limbs` before use.
const KOALABEAR_MODULUS: &str = "2130706433";
const GOLDILOCKS_MODULUS: &str = "18446744069414584321";
const BN254_FR_MODULUS: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";

/// Little-endian 64-bit limbs of a decimal string.
fn decimal_limbs(decimal: &str) -> Vec<u64> {
    let mut limbs: Vec<u64> = Vec::new();
    for digit in decimal.bytes() {
        assert!(digit.is_ascii_digit(), "not a decimal: {decimal}");
        let mut carry = u128::from(digit - b'0');
        for limb in &mut limbs {
            let wide = u128::from(*limb) * 10 + carry;
            *limb = wide as u64;
            carry = wide >> 64;
        }
        if carry != 0 {
            limbs.push(carry as u64);
        }
    }
    limbs
}

fn check_modulus<F: KnownOrder>(decimal: &str) {
    assert_eq!(
        decimal_limbs(decimal),
        F::order_limbs(),
        "modulus constant {decimal} is not the field order"
    );
}

/// `modulus <p>`, `degree <n>`, then the n + 1 coefficients low to high, one per line.
fn write_poly<F: KnownOrder>(path: &Path, modulus: &str, f: &UnivariatePolynomial<F>) {
    check_modulus::<F>(modulus);
    let mut text = format!("modulus {modulus}\ndegree {}\n", f.degree());
    for c in f.coefficients() {
        writeln!(text, "{c}").expect("writing to a String");
    }
    std::fs::write(path, text).unwrap_or_else(|e| panic!("writing {}: {e}", path.display()));
}

/// The inputs `factor` measures, under the names the FLINT harness reports them by.
fn export(dir: &Path) {
    std::fs::create_dir_all(dir).unwrap_or_else(|e| panic!("creating {}: {e}", dir.display()));
    for n in [81, 729] {
        write_poly(
            &dir.join(format!("koalabear-random-{n}.poly")),
            KOALABEAR_MODULUS,
            &random_polynomial::<KoalaBear>(n),
        );
    }
    write_poly(
        &dir.join("goldilocks-random-81.poly"),
        GOLDILOCKS_MODULUS,
        &random_polynomial::<Goldilocks>(81),
    );
    write_poly(
        &dir.join("bn254fr-random-81.poly"),
        BN254_FR_MODULUS,
        &random_polynomial::<Bn254Fr>(81),
    );
    for n in [729, 6561] {
        write_poly(
            &dir.join(format!("koalabear-linquad-{n}.poly")),
            KOALABEAR_MODULUS,
            &few_applications::<KoalaBear>(n),
        );
    }
}

/// Factors with the default route, timing `factorize` alone. `out` gets one line per monic factor,
/// `<multiplicity> <c0> ... <cd>`, sorted bytewise so that `cmp` against the FLINT driver's file
/// is a multiset comparison.
fn factor_file_in<F: KnownOrder>(modulus: &str, coefficients: &[&str], out: Option<&Path>) {
    check_modulus::<F>(modulus);
    let parsed: Vec<F> = coefficients
        .iter()
        .map(|c| F::from_str(c).unwrap_or_else(|e| panic!("coefficient {c}: {e}")))
        .collect();
    let f = UnivariatePolynomial::new(&parsed);
    let mut rng = StdRng::seed_from_u64(3);
    let start = Instant::now();
    let factors = factorize(&f, &mut rng);
    let elapsed = start.elapsed();
    println!("time_ns {}", elapsed.as_nanos());
    if let Some(out) = out {
        let mut lines: Vec<String> = factors
            .iter()
            .map(|(p, m)| {
                let mut line = m.to_string();
                for c in p.coefficients() {
                    write!(line, " {c}").expect("writing to a String");
                }
                line
            })
            .collect();
        lines.sort();
        let mut text = lines.join("\n");
        text.push('\n');
        std::fs::write(out, text).unwrap_or_else(|e| panic!("writing {}: {e}", out.display()));
    }
}

fn factor_file(path: &Path, out: Option<&Path>) {
    let text =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
    let mut lines = text.lines();
    let modulus = lines
        .next()
        .and_then(|l| l.strip_prefix("modulus "))
        .expect("first line: modulus <p>");
    let degree: usize = lines
        .next()
        .and_then(|l| l.strip_prefix("degree "))
        .and_then(|d| d.parse().ok())
        .expect("second line: degree <n>");
    let coefficients: Vec<&str> = lines.map(str::trim).filter(|l| !l.is_empty()).collect();
    assert_eq!(
        coefficients.len(),
        degree + 1,
        "expected degree + 1 coefficients"
    );
    match modulus {
        KOALABEAR_MODULUS => factor_file_in::<KoalaBear>(modulus, &coefficients, out),
        GOLDILOCKS_MODULUS => factor_file_in::<Goldilocks>(modulus, &coefficients, out),
        BN254_FR_MODULUS => factor_file_in::<Bn254Fr>(modulus, &coefficients, out),
        other => panic!("no field with modulus {other}"),
    }
}

fn main() {
    let mut mode = "steps".to_string();
    let mut dir: Option<PathBuf> = None;
    let mut path: Option<PathBuf> = None;
    let mut out: Option<PathBuf> = None;
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
        } else if let Some(v) = arg.strip_prefix("dir=") {
            dir = Some(v.into());
        } else if let Some(v) = arg.strip_prefix("path=") {
            path = Some(v.into());
        } else if let Some(v) = arg.strip_prefix("out=") {
            out = Some(v.into());
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
        "export" => export(&dir.expect("export needs dir=<path>")),
        "factor-file" => factor_file(
            &path.expect("factor-file needs path=<file>"),
            out.as_deref(),
        ),
        other => panic!("unknown mode {other}; expected steps, factor, export or factor-file"),
    }
}
