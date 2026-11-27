//! The Frobenius power `x^q mod f` on the classical route against the cached-inverse one (#1205).
//!
//! `roots` and `RootStream` spend their time in one `pow_mod_limbs(x, q, f)`. Classically every
//! step reduces with `%`, which above the division crossover is Newton division and re-inverts
//! `rev(f)` each time; the `Auto` route inverts it once and reduces by two truncated products.
//! Both routes run from one build, interleaved per repetition, on the same `f`:
//!
//! - **frobenius** — `pow_mod_limbs_with_route_unstable(x, q, f, route)` alone, with its counters.
//! - **roots** — `roots_with_frobenius_route_unstable` on the `univariate_scaling` **roots**
//!   shape (four planted roots, a random cofactor), the row #1205's gate is stated on.
//!
//! Timings are the median of `reps` interleaved runs. Unpinned figures are indicative only; the
//! gate is read on the bench host inside a CPU reservation.
//!
//! ```text
//! cargo run --release --example frobenius_power
//! cargo run --release --example frobenius_power -- koalabear stage=roots
//! cargo run --release --example frobenius_power -- all min_log=8 max_log=14 reps=5
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, KoalaBear, PrimeFieldElement64},
    pow_mod_limbs_with_route_unstable, roots_with_frobenius_route_unstable, KnownOrder, Polynomial,
    PowModRoute, PowModStats, UnivariatePolynomial,
};

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// Roots planted in each `f`, as in `univariate_scaling`'s **roots** row.
const PLANTED: usize = 4;

struct Options {
    min_log: u32,
    max_log: u32,
    reps: usize,
    stage: String,
}

/// The **roots** row's polynomial at degree `d`.
fn planted<F: KnownOrder>(d: usize, seed: u64) -> (UnivariatePolynomial<F>, Vec<F>) {
    let mut rng = StdRng::seed_from_u64(seed);
    let planted: Vec<F> = (0..PLANTED).map(|_| F::random(&mut rng)).collect();
    let cofactor = UnivariatePolynomial::<F>::rand((d - PLANTED) as u64, &mut rng);
    (
        &UnivariatePolynomial::from_zeros(&planted) * &cofactor,
        planted,
    )
}

fn median(times: &mut [Duration]) -> f64 {
    times.sort();
    times[times.len() / 2].as_secs_f64()
}

fn measure_field<F: KnownOrder>(name: &str, options: &Options, seed: u64) {
    println!("\n## {name}, stage {}\n", options.stage);
    println!(
        "| {:>6} | {:>11} | {:>11} | {:>7} | {:>9} | {:>9} | {:>8} | {:>8} |",
        "degree", "classical s", "auto s", "speedup", "products", "products", "inverts", "inverts"
    );
    println!(
        "| {:>6} | {:>11} | {:>11} | {:>7} | {:>9} | {:>9} | {:>8} | {:>8} |",
        "", "", "", "", "classical", "auto", "classic", "auto"
    );
    println!("|{}|", ["-"; 8].map(|_| "------------").join("|"));

    let x = UnivariatePolynomial::new(&[F::zero(), F::one()]);
    for log_d in options.min_log..=options.max_log {
        let d = 1usize << log_d;
        let (f, roots) = planted::<F>(d, seed ^ log_d as u64);

        // Counters and the agreement check, outside the timed runs.
        let (reference, classical_stats) =
            pow_mod_limbs_with_route_unstable(&x, F::order_limbs(), &f, PowModRoute::Classical);
        let (candidate, auto_stats): (_, PowModStats) =
            pow_mod_limbs_with_route_unstable(&x, F::order_limbs(), &f, PowModRoute::Auto);
        assert_eq!(candidate, reference, "the routes disagree at degree {d}");

        let mut times = [Vec::new(), Vec::new()];
        for rep in 0..options.reps {
            // Alternate which route goes first, so drift does not favour one.
            let order = if rep % 2 == 0 { [0, 1] } else { [1, 0] };
            for which in order {
                let route = [PowModRoute::Classical, PowModRoute::Auto][which];
                let start = Instant::now();
                if options.stage == "roots" {
                    let mut rng = StdRng::seed_from_u64(seed);
                    let found = roots_with_frobenius_route_unstable(&f, route, &mut rng);
                    times[which].push(start.elapsed());
                    for a in &roots {
                        assert!(found.contains(a), "planted root lost at degree {d}");
                    }
                } else {
                    let (power, _) =
                        pow_mod_limbs_with_route_unstable(&x, F::order_limbs(), &f, route);
                    times[which].push(start.elapsed());
                    std::hint::black_box(power);
                }
            }
        }
        let classical = median(&mut times[0]);
        let auto = median(&mut times[1]);
        println!(
            "| {:>6} | {:>11.4} | {:>11.4} | {:>6.2}x | {:>9} | {:>9} | {:>8} | {:>8} |",
            d,
            classical,
            auto,
            classical / auto,
            classical_stats.products,
            auto_stats.products,
            classical_stats.inversions,
            auto_stats.inversions
        );
    }
}

fn main() {
    let mut selector = "all".to_string();
    let mut options = Options {
        min_log: 8,
        max_log: 13,
        reps: 3,
        stage: "frobenius".to_string(),
    };
    for argument in std::env::args().skip(1) {
        if let Some(v) = argument.strip_prefix("min_log=") {
            options.min_log = v.parse().expect("min_log=N");
        } else if let Some(v) = argument.strip_prefix("max_log=") {
            options.max_log = v.parse().expect("max_log=N");
        } else if let Some(v) = argument.strip_prefix("reps=") {
            options.reps = v.parse().expect("reps=N");
        } else if let Some(v) = argument.strip_prefix("stage=") {
            assert!(v == "frobenius" || v == "roots", "stage=frobenius|roots");
            options.stage = v.to_string();
        } else {
            selector = argument;
        }
    }
    assert!(options.reps > 0 && options.min_log >= 3);

    println!("# x^q mod f: classical against cached inverse (#1205)");
    println!("\nISA: {}", zeebra::util::isa_floor());
    let all = selector == "all";
    if all || selector == "koalabear" {
        measure_field::<KoalaBear>("KoalaBear, 2^31 - 2^24 + 1, in a u32", &options, 0x4b0a);
    }
    if all || selector == "goldilocks" {
        measure_field::<Goldilocks>("Goldilocks, 2^64 - 2^32 + 1", &options, 0x601d);
    }
    if all || selector == "bn254" {
        measure_field::<Bn254Fr>("BN254 Fr, 254 bits", &options, 0xb254);
    }
}
