//! Classical Euclid against the fast Euclidean algorithm, and where the two cross.
//!
//! #194, which gated half-GCD on two primitives rather than on wanting it: the recursion is
//! `O(M(d) log d)`, so against schoolbook multiplication and long division it is
//! `O(d^2 log d)` — **worse** than the `O(d^2)` it replaces. Both gates have since opened:
//! Karatsuba dispatches at the `Mul` operator (#185, #231) and division goes through Newton
//! inversion of the reversed divisor above its own crossover (#193). So the question this answers
//! is not whether the asymptotics are better but **at what degree the asymptotics win**, which is
//! a measurement and is the one thing #194's acceptance criteria require before `gcd` routes
//! through it.
//!
//! The two arms are `gcd_classical_unstable` and `gcd_half_unstable`, timed **arm by arm inside
//! one repetition** so a drift in the box's speed falls on both. What is quoted is the **ratio**:
//! `graeffe-root-finding.md` §6.3.2 and `multivariate-gcd.md` §5.3 both measured that a
//! within-run ratio survives a 200x swing in this box's ambient load while the absolute seconds do
//! not, so the ratio column is the figure and the seconds are a snapshot with the load stated.
//!
//! The two arms are asserted **equal** at every degree before either is timed. They have to be:
//! a timing comparison between routes that disagree is a comparison of two different functions.
//!
//! ```text
//! cargo run --release --example gcd_crossover
//! cargo run --release --example gcd_crossover -- goldilocks
//! cargo run --release --example gcd_crossover -- list
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, KoalaBear, PrimeFieldElement64},
    gcd_classical_unstable, gcd_half_unstable, FiniteField, Polynomial, UnivariatePolynomial,
    HALF_GCD_BASE_CASE,
};

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// Each arm's time is its fastest over at most this many interleaved repetitions.
const MAX_REPETITIONS: usize = 5;

/// Wall clock after which a degree stops repeating, so one slow arm cannot stall the sweep.
const DEGREE_BUDGET: Duration = Duration::from_millis(900);

/// Degrees swept, straddling the base case by a factor of 64 either side.
///
/// Powers of two plus their odd neighbours: the recursion halves a degree at every level, so the
/// parity of the halving is exactly where an off-by-one in the truncation would show as a cost
/// rather than as a wrong answer.
const DEGREES: [u64; 14] = [
    32, 48, 64, 65, 96, 128, 129, 256, 257, 512, 1024, 1025, 2048, 4096,
];

/// One measured degree.
struct Row {
    degree: u64,
    classical: Duration,
    half: Duration,
    repetitions: usize,
}

/// The one-minute load average, or zero where `/proc` does not carry one.
fn one_minute_load() -> f64 {
    std::fs::read_to_string("/proc/loadavg")
        .ok()
        .and_then(|line| line.split_whitespace().next()?.parse().ok())
        .unwrap_or(0.0)
}

/// A markdown table rule: a dashed cell of each given width, pipe-separated.
fn rule(widths: &[usize]) -> String {
    let mut line = String::from("|");
    for width in widths {
        line.push_str(&"-".repeat(*width));
        line.push('|');
    }
    line
}

/// Time both routes on one pair, after asserting they agree.
fn measure<F: FiniteField>(
    a: &UnivariatePolynomial<F>,
    b: &UnivariatePolynomial<F>,
    degree: u64,
) -> Row {
    let classical = gcd_classical_unstable(a, b);
    let half = gcd_half_unstable(a, b);
    assert_eq!(
        classical, half,
        "the two GCD routes disagree at degree {degree}, so a timing comparison means nothing"
    );

    let mut best = (Duration::MAX, Duration::MAX);
    let mut spent = Duration::ZERO;
    let mut taken = 0;
    while taken < MAX_REPETITIONS && spent < DEGREE_BUDGET {
        let start = Instant::now();
        let value = gcd_classical_unstable(a, b);
        let classical_time = start.elapsed();
        std::hint::black_box(&value);

        let start = Instant::now();
        let value = gcd_half_unstable(a, b);
        let half_time = start.elapsed();
        std::hint::black_box(&value);

        best.0 = best.0.min(classical_time);
        best.1 = best.1.min(half_time);
        spent += classical_time + half_time;
        taken += 1;
    }
    Row {
        degree,
        classical: best.0,
        half: best.1,
        repetitions: taken,
    }
}

/// Sweep one field, and report where the two routes cross.
fn measure_field<F: FiniteField>(name: &str, seed: u64) {
    println!("\n\n## {name}");
    println!("\n- an element is {} bytes", std::mem::size_of::<F>());
    println!(
        "- the shipped threshold is degree {HALF_GCD_BASE_CASE}; a crossover far from it is the \
         signal that the constant is wrong"
    );
    println!();
    println!(
        "| {:>8} | {:>14} | {:>14} | {:>9} | {:>5} |",
        "degree", "classical/s", "half-gcd/s", "speedup", "reps"
    );
    println!("{}", rule(&[10, 16, 16, 11, 7]));

    let mut rng = StdRng::seed_from_u64(seed);
    let mut crossover: Option<u64> = None;
    for degree in DEGREES {
        // Coprime inputs, which is the worst case for both routes: the sequence runs to degree
        // zero rather than stopping at a shared factor, so every row measures a full descent.
        let a = UnivariatePolynomial::<F>::rand(degree, &mut rng);
        let b = UnivariatePolynomial::<F>::rand(degree - 1, &mut rng);
        let row = measure(&a, &b, degree);
        let speedup = row.classical.as_secs_f64() / row.half.as_secs_f64();
        if speedup > 1.0 && crossover.is_none() {
            crossover = Some(degree);
        }
        println!(
            "| {:>8} | {:>14.8} | {:>14.8} | {:>9.2} | {:>5} |",
            row.degree,
            row.classical.as_secs_f64(),
            row.half.as_secs_f64(),
            speedup,
            row.repetitions
        );
    }

    match crossover {
        Some(degree) => println!(
            "\n- the fast route first wins at degree **{degree}**, against a shipped threshold of \
             {HALF_GCD_BASE_CASE}"
        ),
        None => println!(
            "\n- **the fast route never wins over this field at these degrees**, which is a result \
             and not a bug: `gcd` routes through it above degree {HALF_GCD_BASE_CASE}, and a sweep \
             that cannot find a crossover says that threshold is wrong"
        ),
    }
}

fn main() {
    let which = std::env::args().nth(1).unwrap_or_else(|| "all".into());

    if which == "list" {
        println!("fields: all, koalabear, goldilocks, bn254");
        println!("no options: the degree sweep is fixed, so two runs are comparable");
        return;
    }

    println!("# The GCD routes: classical Euclid against the fast Euclidean algorithm");
    println!("\nISA: {}", zeebra::util::isa_floor());
    println!(
        "\n- one-minute load at the start of this run: **{:.2}**. The **speedup** column is a \
         ratio between arms timed inside one repetition and survives ambient contention; the \
         absolute seconds columns do not. See `graeffe-root-finding.md` §6.3.2.",
        one_minute_load()
    );
    println!(
        "- the two routes are asserted equal at every degree before either is timed, and each \
         figure is the fastest of up to {MAX_REPETITIONS} interleaved repetitions"
    );
    println!(
        "- inputs are coprime random pairs at `(d, d - 1)`, the worst case for both routes: the \
         remainder sequence runs all the way down rather than stopping at a shared factor"
    );

    let all = which == "all";
    if all || which == "koalabear" {
        measure_field::<KoalaBear>("KoalaBear, 2^31 - 2^24 + 1", 0x0194_1001);
    }
    if all || which == "goldilocks" {
        measure_field::<Goldilocks>("Goldilocks, 2^64 - 2^32 + 1", 0x0194_1002);
    }
    if all || which == "bn254" {
        measure_field::<Bn254Fr>("BN254 Fr, 254 bits", 0x0194_1003);
    }

    if let Some(peak) = zeebra::util::peak_resident_bytes() {
        println!("\n\nprocess peak resident bytes: {peak}");
    }
}
