//! The determinant stage's per-sample specialization, against a forward-difference batch.
//!
//! Issue #598. `sylvester_resultant_euclid` evaluates every coefficient of the pair in the
//! eliminated variable at the sample point, once per sample:
//!
//! ```text
//! let a: Vec<F> = fc.iter().map(|c| c.eval(&at)).collect();
//! ```
//!
//! `fc` and `gc` are fixed across the whole sweep, so this is a multipoint evaluation of
//! `2(d + 1)` fixed univariate polynomials at `S` fixed points done the slowest way: one Horner
//! pass per polynomial per point. #412 measured it at about **two thirds of the per-determinant
//! cost**.
//!
//! # Why this measures finite differences and not the transform
//!
//! #598 proposes two routes and prices the transform at ~40x. That route needs the sample set to
//! be a multiplicative subgroup, and the module comment on `resultant.rs` records that the
//! subgroup route **loses on this problem shape** — padding 13 123 samples to 16 384 costs more
//! determinants than the Lagrange solve it removes. So the route that actually runs in production
//! samples at **consecutive field elements**, and on an arithmetic progression the available trick
//! is the one #598 names second: forward differences.
//!
//! It is not an asymptotic win. A degree-`e` polynomial stepped by differences costs `e`
//! **additions** per point where Horner costs `e` **multiply-adds**, so the operation count is
//! unchanged and only the operation gets cheaper. Whether that is worth the complexity is a
//! measurement, and this binary is it — run before the integration rather than after, because a
//! ratio near one means the integration should not be written.
//!
//! It is also the route with no memory wall. Holding the whole `2(d + 1) x S` specialization would
//! be about **690 MB** at `rf4-rp2` over an 8-byte field and 2.8 GB over BN254 `Fr`; a difference
//! table is `O(d^2)` total — about 4 MB at `d = 729` — and emits one sample's column at a time, so
//! it slots into the existing per-sample loop without a buffer.
//!
//! ```text
//! cargo run --release --example specialization_batch
//! cargo run --release --example specialization_batch -- --degree 729 --samples 8192
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, KoalaBear, PrimeFieldElement64},
    util::peak_resident_bytes,
    FiniteField, Polynomial, UnivariatePolynomial,
};

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// Each arm's time is its fastest over at most this many interleaved repetitions.
const MAX_REPETITIONS: usize = 5;

/// Target wall time for all repetitions at one shape.
const PAIR_BUDGET: Duration = Duration::from_millis(2_000);

/// The coefficient polynomials of a bivariate pair read in the eliminated variable.
///
/// `fc[j]` has degree `degree - j`, which is the shape `coefficients_in` produces for a CICO row of
/// total degree `degree` — see #598.
fn coefficient_polynomials<F: FiniteField>(
    degree: usize,
    seed: u64,
) -> Vec<UnivariatePolynomial<F>> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..=degree)
        .map(|j| UnivariatePolynomial::<F>::rand((degree - j) as u64, &mut rng))
        .collect()
}

/// One specialized column per sample, by Horner at each point. The shipped route.
fn by_horner<F: FiniteField>(fc: &[UnivariatePolynomial<F>], at: &[F], out: &mut [F]) {
    for (index, x) in at.iter().enumerate() {
        for (slot, c) in out[index * fc.len()..].iter_mut().zip(fc) {
            *slot = c.eval(x);
        }
    }
}

/// The same columns by forward differences along the arithmetic progression.
///
/// `t[k]` holds the `k`-th forward difference of one polynomial at the current point. The output is
/// `t[0]`, and advancing one step is `t[k] += t[k + 1]` for `k` descending — because
/// `D^k p(x + h) = D^k p(x) + D^(k+1) p(x)`. The top difference of a degree-`e` polynomial is
/// constant, so it never changes and the step costs `e` additions.
///
/// Setup evaluates each polynomial at its first `e + 1` points by Horner and differences them
/// down, which is `O(e^2)` once rather than per point.
fn by_differences<F: FiniteField>(fc: &[UnivariatePolynomial<F>], at: &[F], out: &mut [F]) {
    let width = fc.len();
    // One difference table per polynomial, `table[k]` holding the k-th forward difference at the
    // table's current position, which starts at `at[0]`. A polynomial with fewer points available
    // than its degree gets an empty table and stays on Horner — the table would not pay there and
    // could not be built.
    let mut tables: Vec<Vec<F>> = Vec::with_capacity(width);
    for c in fc {
        let e = c.degree() as usize;
        if at.len() < e + 1 {
            tables.push(Vec::new());
            continue;
        }
        let mut row: Vec<F> = at[..=e].iter().map(|x| c.eval(x)).collect();
        // Repeated in-place differencing: after pass `k`, `row[k]` is the k-th difference at
        // `at[0]`. Descending `i` so each read of `row[i - 1]` precedes its overwrite.
        for k in 0..=e {
            for i in (k + 1..=e).rev() {
                row[i] = row[i] - row[i - 1];
            }
        }
        tables.push(row);
    }

    for index in 0..at.len() {
        for (column, table) in tables.iter_mut().enumerate() {
            if table.is_empty() {
                out[index * width + column] = fc[column].eval(&at[index]);
                continue;
            }
            // Read before advancing: the table is at position `index` on entry.
            out[index * width + column] = table[0];
            // `t_k(x + h) = t_k(x) + t_{k+1}(x)`, ascending k so each read of `t_{k+1}` is still
            // the old value. The top difference of a degree-e polynomial is constant and is never
            // touched, which is why the step costs `e` additions and not `e + 1`.
            for k in 0..table.len() - 1 {
                table[k] = table[k] + table[k + 1];
            }
        }
    }
}

/// The first index at which two specializations differ, or `None`.
///
/// Not `assert_eq!` on the two vectors: at the shapes this binary runs, they hold a million field
/// elements each and the panic message was 323 MB.
fn first_mismatch<F: FiniteField>(left: &[F], right: &[F]) -> Option<usize> {
    left.iter().zip(right).position(|(a, b)| a != b)
}

fn rule(widths: &[usize]) -> String {
    let mut line = String::from("|");
    for width in widths {
        line.push_str(&"-".repeat(*width));
        line.push('|');
    }
    line
}

fn measure<F: FiniteField>(name: &str, degree: usize, samples: usize, seed: u64) {
    let fc = coefficient_polynomials::<F>(degree, seed);
    let at: Vec<F> = (0..samples as u64).map(F::new).collect();
    let width = fc.len();

    let mut horner = vec![F::zero(); samples * width];
    let mut differenced = vec![F::zero(); samples * width];
    by_horner(&fc, &at, &mut horner);
    by_differences(&fc, &at, &mut differenced);
    if let Some(index) = first_mismatch(&horner, &differenced) {
        panic!(
            "the differenced specialization disagrees with Horner at flat index {} (sample {}, \
             coefficient {}): {} against {}. The comparison would be meaningless.",
            index,
            index / width,
            index % width,
            horner[index],
            differenced[index],
        );
    }

    let mut best = (Duration::MAX, Duration::MAX);
    let mut spent = Duration::ZERO;
    let mut taken = 0;
    while taken < MAX_REPETITIONS && spent < PAIR_BUDGET {
        let start = Instant::now();
        by_horner(&fc, &at, &mut horner);
        let h = start.elapsed();
        std::hint::black_box(&horner);

        let start = Instant::now();
        by_differences(&fc, &at, &mut differenced);
        let d = start.elapsed();
        std::hint::black_box(&differenced);

        best.0 = best.0.min(h);
        best.1 = best.1.min(d);
        spent += h + d;
        taken += 1;
    }

    println!(
        "| {:<28} | {:>7} | {:>8} | {:>11.6} | {:>11.6} | {:>8.2} | {:>5} |",
        name,
        degree,
        samples,
        best.0.as_secs_f64(),
        best.1.as_secs_f64(),
        best.0.as_secs_f64() / best.1.as_secs_f64(),
        taken,
    );
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let mut degree = 243usize;
    let mut samples = 4096usize;
    let mut index = 0;
    while index < arguments.len() {
        match arguments[index].as_str() {
            "--degree" => {
                degree = arguments[index + 1]
                    .parse()
                    .expect("--degree wants an integer");
                index += 2;
            }
            "--samples" => {
                samples = arguments[index + 1]
                    .parse()
                    .expect("--samples wants an integer");
                index += 2;
            }
            other => panic!("unknown argument {other}"),
        }
    }

    println!("# The per-sample specialization against a forward-difference batch");
    println!("\nISA: {}", zeebra::util::isa_floor());
    println!(
        "\nIssue #598. Both arms produce the same {}-wide columns, asserted before timing.",
        degree + 1
    );
    println!("\n- `fc[j]` has degree `degree - j`, the shape a CICO row produces");
    println!("- the operation count is the same on both arms; only the operation differs");
    println!();
    println!(
        "| {:<28} | {:>7} | {:>8} | {:>11} | {:>11} | {:>8} | {:>5} |",
        "field", "degree", "samples", "horner/s", "diffs/s", "speedup", "reps"
    );
    println!("{}", rule(&[30, 9, 10, 13, 13, 10, 7]));

    measure::<KoalaBear>("KoalaBear, 4 bytes", degree, samples, 0x0598_0001);
    measure::<Goldilocks>("Goldilocks, 8 bytes", degree, samples, 0x0598_0002);
    measure::<Bn254Fr>("BN254 Fr, 32 bytes", degree, samples, 0x0598_0003);

    match peak_resident_bytes() {
        Some(bytes) => println!(
            "\n\nprocess peak resident set: {} bytes ({:.1} MiB)",
            bytes,
            bytes as f64 / (1024.0 * 1024.0)
        ),
        None => println!("\n\nprocess peak resident set: unavailable on this platform"),
    }
}
