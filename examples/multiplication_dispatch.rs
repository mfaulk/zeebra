//! Where each of the three multiplication routes wins, and so what `fft_multiplication_crossover`
//! should be (#185).
//!
//! `fft_multiplication_crossover`'s figures were measured **schoolbook against the transform**,
//! first by #124 and then re-measured one doubling lower by #161. Neither is the threshold the
//! dispatcher needs once Karatsuba sits between them: the question is **Karatsuba against the
//! transform**, and since #165 measures Karatsuba at 10.7x–22.9x schoolbook at `2^14`, that
//! crossing is *higher* than the schoolbook one rather than equal to it. Reusing the schoolbook
//! figure would select the transform inside the band Karatsuba still owns.
//!
//! Three arms per size, all reached through the shipped public API so that what is measured is the
//! dispatched path and not a kernel in isolation:
//!
//! 1. **schoolbook** — `&a * &b`, `DensePolynomial`'s `Mul`
//! 2. **dense** — `multiply_above(a, b, u32::MAX, rng)`, which can never reach the transform, so
//!    it is exactly `multiply_dense`: schoolbook below `karatsuba_base_case` and Karatsuba above
//! 3. **ntt** — `multiply_above(a, b, 0, rng)`, which always attempts the transform
//!
//! Arm 3 over a field whose two-adicity cannot host the domain falls back to arm 2 by design, so on
//! Mersenne-31 the `ntt` column measures the fallback and is marked rather than read as a transform.
//!
//! Interleaved within each repetition and the minimum taken, because this workstation runs
//! concurrent builds; `taskset` pinning is still the caller's job. The arms are checked against
//! each other once per size outside the timing — a crossover measured against a wrong answer is
//! worthless.
//!
//! ```text
//! cargo run --release --example multiplication_dispatch
//! cargo run --release --example multiplication_dispatch -- list
//! cargo run --release --example multiplication_dispatch -- koalabear max_log=17
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, KoalaBear, Mersenne31, PrimeFieldElement64},
    karatsuba_base_case_unstable, multiply_above, FiniteField, KnownOrder, Polynomial,
    UnivariatePolynomial,
};

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// A Proth prime with two-adicity 16, the 8-byte field `fft::multiply`'s own tests use.
type Zp65537 = PrimeFieldElement64<65537>;

/// The sweep runs operand lengths `2^FIRST_LOG ..= 2^max_log`.
const FIRST_LOG: u32 = 4;

/// Default top of the sweep, in operand length. The product degree is twice this.
const DEFAULT_MAX_LOG: u32 = 14;

/// Operand length above which the schoolbook arm is skipped rather than run. Quadratic: at `2^15`
/// one product is about a billion field multiplications, and the arm is only there as the baseline
/// the other two are already known to beat.
const SCHOOLBOOK_LENGTH_CAP: usize = 1 << 14;

/// Each arm's time is its fastest over at most this many interleaved repetitions.
const MAX_REPETITIONS: usize = 7;

/// Target wall time for all repetitions at one size.
const SIZE_BUDGET: Duration = Duration::from_millis(500);

/// One arm's result at one size.
#[derive(Clone, Copy)]
enum Arm {
    Timed(Duration),
    Skipped,
}

impl Arm {
    fn duration(self) -> Option<Duration> {
        match self {
            Arm::Timed(time) => Some(time),
            Arm::Skipped => None,
        }
    }
}

struct Row {
    length: usize,
    product_degree: usize,
    schoolbook: Arm,
    dense: Arm,
    ntt: Arm,
    /// False when the field's two-adicity cannot host the domain this product needs, in which case
    /// the `ntt` arm measured the `multiply_dense` fallback and must not enter the crossing.
    transform_available: bool,
}

fn polynomial<F: FiniteField>(len: usize, seed: u64) -> UnivariatePolynomial<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut coefficients: Vec<F> = (0..len).map(|_| F::random(&mut rng)).collect();
    // Exactly degree `len - 1`: a zero leading coefficient would shorten the product and make the
    // product degree the sweep reports a lie.
    while coefficients[len - 1].is_zero() {
        coefficients[len - 1] = F::random(&mut rng);
    }
    UnivariatePolynomial::new(&coefficients)
}

/// The three arms at one size. `with_schoolbook` is false above [`SCHOOLBOOK_LENGTH_CAP`];
/// `transform_available` is false where the field's two-adicity cannot host the domain, and the
/// third arm then measures the `multiply_dense` fallback that `multiply_above` takes there.
fn measure<F: KnownOrder>(len: usize, with_schoolbook: bool, transform_available: bool) -> Row {
    let a = polynomial::<F>(len, len as u64 * 31 + 5);
    let b = polynomial::<F>(len, len as u64 * 37 + 7);
    let mut rng = StdRng::seed_from_u64(0x185);

    // Agreement first, outside the timing. The dense arm is checked against schoolbook only where
    // schoolbook is affordable; above the cap the two transform-side arms still check each other,
    // and the unit tests carry the coefficient-for-coefficient agreement at every length.
    let dense = multiply_above(&a, &b, u32::MAX, &mut rng);
    let ntt = multiply_above(&a, &b, 0, &mut rng);
    assert_eq!(dense, ntt, "dense and ntt disagree at length {len}");
    if with_schoolbook {
        assert_eq!(
            &a * &b,
            dense,
            "schoolbook and dense disagree at length {len}"
        );
    }
    let product_degree = dense.degree() as usize;
    drop(dense);
    drop(ntt);

    let mut best = [Duration::MAX; 3];
    let mut spent = Duration::ZERO;
    let mut taken = 0;
    while taken < MAX_REPETITIONS && spent < SIZE_BUDGET {
        for (index, slot) in best.iter_mut().enumerate() {
            if index == 0 && !with_schoolbook {
                continue;
            }
            let start = Instant::now();
            match index {
                0 => drop(&a * &b),
                1 => drop(multiply_above(&a, &b, u32::MAX, &mut rng)),
                _ => drop(multiply_above(&a, &b, 0, &mut rng)),
            }
            let elapsed = start.elapsed();
            *slot = (*slot).min(elapsed);
            spent += elapsed;
        }
        taken += 1;
    }

    Row {
        length: len,
        product_degree,
        schoolbook: if with_schoolbook {
            Arm::Timed(best[0])
        } else {
            Arm::Skipped
        },
        dense: Arm::Timed(best[1]),
        ntt: Arm::Timed(best[2]),
        transform_available,
    }
}

fn micros(arm: Arm) -> String {
    match arm {
        Arm::Timed(time) => format!("{:.1}", time.as_secs_f64() * 1e6),
        Arm::Skipped => "skipped".to_string(),
    }
}

fn ratio(numerator: Arm, denominator: Arm) -> String {
    match (numerator.duration(), denominator.duration()) {
        (Some(n), Some(d)) if d > Duration::ZERO => {
            format!("{:.2}x", n.as_secs_f64() / d.as_secs_f64())
        }
        _ => "-".to_string(),
    }
}

fn sweep<F: KnownOrder>(name: &str, max_log: u32) {
    let width = std::mem::size_of::<F>();
    let two_adicity = F::two_adicity();
    println!(
        "\n## {name} — {width} B element, two-adicity {two_adicity}, Karatsuba base case {}",
        karatsuba_base_case_unstable::<F>()
    );
    // A product of degree d needs d+1 points, rounded up to a power of two, so the transform is
    // available only while that exponent is within the field's two-adicity. Stated rather than
    // discovered as a fallback, so the `ntt` column is never silently arm 2.
    println!(
        "| operand len | product deg | schoolbook us | dense us | ntt us | school/dense | dense/ntt |"
    );
    println!("|---:|---:|---:|---:|---:|---:|---:|");

    let mut rows = Vec::new();
    for log in FIRST_LOG..=max_log {
        let len = 1usize << log;
        let points = (2 * len - 1).next_power_of_two();
        let available = points.trailing_zeros() <= two_adicity;
        let row = measure::<F>(len, len <= SCHOOLBOOK_LENGTH_CAP, available);
        println!(
            "| {} | {} | {} | {} | {}{} | {} | {} |",
            row.length,
            row.product_degree,
            micros(row.schoolbook),
            micros(row.dense),
            micros(row.ntt),
            if available { "" } else { " *(fallback)*" },
            ratio(row.schoolbook, row.dense),
            if available {
                ratio(row.dense, row.ntt)
            } else {
                "-".to_string()
            },
        );
        rows.push(row);
    }

    // The crossing: the smallest measured product degree at which the transform beats the dense
    // route. Reported as a bracket, since the sweep doubles.
    let crossing = rows.windows(2).find_map(|pair| {
        let (below, above) = (&pair[0], &pair[1]);
        let faster = |row: &Row| match (row.dense.duration(), row.ntt.duration()) {
            (Some(d), Some(n)) if row.transform_available => Some(n < d),
            _ => None,
        };
        match (faster(below), faster(above)) {
            (Some(false), Some(true)) => Some((below.product_degree, above.product_degree)),
            _ => None,
        }
    });
    match crossing {
        Some((below, above)) => println!(
            "\n**Karatsuba-vs-transform crossing is in ({below}, {above}] product degree.** \
             Rounded up to a power of two as #124 rounds: **{}**.",
            (above + 1).next_power_of_two()
        ),
        None => {
            if rows.iter().all(|row| !row.transform_available) {
                println!(
                    "\n**The transform is unavailable at every size swept** — two-adicity \
                     {two_adicity} hosts no domain past {} points, so `multiply_above` takes the \
                     `multiply_dense` fallback throughout and the `school/dense` column is the \
                     whole of what this issue buys here.",
                    1usize << two_adicity
                );
                return;
            }
            let all_ntt = rows
                .iter()
                .all(|row| match (row.dense.duration(), row.ntt.duration()) {
                    (Some(d), Some(n)) if row.transform_available => n < d,
                    _ => false,
                });
            if all_ntt && !rows.is_empty() {
                println!(
                    "\n**The transform wins at every size swept**, from product degree {}. \
                     The crossing is below the sweep.",
                    rows[0].product_degree
                );
            } else {
                println!(
                    "\n**No crossing inside the sweep**: the dense route wins at every size up to \
                     product degree {}. Raise `max_log`.",
                    rows.last().map(|row| row.product_degree).unwrap_or(0)
                );
            }
        }
    }
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let max_log = arguments
        .iter()
        .find_map(|a| a.strip_prefix("max_log="))
        .and_then(|n| n.parse().ok())
        .unwrap_or(DEFAULT_MAX_LOG);
    let named: Vec<&str> = arguments
        .iter()
        .filter(|a| !a.contains('='))
        .map(|a| a.as_str())
        .collect();

    if named.first() == Some(&"list") {
        println!("koalabear mersenne31 zp65537 goldilocks bn254");
        return;
    }

    let wanted = |field: &str| named.is_empty() || named.contains(&"all") || named.contains(&field);

    println!("# Multiplication dispatch: schoolbook, Karatsuba, transform (#185)");
    println!(
        "\nOperand lengths `2^{FIRST_LOG}..=2^{max_log}`; schoolbook skipped above length {}. \
         Minimum of up to {MAX_REPETITIONS} interleaved repetitions.",
        SCHOOLBOOK_LENGTH_CAP
    );

    if wanted("koalabear") {
        sweep::<KoalaBear>("KoalaBear", max_log);
    }
    if wanted("mersenne31") {
        sweep::<Mersenne31>("Mersenne-31", max_log);
    }
    if wanted("zp65537") {
        sweep::<Zp65537>("Zp65537", max_log);
    }
    if wanted("goldilocks") {
        sweep::<Goldilocks>("Goldilocks", max_log);
    }
    if wanted("bn254") {
        sweep::<Bn254Fr>("BN254 Fr", max_log);
    }
}
