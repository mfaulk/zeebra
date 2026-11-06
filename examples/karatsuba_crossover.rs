//! Where Karatsuba starts beating schoolbook, measured separately per field element width.
//!
//! Issue #165. The crossover cannot be one number for the whole crate: Karatsuba trades
//! multiplications for additions, and a field multiply costs about 1.7 ns over a 64-bit prime
//! field against about 18.7 ns over BN254 `Fr`, so the trade is nearly free on the wide field and
//! comparatively expensive on the narrow one. This binary measures the base case and the degree
//! crossover for each width rather than assuming one.
//!
//! It lives here rather than as a seventh row in `examples/univariate_scaling.rs` for two
//! reasons. The sweep is an interleaved A/B of two implementations at the same size, which that
//! example's doubling harness does not express; and that example's `mul` row measures
//! `DensePolynomial`'s `Mul`, which this change deliberately does not touch — the multiplication
//! dispatcher is #124's.
//!
//! Both arms are the same code path through `karatsuba_unstable`, differing only in the base
//! case: `usize::MAX` never recurses and so is plain schoolbook. That keeps the inner kernel
//! identical on both sides, so the measured difference is the recursion and nothing else.
//!
//! ```text
//! cargo run --release --example karatsuba_crossover
//! cargo run --release --example karatsuba_crossover -- bn254
//! cargo run --release --example karatsuba_crossover -- all max_log=12
//! ```

use std::{
    alloc::{GlobalAlloc, Layout, System},
    sync::atomic::{AtomicUsize, Ordering},
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, Mersenne31, PrimeFieldElement64},
    karatsuba_base_case_unstable, karatsuba_unstable,
    util::peak_resident_bytes,
    FiniteField, UnivariatePolynomial,
};

/// Mersenne-31 backed by a `u64`, the width `examples/univariate_scaling.rs` reports over.
type Mersenne31In64 = PrimeFieldElement64<2_147_483_647>;

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// Plain schoolbook: a base case this large is never recursed past.
const SCHOOLBOOK: usize = usize::MAX;

/// Base cases swept when locating the crossover.
const BASE_CASES: [usize; 10] = [2, 4, 8, 12, 16, 24, 32, 48, 64, 128];

/// The degree sweep runs from `2^FIRST_LOG` to `2^max_log`.
const FIRST_LOG: u32 = 4;

/// Each arm's time is its fastest over at most this many interleaved repetitions of the whole
/// grid, or fewer when one pass already costs more than `GRID_BUDGET`.
const MAX_REPETITIONS: usize = 9;

/// Target wall time for all repetitions of one size's grid.
const GRID_BUDGET: Duration = Duration::from_millis(400);

// === the allocator ===

/// Counts live heap bytes, so a measurement's peak is exact rather than estimated. Same
/// instrument as `examples/univariate_scaling.rs`, for figures that compare directly with §3.2's.
struct Tracking;

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

fn grew(bytes: usize) {
    let live = LIVE.fetch_add(bytes, Ordering::Relaxed) + bytes;
    PEAK.fetch_max(live, Ordering::Relaxed);
}

unsafe impl GlobalAlloc for Tracking {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pointer = System.alloc(layout);
        if !pointer.is_null() {
            grew(layout.size());
        }
        pointer
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
        System.dealloc(pointer, layout);
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let moved = System.realloc(pointer, layout, new_size);
        if !moved.is_null() {
            if new_size >= layout.size() {
                grew(new_size - layout.size());
            } else {
                LIVE.fetch_sub(layout.size() - new_size, Ordering::Relaxed);
            }
        }
        moved
    }
}

#[global_allocator]
static ALLOCATOR: Tracking = Tracking;

/// Peak live heap bytes added by `work`, discarding its value.
fn peak_bytes<T>(work: impl FnOnce() -> T) -> usize {
    let baseline = LIVE.load(Ordering::Relaxed);
    PEAK.store(baseline, Ordering::Relaxed);
    let value = work();
    let peak = PEAK.load(Ordering::Relaxed).saturating_sub(baseline);
    drop(value);
    peak
}

// === timing ===

fn operands<F: FiniteField>(len: usize, seed: u64) -> (Vec<F>, Vec<F>) {
    let mut rng = StdRng::seed_from_u64(seed);
    let a = (0..len).map(|_| F::random(&mut rng)).collect();
    let b = (0..len).map(|_| F::random(&mut rng)).collect();
    (a, b)
}

/// Least-squares slope of `log2(seconds)` against `log2(size)` over the given points, which is
/// the scaling exponent: 2 is quadratic and `log2(3) = 1.585` is Karatsuba's asymptote.
fn exponent(points: &[(usize, Duration)]) -> f64 {
    let n = points.len() as f64;
    if n < 2.0 {
        return f64::NAN;
    }
    let xs: Vec<f64> = points
        .iter()
        .map(|(size, _)| (*size as f64).log2())
        .collect();
    let ys: Vec<f64> = points
        .iter()
        .map(|(_, time)| time.as_secs_f64().log2())
        .collect();
    let mean_x = xs.iter().sum::<f64>() / n;
    let mean_y = ys.iter().sum::<f64>() / n;
    let covariance: f64 = xs
        .iter()
        .zip(ys.iter())
        .map(|(x, y)| (x - mean_x) * (y - mean_y))
        .sum();
    let variance: f64 = xs.iter().map(|x| (x - mean_x).powi(2)).sum();
    covariance / variance
}

fn rule(widths: &[usize]) -> String {
    let mut line = String::from("|");
    for width in widths {
        line.push_str(&"-".repeat(*width));
        line.push('|');
    }
    line
}

// === the sweep ===

/// Every arm at one size, interleaved: plain schoolbook first, then Karatsuba at each candidate
/// base case, repeated until the budget is spent. The returned times are each arm's fastest.
///
/// Interleaved within the repetition rather than arm by arm so that a transient on this shared
/// workstation lands on every arm. The arms are also checked against each other once, outside the
/// timing: a crossover measured against a wrong answer is worthless.
fn grid<F: FiniteField>(a: &[F], b: &[F]) -> Vec<Duration> {
    let arms: Vec<usize> = std::iter::once(SCHOOLBOOK)
        .chain(BASE_CASES.iter().copied())
        .collect();
    let reference = karatsuba_unstable(a, b, SCHOOLBOOK);
    for arm in &arms {
        assert_eq!(
            karatsuba_unstable(a, b, *arm),
            reference,
            "base case {} disagrees with schoolbook",
            arm
        );
    }
    drop(reference);

    let mut best = vec![Duration::MAX; arms.len()];
    let mut spent = Duration::ZERO;
    let mut taken = 0;
    while taken < MAX_REPETITIONS && spent < GRID_BUDGET {
        for (index, arm) in arms.iter().enumerate() {
            let start = Instant::now();
            drop(karatsuba_unstable(a, b, *arm));
            let elapsed = start.elapsed();
            best[index] = best[index].min(elapsed);
            spent += elapsed;
        }
        taken += 1;
    }
    best
}

/// A base case's label: `usize::MAX` is the schoolbook arm.
fn label(base_case: usize) -> String {
    if base_case == SCHOOLBOOK {
        "school".to_string()
    } else {
        base_case.to_string()
    }
}

/// The whole grid over one field: every base case at every size, then the summary the crossover
/// and the scaling exponents are read off.
fn sweep<F: FiniteField>(seed: u64, max_log: u32) {
    let compiled_in = karatsuba_base_case_unstable::<F>();
    let arms: Vec<usize> = std::iter::once(SCHOOLBOOK)
        .chain(BASE_CASES.iter().copied())
        .collect();
    let compiled_column = arms
        .iter()
        .position(|arm| *arm == compiled_in)
        .expect("the compiled-in base case must be one of the swept arms");

    println!("\nseconds per arm — columns are the schoolbook base case the recursion stops at");
    print!("| {:>5} | {:>8} |", "log2", "n");
    for arm in &arms {
        print!(" {:>10} |", label(*arm));
    }
    println!();
    let mut widths = vec![7, 10];
    widths.extend(arms.iter().map(|_| 12));
    println!("{}", rule(&widths));

    let mut rows: Vec<(usize, Vec<Duration>, usize, usize)> = Vec::new();
    for log_len in FIRST_LOG..=max_log {
        let n = 1usize << log_len;
        let (a, b) = operands::<F>(n, seed ^ u64::from(log_len));
        let times = grid(&a, &b);
        let school_bytes = peak_bytes(|| karatsuba_unstable(&a, &b, SCHOOLBOOK));
        let kara_bytes = peak_bytes(|| karatsuba_unstable(&a, &b, compiled_in));
        print!("| {:>5} | {:>8} |", log_len, n);
        for time in &times {
            print!(" {:>10.6} |", time.as_secs_f64());
        }
        println!();
        rows.push((n, times, school_bytes, kara_bytes));
    }

    // === the summary ===

    println!(
        "\nsummary — `chosen` is the compiled-in base case for this width, {}; `best` is the \
         fastest arm at that size",
        compiled_in
    );
    println!(
        "| {:>5} | {:>8} | {:>11} | {:>11} | {:>8} | {:>6} | {:>11} | {:>8} | {:>8} | {:>8} | \
         {:>10} | {:>10} |",
        "log2",
        "n",
        "school s",
        "chosen s",
        "speedup",
        "best",
        "best s",
        "best up",
        "school e",
        "chosen e",
        "school n*B",
        "chosen n*B"
    );
    println!("{}", rule(&[7, 10, 13, 13, 10, 8, 13, 10, 10, 10, 12, 12]));

    let mut school_points: Vec<(usize, Duration)> = Vec::new();
    let mut chosen_points: Vec<(usize, Duration)> = Vec::new();
    let mut crossover: Option<usize> = None;
    let mut best_crossover: Option<usize> = None;
    let mut best_at_largest = SCHOOLBOOK;

    for (n, times, school_bytes, kara_bytes) in &rows {
        let school = times[0];
        let chosen = times[compiled_column];
        let (best_index, best_time) = times
            .iter()
            .enumerate()
            .min_by_key(|(_, time)| **time)
            .map(|(index, time)| (index, *time))
            .expect("a row has at least the schoolbook arm");
        best_at_largest = arms[best_index];

        let local = |points: &Vec<(usize, Duration)>, time: Duration| match points.last() {
            Some((_, previous)) if previous.as_secs_f64() > 0.0 => {
                format!(
                    "{:.2}",
                    (time.as_secs_f64() / previous.as_secs_f64()).log2()
                )
            }
            _ => "-".to_string(),
        };
        let school_exponent = local(&school_points, school);
        let chosen_exponent = local(&chosen_points, chosen);

        let speedup = school.as_secs_f64() / chosen.as_secs_f64();
        let best_speedup = school.as_secs_f64() / best_time.as_secs_f64();
        if crossover.is_none() && speedup > 1.0 {
            crossover = Some(*n);
        }
        if best_crossover.is_none() && best_index != 0 {
            best_crossover = Some(*n);
        }
        let per_coefficient = (*n * std::mem::size_of::<F>()) as f64;
        println!(
            "| {:>5} | {:>8} | {:>11.6} | {:>11.6} | {:>8.2} | {:>6} | {:>11.6} | {:>8.2} | \
             {:>8} | {:>8} | {:>10.2} | {:>10.2} |",
            n.trailing_zeros(),
            n,
            school.as_secs_f64(),
            chosen.as_secs_f64(),
            speedup,
            label(arms[best_index]),
            best_time.as_secs_f64(),
            best_speedup,
            school_exponent,
            chosen_exponent,
            *school_bytes as f64 / per_coefficient,
            *kara_bytes as f64 / per_coefficient,
        );
        school_points.push((*n, school));
        chosen_points.push((*n, chosen));
    }

    match crossover {
        Some(n) => println!(
            "- crossover at the compiled-in base case {}: Karatsuba is first faster at n = {}",
            compiled_in, n
        ),
        None => println!(
            "- crossover at the compiled-in base case {}: NONE — schoolbook wins at every size \
             up to 2^{}",
            compiled_in, max_log
        ),
    }
    match best_crossover {
        Some(n) => println!(
            "- crossover for the best arm at each size: Karatsuba is first faster at n = {}",
            n
        ),
        None => println!(
            "- crossover for the best arm at each size: NONE up to 2^{} — this is a null result \
             and should be reported as one",
            max_log
        ),
    }
    println!(
        "- fastest arm at the largest size measured: {}",
        label(best_at_largest)
    );

    // Fitted over the top half of the sweep only: the small sizes are where the constant factor
    // dominates, and they drag a single fit away from the asymptote in both arms alike.
    let tail = school_points.len() / 2;
    println!(
        "- fitted exponent over the largest {} rows: schoolbook {:.3}, Karatsuba {:.3} \
         (quadratic is 2.000, Karatsuba's asymptote is log2(3) = 1.585)",
        school_points.len() - tail,
        exponent(&school_points[tail..]),
        exponent(&chosen_points[tail..]),
    );
}

/// One field's grid, summary and memory figures, with its element width stated.
fn measure_field<F: FiniteField>(name: &str, seed: u64, max_log: u32) {
    println!("\n\n## {}", name);
    println!("\n- an element is {} bytes", std::mem::size_of::<F>());
    sweep::<F>(seed, max_log);

    // What the product costs once it is a polynomial rather than a coefficient slice, which is
    // the shape a dispatcher hands back and the shape §3.2's `4 n B` for `mul` was measured in.
    let n = 1usize << max_log.min(10);
    let (a, b) = operands::<F>(n, seed);
    let base_case = karatsuba_base_case_unstable::<F>();
    let through_new =
        peak_bytes(|| UnivariatePolynomial::<F>::new(&karatsuba_unstable(&a, &b, base_case)));
    let mul_peak = {
        let f = UnivariatePolynomial::<F>::new(&a);
        let g = UnivariatePolynomial::<F>::new(&b);
        peak_bytes(|| &f * &g)
    };
    let per_coefficient = (n * std::mem::size_of::<F>()) as f64;
    println!(
        "- at n = {}: `Mul` peaks at {} bytes ({:.2} n B), Karatsuba through \
         `UnivariatePolynomial::new` at {} bytes ({:.2} n B)",
        n,
        mul_peak,
        mul_peak as f64 / per_coefficient,
        through_new,
        through_new as f64 / per_coefficient,
    );
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let mut max_log = 14;
    let mut which = "all".to_string();
    for argument in &arguments {
        match argument.strip_prefix("max_log=") {
            Some(value) => max_log = value.parse().expect("max_log must be an integer"),
            None => which = argument.clone(),
        }
    }

    println!("# Karatsuba against schoolbook, per field element width");
    println!("\nISA: {}", zeebra::util::isa_floor());
    println!("\nIssue #165. Both arms are the same code, differing only in the base case;");
    println!("`schoolbook` is a base case so large the recursion never fires.");
    println!(
        "\n- each timed figure is the fastest of up to {MAX_REPETITIONS} interleaved repetitions"
    );
    println!("- sizes from 2^{FIRST_LOG} to 2^{max_log}, operand lengths in coefficients");

    if which == "all" || which == "mersenne31" {
        measure_field::<Mersenne31>("Mersenne-31, 32-bit backing", 0x1651, max_log);
    }
    if which == "all" || which == "mersenne31-64" {
        measure_field::<Mersenne31In64>("Mersenne-31, 64-bit backing", 0x1652, max_log);
    }
    if which == "all" || which == "goldilocks" {
        measure_field::<Goldilocks>("Goldilocks", 0x1653, max_log);
    }
    if which == "all" || which == "bn254" {
        measure_field::<Bn254Fr>("BN254 Fr", 0x1654, max_log);
    }

    match peak_resident_bytes() {
        Some(bytes) => println!(
            "\n\nprocess peak resident set: {} bytes ({:.1} MiB)",
            bytes,
            bytes as f64 / (1024.0 * 1024.0)
        ),
        None => println!("\n\nprocess peak resident set: unavailable on this platform"),
    }
}
