//! Where Newton inversion of the reversed divisor starts beating long division, per element width.
//!
//! Issue #193. Long division costs `k * m` field multiplications for a quotient of length `k`
//! against a divisor of length `m`, in a tight in-place loop that vectorizes and allocates
//! nothing. Newton costs a constant multiple of `M(k)` plus an asymmetric product for the
//! remainder recovery, and since #231 `M` is Karatsuba, so the asymptotics favour it — but with
//! several multiplications per iteration against long division's single pass, and an allocation
//! per iteration. The asymptotic crossing is not where the measured one is, which is what this
//! binary is for.
//!
//! Two things are measured, not one:
//!
//! - **The balanced sweep**, `deg f = 2d - 2` by `deg g = d - 1`, which is the shape
//!   `examples/univariate_scaling.rs`'s `div` row uses and the shape every `pow_mod` squaring
//!   produces. This is what the shipped constant is read off.
//! - **The skew check**, the same total work redistributed between `k` and `m`. The dispatch rule
//!   is **asymmetric** in the two rather than a threshold on either or on their minimum, because
//!   Newton's precision is `k` and so its cost barely sees `m` at all, while long division pays
//!   every one of the `k * m` steps. This table is the evidence for that asymmetry, and the first
//!   version of it is what caught a symmetric `min(k, m)` rule taking long division at `k = 1024,
//!   m = 65536` where Newton is 3.6x faster.
//!
//! Both arms run through the same `div_with_remainder` entry points, forced to one route each, so
//! the measured difference is the algorithm and not the wrapping.
//!
//! ```text
//! cargo run --release --example division_crossover
//! cargo run --release --example division_crossover -- bn254
//! cargo run --release --example division_crossover -- all max_log=13
//! ```

use std::{
    alloc::{GlobalAlloc, Layout, System},
    sync::atomic::{AtomicUsize, Ordering},
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    div_with_remainder_long_unstable, div_with_remainder_newton_unstable,
    fields::{Bn254Fr, Mersenne31, PrimeFieldElement64},
    newton_crossover_unstable, newton_floor_unstable, newton_is_cheaper_at_unstable,
    newton_is_cheaper_unstable,
    util::peak_resident_bytes,
    FiniteField, Polynomial, UnivariatePolynomial,
};

/// Mersenne-31 backed by a `u64`, the width `examples/univariate_scaling.rs` reports over.
type Mersenne31In64 = PrimeFieldElement64<2_147_483_647>;

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// The balanced sweep runs from `2^FIRST_LOG` to `2^max_log` in the divisor's length.
const FIRST_LOG: u32 = 4;

/// Each arm's time is its fastest over at most this many interleaved repetitions, or fewer when
/// one pass already costs more than `PAIR_BUDGET`.
const MAX_REPETITIONS: usize = 7;

/// Target wall time for all repetitions at one size.
const PAIR_BUDGET: Duration = Duration::from_millis(600);

/// Skews measured either side of the base length: `k = base * ratio` against `m = base`, and the
/// same pair the other way round.
const SKEW_RATIOS: [usize; 4] = [1, 4, 16, 64];

// === the allocator ===

/// Counts live heap bytes, so a measurement's peak is exact rather than estimated. Same instrument
/// as `examples/karatsuba_crossover.rs` and `examples/univariate_scaling.rs`, for figures that
/// compare directly with theirs.
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

fn rule(widths: &[usize]) -> String {
    let mut line = String::from("|");
    for width in widths {
        line.push_str(&"-".repeat(*width));
        line.push('|');
    }
    line
}

/// A dividend of length `quotient_len + divisor_len - 1` and a divisor of length `divisor_len`,
/// both with a non-zero leading coefficient so the lengths are the degrees they claim to be.
fn operands<F: FiniteField>(
    quotient_len: usize,
    divisor_len: usize,
    seed: u64,
) -> (UnivariatePolynomial<F>, UnivariatePolynomial<F>) {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut make = |len: usize| {
        let mut c: Vec<F> = (0..len).map(|_| F::random(&mut rng)).collect();
        if c[len - 1].is_zero() {
            c[len - 1] = F::one();
        }
        UnivariatePolynomial::<F>::new(&c)
    };
    let dividend = make(quotient_len + divisor_len - 1);
    let divisor = make(divisor_len);
    (dividend, divisor)
}

/// Least-squares slope of `log2(seconds)` against `log2(size)`, which is the scaling exponent: 2
/// is quadratic and `log2(3) = 1.585` is the asymptote of the product Newton is built from.
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

/// Both arms at one shape, interleaved, each reported as its fastest pass.
///
/// Interleaved within the repetition rather than arm by arm so that a transient on this shared
/// workstation lands on both. The arms are also checked against each other once, outside the
/// timing: a crossover measured against a wrong answer is worthless.
fn pair<F: FiniteField>(
    dividend: &UnivariatePolynomial<F>,
    divisor: &UnivariatePolynomial<F>,
) -> (Duration, Duration) {
    assert_eq!(
        div_with_remainder_long_unstable(dividend, divisor),
        div_with_remainder_newton_unstable(dividend, divisor),
        "the two routes disagree at deg f = {}, deg g = {}",
        dividend.degree(),
        divisor.degree()
    );

    let mut best = (Duration::MAX, Duration::MAX);
    let mut spent = Duration::ZERO;
    let mut taken = 0;
    while taken < MAX_REPETITIONS && spent < PAIR_BUDGET {
        let start = Instant::now();
        drop(div_with_remainder_long_unstable(dividend, divisor));
        let long = start.elapsed();

        let start = Instant::now();
        drop(div_with_remainder_newton_unstable(dividend, divisor));
        let newton = start.elapsed();

        best.0 = best.0.min(long);
        best.1 = best.1.min(newton);
        spent += long + newton;
        taken += 1;
    }
    best
}

/// The balanced sweep over one field, and the crossover read off it.
fn balanced<F: FiniteField>(seed: u64, max_log: u32) {
    let compiled_in = newton_crossover_unstable::<F>();

    println!("\nbalanced: degree 2d-2 by degree d-1, as `pow_mod` reduces");
    println!(
        "| {:>5} | {:>8} | {:>11} | {:>11} | {:>8} | {:>8} | {:>8} | {:>8} | {:>10} | {:>10} |",
        "log2",
        "d",
        "long s",
        "newton s",
        "speedup",
        "rule",
        "long e",
        "newton e",
        "long n*B",
        "newton n*B"
    );
    println!("{}", rule(&[7, 10, 13, 13, 10, 10, 10, 10, 12, 12]));

    let mut long_points: Vec<(usize, Duration)> = Vec::new();
    let mut newton_points: Vec<(usize, Duration)> = Vec::new();
    let mut crossover: Option<usize> = None;
    let mut clear_crossover: Option<usize> = None;
    let mut rule_crossover: Option<usize> = None;

    for log_d in FIRST_LOG..=max_log {
        let d = 1usize << log_d;
        // A quotient of length d against a divisor of length d, so `min = max = d` and the
        // dispatch rule reduces to `d > compiled_in`.
        let (dividend, divisor) = operands::<F>(d, d, seed ^ u64::from(log_d));
        let (long, newton) = pair(&dividend, &divisor);
        let long_bytes = peak_bytes(|| div_with_remainder_long_unstable(&dividend, &divisor));
        let newton_bytes = peak_bytes(|| div_with_remainder_newton_unstable(&dividend, &divisor));

        let local = |points: &Vec<(usize, Duration)>, time: Duration| match points.last() {
            Some((_, previous)) if previous.as_secs_f64() > 0.0 => {
                format!(
                    "{:.2}",
                    (time.as_secs_f64() / previous.as_secs_f64()).log2()
                )
            }
            _ => "-".to_string(),
        };
        let long_exponent = local(&long_points, long);
        let newton_exponent = local(&newton_points, newton);

        let speedup = long.as_secs_f64() / newton.as_secs_f64();
        let chose_newton = newton_is_cheaper_at_unstable(d, d, compiled_in);
        if crossover.is_none() && speedup > 1.0 {
            crossover = Some(d);
        }
        // A 1.01x speedup is a tie on this workstation, not a crossing. The constant is read off
        // the first *clear* win, because a tie is where the two routes cost the same and either
        // choice is defensible — and the shipped rule should prefer the one that allocates less.
        if clear_crossover.is_none() && speedup > 1.1 {
            clear_crossover = Some(d);
        }
        if rule_crossover.is_none() && chose_newton {
            rule_crossover = Some(d);
        }

        let per_coefficient = (d * std::mem::size_of::<F>()) as f64;
        println!(
            "| {:>5} | {:>8} | {:>11.6} | {:>11.6} | {:>8.2} | {:>8} | {:>8} | {:>8} | \
             {:>10.2} | {:>10.2} |",
            log_d,
            d,
            long.as_secs_f64(),
            newton.as_secs_f64(),
            speedup,
            if chose_newton { "newton" } else { "long" },
            long_exponent,
            newton_exponent,
            long_bytes as f64 / per_coefficient,
            newton_bytes as f64 / per_coefficient,
        );
        long_points.push((d, long));
        newton_points.push((d, newton));
    }

    match clear_crossover {
        Some(d) => println!(
            "- measured: Newton is first faster by more than 10% at d = {}",
            d
        ),
        None => println!(
            "- measured: Newton is nowhere faster by more than 10% up to d = 2^{}",
            max_log
        ),
    }
    match crossover {
        Some(d) => println!("- measured: Newton is first faster at all at d = {}", d),
        None => println!(
            "- measured: NONE up to d = 2^{} — long division wins at every size swept, and that \
             is a null result to report as one",
            max_log
        ),
    }
    match rule_crossover {
        Some(d) => println!(
            "- the compiled-in constant is {}, so the shipped rule selects Newton from d = {}",
            compiled_in, d
        ),
        None => println!(
            "- the compiled-in constant is {}, which selects Newton nowhere in this sweep",
            compiled_in
        ),
    }

    // Fitted over the top half of the sweep only: the small sizes are where the constant factor
    // dominates, and they drag a single fit away from the asymptote in both arms alike.
    let tail = long_points.len() / 2;
    println!(
        "- fitted exponent over the largest {} rows: long division {:.3}, Newton {:.3} \
         (quadratic is 2.000, the product underneath is log2(3) = 1.585)",
        long_points.len() - tail,
        exponent(&long_points[tail..]),
        exponent(&newton_points[tail..]),
    );
}

/// The skew check: a base length against quotients and divisors from `base/64` to `64*base`, so
/// the rule's asymmetry in `k` and `m` is measured rather than argued.
///
/// The base is twice the compiled-in crossover rather than a round number, so that every row sits
/// *above* the rule's floor on the precision and the table therefore measures the inequality. At
/// `base = crossover` every `k = base` row lands exactly on the excluded boundary and the table
/// measures the floor instead, which is #527's subject and not this one's.
fn skewed<F: FiniteField>(seed: u64) {
    let compiled_in = newton_crossover_unstable::<F>();
    let base = 2 * compiled_in;

    println!(
        "\nskew: divisor length {} against quotient lengths around it — does the rule pick the \
         faster route?",
        base
    );
    println!(
        "| {:>10} | {:>10} | {:>11} | {:>11} | {:>8} | {:>8} | {:>8} | {:>7} |",
        "k", "m", "long s", "newton s", "speedup", "faster", "rule", "agrees"
    );
    println!("{}", rule(&[12, 12, 13, 13, 10, 10, 10, 9]));

    let mut shapes: Vec<(usize, usize)> = Vec::new();
    for ratio in SKEW_RATIOS {
        shapes.push((base * ratio, base));
        if ratio > 1 {
            shapes.push((base, base * ratio));
        }
    }
    shapes.sort_unstable();

    let mut disagreements = 0;
    for (index, (k, m)) in shapes.iter().enumerate() {
        let (dividend, divisor) = operands::<F>(*k, *m, seed ^ (index as u64) << 8);
        let (long, newton) = pair(&dividend, &divisor);
        let speedup = long.as_secs_f64() / newton.as_secs_f64();
        let faster = if speedup > 1.0 { "newton" } else { "long" };
        let chose_newton = newton_is_cheaper_at_unstable(*k, *m, compiled_in);
        let chosen = if chose_newton { "newton" } else { "long" };
        // Within 10% the two routes are interchangeable and a disagreement is noise, not a defect.
        let agrees = chosen == faster || (0.9..1.1).contains(&speedup);
        if !agrees {
            disagreements += 1;
        }
        println!(
            "| {:>10} | {:>10} | {:>11.6} | {:>11.6} | {:>8.2} | {:>8} | {:>8} | {:>7} |",
            k,
            m,
            long.as_secs_f64(),
            newton.as_secs_f64(),
            speedup,
            faster,
            chosen,
            if agrees { "yes" } else { "NO" },
        );
    }
    if disagreements == 0 {
        println!("- the rule picked the faster route at every skew measured");
    } else {
        println!(
            "- the rule picked the slower route at {} of {} skews by more than 10% — the \
             asymmetric form is not calibrated here and this is the figure to act on",
            disagreements,
            shapes.len()
        );
    }
}

/// The floor on the precision: `k` swept **downward** at a fixed large `m`.
///
/// #527, and the axis [`skewed`] cannot reach. That sweep fixes `base = 2 * crossover` and moves
/// `k` by factors of four *around* it, so every row has `k` at or above the crossover — which is
/// exactly the regime the floor excludes by construction. This one holds `m` large and walks `k`
/// down through the floor.
///
/// The shipped rule is `k > t` **and** `m > t^(2-e) * k^(e-1)`. The second half is derived and
/// measured; the first is a floor that the inequality does not imply — at `k = 2`, `m = 10^6` the
/// inequality holds and the floor is the only thing refusing Newton. #193 put the floor at `t`
/// because that is the one length it had measured, and predicted the true floor near **`t / 68`**
/// from the model
///
/// ```text
///   5 k^(e-1) / m + k^-(2-e)  <  6 t^-(2-e)
/// ```
///
/// which says the fixed cost of five products at the precision stops being amortized somewhere far
/// below `t`. If that is right the shipped rule forgoes Newton across nearly two decades of `k`, in
/// the regime where it measured *fastest*: at `k = 1024` against `m = 65536` Newton was 3.6x long
/// division over Mersenne-31 and 7.8x over BN254 `Fr`.
///
/// **A null result is a complete result here.** If the fixed cost really does dominate up to `t`,
/// the floor stays and the model is wrong, and that is worth knowing.
fn floor_sweep<F: FiniteField>(seed: u64) {
    let compiled_in = newton_crossover_unstable::<F>();
    // Large enough that `m` is never the binding side of the inequality, and a power of two so the
    // quotient lengths below divide it cleanly.
    let m = 1usize << 16;

    println!(
        "\nfloor: divisor length {} fixed, quotient length swept down through the shipped floor \
         of {} (the balanced crossover is {})",
        m,
        newton_floor_unstable::<F>(),
        compiled_in
    );
    println!(
        "| {:>8} | {:>11} | {:>11} | {:>8} | {:>8} | {:>10} | {:>9} |",
        "k", "long s", "newton s", "speedup", "rule", "model says", "agrees"
    );
    println!("{}", rule(&[10, 13, 13, 10, 10, 12, 11]));

    // Through the floor and well below it: the model's t/68 is 15 at t = 1024 and 4 at t = 256.
    let mut lengths: Vec<usize> = vec![2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048];
    lengths.retain(|k| *k <= m);
    lengths.sort_unstable();

    let mut first_win: Option<usize> = None;
    let mut last_loss: Option<usize> = None;

    for k in lengths {
        let (dividend, divisor) = operands::<F>(k, m, seed ^ (k as u64) << 4);
        let (long, newton) = pair(&dividend, &divisor);
        let speedup = long.as_secs_f64() / newton.as_secs_f64();
        if speedup > 1.1 {
            if first_win.is_none() {
                first_win = Some(k);
            }
        } else {
            last_loss = Some(k);
        }
        // What the shipped rule does, and what #193's model predicts it should do.
        let shipped = newton_is_cheaper_unstable::<F>(k, m);
        let model = model_prefers_newton(k, m, compiled_in);
        println!(
            "| {:>8} | {:>11.6} | {:>11.6} | {:>8.2} | {:>10} | {:>12} | {:>11} |",
            k,
            long.as_secs_f64(),
            newton.as_secs_f64(),
            speedup,
            if shipped { "newton" } else { "long" },
            if model { "newton" } else { "long" },
            if shipped == (speedup > 1.1) {
                "yes"
            } else {
                "NO"
            },
        );
    }

    match (last_loss, first_win) {
        (Some(loss), Some(win)) => println!(
            "- measured: long division still wins at k = {loss}, Newton wins by more than 10% from \
             k = {win}. The shipped floor is {}, so the rule takes Newton from k = {}.",
            newton_floor_unstable::<F>(),
            newton_floor_unstable::<F>() + 1
        ),
        (None, Some(win)) => println!(
            "- measured: Newton wins from the smallest k swept, {win} — the floor of \
             {compiled_in} forgoes every one of these"
        ),
        (Some(loss), None) => println!(
            "- measured: long division wins at every k up to {loss} — a null result, and the floor \
             of {compiled_in} is vindicated"
        ),
        (None, None) => println!("- no row was measured"),
    }
    println!(
        "- #193 guessed this floor at t = {} and then at t/68 = {}; #527 measured it and it is \
         neither — the shipped floor is `karatsuba_base_case` = {}",
        compiled_in,
        (compiled_in / 68).max(1),
        newton_floor_unstable::<F>()
    );
}

/// Whether #193's cost model prefers Newton, which is what #527 exists to test against the clock.
///
/// `5 k^(e-1) / m + k^-(2-e) < 6 t^-(2-e)`, the inequality in [`floor_sweep`]'s comment. The
/// constants 5 and 6 count products at the precision and are the modelled part; the exponent is
/// the crate's multiplication exponent.
fn model_prefers_newton(k: usize, m: usize, t: usize) -> bool {
    const E: f64 = 1.584_962_500_721_156;
    let k = k as f64;
    let m = m as f64;
    let t = t as f64;
    5.0 * k.powf(E - 1.0) / m + k.powf(-(2.0 - E)) < 6.0 * t.powf(-(2.0 - E))
}

/// One field's sweeps, with its element width stated.
fn measure_field<F: FiniteField>(name: &str, seed: u64, max_log: u32) {
    println!("\n\n## {}", name);
    println!("\n- an element is {} bytes", std::mem::size_of::<F>());
    balanced::<F>(seed, max_log);
    skewed::<F>(seed ^ 0x5_1193);
    floor_sweep::<F>(seed ^ 0x5_1527);
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let mut max_log = 13;
    let mut which = "all".to_string();
    for argument in &arguments {
        match argument.strip_prefix("max_log=") {
            Some(value) => max_log = value.parse().expect("max_log must be an integer"),
            None => which = argument.clone(),
        }
    }

    println!("# Newton inversion against long division, per field element width");
    println!("\nISA: {}", zeebra::util::isa_floor());
    println!("\nIssue #193. Both arms are the same entry point forced to one route each.");
    println!(
        "\n- each timed figure is the fastest of up to {MAX_REPETITIONS} interleaved repetitions"
    );
    println!("- `k` is the quotient length and `m` the divisor length, both in coefficients");
    println!("- sizes from 2^{FIRST_LOG} to 2^{max_log}");

    if which == "all" || which == "mersenne31" {
        measure_field::<Mersenne31>("Mersenne-31, 32-bit backing", 0x1931, max_log);
    }
    if which == "all" || which == "mersenne31-64" {
        measure_field::<Mersenne31In64>("Mersenne-31, 64-bit backing", 0x1932, max_log);
    }
    if which == "all" || which == "goldilocks" {
        measure_field::<Goldilocks>("Goldilocks", 0x1933, max_log);
    }
    if which == "all" || which == "bn254" {
        measure_field::<Bn254Fr>("BN254 Fr", 0x1934, max_log);
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
