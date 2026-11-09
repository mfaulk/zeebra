//! Where the subproduct tree starts beating the quadratic interpolation, per element width.
//!
//! Issue #162 stage 2. The quadratic form builds one numerator product and divides it down by a
//! linear factor per node, which is `n^2` multiplications in two flat arrays with no allocation
//! per point. The tree is `O(M(n) log n)` with `M` Karatsuba, but it allocates `O(n log n)`
//! polynomial objects and its divisions only reach #193's Newton route once a node's modulus
//! passes that crossover — 1024 coefficients at 4 bytes, 256 at 8, 128 above. So the asymptotically
//! better algorithm starts out slower and the crossing has to be measured, not derived.
//!
//! Two sweeps:
//!
//! - **Interpolation**, the two arms against each other at the same point count. This is what the
//!   shipped constant is read off.
//! - **Multipoint evaluation**, the tree against Horner at each point. There is no second
//!   algorithm here to compare against — `fft::evaluate` cannot take an arbitrary point set, which
//!   is the gap this stage exists to fill — so the comparand is the `n`-Horner loop it replaces.
//!   This arm calls the tree **directly** rather than through `multipoint_evaluate`, which
//!   dispatches: the first version of this sweep went through the dispatcher, so below the
//!   crossover both arms were the same Horner loop and reported a speedup of 1.00 that looked like
//!   a measurement of the tree. A sweep of a dispatcher cannot locate the dispatcher's own
//!   crossover.
//!
//! Both arms run through the same entry points the library uses, forced to one route each, and
//! every timed result goes through `std::hint::black_box`. That is not boilerplate: the first
//! version of this binary dropped the returned `Vec` instead, and LLVM deleted the allocation
//! whose contents nobody read — which made the `n`-Horner comparand measure at a fitted exponent
//! of **0.12** over Mersenne-31 against the 2.00 an `n`-by-`n` loop must have. BN254 escaped it,
//! because its wider arithmetic inlines less, so the defect showed up on three fields out of four
//! and would have been easy to read as a real result.
//!
//! ```text
//! cargo run --release --example subproduct_crossover
//! cargo run --release --example subproduct_crossover -- bn254
//! cargo run --release --example subproduct_crossover -- all max_log=14
//! ```

use std::{
    alloc::{GlobalAlloc, Layout, System},
    sync::atomic::{AtomicUsize, Ordering},
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, Mersenne31, PrimeFieldElement64},
    from_zeros_crossover_unstable, interpolate_quadratic_unstable, product_of_factors_unstable,
    subproduct_evaluate_unstable, subproduct_interpolate_unstable, tree_crossover_unstable,
    util::peak_resident_bytes,
    FiniteField, Polynomial, UnivariatePolynomial,
};

/// Mersenne-31 backed by a `u64`, the width `examples/univariate_scaling.rs` reports over.
type Mersenne31In64 = PrimeFieldElement64<2_147_483_647>;

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// The sweep runs from `2^FIRST_LOG` points to `2^max_log`.
const FIRST_LOG: u32 = 4;

/// Each arm's time is its fastest over at most this many interleaved repetitions, or fewer when
/// one pass already costs more than `PAIR_BUDGET`.
const MAX_REPETITIONS: usize = 7;

/// Target wall time for all repetitions at one size.
const PAIR_BUDGET: Duration = Duration::from_millis(600);

// === the allocator ===

/// Counts live heap bytes, so a measurement's peak is exact rather than estimated. Same instrument
/// as `examples/univariate_scaling.rs`, for figures that compare directly with §3.2's.
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

/// `n` points with distinct abscissae, shuffled out of order so the tree's shape is not the
/// sorted one — the result must not depend on the order, and neither should the cost.
fn points<F: FiniteField>(n: usize, seed: u64) -> Vec<(F, F)> {
    use rand::seq::SliceRandom;
    let mut rng = StdRng::seed_from_u64(seed);
    let mut xs: Vec<F> = Vec::with_capacity(n);
    let mut seen = std::collections::HashSet::new();
    while xs.len() < n {
        let x = F::random(&mut rng);
        if seen.insert(x) {
            xs.push(x);
        }
    }
    xs.shuffle(&mut rng);
    xs.into_iter().map(|x| (x, F::random(&mut rng))).collect()
}

/// Least-squares slope of `log2(seconds)` against `log2(size)`, which is the scaling exponent: 2
/// is quadratic and `log2(3) = 1.585` is the asymptote of the product the tree is built from.
fn exponent(measurements: &[(usize, Duration)]) -> f64 {
    let n = measurements.len() as f64;
    if n < 2.0 {
        return f64::NAN;
    }
    let xs: Vec<f64> = measurements
        .iter()
        .map(|(size, _)| (*size as f64).log2())
        .collect();
    let ys: Vec<f64> = measurements
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

/// Both interpolation arms at one size, interleaved, each reported as its fastest pass.
///
/// The arms are checked against each other once, outside the timing: a crossover measured against
/// a wrong answer is worthless, and the two routes must return the *same* polynomial since the
/// interpolant through n points of degree below n is unique.
fn interpolation_pair<F: FiniteField>(sample: &[(F, F)]) -> (Duration, Duration) {
    assert_eq!(
        subproduct_interpolate_unstable(sample),
        interpolate_quadratic_unstable(sample.to_vec()),
        "the two interpolation routes disagree at n = {}",
        sample.len()
    );

    let mut best = (Duration::MAX, Duration::MAX);
    let mut spent = Duration::ZERO;
    let mut taken = 0;
    while taken < MAX_REPETITIONS && spent < PAIR_BUDGET {
        let start = Instant::now();
        std::hint::black_box(interpolate_quadratic_unstable(sample.to_vec()));
        let quadratic = start.elapsed();

        let start = Instant::now();
        std::hint::black_box(subproduct_interpolate_unstable(sample));
        let tree = start.elapsed();

        best.0 = best.0.min(quadratic);
        best.1 = best.1.min(tree);
        spent += quadratic + tree;
        taken += 1;
    }
    best
}

/// The interpolation sweep over one field, and the crossover read off it.
fn interpolation<F: FiniteField>(seed: u64, max_log: u32) {
    let compiled_in = tree_crossover_unstable::<F>();

    println!("\ninterpolation: n points at arbitrary abscissae");
    println!(
        "| {:>5} | {:>8} | {:>12} | {:>12} | {:>8} | {:>8} | {:>7} | {:>7} | {:>11} | {:>11} |",
        "log2",
        "n",
        "quadratic/s",
        "tree/s",
        "speedup",
        "rule",
        "quad e",
        "tree e",
        "quad n*B",
        "tree n*B"
    );
    println!("{}", rule(&[7, 10, 14, 14, 10, 10, 9, 9, 13, 13]));

    let mut quadratic_points: Vec<(usize, Duration)> = Vec::new();
    let mut tree_points: Vec<(usize, Duration)> = Vec::new();
    let mut crossover: Option<usize> = None;
    let mut clear_crossover: Option<usize> = None;
    let mut rule_crossover: Option<usize> = None;

    for log_n in FIRST_LOG..=max_log {
        let n = 1usize << log_n;
        let sample = points::<F>(n, seed ^ u64::from(log_n));
        let (quadratic, tree) = interpolation_pair(&sample);
        let quadratic_bytes = peak_bytes(|| interpolate_quadratic_unstable(sample.clone()));
        let tree_bytes = peak_bytes(|| subproduct_interpolate_unstable(&sample));

        let local = |previous: &Vec<(usize, Duration)>, time: Duration| match previous.last() {
            Some((_, before)) if before.as_secs_f64() > 0.0 => {
                format!("{:.2}", (time.as_secs_f64() / before.as_secs_f64()).log2())
            }
            _ => "-".to_string(),
        };
        let quadratic_exponent = local(&quadratic_points, quadratic);
        let tree_exponent = local(&tree_points, tree);

        let speedup = quadratic.as_secs_f64() / tree.as_secs_f64();
        if crossover.is_none() && speedup > 1.0 {
            crossover = Some(n);
        }
        // A 1.01x speedup is a tie on this workstation, not a crossing. The constant is read off
        // the first clear win, because a tie is where either choice is defensible and the tiebreak
        // is then memory, where the quadratic form's two flat arrays win.
        if clear_crossover.is_none() && speedup > 1.1 {
            clear_crossover = Some(n);
        }
        let chose_tree = n > compiled_in;
        if rule_crossover.is_none() && chose_tree {
            rule_crossover = Some(n);
        }

        let per_point = (n * std::mem::size_of::<F>()) as f64;
        println!(
            "| {:>5} | {:>8} | {:>12.6} | {:>12.6} | {:>8.2} | {:>8} | {:>7} | {:>7} | \
             {:>11.2} | {:>11.2} |",
            log_n,
            n,
            quadratic.as_secs_f64(),
            tree.as_secs_f64(),
            speedup,
            if chose_tree { "tree" } else { "quad" },
            quadratic_exponent,
            tree_exponent,
            quadratic_bytes as f64 / per_point,
            tree_bytes as f64 / per_point,
        );
        quadratic_points.push((n, quadratic));
        tree_points.push((n, tree));
    }

    match clear_crossover {
        Some(n) => println!("- measured: the tree is first faster by more than 10% at n = {n}"),
        None => println!(
            "- measured: the tree is nowhere faster by more than 10% up to n = 2^{max_log} — a \
             null result, to report as one"
        ),
    }
    match crossover {
        Some(n) => println!("- measured: the tree is first faster at all at n = {n}"),
        None => println!("- measured: the tree is nowhere faster up to n = 2^{max_log}"),
    }
    match rule_crossover {
        Some(n) => println!(
            "- the compiled-in constant is {compiled_in}, so the shipped rule takes the tree from \
             n = {n}"
        ),
        None => println!(
            "- the compiled-in constant is {compiled_in}, which takes the tree nowhere in this \
             sweep"
        ),
    }

    // Fitted over the top half of the sweep only: the small sizes are where the constant factor
    // dominates, and they drag a single fit away from the asymptote in both arms alike.
    let tail = quadratic_points.len() / 2;
    println!(
        "- fitted exponent over the largest {} rows: quadratic {:.3}, tree {:.3} (quadratic is \
         2.000, the product underneath is log2(3) = 1.585)",
        quadratic_points.len() - tail,
        exponent(&quadratic_points[tail..]),
        exponent(&tree_points[tail..]),
    );
}

/// The multipoint evaluation sweep: the tree against the `n`-Horner loop it replaces.
fn evaluation<F: FiniteField>(seed: u64, max_log: u32) {
    println!("\nmultipoint evaluation: one polynomial of degree n-1 at n arbitrary points");
    println!(
        "| {:>5} | {:>8} | {:>12} | {:>12} | {:>8} | {:>7} | {:>7} |",
        "log2", "n", "horner/s", "tree/s", "speedup", "horn e", "tree e"
    );
    println!("{}", rule(&[7, 10, 14, 14, 10, 9, 9]));

    let mut horner_points: Vec<(usize, Duration)> = Vec::new();
    let mut tree_points: Vec<(usize, Duration)> = Vec::new();
    let mut crossover: Option<usize> = None;

    for log_n in FIRST_LOG..=max_log {
        let n = 1usize << log_n;
        let sample = points::<F>(n, seed ^ u64::from(log_n));
        let abscissae: Vec<F> = sample.iter().map(|(x, _y)| *x).collect();
        let mut rng = StdRng::seed_from_u64(seed ^ 0x5eed ^ u64::from(log_n));
        let f = UnivariatePolynomial::<F>::rand(n as u64 - 1, &mut rng);

        let horner_of = |f: &UnivariatePolynomial<F>, xs: &[F]| -> Vec<F> {
            xs.iter().map(|x| f.eval(x)).collect()
        };
        assert_eq!(
            subproduct_evaluate_unstable(&f, &abscissae),
            horner_of(&f, &abscissae),
            "multipoint evaluation disagrees with Horner at n = {n}"
        );

        let mut best = (Duration::MAX, Duration::MAX);
        let mut spent = Duration::ZERO;
        let mut taken = 0;
        while taken < MAX_REPETITIONS && spent < PAIR_BUDGET {
            let start = Instant::now();
            std::hint::black_box(horner_of(&f, &abscissae));
            let horner = start.elapsed();

            let start = Instant::now();
            std::hint::black_box(subproduct_evaluate_unstable(&f, &abscissae));
            let tree = start.elapsed();

            best.0 = best.0.min(horner);
            best.1 = best.1.min(tree);
            spent += horner + tree;
            taken += 1;
        }

        let local = |previous: &Vec<(usize, Duration)>, time: Duration| match previous.last() {
            Some((_, before)) if before.as_secs_f64() > 0.0 => {
                format!("{:.2}", (time.as_secs_f64() / before.as_secs_f64()).log2())
            }
            _ => "-".to_string(),
        };
        let horner_exponent = local(&horner_points, best.0);
        let tree_exponent = local(&tree_points, best.1);
        let speedup = best.0.as_secs_f64() / best.1.as_secs_f64();
        if crossover.is_none() && speedup > 1.1 {
            crossover = Some(n);
        }

        println!(
            "| {:>5} | {:>8} | {:>12.6} | {:>12.6} | {:>8.2} | {:>7} | {:>7} |",
            log_n,
            n,
            best.0.as_secs_f64(),
            best.1.as_secs_f64(),
            speedup,
            horner_exponent,
            tree_exponent,
        );
        horner_points.push((n, best.0));
        tree_points.push((n, best.1));
    }

    match crossover {
        Some(n) => println!(
            "- measured: the tree is first faster than n-Horner by more than 10% at n = {n}"
        ),
        None => println!(
            "- measured: n-Horner wins at every size up to 2^{max_log} — a null result, to report \
             as one"
        ),
    }
    let tail = horner_points.len() / 2;
    println!(
        "- fitted exponent over the largest {} rows: Horner {:.3}, tree {:.3}",
        horner_points.len() - tail,
        exponent(&horner_points[tail..]),
        exponent(&tree_points[tail..]),
    );
}

/// `prod (x - z)` as the tree's root, against the naive fold `from_zeros` used to be.
///
/// A third sweep because the work is different from interpolation's and so is the crossover: this
/// builds the tree and stops, where interpolation also evaluates the derivative down it and
/// accumulates the transposed form back up. #560.
///
/// The fold is `O(n^2)` and cannot be rescued by a better multiplication — it multiplies a growing
/// product by a two-coefficient operand, below every Karatsuba base-case tier, so every step is the
/// schoolbook loop. That is why this is the one arm here whose comparand is a *fold* rather than a
/// second algorithm.
fn from_zeros<F: FiniteField>(seed: u64, max_log: u32) {
    let compiled_in = from_zeros_crossover_unstable::<F>();

    println!("\nfrom_zeros: the product of n linear factors");
    println!(
        "| {:>5} | {:>8} | {:>12} | {:>12} | {:>8} | {:>8} | {:>7} | {:>7} |",
        "log2", "n", "fold/s", "tree/s", "speedup", "rule", "fold e", "tree e"
    );
    println!("{}", rule(&[7, 10, 14, 14, 10, 10, 9, 9]));

    let mut fold_points: Vec<(usize, Duration)> = Vec::new();
    let mut tree_points: Vec<(usize, Duration)> = Vec::new();
    let mut crossover: Option<usize> = None;

    // From `2^1`, not `2^FIRST_LOG`: over a 32-byte element the tree already wins at 16, the other
    // sweeps' floor, so starting there would bound this crossover from above without pinning it.
    for log_n in 1..=max_log {
        let n = 1usize << log_n;
        let zeros: Vec<F> = points::<F>(n, seed ^ u64::from(log_n))
            .into_iter()
            .map(|(x, _y)| x)
            .collect();

        let fold = |z: &[F]| -> UnivariatePolynomial<F> {
            z.iter().fold(UnivariatePolynomial::<F>::one(), |p, x| {
                p * UnivariatePolynomial::new(&[x.neg(), F::one()])
            })
        };
        assert_eq!(
            product_of_factors_unstable(&zeros),
            fold(&zeros),
            "the tree's root disagrees with the fold at n = {n}"
        );

        let mut best = (Duration::MAX, Duration::MAX);
        let mut spent = Duration::ZERO;
        let mut taken = 0;
        while taken < MAX_REPETITIONS && spent < PAIR_BUDGET {
            let start = Instant::now();
            std::hint::black_box(fold(&zeros));
            let f = start.elapsed();

            let start = Instant::now();
            std::hint::black_box(product_of_factors_unstable(&zeros));
            let t = start.elapsed();

            best.0 = best.0.min(f);
            best.1 = best.1.min(t);
            spent += f + t;
            taken += 1;
        }

        let local = |previous: &Vec<(usize, Duration)>, time: Duration| match previous.last() {
            Some((_, before)) if before.as_secs_f64() > 0.0 => {
                format!("{:.2}", (time.as_secs_f64() / before.as_secs_f64()).log2())
            }
            _ => "-".to_string(),
        };
        let fold_exponent = local(&fold_points, best.0);
        let tree_exponent = local(&tree_points, best.1);
        let speedup = best.0.as_secs_f64() / best.1.as_secs_f64();
        if crossover.is_none() && speedup > 1.1 {
            crossover = Some(n);
        }

        println!(
            "| {:>5} | {:>8} | {:>12.6} | {:>12.6} | {:>8.2} | {:>8} | {:>7} | {:>7} |",
            log_n,
            n,
            best.0.as_secs_f64(),
            best.1.as_secs_f64(),
            speedup,
            if n > compiled_in { "tree" } else { "fold" },
            fold_exponent,
            tree_exponent,
        );
        fold_points.push((n, best.0));
        tree_points.push((n, best.1));
    }

    match crossover {
        Some(n) => println!("- measured: the tree is first faster by more than 10% at n = {n}"),
        None => println!(
            "- measured: the fold wins at every size up to 2^{max_log} - a null result, to report \
             as one"
        ),
    }
    println!(
        "- the compiled-in constant is {compiled_in}, so `from_zeros` takes the tree from n = {}",
        compiled_in + 1
    );
    let tail = fold_points.len() / 2;
    println!(
        "- fitted exponent over the largest {} rows: fold {:.3}, tree {:.3}",
        fold_points.len() - tail,
        exponent(&fold_points[tail..]),
        exponent(&tree_points[tail..]),
    );
}

/// One field's sweeps, with its element width stated.
fn measure_field<F: FiniteField>(name: &str, seed: u64, max_log: u32) {
    println!("\n\n## {name}");
    println!("\n- an element is {} bytes", std::mem::size_of::<F>());
    interpolation::<F>(seed, max_log);
    evaluation::<F>(seed ^ 0x1620, max_log);
    from_zeros::<F>(seed ^ 0x0560, max_log);
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

    println!("# The subproduct tree against the quadratic forms, per field element width");
    println!("\nISA: {}", zeebra::util::isa_floor());
    println!("\nIssue #162 stage 2. Both arms are the library's own entry points, forced to one");
    println!("route each, and checked against each other before the clock starts.");
    println!(
        "\n- each timed figure is the fastest of up to {MAX_REPETITIONS} interleaved repetitions"
    );
    println!("- sizes from 2^{FIRST_LOG} to 2^{max_log} points");

    if which == "all" || which == "mersenne31" {
        measure_field::<Mersenne31>("Mersenne-31, 32-bit backing", 0x1621, max_log);
    }
    if which == "all" || which == "mersenne31-64" {
        measure_field::<Mersenne31In64>("Mersenne-31, 64-bit backing", 0x1622, max_log);
    }
    if which == "all" || which == "goldilocks" {
        measure_field::<Goldilocks>("Goldilocks", 0x1623, max_log);
    }
    if which == "all" || which == "bn254" {
        measure_field::<Bn254Fr>("BN254 Fr", 0x1624, max_log);
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
