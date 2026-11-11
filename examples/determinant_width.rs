//! Width attribution and matched-concurrency kernel comparisons must share a process, polynomial
//! pair and sample sequence: mixing those produced the false 3.21x width penalty in #412.
//! `--compare-kernels` alternates timing order and checks every sample before reporting a ratio.

use std::{
    alloc::{GlobalAlloc, Layout, System},
    sync::atomic::{AtomicBool, AtomicU64, Ordering},
    time::Instant,
};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::resultant::{
        random_bivariate, time_sylvester_determinants, DeterminantBatch, DeterminantKernel,
    },
    resultant_from_coefficients, FiniteField, Monomial, MultivariatePolynomial, One, Polynomial,
    UnivariatePolynomial, Zero,
};

/// KoalaBear, `2^31 - 2^24 + 1`, at 64-bit storage.
type K = PrimeFieldElement64<2_130_706_433>;

/// Allocation calls since the counter was armed, and whether it is armed.
///
/// Armed only by `--count-allocations`, which prints counts and refuses to print timings: a
/// `fetch_add` per allocation from 32 threads onto one cache line is itself the contention this
/// example is trying to attribute, so a counted run cannot also be a timed one. Disarmed the cost
/// is one relaxed load of a line nobody writes, which is shared-state and does not invalidate.
static ALLOCATIONS: AtomicU64 = AtomicU64::new(0);
static COUNTING: AtomicBool = AtomicBool::new(false);

/// `System`, counting calls when armed.
struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if COUNTING.load(Ordering::Relaxed) {
            ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
        }
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        System.dealloc(pointer, layout)
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if COUNTING.load(Ordering::Relaxed) {
            ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
        }
        System.realloc(pointer, layout, new_size)
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

/// The widths swept by default: every power of two out to 32.
const WIDTHS: [usize; 6] = [1, 2, 4, 8, 16, 32];

/// Which pair the determinants are taken over.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Pair {
    /// `determinant_sweep`'s: degree 1 in the surviving variable, `order / 2` in the eliminated
    /// one, so the matrix order is the only thing that varies and specialization is nearly free.
    Synthetic,
    /// Total degree `order / 2`, so the support is the triangle `i + j <= order / 2` and the
    /// coefficient of `y^j` is a polynomial in `x` of degree `order / 2 − j` — the shape of a
    /// straight-line program's two outputs in two free inputs.
    Triangular,
}

/// The value of a `--flag <value>` argument, if it was given and parses.
fn flag_value(flag: &str) -> Option<usize> {
    let args: Vec<String> = std::env::args().collect();
    let at = args.iter().position(|a| a == flag)?;
    args.get(at + 1)?.parse().ok()
}

/// Every value of a repeatable `--flag <value>` argument.
fn flag_values(flag: &str) -> Vec<usize> {
    let args: Vec<String> = std::env::args().collect();
    args.iter()
        .enumerate()
        .filter(|(_, a)| *a == flag)
        .filter_map(|(at, _)| args.get(at + 1)?.parse().ok())
        .collect()
}

/// Whether a bare `--flag` was given.
fn flag(name: &str) -> bool {
    std::env::args().any(|a| a == name)
}

/// The string value of a `--flag <value>` argument.
fn flag_string(flag: &str) -> Option<String> {
    let args: Vec<String> = std::env::args().collect();
    let at = args.iter().position(|a| a == flag)?;
    args.get(at + 1).cloned()
}

/// What `--kernel` named. Only two of these are determinant kernels.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Subject {
    /// A determinant kernel, timed through `time_sylvester_determinants`.
    Determinant(DeterminantKernel),
    /// The register-only control: no allocation, no memory traffic, same operation count.
    Clock,
    /// The Euclidean kernel's **first half** alone: evaluating the pair's coefficients in the
    /// eliminated variable at the sample point. Two allocations a sample.
    Specialize,
    /// The Euclidean kernel's **second half** alone: the remainder sequence over coefficient
    /// vectors specialized in advance, outside the timer. This is where every per-step allocation
    /// the issue's candidate mechanism names actually happens.
    Remainder,
}

impl std::fmt::Display for Subject {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Subject::Determinant(kernel) => write!(formatter, "{kernel}"),
            Subject::Clock => write!(formatter, "clock control (registers only)"),
            Subject::Specialize => write!(formatter, "specialize only (no remainder sequence)"),
            Subject::Remainder => write!(formatter, "remainder sequence only (pre-specialized)"),
        }
    }
}

/// The subjects named by `--kernel`, defaulting to the set the mechanism question needs.
///
/// # Panics
/// On an unrecognized value: falling back to a default would report one kernel's figure under
/// another's name, and these differ by three orders of magnitude at the same order.
fn subjects() -> Vec<Subject> {
    let args: Vec<String> = std::env::args().collect();
    let named: Vec<Subject> = args
        .iter()
        .enumerate()
        .filter(|(_, a)| *a == "--kernel")
        .map(|(at, _)| match args.get(at + 1).map(String::as_str) {
            Some("euclidean") => Subject::Determinant(DeterminantKernel::Euclidean),
            Some("dense") => Subject::Determinant(DeterminantKernel::Dense),
            Some("clock") => Subject::Clock,
            Some("specialize") => Subject::Specialize,
            Some("remainder") => Subject::Remainder,
            other => panic!(
                "--kernel takes euclidean, dense, clock, specialize or remainder, not {other:?}"
            ),
        })
        .collect();
    if named.is_empty() {
        vec![
            Subject::Clock,
            Subject::Determinant(DeterminantKernel::Euclidean),
            Subject::Specialize,
            Subject::Remainder,
        ]
    } else {
        named
    }
}

/// `f`'s coefficients in variable `eliminate`, as univariate polynomials in the other variable.
///
/// `coefficients_in` in `src/grobner/resultant.rs` is private, and this is that function:
/// the split the Euclidean kernel takes once per row, so the example can time the per-sample half
/// of it separately from the remainder sequence.
fn coefficients_in(
    f: &MultivariatePolynomial<2, K>,
    eliminate: usize,
) -> Vec<UnivariatePolynomial<K>> {
    let keep = 1 - eliminate;
    let degree = f
        .terms()
        .keys()
        .map(|monomial| monomial.exponents()[eliminate])
        .max()
        .unwrap_or(0) as usize;
    let mut columns = vec![Vec::<K>::new(); degree + 1];
    for (monomial, coefficient) in f.terms() {
        let exponents = monomial.exponents();
        let power = exponents[eliminate] as usize;
        let other = exponents[keep] as usize;
        let column = &mut columns[power];
        if column.len() <= other {
            column.resize(other + 1, K::zero());
        }
        column[other] += *coefficient;
    }
    columns
        .into_iter()
        .map(|coefficients| {
            if coefficients.is_empty() {
                UnivariatePolynomial::new(&[K::zero()])
            } else {
                UnivariatePolynomial::new(&coefficients)
            }
        })
        .collect()
}

/// Horner multiply-adds one sample's specialization costs, exactly.
///
/// `Σ_j deg_x(fc[j]) + Σ_j deg_x(gc[j])`, which is what `sylvester_resultant_euclid` pays per
/// sample before the remainder sequence starts. Counted rather than estimated, because the whole
/// finding is that this term is not small and a derived figure would be the same guess again.
fn specialization_operations(
    fc: &[UnivariatePolynomial<K>],
    gc: &[UnivariatePolynomial<K>],
) -> usize {
    fc.iter().chain(gc).map(|c| c.degree() as usize).sum()
}

/// One sample's specialization: both coefficient vectors evaluated at `x`.
#[inline(never)]
fn specialize_at(
    fc: &[UnivariatePolynomial<K>],
    gc: &[UnivariatePolynomial<K>],
    x: K,
) -> (Vec<K>, Vec<K>) {
    let a: Vec<K> = fc.iter().map(|c| c.eval(&x)).collect();
    let b: Vec<K> = gc.iter().map(|c| c.eval(&x)).collect();
    (a, b)
}

/// `samples` specializations over `concurrency` workers, timed as a determinant batch is.
fn time_specialization(
    fc: &[UnivariatePolynomial<K>],
    gc: &[UnivariatePolynomial<K>],
    at: &[K],
    concurrency: usize,
) -> f64 {
    let mut values = vec![K::zero(); at.len()];
    let started = Instant::now();
    let work = |chunk: &mut [K], seeds: &[K]| {
        for (slot, x) in chunk.iter_mut().zip(seeds) {
            let (a, b) = specialize_at(fc, gc, *x);
            // Consumed so neither vector is dead code; the sum is O(n) against the O(n²) the
            // evaluation costs.
            *slot = a[a.len() - 1] + b[b.len() - 1];
        }
    };
    if concurrency <= 1 {
        work(&mut values, at);
    } else {
        let block = at.len().div_ceil(concurrency).max(1);
        std::thread::scope(|scope| {
            for (chunk, seeds) in values.chunks_mut(block).zip(at.chunks(block)) {
                scope.spawn(|| work(chunk, seeds));
            }
        });
    }
    started.elapsed().as_secs_f64() / at.len() as f64
}

/// `samples` remainder sequences over `concurrency` workers, on vectors specialized in advance.
///
/// The specialization happens outside the timer and at every sample point separately, so each
/// worker still walks its own distinct data and nothing is being re-timed out of cache.
fn time_remainder_sequence(specialized: &[(Vec<K>, Vec<K>)], concurrency: usize) -> f64 {
    let mut values = vec![K::zero(); specialized.len()];
    let started = Instant::now();
    let work = |chunk: &mut [K], pairs: &[(Vec<K>, Vec<K>)]| {
        for (slot, (a, b)) in chunk.iter_mut().zip(pairs) {
            *slot = resultant_from_coefficients(a, b);
        }
    };
    if concurrency <= 1 {
        work(&mut values, specialized);
    } else {
        let block = specialized.len().div_ceil(concurrency).max(1);
        std::thread::scope(|scope| {
            for (chunk, pairs) in values.chunks_mut(block).zip(specialized.chunks(block)) {
                scope.spawn(|| work(chunk, pairs));
            }
        });
    }
    started.elapsed().as_secs_f64() / specialized.len() as f64
}

/// A dependent chain of `operations` field multiply-adds, returning the accumulator.
///
/// The control's per-sample work. Deliberately **latency-bound**: one chain, each step depending on
/// the last, so the wall clock is the chain length times the multiply-add latency and is
/// proportional to `1 / clock` with no memory or pipeline width in it. The accumulator is returned
/// and written into the output, so nothing here is dead code the optimizer may delete.
#[inline(never)]
fn clock_chain(operations: usize, seed: K) -> K {
    let multiplier = K::new(0x1234_5678);
    let addend = K::new(0x9abc_def0);
    let mut accumulator = seed;
    for _ in 0..operations {
        accumulator = accumulator * multiplier + addend;
    }
    accumulator
}

/// `samples` control chains over `concurrency` workers, timed exactly as a determinant batch is.
fn time_clock_control(operations: usize, samples: usize, concurrency: usize) -> f64 {
    let at: Vec<K> = (0..samples).map(|i| K::new(i as u64 + 7)).collect();
    let mut values = vec![K::one(); samples];
    let started = Instant::now();
    if concurrency <= 1 {
        for (slot, x) in values.iter_mut().zip(&at) {
            *slot = clock_chain(operations, *x);
        }
    } else {
        let block = samples.div_ceil(concurrency).max(1);
        std::thread::scope(|scope| {
            for (chunk, seeds) in values.chunks_mut(block).zip(at.chunks(block)) {
                scope.spawn(move || {
                    for (slot, x) in chunk.iter_mut().zip(seeds) {
                        *slot = clock_chain(operations, *x);
                    }
                });
            }
        });
    }
    let elapsed = started.elapsed().as_secs_f64();
    // Consumed so the chains cannot be optimized away across the scope.
    assert!(values.iter().any(|v| !v.is_zero()) || samples == 0);
    elapsed / samples as f64
}

/// The synthetic pair of the named Sylvester order: degree 1 surviving, `order / 2` eliminated.
fn synthetic_pair(
    order: usize,
    seed: u64,
) -> (MultivariatePolynomial<2, K>, MultivariatePolynomial<2, K>) {
    assert!(
        order.is_multiple_of(2),
        "the order is split evenly between the pair"
    );
    let half = (order / 2) as u32;
    let mut rng = StdRng::seed_from_u64(seed);
    let f = random_bivariate::<K, _>(1, half, &mut rng);
    let g = random_bivariate::<K, _>(1, half, &mut rng);
    (f, g)
}

/// A pair of total degree `order / 2` with triangular support.
fn triangular_pair(
    order: usize,
    seed: u64,
) -> (MultivariatePolynomial<2, K>, MultivariatePolynomial<2, K>) {
    assert!(
        order.is_multiple_of(2),
        "the order is split evenly between the pair"
    );
    let degree = (order / 2) as u32;
    let mut rng = StdRng::seed_from_u64(seed);
    let mut one = || -> MultivariatePolynomial<2, K> {
        let mut terms = Vec::new();
        for j in 0..=degree {
            for i in 0..=(degree - j) {
                let mut c = K::random(&mut rng);
                // The top coefficient in the eliminated variable must not vanish, or the Sylvester
                // matrix does not have the order the degree claims.
                if j == degree && c.is_zero() {
                    c = K::one();
                }
                if !c.is_zero() {
                    terms.push((Monomial::new(&[i, j]), c));
                }
            }
        }
        MultivariatePolynomial::new(&terms)
    };
    let f = one();
    let g = one();
    (f, g)
}

/// One width's measurement of one subject.
struct Point {
    /// Workers.
    width: usize,
    /// Wall clock per sample, seconds, median over the draws.
    wall: f64,
    /// Core-time per sample — wall times workers — median over the draws.
    core: f64,
    /// Spread of the core-time draws as a fraction of the median.
    spread: f64,
    /// The one-minute load average read at the start of this arm, before its own workers existed.
    ///
    /// Per point rather than per run: a sweep is a measurement **of** contention, so the ambient
    /// load at the moment of each arm is part of that arm's provenance and a single figure for the
    /// whole run cannot carry it. The 32-wide arms are the fragile ones — another agent's `-j128`
    /// release build during one of them reads as the kernel contending with itself.
    load: f64,
}

/// The median of a nonempty sample.
fn median(values: &[f64]) -> f64 {
    let mut sorted = values.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).expect("no NaN in a measured duration"));
    let n = sorted.len();
    if n % 2 == 1 {
        sorted[n / 2]
    } else {
        0.5 * (sorted[n / 2 - 1] + sorted[n / 2])
    }
}

/// A duration in whatever unit a reader can hold in their head.
fn human(seconds: f64) -> String {
    if seconds < 1e-3 {
        format!("{:.3} µs", seconds * 1e6)
    } else if seconds < 1.0 {
        format!("{:.3} ms", seconds * 1e3)
    } else if seconds < 90.0 {
        format!("{seconds:.3} s")
    } else {
        format!("{:.2} min", seconds / 60.0)
    }
}

/// The sweep for one subject over one pair.
fn sweep(
    subject: Subject,
    pair: Option<&(MultivariatePolynomial<2, K>, MultivariatePolynomial<2, K>)>,
    operations: usize,
    samples: usize,
    widths: &[usize],
    repeats: usize,
) -> Vec<Point> {
    let split = pair.map(|(f, g)| (coefficients_in(f, 1), coefficients_in(g, 1)));
    let mut points = Vec::new();
    for &width in widths {
        // At least one sample per worker, or the static block split leaves workers idle and the
        // run would report a width it never reached.
        let samples = samples.max(width);
        let at: Vec<K> = (0..samples).map(|i| K::new(i as u64 + 7)).collect();
        let mut cores = Vec::new();
        let mut walls = Vec::new();
        // Read once, before this arm's own workers exist. A 32-wide arm that runs for seconds
        // raises the one-minute average by about 32 all on its own — the dense kernel at order
        // 1 458 took its own load from 3.5 to 13.3 — so sampling the average *during* an arm
        // measures the measurement, and gating on that figure would refuse every wide arm of
        // every expensive kernel on a box that was in fact quiet.
        let load = one_minute_load();
        for _ in 0..repeats {
            let wall = match (subject, pair) {
                (Subject::Clock, _) => time_clock_control(operations, samples, width),
                (Subject::Determinant(kernel), Some((f, g))) => {
                    let (_, batch) = time_sylvester_determinants(f, g, 1, &at, width, kernel)
                        .expect("both polynomials have positive degree in the eliminated variable");
                    batch.wall_per_determinant()
                }
                (Subject::Specialize, Some(_)) => {
                    let (fc, gc) = split.as_ref().expect("a pair was split");
                    time_specialization(fc, gc, &at, width)
                }
                (Subject::Remainder, Some(_)) => {
                    let (fc, gc) = split.as_ref().expect("a pair was split");
                    // Specialized outside the timer, once per sample point, so every worker still
                    // walks its own distinct coefficient vectors.
                    let specialized: Vec<(Vec<K>, Vec<K>)> =
                        at.iter().map(|x| specialize_at(fc, gc, *x)).collect();
                    time_remainder_sequence(&specialized, width)
                }
                (_, None) => unreachable!("every subject but the control needs a pair"),
            };
            let core = wall * width as f64;
            walls.push(wall);
            cores.push(core);
        }
        let core = median(&cores);
        let lo = cores.iter().fold(f64::MAX, |a, b| a.min(*b));
        let hi = cores.iter().fold(f64::MIN, |a, b| a.max(*b));
        points.push(Point {
            width,
            wall: median(&walls),
            core,
            spread: (hi - lo) / core,
            load,
        });
    }
    points
}

/// The penalty and efficiency table for one subject's sweep.
fn report(subject: Subject, points: &[Point]) {
    let Some(base) = points.first() else {
        return;
    };
    println!("\n**{subject}**\n");
    println!(
        "| workers | wall/sample | core-time/sample | penalty vs this run's 1 worker | parallel \
         efficiency | spread | load at arm start |"
    );
    println!("|---:|---:|---:|---:|---:|---:|---:|");
    let mut dirty = Vec::new();
    let mut noisy = Vec::new();
    for point in points {
        let penalty = point.core / base.core;
        if point.load > DIRTY_LOAD {
            dirty.push(point.width);
        }
        if point.spread > NOISY_SPREAD {
            noisy.push(point.width);
        }
        println!(
            "| {} | {} | **{}** | {:.3}x | **{:.1}%** | {:.1}%{} | {:.1}{} |",
            point.width,
            human(point.wall),
            human(point.core),
            penalty,
            100.0 / penalty,
            100.0 * point.spread,
            if point.spread > NOISY_SPREAD {
                " **NOISY**"
            } else {
                ""
            },
            point.load,
            if point.load > DIRTY_LOAD {
                " **DIRTY**"
            } else {
                ""
            }
        );
    }
    if !dirty.is_empty() {
        println!(
            "\n**Do not publish this curve.** Width{} {dirty:?} started at a one-minute load above \
             {DIRTY_LOAD:.0}, and a sweep whose subject *is* contention cannot be taken while the \
             box contends for other reasons. Re-take the affected points.",
            if dirty.len() == 1 { "" } else { "s" }
        );
    }
    if !noisy.is_empty() {
        println!(
            "\n**Width{} {noisy:?} is not a point.** Its draws spread by more than {:.0}% of the \
             median, which at this draw count says the arm caught a transient rather than that it \
             measured one. Raise `--repeats` and re-take it.",
            if noisy.len() == 1 { "" } else { "s" },
            100.0 * NOISY_SPREAD
        );
    }
}

fn compare_draw(
    f: &MultivariatePolynomial<2, K>,
    g: &MultivariatePolynomial<2, K>,
    at: &[K],
    workers: usize,
    dense_first: bool,
) -> (Vec<K>, DeterminantBatch, DeterminantBatch) {
    let run = |kernel| time_sylvester_determinants(f, g, 1, at, workers, kernel).unwrap();
    let dense;
    let euclidean;
    if dense_first {
        dense = run(DeterminantKernel::Dense);
        euclidean = run(DeterminantKernel::Euclidean);
    } else {
        euclidean = run(DeterminantKernel::Euclidean);
        dense = run(DeterminantKernel::Dense);
    }
    assert_eq!(dense.0, euclidean.0, "kernels disagree at matched samples");
    (dense.0, dense.1, euclidean.1)
}

fn compare_kernels(
    pair: &(MultivariatePolynomial<2, K>, MultivariatePolynomial<2, K>),
    samples: usize,
    widths: &[usize],
    repeats: usize,
) {
    println!("## Dense versus Euclidean at matched concurrency\n");
    println!(
        "Same pair and samples in every draw; timing order alternates. Ratios compare medians \
         within this run. Times exclude coefficient extraction, interpolation and root finding; \
         thread creation is included. Small batches can be dominated by thread creation.\n"
    );
    for &width in widths {
        println!(
            "| workers | samples | draw | first | dense wall/sample (s) | Euclidean wall/sample (s) |"
        );
        println!("|---:|---:|---:|---|---:|---:|");
        assert!(width > 0, "a comparison needs at least one worker");
        // A multiple of width makes every static block nonempty and uses exactly width workers.
        let count = samples
            .max(width)
            .div_ceil(width)
            .checked_mul(width)
            .unwrap();
        let at: Vec<K> = (0..count).map(|i| K::new(i as u64 + 7)).collect();
        let mut dense_times = Vec::new();
        let mut euclidean_times = Vec::new();
        for draw in 0..repeats {
            let dense_first = draw % 2 == 0;
            let (_, dense, euclidean) = compare_draw(&pair.0, &pair.1, &at, width, dense_first);
            dense_times.push(dense.wall_per_determinant());
            euclidean_times.push(euclidean.wall_per_determinant());
            println!(
                "| {width} | {count} | {} | {} | {:.9} | {:.9} |",
                draw + 1,
                if dense_first { "dense" } else { "Euclidean" },
                dense.wall_per_determinant(),
                euclidean.wall_per_determinant(),
            );
        }
        println!(
            "\n{width} workers, {count} samples: dense median {}, Euclidean median {}, \
             **{:.2}x** determinant-stage ratio; all samples equal in all {repeats} draws.\n",
            human(median(&dense_times)),
            human(median(&euclidean_times)),
            median(&dense_times) / median(&euclidean_times),
        );
    }
}

/// One-minute load average above which a width arm is not publishable.
///
/// The orchestration standard on this box: six agents, release builds at `-j128`, and a one-minute
/// load that has peaked at 687 on 128 cores. A scaling curve is a measurement of contention, so
/// ambient contention is not noise around it — it is the same quantity, from a different source.
const DIRTY_LOAD: f64 = 8.0;

/// Draw spread, as a fraction of the median, above which an arm is reported as not a point.
///
/// A quiet box gave 0.1–3% on every arm long enough to amortize its own thread spawn, and 33–44%
/// on three arms taken in the same minutes. A spread an order of magnitude above the rest of the
/// sweep is a transient inside the arm, and the median of three draws does not remove it.
const NOISY_SPREAD: f64 = 0.15;

/// The one-minute load average, or zero where `/proc` does not carry one.
fn one_minute_load() -> f64 {
    std::fs::read_to_string("/proc/loadavg")
        .ok()
        .and_then(|line| line.split_whitespace().next()?.parse().ok())
        .unwrap_or(0.0)
}

fn main() {
    let repeats = flag_value("--repeats").unwrap_or(3).max(1);
    let order = flag_value("--order").unwrap_or(1_458);
    let samples = flag_value("--samples").unwrap_or(64);
    let compare = flag("--compare-kernels");
    assert!(
        !compare || (!flag("--count-allocations") && flag_string("--kernel").is_none()),
        "--compare-kernels cannot be combined with --count-allocations or --kernel"
    );
    assert!(
        order >= 2 && order.is_multiple_of(2),
        "--order must be positive and even"
    );
    let pair_kind = match flag_string("--pair").as_deref() {
        None | Some("synthetic") => Pair::Synthetic,
        Some("triangular") => Pair::Triangular,
        Some(other) => panic!("--pair takes synthetic or triangular, not {other}"),
    };
    let widths = {
        let named = flag_values("--width");
        if named.is_empty() {
            WIDTHS.to_vec()
        } else {
            named
        }
    };

    println!("# Sylvester determinant measurement\n");
    println!(
        "Machine: {}; affinity: {}.\n",
        std::env::var("ZEEBRA_MACHINE").unwrap_or_else(|_| "unspecified".into()),
        std::env::var("ZEEBRA_AFFINITY").unwrap_or_else(|_| "unspecified".into()),
    );
    println!(
        "Every point below comes out of **this** process on the same pair. {} draw{} per \
         width, {} requested sample{} a draw.\n",
        repeats,
        if repeats == 1 { "" } else { "s" },
        samples,
        if samples == 1 { "" } else { "s" }
    );

    let pair = match pair_kind {
        Pair::Synthetic => {
            println!(
                "Pair: **synthetic**, Sylvester order {order} — degree 1 in the surviving variable \
                 and {} in the eliminated one, which is `determinant_sweep`'s pair and the one the \
                 recorded 1.109 ms single-worker anchor was taken over.\n",
                order / 2
            );
            Some(synthetic_pair(order, 0x5_e51 ^ order as u64))
        }
        Pair::Triangular => {
            println!(
                "Pair: **triangular**, Sylvester order {order} — random of total degree {}, so the \
                 coefficient of `y^j` has degree {} − j in the surviving variable.\n",
                order / 2,
                order / 2
            );
            Some(triangular_pair(order, 0x7_41a ^ order as u64))
        }
    };

    // The control's chain length: the remainder sequence's own operation count at this order,
    // `(order/2)² / 2` multiply-adds, so the control and the kernel are the same amount of
    // arithmetic and the comparison is of *where the time goes* and not of how much there is.
    let half = order / 2;
    let operations = flag_value("--operations").unwrap_or(half * half / 2);

    if let Some((f, g)) = pair.as_ref() {
        let (fc, gc) = (coefficients_in(f, 1), coefficients_in(g, 1));
        let specialization = specialization_operations(&fc, &gc);
        println!(
            "Sylvester order **{}**. Per sample this pair costs **{} Horner multiply-adds** to \
             specialize — `Σ_j deg_x(fc[j]) + Σ_j deg_x(gc[j])`, counted off the pair — against the \
             remainder sequence's **{} multiply-adds**, so specialization is **{:.2}x** the \
             sequence it feeds. Both are inside the per-determinant timer.\n",
            sylvester_order(f, g),
            specialization,
            operations,
            specialization as f64 / operations as f64
        );
    }

    // Counting needs no quiet box: it reports calls and refuses to report times.
    if flag("--count-allocations") {
        count_allocations(pair.as_ref(), samples.min(8));
        return;
    }

    // Read at the moment the timers are about to start, not before the lock was requested: a
    // sweep can wait half an hour for the lock, and the load it gated on is stale by then.
    let start_load = one_minute_load();
    println!("One-minute load at the start of this run: **{start_load:.2}**.\n");
    if start_load > DIRTY_LOAD {
        println!(
            "**Refusing to measure.** The load gate is {DIRTY_LOAD:.0} and the box is at \
             {start_load:.2}. Requeue."
        );
        std::process::exit(3);
    }

    if compare {
        compare_kernels(pair.as_ref().unwrap(), samples, &widths, repeats);
        return;
    }

    for subject in subjects() {
        let points = sweep(
            subject,
            pair.as_ref(),
            operations,
            samples,
            &widths,
            repeats,
        );
        report(subject, &points);
    }

    println!(
        "\nThe control's chain is {operations} dependent field multiply-adds, which is \
         `(order/2)²/2` at order {order} — the remainder sequence's own operation count. It holds \
         two field elements in registers and allocates nothing, so its penalty at width is the \
         machine's and nothing else."
    );
    println!(
        "\nOne-minute load at the end of this run: **{:.2}**.",
        one_minute_load()
    );
}

/// Allocation calls per sample, measured at one worker.
///
/// One worker deliberately: the count per sample is a property of the algorithm, and a `fetch_add`
/// per allocation from 32 threads would be measuring the counter. **No timing from this path is
/// publishable.**
fn count_allocations(
    pair: Option<&(MultivariatePolynomial<2, K>, MultivariatePolynomial<2, K>)>,
    samples: usize,
) {
    println!("## Allocation calls per determinant, one worker\n");
    println!(
        "Counted with a wrapping global allocator. **No timing from this mode is publishable**: \
         the counter is one atomic per allocation.\n"
    );
    let Some((f, g)) = pair else {
        return;
    };
    let at: Vec<K> = (0..samples).map(|i| K::new(i as u64 + 7)).collect();
    println!("| kernel | allocation calls | per determinant |");
    println!("|---|---:|---:|");
    for kernel in [DeterminantKernel::Euclidean, DeterminantKernel::Dense] {
        // One untimed pass first, so a lazily initialized allocation inside the field or the
        // polynomial type is not counted against the kernel.
        let _ = time_sylvester_determinants(f, g, 1, &at[..1], 1, kernel);
        ALLOCATIONS.store(0, Ordering::Relaxed);
        COUNTING.store(true, Ordering::Relaxed);
        let _ = time_sylvester_determinants(f, g, 1, &at, 1, kernel);
        COUNTING.store(false, Ordering::Relaxed);
        let total = ALLOCATIONS.load(Ordering::Relaxed);
        println!(
            "| {} | {} | **{}** |",
            kernel,
            total,
            total / samples.max(1) as u64
        );
    }
}

/// Degree of `p` in variable `index`.
fn degree_in(p: &MultivariatePolynomial<2, K>, index: usize) -> u32 {
    p.terms()
        .keys()
        .map(|monomial| monomial.exponents()[index])
        .max()
        .unwrap_or(0)
}

/// The Sylvester order the pair produces when the second variable is eliminated.
fn sylvester_order(f: &MultivariatePolynomial<2, K>, g: &MultivariatePolynomial<2, K>) -> u32 {
    degree_in(f, 1) + degree_in(g, 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    // The comparison retains every sample in order, including formal-degree specialization points.
    #[test]
    fn comparison_checks_specialization_points_at_matched_widths() {
        let f = MultivariatePolynomial::parse("x*y^2 + y + 1", ["x", "y"]).unwrap();
        let g = MultivariatePolynomial::parse("x*y^2 + 2*y + 3", ["x", "y"]).unwrap();
        let at: Vec<K> = (0..8).map(K::new).collect();
        let expected: Vec<K> = at
            .iter()
            .map(|x| zeebra::grobner::resultant::sylvester_determinant_at(&f, &g, 1, *x).unwrap())
            .collect();
        for workers in [1, 2, 8] {
            for dense_first in [true, false] {
                let (values, dense, euclidean) = compare_draw(&f, &g, &at, workers, dense_first);
                assert_eq!(values, expected);
                for batch in [dense, euclidean] {
                    assert_eq!(batch.concurrency, workers);
                    assert_eq!(batch.determinants, at.len());
                    assert_eq!(batch.matrix_order, 4);
                }
                assert_eq!(dense.kernel, DeterminantKernel::Dense);
                assert_eq!(euclidean.kernel, DeterminantKernel::Euclidean);
            }
        }
    }
}
