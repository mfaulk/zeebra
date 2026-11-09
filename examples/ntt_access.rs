//! Is Zeebra's NTT bound by memory access or by arithmetic? One sweep, per field, with the
//! arithmetic comparand measured in the same run.
//!
//! D3 (issue #84) measured the arithmetic half and left this half undone; #591 is the residue, and
//! `docs/research/graeffe-root-finding.md` §6.3 is the specification this implements. The claim
//! under test is 2025/950's `4/3`-power lower bound on FFT *memory access*, which — if it binds at
//! the sizes this crate reaches — says the transform's cost is not predicted by its arithmetic
//! count. That is the one load-bearing premise of #68 that no Zeebra measurement touched.
//!
//! The shape of an answer is the **`ns / butterfly`** column against the **`coeff bytes`** column.
//! A transform that were access-bound would show `ns/butterfly` rising as the coefficient array
//! crossed L2 and then L3. One that is arithmetic-bound shows it flat, at a fixed fraction of the
//! field's own multiply rate — which is the `achieved %` column, and which is why the multiply rate
//! is measured here rather than quoted from `benches/field_arithmetic.rs`: a figure from another
//! binary, another build and another minute is not a denominator.
//!
//! **Why not KoalaBear alone**, although it is the registered challenge's field: its two-adicity
//! caps `n` at `2^24`, and `2^24` elements in eight bytes is 134 MB, which never leaves this box's
//! 256 MB L3. Over KoalaBear the question cannot be asked at all (§6.2). Goldilocks crosses L3 at
//! `2^25` and BN254 at `2^23`, so they are where the answer lives; KoalaBear stays in the sweep
//! with its ceiling reported as a result. Mersenne-31 is excluded outright — two-adicity 1, so no
//! power-of-two transform above size 2 — and the exclusion is printed rather than left implicit.
//!
//! ```text
//! cargo run --release --example ntt_access                    # all three fields, 1 s budget
//! cargo run --release --example ntt_access -- goldilocks budget=30
//! cargo run --release --example ntt_access -- list
//! ```
//!
//! Serialize it: `tools/benchlock.sh ntt-access cargo run --release --example ntt_access`. The
//! figures are throughput figures and the subject is memory traffic, so a concurrent measurement
//! does not add noise to them — it changes the quantity. The binary refuses to measure above a
//! stated one-minute load for the same reason.

use std::{
    alloc::{GlobalAlloc, Layout, System},
    sync::atomic::{AtomicUsize, Ordering},
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    evaluate,
    fields::{Bn254Fr, KoalaBear, PrimeFieldElement64},
    interpolate, FFTDomain, FiniteField, KnownOrder, Polynomial, UnivariatePolynomial,
};

// === the fields ===

/// KoalaBear, `2^31 - 2^24 + 1`, in a `u64`.
///
/// Eight bytes rather than four, matching `docs/research/graeffe-root-finding.md` §6.1's pre-#161
/// baseline exactly, so the post-#161 curve this binary prints is comparable with it row for row.
/// `fields::KoalaBear` is the same field in four bytes and is selectable as `koalabear32`.
type KoalaBearIn64 = PrimeFieldElement64<2_130_706_433>;

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

// === the cache hierarchy of this box ===
//
// Written down rather than probed, and cited: `docs/MILESTONE-SIMD-PARALLELISM.md` §8.2 records
// this machine's **256 MB L3**, which is what makes a "32 MB, out of cache" working set a
// misreading — it is out of L2 and still in L3. The L1 and L2 figures are the per-core private
// caches of the same part. A row's `cache level` is where its `coeff bytes` falls, which is the
// transform's own working set and not the implementation's temporaries.

/// Per-core L1 data cache. The one level §8.2 does not state outright; it pairs an 8/16 KB working
/// set as fitting L1, and 32 KB is this part's L1d.
const L1_BYTES: usize = 32 * 1024;

/// Per-core L2, the figure `examples/determinant_sweep.rs` already measures against.
const L2_BYTES: usize = 512 * 1024;

/// Shared L3, from `docs/MILESTONE-SIMD-PARALLELISM.md` §8.2.
const L3_BYTES: usize = 256 * 1024 * 1024;

/// Which level of the hierarchy holds `bytes`.
fn cache_level(bytes: usize) -> &'static str {
    if bytes <= L1_BYTES {
        "L1"
    } else if bytes <= L2_BYTES {
        "L2"
    } else if bytes <= L3_BYTES {
        "L3"
    } else {
        "DRAM"
    }
}

// === the sweep bounds ===

/// Smallest transform measured. Below this the timing is noise against the clock.
const FIRST_LOG: u32 = 10;

/// Largest transform measured, whatever the budget and the two-adicity allow.
///
/// A ceiling rather than a budget consequence, so that a default run cannot starve a concurrent
/// agent: at the pre-#161 rate of 217 ns/element, `2^26` is ~15 s for one field.
const CEILING_LOG: u32 = 26;

/// Wall clock a measurement must reach before its median is believed.
///
/// Below this, one `Instant` pair over a sub-millisecond transform is dominated by whatever the
/// scheduler did. The repetition count is derived from a pilot run rather than fixed, because the
/// cost per transform spans five orders of magnitude over the sweep.
const MINIMUM_TOTAL: Duration = Duration::from_millis(300);

/// Most repetitions of one transform, however fast it is.
const MAXIMUM_REPETITIONS: usize = 4096;

/// One-minute load average above which these figures are not publishable.
///
/// The same gate `examples/determinant_width.rs` uses, and for a sharper reason: the hypothesis
/// under test is about memory traffic, and L3 is shared. Ambient contention is not noise around
/// this measurement, it is the same quantity from another source.
///
/// `load-gate=N` raises it, for exercising the code path on a busy box. The gate in force and the
/// load observed are both printed on every run, so a table taken under a raised gate says so.
const DIRTY_LOAD: f64 = 8.0;

/// Sizes at which the `evaluate`/`interpolate` round trip is asserted.
///
/// Two, and both small: the check is the only evidence the timed call computed a transform rather
/// than something cheaper, and it costs one extra transform plus one inverse. Pinning it to small
/// sizes keeps the check off the critical path of the sweep it is checking.
const ROUND_TRIP_LOGS: [u32; 2] = [FIRST_LOG, FIRST_LOG + 2];

/// Bytes of operands the arithmetic comparand streams over.
///
/// 4 KB, which is inside `L1_BYTES` for every field here, so the multiply rate it reports is the
/// rate with operands resident — the right denominator for `achieved %`, because a transform that
/// achieved 100% would be running at the arithmetic rate with nothing stalling on memory.
const ARITHMETIC_WINDOW_BYTES: usize = 4096;

/// Multiply-accumulate steps the arithmetic comparand performs.
const ARITHMETIC_STEPS: usize = 4_000_000;

// === the allocator ===

/// Counts live heap bytes, so a transform's peak is exact rather than estimated.
struct Tracking;

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

/// Record a growth of the live total, raising the peak if it is one.
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

    // Delegated rather than left to the default, which would be an alloc-copy-dealloc and would
    // double-count every reallocating `Vec` push.
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

/// Run `work`, returning its value, its wall time, and the peak live heap bytes it added.
///
/// Single-threaded by construction: the counters are process-wide, so a concurrent allocation
/// elsewhere would be attributed here. This binary spawns no threads.
fn measure<T>(work: impl FnOnce() -> T) -> (T, Duration, usize) {
    let baseline = LIVE.load(Ordering::Relaxed);
    PEAK.store(baseline, Ordering::Relaxed);
    let start = Instant::now();
    let value = work();
    let elapsed = start.elapsed();
    let peak = PEAK.load(Ordering::Relaxed).saturating_sub(baseline);
    (value, elapsed, peak)
}

/// The one-minute load average, or zero where `/proc` does not carry one.
fn one_minute_load() -> f64 {
    std::fs::read_to_string("/proc/loadavg")
        .ok()
        .and_then(|line| line.split_whitespace().next()?.parse().ok())
        .unwrap_or(0.0)
}

// === the arithmetic comparand ===

/// Two field-multiplication rates per second, measured here, over operands resident in L1.
///
/// Both, because the two existing comparands in this repository are these two and they differ by
/// more than the result does:
///
/// - **isolated** — `black_box(black_box(x) * black_box(y))`, the shape of
///   `benches/field_arithmetic.rs`'s `isolated/mul` arm, and what §6.3 specifies. Nothing carries
///   between iterations, so it measures the multiply and not a dependency chain.
/// - **accumulated** — `acc += a[i] * b[i]`, the shape §6.1's pre-#161 baseline used. The addition
///   serialises, so this is a **lower bound** on multiplication throughput; against it, a 32-byte
///   field's transform can read as achieving over 100%, which is a statement about the denominator
///   and not about the transform.
///
/// `achieved %` is quoted against **isolated**. `std::hint::black_box` is load-bearing in both:
/// without it LLVM deletes the loop, which is how a stage meant to be quadratic once measured a
/// fitted exponent of 0.12.
struct MultiplyRates {
    isolated: f64,
    accumulated: f64,
}

fn multiply_rates<F: FiniteField>(seed: u64) -> MultiplyRates {
    let window = (ARITHMETIC_WINDOW_BYTES / std::mem::size_of::<F>()).max(2);
    let mut rng = StdRng::seed_from_u64(seed);
    let a: Vec<F> = (0..window).map(|_| F::random(&mut rng)).collect();
    let b: Vec<F> = (0..window).map(|_| F::random(&mut rng)).collect();

    // One untimed pass, so the first timed multiply is not also a cold miss on `a` and `b`.
    let mut warm = F::zero();
    for index in 0..window {
        warm += a[index] * b[index];
    }
    std::hint::black_box(warm);

    let start = Instant::now();
    let mut index = 0usize;
    for _ in 0..ARITHMETIC_STEPS {
        std::hint::black_box(std::hint::black_box(a[index]) * std::hint::black_box(b[index]));
        index += 1;
        if index == window {
            index = 0;
        }
    }
    let isolated = ARITHMETIC_STEPS as f64 / start.elapsed().as_secs_f64();

    let start = Instant::now();
    let mut accumulator = F::zero();
    let mut index = 0usize;
    for _ in 0..ARITHMETIC_STEPS {
        accumulator += a[index] * b[index];
        index += 1;
        if index == window {
            index = 0;
        }
    }
    std::hint::black_box(accumulator);
    let accumulated = ARITHMETIC_STEPS as f64 / start.elapsed().as_secs_f64();

    MultiplyRates {
        isolated,
        accumulated,
    }
}

// === the sweep ===

/// One measured transform size.
struct Row {
    log_n: u32,
    n: usize,
    /// `n * size_of::<F>()`: the transform's own working set.
    coefficient_bytes: usize,
    /// Peak live heap bytes the measured call added, from the counting allocator.
    peak_bytes: usize,
    /// Median seconds over `repetitions` transforms.
    seconds: f64,
    repetitions: usize,
}

impl Row {
    /// Butterflies in a radix-2 transform of this size: `(n/2) * log2 n`.
    fn butterflies(&self) -> f64 {
        (self.n as f64 / 2.0) * self.log_n as f64
    }

    /// Nanoseconds per butterfly — the headline curve.
    ///
    /// Charged against the textbook `(n/2)·log2 n` count at one multiplication each, which is an
    /// **over**-count of the multiplications a real radix-2 kernel performs: its first stage's
    /// twiddle factors are all one. So `achieved %` can exceed 100, most visibly at the smallest
    /// sizes where that stage is the largest fraction of `log2 n` — a statement about the charge,
    /// not a transform beating its own field arithmetic.
    fn nanos_per_butterfly(&self) -> f64 {
        self.seconds * 1e9 / self.butterflies()
    }

    /// Effective multiplications per second, charging one butterfly one multiplication.
    fn effective_rate(&self) -> f64 {
        self.butterflies() / self.seconds
    }
}

/// What ended a sweep. Printed, because "stopped at `2^24`" means two different things.
enum Stop {
    /// A measurement exceeded the budget. Carries the size that did.
    Budget(usize),
    /// The field's two-adicity admits no larger power-of-two transform.
    TwoAdicity(u32),
    /// `CEILING_LOG` was reached with time to spare.
    Ceiling,
}

impl Stop {
    fn summary(&self) -> String {
        match self {
            Stop::Budget(n) => format!("n = {n} exceeded the budget"),
            Stop::TwoAdicity(s) => {
                format!("the field's two-adicity is {s}, so 2^{s} is the largest radix-2 transform")
            }
            Stop::Ceiling => format!("reached the unconditional 2^{CEILING_LOG} ceiling"),
        }
    }
}

/// Median of `values`, which is sorted in place.
fn median(values: &mut [f64]) -> f64 {
    values.sort_by(|a, b| a.partial_cmp(b).expect("no NaN in a duration"));
    let middle = values.len() / 2;
    if values.len().is_multiple_of(2) {
        (values[middle - 1] + values[middle]) / 2.0
    } else {
        values[middle]
    }
}

/// Time one forward transform of size `n`, repeated enough to clear [`MINIMUM_TOTAL`].
///
/// The polynomial and the domain are built outside the timed region: a domain of `n` powers is
/// itself `n * size_of::<F>()` bytes and one pass to fill, which would be charged to the transform.
fn time_transform<F: KnownOrder>(log_n: u32, seed: u64) -> Row {
    let n = 1usize << log_n;
    let mut rng = StdRng::seed_from_u64(seed ^ u64::from(log_n));
    let root = F::two_adic_root_of_unity(log_n, &mut rng);
    let domain = FFTDomain::from_generator(root, n);
    let polynomial = UnivariatePolynomial::<F>::rand(n as u64 - 1, &mut rng);

    // A pilot transform fixes both the repetition count and the peak, since every repetition
    // allocates the same way.
    let (values, pilot, peak_bytes) = measure(|| evaluate(&polynomial, &domain));
    assert_eq!(
        values.len(),
        n,
        "a size-{n} transform returned {} values",
        values.len()
    );

    let repetitions = if pilot.is_zero() {
        MAXIMUM_REPETITIONS
    } else {
        (MINIMUM_TOTAL.as_secs_f64() / pilot.as_secs_f64()).ceil() as usize
    }
    .clamp(1, MAXIMUM_REPETITIONS);

    let mut draws = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        let start = Instant::now();
        let values = evaluate(&polynomial, &domain);
        let elapsed = start.elapsed();
        std::hint::black_box(&values);
        draws.push(elapsed.as_secs_f64());
    }

    Row {
        log_n,
        n,
        coefficient_bytes: n * std::mem::size_of::<F>(),
        peak_bytes,
        seconds: median(&mut draws),
        repetitions,
    }
}

/// Assert `interpolate(evaluate(p)) == p` at [`ROUND_TRIP_LOGS`].
///
/// The only check that the timed call is a transform. Returns the sizes checked, for the report.
fn assert_round_trip<F: KnownOrder>(two_adicity: u32, seed: u64) -> Vec<usize> {
    let mut checked = Vec::new();
    for log_n in ROUND_TRIP_LOGS {
        if log_n > two_adicity {
            continue;
        }
        let n = 1usize << log_n;
        let mut rng = StdRng::seed_from_u64(seed ^ 0x5173 ^ u64::from(log_n));
        let root = F::two_adic_root_of_unity(log_n, &mut rng);
        let domain = FFTDomain::from_generator(root, n);
        let polynomial = UnivariatePolynomial::<F>::rand(n as u64 - 1, &mut rng);
        let recovered = interpolate(&evaluate(&polynomial, &domain), &domain);
        assert_eq!(
            recovered, polynomial,
            "interpolate did not invert evaluate at n = {n}"
        );
        checked.push(n);
    }
    checked
}

/// Sweep one field and print its table.
fn measure_field<F: KnownOrder>(name: &str, criterion_arm: &str, budget: Duration, seed: u64) {
    let element_bytes = std::mem::size_of::<F>();
    let two_adicity = F::two_adicity();

    println!("\n\n## {name}");
    println!();
    println!("- an element is {element_bytes} bytes, so a size-n coefficient array is {element_bytes}n bytes");
    println!(
        "- two-adicity s = {two_adicity}, so the largest radix-2 transform is 2^{two_adicity} \
         ({} at {element_bytes} bytes an element)",
        bytes_human((1usize << two_adicity.min(63)).saturating_mul(element_bytes))
    );
    let ceiling_bytes = (1usize << two_adicity.min(63)).saturating_mul(element_bytes);
    if ceiling_bytes <= L3_BYTES {
        println!(
            "- **this field cannot answer the access-bound question on this box**: its largest \
             coefficient array, {}, still fits the {} L3",
            bytes_human(ceiling_bytes),
            bytes_human(L3_BYTES)
        );
    } else {
        let mut crossing = two_adicity;
        for log_n in FIRST_LOG..=two_adicity {
            if (1usize << log_n) * element_bytes > L3_BYTES {
                crossing = log_n;
                break;
            }
        }
        println!(
            "- the coefficient array leaves the {} L3 at n = 2^{crossing}",
            bytes_human(L3_BYTES)
        );
    }

    let checked = assert_round_trip::<F>(two_adicity, seed);
    println!(
        "- `interpolate(evaluate(p)) == p` asserted at n = {}",
        checked
            .iter()
            .map(|n| n.to_string())
            .collect::<Vec<_>>()
            .join(" and ")
    );

    let rates = multiply_rates::<F>(seed ^ 0xa417);
    let rate = rates.isolated;
    println!(
        "- multiply rate measured in this run, over a {}-element L1-resident window: **{:.1} M \
         mul/s isolated** ({:.3} ns a multiply), and {:.1} M mul/s accumulated ({:.3} ns a \
         multiply-accumulate). `achieved` below is against the isolated figure, which is what \
         §6.3 specifies; the accumulated one is the shape §6.1's pre-#161 baseline used and is a \
         lower bound, because its additions serialise.",
        ARITHMETIC_WINDOW_BYTES / element_bytes,
        rates.isolated / 1e6,
        1e9 / rates.isolated,
        rates.accumulated / 1e6,
        1e9 / rates.accumulated
    );
    println!(
        "- compare `cargo bench --bench field_arithmetic -- field/isolated/mul/{criterion_arm}`, \
         which measures the same field in the same number of bytes. A divergence between the two \
         is a divergence between two programs and not a result."
    );

    let mut rows = Vec::new();
    let mut stop = Stop::Ceiling;
    for log_n in FIRST_LOG..=CEILING_LOG {
        if log_n > two_adicity {
            stop = Stop::TwoAdicity(two_adicity);
            break;
        }
        let row = time_transform::<F>(log_n, seed);
        let over_budget = row.seconds > budget.as_secs_f64();
        let n = row.n;
        rows.push(row);
        if over_budget {
            stop = Stop::Budget(n);
            break;
        }
    }

    println!();
    println!(
        "| {:>5} | {:>11} | {:>11} | {:>11} | {:>5} | {:>5} | {:>12} | {:>14} | {:>12} | {:>10} | {:>8} |",
        "log2 n",
        "n",
        "coeff bytes",
        "peak bytes",
        "p/c",
        "reps",
        "s/transform",
        "ns/butterfly",
        "eff. Mmul/s",
        "arith Mmul/s",
        "achieved"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(8),
        "-".repeat(13),
        "-".repeat(13),
        "-".repeat(13),
        "-".repeat(7),
        "-".repeat(7),
        "-".repeat(14),
        "-".repeat(16),
        "-".repeat(14),
        "-".repeat(12),
        "-".repeat(10)
    );
    for row in &rows {
        println!(
            "| {:>6} | {:>11} | {:>11} | {:>11} | {:>5.2} | {:>5} | {:>12.6} | {:>14.2} | {:>12.1} | {:>10.1} | {:>7.1}% |",
            row.log_n,
            row.n,
            bytes_human(row.coefficient_bytes),
            bytes_human(row.peak_bytes),
            row.peak_bytes as f64 / row.coefficient_bytes as f64,
            row.repetitions,
            row.seconds,
            row.nanos_per_butterfly(),
            row.effective_rate() / 1e6,
            rate / 1e6,
            100.0 * row.effective_rate() / rate
        );
    }

    println!();
    println!("Stopped: {}.", stop.summary());

    // The verdict for this field, from its own rows rather than from prose: an access-bound
    // transform's `ns/butterfly` rises with the working set, so the comparison that matters is the
    // largest in-L3 row against the largest DRAM row, and the spread over the whole sweep.
    if rows.len() >= 2 {
        let nanos: Vec<f64> = rows.iter().map(Row::nanos_per_butterfly).collect();
        let smallest = nanos[0];
        let largest = nanos[nanos.len() - 1];
        let low = nanos.iter().copied().fold(f64::INFINITY, f64::min);
        let high = nanos.iter().copied().fold(0.0, f64::max);
        println!(
            "`ns/butterfly` spans {low:.2} to {high:.2} over this sweep, a spread of {:+.1}% \
             about the median; {smallest:.2} at n = 2^{} against {largest:.2} at n = 2^{}.",
            100.0 * (high - low) / ((high + low) / 2.0),
            rows[0].log_n,
            rows[rows.len() - 1].log_n
        );
        let crossed: Vec<&Row> = rows
            .iter()
            .filter(|row| row.coefficient_bytes > L3_BYTES)
            .collect();
        if crossed.is_empty() {
            println!(
                "No row's coefficient array left the {} L3, so **this field's rows cannot \
                 falsify the access bound** — only confirm that it does not bind below L3.",
                bytes_human(L3_BYTES)
            );
        } else {
            let in_cache: Vec<&Row> = rows
                .iter()
                .filter(|row| row.coefficient_bytes <= L3_BYTES)
                .collect();
            let last_in = in_cache
                .last()
                .expect("a sweep that left L3 had a row inside it");
            let first_out = crossed[0];
            println!(
                "Across the L3 boundary: {:.2} ns/butterfly at n = 2^{} ({}, {}) against {:.2} at \
                 n = 2^{} ({}, {}) — **{:+.1}%**.",
                last_in.nanos_per_butterfly(),
                last_in.log_n,
                bytes_human(last_in.coefficient_bytes),
                cache_level(last_in.coefficient_bytes),
                first_out.nanos_per_butterfly(),
                first_out.log_n,
                bytes_human(first_out.coefficient_bytes),
                cache_level(first_out.coefficient_bytes),
                100.0 * (first_out.nanos_per_butterfly() - last_in.nanos_per_butterfly())
                    / last_in.nanos_per_butterfly()
            );
        }
    }

    println!();
    println!("Cache level of each row's **coefficient array** — the transform's own working set, not the implementation's temporaries:");
    println!();
    for row in &rows {
        println!(
            "- n = 2^{:<2} {:>11} — {}",
            row.log_n,
            bytes_human(row.coefficient_bytes),
            cache_level(row.coefficient_bytes)
        );
    }
}

/// Bytes as a short decimal string, so a column of them is readable.
fn bytes_human(bytes: usize) -> String {
    const UNITS: [(usize, &str); 4] = [
        (1024 * 1024 * 1024, "GB"),
        (1024 * 1024, "MB"),
        (1024, "KB"),
        (1, "B"),
    ];
    for (scale, unit) in UNITS {
        if bytes >= scale {
            if scale == 1 {
                return format!("{bytes} {unit}");
            }
            return format!("{:.1} {unit}", bytes as f64 / scale as f64);
        }
    }
    "0 B".to_string()
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();

    let mut selector = "all".to_string();
    let mut budget = Duration::from_secs_f64(1.0);
    let mut gate = DIRTY_LOAD;
    for argument in &arguments {
        if let Some(seconds) = argument.strip_prefix("budget=") {
            budget =
                Duration::from_secs_f64(seconds.parse().expect("budget=SECONDS takes a number"));
        } else if let Some(value) = argument.strip_prefix("load-gate=") {
            gate = value.parse().expect("load-gate=LOAD takes a number");
        } else {
            selector = argument.clone();
        }
    }

    if selector == "list" {
        println!("fields: all, koalabear, goldilocks, bn254, koalabear32");
        println!("        `all` is koalabear, goldilocks, bn254 — the three §6.3 specifies.");
        println!(
            "        koalabear32 is the same field in a u32, selectable but not in `all`: it \
             halves the working set without changing the arithmetic, which is the access axis with \
             the field held fixed."
        );
        println!(
            "        mersenne31 is excluded and cannot be selected: two-adicity 1, so no \
             power-of-two transform above size 2."
        );
        println!("options: budget=SECONDS (default 1.0), the wall clock allowed per transform");
        println!(
            "         load-gate=LOAD (default {DIRTY_LOAD:.0}) raises the one-minute load this \
             refuses to measure above. For exercising the sweep on a busy box; a table taken \
             under a raised gate is not a figure."
        );
        return;
    }

    println!("# Is the NTT access-bound? A size sweep against the in-run multiply rate");
    println!();
    println!("ISA: {}", zeebra::util::isa_floor());
    println!();

    // Read where the timers are about to start, not where the lock was requested: a sweep can wait
    // a long time for the benchlock, and the load it gated on is stale by then.
    let load = one_minute_load();
    println!(
        "One-minute load at the start of this run: **{load:.2}**, against a gate of {gate:.2}."
    );
    if load > gate {
        println!();
        println!(
            "**Refusing to measure.** The gate is {gate:.2} and the box is at {load:.2}. The \
             subject here is memory traffic and L3 is shared, so a figure taken under contention \
             is not a noisy version of the right number — it is a different number. Requeue under \
             `tools/benchlock.sh`."
        );
        std::process::exit(3);
    }
    if gate > DIRTY_LOAD {
        println!();
        println!(
            "**These numbers are not figures.** `load-gate={gate:.2}` raises the publishable gate \
             of {DIRTY_LOAD:.0}, which exists because this measurement's subject is shared-cache \
             traffic. Anything below is an exercise of the sweep, not a result."
        );
    }

    println!();
    println!(
        "Each field doubles its transform size from 2^{FIRST_LOG} until one transform exceeds \
         {:.2} s, the field's two-adicity runs out, or the unconditional 2^{CEILING_LOG} ceiling \
         is reached — whichever comes first, and which one is printed. Each row is the **median** \
         of as many repetitions as clear {} ms in total. `peak bytes` is peak live heap from a \
         counting allocator attributed to the measured call, not process RSS; `p/c` is that over \
         `coeff bytes`, the implementation's multiplier.",
        budget.as_secs_f64(),
        MINIMUM_TOTAL.as_millis()
    );
    println!();
    println!(
        "`ns/butterfly` charges a radix-2 transform `(n/2)·log2 n` butterflies and one \
         multiplication each. `arith Mmul/s` is measured **in this run and this binary** over an \
         L1-resident window, and `achieved` is the ratio: it is the access-bound verdict per row."
    );
    println!();
    println!(
        "Mersenne-31 is excluded from this sweep. Its two-adicity is 1, so it admits no \
         power-of-two transform above size 2 (`docs/research/fast-univariate.md` §1.1) — the \
         exclusion is a property of the field, not a choice about coverage."
    );

    let run_all = selector == "all";
    if run_all || selector == "koalabear" {
        measure_field::<KoalaBearIn64>(
            "KoalaBear, 2^31 - 2^24 + 1, in a u64",
            "p31_koalabear",
            budget,
            0x4b0a,
        );
    }
    if selector == "koalabear32" {
        measure_field::<KoalaBear>(
            "KoalaBear, 2^31 - 2^24 + 1, in a u32",
            "p31_koalabear",
            budget,
            0x4b0a,
        );
    }
    if run_all || selector == "goldilocks" {
        measure_field::<Goldilocks>(
            "Goldilocks, 2^64 - 2^32 + 1",
            "p64_goldilocks",
            budget,
            0x601d,
        );
    }
    if run_all || selector == "bn254" {
        measure_field::<Bn254Fr>("BN254 Fr, 254 bits", "p254_bn254", budget, 0xb254);
    }

    // A ceiling on recent usage rather than a per-row figure; the `peak bytes` column is what to
    // quote. Printed so the two can be compared.
    if let Some(peak) = zeebra::util::peak_resident_bytes() {
        println!("\n\nprocess peak resident bytes: {peak}");
    }
}
