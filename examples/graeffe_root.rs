//! What Graeffe root finding costs against degree, stage by stage, with the quadratic comparand.
//!
//! Gate D of #84. The target degree is `3^13 = 1 594 323` over KoalaBear — the working degree of
//! the disclosed `R_P = 8` CICO-2 solve (`docs/research/elimination-beyond-grobner.md` §2.1) —
//! which needs order-2 Graeffe steps over domains of `2^21` points, inside KoalaBear's two-adic
//! ceiling of `2^24`.
//!
//! Three things are reported separately, because they answer differently:
//!
//! 1. **The Graeffe ladder.** Per degree: the three stages of [`graeffe_root_with_stats`], the
//!    number of transforms and their sizes, and peak memory measured and estimated.
//! 2. **The `roots` comparand**, the crate's existing `O(log q * d^2)` gcd-based finder, swept by
//!    doubling until a measurement exceeds the budget. It does not reach `3^13`; the largest
//!    degree it *does* reach is printed, and any statement about `3^13` on that side is an
//!    extrapolation of this measured curve rather than a measurement.
//! 3. **What none of it is evidence for** — printed, not left to the reader.
//!
//! ```text
//! cargo run --release --example graeffe_root
//! cargo run --release --example graeffe_root -- list
//! cargo run --release --example graeffe_root -- koalabear degrees=6561,19683
//! cargo run --release --example graeffe_root -- all budget=5.0
//! cargo run --release --example graeffe_root -- koalabear no-comparand
//! ```
//!
//! Pin the run, as `tools/scoreboard.sh` does, and give it a private target directory:
//!
//! ```text
//! RUSTC_WRAPPER="" CARGO_TARGET_DIR=/path/to/target \
//!   cargo build --release --example graeffe_root
//! taskset --cpu-list 8 /path/to/target/release/examples/graeffe_root
//! ```
//!
//! The binary is single-threaded, so one core is the whole measurement.

use std::{
    alloc::{GlobalAlloc, Layout, System},
    sync::atomic::{AtomicUsize, Ordering},
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::{two_adic::two_adic_decomposition, KoalaBear, PrimeFieldElement64},
    graeffe_root_with_stats, roots, FiniteField, GraeffeStats, KnownOrder, Polynomial,
    UnivariatePolynomial,
};

// === the fields ===

/// KoalaBear, `2^31 - 2^24 + 1`, in a `u64`.
///
/// The width `docs/research/graeffe-root-finding.md` §6.1's transform curve was taken at, so the
/// per-transform figures here are comparable with it.
type KoalaBearIn64 = PrimeFieldElement64<2_130_706_433>;

/// Goldilocks, `2^64 - 2^32 + 1`, whose odd part is `2^32 - 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// `3^13`, the degree of the disclosed `R_P = 8` solve's univariate.
const TARGET_DEGREE: usize = 1_594_323;

/// How many roots are planted. Four, as `examples/univariate_scaling.rs` plants, so the two
/// **roots** rows measure the same shape of problem.
const PLANTED: usize = 4;

/// The pre-#161 recursive NTT's peak live heap, as a multiple of the coefficient array.
///
/// `docs/research/fast-univariate.md` §3.2 measures `7 n B`; §6.1's table prints it per row. Used
/// only in the *estimated* memory column, which is printed beside the measured one rather than
/// instead of it.
const RECURSIVE_NTT_MULTIPLIER: usize = 7;

// === the allocator ===

/// Counts live heap bytes, so a stage's peak is exact rather than estimated.
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

// === the input ===

/// A polynomial of exactly `degree` with `PLANTED` roots planted in a random cofactor.
///
/// The shape an interpolated output coordinate leaves behind: a high-degree polynomial with a
/// handful of base-field roots. Building the full product of `degree` linear factors would be
/// quadratic and would dominate the measurement.
fn with_planted_roots<F: FiniteField, R: Rng>(
    degree: usize,
    rng: &mut R,
) -> (UnivariatePolynomial<F>, Vec<F>) {
    let mut planted: Vec<F> = Vec::with_capacity(PLANTED);
    while planted.len() < PLANTED {
        let candidate = F::new(rng.gen::<u32>() as u64);
        if !candidate.is_zero() && !planted.contains(&candidate) {
            planted.push(candidate);
        }
    }

    let cofactor_degree = degree - PLANTED;
    let mut coefficients: Vec<F> = (0..=cofactor_degree)
        .map(|_| F::new(rng.gen::<u32>() as u64))
        .collect();
    while coefficients[cofactor_degree].is_zero() {
        coefficients[cofactor_degree] = F::new(rng.gen::<u32>() as u64);
    }
    let cofactor = UnivariatePolynomial::new(&coefficients);
    let f = &cofactor * &UnivariatePolynomial::from_zeros(&planted);
    (f, planted)
}

// === the Graeffe ladder ===

/// A markdown table rule: a dashed cell of each given width, pipe-separated.
fn rule(widths: &[usize]) -> String {
    let mut line = String::from("|");
    for width in widths {
        line.push_str(&"-".repeat(*width));
        line.push('|');
    }
    line
}

/// One measured Graeffe root find.
struct GraeffeRow {
    degree: usize,
    total: Duration,
    peak_bytes: usize,
    stats: GraeffeStats,
    found: bool,
}

/// What the implementation's memory *should* be, in bytes, from the stage's own structure.
///
/// Two terms, and they are the two the report has to separate: the retained `G_{2^i}`, which is
/// what the descent needs, and the largest transform's temporaries, which `RECURSIVE_NTT_MULTIPLIER`
/// charges at the pre-#161 kernel's measured multiple of the coefficient array.
fn estimated_bytes<F>(stats: &GraeffeStats) -> usize {
    let element = std::mem::size_of::<F>();
    element * (stats.stored_coefficients + RECURSIVE_NTT_MULTIPLIER * stats.max_transform_size)
}

/// Run the Graeffe ladder over F and print it.
fn graeffe_ladder<F: KnownOrder>(name: &str, degrees: &[usize], budget: Duration, seed: u64) {
    let element = std::mem::size_of::<F>();
    let (two_adicity, odd_part) = two_adic_decomposition(F::order_limbs());
    println!("\n\n## {name}");
    println!();
    println!("- an element is {element} bytes");
    println!(
        "- two-adicity s = {two_adicity}, so the largest power-of-two domain is 2^{two_adicity}"
    );
    println!(
        "- the odd part of q - 1 is {}, which is the order of the subgroup the iteration leaves \
         the roots in",
        odd_part
            .iter()
            .rev()
            .map(|limb| limb.to_string())
            .collect::<Vec<_>>()
            .join(":")
    );

    let mut rows: Vec<GraeffeRow> = Vec::new();
    for &degree in degrees {
        let mut rng = StdRng::seed_from_u64(seed ^ degree as u64);
        let (f, planted) = with_planted_roots::<F, _>(degree, &mut rng);
        assert_eq!(
            f.degree() as usize,
            degree,
            "the input is not of degree {degree}"
        );

        let (result, total, peak_bytes) = measure(|| graeffe_root_with_stats(&f, &mut rng));
        let (outcome, stats) = match result {
            Ok(pair) => pair,
            Err(error) => {
                println!("\ndegree {degree}: {error}");
                break;
            }
        };
        let found = match outcome {
            Some(root) => {
                assert!(
                    f.eval(&root).is_zero(),
                    "degree {degree}: {root} is not a root"
                );
                true
            }
            None => false,
        };
        assert!(
            found,
            "degree {degree}: {PLANTED} roots were planted, among them {}",
            planted[0]
        );

        rows.push(GraeffeRow {
            degree,
            total,
            peak_bytes,
            stats,
            found,
        });
        if total > budget {
            println!(
                "\nstopped: degree {degree} exceeded the {:.2} s budget",
                budget.as_secs_f64()
            );
            break;
        }
    }

    println!("\n### Stage-separated cost");
    println!();
    println!(
        "| {:>9} | {:>7} | {:>7} | {:>6} | {:>9} | {:>9} | {:>8} | {:>9} |",
        "degree", "log2 d", "steps", "xforms", "forward s", "subgrp s", "descent s", "total s"
    );
    println!("{}", rule(&[11, 9, 9, 8, 11, 11, 10, 11]));
    for row in &rows {
        println!(
            "| {:>9} | {:>7.2} | {:>7} | {:>6} | {:>9.4} | {:>9.6} | {:>8.6} | {:>9.4} |",
            row.degree,
            (row.degree as f64).log2(),
            row.stats.graeffe_steps,
            row.stats.transforms,
            row.stats.forward_time.as_secs_f64(),
            row.stats.subgroup_time.as_secs_f64(),
            row.stats.descent_time.as_secs_f64(),
            row.total.as_secs_f64(),
        );
    }

    println!("\n### Transform sizes, memory and the subgroup search");
    println!();
    println!(
        "`peak bytes` is peak live heap from a counting allocator, attributed to the call alone. \
         `est. bytes` is the retained `G_(2^i)` plus {RECURSIVE_NTT_MULTIPLIER} x the largest \
         transform, which is the pre-#161 recursive kernel's measured multiple."
    );
    println!();
    println!(
        "| {:>9} | {:>10} | {:>13} | {:>11} | {:>12} | {:>12} | {:>8} | {:>7} | {:>5} |",
        "degree",
        "log2 max n",
        "sum n / max n",
        "final deg",
        "peak bytes",
        "est. bytes",
        "stored",
        "cands",
        "root"
    );
    println!("{}", rule(&[11, 12, 15, 13, 14, 14, 10, 9, 7]));
    for row in &rows {
        let stats = &row.stats;
        println!(
            "| {:>9} | {:>10} | {:>13.2} | {:>11} | {:>12} | {:>12} | {:>8} | {:>7} | {:>5} |",
            row.degree,
            stats.max_transform_size.trailing_zeros(),
            stats.total_transform_elements as f64 / stats.max_transform_size as f64,
            stats.final_degree,
            row.peak_bytes,
            estimated_bytes::<F>(stats),
            stats.stored_coefficients,
            stats.candidates,
            row.found,
        );
    }

    if let Some(last) = rows.last() {
        println!();
        println!(
            "The subgroup search took the {:?} route at the largest degree.",
            last.stats.subgroup_route
        );
        println!(
            "Largest degree completed: {} (log2 {:.2}), in {:.4} s.",
            last.degree,
            (last.degree as f64).log2(),
            last.total.as_secs_f64()
        );
        if last.degree >= TARGET_DEGREE {
            println!(
                "This reaches the 3^13 = {TARGET_DEGREE} target degree of the disclosed R_P = 8 \
                 solve."
            );
        } else {
            println!("This does **not** reach the 3^13 = {TARGET_DEGREE} target degree.");
        }
    }
}

// === the comparand ===

/// Sweep `roots` by doubling until a measurement exceeds the budget, and print the curve.
///
/// The same planted-root shape as the ladder above, so the two are the same problem at the same
/// degree. This is the measured half of the comparison; nothing here is extrapolated.
fn roots_comparand<F: KnownOrder>(name: &str, budget: Duration, seed: u64) {
    println!("\n\n## `roots` comparand over {name}");
    println!();
    println!(
        "`src/poly/univariate/roots.rs`, the crate's existing gcd-based finder: `x^q mod f` by \
         square-and-multiply with schoolbook multiplication and division, so `O(log q * d^2)`. \
         Doubling until one measurement exceeds {:.2} s.",
        budget.as_secs_f64()
    );
    println!();
    println!(
        "| {:>9} | {:>7} | {:>10} | {:>12} | {:>8} |",
        "degree", "log2 d", "seconds", "peak bytes", "exponent"
    );
    println!("{}", rule(&[11, 9, 12, 14, 10]));

    let mut previous: Option<(usize, f64)> = None;
    let mut last: Option<(usize, f64)> = None;
    for log_degree in 8..=24u32 {
        let degree = 1usize << log_degree;
        let mut rng = StdRng::seed_from_u64(seed ^ degree as u64);
        let (f, planted) = with_planted_roots::<F, _>(degree, &mut rng);
        let (found, elapsed, peak_bytes) = measure(|| roots(&f, &mut rng));
        for root in &planted {
            assert!(
                found.contains(root),
                "degree {degree}: a planted root was missed"
            );
        }

        let seconds = elapsed.as_secs_f64();
        let exponent = match previous {
            Some((_, before)) if before > 0.0 => format!("{:.2}", (seconds / before).log2()),
            _ => "-".to_string(),
        };
        println!(
            "| {:>9} | {:>7} | {:>10.4} | {:>12} | {:>8} |",
            degree, log_degree, seconds, peak_bytes, exponent
        );
        previous = Some((degree, seconds));
        last = Some((degree, seconds));
        if elapsed > budget {
            break;
        }
    }

    if let Some((degree, seconds)) = last {
        println!();
        println!(
            "**Largest degree `roots` reached: {degree} in {seconds:.4} s.** It does not reach \
             3^13 = {TARGET_DEGREE}."
        );
        // Quadratic in the degree, which the exponent column above is there to check rather than
        // assume. Printed as an extrapolation and labelled as one.
        let ratio = TARGET_DEGREE as f64 / degree as f64;
        let extrapolated = seconds * ratio * ratio;
        println!(
            "Extrapolating the measured quadratic growth to 3^13: {:.0} s = {:.1} hours. \
             **An extrapolation of `roots`, not a measurement of it.**",
            extrapolated,
            extrapolated / 3600.0
        );
    }
}

// === what this is not ===

/// Print the scope statement, so it travels with the numbers rather than beside them.
fn print_scope() {
    println!("\n\n## What these figures are, and are not");
    println!();
    println!(
        "- A working order-2 transform validated against directly squared roots is a **unit \
         test**. It establishes correctness of one transform and nothing about a challenge."
    );
    println!(
        "- A degree-3^13 root find completing is a **benchmark of one stage of one family**. Per \
         the scoreboard's class discipline this is `BenchmarkClass::Engineering` and could not be \
         anything else until it produces a witness verified through the permutation."
    );
    println!(
        "- It is **not** evidence about `poseidon31-cico-rf6-rp8`. The per-family cost measured \
         here is separate from the number of families a CICO-2 witness needs, which is an open \
         question tracked in `docs/research/graeffe-root-finding.md` §11 — §9.3's estimate there \
         is marked superseded pending verification and is not quoted."
    );
    println!(
        "- Nothing here reproduces the published attack. Three attack-specific components are \
         absent: the round-skipping parametrization, the univariate construction, and candidate \
         reconstruction through the permutation."
    );
    println!(
        "- Timings are **pre-#161**: the NTT kernel is the recursive one that `fast-univariate.md` \
         §3.2 measures at a `7 n B` peak, and #161's iterative in-place kernel will improve both \
         the time and the memory columns."
    );
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();

    let mut selector = "koalabear".to_string();
    let mut budget = Duration::from_secs_f64(60.0);
    let mut degrees: Vec<usize> = Vec::new();
    let mut comparand = true;
    for argument in &arguments {
        if let Some(seconds) = argument.strip_prefix("budget=") {
            budget =
                Duration::from_secs_f64(seconds.parse().expect("budget=SECONDS takes a number"));
        } else if let Some(list) = argument.strip_prefix("degrees=") {
            degrees = list
                .split(',')
                .map(|n| {
                    n.trim()
                        .parse()
                        .expect("degrees= takes a comma-separated list")
                })
                .collect();
        } else if argument == "no-comparand" {
            comparand = false;
        } else {
            selector = argument.clone();
        }
    }

    if selector == "list" {
        println!("fields: all, koalabear, koalabear32, goldilocks");
        println!("options: budget=SECONDS (default 60.0), the wall clock allowed per measurement");
        println!("         degrees=N,N,... replaces the default 3^k ladder");
        println!("         no-comparand skips the `roots` sweep");
        return;
    }

    // Powers of three up to 3^13, because 3^13 is the degree the disclosed solve works at and the
    // ladder is there to show the approach to it rather than to fill a power-of-two grid.
    if degrees.is_empty() {
        degrees = (6..=13).map(|k| 3usize.pow(k)).collect();
    }

    println!("# Graeffe root finding: stage-separated cost against degree");
    println!();
    println!(
        "`graeffe_root` is [P937] Algorithm 2's forward phase with [P937] §5.3's progressive \
         degree reduction and [PC] Algorithm 2 line 8's gcd descent. See \
         `docs/research/graeffe-root-finding.md` §3.5 and §3.6."
    );
    println!();
    println!("Degrees: {degrees:?}");

    let run_all = selector == "all";
    if run_all || selector == "koalabear" {
        graeffe_ladder::<KoalaBearIn64>(
            "KoalaBear, 2^31 - 2^24 + 1, in a u64",
            &degrees,
            budget,
            0x4b0a,
        );
    }
    if run_all || selector == "koalabear32" {
        graeffe_ladder::<KoalaBear>(
            "KoalaBear, 2^31 - 2^24 + 1, in a u32",
            &degrees,
            budget,
            0x4b32,
        );
    }
    if run_all || selector == "goldilocks" {
        graeffe_ladder::<Goldilocks>("Goldilocks, 2^64 - 2^32 + 1", &degrees, budget, 0x601d);
    }

    if comparand {
        roots_comparand::<KoalaBearIn64>("KoalaBear in a u64", budget, 0x4b0a);
    }

    print_scope();

    if let Some(peak) = zeebra::util::peak_resident_bytes() {
        println!("\n\nprocess peak resident bytes: {peak}");
    }
}
