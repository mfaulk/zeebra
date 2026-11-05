//! What the univariate layer costs against degree, per stage, over four prime fields.
//!
//! D2 (issue #83). Both routes into #68 — the resultant of D1 and the Graeffe iteration of D3 —
//! end at one univariate polynomial of very large degree whose roots are wanted, and the published
//! work reports that stage rather than the elimination as the binding constraint. This measures
//! whether Zeebra's univariate layer reaches those degrees at all, and which stage stops first.
//!
//! Six stages per field, each swept by doubling until one measurement exceeds a wall-clock
//! budget:
//!
//! 1. **mul** — a dense product at degree `n - 1`. Schoolbook; there is no NTT-based multiply.
//! 2. **div** — `div_with_remainder` at the shape `pow_mod` reduces at: degree `2n - 2` by
//!    degree `n - 1`. Separated from **mul** because root finding spends its time here.
//! 3. **ntt** — `evaluate` over a size-n domain, which needs a primitive `2^k`-th root of unity
//!    and so is bounded by the field's two-adicity.
//! 4. **intt** — `interpolate`, which is **ntt** plus the inverse domain and the `1/n` scaling.
//! 5. **lagrange** — `lagrange_interpolate` over n points at arbitrary abscissae, which is what
//!    D1's evaluation-interpolation resultant needs and which the NTT domain cannot serve.
//! 6. **roots** — `roots` on a degree-d polynomial with four planted roots and a random cofactor,
//!    the shape a resultant leaves behind. Every planted root is asserted to be recovered.
//!
//! Memory is the **peak live heap bytes** attributed to the stage, from a counting global
//! allocator, not an estimate of what a representation holds and not process RSS. The byte
//! figures are therefore exact and comparable across fields: a dense univariate coefficient is
//! `size_of::<F>()`, which is 8 bytes for a 64-bit field and 32 for a 254-bit one — 4x, not the
//! 2.5x `docs/MILESTONE-LARGE-PRIME-FIELDS.md` §5.2 records for sparse `(usize, F)` entries,
//! because there is no index word here to amortize the difference.
//!
//! ```text
//! cargo run --release --example univariate_scaling
//! cargo run --release --example univariate_scaling -- list
//! cargo run --release --example univariate_scaling -- bn254
//! cargo run --release --example univariate_scaling -- all budget=0.5
//! ```

use std::{
    alloc::{GlobalAlloc, Layout, System},
    sync::atomic::{AtomicUsize, Ordering},
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    evaluate,
    fields::{two_adic::two_adic_decomposition, Bn254Fr, PrimeFieldElement64},
    integers::highest_set_bit,
    interpolate, lagrange_interpolate, roots, FFTDomain, FiniteField, KnownOrder, Polynomial,
    UnivariatePolynomial,
};

// === the fields ===

// All four are backed by a `u64`, so `size_of::<F>()` is 8 for the three narrow ones and the peak
// byte figures are comparable across them. `fields::Mersenne31` and `fields::KoalaBear` are the
// same two fields backed by a `u32`; every peak figure below would halve over those, and nothing
// else about the curves would change, since the stages are linear in `size_of::<F>()`.

/// Mersenne-31, `2^31 - 1`. The field almost every F4 benchmark in this crate uses.
type Mersenne31In64 = PrimeFieldElement64<2_147_483_647>;

/// KoalaBear, `2^31 - 2^24 + 1`. The field the 2026 Poseidon challenges are over, chosen for
/// NTT-friendliness.
type KoalaBearIn64 = PrimeFieldElement64<2_130_706_433>;

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// How many roots are planted in the **roots** stage's polynomial.
///
/// Four rather than d: a resultant leaves a high-degree polynomial with a handful of base-field
/// roots, and splitting d linear factors would measure the splitter instead of the `x^q mod f`
/// computation that dominates.
const PLANTED: usize = 4;

/// Sizes below this are too fast to time reliably, so every sweep starts here.
const FIRST_LOG: u32 = 6;

/// No sweep goes past `2^30`, whatever the budget allows.
const CEILING_LOG: u32 = 30;

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

    // Delegated rather than left to the default, which would be an alloc-copy-dealloc. `Vec`
    // growth goes through here, so the default would also double-count a reallocating push.
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

// === the sweep ===

/// One measured point of one stage.
struct Row {
    /// `log2` of the stage's size parameter.
    log_size: u32,
    /// The size parameter: a transform size, or a degree.
    size: usize,
    elapsed: Duration,
    /// Peak live heap bytes added by the measurement.
    bytes: usize,
}

/// What ended a sweep.
enum Stop {
    /// A measurement exceeded the budget. Carries the size that did.
    Budget(usize),
    /// `CEILING_LOG` was reached with time to spare.
    Ceiling,
    /// The stage cannot run past this size at all, for the stated reason.
    Unreachable(String),
}

impl Stop {
    /// One line naming what ended the sweep, for the summary table.
    fn summary(&self) -> String {
        match self {
            Stop::Budget(size) => format!("{} exceeded the budget", size),
            Stop::Ceiling => format!("reached the 2^{} ceiling", CEILING_LOG),
            Stop::Unreachable(reason) => reason.clone(),
        }
    }
}

/// A stage's measured curve.
struct Curve {
    name: &'static str,
    rows: Vec<Row>,
    stop: Stop,
}

impl Curve {
    /// The largest size that completed.
    fn reached(&self) -> usize {
        self.rows.last().map(|row| row.size).unwrap_or(0)
    }
}

/// Double the size from `FIRST_LOG` until `once` exceeds `budget`, or the stage runs out of room.
///
/// `once` returns `None` when the stage cannot run at that size, with the reason; that ends the
/// sweep rather than skipping the point, since every stage here is monotone in size.
fn sweep(
    name: &'static str,
    budget: Duration,
    mut once: impl FnMut(u32) -> Result<(Duration, usize), String>,
) -> Curve {
    let mut rows = Vec::new();
    for log_size in FIRST_LOG..=CEILING_LOG {
        match once(log_size) {
            Err(reason) => {
                return Curve {
                    name,
                    rows,
                    stop: Stop::Unreachable(reason),
                }
            }
            Ok((elapsed, bytes)) => {
                let size = 1usize << log_size;
                rows.push(Row {
                    log_size,
                    size,
                    elapsed,
                    bytes,
                });
                if elapsed > budget {
                    return Curve {
                        name,
                        rows,
                        stop: Stop::Budget(size),
                    };
                }
            }
        }
    }
    Curve {
        name,
        rows,
        stop: Stop::Ceiling,
    }
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

/// Print a stage's curve, with the local scaling exponent between consecutive rows.
///
/// The exponent is `log2(t_i / t_{i-1})` at a doubling size, so 2 is quadratic and 3 is cubic. It
/// is what makes a claim about a stage's complexity a measurement rather than a reading of the
/// source.
fn print_curve(curve: &Curve) {
    println!("\n{} — size parameter doubles each row", curve.name);
    println!(
        "| {:>5} | {:>10} | {:>10} | {:>12} | {:>13} | {:>9} | {:>8} |",
        "log2", "size", "seconds", "ns/element", "peak bytes", "bytes/elt", "exponent"
    );
    println!("{}", rule(&[7, 12, 12, 14, 15, 11, 10]));
    for (index, row) in curve.rows.iter().enumerate() {
        let nanos = row.elapsed.as_secs_f64() * 1e9;
        let exponent = if index == 0 {
            "-".to_string()
        } else {
            let previous = curve.rows[index - 1].elapsed.as_secs_f64();
            if previous > 0.0 {
                format!("{:.2}", (row.elapsed.as_secs_f64() / previous).log2())
            } else {
                "-".to_string()
            }
        };
        println!(
            "| {:>5} | {:>10} | {:>10.4} | {:>10.1} | {:>12} | {:>13.1} | {:>8} |",
            row.log_size,
            row.size,
            row.elapsed.as_secs_f64(),
            nanos / row.size as f64,
            row.bytes,
            row.bytes as f64 / row.size as f64,
            exponent
        );
    }
    println!("stopped: {}", curve.stop.summary());
}

// === the stages ===

/// Measure every stage over F, and report the curves and the field's two-adic ceiling.
fn measure_field<F: KnownOrder>(name: &str, budget: Duration, seed: u64) -> Vec<Curve> {
    let element_bytes = std::mem::size_of::<F>();
    let (two_adicity, odd_part) = two_adic_decomposition(F::order_limbs());
    let odd_bits = highest_set_bit(&odd_part).map(|bit| bit + 1).unwrap_or(0);
    let order_bits = highest_set_bit(F::order_limbs())
        .map(|bit| bit + 1)
        .unwrap_or(0);

    println!("\n\n## {}", name);
    println!();
    println!(
        "- q is {} bits, in {} limbs",
        order_bits,
        F::order_limbs().len()
    );
    println!("- an element is {} bytes", element_bytes);
    println!(
        "- two-adicity s = {}, so the largest power-of-two NTT is 2^{} and the odd part of q - 1 \
         is {} bits",
        two_adicity, two_adicity, odd_bits
    );

    // The root of unity itself, timed: it is one exponentiation by the odd part of q - 1, twice
    // over on average, and is paid once per transform size rather than per transform.
    let mut rng = StdRng::seed_from_u64(seed);
    let log_root = two_adicity.min(20);
    let (_root, elapsed, bytes) = measure(|| F::two_adic_root_of_unity(log_root, &mut rng));
    println!(
        "- a primitive 2^{}-th root of unity took {:.6} s and {} peak bytes",
        log_root,
        elapsed.as_secs_f64(),
        bytes
    );

    let mut curves = Vec::new();
    curves.push(sweep(
        "mul: schoolbook product at degree n-1",
        budget,
        |log_n| {
            let n = 1usize << log_n;
            let mut rng = StdRng::seed_from_u64(seed ^ 0x3171);
            let a = UnivariatePolynomial::<F>::rand(n as u64 - 1, &mut rng);
            let b = UnivariatePolynomial::<F>::rand(n as u64 - 1, &mut rng);
            let (product, elapsed, bytes) = measure(|| &a * &b);
            assert_eq!(product.degree() as usize, 2 * n - 2, "product degree");
            Ok((elapsed, bytes))
        },
    ));

    curves.push(sweep(
        "div: degree 2n-2 by degree n-1, as pow_mod reduces",
        budget,
        |log_n| {
            let n = 1usize << log_n;
            let mut rng = StdRng::seed_from_u64(seed ^ 0x5172);
            let dividend = UnivariatePolynomial::<F>::rand(2 * n as u64 - 2, &mut rng);
            let divisor = UnivariatePolynomial::<F>::rand(n as u64 - 1, &mut rng);
            let ((quotient, remainder), elapsed, bytes) = measure(|| dividend.div(&divisor));
            // The division identity, checked rather than assumed — it costs another multiply, so
            // it is outside the measurement.
            assert_eq!(&(&quotient * &divisor) + &remainder, dividend);
            Ok((elapsed, bytes))
        },
    ));

    curves.push(sweep(
        "ntt: evaluate over a size-n domain",
        budget,
        |log_n| {
            if log_n > two_adicity {
                return Err(format!(
                    "no primitive 2^{}-th root of unity: the two-adicity of this field is {}",
                    log_n, two_adicity
                ));
            }
            let n = 1usize << log_n;
            let mut rng = StdRng::seed_from_u64(seed ^ 0x7173);
            let w = F::two_adic_root_of_unity(log_n, &mut rng);
            let domain = FFTDomain::from_generator(w, n);
            let p = UnivariatePolynomial::<F>::rand(n as u64 - 1, &mut rng);
            let (values, elapsed, bytes) = measure(|| evaluate(&p, &domain));
            assert_eq!(values.len(), n);
            Ok((elapsed, bytes))
        },
    ));

    curves.push(sweep(
        "intt: interpolate over a size-n domain",
        budget,
        |log_n| {
            if log_n > two_adicity {
                return Err(format!(
                    "no primitive 2^{}-th root of unity: the two-adicity of this field is {}",
                    log_n, two_adicity
                ));
            }
            let n = 1usize << log_n;
            let mut rng = StdRng::seed_from_u64(seed ^ 0x9174);
            let w = F::two_adic_root_of_unity(log_n, &mut rng);
            let domain = FFTDomain::from_generator(w, n);
            let p = UnivariatePolynomial::<F>::rand(n as u64 - 1, &mut rng);
            let values = evaluate(&p, &domain);
            let (recovered, elapsed, bytes) = measure(|| interpolate(&values, &domain));
            // The round trip, which is the only check that the transform was the right one.
            assert_eq!(
                recovered, p,
                "interpolate did not invert evaluate at n = {n}"
            );
            Ok((elapsed, bytes))
        },
    ));

    curves.push(sweep(
        "lagrange: interpolate n points at arbitrary abscissae",
        budget,
        |log_n| {
            let n = 1usize << log_n;
            let mut rng = StdRng::seed_from_u64(seed ^ 0xa176);
            // `x_i = i` rather than random draws, so the abscissae are distinct by construction.
            let points: Vec<(F, F)> = (0..n)
                .map(|i| (<F as FiniteField>::new(i as u64), F::random(&mut rng)))
                .collect();

            let (p, elapsed, bytes) = measure(|| lagrange_interpolate(points.clone()));
            // Four of the n constraints, spot-checked: all n would cost another quadratic pass.
            for index in [0, n / 3, n / 2, n - 1] {
                let (x, y) = points[index];
                assert_eq!(p.eval(&x), y, "the interpolant misses point {index}");
            }
            Ok((elapsed, bytes))
        },
    ));

    curves.push(sweep(
        "roots: degree d, four planted roots and a random cofactor",
        budget,
        |log_d| {
            let d = 1usize << log_d;
            let mut rng = StdRng::seed_from_u64(seed ^ 0xb175);
            let planted: Vec<F> = (0..PLANTED).map(|_| F::random(&mut rng)).collect();
            let cofactor = UnivariatePolynomial::<F>::rand((d - PLANTED) as u64, &mut rng);
            let f = &UnivariatePolynomial::from_zeros(&planted) * &cofactor;
            assert_eq!(f.degree() as usize, d);

            let (found, elapsed, bytes) = measure(|| roots(&f, &mut rng));
            // Every planted root must be reported. Extra roots are legitimate: the cofactor has
            // its own, and over a 31-bit field it has them with real probability.
            for a in &planted {
                assert!(found.contains(a), "planted root {a} was not recovered");
            }
            Ok((elapsed, bytes))
        },
    ));

    for curve in &curves {
        print_curve(curve);
    }

    println!(
        "\n### {} — reachable size per stage, in bytes at the peak",
        name
    );
    println!(
        "| {:<52} | {:>10} | {:>13} | why it stopped",
        "stage", "reached", "peak bytes"
    );
    println!("{}", rule(&[54, 12, 15, 16]));
    for curve in &curves {
        let peak = curve.rows.last().map(|row| row.bytes).unwrap_or(0);
        println!(
            "| {:<52} | {:>10} | {:>13} | {}",
            curve.name,
            curve.reached(),
            peak,
            curve.stop.summary()
        );
    }
    let first_to_fail = curves
        .iter()
        .min_by_key(|curve| curve.reached())
        .expect("six stages");
    println!(
        "\nfirst stage to stop: **{}**, at size {} — {}",
        first_to_fail.name,
        first_to_fail.reached(),
        first_to_fail.stop.summary()
    );

    curves
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();

    let mut selector = "all".to_string();
    let mut budget = Duration::from_secs_f64(2.0);
    for argument in &arguments {
        if let Some(seconds) = argument.strip_prefix("budget=") {
            budget =
                Duration::from_secs_f64(seconds.parse().expect("budget=SECONDS takes a number"));
        } else {
            selector = argument.clone();
        }
    }

    if selector == "list" {
        println!("fields: all, mersenne31, koalabear, goldilocks, bn254");
        println!("options: budget=SECONDS (default 2.0), the wall clock allowed per measurement");
        return;
    }

    println!("# Univariate cost and memory against degree");
    println!();
    println!(
        "Every stage doubles its size parameter until one measurement exceeds {:.2} s. Memory is \
         peak live heap bytes from a counting allocator, attributed to the measured call alone.",
        budget.as_secs_f64()
    );
    println!();
    println!(
        "The **exponent** column is `log2(t_i / t_(i-1))` at a doubling size: 1 is linear, 2 \
         quadratic, 3 cubic."
    );

    let run_all = selector == "all";
    if run_all || selector == "mersenne31" {
        measure_field::<Mersenne31In64>("Mersenne-31, 2^31 - 1", budget, 0x4d31);
    }
    if run_all || selector == "koalabear" {
        measure_field::<KoalaBearIn64>("KoalaBear, 2^31 - 2^24 + 1", budget, 0x4b0a);
    }
    if run_all || selector == "goldilocks" {
        measure_field::<Goldilocks>("Goldilocks, 2^64 - 2^32 + 1", budget, 0x601d);
    }
    if run_all || selector == "bn254" {
        measure_field::<Bn254Fr>("BN254 Fr, 254 bits", budget, 0xb254);
    }

    // A reading of this is a ceiling on recent usage, not a per-stage figure; the tables above
    // are what to quote. Printed so that the two can be compared.
    if let Some(peak) = zeebra::util::peak_resident_bytes() {
        println!("\n\nprocess peak resident bytes: {}", peak);
    }
}
