//! What each multivariate multiplication route costs in time and in live heap, and so what
//! `sparse_multivariate_multiply::route` should select (#243).
//!
//! The multiply before #243 materialised every pairwise term-product in one `Vec` and collected
//! like terms afterwards. `docs/research/resultant-elimination.md` §6.8 measured where that ends
//! up: the six-round `poseidon31-cico-t16-rf2-rp4` symbolic build held **57.0 GB** peak RSS to
//! produce **4.3 MB** of polynomial, because `cico_bivariate` cubes sixteen degree-243 bivariate
//! words as `p * p` then `(p²) * p` and the second step is 3.54 × 10⁹ term-products.
//!
//! So the question is **two columns, not one**: a collecting route trades a `push` for a hash
//! lookup per product, and the memory win has to be read beside what it costs in time. Four arms:
//!
//! 1. **materialize** — the pre-#243 loop, one `Vec` of every product into `SparseMultiPoly::new`
//! 2. **accumulate** — merge each product into a monomial-keyed map as it is formed
//! 3. **chunked** — materialise `rows` terms of the left operand at a time and fold each block in
//! 4. **triangle** — a flat `Vec<F>` indexed by the bivariate total-degree triangle, hashing nothing
//!
//! Arm 1 is **skipped** above [`MATERIALIZE_PRODUCT_CAP`] products rather than run: it is the arm
//! whose cost is already known in closed form, and running it at the six-round size would be the
//! 57 GB measurement again. A skipped cell is marked, never reported as a result.
//!
//! The operands are **dense total-degree triangles**, which is the shape the six-round build
//! actually produces: §6.8 found 266 815 terms at degree 729, exactly `(729+1)(729+2)/2`, with no
//! cancellation anywhere in six rounds. Sparsity is therefore not the lever, and a sparse operand
//! would measure a different problem.
//!
//! Every arm is checked against arm 1's answer — or against arm 2's where arm 1 is skipped —
//! outside the timing. A route measured against a wrong answer is worthless.
//!
//! **Two different memory numbers, and they are not interchangeable.** The per-arm `live heap`
//! column is the tracking allocator's peak of `sum(alloc) - sum(dealloc)` *during that one
//! product*, so it attributes bytes to a route. The single `peak RSS` line at the end is `VmHWM`
//! for the whole process — every arm, every operand, plus the allocator's unreturned arenas — so it
//! is an upper bound on the run and attributes nothing. #237 found the two differing by 55% on an
//! F4 row (21 674 MB tracked against 13 996 MB resident), in that direction, because an allocator
//! that has not returned a freed arena is live to the tracker and resident to nobody. Read the
//! columns for what each is.
//!
//! ```text
//! cargo run --release --example multivariate_mul
//! cargo run --release --example multivariate_mul -- chunk
//! cargo run --release --example multivariate_mul -- max_degree=90
//! ```

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use zeebra::{
    fields::KoalaBear, multiply_multivariate_unstable, multivariate_multiply_route_unstable,
    util::peak_resident_bytes, FiniteField, Monomial, MultiplyRoute, MultivariatePolynomial,
};

/// KoalaBear, the field the six-round row is built over.
type F = KoalaBear;

/// Product count above which the materialising arm is skipped rather than run.
///
/// Quadratic in the operand term count and linear in memory: at 2^28 products the arm already holds
/// about 4 GB, and the six-round `(p²) * p` step is 3.54 × 10⁹ products — 56.6 GB, which is the
/// figure §6.8 took once and which this example exists to avoid taking again.
const MATERIALIZE_PRODUCT_CAP: u64 = 1 << 28;

/// Bivariate operand degrees swept by default. `tri(d) = (d+1)(d+2)/2` terms each.
///
/// The low end is there because it is where a collecting route could plausibly lose: degree 2 is
/// 36 term-products, below the smallest `mul/{arity}` Criterion arm's 256. 243 is the
/// six-round-relevant one: §6.8's words are degree 243 with 29 768 terms, against this dense
/// triangle's 29 890.
const DEGREES: [u32; 8] = [2, 4, 6, 8, 24, 56, 90, 243];

/// Chunk sizes the `chunk` sweep covers, in rows of the left operand per block.
const CHUNK_ROWS: [usize; 8] = [1, 4, 16, 64, 256, 1024, 4096, usize::MAX];

// === the tracking allocator ===

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

// === operands ===

/// The dense bivariate triangle of total degree `degree`, every coefficient nonzero.
fn dense_triangle(degree: u32) -> MultivariatePolynomial<2, F> {
    let mut terms: Vec<(Monomial<2>, F)> = Vec::with_capacity(triangle_len(degree as u64) as usize);
    for x in 0..=degree {
        for y in 0..=(degree - x) {
            terms.push((
                Monomial::<2>::new(&[x, y]),
                F::new(1 + (x as u64 * 31 + y as u64) % 1000),
            ));
        }
    }
    MultivariatePolynomial::new(&terms)
}

/// A dense trivariate simplex of total degree `degree`, the case no specialised route covers.
fn dense_simplex_3(degree: u32) -> MultivariatePolynomial<3, F> {
    let mut terms: Vec<(Monomial<3>, F)> = Vec::new();
    for x in 0..=degree {
        for y in 0..=(degree - x) {
            for z in 0..=(degree - x - y) {
                terms.push((
                    Monomial::<3>::new(&[x, y, z]),
                    F::new(1 + (x as u64 * 31 + y as u64 * 7 + z as u64) % 1000),
                ));
            }
        }
    }
    MultivariatePolynomial::new(&terms)
}

/// A dense simplex of total degree `degree` in `N` variables, every coefficient nonzero.
///
/// Generic where [`dense_simplex_3`] is not, because #362's question is how the dense routes
/// behave *in* `N` and one arity cannot answer it.
fn dense_simplex<const N: usize>(degree: u32) -> MultivariatePolynomial<N, F> {
    let mut exponents = [0u32; N];
    let mut terms: Vec<(Monomial<N>, F)> = Vec::new();
    fill_simplex::<N>(0, degree, &mut exponents, &mut terms);
    MultivariatePolynomial::new(&terms)
}

/// Enumerate the exponent vectors of total degree at most `remaining` over variables `index..N`.
fn fill_simplex<const N: usize>(
    index: usize,
    remaining: u32,
    exponents: &mut [u32; N],
    terms: &mut Vec<(Monomial<N>, F)>,
) {
    if index == N {
        let seed: u64 = exponents
            .iter()
            .enumerate()
            .map(|(i, e)| *e as u64 * (7 * i as u64 + 31))
            .sum();
        terms.push((Monomial::new(exponents), F::new(1 + seed % 1000)));
        return;
    }
    for e in 0..=remaining {
        exponents[index] = e;
        fill_simplex::<N>(index + 1, remaining - e, exponents, terms);
    }
    exponents[index] = 0;
}

/// The number of monomials of total degree at most `degree` in two variables.
fn triangle_len(degree: u64) -> u64 {
    (degree + 1) * (degree + 2) / 2
}

// === reporting ===

/// One measured cell: an arm at a size.
struct Cell {
    arm: &'static str,
    /// `None` when the arm was skipped for exceeding [`MATERIALIZE_PRODUCT_CAP`].
    result: Option<CellResult>,
}

struct CellResult {
    elapsed: Duration,
    /// Peak live heap bytes added by the product.
    heap: usize,
    /// Distinct terms in the product.
    output_terms: u64,
}

fn format_bytes(bytes: u64) -> String {
    const UNITS: [&str; 5] = ["B", "KiB", "MiB", "GiB", "TiB"];
    let mut value = bytes as f64;
    let mut unit = 0;
    while value >= 1024.0 && unit + 1 < UNITS.len() {
        value /= 1024.0;
        unit += 1;
    }
    format!("{value:.1} {}", UNITS[unit])
}

fn format_duration(elapsed: Duration) -> String {
    let seconds = elapsed.as_secs_f64();
    if seconds < 1e-3 {
        format!("{:.1} us", seconds * 1e6)
    } else if seconds < 1.0 {
        format!("{:.2} ms", seconds * 1e3)
    } else {
        format!("{seconds:.3} s")
    }
}

/// Print one step's table: the arms, side by side, against the same operands.
fn report(label: &str, products: u64, cells: &[Cell], route: MultiplyRoute) {
    println!();
    println!("  {label}");
    println!("    {products} term-products, dispatched route {route:?}");
    println!(
        "    {:<12} {:>12} {:>12} {:>12} {:>10} {:>14}",
        "arm", "elapsed", "live heap", "out terms", "B/out term", "vs materialize"
    );

    let baseline = cells
        .iter()
        .find(|c| c.arm == "materialize")
        .and_then(|c| c.result.as_ref());

    for cell in cells {
        match &cell.result {
            None => println!(
                "    {:<12} {:>12} {:>12} {:>12} {:>10} {:>14}",
                cell.arm, "skipped", "-", "-", "-", "-"
            ),
            Some(result) => {
                let per_term = (result.heap as u64)
                    .checked_div(result.output_terms)
                    .unwrap_or(0);
                let ratio = match baseline {
                    Some(base) if cell.arm != "materialize" => format!(
                        "{:.2}x t  {:.3}x m",
                        result.elapsed.as_secs_f64() / base.elapsed.as_secs_f64(),
                        result.heap as f64 / base.heap as f64
                    ),
                    _ => "-".to_string(),
                };
                println!(
                    "    {:<12} {:>12} {:>12} {:>12} {:>10} {:>14}",
                    cell.arm,
                    format_duration(result.elapsed),
                    format_bytes(result.heap as u64),
                    result.output_terms,
                    per_term,
                    ratio
                );
            }
        }
    }
}

// === the sweep ===

/// Measure every arm on one operand pair, checking each against the first arm that ran.
fn measure_arms<const N: usize>(
    label: &str,
    a: &MultivariatePolynomial<N, F>,
    b: &MultivariatePolynomial<N, F>,
) -> MultivariatePolynomial<N, F> {
    let products = (a.terms().len() as u64) * (b.terms().len() as u64);
    let mut arms: Vec<(&'static str, MultiplyRoute)> = vec![
        ("materialize", MultiplyRoute::Materialize),
        ("accumulate", MultiplyRoute::Accumulate),
        ("chunked", MultiplyRoute::Chunked { rows: 64 }),
    ];
    if N == 2 {
        arms.push(("triangle", MultiplyRoute::DenseTriangle));
    }
    // The generalisations of the triangle past N = 2 (#362). Named rather than dispatched, so the
    // sweep measures them where the predicate would refuse them too — the pessimistic direction of
    // a predicate is only visible against the route it declined.
    arms.push(("simplex", MultiplyRoute::DenseSimplex));
    arms.push(("box", MultiplyRoute::DenseBox));

    let mut cells: Vec<Cell> = Vec::new();
    let mut reference: Option<MultivariatePolynomial<N, F>> = None;

    for (arm, route) in arms {
        if route == MultiplyRoute::Materialize && products > MATERIALIZE_PRODUCT_CAP {
            cells.push(Cell { arm, result: None });
            continue;
        }

        let (product, elapsed, heap) = measure(|| multiply_multivariate_unstable(a, b, route));
        cells.push(Cell {
            arm,
            result: Some(CellResult {
                elapsed,
                heap,
                output_terms: product.terms().len() as u64,
            }),
        });

        // Correctness outside the timing. Compared against whichever arm ran first, so a skipped
        // materialising arm does not leave the others unchecked.
        match &reference {
            None => reference = Some(product),
            Some(expected) => assert_eq!(
                &product, expected,
                "{arm} disagrees with the reference answer at {label}"
            ),
        }
    }

    report(
        label,
        products,
        &cells,
        multivariate_multiply_route_unstable(a, b),
    );
    reference.expect("at least one arm ran")
}

/// The `p * p` then `(p²) * p` pair the six-round build costs, at one bivariate degree.
fn sweep_degree(degree: u32) {
    println!();
    println!(
        "=== bivariate degree {degree}, {} terms ===",
        triangle_len(degree as u64)
    );
    let p = dense_triangle(degree);
    let square = measure_arms("p * p", &p, &p);
    let _cube = measure_arms("(p^2) * p", &square, &p);
}

/// Sensitivity of the chunked route to its block size, at one bivariate degree.
fn sweep_chunk(degree: u32) {
    let p = dense_triangle(degree);
    let square = multiply_multivariate_unstable(&p, &p, MultiplyRoute::DenseTriangle);
    for (label, a, b) in [("p * p", &p, &p), ("(p^2) * p", &square, &p)] {
        let products = (a.terms().len() as u64) * (b.terms().len() as u64);
        println!();
        println!("  {label} at degree {degree}: {products} term-products");
        println!(
            "    {:<12} {:>12} {:>12} {:>12}",
            "rows", "elapsed", "live heap", "out terms"
        );
        let mut reference: Option<MultivariatePolynomial<2, F>> = None;
        for rows in CHUNK_ROWS {
            // `usize::MAX` rows is one block, i.e. the materialising transient with the
            // accumulating combine — the degenerate end of the sweep.
            let block = (rows as u128) * (b.terms().len() as u128);
            if block > MATERIALIZE_PRODUCT_CAP as u128 {
                println!(
                    "    {:<12} {:>12} {:>12} {:>12}",
                    "all", "skipped", "-", "-"
                );
                continue;
            }
            let (product, elapsed, heap) =
                measure(|| multiply_multivariate_unstable(a, b, MultiplyRoute::Chunked { rows }));
            println!(
                "    {:<12} {:>12} {:>12} {:>12}",
                rows,
                format_duration(elapsed),
                format_bytes(heap as u64),
                product.terms().len()
            );
            match &reference {
                None => reference = Some(product),
                Some(expected) => assert_eq!(&product, expected, "rows = {rows} disagrees"),
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let chunk_only = args.iter().any(|a| a == "chunk");
    let max_degree: u32 = args
        .iter()
        .find_map(|a| a.strip_prefix("max_degree="))
        .map(|v| v.parse().expect("max_degree must be an integer"))
        .unwrap_or(*DEGREES.last().unwrap());

    println!(
        "sparse multivariate multiplication, {} bytes an element, {} bytes a term",
        std::mem::size_of::<F>(),
        std::mem::size_of::<(Monomial<2>, F)>()
    );
    println!(
        "materialising arm skipped above {MATERIALIZE_PRODUCT_CAP} products ({})",
        format_bytes(MATERIALIZE_PRODUCT_CAP * std::mem::size_of::<(Monomial<2>, F)>() as u64)
    );

    if chunk_only {
        println!();
        println!("=== chunk size sensitivity ===");
        sweep_chunk(max_degree.min(243));
    } else {
        for degree in DEGREES {
            if degree > max_degree {
                continue;
            }
            sweep_degree(degree);
        }

        // The case no specialisation covers: three variables, so the triangle index does not
        // apply and the dispatcher must fall through to a general collecting route. Small sizes
        // included, because the `mul/{arity}` Criterion arms live there and they are the control
        // for a small-operation regression.
        for degree in [2u32, 4, 8, 16, 24] {
            println!();
            let p3 = dense_simplex_3(degree);
            println!(
                "=== trivariate degree {degree}, {} terms — the unspecialised case ===",
                p3.terms().len()
            );
            measure_arms("p * p", &p3, &p3);
        }

        // #362's open question is where the crossover in `N` sits, so the sweep needs more than
        // one arity above the triangle. Sized by term count rather than by degree: the simplex of
        // a fixed degree is a wildly different size at each arity, and comparing arities at
        // different sizes would attribute to `N` what belongs to the size.
        for degree in [3u32, 6, 9] {
            println!();
            let p4 = dense_simplex::<4>(degree);
            println!(
                "=== quadrivariate degree {degree}, {} terms ===",
                p4.terms().len()
            );
            measure_arms("p * p", &p4, &p4);
        }
        for degree in [2u32, 4, 6] {
            println!();
            let p5 = dense_simplex::<5>(degree);
            println!(
                "=== 5-variate degree {degree}, {} terms ===",
                p5.terms().len()
            );
            measure_arms("p * p", &p5, &p5);
        }

        // One term against many at N = 3: the reduction inner step, where the simplex's cell count
        // is tight and the box's is not.
        println!();
        let p3 = dense_simplex_3(20);
        let term3 =
            MultivariatePolynomial::<3, F>::new(&[(Monomial::<3>::new(&[1, 1, 1]), F::new(7))]);
        println!(
            "=== trivariate: one term against {} — the reduction inner step ===",
            p3.terms().len()
        );
        measure_arms("p * term", &p3, &term3);

        // Dense in two variables and linear in the third: the shape whose bounding box is the
        // output and whose total-degree simplex is 28x larger.
        println!();
        let lopsided = {
            let mut terms: Vec<(Monomial<3>, F)> = Vec::new();
            for x in 0..=40u32 {
                for y in 0..=40u32 {
                    for z in 0..=1u32 {
                        terms.push((Monomial::<3>::new(&[x, y, z]), F::new(1 + x as u64)));
                    }
                }
            }
            MultivariatePolynomial::<3, F>::new(&terms)
        };
        println!(
            "=== trivariate, lopsided degrees (40, 40, 1), {} terms ===",
            lopsided.terms().len()
        );
        measure_arms("p * p", &lopsided, &lopsided);

        // One term against many: the inner operation of every Groebner reduction step, and the
        // `mul_by_term/{arity}` Criterion arm.
        println!();
        let p = dense_triangle(56);
        let single =
            MultivariatePolynomial::<2, F>::new(&[(Monomial::<2>::new(&[2, 1]), F::new(7))]);
        println!(
            "=== one term against {} — the reduction inner step ===",
            p.terms().len()
        );
        measure_arms("p * term", &p, &single);
    }

    // The whole process, not one arm: `VmHWM` is monotonic and has no notion of which product was
    // running. It is reported as a sanity bound on the per-arm `live heap` column above, never as a
    // per-route figure.
    match peak_resident_bytes() {
        Some(bytes) => println!(
            "\npeak RSS (VmHWM) for the whole process, all arms and operands: {}",
            format_bytes(bytes)
        ),
        None => println!("\npeak RSS unavailable on this platform"),
    }
}
