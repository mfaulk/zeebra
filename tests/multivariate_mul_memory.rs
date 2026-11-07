//! The multivariate multiply's live heap is bounded by its output, not by its product count.
//!
//! Its own integration test binary because the bound is asserted against a process-wide tracking
//! `#[global_allocator]`: a second test running concurrently in the same process would be
//! attributed here. One test per binary makes the counters unambiguous without depending on the
//! runner's thread policy.
//!
//! The regression this pins is `resultant-elimination.md` §6.8 — a six-round symbolic build whose
//! peak RSS was 57.0 GB to produce 4.3 MB of polynomial, because every pairwise term-product was
//! materialised in one `Vec` before like terms were collected.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

use zeebra::{fields::KoalaBear, FiniteField, Monomial, MultivariatePolynomial};

type F = KoalaBear;

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

/// Run `work`, returning its value and the peak live heap bytes it added.
fn measure<T>(work: impl FnOnce() -> T) -> (T, usize) {
    let baseline = LIVE.load(Ordering::Relaxed);
    PEAK.store(baseline, Ordering::Relaxed);
    let value = work();
    let peak = PEAK.load(Ordering::Relaxed).saturating_sub(baseline);
    (value, peak)
}

/// The dense bivariate triangle of total degree `degree`, every coefficient nonzero.
///
/// The shape `cico_bivariate` actually builds: no cancellation anywhere, so the product's term
/// count is exactly the triangle of the summed degree and the gap between the product count and
/// the output size is the whole of the effect being measured.
fn dense_triangle(degree: u32) -> MultivariatePolynomial<2, F> {
    let mut terms: Vec<(Monomial<2>, F)> = Vec::new();
    for i in 0..=degree {
        for j in 0..=(degree - i) {
            // 1-based so that no coefficient is zero and no term is dropped on construction.
            terms.push((
                Monomial::<2>::new(&[i, j]),
                F::new(1 + (i as u64 * 31 + j as u64) % 1000),
            ));
        }
    }
    MultivariatePolynomial::new(&terms)
}

/// The number of terms in the dense bivariate triangle of total degree `d`.
fn triangle(d: u64) -> u64 {
    (d + 1) * (d + 2) / 2
}

/// Squaring a dense bivariate triangle allocates on the order of its output, not its product count.
#[test]
fn multiply_live_heap_is_bounded_by_the_output() {
    const DEGREE: u32 = 90;

    let a = dense_triangle(DEGREE);
    assert_eq!(a.terms().len() as u64, triangle(DEGREE as u64));

    let (product, peak) = measure(|| &a * &a);

    // No cancellation: the square of a dense triangle is the dense triangle of twice the degree.
    assert_eq!(
        product.terms().len() as u64,
        triangle(2 * DEGREE as u64),
        "the product is not the dense triangle, so this test is not measuring what it claims"
    );

    let products = (a.terms().len() as u64) * (a.terms().len() as u64);
    let output_terms = product.terms().len() as u64;
    assert!(
        products > 1000 * output_terms,
        "{products} products against {output_terms} output terms is not a wide enough gap to \
         distinguish an output-sized live set from a product-sized one"
    );

    // Materialising all 17.5 million products held **384 MiB** here: a term is 12 bytes padded to
    // 16, and the reallocation chain has both buffers live at the final doubling. Collecting as the
    // products are formed holds **480 KiB** for the same 16 471-term output.
    //
    // The bound sits at 4 MiB — 8x above what the collecting routes measure, so a hash map that
    // grows differently under a new toolchain does not fail it, and 94x below the materialising
    // figure, so a partial regression does. It is a bound on the live set, not an allocation count.
    const BOUND: usize = 4 * 1024 * 1024;
    assert!(
        peak <= BOUND,
        "peak live heap {} MiB exceeds the {} MiB bound for a product of {} terms from {} \
         term-products",
        peak / (1024 * 1024),
        BOUND / (1024 * 1024),
        output_terms,
        products
    );
}
