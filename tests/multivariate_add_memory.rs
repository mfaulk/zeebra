//! Addition accumulates into an operand's own map rather than building a third.
//!
//! One test per binary, for the reason `multivariate_mul_memory.rs` gives: the bound is asserted
//! against a process-wide tracking `#[global_allocator]`, and *everything* the process allocates
//! raises it — including another test's operand construction, which no lock around the measured
//! region can cover. A single test is the only arrangement under which the counters mean what they
//! say; see #499 for the two tests that shared this binary and attributed each other's setup.
//!
//! The regression this pins is #361. #243 bounded the multiply's transient by its output and left
//! `Add` materialising a `Vec` of `|a| + |b|` terms and rebuilding a fresh map through
//! `MultivariatePolynomial::new` — so the six-round `cico_bivariate` build's MDS layer, which folds
//! sixteen 266 815-term state words through `acc + word.scale(m)` once per round, allocated each
//! sum two to three times over. Unlike the multiply the cost is a constant factor on the output
//! rather than a quadratic blow-up, so what is asserted is the gap against the materialising form,
//! measured here in the same binary rather than quoted. The fold's half of that gap is
//! `multivariate_mds_fold_memory.rs`.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

use zeebra::{fields::KoalaBear, FiniteField, Monomial, MultivariatePolynomial};

type F = KoalaBear;
type Poly = MultivariatePolynomial<2, F>;

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

    // Delegated rather than left to the default, which would be an alloc-copy-dealloc. A `Vec`'s
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
///
/// Correct only because this binary holds one test: `PEAK` is reset to the current `LIVE` here, so
/// a concurrent measurement would erase this one's high-water mark, and a concurrent *allocation*
/// of any kind would be charged to it.
fn measure<T>(work: impl FnOnce() -> T) -> (T, usize) {
    let baseline = LIVE.load(Ordering::Relaxed);
    PEAK.store(baseline, Ordering::Relaxed);
    let value = work();
    let peak = PEAK.load(Ordering::Relaxed).saturating_sub(baseline);
    (value, peak)
}

/// The dense bivariate triangle of total degree `degree`, coefficient `1 + offset` at every term.
fn dense_triangle(degree: u32, offset: u64) -> Poly {
    let mut terms: Vec<(Monomial<2>, F)> = Vec::new();
    for i in 0..=degree {
        for j in 0..=(degree - i) {
            // 1-based so that no coefficient is zero and no term is dropped on construction.
            terms.push((
                Monomial::<2>::new(&[i, j]),
                F::new(1 + offset + (i as u64 * 31 + j as u64) % 1000),
            ));
        }
    }
    MultivariatePolynomial::new(&terms)
}

/// The number of terms in the dense bivariate triangle of total degree `d`.
fn triangle(d: u64) -> u64 {
    (d + 1) * (d + 2) / 2
}

/// `a + b` as it was built before #361: one `Vec` of every term, collected by `new`.
///
/// The independent reference and the measurement's baseline arm, in the shape
/// `MultiplyRoute::Materialize` plays for the product.
fn add_materialize(a: &Poly, b: &Poly) -> Poly {
    let terms: Vec<(Monomial<2>, F)> = a
        .terms()
        .iter()
        .chain(b.terms().iter())
        .map(|(monomial, c)| (*monomial, *c))
        .collect();
    MultivariatePolynomial::new(&terms)
}

/// Degree of the triangles summed. 150 is 11 476 terms a side, enough that the `Vec` of
/// `|a| + |b|` terms is hundreds of kilobytes and well clear of the allocator's own noise.
const DEGREE: u32 = 150;

/// A sum whose operands are large and whose result cancels almost entirely holds no `Vec` of
/// `|a| + |b|` terms, and allocates far less than the materialising form it replaces.
#[test]
fn add_live_heap_is_far_below_the_materialising_form() {
    // b = -a except on the single term `1`, so the sum is one term out of 11 476 a side. This is
    // the shape that separates accumulating from materialising: the materialising form's transient
    // is set by `|a| + |b|` whatever the output is, so a near-total cancellation makes the gap
    // between transient and output the whole of the measurement.
    let a = dense_triangle(DEGREE, 0);
    let b = {
        let mut negated = -a.clone();
        negated += Poly::from(F::new(7));
        negated
    };
    assert_eq!(a.terms().len() as u64, triangle(DEGREE as u64));
    assert_eq!(b.terms().len() as u64, triangle(DEGREE as u64));

    let (reference, materialising_peak) = measure(|| add_materialize(&a, &b));
    assert_eq!(
        reference.terms().len(),
        1,
        "the operands do not cancel, so this test is not measuring what it claims"
    );

    // Each arm starts from freshly built operands, so neither is charged for the other's input.
    let (in_place, in_place_peak) = {
        let left = dense_triangle(DEGREE, 0);
        let right = b.clone();
        measure(move || left + right)
    };
    assert_eq!(in_place, reference, "the in-place sum is not the sum");

    // Measured in this test: materialising peaks at **594 944 bytes** — a `Vec` of 22 952 terms,
    // 12 bytes padded to 16, with both buffers live at the final doubling, plus the rebuilt map —
    // against **0 bytes** for merging into the left operand's map, because every one of the 11 476
    // merges lands on a monomial already present and removes it, so the table never grows. That is
    // the bound #243's §6.8 was about, now holding for `Add`: the live set is the output.
    //
    // The bound is a sixteenth of the materialising figure rather than zero, so that a hash map
    // which grows differently under a new toolchain does not fail it — but no form that holds a
    // `Vec` of `|a| + |b|` terms can fit underneath it.
    assert!(
        in_place_peak * 16 <= materialising_peak,
        "in-place addition peaked at {in_place_peak} bytes against the materialising form's \
         {materialising_peak}: the transient is no longer bounded by the output"
    );
}
