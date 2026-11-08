//! Folding scaled words into one accumulator — the MDS layer's shape — is bounded by its output.
//!
//! One test per binary, for the reason `multivariate_mul_memory.rs` gives: the bound is asserted
//! against a process-wide tracking `#[global_allocator]`, and *everything* the process allocates
//! raises it — including another test's operand construction, which no lock around the measured
//! region can cover. This test and `multivariate_add_memory.rs`'s shared one binary until #499,
//! and the 11 476-term operands built there were charged to the fold's peak here, failing the
//! bound below by 4.4x on a measurement that was correct.
//!
//! The second half of #361's regression; the cancelling case is in `multivariate_add_memory.rs`.

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

/// `a + b` as it was built before #361: one `Vec` of every term, collected by `new`.
fn add_materialize(a: &Poly, b: &Poly) -> Poly {
    let terms: Vec<(Monomial<2>, F)> = a
        .terms()
        .iter()
        .chain(b.terms().iter())
        .map(|(monomial, c)| (*monomial, *c))
        .collect();
    MultivariatePolynomial::new(&terms)
}

/// `p.scale(c)` as it was built before #361: a `Vec` of the scaled terms, rehashed by `new`.
fn scale_materialize(p: &Poly, factor: &F) -> Poly {
    let terms: Vec<(Monomial<2>, F)> = p
        .terms()
        .iter()
        .map(|(monomial, c)| (*monomial, *c * factor))
        .collect();
    MultivariatePolynomial::new(&terms)
}

/// Terms per state word, matching the degree the cancelling case in `multivariate_add_memory.rs`
/// sums at.
const DEGREE: u32 = 150;

/// Folding many scaled words into one accumulator — the MDS layer's shape — allocates far less
/// than rebuilding the accumulator at every step.
#[test]
fn the_mds_fold_allocates_far_less_than_rebuilding_each_step() {
    const WORDS: usize = 8;
    // Disjoint supports, so the accumulator grows monotonically and nothing cancels: the opposite
    // extreme from the cancelling case, and the shape the symbolic build actually runs. Here the
    // in-place form cannot peak at nothing — the output has to be allocated — so what is asserted
    // is the gap against the pre-#361 `Add` and `scale`, measured in the same binary.
    let state: Vec<Poly> = (0..WORDS)
        .map(|w| {
            let mut terms: Vec<(Monomial<2>, F)> = Vec::new();
            for i in 0..=DEGREE {
                terms.push((
                    Monomial::<2>::new(&[i, w as u32 * (DEGREE + 1)]),
                    F::new(1 + i as u64),
                ));
            }
            MultivariatePolynomial::new(&terms)
        })
        .collect();
    let row: Vec<F> = (0..WORDS).map(|w| F::new(3 + w as u64)).collect();

    let (reference, materialising_peak) = measure(|| {
        row.iter().zip(&state).fold(Poly::zero(), |acc, (m, word)| {
            add_materialize(&acc, &scale_materialize(word, m))
        })
    });

    let (folded, in_place_peak) = measure(|| {
        row.iter()
            .zip(&state)
            .fold(Poly::zero(), |acc, (m, word)| acc + word.scale(m))
    });

    assert_eq!(folded, reference, "the in-place fold is not the fold");
    assert_eq!(
        folded.terms().len(),
        WORDS * (DEGREE as usize + 1),
        "the supports are not disjoint, so this test is not measuring what it claims"
    );

    // Measured in this test: 8 words of 151 terms folded to 1 208 terms peaks at **43 312 bytes**
    // in place against **84 448 bytes** rebuilt at every step — the 2x #361 predicted for this
    // shape, which unlike the cancelling case is all there is to win here, since the output does
    // have to be allocated.
    //
    // So the bound is stated against the output rather than against the other arm: four times the
    // output's terms, which leaves room for the growth chain holding the old table and the new one
    // at once during a rehash (that residual is the 2.2x actually measured). The second assertion
    // is what makes the first one mean something — the rebuilding form does not fit underneath it.
    let output_bytes = folded.terms().len() * std::mem::size_of::<(Monomial<2>, F)>();
    let bound = 4 * output_bytes;
    assert!(
        in_place_peak <= bound,
        "the fold peaked at {in_place_peak} bytes, above the {bound} byte bound for a {} term \
         output",
        folded.terms().len()
    );
    assert!(
        materialising_peak > bound,
        "the rebuilding form peaked at {materialising_peak} bytes, inside the {bound} byte bound, \
         so the bound does not distinguish the two and this test asserts nothing"
    );
}
