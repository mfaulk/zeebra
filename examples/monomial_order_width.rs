//! Replay recommended F4 column sorts with one-byte and two-word order dispatch.
//! The production comparator is a control for code generation in the wide ablation arm.

use std::cmp::Ordering;
use std::hint::black_box;
use std::mem::size_of;
use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4::{symbolic_preprocessing_with, MonomialHandle, ReducerCache},
        trace_batches, F4Options,
    },
    Monomial, MonomialOrder, WeightedOrder, WeightedTieBreak,
};

type F = Zp2147483647;
type Column<const N: usize> = (Monomial<N>, MonomialHandle);

// Take the minimum of nine rotated repetitions to reduce the effect of interruptions.
const REPETITIONS: usize = 9;

// Batch the comparisons so one clock reading covers millions of dispatches.
const DISPATCH_COMPARISONS: usize = 20_000_000;

// Batch the short sorts to reduce the relative cost of clock reads.
const SORT_PASSES: usize = 20;

// Both ablations share the built-in leaves from monomial_order.rs.
#[inline]
fn lex<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
    a.exponents().cmp(b.exponents())
}

#[inline]
fn grlex<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
    match a.degree().cmp(&b.degree()) {
        Ordering::Equal => lex(a, b),
        ord => ord,
    }
}

#[inline]
fn grevlex<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
    match a.degree().cmp(&b.degree()) {
        Ordering::Equal => {
            for i in (0..N).rev() {
                match a.exponents()[i].cmp(&b.exponents()[i]).reverse() {
                    Ordering::Equal => continue,
                    ord => return ord,
                }
            }
            Ordering::Equal
        }
        ord => ord,
    }
}

/// `MonomialOrder` as it was before #306: three variants, one byte, three arms.
#[derive(Copy, Clone)]
enum NarrowOrder {
    Lexicographic,
    GradedLexicographic,
    GradedReverseLexicographic,
}

impl NarrowOrder {
    #[inline]
    fn cmp<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
        match self {
            NarrowOrder::Lexicographic => lex(a, b),
            NarrowOrder::GradedLexicographic => grlex(a, b),
            NarrowOrder::GradedReverseLexicographic => grevlex(a, b),
        }
    }
}

/// `MonomialOrder` as it is after #306: four variants, two words, four arms.
#[derive(Copy, Clone)]
enum WideOrder {
    Lexicographic,
    GradedLexicographic,
    GradedReverseLexicographic,
    Weighted(&'static WeightedOrder),
}

impl WideOrder {
    #[inline]
    fn cmp<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
        match self {
            WideOrder::Lexicographic => lex(a, b),
            WideOrder::GradedLexicographic => grlex(a, b),
            WideOrder::GradedReverseLexicographic => grevlex(a, b),
            WideOrder::Weighted(weighted) => weighted.cmp(a, b),
        }
    }
}

static WEIGHTED: WeightedOrder = WeightedOrder::new(
    &[3, 1, 1, 1, 1, 1, 1],
    WeightedTieBreak::ReverseLexicographic,
);

/// The three built-in orders in each arm's own representation, in one place so the three rows
/// cannot drift apart.
fn triple(order: MonomialOrder) -> (NarrowOrder, WideOrder) {
    match order {
        MonomialOrder::Lexicographic => (NarrowOrder::Lexicographic, WideOrder::Lexicographic),
        MonomialOrder::GradedLexicographic => (
            NarrowOrder::GradedLexicographic,
            WideOrder::GradedLexicographic,
        ),
        MonomialOrder::GradedReverseLexicographic => (
            NarrowOrder::GradedReverseLexicographic,
            WideOrder::GradedReverseLexicographic,
        ),
        MonomialOrder::Weighted(_) | MonomialOrder::Block(_) => {
            panic!("this harness measures the three built-in orders")
        }
    }
}

/// Fold an `Ordering` into an accumulator, so no comparison can be dropped as dead.
#[inline(always)]
fn fold(acc: u64, ord: Ordering) -> u64 {
    acc.wrapping_mul(3).wrapping_add(ord as i8 as u64)
}

// Stride through the sorted snapshot to mix degrees and comparison outcomes.
const STRIDE: usize = 7919;

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

// Reload the order each time so the compiler cannot hoist the dispatch out of the loop.
macro_rules! dispatch_lap {
    ($order:expr, $data:expr, $count:expr) => {{
        let order = $order;
        let data: &[Monomial<_>] = $data;
        let mut acc = 0u64;
        let mut i = 0usize;
        for _ in 0..$count {
            let j = (i * STRIDE + 13) % data.len();
            acc = fold(acc, black_box(&order).cmp(&data[i], &data[j]));
            i += 1;
            if i == data.len() {
                i = 0;
            }
        }
        acc
    }};
}

/// Sort every prepared copy and time the whole lap with one clock reading.
macro_rules! sort_lap {
    ($order:expr, $copies:expr) => {{
        let order = $order;
        let started = Instant::now();
        for columns in &mut $copies {
            columns.sort_unstable_by(|a, b| order.cmp(&b.0, &a.0));
        }
        started.elapsed()
    }};
}

/// Minimum elapsed time per arm for one instance.
struct Row {
    system: &'static str,
    order: MonomialOrder,
    batches: usize,
    columns: usize,
    /// Distinct monomials across every snapshot: the `dispatch` lap's working set.
    distinct: usize,
    /// `production`, `wide`, `narrow`, in that order.
    dispatch: [Duration; 3],
    sort: [Duration; 3],
}

impl Row {
    fn print_dispatch(&self) {
        let (p, w, n) = (
            millis(self.dispatch[0]),
            millis(self.dispatch[1]),
            millis(self.dispatch[2]),
        );
        println!(
            "{:<12} {:<8} {:>8} {:>10.3} {:>10.3} {:>10.3} {:>9.3}x {:>9.3}x",
            self.system,
            self.order.name(),
            self.distinct,
            p,
            w,
            n,
            w / p,
            w / n
        );
    }

    fn print_sort(&self) {
        let (p, w, n) = (
            millis(self.sort[0]),
            millis(self.sort[1]),
            millis(self.sort[2]),
        );
        println!(
            "{:<12} {:<8} {:>8} {:>8} {:>10.3} {:>10.3} {:>10.3} {:>9.3}x {:>9.3}x",
            self.system,
            self.order.name(),
            self.batches,
            self.columns,
            p,
            w,
            n,
            w / p,
            w / n
        );
    }
}

fn measure<const N: usize>(
    system: &'static str,
    order: MonomialOrder,
    polynomials: Vec<zeebra::MultivariatePolynomial<N, F>>,
) -> Row {
    // Keep the order opaque at each arm's entry, as with a caller-supplied order.
    let (narrow, wide) = triple(black_box(order));
    let narrow = black_box(narrow);
    let wide = black_box(wide);
    let options = F4Options::recommended();
    let (_, _, trace) = trace_batches(&polynomials, order, &options)
        .unwrap_or_else(|err| panic!("{system} {}: trace failed: {err:?}", order.name()));

    // Replay the same monomial/handle pairs that MacaulayMatrix::build_measured sorts.
    let mut cache = ReducerCache::new(options.reducer_cache);
    let snapshots: Vec<Vec<Column<N>>> = trace
        .batches()
        .iter()
        .map(|batch| {
            symbolic_preprocessing_with(
                &batch.basis,
                &batch.pairs,
                options.max_matrix_rows,
                options.reducer_selection,
                &mut cache,
            )
            .expect("recommended trace batch fits the row budget")
            .monomials
            .into_iter()
            .zip(0 as MonomialHandle..)
            .collect()
        })
        .collect();
    let columns: usize = snapshots.iter().map(Vec::len).sum();
    assert!(columns > 0, "{system} {}: no columns", order.name());

    let mut flat: Vec<Monomial<N>> = snapshots.iter().flatten().map(|pair| pair.0).collect();
    flat.sort_unstable_by(|a, b| order.cmp(b, a));
    flat.dedup();

    let mut dispatch = [Duration::MAX; 3];
    let mut sort = [Duration::MAX; 3];
    let mut dispatch_checksum: Option<u64> = None;
    let mut sort_reference: Option<Vec<Vec<Column<N>>>> = None;

    for repetition in 0..REPETITIONS {
        // Arm order rotated per repetition, so no arm always runs first or last.
        for slot in 0..3 {
            let which = (slot + repetition) % 3;
            let started = Instant::now();
            let checksum = match which {
                0 => dispatch_lap!(black_box(order), &flat, DISPATCH_COMPARISONS),
                1 => dispatch_lap!(wide, &flat, DISPATCH_COMPARISONS),
                _ => dispatch_lap!(narrow, &flat, DISPATCH_COMPARISONS),
            };
            let elapsed = started.elapsed();
            dispatch[which] = dispatch[which].min(elapsed);
            // All three arms must fold to the same value, or one of them is not performing the
            // comparisons the other two are.
            match dispatch_checksum {
                None => dispatch_checksum = Some(checksum),
                Some(expected) => assert_eq!(
                    expected,
                    checksum,
                    "{system} {}: arm {which} disagrees on the dispatch checksum",
                    order.name()
                ),
            }
        }

        for slot in 0..3 {
            let which = (slot + repetition) % 3;
            let mut copies: Vec<_> = (0..SORT_PASSES)
                .flat_map(|_| snapshots.iter().cloned())
                .collect();
            let elapsed = match which {
                0 => sort_lap!(black_box(order), copies),
                1 => sort_lap!(wide, copies),
                _ => sort_lap!(narrow, copies),
            };
            sort[which] = sort[which].min(elapsed);
            let sorted = black_box(copies);
            match &sort_reference {
                None => sort_reference = Some(sorted),
                Some(expected) => assert_eq!(
                    expected,
                    &sorted,
                    "{system} {}: arm {which} sorts the columns differently",
                    order.name()
                ),
            }
        }
    }

    println!(
        "  {system} {} checksum {:#018x}",
        order.name(),
        dispatch_checksum.expect("one repetition ran")
    );

    Row {
        system,
        order,
        batches: snapshots.len(),
        columns,
        distinct: flat.len(),
        dispatch,
        sort,
    }
}

// A fixed LCG keeps the checksum independent of rand's generator.
fn corpus<const N: usize>(count: usize, seed: u64, max_exponent: u32) -> Vec<Monomial<N>> {
    let mut state = seed;
    let mut next = || {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (state >> 33) as u32
    };
    (0..count)
        .map(|_| {
            let exponents: Vec<u32> = (0..N).map(|_| next() % (max_exponent + 1)).collect();
            Monomial::new(&exponents)
        })
        .collect()
}

fn validate_arms() {
    assert_eq!(size_of::<NarrowOrder>(), 1);
    assert_eq!(size_of::<WideOrder>(), size_of::<MonomialOrder>());
    assert_eq!(size_of::<MonomialOrder>(), 2 * size_of::<usize>());

    let monomials = corpus::<7>(512, 626, 6);
    for (order, expected) in [
        (MonomialOrder::Lexicographic, 0xd82a_7e49_9809_0a36),
        (MonomialOrder::GradedLexicographic, 0x980e_b965_23a8_e1a6),
        (
            MonomialOrder::GradedReverseLexicographic,
            0x59ca_b12a_c05e_2cf8,
        ),
    ] {
        let (narrow, wide) = triple(order);
        for checksum in [
            dispatch_lap!(order, &monomials, monomials.len()),
            dispatch_lap!(wide, &monomials, monomials.len()),
            dispatch_lap!(narrow, &monomials, monomials.len()),
        ] {
            assert_eq!(checksum, expected, "{}", order.name());
        }
    }

    // Exercise the weighted variant so both representations retain a live fourth arm.
    let production = black_box(MonomialOrder::Weighted(&WEIGHTED));
    let wide = black_box(WideOrder::Weighted(&WEIGHTED));
    assert_eq!(
        dispatch_lap!(wide, &monomials, monomials.len()),
        dispatch_lap!(production, &monomials, monomials.len()),
    );
}

fn main() {
    validate_arms();

    println!(
        "MonomialOrder = {} bytes, NarrowOrder = {} byte, WideOrder = {} bytes; \
         pinned dispatch checksums reproduced",
        size_of::<MonomialOrder>(),
        size_of::<NarrowOrder>(),
        size_of::<WideOrder>()
    );
    println!(
        "{REPETITIONS} repetitions, min-reduced, arms rotated; \
         {DISPATCH_COMPARISONS} comparisons per dispatch lap, {SORT_PASSES} sort passes per lap\n"
    );

    let rows = [
        measure("cyclic-5", MonomialOrder::Lexicographic, cyclic::<5, F>()),
        measure("katsura-5", MonomialOrder::Lexicographic, katsura::<5, F>()),
        measure("katsura-6", MonomialOrder::Lexicographic, katsura::<6, F>()),
        measure(
            "katsura-6",
            MonomialOrder::GradedReverseLexicographic,
            katsura::<6, F>(),
        ),
        measure(
            "katsura-7",
            MonomialOrder::GradedLexicographic,
            katsura::<7, F>(),
        ),
    ];

    println!("\ndispatch: {DISPATCH_COMPARISONS} comparisons, the order reloaded per comparison");
    println!(
        "{:<12} {:<8} {:>8} {:>10} {:>10} {:>10} {:>10} {:>10}",
        "system",
        "order",
        "distinct",
        "prod/ms",
        "wide/ms",
        "narrow/ms",
        "wide/prod",
        "wide/narrow"
    );
    for row in &rows {
        row.print_dispatch();
    }

    println!("\nsort: {SORT_PASSES} passes over the trace's column snapshots");
    println!(
        "{:<12} {:<8} {:>8} {:>8} {:>10} {:>10} {:>10} {:>10} {:>10}",
        "system",
        "order",
        "batches",
        "cols",
        "prod/ms",
        "wide/ms",
        "narrow/ms",
        "wide/prod",
        "wide/narrow"
    );
    for row in &rows {
        row.print_sort();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The measured dispatch loops reproduce fixed checksums with the expected enum sizes.
    #[test]
    fn dispatch_arms_reproduce_pinned_checksums() {
        validate_arms();
    }
}
