//! What #306 cost by widening `MonomialOrder` from one byte to two words (#626).
//!
//! #306 added `MonomialOrder::Weighted(&'static WeightedOrder)`. That took the type from a
//! one-byte three-variant enum to a two-word four-variant one, and added a fourth arm to the
//! `match` in `MonomialOrder::cmp` — the hottest comparison in the crate, threaded by value
//! through 678 sites. The argument that this is free is in the issue; this is the measurement.
//!
//! **Three arms, because a transcription measures itself unless something says it does not.**
//! `benches/monomial_order.rs` records what that costs: two earlier cuts of it reported 3.32x and
//! 3.555x on an order that could not have been affected, both times because the comparand differed
//! from production in something other than the change under test.
//!
//! | arm | the enum dispatched on | size | arms | what it is for |
//! |---|---|---|---|---|
//! | `production` | `MonomialOrder` | 2 words | 4 | the tree as it stands |
//! | `wide` | [`WideOrder`] | 2 words | 4 | fidelity check against `production` |
//! | `narrow` | [`NarrowOrder`] | 1 byte | 3 | **the pre-#306 shape** |
//!
//! `wide` and `narrow` call the *same* transcribed leaf comparisons ([`lex`], [`grlex`],
//! [`grevlex`], copied from `src/poly/multivariate/monomial_order.rs`) and differ in exactly the
//! width of the enum they dispatch on and the number of arms in that `match`. So `narrow` against
//! `wide` is the widening alone. `wide` against `production` is the control: it must come out at
//! ~1.0, and anything else means the transcription is not the production comparison and no ratio
//! here means anything.
//!
//! Two measurements, over the column vectors a `recommended` trace actually produces:
//!
//! - **`dispatch`** reloads the order through `black_box(&order)` on every comparison, so the
//!   discriminant is loaded and branched on per comparison and the compiler cannot unswitch the
//!   `match` out of the loop. This is the maximal-stress model of the widening: if it is free
//!   here it is free everywhere.
//! - **`sort`** is the real call site — `sort_unstable_by(|a, b| cmp(b, a))` over the vectors
//!   `MacaulayMatrix::build_measured` hands the sort, the same snapshots
//!   `examples/column_sort_routes.rs` takes. The order is captured rather than reloaded, so the
//!   compiler may hoist the `match`, which is what production permits too.
//!
//! Every arm folds its `Ordering`s into a checksum and the arms must agree, so an arm the
//! optimiser emptied cannot report a plausible-looking time. The checksum over a deterministic
//! corpus is pinned by `test_the_built_in_orders_agree_with_their_pinned_checksum` in
//! `src/poly/multivariate/monomial_order.rs`, which is what makes the agreement a fact about the
//! production comparator and not three arms being wrong together.
//!
//! Run it pinned and serialized, and gate on the runnable count rather than on the load average —
//! this box carries thousands of threads in I/O wait that cost a pinned single-core measurement
//! nothing:
//!
//! ```text
//! RUSTC_WRAPPER="" CARGO_TARGET_DIR=target-626 cargo build --release --example monomial_order_width
//! tools/benchlock.sh 626 taskset --cpu-list 2 target-626/release/examples/monomial_order_width
//! ```

use std::cmp::Ordering;
use std::hint::black_box;
use std::mem::size_of;
use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4::symbolic_preprocessing,
        trace_batches, F4Options, PairCriteria, ReductionStrategy,
    },
    linalg::Backend,
    Monomial, MonomialOrder,
};

type F = Zp2147483647;

/// Repetitions per arm, min-reduced. The minimum and not the mean, because interference on this
/// box only ever adds time.
const REPETITIONS: usize = 9;

/// Comparisons per timed `dispatch` region, so that a region is tens of milliseconds whatever the
/// instance's column count is and the three arms are compared over the same amount of work.
const DISPATCH_COMPARISONS: usize = 20_000_000;

/// Sorts of the whole snapshot set per timed `sort` region. One pass is 0.01–0.3 ms, which is too
/// short to resolve a per-comparison effect in.
const SORT_PASSES: usize = 20;

// ---------------------------------------------------------------------------------------------
// The leaf comparisons, transcribed from `src/poly/multivariate/monomial_order.rs`.
//
// Both ablation arms call these, so neither can differ from the other in the comparison itself.
// `production` calls the originals; the `wide` row against the `production` row is what says the
// transcription is faithful.
// ---------------------------------------------------------------------------------------------

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
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
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

/// [`WeightedTieBreak`]'s shape, so that [`WideWeighted`] and [`WideOrder`] match the production
/// type's size and the fourth arm's body is comparable work rather than a stub.
///
/// [`WeightedTieBreak`]: zeebra::WeightedTieBreak
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum WideTieBreak {
    Lexicographic,
    ReverseLexicographic,
    LastVariableFirst,
}

/// [`WeightedOrder`]'s shape.
///
/// [`WeightedOrder`]: zeebra::WeightedOrder
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct WideWeighted {
    weights: &'static [u32],
    tie_break: WideTieBreak,
}

impl WideWeighted {
    #[inline]
    fn cmp<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
        match self.weighted_degree(a).cmp(&self.weighted_degree(b)) {
            Ordering::Equal => self.break_tie(a, b),
            ord => ord,
        }
    }

    #[inline]
    fn weighted_degree<const N: usize>(&self, m: &Monomial<N>) -> u64 {
        assert_eq!(self.weights.len(), N, "weighted order arity");
        let mut total: u64 = 0;
        for i in 0..N {
            let term = self.weights[i] as u64 * m.exponents()[i] as u64;
            total = total.checked_add(term).expect("weighted degree overflow");
        }
        total
    }

    #[inline]
    fn break_tie<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Ordering {
        match self.tie_break {
            WideTieBreak::Lexicographic => a.exponents().cmp(b.exponents()),
            WideTieBreak::ReverseLexicographic => {
                for i in (0..N).rev() {
                    match a.exponents()[i].cmp(&b.exponents()[i]).reverse() {
                        Ordering::Equal => continue,
                        ord => return ord,
                    }
                }
                Ordering::Equal
            }
            WideTieBreak::LastVariableFirst => {
                for i in (0..N).rev() {
                    match a.exponents()[i].cmp(&b.exponents()[i]) {
                        Ordering::Equal => continue,
                        ord => return ord,
                    }
                }
                Ordering::Equal
            }
        }
    }
}

/// `MonomialOrder` as it is after #306: four variants, two words, four arms.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum WideOrder {
    Lexicographic,
    GradedLexicographic,
    GradedReverseLexicographic,
    /// Never constructed in the measured loops, exactly as the production variant is never
    /// constructed on the built-in-order paths. It is here for its effect on the type's size and
    /// on the `match` below, which is the whole of what #306 changed.
    Weighted(&'static WideWeighted),
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

/// A weight vector for the one value of [`WideOrder::Weighted`] this harness constructs.
///
/// It has to be constructed somewhere. A variant no code builds is a variant LLVM can prove
/// unreachable, and it would then fold the four-arm `match` back to three and leave the `wide` and
/// `narrow` arms identical by construction — the harness would report the widening free having
/// measured nothing. [`weighted_arms_agree`] builds it, and every arm value the timed loops see
/// passes through `black_box` so that no arm's discriminant is known at compile time.
static WIDE_WEIGHTED: WideWeighted = WideWeighted {
    weights: &[3, 1, 1, 1, 1, 1, 1],
    tie_break: WideTieBreak::ReverseLexicographic,
};

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
        MonomialOrder::Weighted(_) => panic!("this harness measures the three built-in orders"),
    }
}

/// Fold an `Ordering` into an accumulator, so no comparison can be dropped as dead.
#[inline(always)]
fn fold(acc: u64, ord: Ordering) -> u64 {
    acc.wrapping_mul(3).wrapping_add(ord as i8 as u64)
}

/// Stride through the sorted snapshot so the pairs mix degrees and the comparison outcomes are not
/// all `Greater`. Coprime with nothing in particular; it only has to not be 1.
const STRIDE: usize = 7919;

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

/// One `dispatch` lap: `count` comparisons with the order reloaded through `black_box` each time.
///
/// The reload is what makes this the measurement it claims to be. Without it the compiler hoists
/// the `match` out of the loop and all three arms collapse to a direct call to the same leaf, so
/// the harness would report that the widening is free by having measured nothing.
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

/// One `sort` lap: every snapshot cloned and sorted descending, `SORT_PASSES` times over.
macro_rules! sort_lap {
    ($order:expr, $snapshots:expr) => {{
        let order = $order;
        let snapshots: &[Vec<Monomial<_>>] = $snapshots;
        let mut last = Vec::new();
        for _ in 0..SORT_PASSES {
            last.clear();
            for snapshot in snapshots {
                let mut scratch = snapshot.clone();
                scratch.sort_unstable_by(|a, b| order.cmp(b, a));
                last.push(black_box(scratch));
            }
        }
        last
    }};
}

/// Timings and checksums for one instance.
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
            n / w
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
            n / w
        );
    }
}

/// `configuration("recommended")` from `examples/f4_profile.rs`, mirrored as
/// `examples/column_sort_routes.rs` mirrors it, so the batches replayed here are the batches §8.5
/// was taken over. Keep the three in step.
fn recommended() -> F4Options {
    F4Options {
        reduction: ReductionStrategy::Structured,
        criteria: PairCriteria::ALL,
        elimination: Backend::Adaptive,
        measure_stages: true,
        ..F4Options::baseline()
    }
}

fn measure<const N: usize>(
    system: &'static str,
    order: MonomialOrder,
    polynomials: Vec<zeebra::MultivariatePolynomial<N, F>>,
) -> Option<Row> {
    // Opaque, so no arm's discriminant is a compile-time constant. Production threads the order
    // in from a caller and stores it in `F4Options`, so a comparison that knows its order
    // statically is not the comparison the crate performs.
    let (narrow, wide) = triple(black_box(order));
    let narrow = black_box(narrow);
    let wide = black_box(wide);
    let options = recommended();
    let trace = match trace_batches(&polynomials, order, &options) {
        Ok((_, _, trace)) => trace,
        Err(_) => {
            println!("{system:<12} {:<8} did not finish", order.name());
            return None;
        }
    };

    // The column vector each batch hands the sort: `preprocessed.monomials` drained in hash-set
    // order, exactly as `MacaulayMatrix::build_measured` collects it. Snapshotted outside every
    // arm, so all three arms see the same input in the same input order.
    let snapshots: Vec<Vec<Monomial<N>>> = trace
        .batches()
        .iter()
        .map(|batch| {
            let preprocessed = symbolic_preprocessing(&batch.basis, &batch.pairs);
            preprocessed.monomials.iter().copied().collect()
        })
        .collect();
    let columns: usize = snapshots.iter().map(|v| v.len()).sum();
    if columns == 0 {
        println!("{system:<12} {:<8} no columns", order.name());
        return None;
    }

    // `dispatch` runs over one flat, *sorted* vector. Sorted because the hash-set handout order
    // varies per process, and a checksum over a non-deterministic input order could not be
    // compared with anything.
    let mut flat: Vec<Monomial<N>> = snapshots.iter().flatten().copied().collect();
    flat.sort_unstable_by(|a, b| order.cmp(b, a));
    flat.dedup();

    let mut dispatch = [Duration::MAX; 3];
    let mut sort = [Duration::MAX; 3];
    let mut dispatch_checksum: Option<u64> = None;
    let mut sort_reference: Option<Vec<Vec<Monomial<N>>>> = None;

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
                    expected, checksum,
                    "{system} {}: arm {which} disagrees on the dispatch checksum",
                    order.name()
                ),
            }
        }

        for slot in 0..3 {
            let which = (slot + repetition) % 3;
            let started = Instant::now();
            let sorted = match which {
                0 => sort_lap!(black_box(order), &snapshots),
                1 => sort_lap!(wide, &snapshots),
                _ => sort_lap!(narrow, &snapshots),
            };
            let elapsed = started.elapsed();
            sort[which] = sort[which].min(elapsed);
            match &sort_reference {
                None => sort_reference = Some(sorted),
                Some(expected) => assert_eq!(
                    expected, &sorted,
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

    Some(Row {
        system,
        order,
        batches: snapshots.len(),
        columns,
        distinct: flat.len(),
        dispatch,
        sort,
    })
}

/// A deterministic monomial corpus from a 64-bit LCG.
///
/// Not `rand`, so that the checksum below is a function of the comparator alone and not of a
/// dependency's generator. Mirrored by
/// `test_the_built_in_orders_agree_with_their_pinned_checksum` in
/// `src/poly/multivariate/monomial_order.rs`; the two must stay in step, which is the point of
/// stating the number twice.
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

/// The checksum of the three built-in orders over [`corpus`], folded in a fixed sequence.
///
/// Stated here and in `src/poly/multivariate/monomial_order.rs`'s test of the same name, so that
/// an arm the optimiser emptied, or a transcription that drifted, cannot agree with the other two
/// by all being wrong together.
const PINNED_CHECKSUM: u64 = 0x0cea_9e4a_3bc4_b1a1;

/// Fold all three built-in orders over the fixed corpus, in production's representation.
fn pinned_checksum() -> u64 {
    let monomials = corpus::<7>(512, 626, 6);
    let mut acc = 0u64;
    for order in [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ] {
        for i in 0..monomials.len() {
            let j = (i * STRIDE + 13) % monomials.len();
            acc = fold(acc, order.cmp(&monomials[i], &monomials[j]));
        }
    }
    acc
}

/// The fourth arm's body must do the fourth arm's work, so it is checked against production's.
///
/// This is also the only place [`WideOrder::Weighted`] is constructed; see [`WIDE_WEIGHTED`].
fn weighted_arms_agree() {
    let monomials = corpus::<7>(128, 627, 6);
    let production = MonomialOrder::weighted(
        WIDE_WEIGHTED.weights,
        zeebra::WeightedTieBreak::ReverseLexicographic,
    )
    .expect("positive weights");
    let wide = black_box(WideOrder::Weighted(&WIDE_WEIGHTED));
    for i in 0..monomials.len() {
        let j = (i * STRIDE + 13) % monomials.len();
        assert_eq!(
            production.cmp(&monomials[i], &monomials[j]),
            wide.cmp(&monomials[i], &monomials[j]),
            "the wide arm's weighted transcription disagrees with production at {i}"
        );
    }
}

/// The same fold through the two ablation representations, which must give the same number.
fn ablation_checksums() -> (u64, u64) {
    let monomials = corpus::<7>(512, 626, 6);
    let mut wide_acc = 0u64;
    let mut narrow_acc = 0u64;
    for order in [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ] {
        let (narrow, wide) = triple(order);
        for i in 0..monomials.len() {
            let j = (i * STRIDE + 13) % monomials.len();
            wide_acc = fold(wide_acc, wide.cmp(&monomials[i], &monomials[j]));
            narrow_acc = fold(narrow_acc, narrow.cmp(&monomials[i], &monomials[j]));
        }
    }
    (wide_acc, narrow_acc)
}

fn main() {
    // The sizes are the premise, so they are checked rather than described. `narrow` must be the
    // pre-#306 width and `wide` must be the current one, or the two rows are not the comparison
    // this harness claims to make.
    assert_eq!(size_of::<NarrowOrder>(), 1, "the narrow arm is not one byte");
    assert_eq!(
        size_of::<WideOrder>(),
        size_of::<MonomialOrder>(),
        "the wide arm does not match the production type's size"
    );
    assert_eq!(
        size_of::<MonomialOrder>(),
        2 * size_of::<usize>(),
        "MonomialOrder is no longer two words"
    );

    weighted_arms_agree();
    let produced = pinned_checksum();
    let (wide_sum, narrow_sum) = ablation_checksums();
    assert_eq!(
        produced, PINNED_CHECKSUM,
        "the production comparator no longer matches its pinned checksum; \
         src/poly/multivariate/monomial_order.rs has the other copy of this number"
    );
    assert_eq!(
        produced, wide_sum,
        "the wide transcription disagrees with production"
    );
    assert_eq!(
        produced, narrow_sum,
        "the narrow transcription disagrees with production"
    );

    println!(
        "MonomialOrder = {} bytes, NarrowOrder = {} byte, WideOrder = {} bytes; \
         pinned checksum {PINNED_CHECKSUM:#018x} reproduced",
        size_of::<MonomialOrder>(),
        size_of::<NarrowOrder>(),
        size_of::<WideOrder>()
    );
    println!(
        "{REPETITIONS} repetitions, min-reduced, arms rotated; \
         {DISPATCH_COMPARISONS} comparisons per dispatch lap, {SORT_PASSES} sort passes per lap\n"
    );

    let mut rows = Vec::new();
    rows.extend(measure(
        "cyclic-5",
        MonomialOrder::Lexicographic,
        cyclic::<5, F>(),
    ));
    rows.extend(measure(
        "katsura-5",
        MonomialOrder::Lexicographic,
        katsura::<5, F>(),
    ));
    rows.extend(measure(
        "katsura-6",
        MonomialOrder::Lexicographic,
        katsura::<6, F>(),
    ));
    rows.extend(measure(
        "katsura-6",
        MonomialOrder::GradedReverseLexicographic,
        katsura::<6, F>(),
    ));
    rows.extend(measure(
        "katsura-7",
        MonomialOrder::GradedLexicographic,
        katsura::<7, F>(),
    ));

    println!("\ndispatch: {DISPATCH_COMPARISONS} comparisons, the order reloaded per comparison");
    println!(
        "{:<12} {:<8} {:>8} {:>10} {:>10} {:>10} {:>10} {:>10}",
        "system", "order", "distinct", "prod/ms", "wide/ms", "narrow/ms", "wide/prod", "narrow/wide"
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
        "narrow/wide"
    );
    for row in &rows {
        row.print_sort();
    }
}
