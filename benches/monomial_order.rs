//! `MonomialOrder::cmp` against the same comparison with the total degree stored.
//!
//! #317's gate. A graded order recomputes `degree()` on both operands by summing `[u32; N]`
//! (`monomial.rs:53`), and `interreduction-cost.md` §3d counts 893 610 377 of those comparisons in
//! the span of one `mq-random-10` run. Whether storing the degree is worth a change to a
//! serialized type is decided here, before anything is built.
//!
//! **Four arms, because two earlier cuts of this benchmark measured themselves.** `lex` never
//! reads the degree, so a lex row is a control: anything it shows is something other than the
//! change under test. The first cut registered the production `cmp` straight against a prototype
//! and reported lex at **3.32x**. The second split the prototype in two but let the two differ in
//! size as well as in the degree, and reported lex at **3.555x at N = 7** — because
//! `[u32; 7]` is exactly 28 bytes while the same array beside a `u64` degree sits in a 40-byte
//! struct with four bytes of padding behind it, and a wider aligned load over the array is legal
//! in the second and out of bounds in the first. That is a layout effect wearing the degree's
//! clothes, and at N = 7 it was larger than the effect being measured.
//!
//! So the degree and the layout are separated by construction:
//!
//! | arm | layout | `degree()` | what it is for |
//! |---|---|---|---|
//! | `production` | `Monomial<N>` | sums the array | the tree as it stands |
//! | `tight` | `[u32; N]` alone | sums the array | fidelity check against `production` |
//! | `summed` | `[u32; N]` + a dead `u64` | sums the array | **the comparand for `stored`** |
//! | `stored` | `[u32; N]` + a `u64` degree | reads the field | the change under test |
//!
//! `summed` and `stored` are byte-for-byte the same shape and differ in exactly one expression, so
//! **their lex rows must come out at ~1.0** — that is the control, and a large value there means
//! the harness is measuring itself (#517/#496) rather than the representation. `tight` against
//! `summed` isolates the layout effect on its own, which is a real cost of the change and is
//! reported as layout rather than folded into the degree. `tight` against `production` says
//! whether the transcription is the production path at all.
//!
//! Every arm is a concrete named type with its comparison written out, not one kernel
//! parameterized by representation, for the same reason.

use std::cmp::Ordering;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{Monomial, MonomialOrder};

/// Monomials per array.
///
/// Sized to the stage this gate is aimed at rather than to the cache: `interreduction-cost.md` §3
/// measures the mean working polynomial at 2 199 terms and the comparison span at 1 673 of them a
/// step. Two arrays of 2 048 monomials are 115–131 kB depending on the arm, so every arm is
/// L2-resident exactly as the real merge is. An L1-resident length would make the degree sum look
/// more expensive relative to the loads than it is in the loop that motivated the issue.
const LEN: usize = 2048;

/// Exponent bound in the `distinct` regime.
const MAX_EXPONENT: u32 = 6;

/// Total degree every monomial carries in the `tied` regime.
const TIED_DEGREE: u32 = 8;

const ORDERS: [MonomialOrder; 3] = [
    MonomialOrder::Lexicographic,
    MonomialOrder::GradedLexicographic,
    MonomialOrder::GradedReverseLexicographic,
];

/// A bench-local copy of `Monomial<N>`'s layout and accessor, at the production size.
///
/// Field order, the `&[u32]`-returning accessor and the `u64` degree sum are all copied from
/// `src/poly/multivariate/monomial.rs` deliberately. Its only job is the fidelity check: if this
/// does not track `production`, the transcription below is not the production comparison.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
struct TightMonomial<const N: usize> {
    exponents: [u32; N],
}

impl<const N: usize> TightMonomial<N> {
    fn new(exponents: &[u32]) -> Self {
        let mut e = [0; N];
        e.copy_from_slice(exponents);
        Self { exponents: e }
    }

    #[inline]
    fn exponents(&self) -> &[u32] {
        &self.exponents
    }

    #[inline]
    fn degree(&self) -> u64 {
        self.exponents.iter().map(|e| *e as u64).sum()
    }
}

/// `TightMonomial` grown to `StoredMonomial`'s exact layout, still summing the degree.
///
/// The dead `u64` is the whole point: it reproduces the padding and alignment a stored degree
/// forces, so that `summed` against `stored` is the degree alone. Without it the two arms differ
/// in size, and at N = 7 that difference was worth 3.555x on an order that never reads the degree.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
struct SummedMonomial<const N: usize> {
    exponents: [u32; N],
    /// Never read. Present only to match `StoredMonomial<N>`'s size and alignment.
    _layout: u64,
}

impl<const N: usize> SummedMonomial<N> {
    fn new(exponents: &[u32]) -> Self {
        let mut e = [0; N];
        e.copy_from_slice(exponents);
        Self {
            exponents: e,
            _layout: 0,
        }
    }

    #[inline]
    fn exponents(&self) -> &[u32] {
        &self.exponents
    }

    #[inline]
    fn degree(&self) -> u64 {
        self.exponents.iter().map(|e| *e as u64).sum()
    }
}

/// The same, with the total degree stored rather than summed.
///
/// The prototype the gate prices, and deliberately not a candidate for the tree: it carries no
/// arithmetic, no serialization and no overflow contract, because none of those are what is being
/// measured. The degree is `u64` so that `degree()` returns the same type as the production method
/// and the comparison it feeds is the same width.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
struct StoredMonomial<const N: usize> {
    exponents: [u32; N],
    degree: u64,
}

impl<const N: usize> StoredMonomial<N> {
    fn new(exponents: &[u32]) -> Self {
        let mut e = [0; N];
        e.copy_from_slice(exponents);
        Self {
            exponents: e,
            degree: exponents.iter().map(|x| *x as u64).sum(),
        }
    }

    #[inline]
    fn exponents(&self) -> &[u32] {
        &self.exponents
    }

    #[inline]
    fn degree(&self) -> u64 {
        self.degree
    }
}

/// Transcribes `MonomialOrder::cmp` over `TightMonomial`, including the `match` on `&self`.
fn tight_cmp<const N: usize>(
    order: &MonomialOrder,
    a: &TightMonomial<N>,
    b: &TightMonomial<N>,
) -> Ordering {
    match order {
        MonomialOrder::Lexicographic => a.exponents().cmp(b.exponents()),
        MonomialOrder::GradedLexicographic => match a.degree().cmp(&b.degree()) {
            Ordering::Equal => a.exponents().cmp(b.exponents()),
            ord => ord,
        },
        MonomialOrder::GradedReverseLexicographic => match a.degree().cmp(&b.degree()) {
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
        },
    }
}

/// The same body over `SummedMonomial`, which is `StoredMonomial`'s layout with a summed degree.
fn summed_cmp<const N: usize>(
    order: &MonomialOrder,
    a: &SummedMonomial<N>,
    b: &SummedMonomial<N>,
) -> Ordering {
    match order {
        MonomialOrder::Lexicographic => a.exponents().cmp(b.exponents()),
        MonomialOrder::GradedLexicographic => match a.degree().cmp(&b.degree()) {
            Ordering::Equal => a.exponents().cmp(b.exponents()),
            ord => ord,
        },
        MonomialOrder::GradedReverseLexicographic => match a.degree().cmp(&b.degree()) {
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
        },
    }
}

/// The same body over `StoredMonomial`. `degree()` reads a field; everything else is identical.
fn stored_cmp<const N: usize>(
    order: &MonomialOrder,
    a: &StoredMonomial<N>,
    b: &StoredMonomial<N>,
) -> Ordering {
    match order {
        MonomialOrder::Lexicographic => a.exponents().cmp(b.exponents()),
        MonomialOrder::GradedLexicographic => match a.degree().cmp(&b.degree()) {
            Ordering::Equal => a.exponents().cmp(b.exponents()),
            ord => ord,
        },
        MonomialOrder::GradedReverseLexicographic => match a.degree().cmp(&b.degree()) {
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
        },
    }
}

/// Exponent vectors whose total degrees vary, so a graded comparison usually exits on the degree.
fn distinct_exponents<const N: usize>(rng: &mut StdRng) -> Vec<Vec<u32>> {
    (0..LEN)
        .map(|_| (0..N).map(|_| rng.gen_range(0..=MAX_EXPONENT)).collect())
        .collect()
}

/// Exponent vectors all of total degree `TIED_DEGREE`, so a graded comparison never exits early.
///
/// Built by distributing the degree over the variables one unit at a time, which gives a different
/// vector per draw without rejection sampling.
fn tied_exponents<const N: usize>(rng: &mut StdRng) -> Vec<Vec<u32>> {
    (0..LEN)
        .map(|_| {
            let mut e = vec![0u32; N];
            for _ in 0..TIED_DEGREE {
                e[rng.gen_range(0..N)] += 1;
            }
            e
        })
        .collect()
}

/// The four arms' inputs, built from one set of exponent vectors so they compare the same pairs.
struct Inputs<const N: usize> {
    production_a: Vec<Monomial<N>>,
    production_b: Vec<Monomial<N>>,
    tight_a: Vec<TightMonomial<N>>,
    tight_b: Vec<TightMonomial<N>>,
    summed_a: Vec<SummedMonomial<N>>,
    summed_b: Vec<SummedMonomial<N>>,
    stored_a: Vec<StoredMonomial<N>>,
    stored_b: Vec<StoredMonomial<N>>,
}

impl<const N: usize> Inputs<N> {
    fn build(left: &[Vec<u32>], right: &[Vec<u32>]) -> Self {
        let inputs = Self {
            production_a: left.iter().map(|e| Monomial::new(e)).collect(),
            production_b: right.iter().map(|e| Monomial::new(e)).collect(),
            tight_a: left.iter().map(|e| TightMonomial::new(e)).collect(),
            tight_b: right.iter().map(|e| TightMonomial::new(e)).collect(),
            summed_a: left.iter().map(|e| SummedMonomial::new(e)).collect(),
            summed_b: right.iter().map(|e| SummedMonomial::new(e)).collect(),
            stored_a: left.iter().map(|e| StoredMonomial::new(e)).collect(),
            stored_b: right.iter().map(|e| StoredMonomial::new(e)).collect(),
        };
        Self::assert_layouts_match();
        inputs.assert_arms_agree();
        inputs
    }

    /// `summed` and `stored` must be the same shape, or their ratio is not the degree.
    ///
    /// This is the assertion the second cut of this benchmark lacked. With `summed` at the
    /// production size and `stored` eight bytes larger, the lex control read 3.555x at N = 7 and
    /// the number had nothing to do with the degree.
    fn assert_layouts_match() {
        assert_eq!(
            std::mem::size_of::<SummedMonomial<N>>(),
            std::mem::size_of::<StoredMonomial<N>>(),
            "the summed and stored arms differ in size at N = {N}, so their ratio is layout",
        );
        assert_eq!(
            std::mem::align_of::<SummedMonomial<N>>(),
            std::mem::align_of::<StoredMonomial<N>>(),
            "the summed and stored arms differ in alignment at N = {N}",
        );
    }

    /// Every arm must return the same `Ordering` on every pair this benchmark will time.
    ///
    /// Checked on the measured inputs rather than only in a unit test, because the failure this
    /// guards against is an arm that is faster for the wrong reason, and the inputs are where that
    /// shows up. A transcription that has drifted from the production comparison fails here.
    fn assert_arms_agree(&self) {
        for order in ORDERS {
            for i in 0..LEN {
                let expected = order.cmp(&self.production_a[i], &self.production_b[i]);
                assert_eq!(
                    expected,
                    tight_cmp(&order, &self.tight_a[i], &self.tight_b[i]),
                    "{}: the tight transcription disagrees with production on pair {i}, N = {N}",
                    order.name()
                );
                assert_eq!(
                    expected,
                    summed_cmp(&order, &self.summed_a[i], &self.summed_b[i]),
                    "{}: the summed transcription disagrees with production on pair {i}, N = {N}",
                    order.name()
                );
                assert_eq!(
                    expected,
                    stored_cmp(&order, &self.stored_a[i], &self.stored_b[i]),
                    "{}: the stored prototype disagrees with production on pair {i}, N = {N}",
                    order.name()
                );
            }
        }
    }
}

/// Fold an `Ordering` into an accumulator, so no comparison can be dropped as dead.
#[inline(always)]
fn fold(acc: u64, ord: Ordering) -> u64 {
    acc.wrapping_mul(3).wrapping_add(ord as i8 as u64)
}

fn arms<const N: usize>(c: &mut Criterion, regime: &str, left: &[Vec<u32>], right: &[Vec<u32>]) {
    let inputs = Inputs::<N>::build(left, right);
    let mut group = c.benchmark_group("monomial-cmp");
    group.throughput(criterion::Throughput::Elements(LEN as u64));

    for order in ORDERS {
        // Registered adjacently so one configuration's arms are measured together rather than at
        // opposite ends of the run (the house interleaving protocol).
        let label = format!("N={N}/{}/{regime}", order.name());

        group.bench_function(BenchmarkId::new("production", &label), |b| {
            let (a, d) = (&inputs.production_a, &inputs.production_b);
            b.iter(|| {
                let mut acc = 0u64;
                for i in 0..LEN {
                    acc = fold(acc, order.cmp(&a[i], &d[i]));
                }
                black_box(acc)
            });
        });

        group.bench_function(BenchmarkId::new("tight", &label), |b| {
            let (a, d) = (&inputs.tight_a, &inputs.tight_b);
            b.iter(|| {
                let mut acc = 0u64;
                for i in 0..LEN {
                    acc = fold(acc, tight_cmp(&order, &a[i], &d[i]));
                }
                black_box(acc)
            });
        });

        group.bench_function(BenchmarkId::new("summed", &label), |b| {
            let (a, d) = (&inputs.summed_a, &inputs.summed_b);
            b.iter(|| {
                let mut acc = 0u64;
                for i in 0..LEN {
                    acc = fold(acc, summed_cmp(&order, &a[i], &d[i]));
                }
                black_box(acc)
            });
        });

        group.bench_function(BenchmarkId::new("stored", &label), |b| {
            let (a, d) = (&inputs.stored_a, &inputs.stored_b);
            b.iter(|| {
                let mut acc = 0u64;
                for i in 0..LEN {
                    acc = fold(acc, stored_cmp(&order, &a[i], &d[i]));
                }
                black_box(acc)
            });
        });
    }

    group.finish();
}

fn benches(c: &mut Criterion) {
    let mut rng = StdRng::seed_from_u64(317);

    // N = 5, 7, 8 are the arities #317 names: below, at and above the seven that fits a packed
    // u64 with eight-bit exponents and a degree byte. N = 10 is added because it is the arity of
    // `mq-random-10`, and factor C — the 14.0x per-operation constant this change is aimed at
    // (`groebner-jl-gap.md` §7) — was measured there and nowhere else. A gate run only at 5, 7
    // and 8 would not speak to the instance whose gap is the premise.
    let left = distinct_exponents::<5>(&mut rng);
    let right = distinct_exponents::<5>(&mut rng);
    arms::<5>(c, "distinct", &left, &right);
    let left = tied_exponents::<5>(&mut rng);
    let right = tied_exponents::<5>(&mut rng);
    arms::<5>(c, "tied", &left, &right);

    let left = distinct_exponents::<7>(&mut rng);
    let right = distinct_exponents::<7>(&mut rng);
    arms::<7>(c, "distinct", &left, &right);
    let left = tied_exponents::<7>(&mut rng);
    let right = tied_exponents::<7>(&mut rng);
    arms::<7>(c, "tied", &left, &right);

    let left = distinct_exponents::<8>(&mut rng);
    let right = distinct_exponents::<8>(&mut rng);
    arms::<8>(c, "distinct", &left, &right);
    let left = tied_exponents::<8>(&mut rng);
    let right = tied_exponents::<8>(&mut rng);
    arms::<8>(c, "tied", &left, &right);

    let left = distinct_exponents::<10>(&mut rng);
    let right = distinct_exponents::<10>(&mut rng);
    arms::<10>(c, "distinct", &left, &right);
    let left = tied_exponents::<10>(&mut rng);
    let right = tied_exponents::<10>(&mut rng);
    arms::<10>(c, "tied", &left, &right);
}

criterion_group!(monomial_order, benches);
criterion_main!(monomial_order);
