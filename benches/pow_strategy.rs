//! `FiniteField::pow`'s body: the recursive shape against three iterative bit-walks.
//!
//! #181's gate rather than a coverage benchmark. `pow`'s default body was recursive and
//! `pow_limbs` is the same algorithm as a loop, so the question is whether the one-line delegation
//! `pow(b) = pow_limbs(&[b as u64, (b >> 64) as u64])` costs anything at the exponent widths the
//! call sites actually use. It turns out to depend on the width, and the five arms are what
//! separates the two reasons:
//!
//! - `production` — `FiniteField::pow` as shipped. The arm that moves when the default changes.
//! - `recursive` — the pre-#181 recursive body.
//! - `ascending` — the delegation as proposed: the upward walk `pow_limbs` was, from an
//!   accumulator seeded with `one`.
//! - `descending` — the same walk from the top bit down, which needs no seed because the top bit
//!   is set, but whose squaring and accumulate are one value and so strictly serial.
//! - `seeded` — upward, with the accumulator started at `a^(2^lowest)` rather than at one. The
//!   multiplication count of `recursive` and `descending`, the dependency structure of
//!   `ascending`.
//!
//! The four candidates are bench-local transcriptions, including the two the shipped `pow_limbs`
//! is made of: `pow_limbs` chooses between them on the exponent's width, so an arm that called it
//! would measure the shipped choice rather than the walk it names. `production` tracking the arm
//! the threshold selects — `descending` at `d1` to `d5`, `ascending` above — is therefore the
//! fidelity check, and it has to be made rather than assumed: this crate builds under fat LTO at
//! one codegen unit, so a transcription is not automatically compiled like the trait default it
//! copies, and one that does not match the arm it claims to reproduce prices nothing.
//!
//! It does not match perfectly, and the `d1` cells are where it shows: at about 2 ns a call the
//! whole measurement is a handful of cycles, and `production` and the arm it should be have been
//! seen 0.8 ns apart. Read those cells as "both are about 2 ns" rather than as a ratio; the
//! differences this benchmark exists to price are 1.2x to 41x and sit well clear of it.
//!
//! The exponent widths are the ones in the tree, plus two that are not. `d1` through `d5` are
//! every small-exponent site — `Monomial::eval`, `SparseMultiPoly::substitute`, Poseidon's
//! `x^alpha` — which are all literally `x.pow(d)` for a degree of 1 to 5. `e31` is the width of
//! `PowerPermutation`'s `inverse_exponent`, `d^-1 mod q - 1`, which is as wide as the field; the
//! `power_permutation` group runs the real `invert` at the real inverse exponent, and the
//! microbench cells hold the width fixed across fields so the per-field multiply cost is what
//! varies. `e8` and `e16` are in no call site and exist only to site `NARROW_EXPONENT_BITS`.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, Mersenne31, Zp18446744073709551557},
    integers::{bit, highest_set_bit, lowest_set_bit},
    FiniteField, Monomial, MultivariatePolynomial, PowerPermutation,
};

/// Enough operands that the sequence does not sit in a single cache line, few enough to stay hot.
const OPERANDS: usize = 64;

/// An 8-bit and a 16-bit exponent. Nothing in the crate uses a width between a monomial degree
/// and the field's order, so these exist only to site `NARROW_EXPONENT_BITS`: the threshold is set
/// at the top of the region where the downward walk measured faster, and these say where that
/// region ends.
const E8: u128 = 0xA5;
const E16: u128 = 0xA5A5;

/// A 31-bit exponent, odd so the recursion takes both of its branches at the bottom.
const E31: u128 = 0x5A5A_5A5B;

/// A 63-bit exponent. 63 rather than 64 so the top limb stays empty and every arm walks the same
/// number of bits. Used by the agreement assertion rather than by a timed cell: `e31` settles the
/// wide regime and `e63` only doubled it.
const E63: u128 = 0x5A5A_5A5A_5A5A_5A5B;

fn operands<F: FiniteField>(seed: u64) -> Vec<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..OPERANDS).map(|_| F::random(&mut rng)).collect()
}

/// The pre-#181 recursive default body, transcribed.
fn recursive_pow<F: FiniteField>(a: &F, b: u128) -> F {
    if a.is_zero() {
        if b == 0 {
            return F::one();
        }
        return F::zero();
    }
    if b == 0 {
        return F::one();
    }
    if b == 1 {
        *a
    } else if b.is_multiple_of(2) {
        let y = recursive_pow(a, b / 2);
        y * y
    } else {
        *a * recursive_pow(a, b - 1)
    }
}

/// The delegation as #181 proposed it: straight onto the upward walk `pow_limbs` was before this
/// change, from an accumulator seeded with `one`.
///
/// Transcribed rather than calling `pow_limbs`, because `pow_limbs` now chooses between this walk
/// and [`descending_pow_limbs`] on the exponent's width, so calling it would measure the shipped
/// choice twice and the arm under test not at all.
///
/// The seed costs one multiplication by one that the recursive body does not pay: one against zero
/// at `b = 1`, two against one at `b = 2`, three against two at `b = 3`.
fn ascending_pow<F: FiniteField>(a: &F, b: u128) -> F {
    ascending_pow_limbs(a, &[b as u64, (b >> 64) as u64])
}

fn ascending_pow_limbs<F: FiniteField>(a: &F, exponent: &[u64]) -> F {
    let Some(highest) = highest_set_bit(exponent) else {
        return F::one();
    };
    let mut result = F::one();
    let mut square = *a;
    for index in 0..=highest {
        if bit(exponent, index) {
            result *= square;
        }
        if index < highest {
            square = square * square;
        }
    }
    result
}

/// The walk from the top bit down, which spends the seed multiplication instead of paying it: the
/// highest bit is set by definition, so the accumulator starts at the base.
///
/// Its squaring and its accumulate are the *same* value, which is a strictly serial dependency
/// chain. `pow_limbs`'s squaring and accumulate are two different values and can overlap, so this
/// arm trades instruction-level parallelism for the multiplication it saves.
fn descending_pow<F: FiniteField>(a: &F, b: u128) -> F {
    descending_pow_limbs(a, &[b as u64, (b >> 64) as u64])
}

fn descending_pow_limbs<F: FiniteField>(a: &F, exponent: &[u64]) -> F {
    let Some(highest) = highest_set_bit(exponent) else {
        return F::one();
    };
    let mut result = *a;
    for index in (0..highest).rev() {
        result = result * result;
        if bit(exponent, index) {
            result *= *a;
        }
    }
    result
}

/// `pow_limbs`'s upward walk with the seed multiplication removed rather than traded away: the
/// accumulator starts at `a^(2^lowest)` for the lowest set bit of the exponent, which is the first
/// value the upward walk would have multiplied into it.
///
/// Same multiplication count as the recursive body and as [`descending_pow`], and the same
/// independent squaring and accumulate as the upward walk, so it is the arm that should take both
/// wins.
fn seeded_pow<F: FiniteField>(a: &F, b: u128) -> F {
    seeded_pow_limbs(a, &[b as u64, (b >> 64) as u64])
}

fn seeded_pow_limbs<F: FiniteField>(a: &F, exponent: &[u64]) -> F {
    let Some(highest) = highest_set_bit(exponent) else {
        return F::one();
    };
    // A nonzero exponent has a lowest set bit whenever it has a highest one.
    let lowest = lowest_set_bit(exponent).unwrap_or(highest);

    let mut square = *a;
    for _ in 0..lowest {
        square = square * square;
    }
    let mut result = square;
    for index in (lowest + 1)..=highest {
        square = square * square;
        if bit(exponent, index) {
            result *= square;
        }
    }
    result
}

fn bench_pow<F: FiniteField>(c: &mut Criterion, name: &str) {
    let values = operands::<F>(181);

    // The arms have to compute the same thing for their timings to mean anything, and a benchmark
    // of a wrong answer is the one failure a criterion report cannot show.
    for x in values.iter().take(4).chain([F::zero(), F::one()].iter()) {
        for b in [0u128, 1, 2, 3, 5, 17, E31, E63, u128::MAX] {
            assert_eq!(x.pow(b), recursive_pow(x, b), "{name}: {x}^{b}");
            assert_eq!(x.pow(b), ascending_pow(x, b), "{name}: {x}^{b}");
            assert_eq!(x.pow(b), descending_pow(x, b), "{name}: {x}^{b}");
            assert_eq!(x.pow(b), seeded_pow(x, b), "{name}: {x}^{b}");
        }
    }

    let mut group = c.benchmark_group("pow");

    // `d1` is where the upward walk is most exposed: it seeds its accumulator with one and so
    // pays a multiplication the recursive body does not — one against zero. Exponent-1 variables
    // are the common case in `Monomial::eval`, so this is not a corner.
    for (label, exponent) in [
        ("d1", 1u128),
        ("d3", 3),
        ("d5", 5),
        ("e8", E8),
        ("e16", E16),
        ("e31", E31),
    ] {
        // Registered adjacently, so the five arms of one cell are measured as close together in
        // one process as criterion allows.
        group.bench_with_input(
            BenchmarkId::new(format!("{name}/{label}/production"), OPERANDS),
            &values,
            |bencher, values| {
                bencher.iter(|| {
                    for x in values.iter() {
                        black_box(black_box(x).pow(black_box(exponent)));
                    }
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new(format!("{name}/{label}/recursive"), OPERANDS),
            &values,
            |bencher, values| {
                bencher.iter(|| {
                    for x in values.iter() {
                        black_box(recursive_pow(black_box(x), black_box(exponent)));
                    }
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new(format!("{name}/{label}/ascending"), OPERANDS),
            &values,
            |bencher, values| {
                bencher.iter(|| {
                    for x in values.iter() {
                        black_box(ascending_pow(black_box(x), black_box(exponent)));
                    }
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new(format!("{name}/{label}/descending"), OPERANDS),
            &values,
            |bencher, values| {
                bencher.iter(|| {
                    for x in values.iter() {
                        black_box(descending_pow(black_box(x), black_box(exponent)));
                    }
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new(format!("{name}/{label}/seeded"), OPERANDS),
            &values,
            |bencher, values| {
                bencher.iter(|| {
                    for x in values.iter() {
                        black_box(seeded_pow(black_box(x), black_box(exponent)));
                    }
                })
            },
        );
    }

    group.finish();
}

/// `PowerPermutation::invert` at the real inverse exponent, which is the one large-exponent site
/// #181 names. The `iterative` arm is the body `invert` would have after the delegation.
fn bench_power_permutation<F: FiniteField + zeebra::KnownOrder>(c: &mut Criterion, name: &str) {
    let Some(permutation) = PowerPermutation::<F>::new(5).or_else(|| PowerPermutation::new(3))
    else {
        panic!("neither x^5 nor x^3 permutes {name}");
    };
    let exponent = permutation.inverse_exponent();
    let values = operands::<F>(182);

    let mut group = c.benchmark_group("power_permutation");
    group.bench_with_input(
        BenchmarkId::new(format!("{name}/invert/production"), exponent.ilog2() + 1),
        &values,
        |bencher, values| {
            bencher.iter(|| {
                for y in values.iter() {
                    black_box(permutation.invert(black_box(y)));
                }
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new(format!("{name}/invert/recursive"), exponent.ilog2() + 1),
        &values,
        |bencher, values| {
            bencher.iter(|| {
                for y in values.iter() {
                    black_box(recursive_pow(black_box(y), exponent));
                }
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new(format!("{name}/invert/ascending"), exponent.ilog2() + 1),
        &values,
        |bencher, values| {
            bencher.iter(|| {
                for y in values.iter() {
                    black_box(ascending_pow(black_box(y), exponent));
                }
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new(format!("{name}/invert/descending"), exponent.ilog2() + 1),
        &values,
        |bencher, values| {
            bencher.iter(|| {
                for y in values.iter() {
                    black_box(descending_pow(black_box(y), exponent));
                }
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new(format!("{name}/invert/seeded"), exponent.ilog2() + 1),
        &values,
        |bencher, values| {
            bencher.iter(|| {
                for y in values.iter() {
                    black_box(seeded_pow(black_box(y), exponent));
                }
            })
        },
    );
    group.finish();
}

const ARITY: usize = 4;

/// An exponentiation route, carried as a type rather than as a `fn` pointer so that each site
/// transcription monomorphizes on it. A function pointer would charge every arm an indirect call
/// it cannot inline through, which is equal across the three candidates but leaves none of them
/// comparable with `production`.
trait Route {
    fn pow<F: FiniteField>(a: &F, b: u128) -> F;
}

struct Recursive;
impl Route for Recursive {
    fn pow<F: FiniteField>(a: &F, b: u128) -> F {
        recursive_pow(a, b)
    }
}

struct Ascending;
impl Route for Ascending {
    fn pow<F: FiniteField>(a: &F, b: u128) -> F {
        ascending_pow(a, b)
    }
}

struct Descending;
impl Route for Descending {
    fn pow<F: FiniteField>(a: &F, b: u128) -> F {
        descending_pow(a, b)
    }
}

struct Seeded;
impl Route for Seeded {
    fn pow<F: FiniteField>(a: &F, b: u128) -> F {
        seeded_pow(a, b)
    }
}

/// `Monomial::eval`, transcribed with a given exponentiation route in place of `pow`.
fn eval_with<F: FiniteField, R: Route>(monomial: &Monomial<ARITY>, x: &[F]) -> F {
    monomial
        .exponents()
        .iter()
        .zip(x)
        .fold(F::one(), |acc, (e, x)| acc * R::pow(x, *e as u128))
}

/// `SparseMultiPoly::substitute`, transcribed with a given exponentiation route in place of `pow`.
fn substitute_with<F: FiniteField, R: Route>(
    polynomial: &MultivariatePolynomial<ARITY, F>,
    index: usize,
    value: F,
) -> MultivariatePolynomial<ARITY, F> {
    let substituted: Vec<(Monomial<ARITY>, F)> = polynomial
        .terms()
        .iter()
        .map(|(monomial, coefficient)| {
            let exponent = monomial.exponents()[index];
            let mut exponents = [0u32; ARITY];
            exponents.copy_from_slice(monomial.exponents());
            exponents[index] = 0;
            (
                Monomial::new(&exponents),
                *coefficient * R::pow(&value, exponent as u128),
            )
        })
        .collect();
    MultivariatePolynomial::new(&substituted)
}

/// The small-exponent sites at the shape they occur in: a degree-5 monomial in four variables,
/// and a 64-term polynomial over the same ring.
fn bench_small_exponent_sites<F: FiniteField>(c: &mut Criterion, name: &str) {
    let mut rng = StdRng::seed_from_u64(183);
    let monomial = Monomial::<ARITY>::new(&[3, 0, 5, 1]);
    let point: Vec<F> = (0..ARITY).map(|_| F::random(&mut rng)).collect();

    let terms: Vec<(Monomial<ARITY>, F)> = (0..64)
        .map(|i: u32| {
            let exponents = [i % 6, (i / 2) % 6, (i / 3) % 6, (i / 5) % 6];
            (Monomial::new(&exponents), F::random(&mut rng))
        })
        .collect();
    let polynomial = MultivariatePolynomial::<ARITY, F>::new(&terms);
    let value = F::random(&mut rng);

    let mut group = c.benchmark_group("small_exponent");
    group.bench_function(
        BenchmarkId::new(format!("{name}/eval/production"), ARITY),
        |bencher| bencher.iter(|| black_box(black_box(&monomial).eval(black_box(&point)))),
    );
    macro_rules! eval_arm {
        ($arm:literal, $route:ty) => {
            group.bench_function(
                BenchmarkId::new(format!("{name}/eval/{}", $arm), ARITY),
                |bencher| {
                    bencher.iter(|| {
                        black_box(eval_with::<F, $route>(
                            black_box(&monomial),
                            black_box(&point),
                        ))
                    })
                },
            );
        };
    }
    eval_arm!("recursive", Recursive);
    eval_arm!("ascending", Ascending);
    eval_arm!("descending", Descending);
    eval_arm!("seeded", Seeded);

    group.bench_function(
        BenchmarkId::new(format!("{name}/substitute/production"), 64),
        |bencher| {
            bencher.iter(|| black_box(black_box(&polynomial).substitute(0, black_box(value))))
        },
    );
    macro_rules! substitute_arm {
        ($arm:literal, $route:ty) => {
            group.bench_function(
                BenchmarkId::new(format!("{name}/substitute/{}", $arm), 64),
                |bencher| {
                    bencher.iter(|| {
                        black_box(substitute_with::<F, $route>(
                            black_box(&polynomial),
                            0,
                            black_box(value),
                        ))
                    })
                },
            );
        };
    }
    substitute_arm!("recursive", Recursive);
    substitute_arm!("ascending", Ascending);
    substitute_arm!("descending", Descending);
    substitute_arm!("seeded", Seeded);
    group.finish();
}

/// 3 * 2^66 + 1, a 68-bit Proth prime over the deprecated 128-bit field. It is the one arm of
/// #160's A/B that still reached `pow` after that change, so it is kept here for continuity.
#[allow(deprecated)]
type Zp128 = zeebra::fields::PrimeFieldElement128<221360928884514619393>;

fn benches(c: &mut Criterion) {
    bench_pow::<Mersenne31>(c, "p31_u32");
    bench_pow::<Zp18446744073709551557>(c, "p64");
    bench_pow::<Zp128>(c, "p68");
    bench_pow::<Bn254Fr>(c, "p254_bn254");

    bench_power_permutation::<Mersenne31>(c, "p31_u32");
    bench_power_permutation::<Zp18446744073709551557>(c, "p64");

    bench_small_exponent_sites::<Mersenne31>(c, "p31_u32");
    bench_small_exponent_sites::<Zp18446744073709551557>(c, "p64");
    bench_small_exponent_sites::<Bn254Fr>(c, "p254_bn254");
}

criterion_group!(pow_strategy, benches);
criterion_main!(pow_strategy);
