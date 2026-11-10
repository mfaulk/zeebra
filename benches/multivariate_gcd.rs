//! The three multivariate GCD routes, over the shapes that separate them.
//!
//! #433 deliberately added no bench, and #434's objection to that is the reason this file exists: a
//! measurement nobody can re-run is a measurement that rots silently. `examples/gcd_routes.rs` is
//! the *sweep* — it crosses arity, factor size and exponent and prints a table with per-shape
//! verdicts — and this is the *regression surface*, a fixed set of shapes under criterion so a
//! change to any route shows up as a number moving rather than as a table someone has to read.
//!
//! The shapes are the four that `docs/research/multivariate-gcd.md` found to matter, one per
//! regime, and each is built the same way the example builds them: a planted shared factor times
//! two cofactors, so there is a GCD to find rather than a coprime pair.
//!
//! **`Brown` is probed before it is registered.** It is the one route that can refuse — it needs a
//! prime field with more elements than the degree it interpolates over — and criterion has no way
//! to express "this arm does not apply". An arm that panicked mid-measurement would abort the
//! suite; an arm that silently fell back to another route would report that route's time under
//! Brown's name. So the probe runs outside the timed region and the arm is simply not added, the
//! same shape `benches/polynomial_solving.rs` uses for an unsupported solve strategy.
//!
//! Every field here is prime: `Brown` is the subject, and the extension-field refusal is a
//! correctness property that `multivariate_gcd`'s own tests pin rather than a thing to time.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, KoalaBear, PrimeFieldElement64},
    FiniteField, GcdRoute, KnownOrder, Monomial, MultivariatePolynomial,
};

/// Goldilocks, `2^64 - 2^32 + 1`.
type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

/// Fixed, so two runs of this bench are comparable with each other.
const SEED: u64 = 20_260_434;

/// One generated pair: a shared factor of `shared_terms`, cofactors of `cofactor_terms`.
#[derive(Clone, Copy)]
struct Shape {
    name: &'static str,
    shared_terms: usize,
    cofactor_terms: usize,
    max_exponent: u32,
}

/// Four shapes, one per regime `docs/research/multivariate-gcd.md` separates.
///
/// `small` is where the routes are within noise of each other and the setup cost of a modular route
/// is the whole story. `wide` is where the primitive route's content recursion was measured at 628x.
/// `grown` is where the subresultant route's own coefficient growth was measured at 24x. `deep` is
/// the shape that crosses both at four variables.
const SHAPES: [Shape; 4] = [
    Shape {
        name: "small",
        shared_terms: 2,
        cofactor_terms: 2,
        max_exponent: 2,
    },
    Shape {
        name: "wide",
        shared_terms: 2,
        cofactor_terms: 6,
        max_exponent: 3,
    },
    Shape {
        name: "grown",
        shared_terms: 4,
        cofactor_terms: 4,
        max_exponent: 3,
    },
    Shape {
        name: "deep",
        shared_terms: 5,
        cofactor_terms: 5,
        max_exponent: 4,
    },
];

/// A random polynomial with `terms` terms and exponents up to `max_exponent`.
fn random_poly<const N: usize, F: FiniteField>(
    terms: usize,
    max_exponent: u32,
    rng: &mut StdRng,
) -> MultivariatePolynomial<N, F> {
    let mut collected: Vec<(Monomial<N>, F)> = Vec::with_capacity(terms);
    for _ in 0..terms {
        let mut exponents = [0u32; N];
        for exponent in exponents.iter_mut() {
            *exponent = rng.gen_range(0..=max_exponent);
        }
        collected.push((Monomial::new(&exponents), F::random(rng)));
    }
    MultivariatePolynomial::new(&collected)
}

/// `(f, g)` sharing a planted factor, or `None` if the draw degenerated.
fn planted<const N: usize, F: FiniteField>(
    shape: Shape,
    rng: &mut StdRng,
) -> Option<(MultivariatePolynomial<N, F>, MultivariatePolynomial<N, F>)> {
    let shared = random_poly::<N, F>(shape.shared_terms, shape.max_exponent, rng);
    let left = random_poly::<N, F>(shape.cofactor_terms, shape.max_exponent, rng);
    let right = random_poly::<N, F>(shape.cofactor_terms, shape.max_exponent, rng);
    if shared.is_zero() || left.is_zero() || right.is_zero() || shared.is_constant() {
        return None;
    }
    Some((&shared * &left, &shared * &right))
}

fn bench_field<const N: usize, F: KnownOrder>(criterion: &mut Criterion, field: &str) {
    let mut rng = StdRng::seed_from_u64(SEED ^ N as u64);
    let mut group = criterion.benchmark_group("multivariate_gcd");

    for shape in SHAPES {
        let Some((f, g)) = planted::<N, F>(shape, &mut rng) else {
            continue;
        };
        let case = format!("{field}/{N}vars/{}", shape.name);

        for route in [GcdRoute::PrimitivePrs, GcdRoute::SubresultantPrs] {
            let label = if route == GcdRoute::PrimitivePrs {
                "primitive"
            } else {
                "subresultant"
            };
            group.bench_with_input(BenchmarkId::new(label, &case), &(&f, &g), |b, (f, g)| {
                b.iter(|| black_box(f.gcd_by(g, route)))
            });
        }

        // Probed outside the timed region: an arm criterion cannot be told to skip has to be one
        // that is never added. See the module header.
        if f.try_gcd_by(&g, GcdRoute::Brown).is_ok() {
            group.bench_with_input(BenchmarkId::new("brown", &case), &(&f, &g), |b, (f, g)| {
                b.iter(|| black_box(f.try_gcd_by(g, GcdRoute::Brown)))
            });
        }
    }
    group.finish();
}

fn routes(criterion: &mut Criterion) {
    // Two arities, because the arity is what drives the content recursion's depth and so is the
    // axis the two sequences diverge along; and three fields, because the coefficient growth the
    // subresultant route pays for is paid in the element's width.
    bench_field::<2, KoalaBear>(criterion, "koalabear");
    bench_field::<3, KoalaBear>(criterion, "koalabear");
    bench_field::<2, Goldilocks>(criterion, "goldilocks");
    bench_field::<3, Goldilocks>(criterion, "goldilocks");
    bench_field::<2, Bn254Fr>(criterion, "bn254");
}

criterion_group!(multivariate_gcd, routes);
criterion_main!(multivariate_gcd);
