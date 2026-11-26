//! Eager, lazy and gcd-first root extraction in first-point solving (#1166).
//!
//! Two tables. The first isolates root extraction on one univariate polynomial: every root by
//! `roots`, against the first root and every root from a `RootStream`. The second runs the
//! back-substitution half of `solve_one` from a lexicographic basis already in hand, under each
//! `RootExtraction`, so the basis computation's cost does not hide the difference. Its last column
//! is that basis computation's time, for scale.
//!
//! Development figures: unpinned, one machine, median of the repetitions. They say where the
//! stream helps and where it does not, not by how much a deciding measurement would find.
//!
//! ```text
//! cargo run --release --example lazy_roots_ablation
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::{Bn254Fr, Zp2147483647},
    grobner::{
        benchmark_systems::{katsura, planted},
        f4, solve_from_lex_basis, RootExtraction, SolveOptions, SolveStatistics,
    },
    roots, FiniteField, KnownOrder, Monomial, MonomialOrder, MultivariatePolynomial, Polynomial,
    RootStream, UnivariatePolynomial,
};

const REPETITIONS: usize = 7;

fn median(mut samples: Vec<Duration>) -> f64 {
    samples.sort();
    samples[samples.len() / 2].as_secs_f64() * 1e3
}

/// The median time of `REPETITIONS` runs of `f`, each with the same seed.
fn time<T>(mut f: impl FnMut(&mut StdRng) -> T) -> (f64, T) {
    let mut samples = Vec::new();
    let mut last = None;
    for _ in 0..REPETITIONS {
        let mut rng = StdRng::seed_from_u64(1166);
        let at = Instant::now();
        last = Some(f(&mut rng));
        samples.push(at.elapsed());
    }
    (median(samples), last.expect("at least one repetition"))
}

/// `D` random roots, times a random polynomial of degree `D` that mostly has roots only in
/// extensions, so the linear part is a strict factor as it usually is.
fn univariate<F: FiniteField>(degree: usize, seed: u64) -> UnivariatePolynomial<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut f = UnivariatePolynomial::new(&[F::one()]);
    for _ in 0..degree {
        f = &f * &UnivariatePolynomial::new(&[F::zero() - F::random(&mut rng), F::one()]);
    }
    let mut noise: Vec<F> = (0..degree).map(|_| F::random(&mut rng)).collect();
    noise.push(F::one());
    &f * &UnivariatePolynomial::new(&noise)
}

fn root_row<F: KnownOrder>(field: &str, degree: usize) {
    let f = univariate::<F>(degree, degree as u64);
    let (eager, all) = time(|rng| roots(&f, rng));
    let (first, first_counters) = time(|rng| {
        let mut stream = RootStream::new(&f).expect("nonzero");
        stream.next_root(rng).expect("default bound");
        stream.counters()
    });
    let (drain, drain_counters) = time(|rng| {
        let mut stream = RootStream::new(&f).expect("nonzero");
        while stream.next_root(rng).expect("default bound").is_some() {}
        stream.counters()
    });
    println!(
        "| {field} | {} | {} | {eager:.2} | {first:.2} | {drain:.2} | {} / {} | {} / {} |",
        f.degree(),
        all.len(),
        first_counters.splits,
        drain_counters.splits,
        first_counters.pow_mods,
        drain_counters.pow_mods,
    );
}

/// `x - y - c` or `x^2 - y`, with `y` constrained to `D` random values.
///
/// With `one_square`, every value but one is `7 s^2`, a non-square whenever 7 is (it is a
/// primitive root mod 2^31 - 1), so under `x^2 - y` all branches but one die.
fn two_variable<F: FiniteField>(
    degree: usize,
    square: bool,
    one_square: bool,
) -> Vec<MultivariatePolynomial<2, F>> {
    let mut rng = StdRng::seed_from_u64(degree as u64 + 7);
    let names = ["x", "y"];
    let seven = F::from_str("7").expect("7");
    let mut eliminant = MultivariatePolynomial::<2, F>::parse("1", names).expect("constant");
    for i in 0..degree {
        let s = F::random(&mut rng);
        let value = match (one_square, i) {
            (false, _) => s,
            (true, 0) => s * s,
            (true, _) => seven * s * s,
        };
        let linear = MultivariatePolynomial::new(&[
            (Monomial::new(&[0, 1]), F::one()),
            (Monomial::one(), F::zero() - value),
        ]);
        eliminant = &eliminant * &linear;
    }
    let top = if square { "x^2 - y" } else { "x - y - 1" };
    vec![
        MultivariatePolynomial::parse(top, names).expect("valid"),
        eliminant,
    ]
}

fn search_row<const N: usize, F: KnownOrder>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    basis: Option<Vec<MultivariatePolynomial<N, F>>>,
) {
    let (basis_ms, basis) = match basis {
        Some(b) => (None, b),
        None => {
            let (ms, b) = time(|_| f4(system, MonomialOrder::Lexicographic).expect("lex basis"));
            (Some(ms), b)
        }
    };
    let mut cells = Vec::new();
    let mut counters: Vec<SolveStatistics> = Vec::new();
    for route in [
        RootExtraction::Eager,
        RootExtraction::Lazy,
        RootExtraction::GcdFirst,
    ] {
        let options = SolveOptions {
            root_extraction: route,
            ..SolveOptions::default()
        };
        let (ms, (outcome, statistics)) =
            time(|rng| solve_from_lex_basis(&basis, system, &options, rng).expect("within limits"));
        assert!(outcome.point().is_some(), "{name} has a point");
        cells.push(format!("{ms:.2}"));
        counters.push(statistics);
    }
    let lazy = &counters[1].roots;
    println!(
        "| {name} | {} | {} | {} / {} | {} | {} | {} |",
        cells.join(" | "),
        counters[1].branches,
        lazy.splits,
        lazy.roots_available,
        counters[1].roots.pow_mods,
        counters[2].roots.pow_mods,
        basis_ms.map_or("—".to_string(), |ms| format!("{ms:.2}")),
    );
}

fn main() {
    println!("## Root extraction on one polynomial (ms)\n");
    println!(
        "| field | deg f | roots | eager `roots` | stream: first | stream: all | splits first / all \
         | pow_mods first / all |"
    );
    println!("|---|---|---|---|---|---|---|---|");
    for degree in [16, 64, 256] {
        root_row::<Zp2147483647>("GF(2^31 - 1)", degree);
    }
    for degree in [16, 64] {
        root_row::<Bn254Fr>("BN254 Fr", degree);
    }

    println!("\n## Back-substitution from a lex basis, first point (ms)\n");
    println!(
        "| system | eager | lazy | gcd-first | branches (lazy) | splits / roots available (lazy) \
         | pow_mods lazy | pow_mods gcd-first | lex basis |"
    );
    println!("|---|---|---|---|---|---|---|---|---|");
    type F = Zp2147483647;
    for degree in [16, 64, 256] {
        let s = two_variable::<F>(degree, false, false);
        search_row(&format!("x = y + 1, D = {degree}"), &s, Some(s.clone()));
        let s = two_variable::<F>(degree, true, false);
        search_row(&format!("x^2 = y, D = {degree}"), &s, Some(s.clone()));
        let s = two_variable::<F>(degree, true, true);
        search_row(
            &format!("x^2 = y, one square of D = {degree}"),
            &s,
            Some(s.clone()),
        );
    }
    let s = two_variable::<Bn254Fr>(64, true, false);
    search_row("x^2 = y, D = 64, BN254", &s, Some(s.clone()));

    // Generated systems with fresh points, not corpus rows: one base-field root per level is the
    // unfavourable case, where there is no other root to skip.
    let point: Vec<F> = (0..6).map(|i| F::new(1_000_003 * i as u64 + 11)).collect();
    search_row("planted-6 (fresh point)", &planted::<6, F>(&point), None);
    search_row("katsura-5", &katsura::<5, F>(), None);
    search_row("katsura-6", &katsura::<6, F>(), None);
}
