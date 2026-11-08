//! #318/#319: one order-162 determinant, timed identically at two commits and three widths.
//!
//! ```text
//! cargo run --release --example determinant_era                          # the row, 1/8/32 workers
//! cargo run --release --example determinant_era -- --workers 1,8,32
//! cargo run --release --example determinant_era -- --determinants 13123  # §6.6's batch length
//! cargo run --release --example determinant_era -- --per-worker 16       # batch scaled to width
//! cargo run --release --example determinant_era -- --row poseidon31-cico-t16-rf2-rp0
//! ```
//!
//! # Why this is not `determinant_sweep` or `resultant_cico`
//!
//! #318 asks whether a figure on record from one commit reproduces at another, which needs the
//! *same* instrument compiled against *both* libraries. `determinant_sweep` cannot do it: it did
//! not exist at the commit §6.5's figure came from, and neither did the `time_sylvester_determinants`
//! and `DeterminantKernel` it is written against. `resultant_cico` existed but its flags, its
//! sample count and its default route all changed in between, so the two ends of the comparison
//! would not be running the same measurement.
//!
//! This file is written against the narrowest API that is **byte-identical across the range** —
//! `challenge`, `Specialization`, `cico_bivariate`, `sylvester_determinant_at` — so the source can
//! be dropped into a worktree at either end and only the library beneath it differs. That is the
//! whole design constraint, and it is why the determinant is taken through
//! `sylvester_determinant_at` rather than through the batched `sample_determinants` the routes use:
//! the batched entry point is not in the old library's surface. The per-call price is one
//! `coefficients_in` extraction, about 3 400 term reads against the LU's `162³/3 ≈ 1.4 × 10⁶`
//! multiply-subtracts — under 0.3%, and paid identically on both sides, so it cannot bias a ratio.
//!
//! # Why the row and not a synthetic pair
//!
//! §6.5's 2.868 ms and §6.6's 3.007 ms are both from the **registered** `rf2-rp2` slice at seed 1.
//! §6.9's 3.624 ms is from a synthetic pair of the same matrix order. #318 holds that the gap
//! between them is an era and not a difference of subject; this example keeps the subject fixed at
//! the registered row so that era is the only thing left varying.
//!
//! # Why the batch length is a flag
//!
//! §6.6 spread 13 123 determinants over its workers — 410 each at 32 — and §6.9's sweep spread 500,
//! which is 16 each. Those are two batch lengths as well as two eras, and a width penalty read off
//! a 58 ms burst is not the same measurement as one read off a 1.3 s run: the clock a short burst
//! sees is not the one a sustained row settles at. `--determinants` fixes the batch length across
//! widths and `--per-worker` fixes the work each worker does, so the two can be separated.

use std::time::{Duration, Instant};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::research::{
        challenge, cico_bivariate, sylvester_determinant_at, Specialization, KOALABEAR_PRIME,
    },
    FiniteField, MultivariatePolynomial,
};

type K = PrimeFieldElement64<KOALABEAR_PRIME>;

/// The registered row every figure in dispute was taken on.
const DEFAULT_ROW: &str = "poseidon31-cico-t16-rf2-rp2";

/// The value of a `--flag <value>` argument, if it was given and parses.
fn flag(name: &str) -> Option<String> {
    let args: Vec<String> = std::env::args().collect();
    let at = args.iter().position(|a| a == name)?;
    args.get(at + 1).cloned()
}

/// A `--flag a,b,c` list of counts, or `fallback`.
fn counts(name: &str, fallback: &[usize]) -> Vec<usize> {
    match flag(name) {
        Some(value) => value
            .split(',')
            .map(|part| part.trim().parse().expect("a worker count"))
            .collect(),
        None => fallback.to_vec(),
    }
}

/// `at.len()` determinants over `workers` threads, chunked exactly as `sample_determinants` is.
///
/// The chunking is reproduced rather than called because the library entry point that does it is
/// not in the old commit's surface. `div_ceil` so the blocks cover the range: a short tail means
/// fewer threads than asked for, never more.
fn time_batch(
    f: &MultivariatePolynomial<2, K>,
    g: &MultivariatePolynomial<2, K>,
    at: &[K],
    workers: usize,
) -> (Duration, Vec<K>) {
    // Seeded from the abscissae rather than from `K::zero()`: `Zero` and `FiniteField` both
    // provide `zero` and which one is in scope changed across the commit range this file has to
    // compile at both ends of. Every slot is overwritten before it is read.
    let mut values = at.to_vec();
    let started = Instant::now();
    if workers <= 1 {
        for (slot, x) in values.iter_mut().zip(at) {
            *slot = sylvester_determinant_at(f, g, 1, *x).expect("both involve the second");
        }
    } else {
        let block = at.len().div_ceil(workers).max(1);
        std::thread::scope(|scope| {
            for (chunk, abscissae) in values.chunks_mut(block).zip(at.chunks(block)) {
                scope.spawn(move || {
                    for (slot, x) in chunk.iter_mut().zip(abscissae) {
                        *slot =
                            sylvester_determinant_at(f, g, 1, *x).expect("both involve the second");
                    }
                });
            }
        });
    }
    (started.elapsed(), values)
}

fn main() {
    let row = flag("--row").unwrap_or_else(|| DEFAULT_ROW.to_string());
    let widths = counts("--workers", &[1, 8, 32]);
    let repeats = counts("--repeats", &[3])[0].max(1);
    let per_worker = flag("--per-worker").map(|v| v.parse::<usize>().expect("a count"));
    let fixed_batch = flag("--determinants").map(|v| v.parse::<usize>().expect("a count"));

    let manifest = challenge(&row).expect("a registered challenge id");
    let instance = manifest.cico_instance::<K>().expect("a registered problem");
    let free = instance.free_inputs();
    let variables: Vec<usize> = (2..free).collect();
    let specialization = Specialization::<46, K>::seeded(&variables, 1).expect("distinct indices");
    let slice: Vec<K> = (2..free)
        .map(|i| specialization.value_of(i).expect("fixed"))
        .collect();

    let built = Instant::now();
    let outputs = cico_bivariate(&instance, &slice).expect("two free inputs remain");
    let build_ms = built.elapsed().as_secs_f64() * 1e3;
    let (f, g) = (&outputs[0], &outputs[1]);
    // The Sylvester order is `deg_y(f) + deg_y(g)`, and on a CICO bivariate the degree in either
    // variable equals the total degree — both outputs are `3^rounds` in each — so the total
    // degrees are what it is read off. Done this way rather than by walking the exponent vectors
    // because `Monomial`'s accessors are not the same at both ends of the commit range.
    let order = f.degree() + g.degree();

    println!("# determinant era, #318/#319");
    println!();
    println!(
        "row {row}, seed 1, {} fixed inputs, bivariates of degree {} and {} built in {build_ms:.1} ms",
        slice.len(),
        f.degree(),
        g.degree()
    );
    println!("Sylvester order {order}, dense Crout LU, {repeats} draws a point");
    println!();
    println!("| workers | determinants | per worker | wall | wall/det | core/det |");
    println!("|---:|---:|---:|---:|---:|---:|");

    for workers in &widths {
        let workers = (*workers).max(1);
        let batch = match (fixed_batch, per_worker) {
            (Some(n), _) => n.max(workers),
            (None, Some(n)) => n * workers,
            (None, None) => 500usize.max(workers),
        };
        let at: Vec<K> = (0..batch).map(|i| K::new(i as u64 + 7)).collect();

        let mut walls = Vec::new();
        let mut first: Option<Vec<K>> = None;
        for _ in 0..repeats {
            let (elapsed, values) = time_batch(f, g, &at, workers);
            match &first {
                None => first = Some(values),
                Some(reference) => assert_eq!(
                    reference, &values,
                    "the determinants disagree between draws at {workers} workers"
                ),
            }
            walls.push(elapsed.as_secs_f64());
        }
        // The fastest draw, not the mean: a slower draw on a contended box is contention, and the
        // quantity wanted is what the kernel costs when nothing else is resident.
        let wall = walls.iter().copied().fold(f64::INFINITY, f64::min);
        let per_det = wall / batch as f64;
        println!(
            "| {workers} | {batch} | {} | {:.3} s | {:.4} ms | {:.4} ms |",
            batch.div_ceil(workers),
            wall,
            per_det * 1e3,
            per_det * workers as f64 * 1e3
        );
    }

    println!();
    println!(
        "walls are the fastest of {repeats} draws; core/det is wall x workers / determinants, \
         which is the figure that extrapolates"
    );
}
