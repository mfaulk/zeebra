//! #606: what a `KnownOrder` transform buys the subproduct tree, measured before it is specialized.
//!
//! Three arms per size, in one binary, interleaved and checked equal before the clock starts:
//!
//! - `shipped` — `subproduct_interpolate_unstable`, the Karatsuba tree `lagrange_interpolate`
//!   dispatches to;
//! - `control` — the research `TransformTree` with a kernel whose threshold is `usize::MAX`, so
//!   every product and remainder takes the shipped Karatsuba / long-division / Newton route. It is
//!   the same tree code as the transform arm, so the transform arm's ratio is read against this
//!   and not against `shipped`, whose data layout differs;
//! - `t=<d>` — the same tree with every product of degree at least `d` through the transform,
//!   kernel construction (root sampling and every twiddle table) included in the timing.
//!
//! Then a stage breakdown — build, `M'` down the tree, combine — for `control` and the fastest
//! threshold, because a whole-route ratio does not say where the gain or loss sits.
//!
//! ```text
//! cargo run --release --example transform_tree_ab -- all
//! cargo run --release --example transform_tree_ab -- koalabear sizes=13123,16384 thresholds=256,1024
//! ```

use std::time::{Duration, Instant};

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, KoalaBear, PrimeFieldElement64},
    subproduct_interpolate_unstable, transform_tree_interpolate_unstable, KnownOrder,
    TransformKernel, TransformTree, UnivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18_446_744_069_414_584_321>;

fn points<F: KnownOrder>(n: usize, seed: u64) -> Vec<(F, F)> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut seen = std::collections::HashSet::new();
    let mut out = Vec::with_capacity(n);
    while out.len() < n {
        let x = F::random(&mut rng);
        if seen.insert(x) {
            out.push((x, F::random(&mut rng)));
        }
    }
    out
}

/// One whole interpolation through the research tree, kernel construction included.
fn research<F: KnownOrder>(
    sample: &[(F, F)],
    threshold: usize,
    rng: &mut StdRng,
) -> UnivariatePolynomial<F> {
    let kernel = TransformKernel::<F>::new(sample.len() + 1, threshold, rng)
        .expect("the field hosts the domain");
    transform_tree_interpolate_unstable(sample, &kernel)
}

/// `[kernel, build, M' down the tree, combine]` for one pass.
fn stages<F: KnownOrder>(sample: &[(F, F)], threshold: usize, rng: &mut StdRng) -> [Duration; 4] {
    let start = Instant::now();
    let kernel = TransformKernel::<F>::new(sample.len() + 1, threshold, rng).expect("domain");
    let setup = start.elapsed();
    let xs: Vec<F> = sample.iter().map(|(x, _)| *x).collect();
    let start = Instant::now();
    let tree = TransformTree::build(&xs, &kernel);
    let build = start.elapsed();
    let start = Instant::now();
    let mut denominators = std::hint::black_box(tree.derivative_values());
    let evaluate = start.elapsed();
    zeebra::fields::batch_invert(&mut denominators);
    let scaled: Vec<F> = sample
        .iter()
        .zip(&denominators)
        .map(|((_, y), d)| *y * *d)
        .collect();
    let start = Instant::now();
    std::hint::black_box(tree.combine(&scaled));
    let combine = start.elapsed();
    [setup, build, evaluate, combine]
}

fn field<F: KnownOrder>(name: &str, sizes: &[usize], thresholds: &[usize], reps: usize) {
    println!("\n## {name} ({} B element)\n", std::mem::size_of::<F>());
    let mut rng = StdRng::seed_from_u64(0x606);
    let mut header = String::from("| n | shipped/s | control/s |");
    let mut rule = String::from("|---:|---:|---:|");
    for t in thresholds {
        header.push_str(&format!(" t={t}/s |"));
        rule.push_str("---:|");
    }
    header.push_str(" best t | control/best |");
    rule.push_str("---:|---:|");
    println!("{header}\n{rule}");

    let mut best_by_size = Vec::new();
    for &n in sizes {
        let sample = points::<F>(n, 0x606 ^ n as u64);
        let expected = subproduct_interpolate_unstable(&sample);
        assert_eq!(
            research(&sample, usize::MAX, &mut rng),
            expected,
            "control, n = {n}"
        );
        for &t in thresholds {
            assert_eq!(research(&sample, t, &mut rng), expected, "t = {t}, n = {n}");
        }

        // Arm 0 shipped, 1 control, 2.. thresholds; the order rotates each repetition so no arm
        // always runs first after the agreement check warmed the caches.
        let arms = 2 + thresholds.len();
        let mut best = vec![Duration::MAX; arms];
        for rep in 0..reps {
            for k in 0..arms {
                let arm = (k + rep) % arms;
                let start = Instant::now();
                match arm {
                    0 => drop(std::hint::black_box(subproduct_interpolate_unstable(
                        &sample,
                    ))),
                    1 => drop(std::hint::black_box(research(
                        &sample,
                        usize::MAX,
                        &mut rng,
                    ))),
                    _ => drop(std::hint::black_box(research(
                        &sample,
                        thresholds[arm - 2],
                        &mut rng,
                    ))),
                }
                best[arm] = best[arm].min(start.elapsed());
            }
        }
        let (fastest, fastest_time) = best[2..]
            .iter()
            .enumerate()
            .min_by_key(|(_, d)| **d)
            .map(|(i, d)| (thresholds[i], *d))
            .expect("at least one threshold");
        let mut row = format!(
            "| {n} | {:.4} | {:.4} |",
            best[0].as_secs_f64(),
            best[1].as_secs_f64()
        );
        for d in &best[2..] {
            row.push_str(&format!(" {:.4} |", d.as_secs_f64()));
        }
        row.push_str(&format!(
            " {fastest} | {:.3} |",
            best[1].as_secs_f64() / fastest_time.as_secs_f64()
        ));
        println!("{row}");
        best_by_size.push((n, sample, fastest));
    }

    println!(
        "\nstages, fastest of {reps} (kernel / build / M' down the tree / combine, seconds):\n"
    );
    println!("| n | arm | kernel | build | M' eval | combine |\n|---:|---|---:|---:|---:|---:|");
    for (n, sample, fastest) in &best_by_size {
        for (label, t) in [
            ("control".to_string(), usize::MAX),
            (format!("t={fastest}"), *fastest),
        ] {
            let mut best = [Duration::MAX; 4];
            for _ in 0..reps {
                for (b, s) in best.iter_mut().zip(stages(sample, t, &mut rng)) {
                    *b = (*b).min(s);
                }
            }
            println!(
                "| {n} | {label} | {:.4} | {:.4} | {:.4} | {:.4} |",
                best[0].as_secs_f64(),
                best[1].as_secs_f64(),
                best[2].as_secs_f64(),
                best[3].as_secs_f64()
            );
        }
    }
}

fn parse_list(value: &str) -> Vec<usize> {
    value
        .split(',')
        .map(|s| s.parse().expect("a comma-separated list of integers"))
        .collect()
}

fn main() {
    let mut which = "all".to_string();
    let mut sizes = vec![4096, 8192, 13_123, 16_384];
    let mut thresholds = vec![64, 128, 256, 512, 1024, 2048, 4096];
    let mut reps = 5;
    for arg in std::env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("sizes=") {
            sizes = parse_list(v);
        } else if let Some(v) = arg.strip_prefix("thresholds=") {
            thresholds = parse_list(v);
        } else if let Some(v) = arg.strip_prefix("reps=") {
            reps = v.parse().expect("reps=<integer>");
        } else {
            which = arg;
        }
    }

    println!("# transform_tree_ab (#606)");
    println!("ISA: {}", zeebra::util::isa_floor());
    println!("sizes {sizes:?}, thresholds (transform at product degree >= t) {thresholds:?}, fastest of {reps}");

    let all = which == "all";
    if all || which == "koalabear" {
        field::<KoalaBear>("KoalaBear", &sizes, &thresholds, reps);
    }
    if all || which == "goldilocks" {
        field::<Goldilocks>("Goldilocks", &sizes, &thresholds, reps);
    }
    if all || which == "bn254" {
        field::<Bn254Fr>("BN254 Fr", &sizes, &thresholds, reps);
    }
}
