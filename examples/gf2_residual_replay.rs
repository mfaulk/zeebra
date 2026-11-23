//! #1077 / #1092: the packed `GF(2)` route's residual-width reducer sweep (the default since
//! #1092) against the full-width sweep it replaced, as whole solves in fresh processes.
//!
//! `one <set> <instance> <arm> [workers]` is one solve in a fresh process, for the bench host's
//! interleaved runs (`research/gf2-residual/fresh.sh`). Arms, named as #1077 measured them:
//! `packed` (`Gf2Elimination::FullWidth`), `eager` (`Packed`, the residual sweep on every eligible
//! batch), `auto` (`AutoFullWidth`, the default before #1092) and `auto-eager` (`Auto`, the default
//! now). It prints wall and elimination time and the process's peak RSS (`VmHWM`), then re-solves
//! under `packed` and asserts the basis equal. `workers` above one enables `ParallelForward::Auto`.
//! `list <set>` prints the instance names of `dev`, `heldout` or `big` (n = 16 square and n = 17
//! square MQ, seed 1077, a held-out set named before it was measured).
//!
//! #1077's per-batch and in-process replays (`batches`, `solve`), which also compared building
//! only the reachable tails, ran at `7f223df4` and are reproducible there; that arm no longer
//! exists. On the bench host:
//!
//! ```text
//! cargo build --release --example gf2_residual_replay
//! tools/benchlock.sh 1092 research/gf2-residual/fresh.sh <binary> <out.tsv> 5 1 5 dev heldout big
//! ```

use std::time::{Duration, Instant};

use rand::{rngs::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::Zp2,
    grobner::{
        benchmark_systems::cyclic,
        f4::{f4_with_options, F4Options, Gf2Elimination, ParallelForward},
        field_equations::with_field_equations,
    },
    Monomial, MonomialOrder, MultivariatePolynomial, One, Zero,
};

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// #272's construction, as `examples/gf2_f4_dispatch.rs`.
fn random_mq<const N: usize>(
    seed: u64,
    equations: usize,
    density: f64,
) -> Vec<MultivariatePolynomial<N, Zp2>> {
    let mut rng = StdRng::seed_from_u64(seed);
    let plant: [Zp2; N] = std::array::from_fn(|_| {
        if rng.gen_bool(0.5) {
            Zp2::one()
        } else {
            Zp2::zero()
        }
    });
    let system: Vec<_> = (0..equations)
        .map(|_| {
            let mut terms = Vec::new();
            for i in 0..N {
                for j in i..N {
                    if rng.gen_bool(density) {
                        let mut exponents = [0u32; N];
                        exponents[i] += 1;
                        exponents[j] += 1;
                        terms.push((Monomial::new(&exponents), Zp2::one()));
                    }
                }
            }
            let mut polynomial = MultivariatePolynomial::new(&terms);
            let value = polynomial.eval(&plant);
            polynomial += MultivariatePolynomial::new(&[(Monomial::one(), Zp2::zero() - value)]);
            polynomial
        })
        .collect();
    with_field_equations(&system).expect("GF(2) has an order")
}

fn arm(name: &str) -> F4Options {
    let gf2_elimination = match name {
        "packed" => Gf2Elimination::FullWidth,
        "eager" => Gf2Elimination::Packed,
        "auto" => Gf2Elimination::AutoFullWidth,
        "auto-eager" => Gf2Elimination::Auto,
        other => panic!("unknown arm {other}"),
    };
    F4Options {
        measure_stages: true,
        gf2_elimination,
        ..F4Options::default()
    }
}

/// The process's peak resident set, in KiB.
fn peak_rss_kib() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|status| {
            status
                .lines()
                .find_map(|line| line.strip_prefix("VmHWM:"))
                .and_then(|value| value.trim().trim_end_matches("kB").trim().parse().ok())
        })
        .unwrap_or(0)
}

/// Which instance, arm and worker count `one` runs.
struct OneSolve {
    instance: String,
    arm: String,
    workers: usize,
}

fn one<const N: usize>(label: &str, system: &[MultivariatePolynomial<N, Zp2>], target: &OneSolve) {
    if label != target.instance {
        return;
    }
    let parallel_forward = if target.workers > 1 {
        ParallelForward::Auto {
            max_workers: target.workers,
        }
    } else {
        ParallelForward::Serial
    };
    let options = F4Options {
        parallel_forward,
        ..arm(&target.arm)
    };
    let start = Instant::now();
    let (basis, statistics) = f4_with_options(system, ORDER, &options).expect("instance solves");
    let elapsed = start.elapsed();
    let rss = peak_rss_kib();
    let (expected, _) = f4_with_options(system, ORDER, &arm("packed")).expect("instance solves");
    assert_eq!(basis, expected, "{label} {}", target.arm);
    let ms = |d: Duration| format!("{:.2}", d.as_secs_f64() * 1e3);
    println!(
        "{label}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{rss}",
        target.arm,
        target.workers,
        basis.len(),
        ms(elapsed),
        ms(statistics.stages.elimination),
        statistics.batches,
        statistics.packed_gf2.batches,
        statistics.packed_gf2.residual.batches,
    );
}

fn list<const N: usize>(label: &str, _: &[MultivariatePolynomial<N, Zp2>], _: &()) {
    println!("{label}");
}

/// Development: #777's instances (seed 272) and #794's grid at n = 12..14 (seed 794).
macro_rules! dev {
    ($run:ident, $reps:expr) => {{
        $run::<10>("mq-10", &random_mq::<10>(272, 10, 0.3), $reps);
        $run::<12>("mq-12", &random_mq::<12>(272, 12, 0.3), $reps);
        $run::<13>("mq-13", &random_mq::<13>(272, 13, 0.3), $reps);
        $run::<14>(
            "overdetermined-mq-14",
            &random_mq::<14>(272, 28, 0.3),
            $reps,
        );
        $run::<16>(
            "overdetermined-mq-16",
            &random_mq::<16>(272, 32, 0.3),
            $reps,
        );
        $run::<12>("sparse-mq-12", &random_mq::<12>(272, 12, 0.05), $reps);
        $run::<8>(
            "cyclic-8",
            &with_field_equations(&cyclic::<8, Zp2>()).expect("GF(2) has an order"),
            $reps,
        );
        $run::<9>(
            "cyclic-9",
            &with_field_equations(&cyclic::<9, Zp2>()).expect("GF(2) has an order"),
            $reps,
        );
        grid!($run, $reps, 794, 12, 13, 14);
    }};
}

/// Held out, named before any measurement: #794's grid at n = 15, on a fresh seed, 1077.
macro_rules! heldout {
    ($run:ident, $reps:expr) => {{
        grid!($run, $reps, 1077, 15);
    }};
}

/// Held out for the bench host, named before any measurement: square MQ at n = 16 over #794's
/// densities and at n = 17 at two of them, seed 1077.
macro_rules! big {
    ($run:ident, $reps:expr) => {{
        for density in [0.05, 0.1, 0.15, 0.2, 0.3] {
            let label = format!("mq-16-d{density:.2}-s1077");
            $run::<16>(&label, &random_mq::<16>(1077, 16, density), $reps);
        }
        for density in [0.1, 0.3] {
            let label = format!("mq-17-d{density:.2}-s1077");
            $run::<17>(&label, &random_mq::<17>(1077, 17, density), $reps);
        }
    }};
}

macro_rules! grid {
    ($run:ident, $reps:expr, $seed:expr, $($n:literal),+) => {{
        $(
            for density in [0.05, 0.1, 0.15, 0.2, 0.3] {
                for (shape, equations) in [("mq", $n), ("overdetermined-mq", 2 * $n)] {
                    let label = format!("{shape}-{}-d{density:.2}-s{}", $n, $seed);
                    $run::<$n>(&label, &random_mq::<$n>($seed, equations, density), $reps);
                }
            }
        )+
    }};
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let set = args.get(1).map(String::as_str);
    match (args.first().map(String::as_str), set) {
        (Some(mode @ ("one" | "list")), Some(set)) => {
            let target = OneSolve {
                instance: args.get(2).cloned().unwrap_or_default(),
                arm: args.get(3).cloned().unwrap_or_else(|| "auto-eager".into()),
                workers: args
                    .get(4)
                    .map_or(1, |w| w.parse().expect("a worker count")),
            };
            match (mode, set) {
                ("list", "dev") => dev!(list, &()),
                ("list", "heldout") => heldout!(list, &()),
                ("list", "big") => big!(list, &()),
                ("one", "dev") => dev!(one, &target),
                ("one", "heldout") => heldout!(one, &target),
                ("one", "big") => big!(one, &target),
                _ => {
                    eprintln!("unknown set {set}");
                    std::process::exit(64);
                }
            }
        }
        _ => {
            eprintln!(
                "usage: gf2_residual_replay list <dev|heldout|big>\n       \
                 gf2_residual_replay one <dev|heldout|big> <instance> <arm> [workers]"
            );
            std::process::exit(64);
        }
    }
}
