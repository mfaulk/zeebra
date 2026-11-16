//! #777: F4 with bit-packed `GF(2)` elimination against the generic route, measured as solves.
//!
//! `batches` replays every batch of each instance under `Gf2Elimination::Generic` and
//! `Gf2Elimination::Packed` and prints one row per batch — shape, density, and each route's
//! elimination stage — which is what the `Auto` threshold is read from. `sweep` does the same over
//! #794's grid of MQ sizes and densities. `solve` times whole F4 runs
//! under `Generic`, `Auto` and `Packed`. Every arm's candidates (per batch) or basis (per solve) is
//! asserted equal to the generic route's before its time is kept.
//!
//! Arms are interleaved with a rotating order and the minimum over repetitions is kept; run pinned
//! and under `tools/benchlock.sh`:
//!
//! ```text
//! taskset -c 5 tools/benchlock.sh 777 target/release/examples/gf2_f4_dispatch batches 5
//! taskset -c 5 tools/benchlock.sh 777 target/release/examples/gf2_f4_dispatch solve 7
//! taskset -c 5 tools/benchlock.sh 794 target/release/examples/gf2_f4_dispatch sweep 5
//! ```

use std::time::{Duration, Instant};

use rand::{rngs::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::Zp2,
    grobner::{
        benchmark_systems::cyclic,
        f4::{f4_with_options, reduce_batch, trace_batches, F4Options, Gf2Elimination},
        field_equations::with_field_equations,
    },
    Monomial, MonomialOrder, MultivariatePolynomial, One, Zero,
};

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// #272's construction: `equations` random quadratics in `N` variables, each quadratic monomial
/// present with probability `density`, with a planted root, then the field equations.
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

fn options(gf2_elimination: Gf2Elimination) -> F4Options {
    F4Options {
        gf2_elimination,
        measure_stages: true,
        ..F4Options::default()
    }
}

fn micros(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e6
}

fn batches<const N: usize>(label: &str, system: &[MultivariatePolynomial<N, Zp2>], reps: usize) {
    let (_, _, trace) =
        trace_batches(system, ORDER, &options(Gf2Elimination::Generic)).expect("instance solves");
    let arms = [Gf2Elimination::Generic, Gf2Elimination::Packed];
    for (index, batch) in trace.batches().iter().enumerate() {
        let expected = reduce_batch(&batch.basis, &batch.pairs, ORDER, &options(arms[0]))
            .expect("batch reduces");
        let mut best = [Duration::MAX; 2];
        for rep in 0..reps {
            for offset in 0..arms.len() {
                let slot = (rep + offset) % arms.len();
                let outcome = reduce_batch(&batch.basis, &batch.pairs, ORDER, &options(arms[slot]))
                    .expect("batch reduces");
                assert_eq!(
                    outcome.candidates, expected.candidates,
                    "{label} batch {index}"
                );
                best[slot] = best[slot].min(outcome.statistics.stages.elimination);
            }
        }
        let s = &expected.statistics;
        let cells = (s.rows * s.columns).max(1);
        let nonzeros = s.elimination.initial_nonzeros;
        println!(
            "| {label} | {index} | {} | {} | {} | {} | {} | {:.0} | {:.1} | {:.1} | {:.2}x | {} |",
            s.rows,
            s.reducer_rows,
            s.rows - s.reducer_rows,
            s.columns,
            nonzeros,
            nonzeros as f64 * 1e6 / cells as f64,
            micros(best[0]),
            micros(best[1]),
            best[0].as_secs_f64() / best[1].as_secs_f64().max(1e-9),
            if Gf2Elimination::prefers_packed(s.rows, s.rows - s.reducer_rows, s.columns, nonzeros)
            {
                "packed"
            } else {
                "generic"
            },
        );
    }
}

fn solve<const N: usize>(label: &str, system: &[MultivariatePolynomial<N, Zp2>], reps: usize) {
    let arms = [
        Gf2Elimination::Generic,
        Gf2Elimination::Auto,
        Gf2Elimination::Packed,
    ];
    let (expected, _) = f4_with_options(system, ORDER, &options(arms[0])).expect("instance solves");
    let mut best = [Duration::MAX; 3];
    let mut elimination = [Duration::MAX; 3];
    let mut packed_batches = [0; 3];
    let mut total_batches = 0;
    for rep in 0..reps {
        for offset in 0..arms.len() {
            let slot = (rep + offset) % arms.len();
            let start = Instant::now();
            let (basis, statistics) =
                f4_with_options(system, ORDER, &options(arms[slot])).expect("instance solves");
            let elapsed = start.elapsed();
            assert_eq!(basis, expected, "{label} {:?}", arms[slot]);
            best[slot] = best[slot].min(elapsed);
            elimination[slot] = elimination[slot].min(statistics.stages.elimination);
            packed_batches[slot] = statistics.packed_gf2.batches;
            total_batches = statistics.batches;
        }
    }
    let ms = |d: Duration| d.as_secs_f64() * 1e3;
    println!(
        "| {label} | {} | {total_batches} | {:.2} | {:.2} | {:.2} | {} | {:.2} | {:.2} | {:.2} | **{:.2}x** | {:.2}x |",
        expected.len(),
        ms(best[0]),
        ms(elimination[0]),
        ms(best[1]),
        packed_batches[1],
        ms(elimination[1]),
        ms(best[2]),
        ms(elimination[2]),
        best[0].as_secs_f64() / best[1].as_secs_f64(),
        best[0].as_secs_f64() / best[2].as_secs_f64(),
    );
}

macro_rules! each_instance {
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
    }};
}

/// #794: random MQ over a grid of size and quadratic-monomial density, on a seed the shipped rule
/// was not read from, so the threshold is tested on batches it has not seen.
macro_rules! sweep_instances {
    ($run:ident, $reps:expr, $($n:literal),+) => {{
        $(
            for density in [0.05, 0.1, 0.15, 0.2, 0.3] {
                for (shape, equations) in [("mq", $n), ("overdetermined-mq", 2 * $n)] {
                    let label = format!("{shape}-{}-d{density:.2}", $n);
                    $run::<$n>(&label, &random_mq::<$n>(794, equations, density), $reps);
                }
            }
        )+
    }};
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let reps = args
        .get(1)
        .map_or(5, |r| r.parse().expect("a repetition count"));
    match args.first().map(String::as_str) {
        Some("batches") => {
            println!("| instance | batch | rows | reducer rows | pair rows | columns | entries | density ppm | generic us | packed us | generic/packed | auto picks |");
            println!("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |");
            each_instance!(batches, reps);
        }
        Some("sweep") => {
            println!("| instance | batch | rows | reducer rows | pair rows | columns | entries | density ppm | generic us | packed us | generic/packed | auto picks |");
            println!("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |");
            sweep_instances!(batches, reps, 12, 13, 14, 15, 16);
        }
        Some("solve") => {
            println!("| instance | basis | batches | generic ms | generic elim ms | auto ms | auto packed batches | auto elim ms | packed ms | packed elim ms | generic/auto | generic/packed |");
            println!("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |");
            each_instance!(solve, reps);
        }
        _ => {
            eprintln!("usage: gf2_f4_dispatch <batches|sweep|solve> [reps]");
            std::process::exit(64);
        }
    }
}
