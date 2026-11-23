//! #1077: the packed `GF(2)` route on the residual columns only, against the shipped full-width
//! packed route and the Faugère–Lachartre route, replayed batch by batch and as whole solves.
//!
//! `batches <set> [reps]` replays every batch of each instance in `set` (`dev` or `heldout`) under
//! four arms: `packed` (shipped full width), `fl` (Faugère–Lachartre order, generic kernel),
//! `lazy` and `eager` (residual width, tails built on demand or all of them). Every arm's
//! candidates are asserted equal to `packed`'s on every repetition. It prints one tab-separated
//! row per batch: shape, residual width and density, tail counts and fill, `xor` words, bytes,
//! the residual arms' phase times, and each arm's minimum elimination stage over `reps`.
//! `solve <set> [reps]` times whole solves under `packed`, `lazy` and `eager`, bases asserted
//! equal to `packed`'s.
//!
//! Arms are interleaved with a rotating order. Run pinned and under `tools/benchlock.sh` on the
//! bench host:
//!
//! ```text
//! cargo build --release --features research-gf2-residual --example gf2_residual_replay
//! taskset -c 5 tools/benchlock.sh 1077 target/release/examples/gf2_residual_replay batches dev 5
//! ```

use std::time::{Duration, Instant};

use rand::{rngs::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::Zp2,
    grobner::{
        benchmark_systems::cyclic,
        f4::{
            f4_with_options, packed_residual::ResidualTails, reduce_batch, trace_batches,
            BatchOrder, F4Options, Gf2Elimination,
        },
        field_equations::with_field_equations,
    },
    Monomial, MonomialOrder, MultivariatePolynomial, One, Zero,
};

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const ARMS: [&str; 4] = ["packed", "fl", "lazy", "eager"];

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
    let base = F4Options {
        measure_stages: true,
        ..F4Options::default()
    };
    match name {
        "packed" => F4Options {
            gf2_elimination: Gf2Elimination::Packed,
            ..base
        },
        "fl" => F4Options {
            gf2_elimination: Gf2Elimination::Generic,
            batch_order: BatchOrder::FaugereLachartre,
            ..base
        },
        "lazy" => F4Options {
            gf2_elimination: Gf2Elimination::Residual(ResidualTails::Lazy),
            ..base
        },
        "eager" => F4Options {
            gf2_elimination: Gf2Elimination::Residual(ResidualTails::Eager),
            ..base
        },
        _ => unreachable!(),
    }
}

fn us(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e6
}

fn batches<const N: usize>(label: &str, system: &[MultivariatePolynomial<N, Zp2>], reps: usize) {
    let (_, _, trace) = trace_batches(system, ORDER, &arm("packed")).expect("instance solves");
    let options: Vec<F4Options> = ARMS.iter().map(|name| arm(name)).collect();
    for (index, batch) in trace.batches().iter().enumerate() {
        let run = |slot: usize| {
            reduce_batch(&batch.basis, &batch.pairs, ORDER, &options[slot]).expect("batch reduces")
        };
        let expected = run(0);
        let (lazy, eager) = (run(2), run(3));
        let mut best = [Duration::MAX; 4];
        let mut phases = [Duration::MAX; 5];
        for rep in 0..reps {
            for offset in 0..ARMS.len() {
                let slot = (rep + offset) % ARMS.len();
                let outcome = run(slot);
                assert_eq!(
                    outcome.candidates, expected.candidates,
                    "{label} batch {index} {}",
                    ARMS[slot]
                );
                best[slot] = best[slot].min(outcome.statistics.stages.elimination);
                if slot == 2 {
                    let r = &outcome.statistics.packed_gf2.residual;
                    for (p, d) in phases.iter_mut().zip([
                        r.pack,
                        r.tails,
                        r.multiply,
                        r.echelon,
                        r.write_back,
                    ]) {
                        *p = (*p).min(d);
                    }
                }
            }
        }
        let s = &expected.statistics;
        let (l, e) = (
            &lazy.statistics.packed_gf2.residual,
            &eager.statistics.packed_gf2.residual,
        );
        let pair_rows = s.rows - s.reducer_rows;
        let ppm = |entries: usize, cells: usize| entries as f64 * 1e6 / cells.max(1) as f64;
        let fields: Vec<String> = vec![
            label.to_string(),
            index.to_string(),
            s.rows.to_string(),
            s.reducer_rows.to_string(),
            pair_rows.to_string(),
            s.columns.to_string(),
            l.residual_columns.to_string(),
            s.elimination.initial_nonzeros.to_string(),
            format!(
                "{:.0}",
                ppm(s.elimination.initial_nonzeros, s.rows * s.columns)
            ),
            l.known_entries.to_string(),
            l.residual_entries.to_string(),
            format!(
                "{:.0}",
                ppm(l.residual_entries, pair_rows * l.residual_columns)
            ),
            format!(
                "{:.0}",
                ppm(l.reduced_entries, pair_rows * l.residual_columns)
            ),
            l.reducer_residual_entries.to_string(),
            l.referenced_tails.to_string(),
            l.tails_built.to_string(),
            e.tails_built.to_string(),
            l.tail_entries.to_string(),
            e.tail_entries.to_string(),
            l.tail_uses.to_string(),
            s.packed_gf2.xor_words.to_string(),
            lazy.statistics.packed_gf2.xor_words.to_string(),
            eager.statistics.packed_gf2.xor_words.to_string(),
            l.tail_words.to_string(),
            l.multiply_words.to_string(),
            l.echelon_words.to_string(),
            l.tables.to_string(),
            l.table_bytes.to_string(),
            l.tail_bytes.to_string(),
            e.tail_bytes.to_string(),
            s.packed_gf2.workspace_bytes.to_string(),
            l.workspace_bytes.to_string(),
            e.workspace_bytes.to_string(),
        ]
        .into_iter()
        .chain(phases.iter().map(|&d| format!("{:.1}", us(d))))
        .chain(best.iter().map(|&d| format!("{:.1}", us(d))))
        .collect();
        println!("{}", fields.join("\t"));
    }
}

fn solve<const N: usize>(label: &str, system: &[MultivariatePolynomial<N, Zp2>], reps: usize) {
    let names = ["packed", "lazy", "eager"];
    let options: Vec<F4Options> = names.iter().map(|name| arm(name)).collect();
    let (expected, _) = f4_with_options(system, ORDER, &options[0]).expect("instance solves");
    let mut best = [Duration::MAX; 3];
    let mut elimination = [Duration::MAX; 3];
    for rep in 0..reps {
        for offset in 0..names.len() {
            let slot = (rep + offset) % names.len();
            let start = Instant::now();
            let (basis, statistics) =
                f4_with_options(system, ORDER, &options[slot]).expect("instance solves");
            let elapsed = start.elapsed();
            assert_eq!(basis, expected, "{label} {}", names[slot]);
            best[slot] = best[slot].min(elapsed);
            elimination[slot] = elimination[slot].min(statistics.stages.elimination);
        }
    }
    let ms = |d: Duration| format!("{:.2}", d.as_secs_f64() * 1e3);
    let mut fields = vec![label.to_string(), expected.len().to_string()];
    for slot in 0..names.len() {
        fields.push(ms(best[slot]));
        fields.push(ms(elimination[slot]));
    }
    println!("{}", fields.join("\t"));
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

const BATCH_HEADER: &str = "instance\tbatch\trows\treducers\tpair_rows\tcolumns\tresidual_columns\tentries\tdensity_ppm\tC_entries\tD_entries\tD_ppm\treduced_ppm\tB_entries\treferenced_tails\tlazy_tails\teager_tails\tlazy_tail_entries\teager_tail_entries\ttail_uses\tpacked_words\tlazy_words\teager_words\tlazy_tail_words\tlazy_multiply_words\tlazy_echelon_words\tmultiply_tables\ttable_bytes\tlazy_tail_bytes\teager_tail_bytes\tpacked_workspace\tlazy_workspace\teager_workspace\tlazy_pack_us\tlazy_tails_us\tlazy_multiply_us\tlazy_echelon_us\tlazy_write_back_us\tpacked_us\tfl_us\tlazy_us\teager_us";

const SOLVE_HEADER: &str =
    "instance\tbasis\tpacked_ms\tpacked_elim_ms\tlazy_ms\tlazy_elim_ms\teager_ms\teager_elim_ms";

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let reps = args
        .get(2)
        .map_or(5, |r| r.parse().expect("a repetition count"));
    let set = args.get(1).map(String::as_str);
    match (args.first().map(String::as_str), set) {
        (Some("batches"), Some("dev")) => {
            println!("{BATCH_HEADER}");
            dev!(batches, reps);
        }
        (Some("batches"), Some("heldout")) => {
            println!("{BATCH_HEADER}");
            heldout!(batches, reps);
        }
        (Some("solve"), Some("dev")) => {
            println!("{SOLVE_HEADER}");
            dev!(solve, reps);
        }
        (Some("solve"), Some("heldout")) => {
            println!("{SOLVE_HEADER}");
            heldout!(solve, reps);
        }
        _ => {
            eprintln!("usage: gf2_residual_replay <batches|solve> <dev|heldout> [reps]");
            std::process::exit(64);
        }
    }
}
