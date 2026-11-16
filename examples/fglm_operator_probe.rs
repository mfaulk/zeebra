//! Operator construction at one border-worker count against another, on one source basis per system.
//!
//! The A/B behind #826: `BorderBatch::workers` shares whole border batches across threads, so the
//! answer must not move and only the clock may. Every row asserts the operators equal to the
//! first worker count's, and reports the fastest of `REPS` (default 7) constructions.
//!
//! ```text
//! cargo run --release --features external-runners --example fglm_operator_probe -- 1 16
//! ```

use std::time::{Duration, Instant};

use zeebra::{
    fields::{Zp2147483647, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        external::corpus,
        f4_with_options,
        fglm::{BorderBatch, FglmOptions, QuotientAlgebra},
        F4Options,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

fn mq10<F: FiniteField>(modulus: u64) -> Vec<MultivariatePolynomial<10, F>> {
    let input = corpus::instance("mq-random-10", modulus, ORDER).expect("corpus problem");
    let names: [&str; 10] = std::array::from_fn(|i| input.variables[i].as_str());
    input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).expect("corpus polynomial"))
        .collect()
}

fn point<F: FiniteField>(n: usize) -> Vec<F> {
    (0..n as u64).map(|i| F::new(2 * i + 3)).collect()
}

fn measure<const N: usize, F: FiniteField>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    workers: &[usize],
    reps: usize,
) {
    let (basis, _) = f4_with_options(system, ORDER, &F4Options::default()).expect("basis");
    let mut reference = None;
    let mut row = format!("{name:>19}");
    for &w in workers {
        let options = FglmOptions::recommended()
            .with_border_batch(BorderBatch::recommended().with_workers(w));
        let mut best = Duration::MAX;
        let mut batches = 0;
        for _ in 0..reps {
            let start = Instant::now();
            let (algebra, statistics) =
                QuotientAlgebra::new_with_statistics(&basis, ORDER, &options).expect("finite");
            best = best.min(start.elapsed());
            batches = statistics.batches.batches;
            match &reference {
                None => reference = Some(algebra),
                Some(r) => assert_eq!(r, &algebra, "{name}: {w} workers changed the operators"),
            }
        }
        if w == workers[0] {
            row += &format!(" {batches:>4} batches");
        }
        row += &format!("  w{w:<2} {:8.3} ms", best.as_secs_f64() * 1e3);
    }
    println!("{row}");
}

fn main() {
    let workers: Vec<usize> = std::env::args()
        .skip(1)
        .map(|w| w.parse().expect("worker count"))
        .collect();
    let workers = if workers.is_empty() {
        vec![1, 16]
    } else {
        workers
    };
    let reps = std::env::var("REPS").map_or(7, |r| r.parse().expect("REPS"));
    type F = Zp2147483647;
    measure("katsura-6", &katsura::<6, F>(), &workers, reps);
    measure("katsura-7", &katsura::<7, F>(), &workers, reps);
    measure("cyclic-5", &cyclic::<5, F>(), &workers, reps);
    measure("cyclic-6", &cyclic::<6, F>(), &workers, reps);
    measure("planted-8", &planted::<8, F>(&point(8)), &workers, reps);
    measure("planted-10", &planted::<10, F>(&point(10)), &workers, reps);
    measure(
        "mq-random-10 32003",
        &mq10::<Zp32003>(32003),
        &workers,
        reps,
    );
    measure(
        "mq-random-10 2^31-1",
        &mq10::<F>(2147483647),
        &workers,
        reps,
    );
}
