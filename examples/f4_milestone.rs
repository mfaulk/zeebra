//! The milestone figure: the recommended configuration beside classical Buchberger.
//!
//! The ablation in `examples/f4_ablation.rs` compares configurations of *this* build, and two of
//! M16's changes are not option-gated — a cheaper monomial hash in symbolic preprocessing and the
//! rewritten final interreduction are unconditional — so they are inside every ablation row
//! including its baseline. The ablation therefore measures what the options contribute and not
//! what the milestone contributed.
//!
//! This reports the other half: the recommended configuration against `buchberger` on identical
//! inputs, in one process, so the comparison the preceding milestone's §7.2 made can be made again
//! on the same terms. Run the same binary built from `feat/m16-foundation` to get the M16-0 side.
//!
//! ```text
//! cargo run --release --example f4_milestone
//! ```

use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        buchberger, f4_with_options, F4Options,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// The fastest of `rounds` runs: interference can only make a run slower.
fn fastest(rounds: usize, mut run: impl FnMut() -> Duration) -> f64 {
    millis((0..rounds).map(|_| run()).min().expect("a round"))
}

fn row<const N: usize>(
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    rounds: usize,
    run_buchberger: bool,
) {
    let options = F4Options::recommended();
    let baseline_options = F4Options::baseline();

    let f4_time = fastest(rounds, || {
        let at = Instant::now();
        let _ = f4_with_options(system, order, &options).expect("within limits");
        at.elapsed()
    });
    let plain_time = fastest(rounds, || {
        let at = Instant::now();
        let _ = f4_with_options(system, order, &baseline_options).expect("within limits");
        at.elapsed()
    });

    let (basis, _) = f4_with_options(system, order, &options).expect("within limits");

    let buchberger_time = if run_buchberger {
        let time = fastest(rounds, || {
            let at = Instant::now();
            let _ = buchberger(system, order);
            at.elapsed()
        });
        // The oracle: both engines must return the same basis wherever both can run.
        assert_eq!(
            buchberger(system, order),
            basis,
            "{} / {}: the two engines disagree",
            name,
            order.name()
        );
        Some(time)
    } else {
        None
    };

    match buchberger_time {
        Some(bb) => println!(
            "{:<12} {:<8} {:>11.2} {:>11.2} {:>11.2} {:>9.2}x {:>9.2}x {:>6}",
            name,
            order.name(),
            bb,
            plain_time,
            f4_time,
            bb / f4_time,
            plain_time / f4_time,
            basis.len()
        ),
        None => println!(
            "{:<12} {:<8} {:>11} {:>11.2} {:>11.2} {:>10} {:>9.2}x {:>6}",
            name,
            order.name(),
            "-",
            plain_time,
            f4_time,
            "-",
            plain_time / f4_time,
            basis.len()
        ),
    }
}

fn planted_point<const N: usize>(seed: u64) -> Vec<F> {
    use rand::{prelude::StdRng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(seed);
    (0..N).map(|_| F::random(&mut rng)).collect()
}

fn main() {
    println!("Classical Buchberger, F4 at `F4Options::baseline()`, and F4 at the recommended");
    println!("configuration (structured elimination, all pair criteria, dense accumulator), on");
    println!("identical inputs in one process. A dash means Buchberger does not finish here.");
    println!("Each figure is the fastest of several runs. GF(2^31 - 1).");
    println!();
    println!(
        "{:<12} {:<8} {:>11} {:>11} {:>11} {:>10} {:>10} {:>6}",
        "system", "order", "buchberger", "f4 base", "f4 best", "vs bb", "vs base", "basis"
    );

    use MonomialOrder::Lexicographic as LEX;
    use MonomialOrder::{GradedLexicographic as GRLEX, GradedReverseLexicographic as GREVLEX};

    for order in [LEX, GRLEX, GREVLEX] {
        row::<4>("cyclic-4", &cyclic::<4, F>(), order, 5, true);
    }
    for order in [LEX, GRLEX, GREVLEX] {
        row::<5>("cyclic-5", &cyclic::<5, F>(), order, 3, true);
    }
    for order in [LEX, GRLEX, GREVLEX] {
        row::<5>("katsura-5", &katsura::<5, F>(), order, 3, true);
    }
    // katsura-6 under lex is the instance Buchberger did not finish in 1800 s.
    for order in [GRLEX, GREVLEX] {
        row::<6>("katsura-6", &katsura::<6, F>(), order, 3, true);
    }
    row::<6>("katsura-6", &katsura::<6, F>(), LEX, 2, false);
    for order in [GRLEX, GREVLEX] {
        row::<7>("katsura-7", &katsura::<7, F>(), order, 2, false);
    }
    let point = planted_point::<6>(9);
    for order in [LEX, GRLEX, GREVLEX] {
        row::<6>("planted-6", &planted::<6, F>(&point), order, 5, true);
    }
}
