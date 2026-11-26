//! What `FglmControl` costs when it never fires, and how far a conversion overruns a deadline (#1167).
//!
//! Two figures per system, on a grevlex source over GF(2^31 - 1):
//!
//! * **Poll overhead**: the fastest of `REPS` (default 9) conversions with no control against the
//!   fastest with a deadline an hour away and a cancellation flag never set, interleaved. The armed
//!   control reads the clock at every safe point, which is the cost a caller pays.
//! * **Overrun**: deadlines at 25%, 50% and 75% of the unlimited time; the time from the deadline to
//!   the return, and the stage that observed it. Bounded by that stage's indivisible unit (see
//!   `FglmStage`), not by zero.
//!
//! ```text
//! cargo run --release --example fglm_control_probe -- [REPS]
//! ```

use std::{
    sync::atomic::AtomicBool,
    time::{Duration, Instant},
};

use zeebra::{
    fields::Zp2147483647 as F,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4,
        fglm::{ConversionStrategy, FglmControl, FglmOptions},
        fglm_to_lex_with_control, fglm_to_lex_with_options,
    },
    MonomialOrder, MultivariatePolynomial,
};

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

fn main() {
    let reps: usize = std::env::args()
        .nth(1)
        .map(|s| s.parse().expect("REPS is a count"))
        .unwrap_or(9);
    println!(
        "{:<12} {:<10} {:>5} {:>11} {:>11} {:>8}   overrun at 25% / 50% / 75% of unlimited",
        "system", "strategy", "D", "none (ms)", "armed (ms)", "ratio"
    );
    for strategy in [ConversionStrategy::Classical, ConversionStrategy::Wiedemann] {
        row(
            "katsura-7",
            &f4(&katsura::<7, F>(), ORDER).unwrap(),
            strategy,
            reps,
        );
        row(
            "katsura-8",
            &f4(&katsura::<8, F>(), ORDER).unwrap(),
            strategy,
            reps,
        );
        row(
            "cyclic-6",
            &f4(&cyclic::<6, F>(), ORDER).unwrap(),
            strategy,
            reps,
        );
        row(
            "katsura-9",
            &f4(&katsura::<9, F>(), ORDER).unwrap(),
            strategy,
            reps,
        );
        row(
            "katsura-10",
            &f4(&katsura::<10, F>(), ORDER).unwrap(),
            strategy,
            reps,
        );
    }
}

fn row<const N: usize>(
    name: &str,
    source: &[MultivariatePolynomial<N, F>],
    strategy: ConversionStrategy,
    reps: usize,
) {
    let options = FglmOptions {
        conversion_strategy: strategy,
        ..FglmOptions::recommended()
    };
    let cancel = AtomicBool::new(false);
    let (expected, statistics) = fglm_to_lex_with_options(source, ORDER, &options).unwrap();

    let mut none = Duration::MAX;
    let mut armed = Duration::MAX;
    for _ in 0..reps {
        let started = Instant::now();
        let (basis, _) = fglm_to_lex_with_options(source, ORDER, &options).unwrap();
        none = none.min(started.elapsed());
        assert_eq!(basis, expected);

        let control = FglmControl::unlimited()
            .with_time_limit(Duration::from_secs(3_600))
            .with_cancellation(&cancel);
        let started = Instant::now();
        let (basis, _) = fglm_to_lex_with_control(source, ORDER, &options, &control);
        armed = armed.min(started.elapsed());
        assert_eq!(basis.unwrap(), expected);
    }

    let overruns: Vec<String> = [0.25, 0.5, 0.75]
        .iter()
        .map(|fraction| {
            let deadline = Instant::now() + none.mul_f64(*fraction);
            let control = FglmControl::unlimited().with_deadline(deadline);
            let (result, _) = fglm_to_lex_with_control(source, ORDER, &options, &control);
            let returned = Instant::now();
            match result {
                Ok(_) => "completed".to_string(),
                Err(e) => format!(
                    "{:.3} ms ({})",
                    returned.saturating_duration_since(deadline).as_secs_f64() * 1e3,
                    control
                        .stopped()
                        .map_or(e.to_string(), |s| format!("{s:?}"))
                ),
            }
        })
        .collect();

    println!(
        "{:<12} {:<10} {:>5} {:>11.3} {:>11.3} {:>8.3}   {}",
        name,
        format!("{strategy:?}"),
        statistics.quotient_dimension,
        none.as_secs_f64() * 1e3,
        armed.as_secs_f64() * 1e3,
        armed.as_secs_f64() / none.as_secs_f64(),
        overruns.join(" / ")
    );
}
