//! What the FGLM pipeline costs, stage by stage, against computing the lex basis directly.
//!
//! Three columns are the pipeline — compute a grevlex basis, build the quotient algebra, convert —
//! and the fourth is what it replaces. The comparison is `build + convert` against `lex f4`, on
//! identical inputs in one process, with the two bases asserted equal wherever both exist.
//!
//! A fifth column prices the safety the conversion does not buy by default. `fglm_to_lex` trusts
//! its input to be a Gröbner basis and returns a **wrong basis** rather than an error if it is
//! not; `fglm_to_lex_checked` verifies first. The `verify` column is what that verification costs,
//! and it is why the trusted entry point is the default rather than the other way round.
//!
//! ```text
//! cargo run --release --example fglm_conversion
//! cargo run --release --example fglm_conversion -- katsura-7
//! ```

use std::{
    io::Write,
    time::{Duration, Instant},
};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        f4, f4_with_options,
        fglm::{fglm_to_lex_with_options, is_grobner_basis, FglmOptions, QuotientAlgebra},
        F4Options,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

/// Verification is skipped above this basis size, where it costs seconds and the figure is already
/// established. Reported as a dash rather than omitted.
const VERIFY_LIMIT: usize = 64;

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// The fastest of three runs: interference can only make a run slower.
fn fastest(mut run: impl FnMut() -> Duration) -> Duration {
    (0..3).map(|_| run()).min().expect("a round")
}

fn time(mut body: impl FnMut()) -> f64 {
    millis(fastest(|| {
        let at = Instant::now();
        body();
        at.elapsed()
    }))
}

fn measure<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
    let source_order = MonomialOrder::GradedReverseLexicographic;
    let lex = MonomialOrder::Lexicographic;
    let f4_options = F4Options::default();
    let fglm_options = FglmOptions::unbounded();

    let source = f4(system, source_order).expect("within limits");
    let build = time(|| {
        let _ = f4_with_options(system, source_order, &f4_options);
    });

    let algebra = time(|| {
        let _ = QuotientAlgebra::new(&source, source_order, &fglm_options).expect("finite");
    });

    let convert = time(|| {
        let _ =
            fglm_to_lex_with_options(&source, source_order, &fglm_options).expect("convertible");
    });

    let (converted, statistics) =
        fglm_to_lex_with_options(&source, source_order, &fglm_options).expect("convertible");

    let verify = if source.len() <= VERIFY_LIMIT {
        Some(time(|| {
            assert!(is_grobner_basis(&source, source_order));
        }))
    } else {
        None
    };

    // The direct route, which the pipeline replaces. An instance F4 cannot finish under lex at the
    // default limits is the case the milestone exists for, so it is reported rather than skipped.
    let direct = f4_with_options(system, lex, &f4_options)
        .ok()
        .map(|(basis, _)| {
            assert_eq!(
                converted, basis,
                "{}: the conversion disagrees with direct lex F4",
                name
            );
            time(|| {
                let _ = f4_with_options(system, lex, &f4_options);
            })
        });

    let pipeline = build + convert;
    println!(
        "| {:<11} | {:>5} | {:>9.2} | {:>9.2} | {:>9.2} | {:>9.2} | {:>11} | {:>9} | {:>5} | {:>8} |",
        name,
        statistics.quotient_dimension,
        build,
        algebra,
        convert,
        pipeline,
        direct.map(|d| format!("{:.2}", d)).unwrap_or_else(|| "no basis".to_string()),
        verify.map(|v| format!("{:.2}", v)).unwrap_or_else(|| "—".to_string()),
        statistics.target_basis_elements,
        statistics.span_row_operations,
    );
    std::io::stdout().flush().expect("stdout");
}

fn header() {
    println!(
        "| {:<11} | {:>5} | {:>9} | {:>9} | {:>9} | {:>9} | {:>11} | {:>9} | {:>5} | {:>8} |",
        "system",
        "D",
        "build ms",
        "algebra",
        "convert",
        "pipeline",
        "lex f4 ms",
        "verify ms",
        "|G|",
        "span ops",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(7),
        "-".repeat(11),
        "-".repeat(11),
        "-".repeat(11),
        "-".repeat(11),
        "-".repeat(13),
        "-".repeat(11),
        "-".repeat(7),
        "-".repeat(10),
    );
}

fn planted_point<const N: usize>() -> Vec<F> {
    (0..N).map(|i| F::new(2 * i as u64 + 3)).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let wanted = |name: &str| args.is_empty() || args.iter().any(|a| a == name);

    println!("# FGLM pipeline against direct lex F4, GF(2^31 - 1), fastest of three");
    println!();
    header();

    if wanted("cyclic-3") {
        measure("cyclic-3", &cyclic::<3, F>());
    }
    if wanted("cyclic-5") {
        measure("cyclic-5", &cyclic::<5, F>());
    }
    if wanted("cyclic-6") {
        measure("cyclic-6", &cyclic::<6, F>());
    }
    if wanted("katsura-3") {
        measure("katsura-3", &katsura::<3, F>());
    }
    if wanted("katsura-4") {
        measure("katsura-4", &katsura::<4, F>());
    }
    if wanted("katsura-5") {
        measure("katsura-5", &katsura::<5, F>());
    }
    if wanted("katsura-6") {
        measure("katsura-6", &katsura::<6, F>());
    }
    if wanted("katsura-7") {
        measure("katsura-7", &katsura::<7, F>());
    }
    if wanted("planted-4") {
        measure("planted-4", &planted::<4, F>(&planted_point::<4>()));
    }
    if wanted("planted-6") {
        measure("planted-6", &planted::<6, F>(&planted_point::<6>()));
    }
    if wanted("planted-8") {
        measure("planted-8", &planted::<8, F>(&planted_point::<8>()));
    }

    println!();
    println!(
        "`pipeline` is build + convert, against `lex f4` for the same ideal. `algebra` is the"
    );
    println!("quotient-algebra construction, which `convert` includes rather than adds to.");
    println!(
        "`verify ms` prices `fglm_to_lex_checked` against `fglm_to_lex`, which trusts its input."
    );
    println!("`no basis` means direct lex F4 crossed a limit in F4Options::default().");
}
