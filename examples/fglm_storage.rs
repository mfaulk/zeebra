//! What each multiplication-operator representation costs to store and to apply.
//!
//! A reduced column is not necessarily sparse. Measured over the corpus, one holds **79% of `D` on
//! katsura-7 and 0.14% on planted-10** — and a sparse entry carries an index as well as a
//! coefficient, so it costs twice a dense cell. Sparse therefore saves memory only below half
//! fill, and the corpus has families on both sides of that line.
//!
//! Three tables, because storage and time are different questions and the answer to the second
//! depends on the input:
//!
//! * **Storage** is exact and machine-independent: bytes under each strategy, and how many columns
//!   `Adaptive` chose to hold densely.
//! * **Application** times `T_i(v)` on a *dense* `v` and on a *unit* `v`. The conversion applies
//!   operators to unit vectors at the start of its walk and to dense ones later, so a
//!   representation that is quicker on one and slower on the other has not obviously won.
//! * **Conversion** is the whole thing, which is what a caller pays.
//!
//! ```text
//! cargo run --release --example fglm_storage
//! cargo run --release --example fglm_storage -- katsura-7
//! ```

use std::{
    io::Write,
    time::{Duration, Instant},
};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        f4,
        fglm::{fglm_to_lex_with_options, FglmOptions, OperatorStorage, QuotientAlgebra},
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

const SOURCE: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

const STORAGES: [OperatorStorage; 3] = [
    OperatorStorage::Sparse,
    OperatorStorage::Adaptive,
    OperatorStorage::Dense,
];

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

fn kilobytes(bytes: usize) -> f64 {
    bytes as f64 / 1024.0
}

/// The fastest of three runs: interference can only make a run slower.
fn fastest(mut run: impl FnMut() -> Duration) -> Duration {
    (0..3).map(|_| run()).min().expect("a round")
}

fn algebra_of<const N: usize>(
    source: &[MultivariatePolynomial<N, F>],
    storage: OperatorStorage,
) -> QuotientAlgebra<N, F> {
    QuotientAlgebra::new(
        source,
        SOURCE,
        &FglmOptions::unbounded().with_operator_storage(storage),
    )
    .expect("finite")
}

/// Every operator applied to `v`, once per variable, `rounds` times.
fn apply_all<const N: usize>(algebra: &QuotientAlgebra<N, F>, v: &[F], rounds: usize) -> Duration {
    fastest(|| {
        let at = Instant::now();
        for _ in 0..rounds {
            for i in 0..N {
                std::hint::black_box(algebra.operator(i).apply(v));
            }
        }
        at.elapsed()
    })
}

fn storage_header() {
    println!(
        "| {:<11} | {:>5} | {:>7} | {:>6} | {:>10} | {:>10} | {:>10} | {:>8} | {:>8} |",
        "system", "D", "reduced", "fill %", "sparse kB", "adaptive", "dense kB", "dense of", "won",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(7),
        "-".repeat(9),
        "-".repeat(8),
        "-".repeat(12),
        "-".repeat(12),
        "-".repeat(12),
        "-".repeat(10),
        "-".repeat(10),
    );
}

fn storage_row<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
    let source = f4(system, SOURCE).expect("within limits");
    let sparse = algebra_of(&source, OperatorStorage::Sparse);
    let adaptive = algebra_of(&source, OperatorStorage::Adaptive);
    let dense = algebra_of(&source, OperatorStorage::Dense);

    // Asserted here as well as in the test suite, so a table printed from a broken build cannot
    // be mistaken for a measurement.
    assert_eq!(
        sparse.operator_entries(),
        adaptive.operator_entries(),
        "{}: adaptive storage found a different number of nonzeros",
        name
    );
    assert_eq!(
        sparse.operator_entries(),
        dense.operator_entries(),
        "{}: dense storage found a different number of nonzeros",
        name
    );

    let d = sparse.dimension();
    let columns: usize = (0..N).map(|i| sparse.operator(i).dimension()).sum();
    let reduced = columns
        - (0..N)
            .map(|i| sparse.operator(i).standard_columns())
            .sum::<usize>();
    let fill = if reduced == 0 || d == 0 {
        0.0
    } else {
        100.0 * sparse.operator_entries() as f64 / (reduced * d) as f64
    };

    let sparse_bytes = sparse.operator_bytes();
    let adaptive_bytes = adaptive.operator_bytes();

    println!(
        "| {:<11} | {:>5} | {:>7} | {:>6.1} | {:>10.1} | {:>10.1} | {:>10.1} | {:>8} | {:>7.2}x |",
        name,
        d,
        reduced,
        fill,
        kilobytes(sparse_bytes),
        kilobytes(adaptive_bytes),
        kilobytes(dense.operator_bytes()),
        adaptive.dense_columns(),
        sparse_bytes as f64 / adaptive_bytes.max(1) as f64,
    );
    std::io::stdout().flush().expect("stdout");
}

fn apply_header() {
    println!(
        "| {:<11} | {:>5} | {:>10} | {:>10} | {:>10} | {:>10} | {:>10} | {:>10} |",
        "system", "D", "sparse/e_j", "adapt/e_j", "dense/e_j", "sparse/v", "adapt/v", "dense/v",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(7),
        "-".repeat(12),
        "-".repeat(12),
        "-".repeat(12),
        "-".repeat(12),
        "-".repeat(12),
        "-".repeat(12),
    );
}

fn apply_row<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>], rounds: usize) {
    let source = f4(system, SOURCE).expect("within limits");
    let algebras: Vec<QuotientAlgebra<N, F>> = STORAGES
        .iter()
        .map(|storage| algebra_of(&source, *storage))
        .collect();

    let d = algebras[0].dimension();
    // A unit vector, as the walk starts with, and a vector with every coordinate nonzero, as it
    // ends with. The sparse path short-circuits on a zero input coordinate and the dense path
    // does not, so the two inputs do not rank the representations the same way.
    let unit = algebras[0].one();
    let full: Vec<F> = (0..d).map(|j| F::new(j as u64 + 1)).collect();

    let unit_times: Vec<f64> = algebras
        .iter()
        .map(|a| millis(apply_all(a, &unit, rounds)))
        .collect();
    let full_times: Vec<f64> = algebras
        .iter()
        .map(|a| millis(apply_all(a, &full, rounds)))
        .collect();

    println!(
        "| {:<11} | {:>5} | {:>10.3} | {:>10.3} | {:>10.3} | {:>10.3} | {:>10.3} | {:>10.3} |",
        name,
        d,
        unit_times[0],
        unit_times[1],
        unit_times[2],
        full_times[0],
        full_times[1],
        full_times[2],
    );
    std::io::stdout().flush().expect("stdout");
}

fn conversion_header() {
    println!(
        "| {:<11} | {:>5} | {:>11} | {:>11} | {:>11} | {:>8} |",
        "system", "D", "sparse ms", "adaptive ms", "dense ms", "won",
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(7),
        "-".repeat(13),
        "-".repeat(13),
        "-".repeat(13),
        "-".repeat(10),
    );
}

fn conversion_row<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
    let source = f4(system, SOURCE).expect("within limits");

    let mut reference: Option<Vec<MultivariatePolynomial<N, F>>> = None;
    let mut times = Vec::new();
    let mut dimension = 0;
    for storage in STORAGES {
        let options = FglmOptions::unbounded().with_operator_storage(storage);
        let (basis, statistics) =
            fglm_to_lex_with_options(&source, SOURCE, &options).expect("convertible");
        dimension = statistics.quotient_dimension;
        match &reference {
            None => reference = Some(basis),
            Some(expected) => assert_eq!(
                &basis, expected,
                "{}: {:?} converted to a different basis",
                name, storage
            ),
        }
        times.push(millis(fastest(|| {
            let at = Instant::now();
            let _ = fglm_to_lex_with_options(&source, SOURCE, &options).expect("convertible");
            at.elapsed()
        })));
    }

    println!(
        "| {:<11} | {:>5} | {:>11.2} | {:>11.2} | {:>11.2} | {:>7.2}x |",
        name,
        dimension,
        times[0],
        times[1],
        times[2],
        times[0] / times[1].max(f64::MIN_POSITIVE),
    );
    std::io::stdout().flush().expect("stdout");
}

fn planted_point<const N: usize>() -> Vec<F> {
    (0..N).map(|i| F::new(2 * i as u64 + 3)).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let wanted = |name: &str| args.is_empty() || args.iter().any(|a| a == name);

    println!("# Operator storage, GF(2^31 - 1), grevlex source");
    println!();
    storage_header();
    if wanted("katsura-5") {
        storage_row("katsura-5", &katsura::<5, F>());
    }
    if wanted("katsura-6") {
        storage_row("katsura-6", &katsura::<6, F>());
    }
    if wanted("katsura-7") {
        storage_row("katsura-7", &katsura::<7, F>());
    }
    if wanted("cyclic-5") {
        storage_row("cyclic-5", &cyclic::<5, F>());
    }
    if wanted("cyclic-6") {
        storage_row("cyclic-6", &cyclic::<6, F>());
    }
    if wanted("planted-6") {
        storage_row("planted-6", &planted::<6, F>(&planted_point::<6>()));
    }
    if wanted("planted-8") {
        storage_row("planted-8", &planted::<8, F>(&planted_point::<8>()));
    }
    if wanted("planted-10") {
        storage_row("planted-10", &planted::<10, F>(&planted_point::<10>()));
    }
    println!();
    println!("`reduced` is the columns that left the staircase and `fill %` is their average");
    println!("occupancy of `D`. `dense of` is how many of them `Adaptive` chose to hold densely,");
    println!("and `won` is sparse bytes over adaptive bytes. Exact figures, not timings: a boxed");
    println!("slice has no spare capacity, so these are the bytes allocated.");

    println!();
    println!("# Operator application, milliseconds for 1000 rounds of all N operators");
    println!();
    apply_header();
    if wanted("katsura-6") {
        apply_row("katsura-6", &katsura::<6, F>(), 1000);
    }
    if wanted("katsura-7") {
        apply_row("katsura-7", &katsura::<7, F>(), 1000);
    }
    if wanted("cyclic-6") {
        apply_row("cyclic-6", &cyclic::<6, F>(), 1000);
    }
    if wanted("planted-8") {
        apply_row("planted-8", &planted::<8, F>(&planted_point::<8>()), 1000);
    }
    println!();
    println!("`/e_j` applies to the class of 1, a unit vector, as the lex walk does at its start;");
    println!("`/v` applies to a vector with every coordinate nonzero, as it does later. A sparse");
    println!("column skips a zero input coordinate and a dense one still walks `D` cells, so the");
    println!("two inputs need not rank the representations the same way.");

    println!();
    println!("# Whole conversion under each storage, fastest of three");
    println!();
    conversion_header();
    if wanted("katsura-6") {
        conversion_row("katsura-6", &katsura::<6, F>());
    }
    if wanted("katsura-7") {
        conversion_row("katsura-7", &katsura::<7, F>());
    }
    if wanted("cyclic-6") {
        conversion_row("cyclic-6", &cyclic::<6, F>());
    }
    if wanted("planted-8") {
        conversion_row("planted-8", &planted::<8, F>(&planted_point::<8>()));
    }
    println!();
    println!("The bases are asserted equal across strategies before any timing is printed.");
    println!("`won` is sparse over adaptive, on the whole conversion rather than on the storage.");
}
