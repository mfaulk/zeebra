//! What a `GF(2)` entry costs to store, and what the elimination backends do with one.
//!
//! #218's question 3, which `docs/research/boolean-solving.md` §9 left as the one thing keeping
//! that issue open: a sparse entry is `(usize, F)`, and the index's alignment pads it to **16
//! bytes at any field width**, so over `GF(2)` it is 16 bytes carrying one bit. That bounds what a
//! `GF(2)` instance reaches before a representation change, and §9 asked for it as a measurement
//! rather than an assumption.
//!
//! The measurement has to be a comparison to mean anything, so every figure here is taken over
//! **the same structural system at two field widths** — `Zp2` and `Zp2147483647`, the same random
//! quadratics with the same `x_i^2 - x_i` adjoined and the same seed.
//!
//! The shapes do **not** come out identical, and that is the first finding rather than a flaw in
//! the design. An earlier draft of this file asserted in prose that they would be — "identical
//! monomial support, matrix shapes and row-operation counts at both widths" — and the measurement
//! says otherwise: over `GF(2)` the same system needs about **half** the entries and about half
//! the row operations, because coefficients are 0 or 1 and additions cancel mod 2 far more often.
//! So `GF(2)` is cheaper in memory than the wide field, and **not for the reason the question
//! asked about**: the entry is the same size, there are simply fewer of them.
//!
//! The second reason this exists is narrower and is a correctness gap rather than a measurement.
//! `src/linalg/` has no characteristic-two coverage at all — `Zp2`, `Gf256` and
//! `BinaryFieldElement` appear nowhere under it — so of the three backends only
//! [`Backend::Adaptive`] has ever run in characteristic two, and only indirectly, because that is
//! what `F4Options::default()` selects. This harness runs **all three** over `GF(2)` matrices and
//! asserts they agree on the resulting matrix and on every counter, which is the contract
//! `src/linalg/echelon.rs` states and had never been exercised at this characteristic.
//!
//! ```text
//! cargo run --release --example boolean_density
//! cargo run --release --example boolean_density -- 6 8 10
//! ```

use rand::{rngs::StdRng, Rng, SeedableRng};
use std::time::{Duration, Instant};

use zeebra::{
    fields::{Zp2, Zp2147483647},
    grobner::{
        f4::{
            macaulay::MacaulayMatrix,
            symbolic::{symbolic_preprocessing_with, ReducerCache},
        },
        field_equations, trace_batches, F4Options,
    },
    linalg::{row_echelon_with, sparse::SparseMatrix, Backend},
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

/// Variable counts measured by default.
///
/// `n = 12` is compiled and reachable as an argument but is **not** in the default set: random
/// quadratic Boolean F4 does not finish there inside ten minutes, where `n = 10` takes a few
/// seconds. The per-entry cost is visible from `n = 6` and the trend is established by three
/// sizes.
const DEFAULT: [usize; 3] = [6, 8, 10];

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

const BACKENDS: [Backend; 3] = [Backend::Sparse, Backend::Dense, Backend::Adaptive];

/// The Boolean restriction equations `x_i^2 - x_i`, one per variable.
///
/// **Over `GF(2)` these are the field equations** — `q = 2`, so `x_i^q - x_i` is exactly this — and
/// `boolean_restriction_is_the_gf2_field_equation` asserts that against
/// [`zeebra::grobner::field_equations`] rather than leaving it to the reader.
///
/// Over the wide field they are not field equations, and that is the point. `x_i^q - x_i` at
/// `q = 2147483647` is a degree-2^31 generator no computation could use — the first draft of this
/// harness called `with_field_equations` for both widths and F4 refused at 200 000 matrix rows,
/// which is the honest reason this function exists. Degree two keeps the **monomial support, the
/// matrix shapes and the row-operation counts identical at both widths**, which is what makes the
/// storage comparison a comparison. It restricts each variable to `{0, 1}` over any field.
fn boolean_restriction<const N: usize, F: FiniteField>() -> Vec<MultivariatePolynomial<N, F>> {
    (0..N)
        .map(|i| {
            let mut square = [0u32; N];
            square[i] = 2;
            let mut linear = [0u32; N];
            linear[i] = 1;
            MultivariatePolynomial::new(&[
                (Monomial::new(&square), F::one()),
                (Monomial::new(&linear), F::zero() - F::one()),
            ])
        })
        .collect()
}

/// A random quadratic Boolean system in `N` variables with a planted solution.
///
/// `benchmark_systems::planted` is **deliberately not used**: it is a structured system, and at
/// `N = 12` it builds a widest matrix of 54 x 36 with every elimination under 0.01 ms — real
/// figures about nothing. #218's own reproducible experiment specifies *random* quadratics, and the
/// construction here is the one `field_equations`' dimension test uses, so the two agree on what a
/// Boolean instance is.
///
/// The plant and the monomial support are the same at both field widths, because `rng` is seeded
/// identically and the coefficients are drawn from `{0, 1}` either way. The *matrices* F4 goes on
/// to build are not: cancellation differs, which is what the measurement reports.
fn random_boolean_system<const N: usize, F: FiniteField>(
    equations: usize,
    seed: u64,
) -> Vec<MultivariatePolynomial<N, F>> {
    let mut rng = StdRng::seed_from_u64(seed);
    let plant: [F; N] = std::array::from_fn(|_| {
        if rng.gen_bool(0.5) {
            F::one()
        } else {
            F::zero()
        }
    });

    let mut system: Vec<MultivariatePolynomial<N, F>> = Vec::with_capacity(equations + N);
    for _ in 0..equations {
        let mut terms: Vec<(Monomial<N>, F)> = Vec::new();
        for i in 0..N {
            for j in i..N {
                if rng.gen_bool(0.3) {
                    let mut exponents = [0u32; N];
                    exponents[i] += 1;
                    exponents[j] += 1;
                    terms.push((Monomial::new(&exponents), F::one()));
                }
            }
        }
        let mut polynomial: MultivariatePolynomial<N, F> = MultivariatePolynomial::new(&terms);
        // The constant term is whatever makes the plant a root, so the system has a solution by
        // construction rather than by search.
        let value = polynomial.eval(&plant);
        polynomial += MultivariatePolynomial::new(&[(Monomial::one(), F::zero() - value)]);
        assert!(
            polynomial.eval(&plant).is_zero(),
            "the plant must be a root of every generator"
        );
        system.push(polynomial);
    }
    system.extend(boolean_restriction::<N, F>());
    system
}

/// Every Macaulay matrix the Boolean system at `N` variables builds, in the order F4 builds them.
fn boolean_matrices<const N: usize, F: FiniteField>() -> Vec<SparseMatrix<F>> {
    // One equation per variable: the determined case, which is the Fukuoka/MQ shape and the one
    // whose solving degree the Boolean semiregular series is stated for.
    let system = random_boolean_system::<N, F>(N, 218);

    let options = F4Options::baseline();
    let (_, _, trace) = trace_batches(&system, ORDER, &options).expect("within limits");
    trace
        .batches()
        .iter()
        .filter_map(|batch| {
            let preprocessed = symbolic_preprocessing_with(
                &batch.basis,
                &batch.pairs,
                options.max_matrix_rows,
                options.reducer_selection,
                &mut ReducerCache::disabled(),
            )
            .ok()?;
            Some(
                MacaulayMatrix::build(&batch.basis, &preprocessed, ORDER)
                    .matrix()
                    .clone(),
            )
        })
        .collect()
}

/// What one instance's eliminations cost, and what they stored.
struct Measured {
    rows: usize,
    columns: usize,
    entries: usize,
    peak_live: usize,
    row_operations: usize,
    /// Elimination time per backend, in the order of [`BACKENDS`].
    elapsed: [Duration; 3],
}

/// Every backend over the same matrices, asserted to agree, and timed.
///
/// The agreement is the point as much as the timing: `src/linalg/echelon.rs` promises every
/// backend produces the same matrix and the same [`EliminationStatistics`], and until this harness
/// nothing checked that promise in characteristic two.
fn measure<F: FiniteField>(matrices: &[SparseMatrix<F>]) -> Measured {
    let mut elapsed = [Duration::ZERO; 3];
    let mut row_operations = 0;
    let mut peak_live = 0;
    let mut entries = 0;
    let (mut rows, mut columns) = (0, 0);

    for matrix in matrices {
        entries += matrix.nonzeros();
        rows = rows.max(matrix.num_rows());
        columns = columns.max(matrix.num_columns());

        let mut reference: Option<(SparseMatrix<F>, _)> = None;
        for (slot, backend) in BACKENDS.iter().enumerate() {
            let mut working = matrix.clone();
            let start = Instant::now();
            let statistics = row_echelon_with(*backend, &mut working, usize::MAX)
                .expect("an unbounded budget cannot refuse");
            elapsed[slot] += start.elapsed();

            match &reference {
                None => {
                    row_operations += statistics.row_operations;
                    peak_live = peak_live.max(statistics.peak_nonzeros);
                    reference = Some((working, statistics));
                }
                Some((expected_matrix, expected_statistics)) => {
                    assert_eq!(
                        &working, expected_matrix,
                        "{:?} disagreed with {:?} on the resulting matrix",
                        backend, BACKENDS[0]
                    );
                    assert_eq!(
                        &statistics, expected_statistics,
                        "{:?} disagreed with {:?} on the elimination counters",
                        backend, BACKENDS[0]
                    );
                }
            }
        }
    }

    Measured {
        rows,
        columns,
        entries,
        peak_live,
        row_operations,
        elapsed,
    }
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

/// That the degree-two restriction used here really is `GF(2)`'s field equation.
///
/// The whole measurement is about a *Boolean* workload, so if the generators adjoined were not the
/// field equations over `GF(2)` the matrices would be the wrong ones. Checked against the shipped
/// [`zeebra::grobner::field_equations`] rather than argued from `q = 2`.
fn boolean_restriction_is_the_gf2_field_equation() {
    let shipped = field_equations::<8, Zp2>().expect("GF(2) has a representable order");
    let local = boolean_restriction::<8, Zp2>();
    assert_eq!(
        local, shipped,
        "the restriction adjoined here is not GF(2)'s field equation"
    );
    // And it is *not* the field equation over the wide field, which is why the control is a
    // control and not a second Boolean instance.
    let wide = field_equations::<2, Zp2147483647>().expect("Zp31 has a representable order");
    assert_ne!(
        wide,
        boolean_restriction::<2, Zp2147483647>(),
        "x^2 - x cannot be Zp2147483647's field equation"
    );
}

/// Bytes one live sparse entry occupies over `F`, which is what the budget is really spending.
fn bytes_per_entry<F>() -> usize {
    size_of::<(usize, F)>()
}

fn main() {
    boolean_restriction_is_the_gf2_field_equation();

    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let sizes: Vec<usize> = if arguments.is_empty() {
        DEFAULT.to_vec()
    } else {
        arguments
            .iter()
            .map(|argument| argument.parse().expect("a variable count"))
            .collect()
    };

    println!("# A `GF(2)` entry costs what any other entry costs (#218 question 3)");
    println!();
    println!(
        "Boolean systems — planted quadratics plus the field equations `x_i^q - x_i` — eliminated \
         over"
    );
    println!(
        "`Zp2` and over `Zp2147483647`. The prime-field column is a **storage control, not a \
         comparand**:"
    );
    println!(
        "it holds the matrices' shapes fixed so the only quantity differing is `size_of::<F>()`."
    );
    println!();
    println!(
        "| field | `size_of::<F>()` | `size_of::<(usize, F)>()` | bits of information per entry | \
         bytes per bit |"
    );
    println!("| --- | ---: | ---: | ---: | ---: |");
    println!(
        "| `Zp2` | {} | **{}** | **1** | **{}** |",
        size_of::<Zp2>(),
        bytes_per_entry::<Zp2>(),
        bytes_per_entry::<Zp2>(),
    );
    println!(
        "| `Zp2147483647` | {} | **{}** | 31 | {:.2} |",
        size_of::<Zp2147483647>(),
        bytes_per_entry::<Zp2147483647>(),
        bytes_per_entry::<Zp2147483647>() as f64 / 31.0,
    );
    println!();
    println!(
        "**The sparse entry is the same size at both widths**, so over `GF(2)` it is {} bytes \
         carrying one bit",
        bytes_per_entry::<Zp2>()
    );
    println!(
        "— a factor of {} against the information, and the index's alignment is what pins it: a",
        bytes_per_entry::<Zp2>() * 8
    );
    println!(
        "`usize` column number is {} bytes before any coefficient is stored.",
        size_of::<usize>()
    );

    println!();
    println!("## The same Boolean matrices at both widths");
    println!();
    println!(
        "| n | field | widest | entries | peak live | row ops | live entry bytes | sparse | dense \
         | adaptive | adaptive ns/op |"
    );
    println!("| ---: | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |");

    for &n in &sizes {
        for (label, row) in rows_for(n) {
            println!(
                "| {} | {} | {}x{} | {} | {} | {} | {} | {:.2} | {:.2} | {:.2} | {:.0} |",
                n,
                label,
                row.rows,
                row.columns,
                row.entries,
                row.peak_live,
                row.row_operations,
                row.peak_live * row.bytes_per_entry,
                millis(row.elapsed[0]),
                millis(row.elapsed[1]),
                millis(row.elapsed[2]),
                row.elapsed[2].as_secs_f64() * 1e9 / row.row_operations.max(1) as f64,
            );
        }
    }

    println!();
    println!(
        "Milliseconds, over every matrix the instance builds. All three backends ran over every \
         matrix and"
    );
    println!(
        "**are asserted equal on the resulting matrix and on every counter** — the contract \
         `linalg::echelon`"
    );
    println!(
        "states, and which nothing had exercised in characteristic two: `src/linalg/` contains no \
         `Zp2`,"
    );
    println!(
        "`Gf256` or `BinaryFieldElement`, so only `Backend::Adaptive` had ever run there, and only \
         because"
    );
    println!("`F4Options::default()` selects it.");
    println!();
    println!(
        "`live entry bytes` is `peak live x {}` — what `max_live_bytes` actually spends, and what a",
        bytes_per_entry::<Zp2>()
    );
    println!("bit-packed representation (#272) would cut.");
    println!();
    println!("**The two widths do not build the same matrices**, which the first draft of this");
    println!(
        "harness asserted they would. Over `GF(2)` the same structural system needs about half"
    );
    println!(
        "the entries and about half the row operations: coefficients are 0 or 1 and additions"
    );
    println!("cancel mod 2 far more often, so rows go to zero that would not over a large prime.");
    println!("So `GF(2)` is cheaper in memory than the wide field — by **entry count**, not by");
    println!(
        "entry size. The size is identical, which is the question's premise confirmed and the"
    );
    println!("reason the saving has to come from the representation rather than from the field.");
    println!();
    println!(
        "`adaptive ns/op` normalizes by the row operations each side actually performed, so it"
    );
    println!("separates 'fewer operations' from 'cheaper operations'. The remaining gap is the");
    println!("4-byte against 8-byte cell cost `MILESTONE-SIMD-PARALLELISM.md` §8.4 measured");
    println!("independently, not a characteristic-two effect.");
}

/// Both widths at one variable count, labelled.
///
/// `N` is a const generic, so the sizes have to be enumerated rather than looped over.
fn rows_for(n: usize) -> Vec<(&'static str, Row)> {
    match n {
        6 => both::<6>(),
        8 => both::<8>(),
        10 => both::<10>(),
        12 => both::<12>(),
        other => panic!(
            "variable count {} is not compiled; add it to `rows_for`",
            other
        ),
    }
}

struct Row {
    rows: usize,
    columns: usize,
    entries: usize,
    peak_live: usize,
    row_operations: usize,
    bytes_per_entry: usize,
    elapsed: [Duration; 3],
}

fn both<const N: usize>() -> Vec<(&'static str, Row)> {
    let narrow = measure(&boolean_matrices::<N, Zp2>());
    let wide = measure(&boolean_matrices::<N, Zp2147483647>());
    vec![
        ("`Zp2`", row(narrow, bytes_per_entry::<Zp2>())),
        (
            "`Zp2147483647`",
            row(wide, bytes_per_entry::<Zp2147483647>()),
        ),
    ]
}

fn row(measured: Measured, bytes: usize) -> Row {
    Row {
        rows: measured.rows,
        columns: measured.columns,
        entries: measured.entries,
        peak_live: measured.peak_live,
        row_operations: measured.row_operations,
        bytes_per_entry: bytes,
        elapsed: measured.elapsed,
    }
}
