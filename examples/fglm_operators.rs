//! How sparse the multiplication operators really are, and therefore what they cost to store.
//!
//! FGLM's memory is dominated by the `N` operators `T_i`, each a `D x D` linear map on the
//! quotient algebra. Column `j` of `T_i` is the normal form of `x_i b_j`, and where that product
//! is itself a standard monomial the column is a unit vector costing nothing. How often that
//! happens is a property of the staircase's shape, not something to assume: this measures it.
//!
//! Two columns matter, and they disagree. `standard cols` is how many products stayed inside the
//! staircase. `stored entries` is what the representation actually holds, against the `N * D^2`
//! cells a dense matrix would. **A sparse entry costs 16 bytes against a dense cell's 8**, so the
//! sparse form only saves memory below 50% fill — which holds on two of the three families here
//! and not on the third.
//!
//! **`bytes won` below counts entries, not allocations**, and the two differ: the columns also cost
//! one 24-byte `Column` each, and a `Vec` of this element type allocates four slots at a minimum
//! even to hold one. On the planted family that slack is 41% of what the operators really occupy.
//! `cargo run --release --example fglm_profile` reports the allocated figure; this reports the
//! mathematical one. See §3.5 of `docs/MILESTONE-FGLM-SCALABILITY.md`.
//!
//! ```text
//! cargo run --release --example fglm_operators
//! ```

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        f4,
        fglm::{FglmOptions, QuotientAlgebra},
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

/// Bytes per stored sparse entry: a `usize` index and a 64-bit field element.
const SPARSE_ENTRY_BYTES: usize = 16;

/// Bytes per cell of a dense `D x D` matrix of 64-bit field elements.
const DENSE_CELL_BYTES: usize = 8;

fn report<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let basis = f4(system, order).expect("within limits");
    let algebra = QuotientAlgebra::new(&basis, order, &FglmOptions::unbounded()).expect("finite");

    let d = algebra.dimension();
    let standard: usize = (0..N).map(|i| algebra.operator(i).standard_columns()).sum();
    let stored: usize = (0..N).map(|i| algebra.operator(i).stored_entries()).sum();
    let columns = N * d;
    let cells = N * d * d;

    let sparse_bytes = stored * SPARSE_ENTRY_BYTES;
    let dense_bytes = cells * DENSE_CELL_BYTES;

    println!(
        "| {:<11} | {:>2} | {:>5} | {:>6}/{:<6} {:>5.1}% | {:>8}/{:<9} {:>6.2}% | {:>9.2}x |",
        name,
        N,
        d,
        standard,
        columns,
        100.0 * standard as f64 / columns as f64,
        stored,
        cells,
        100.0 * stored as f64 / cells as f64,
        dense_bytes as f64 / sparse_bytes as f64,
    );
}

fn main() {
    println!("# Multiplication-operator density, GF(2^31 - 1), grevlex");
    println!();
    println!(
        "| {:<11} | {:>2} | {:>5} | {:<20} | {:<25} | {:>9} |",
        "system", "N", "D", "standard cols", "stored entries vs dense", "bytes won"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|",
        "-".repeat(13),
        "-".repeat(4),
        "-".repeat(7),
        "-".repeat(22),
        "-".repeat(27),
        "-".repeat(11)
    );

    report("katsura-3", &katsura::<3, F>());
    report("katsura-4", &katsura::<4, F>());
    report("katsura-5", &katsura::<5, F>());
    report("katsura-6", &katsura::<6, F>());
    report("katsura-7", &katsura::<7, F>());
    report("cyclic-3", &cyclic::<3, F>());
    report("cyclic-5", &cyclic::<5, F>());
    report("cyclic-6", &cyclic::<6, F>());

    let point4: Vec<F> = [3u64, 5, 7, 11].iter().map(|v| F::new(*v)).collect();
    report("planted-4", &planted::<4, F>(&point4));
    let point6: Vec<F> = [3u64, 5, 7, 11, 13, 17]
        .iter()
        .map(|v| F::new(*v))
        .collect();
    report("planted-6", &planted::<6, F>(&point6));
    let point8: Vec<F> = [3u64, 5, 7, 11, 13, 17, 19, 23]
        .iter()
        .map(|v| F::new(*v))
        .collect();
    report("planted-8", &planted::<8, F>(&point8));

    println!();
    println!(
        "`bytes won` is dense bytes over sparse bytes at {} bytes per stored entry against",
        SPARSE_ENTRY_BYTES
    );
    println!(
        "{} per dense cell. Below 1.00x the dense form would be smaller.",
        DENSE_CELL_BYTES
    );
    println!("Cyclic-4 is absent because it is positive-dimensional and has no quotient algebra.");
}
