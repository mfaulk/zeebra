//! Symbolic state with and without exact component decomposition (#1036, Stage 1).
//!
//! Each row is a seeded `benchmark_systems::dense_blocks` input: disjoint dense quadratic blocks,
//! interleaved in the variable order, over GF(2^31 - 1). Both arms return the same reduced basis
//! (checked); what differs is the matrices F4 builds on the way.
//!
//! - `rows`, `cols`, `live`: the largest Macaulay matrix's rows and columns and the peak live
//!   nonzeros of any one batch. For the decomposed arm, the maximum over components.
//! - `ops`: row operations summed over every batch (and every component).
//! - `batches`: matrices built, summed over components.
//! - `ms`: wall time of the whole call, detection included. **Development figures on whatever
//!   machine runs this**, not a deciding measurement: no pinning, no repetition, no comparand.
//!
//! ```text
//! cargo run --release --example decompose_evidence
//! ```

use std::time::Instant;

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::dense_blocks, f4_decomposed, f4_with_options, DecomposeRoute, F4Options,
        F4Statistics,
    },
    MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

/// Fresh development sizes: none is a `zb/coupled-blocks` rung (`blk-2x4`, `blk-3x3`, `blk-2x6`).
const SEED: u64 = 0x1036;

struct Shape {
    rows: usize,
    cols: usize,
    live: usize,
    ops: usize,
    batches: usize,
    ms: f64,
}

fn shape<'a>(statistics: impl Iterator<Item = &'a F4Statistics>, ms: f64) -> Shape {
    let mut out = Shape {
        rows: 0,
        cols: 0,
        live: 0,
        ops: 0,
        batches: 0,
        ms,
    };
    for s in statistics {
        out.rows = out.rows.max(s.max_matrix_rows);
        out.cols = out.cols.max(s.max_matrix_columns);
        out.live = out.live.max(s.max_live_nonzeros);
        out.ops += s.row_operations;
        out.batches += s.batches;
    }
    out
}

fn row<const N: usize>(label: &str, sizes: &[usize], order: MonomialOrder, order_name: &str) {
    let system: Vec<MultivariatePolynomial<N, F>> = dense_blocks(sizes, SEED);
    let options = F4Options::default();

    let start = Instant::now();
    let (whole_basis, whole) = f4_with_options(&system, order, &options).expect("undecomposed");
    let whole = shape(std::iter::once(&whole), start.elapsed().as_secs_f64() * 1e3);

    let start = Instant::now();
    let (basis, report) = f4_decomposed(&system, order, &options, None);
    let ms = start.elapsed().as_secs_f64() * 1e3;
    assert_eq!(report.route, DecomposeRoute::Decomposed);
    assert_eq!(
        basis.expect("decomposed"),
        whole_basis,
        "{label}: bases differ"
    );
    let parts = shape(report.components.iter().map(|c| &c.statistics), ms);

    for (arm, s) in [("whole", &whole), ("split", &parts)] {
        println!(
            "{label:<10} {order_name:<8} {arm:<6} {:>7} {:>7} {:>10} {:>11} {:>7} {:>9.1}",
            s.rows, s.cols, s.live, s.ops, s.batches, s.ms
        );
    }
    println!(
        "{label:<10} {order_name:<8} ratio  {:>7.1} {:>7.1} {:>10.1} {:>11.1} {:>7} {:>9.1}   detect {:.1} us",
        whole.rows as f64 / parts.rows as f64,
        whole.cols as f64 / parts.cols as f64,
        whole.live as f64 / parts.live as f64,
        whole.ops as f64 / parts.ops.max(1) as f64,
        "",
        whole.ms / parts.ms,
        report.detection.as_secs_f64() * 1e6,
    );
}

fn main() {
    println!(
        "{:<10} {:<8} {:<6} {:>7} {:>7} {:>10} {:>11} {:>7} {:>9}",
        "input", "order", "arm", "rows", "cols", "live", "ops", "batches", "ms"
    );
    let grevlex = MonomialOrder::GradedReverseLexicographic;
    row::<7>("3+4", &[3, 4], MonomialOrder::Lexicographic, "lex");
    row::<10>("2x5", &[5, 5], grevlex, "grevlex");
    row::<12>("3x4", &[4, 4, 4], grevlex, "grevlex");
    row::<12>("4x3", &[3, 3, 3, 3], grevlex, "grevlex");
    row::<9>("3+6", &[3, 6], grevlex, "grevlex");
    row::<11>("5+6", &[5, 6], grevlex, "grevlex");
    row::<14>("2x7", &[7, 7], grevlex, "grevlex");
    row::<18>("3x6", &[6, 6, 6], grevlex, "grevlex");
    row::<16>("2x8", &[8, 8], grevlex, "grevlex");
}
