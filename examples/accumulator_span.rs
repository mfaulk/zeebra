//! Whether a contiguous — and therefore vectorizable — inner loop is available to the shipped
//! backend, and what it would cost.
//!
//! `Backend::Adaptive` is what `F4Options::default()` selects, and its inner loop is
//! `DenseAccumulator::subtract_scaled`: it walks the *pivot's* sparse entries and indexes
//! `cells[column]`, a gather and a scatter over a sparse support. AVX2 has `vpgatherdd` and no
//! scatter at all, so the 8-lane kernel in `examples/field_width.rs` cannot be dropped into it.
//! The only route to a contiguous span is to update `cells[pivot.lead .. pivot.tail)` whole,
//! treating the pivot as dense within its own span, which does
//!
//!     span = trailing_column - leading_column + 1
//!
//! cell updates where the shipped loop does `support = nonzeros`. **`span / support` is the work
//! multiplier a wide kernel has to beat with its lane win**, and it is the number this harness
//! reports — weighted by row operations, since that is where the time is.
//!
//! Two further quantities decide whether the lanes could fill at all: the share of row operations
//! whose span is under one vector (8 cells at four bytes) and the share under one cache line
//! (16 cells), where a wide kernel is all prologue and epilogue.
//!
//! The second table accounts for *all* of the accumulator's cell traffic, because two of its loops
//! — `normalize` and the gather in `take` — already run over the contiguous span `[lead, tail)` and
//! could be widened today with no restructuring at all. Their share of the traffic is what says
//! whether that is worth doing. They run once per row; `subtract_scaled` runs once per row
//! operation.
//!
//! Everything is reported for **both reduction strategies**, and the choice is not cosmetic:
//! `ReductionStrategy` changes which candidates leave each batch and hence every later batch, so
//! the two plans do not see the same matrices, and the multiplier is 4.04x under the baseline
//! against 9.81x under the one `F4Options::default()` runs. A conclusion drawn from the baseline
//! alone would be drawn from the wrong population — which is how #539 came to be filed and closed.
//!
//! The statistic is a property of the matrices, not of a timing, so it needs no exclusive lock and
//! reproduces exactly — bit-identical across runs, not merely within noise. The elimination
//! replayed here is `accumulated_row_echelon`'s under the baseline plan and
//! `accumulated_reduce_rows_against_pivots`' under the structured one, with
//! `PivotIndex` — crate-private — standing in as a `Vec<usize>`. A replay that drifted from the
//! shipped loop would report a real histogram of the wrong population, so it is not argued but
//! checked: every matrix is also eliminated by the real backend, and the replay's pivot-application
//! and normalization counts are asserted equal to `EliminationStatistics::row_operations` and
//! `pivot_inversions`.
//!
//! ```text
//! cargo run --release --example accumulator_span
//! cargo run --release --example accumulator_span -- list
//! cargo run --release --example accumulator_span -- katsura-7/grevlex
//! ```

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4::{
            macaulay::MacaulayMatrix,
            symbolic::{symbolic_preprocessing_with, ReducerCache},
        },
        trace_batches, F4Options,
    },
    linalg::{
        reduce_rows_against_pivots_with, row_echelon_with,
        sparse::{SparseMatrix, SparseRow},
        Backend, DenseAccumulator,
    },
    MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

/// The instances §8.4 and §9.1 of `docs/MILESTONE-SIMD-PARALLELISM.md` are measured on.
const DEFAULT: [&str; 7] = [
    "cyclic-4/lex",
    "cyclic-5/grevlex",
    "katsura-5/lex",
    "katsura-5/grevlex",
    "katsura-6/grlex",
    "katsura-6/grevlex",
    "katsura-7/grevlex",
];

/// Lanes in one AVX2 vector over a four-byte cell.
const LANES: usize = 8;

/// Four-byte cells in one 64-byte cache line.
const LINE: usize = 16;

/// What the 8-lane kernel measured in §8.3 is worth on a contiguous span, in cache.
const LANE_SPEEDUP: f64 = 2.9;

fn order_of(name: &str) -> MonomialOrder {
    match name {
        "lex" => MonomialOrder::Lexicographic,
        "grlex" => MonomialOrder::GradedLexicographic,
        "grevlex" => MonomialOrder::GradedReverseLexicographic,
        other => panic!("unknown order {}", other),
    }
}

/// Which configuration's eliminations are being characterized.
///
/// The two differ in more than the split: `ReductionStrategy` changes which candidates come out of
/// each batch, hence every later batch, so the two plans do not even see the same matrices. Both
/// are reported because the first is the instrument §9.1 used and the second is what
/// `F4Options::default()` runs.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Plan {
    /// `F4Options::baseline()`: one echelon pass over every row, no split.
    Unstructured,
    /// `F4Options::recommended()`: reducer rows taken as established pivots, the pair rows reduced
    /// against them. `ReductionStrategy::Structured` is `BlockPlan::ReducersFirstBlock`.
    Structured,
}

impl Plan {
    fn label(self) -> &'static str {
        match self {
            Plan::Unstructured => "unstructured",
            Plan::Structured => "structured (default)",
        }
    }

    fn options(self) -> F4Options {
        match self {
            Plan::Unstructured => F4Options::baseline(),
            Plan::Structured => F4Options::recommended(),
        }
    }
}

/// Every Macaulay matrix one instance builds, each with the row index its pivot block ends at.
///
/// The split is zero under `Plan::Unstructured`, where the elimination discovers every pivot, and
/// `partition_reducers_first()` under `Plan::Structured`, which is what `structured::eliminate`
/// passes to `reduce_rows_against_pivots_with`.
fn matrices(instance: &str, plan: Plan) -> Vec<(SparseMatrix<F>, usize)> {
    let (system, order) = instance
        .split_once('/')
        .expect("an instance is named system/order");
    let order = order_of(order);
    let options = plan.options();

    match system {
        "cyclic-4" => collect(&cyclic::<4, F>(), order, &options, plan),
        "cyclic-5" => collect(&cyclic::<5, F>(), order, &options, plan),
        "katsura-5" => collect(&katsura::<5, F>(), order, &options, plan),
        "katsura-6" => collect(&katsura::<6, F>(), order, &options, plan),
        "katsura-7" => collect(&katsura::<7, F>(), order, &options, plan),
        other => panic!("unknown system {}", other),
    }
}

fn collect<const N: usize>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
    plan: Plan,
) -> Vec<(SparseMatrix<F>, usize)> {
    let (_, _, trace) = trace_batches(system, order, options).expect("within limits");
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
            let mut matrix = MacaulayMatrix::build(&batch.basis, &preprocessed, order);
            let split = match plan {
                Plan::Unstructured => 0,
                Plan::Structured => matrix.partition_reducers_first(),
            };
            Some((matrix.matrix().clone(), split))
        })
        .collect()
}

/// The pivot shapes a whole instance's eliminations present to the inner loop.
#[derive(Default)]
struct Spans {
    row_operations: u64,
    /// Cells the shipped gather/scatter loop touches: the pivot's support, summed.
    support_cells: u64,
    /// Cells a contiguous loop over the pivot's span would touch, summed.
    span_cells: u64,
    /// Row operations whose pivot span is under one vector.
    under_vector: u64,
    /// Row operations whose pivot span is under one cache line.
    under_line: u64,
    /// Occupancy buckets, by decile of `support / span`, weighted by row operations.
    deciles: [u64; 10],
    /// Rows whose leading coefficient was not already one, so `normalize` looped.
    normalizations: u64,
    /// Cells `normalize` scaled, summed: the accumulator's span at each of those.
    normalize_cells: u64,
    /// Cells the gather in `take` scanned, summed: the accumulator's span once per row.
    gather_cells: u64,
}

impl Spans {
    fn observe(&mut self, support: usize, span: usize) {
        self.row_operations += 1;
        self.support_cells += support as u64;
        self.span_cells += span as u64;
        if span < LANES {
            self.under_vector += 1;
        }
        if span < LINE {
            self.under_line += 1;
        }
        let occupancy = support as f64 / span as f64;
        let bucket = ((occupancy * 10.0) as usize).min(9);
        self.deciles[bucket] += 1;
    }

    fn merge(&mut self, other: &Self) {
        self.row_operations += other.row_operations;
        self.support_cells += other.support_cells;
        self.span_cells += other.span_cells;
        self.under_vector += other.under_vector;
        self.under_line += other.under_line;
        self.normalizations += other.normalizations;
        self.normalize_cells += other.normalize_cells;
        self.gather_cells += other.gather_cells;
        for (into, from) in self.deciles.iter_mut().zip(other.deciles.iter()) {
            *into += *from;
        }
    }

    /// Every cell the accumulator reads or writes, across all three of its loops.
    fn traffic(&self) -> u64 {
        self.support_cells + self.normalize_cells + self.gather_cells
    }

    fn traffic_share(&self, cells: u64) -> f64 {
        if self.traffic() == 0 {
            return 0.0;
        }
        100.0 * cells as f64 / self.traffic() as f64
    }

    /// Cell updates a contiguous loop would do for each one the shipped loop does.
    fn multiplier(&self) -> f64 {
        if self.support_cells == 0 {
            return 0.0;
        }
        self.span_cells as f64 / self.support_cells as f64
    }

    fn mean_support(&self) -> f64 {
        if self.row_operations == 0 {
            return 0.0;
        }
        self.support_cells as f64 / self.row_operations as f64
    }

    fn mean_span(&self) -> f64 {
        if self.row_operations == 0 {
            return 0.0;
        }
        self.span_cells as f64 / self.row_operations as f64
    }

    fn share(&self, count: u64) -> f64 {
        if self.row_operations == 0 {
            return 0.0;
        }
        100.0 * count as f64 / self.row_operations as f64
    }
}

/// That the replay applies the same pivots the shipped backend does.
///
/// The whole measurement is a statement about pivots `Backend::Adaptive` actually applies, so a
/// replay that drifted from it would report a real histogram of the wrong population. Checked per
/// matrix rather than argued: `row_operations` is one pivot application each, and
/// `EliminationStatistics` is what the backend itself reports.
fn replay_matches_the_backend(matrix: &SparseMatrix<F>, split: usize, spans: &Spans) {
    let mut eliminated = matrix.clone();
    let statistics = if split == 0 {
        row_echelon_with(Backend::Adaptive, &mut eliminated, usize::MAX)
    } else {
        reduce_rows_against_pivots_with(Backend::Adaptive, &mut eliminated, split, usize::MAX)
    }
    .expect("an unbounded budget admits every matrix");
    assert_eq!(
        statistics.row_operations as u64, spans.row_operations,
        "the replay applied {} pivots where the backend applies {}",
        spans.row_operations, statistics.row_operations
    );
    assert_eq!(
        statistics.pivot_inversions as u64, spans.normalizations,
        "the replay normalized {} rows where the backend normalizes {}",
        spans.normalizations, statistics.pivot_inversions
    );
}

/// `accumulated_row_echelon`'s loop, recording the shape of every pivot it applies.
///
/// The arithmetic is the shipped one, so the `row_operations` this returns is the counter
/// `EliminationStatistics` reports for the same matrix under `Backend::Adaptive` — which
/// [`replay_matches_the_backend`] checks rather than assumes.
fn spans_of(matrix: &SparseMatrix<F>, split: usize) -> Spans {
    let mut spans = Spans::default();
    let mut rows: Vec<SparseRow<F>> = matrix.rows().to_vec();
    let vacant = usize::MAX;
    let mut pivot_of_column = vec![vacant; matrix.num_columns()];
    let mut accumulator = DenseAccumulator::new(matrix.num_columns());

    // `upper_block_pivots`: rows `[..split]` are pivots already, and are neither normalized nor
    // reduced against one another. `reduce_rows_against_pivots_with` panics on a duplicated
    // leading column, so the verification call is what enforces the precondition here too.
    for (index, row) in rows.iter().enumerate().take(split) {
        if let Some(column) = row.leading_column() {
            pivot_of_column[column] = index;
        }
    }

    for index in split..rows.len() {
        let row = std::mem::take(&mut rows[index]);
        // `tail` tracks the accumulator's own upper bound, which is crate-private. The rules are
        // the shipped ones: `load` sets it, `subtract_scaled` widens it, and `leading_column`
        // returns the tightened lower bound, so `lead` needs no replica at all.
        let mut tail = row.trailing_column().map_or(0, |column| column + 1);
        accumulator.load(&row);

        let mut lead = accumulator.num_columns();
        while let Some(column) = accumulator.leading_column() {
            lead = column;
            let pivot_index = pivot_of_column[column];
            if pivot_index == vacant {
                if accumulator.normalize() {
                    spans.normalizations += 1;
                    spans.normalize_cells += (tail - lead) as u64;
                }
                pivot_of_column[column] = index;
                break;
            }
            let pivot = &rows[pivot_index];
            let factor = accumulator
                .leading_coefficient()
                .expect("a row with a leading column has a leading coefficient");
            let leading = pivot.leading_column().expect("a pivot row is nonzero");
            let trailing = pivot.trailing_column().expect("a pivot row is nonzero");
            spans.observe(pivot.nonzeros(), trailing - leading + 1);
            accumulator.subtract_scaled(pivot, factor);
            // `subtract_scaled` also lowers `lead` to the pivot's leading column, which is this
            // very column — a pivot leads with the column it is the pivot of — so only `tail`
            // can move here.
            tail = tail.max(trailing + 1);
        }

        // A row reduced to zero leaves the accumulator empty, and `take` then scans nothing.
        if accumulator.nonzeros() > 0 {
            spans.gather_cells += (tail - lead) as u64;
        }
        rows[index] = accumulator.take();
    }

    spans
}

/// One plan's tables: the multiplier, the traffic split, and the occupancy histogram.
fn report(instances: &[&str], plan: Plan) {
    println!("## {}", plan.label());
    println!();
    println!(
        "| instance | row operations | mean support | mean span | span / support \
         | span < {} cells | span < {} cells | projected |",
        LANES, LINE
    );
    println!("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |");

    let mut total = Spans::default();
    let mut rows = Vec::new();
    for instance in instances {
        let mut spans = Spans::default();
        for (matrix, split) in matrices(instance, plan) {
            let of_matrix = spans_of(&matrix, split);
            replay_matches_the_backend(&matrix, split, &of_matrix);
            spans.merge(&of_matrix);
        }
        println!(
            "| {} | {} | {:.1} | {:.1} | **{:.2}x** | {:.1}% | {:.1}% | {:.2}x |",
            instance,
            spans.row_operations,
            spans.mean_support(),
            spans.mean_span(),
            spans.multiplier(),
            spans.share(spans.under_vector),
            spans.share(spans.under_line),
            LANE_SPEEDUP / spans.multiplier(),
        );
        total.merge(&spans);
        rows.push((*instance, spans));
    }
    println!(
        "| **all** | {} | {:.1} | {:.1} | **{:.2}x** | {:.1}% | {:.1}% | {:.2}x |",
        total.row_operations,
        total.mean_support(),
        total.mean_span(),
        total.multiplier(),
        total.share(total.under_vector),
        total.share(total.under_line),
        LANE_SPEEDUP / total.multiplier(),
    );

    println!();
    println!("Where the accumulator's cell traffic is. `normalize` and the gather in `take` are");
    println!("already contiguous over `[lead, tail)`, so they could be widened with no");
    println!("restructuring; this is the share of the traffic that would buy.");
    println!();
    println!(
        "| instance | cells touched | `subtract_scaled` | `normalize` | the gather in `take` |"
    );
    println!("| --- | ---: | ---: | ---: | ---: |");
    for (instance, spans) in &rows {
        println!(
            "| {} | {} | **{:.1}%** | {:.1}% | {:.1}% |",
            instance,
            spans.traffic(),
            spans.traffic_share(spans.support_cells),
            spans.traffic_share(spans.normalize_cells),
            spans.traffic_share(spans.gather_cells),
        );
    }
    println!(
        "| **all** | {} | **{:.1}%** | {:.1}% | {:.1}% |",
        total.traffic(),
        total.traffic_share(total.support_cells),
        total.traffic_share(total.normalize_cells),
        total.traffic_share(total.gather_cells),
    );

    println!();
    println!("Occupancy of the pivot within its own span, by decile of row operations.");
    println!();
    print!("| instance |");
    for decile in 0..10 {
        print!(" {}-{}% |", decile * 10, decile * 10 + 10);
    }
    println!();
    print!("| --- |");
    for _ in 0..10 {
        print!(" ---: |");
    }
    println!();
    for (instance, spans) in &rows {
        print!("| {} |", instance);
        for count in spans.deciles {
            print!(" {:.1}% |", spans.share(count));
        }
        println!();
    }
    print!("| **all** |");
    for count in total.deciles {
        print!(" {:.1}% |", total.share(count));
    }
    println!();
    println!();
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    if arguments.first().map(String::as_str) == Some("list") {
        for instance in DEFAULT {
            println!("{}", instance);
        }
        return;
    }
    let instances: Vec<&str> = if arguments.is_empty() {
        DEFAULT.to_vec()
    } else {
        arguments.iter().map(String::as_str).collect()
    };

    println!("# The pivot's span against its support, in `DenseAccumulator::subtract_scaled`");
    println!();
    println!(
        "`span / support` is the cell updates a contiguous loop over the pivot's span would do \
         for each one"
    );
    println!(
        "the shipped gather/scatter loop does. The 8-lane kernel of §8.3 is worth {:.1}x on a \
         contiguous",
        LANE_SPEEDUP
    );
    println!(
        "span in cache, so a multiplier at or above that is a loss before any code is written, and"
    );
    println!(
        "`projected` — {:.1}x over the multiplier — is above 1.0 exactly where a wide contiguous",
        LANE_SPEEDUP
    );
    println!("kernel would win. It assumes the lane win carries to a span this short, which the");
    println!("span columns are there to doubt.");
    println!();

    for plan in [Plan::Unstructured, Plan::Structured] {
        report(&instances, plan);
    }
}
