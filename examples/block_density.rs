//! Whether any F4 matrix Zeebra really builds has a block dense enough for a dense tile kernel.
//!
//! #225 asks this of a GPU proposal, and the answer is a count, not a timing: so nothing here is
//! timed, every figure is exact, and it reproduces at any commit where the corpus has not moved.
//!
//! Two matrices per corpus entry, because a dense kernel would be handed either:
//!
//! - **As built**, in the structured arrangement `[A B; C D]` that `ReductionStrategy::Structured`
//!   eliminates: reducer rows first, ascending by leading column, then the pair rows.
//! - **The pair-row residual** `D' = D - C A^-1 B`: each pair row reduced by the reducer block,
//!   restricted to the columns no reducer leads. This is the Faugère–Lachartre split's dense
//!   candidate — the part a GPU echelon would get after the sparse triangular solve stayed on the
//!   CPU — and it is reported before and after its own echelon, since that echelon is where fill-in
//!   happens.
//!
//! Each is tiled into `TILE x TILE` cells. A global density says nothing about tiles (a few full
//! rows are a fraction of a percent overall), so the figures are the densest tile, and the share of
//! all nonzeros that lie in tiles at least half full — the work a dense tile kernel would get.
//!
//! ```text
//! cargo run --release --example block_density          # the default corpus
//! cargo run --release --example block_density -- large # the explicit large captures
//! cargo run --release --example block_density -- split mq-random-10        # timed, see below
//! cargo run --release --features research-work --example block_density -- split-large mq-random-14
//! ```
//!
//! `split` is the one timed mode (#803), and its figures need the benchmark lock. It asks whether a
//! device that did the residual's echelon for free could halve a batch: the CPU would still owe the
//! sweep that produces `D'`, so the ceiling is the production batch time over the sweep time. Six
//! arms per entry, interleaved with rotated order: the production route (echelon, then the
//! candidate-only backward pass `F4Options::recommended` drives), the full-RREF route
//! `eliminate_to(.., RowForm::Reduced, ..)`, the forward pass alone, the full sweep (this file's
//! reference `residual`, not a shipped kernel), the shipped backend's echelon of `D'` alone, and the
//! Faugère–Lachartre order (sweep, then echelon and back-substitution of `D'` only), whose candidate
//! rows are asserted equal to production's. With `research-work` it also prices the sweep at the
//! forward pass's own nanoseconds per coefficient product, since the reference sweep is not an
//! optimized kernel; hooks sit in the hot loop, so take times from a stock build.

use std::{
    collections::HashMap,
    hint::black_box,
    time::{Duration, Instant},
};

use zeebra::{
    grobner::f4::{
        candidate::{finish, WORKSPACE_LIMIT},
        macaulay::MacaulayMatrix,
        matrix_corpus::{
            walk_corpus, walk_large_corpus, CapturedMatrix, CorpusVisitor, MatrixSpec,
        },
        options::ReductionStrategy,
        structured::{eliminate_to, BlockPlan, RowForm},
        symbolic::RowKind,
    },
    linalg::{
        row_echelon_with,
        sparse::{back_substitute_pivots_within, SparseMatrix, SparseRow},
        Backend,
    },
    FiniteField,
};

/// A GPU tile's edge: a warp-sized dense block, the granularity `elimination_density.rs` reports.
const TILE: usize = 64;

/// A tile at least this full is one a dense kernel would take.
const DENSE_TILE: f64 = 0.5;

/// Tile occupancy of a matrix given as each row's nonzero columns, in row order.
#[derive(Clone, Debug, Default, PartialEq)]
struct Tiles {
    /// Fraction of cells nonzero in the fullest tile, edge tiles counted by their real area.
    max: f64,
    /// Tiles holding at least one nonzero.
    occupied: usize,
    /// Tiles at least `DENSE_TILE` full.
    dense: usize,
    /// Share of the matrix's nonzeros lying in those tiles.
    dense_share: f64,
}

fn tiles(rows: &[Vec<usize>], num_columns: usize) -> Tiles {
    let mut counts: HashMap<(usize, usize), usize> = HashMap::new();
    let mut total = 0usize;
    for (row, columns) in rows.iter().enumerate() {
        for column in columns {
            *counts.entry((row / TILE, column / TILE)).or_default() += 1;
            total += 1;
        }
    }
    let area = |(r, c): (usize, usize)| {
        let height = TILE.min(rows.len() - r * TILE);
        let width = TILE.min(num_columns - c * TILE);
        (height * width) as f64
    };
    let mut out = Tiles {
        occupied: counts.len(),
        ..Tiles::default()
    };
    let mut in_dense = 0usize;
    for (&tile, &count) in &counts {
        let fill = count as f64 / area(tile);
        out.max = out.max.max(fill);
        if fill >= DENSE_TILE {
            out.dense += 1;
            in_dense += count;
        }
    }
    out.dense_share = if total == 0 {
        0.0
    } else {
        in_dense as f64 / total as f64
    };
    out
}

fn columns_of<F: FiniteField>(rows: &[SparseRow<F>]) -> Vec<Vec<usize>> {
    rows.iter()
        .map(|row| row.entries().iter().map(|(column, _)| *column).collect())
        .collect()
}

/// `D - C A^-1 B` on the non-pivot columns, renumbered densely, and that column count.
///
/// `reducers` must have distinct leading columns with unit leading coefficients — the
/// reducer-block invariant `src/grobner/f4/structured.rs` checks — and is asserted here too, since
/// a violation would silently understate the residual.
fn residual<F: FiniteField>(
    reducers: &[&SparseRow<F>],
    pairs: &[&SparseRow<F>],
    num_columns: usize,
) -> (Vec<SparseRow<F>>, usize, usize) {
    let mut pivot: Vec<Option<usize>> = vec![None; num_columns];
    for (index, row) in reducers.iter().enumerate() {
        let lead = row.leading_column().expect("a reducer row is nonzero");
        assert_eq!(
            row.leading_coefficient(),
            Some(F::one()),
            "unit reducer pivot"
        );
        assert!(
            pivot[lead].replace(index).is_none(),
            "distinct reducer leads"
        );
    }
    let mut renumber = vec![usize::MAX; num_columns];
    let mut free = 0usize;
    for (column, slot) in renumber.iter_mut().enumerate() {
        if pivot[column].is_none() {
            *slot = free;
            free += 1;
        }
    }

    let mut multiply_adds = 0usize;
    let mut accumulator = vec![F::zero(); num_columns];
    let mut out = Vec::with_capacity(pairs.len());
    for row in pairs {
        let Some(lead) = row.leading_column() else {
            out.push(SparseRow::zero());
            continue;
        };
        for (column, value) in row.entries() {
            accumulator[*column] = *value;
        }
        // A reducer's entries lie at or right of its lead, so one ascending sweep suffices.
        for column in lead..num_columns {
            let factor = accumulator[column];
            if factor.is_zero() {
                continue;
            }
            if let Some(index) = pivot[column] {
                multiply_adds += reducers[index].nonzeros();
                for (target, value) in reducers[index].entries() {
                    accumulator[*target] -= factor * *value;
                }
            }
        }
        let mut entries = Vec::new();
        for (column, value) in accumulator.iter_mut().enumerate().skip(lead) {
            if !value.is_zero() {
                debug_assert!(pivot[column].is_none(), "pivot columns are cleared");
                entries.push((renumber[column], *value));
            }
            *value = F::zero();
        }
        out.push(SparseRow::new(&entries));
    }
    (out, free, multiply_adds)
}

/// Multiply-adds a dense echelon of an `rows x columns` block of rank `rank` performs.
///
/// Pivot `k` updates every row below it across every column right of it; with `rank` pivots the
/// count is the sum of `(rows - k - 1) * (columns - k - 1)`. This is what a dense tile kernel would
/// execute on the block whatever its sparsity, so it is the work a GPU would be handed.
fn dense_echelon_work(rows: usize, columns: usize, rank: usize) -> usize {
    (0..rank)
        .map(|k| rows.saturating_sub(k + 1) * columns.saturating_sub(k + 1))
        .sum()
}

/// One corpus entry's report line.
#[derive(Debug)]
struct Report {
    label: &'static str,
    rows: usize,
    columns: usize,
    density: f64,
    reducer_rows: usize,
    built: Tiles,
    residual_rows: usize,
    residual_columns: usize,
    residual_density: f64,
    residual: Tiles,
    rank: usize,
    sparse_work: usize,
    dense_work: usize,
    echelon_density: f64,
    echelon: Tiles,
}

fn measure<F: FiniteField>(
    label: &'static str,
    matrix: &SparseMatrix<F>,
    kinds: &[RowKind],
) -> Report {
    let mut reducers: Vec<&SparseRow<F>> = Vec::new();
    let mut pairs: Vec<&SparseRow<F>> = Vec::new();
    for (row, kind) in matrix.rows().iter().zip(kinds) {
        match kind {
            RowKind::Reducer => reducers.push(row),
            RowKind::PairComponent { .. } => pairs.push(row),
        }
    }
    reducers.sort_by_key(|row| row.leading_column());

    let arranged: Vec<Vec<usize>> = columns_of(
        &reducers
            .iter()
            .chain(pairs.iter())
            .map(|row| (*row).clone())
            .collect::<Vec<_>>(),
    );
    let built = tiles(&arranged, matrix.num_columns());

    let (rows, free, sparse_work) = residual(&reducers, &pairs, matrix.num_columns());
    let mut residual = SparseMatrix::new(free, rows);
    let residual_density = residual.density();
    let residual_tiles = tiles(&columns_of(residual.rows()), free);

    let statistics = row_echelon_with(Backend::Sparse, &mut residual, usize::MAX)
        .expect("an unbounded echelon cannot refuse");
    residual.sort_rows_by_leading_column();
    let echelon_rows: Vec<Vec<usize>> = columns_of(residual.rows())
        .into_iter()
        .filter(|row| !row.is_empty())
        .collect();
    let echelon_cells = (echelon_rows.len() * free).max(1) as f64;
    let echelon_nonzeros: usize = echelon_rows.iter().map(Vec::len).sum();

    Report {
        label,
        rows: matrix.num_rows(),
        columns: matrix.num_columns(),
        density: matrix.density(),
        reducer_rows: reducers.len(),
        built,
        residual_rows: pairs.len(),
        residual_columns: free,
        residual_density,
        residual: residual_tiles,
        rank: statistics.rank,
        sparse_work,
        dense_work: dense_echelon_work(pairs.len(), free, statistics.rank),
        echelon_density: echelon_nonzeros as f64 / echelon_cells,
        echelon: tiles(&echelon_rows, free),
    }
}

struct Collect(Vec<Report>);

impl CorpusVisitor for Collect {
    fn visit<const N: usize, F: FiniteField>(
        &mut self,
        spec: &MatrixSpec,
        captured: &CapturedMatrix<N, F>,
    ) {
        let kinds: Vec<RowKind> = captured
            .matrix
            .row_origins()
            .iter()
            .map(|origin| origin.kind)
            .collect();
        let report = measure(spec.label, captured.matrix.matrix(), &kinds);
        eprintln!("measured {}", spec.label);
        self.0.push(report);
    }
}

/// Repetitions per arm in `split` mode. Odd, so the median is an observation.
const REPS: usize = 5;

/// `split` mode's visitor: times the entries whose label contains `filter`.
struct Split {
    filter: String,
    matched: usize,
}

fn median_range(samples: &mut [Duration]) -> (f64, f64, f64) {
    samples.sort();
    let ms = |d: Duration| d.as_secs_f64() * 1e3;
    (
        ms(samples[samples.len() / 2]),
        ms(samples[0]),
        ms(samples[samples.len() - 1]),
    )
}

impl CorpusVisitor for Split {
    fn visit<const N: usize, F: FiniteField>(
        &mut self,
        spec: &MatrixSpec,
        captured: &CapturedMatrix<N, F>,
    ) {
        if !spec.label.contains(self.filter.as_str()) {
            return;
        }
        self.matched += 1;
        let options = spec.options.options();
        let plan = match options.reduction {
            ReductionStrategy::Unstructured => BlockPlan::Baseline,
            ReductionStrategy::Structured => BlockPlan::ReducersFirstBlock,
        };
        let form = if options.reduce_batch_rows {
            RowForm::Reduced
        } else {
            RowForm::Echelon
        };
        let budget = options.live_entry_allowance::<F>();
        let backend = options.elimination;
        // A refusal is a result, not a failure: the large entry is captured under a raised budget
        // that its own elimination still crosses. It is reported, and the arms then run unbounded.
        let allowance = match eliminate_to(
            plan,
            form,
            backend,
            &mut captured.matrix.clone(),
            budget,
        ) {
            Ok(_) => budget,
            Err(live) => {
                println!(
                    "|   | **refused** under its own {} live-entry budget at {} live entries; arms below run unbounded | | | | | |",
                    budget, live
                );
                usize::MAX
            }
        };

        let matrix = captured.matrix.matrix();
        let mut reducers: Vec<&SparseRow<F>> = Vec::new();
        let mut pairs: Vec<&SparseRow<F>> = Vec::new();
        for (row, origin) in matrix.rows().iter().zip(captured.matrix.row_origins()) {
            match origin.kind {
                RowKind::Reducer => reducers.push(row),
                RowKind::PairComponent { .. } => pairs.push(row),
            }
        }
        reducers.sort_by_key(|row| row.leading_column());
        let (residual_rows, free, sweep_products) =
            residual(&reducers, &pairs, matrix.num_columns());

        // The last arm is the Faugère–Lachartre order end to end: the full sweep, then the shipped
        // backend's echelon of D' and the shipped back-substitution over D' alone. It produces the
        // reduced candidate rows without touching a reducer row; `same_candidates` checks that they
        // are the production batch's, coefficient for coefficient.
        let faugere_lachartre = || {
            let (rows, free, _) = residual(&reducers, &pairs, matrix.num_columns());
            let mut block = SparseMatrix::new(free, rows);
            let mut statistics = row_echelon_with(backend, &mut block, usize::MAX)
                .expect("an unbounded echelon cannot refuse");
            back_substitute_pivots_within(&mut block, usize::MAX, &mut statistics)
                .expect("an unbounded pass cannot refuse");
            block
        };

        // The production backward pass finishes only candidate rows, so a reducer row keeps its
        // echelon tail; `eliminate_to(.., RowForm::Reduced, ..)` is the full-RREF route F4 left.
        // A candidate leads with a monomial no input row led with: neither a reducer's lead nor a
        // pair's lcm, which is what every pair row leads with as built. Selecting only the
        // reducer leads (as #803 did) also finishes the rows left leading at an lcm, which F4
        // never does: 417 ms of backward pass on mq-random-10 where F4 spends 6 ms (#816).
        let lcm_columns: Vec<usize> = pairs
            .iter()
            .filter_map(|row| row.leading_column())
            .collect();
        let selected: Vec<bool> = {
            let mut selected = vec![true; matrix.num_columns()];
            for row in &reducers {
                selected[row.leading_column().expect("a reducer row is nonzero")] = false;
            }
            for &column in &lcm_columns {
                selected[column] = false;
            }
            selected
        };
        let production = |copy: &mut MacaulayMatrix<N, F>| {
            let mut outcome = eliminate_to(plan, RowForm::Echelon, backend, copy, allowance)
                .expect("within the allowance the live run used");
            if form == RowForm::Reduced {
                finish(
                    copy.matrix_mut(),
                    &selected,
                    allowance,
                    WORKSPACE_LIMIT,
                    &mut outcome.statistics,
                )
                .expect("within the allowance the live run used");
            }
            outcome.statistics.rank
        };

        // production, full RREF, forward only, reference sweep, echelon of D', Faugère–Lachartre
        const ARMS: usize = 6;
        let mut times: [Vec<Duration>; ARMS] = Default::default();
        let mut ranks = [0usize; 2];
        for repetition in 0..REPS {
            for offset in 0..ARMS {
                let arm = (repetition + offset) % ARMS;
                match arm {
                    0 => {
                        let mut copy = captured.matrix.clone();
                        let started = Instant::now();
                        ranks[0] = production(&mut copy);
                        times[0].push(started.elapsed());
                        black_box(&copy);
                    }
                    1 | 2 => {
                        let mut copy = captured.matrix.clone();
                        let form = if arm == 1 {
                            RowForm::Reduced
                        } else {
                            RowForm::Echelon
                        };
                        let started = Instant::now();
                        eliminate_to(plan, form, backend, &mut copy, allowance)
                            .expect("within the allowance the live run used");
                        times[arm].push(started.elapsed());
                        black_box(&copy);
                    }
                    3 => {
                        let started = Instant::now();
                        let swept = residual(&reducers, &pairs, matrix.num_columns());
                        times[3].push(started.elapsed());
                        black_box(&swept);
                    }
                    4 => {
                        let mut block = SparseMatrix::new(free, residual_rows.clone());
                        let started = Instant::now();
                        let statistics = row_echelon_with(backend, &mut block, usize::MAX)
                            .expect("an unbounded echelon cannot refuse");
                        times[4].push(started.elapsed());
                        ranks[1] = statistics.rank;
                    }
                    _ => {
                        let started = Instant::now();
                        let block = faugere_lachartre();
                        times[5].push(started.elapsed());
                        black_box(&block);
                    }
                }
            }
        }
        // The pair rows' rank in the batch is the residual's rank: the reducer block is independent
        // and every pair row's reducer-column content is in its span.
        assert_eq!(
            ranks[0],
            reducers.len() + ranks[1],
            "{}: residual rank disagrees with the batch",
            spec.label
        );

        if form == RowForm::Reduced {
            let mut shipped = captured.matrix.clone();
            production(&mut shipped);
            same_candidates(
                spec.label,
                shipped.matrix(),
                &reducers,
                &lcm_columns,
                &faugere_lachartre(),
            );
        }

        let [shipped, full, forward, sweep, echelon, ordered] =
            times.map(|mut arm| median_range(&mut arm));
        let cell =
            |(median, low, high): (f64, f64, f64)| format!("{median:.1} [{low:.1}, {high:.1}]");
        println!(
            "| {} | {} x {} | {:?} | {} | {} | {} | {} | {} | {} | {} |",
            spec.label,
            matrix.num_rows(),
            matrix.num_columns(),
            backend,
            cell(shipped),
            cell(full),
            cell(forward),
            cell(sweep),
            cell(echelon),
            cell(ordered),
            sweep_products,
        );
        println!(
            "|   | ceilings over production: reference sweep {:.2}x, Faugère–Lachartre order {:.2}x; full RREF is {:.2}x production | | | | | | | | | |",
            shipped.0 / sweep.0,
            shipped.0 / ordered.0,
            full.0 / shipped.0,
        );
        products(
            spec.label,
            captured,
            plan,
            backend,
            allowance,
            sweep_products,
            forward.0,
            shipped.0,
        );
    }
}

/// Assert that the shipped reduced batch and the Faugère–Lachartre order yield the same candidates.
///
/// A candidate is a row whose leading column no reducer leads. Both forms are reduced row echelon
/// over the same row space with the same pivot set, which is unique, so equality is required and
/// not merely expected; anything less is a defect in one of the two routes.
fn same_candidates<F: FiniteField>(
    label: &str,
    shipped: &SparseMatrix<F>,
    reducers: &[&SparseRow<F>],
    lcm_columns: &[usize],
    ordered: &SparseMatrix<F>,
) {
    let mut led = vec![false; shipped.num_columns()];
    for row in reducers {
        led[row.leading_column().expect("a reducer row is nonzero")] = true;
    }
    let free: Vec<usize> = (0..shipped.num_columns()).filter(|&c| !led[c]).collect();
    // Rows still leading at an lcm are not candidates, and F4 leaves them unfinished.
    let candidate = |c: usize| !led[c] && !lcm_columns.contains(&c);
    let mut from_shipped: Vec<Vec<(usize, F)>> = shipped
        .rows()
        .iter()
        .filter(|row| row.leading_column().is_some_and(candidate))
        .map(|row| row.entries().to_vec())
        .collect();
    let mut from_ordered: Vec<Vec<(usize, F)>> = ordered
        .rows()
        .iter()
        .filter(|row| !row.is_zero())
        .map(|row| -> Vec<(usize, F)> {
            row.entries().iter().map(|(c, v)| (free[*c], *v)).collect()
        })
        .filter(|row| candidate(row[0].0))
        .collect();
    from_shipped.sort_by_key(|row| row[0].0);
    from_ordered.sort_by_key(|row| row[0].0);
    assert!(
        from_shipped == from_ordered,
        "{}: the two routes' candidates differ ({} against {} rows)",
        label,
        from_shipped.len(),
        from_ordered.len()
    );
    println!(
        "|   | candidates identical: {} rows, coefficient for coefficient | | | | | |",
        from_shipped.len()
    );
}

/// The forward pass's coefficient products split by pivot origin, and the gate it implies.
#[cfg(feature = "research-work")]
#[allow(clippy::too_many_arguments)]
fn products<const N: usize, F: FiniteField>(
    label: &str,
    captured: &CapturedMatrix<N, F>,
    plan: BlockPlan,
    backend: Backend,
    allowance: usize,
    sweep_products: usize,
    forward_ms: f64,
    shipped_ms: f64,
) {
    let mut copy = captured.matrix.clone();
    let (_, report) = zeebra::linalg::work::measure_discovery(|| {
        eliminate_to(plan, RowForm::Echelon, backend, &mut copy, allowance)
            .expect("within the allowance the live run used")
    });
    let rows = report
        .batches
        .iter()
        .chain(std::iter::once(&report.outside_batch))
        .flat_map(|batch| batch.discovery.iter());
    let (mut inherited, mut discovered) = (0usize, 0usize);
    for row in rows {
        inherited += row.inherited_products;
        discovered += row.discovered_products;
    }
    let total = (inherited + discovered).max(1);
    let per_product = forward_ms / total as f64;
    let sweep_estimate = sweep_products as f64 * per_product;
    println!(
        "|   | forward products: inherited {} + discovered {} ({}); sweep at {:.3} ns/product = {:.1} ms; estimated ceiling {:.2}x | | | | | |",
        inherited,
        discovered,
        pct(discovered as f64 / total as f64),
        per_product * 1e6,
        sweep_estimate,
        shipped_ms / sweep_estimate,
    );
    let _ = label;
}

#[cfg(not(feature = "research-work"))]
#[allow(clippy::too_many_arguments)]
fn products<const N: usize, F: FiniteField>(
    _label: &str,
    _captured: &CapturedMatrix<N, F>,
    _plan: BlockPlan,
    _backend: Backend,
    _allowance: usize,
    _sweep_products: usize,
    _forward_ms: f64,
    _shipped_ms: f64,
) {
}

fn split(large: bool, filter: String) {
    println!("{REPS} interleaved repetitions per arm; medians [min, max] in ms.\n");
    println!("| entry | rows x cols | backend | production batch | full RREF | forward only | reference sweep | echelon of D' | Faugère–Lachartre order | sweep multiply-adds |");
    println!("|---|---|---|---:|---:|---:|---:|---:|---:|---:|");
    let mut visitor = Split { filter, matched: 0 };
    let walked = if large {
        walk_large_corpus(&mut visitor)
    } else {
        walk_corpus(&mut visitor)
    };
    if let Err(error) = walked {
        eprintln!("CORPUS DRIFTED: {}", error);
        std::process::exit(1);
    }
    if visitor.matched == 0 {
        eprintln!("no corpus entry matched");
        std::process::exit(64);
    }
}

fn pct(value: f64) -> String {
    format!("{:.1}%", 100.0 * value)
}

fn main() {
    let mode = std::env::args().nth(1);
    if let Some(large) = match mode.as_deref() {
        Some("split") => Some(false),
        Some("split-large") => Some(true),
        _ => None,
    } {
        split(large, std::env::args().nth(2).unwrap_or_default());
        return;
    }
    let large = mode.as_deref() == Some("large");
    let mut collect = Collect(Vec::new());
    let walked = if large {
        walk_large_corpus(&mut collect)
    } else {
        walk_corpus(&mut collect)
    };
    if let Err(error) = walked {
        eprintln!("CORPUS DRIFTED: {}", error);
        std::process::exit(1);
    }

    println!(
        "Tiles are {TILE}x{TILE}; \"dense\" means at least {} full.\n",
        pct(DENSE_TILE)
    );
    println!("## As built, reducers first: [A B; C D]\n");
    println!("| entry | rows x cols | reducer rows | density | max tile | dense tiles / occupied | nz in dense tiles |");
    println!("|---|---|---:|---:|---:|---:|---:|");
    for r in &collect.0 {
        println!(
            "| {} | {} x {} | {} | {} | {} | {} / {} | {} |",
            r.label,
            r.rows,
            r.columns,
            r.reducer_rows,
            pct(r.density),
            pct(r.built.max),
            r.built.dense,
            r.built.occupied,
            pct(r.built.dense_share),
        );
    }
    println!("\n## Pair-row residual D' = D - C A^-1 B, before and after its own echelon\n");
    println!("| entry | D' rows x cols | D' density | D' max tile | D' nz in dense tiles | rank | echelon density | echelon max tile | echelon nz in dense tiles |");
    println!("|---|---|---:|---:|---:|---:|---:|---:|---:|");
    for r in &collect.0 {
        println!(
            "| {} | {} x {} | {} | {} | {} | {} | {} | {} | {} |",
            r.label,
            r.residual_rows,
            r.residual_columns,
            pct(r.residual_density),
            pct(r.residual.max),
            pct(r.residual.dense_share),
            r.rank,
            pct(r.echelon_density),
            pct(r.echelon.max),
            pct(r.echelon.dense_share),
        );
    }
    println!(
        "\n## Where the multiply-adds are: sparse C A^-1 B sweep against a dense echelon of D'\n"
    );
    println!("| entry | sweep multiply-adds (exact) | dense D' echelon multiply-adds | dense share | D' cells |");
    println!("|---|---:|---:|---:|---:|");
    for r in &collect.0 {
        let total = (r.sparse_work + r.dense_work).max(1) as f64;
        println!(
            "| {} | {} | {} | {} | {} |",
            r.label,
            r.sparse_work,
            r.dense_work,
            pct(r.dense_work as f64 / total),
            r.residual_rows * r.residual_columns,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zeebra::fields::Zp7;

    fn row(entries: &[(usize, u64)]) -> SparseRow<Zp7> {
        let entries: Vec<(usize, Zp7)> = entries.iter().map(|&(c, v)| (c, Zp7::new(v))).collect();
        SparseRow::new(&entries)
    }

    // A full 64x64 block reads as one dense tile holding every nonzero.
    #[test]
    fn a_full_tile_is_dense_and_holds_everything() {
        let rows: Vec<Vec<usize>> = (0..TILE).map(|_| (0..TILE).collect()).collect();
        let t = tiles(&rows, TILE);
        assert_eq!(t.occupied, 1);
        assert_eq!(t.dense, 1);
        assert_eq!(t.max, 1.0);
        assert_eq!(t.dense_share, 1.0);
    }

    // An edge tile is measured against its real area, so a 2x2 remainder that is full counts as full.
    #[test]
    fn edge_tiles_use_their_real_area() {
        let rows: Vec<Vec<usize>> = (0..TILE + 2)
            .map(|r| {
                if r >= TILE {
                    vec![TILE, TILE + 1]
                } else {
                    vec![]
                }
            })
            .collect();
        let t = tiles(&rows, TILE + 2);
        assert_eq!(t.occupied, 1);
        assert_eq!(t.max, 1.0);
    }

    // A diagonal spreads one nonzero per row, so no tile is dense however large the matrix.
    #[test]
    fn a_diagonal_has_no_dense_tile() {
        let rows: Vec<Vec<usize>> = (0..4 * TILE).map(|r| vec![r]).collect();
        let t = tiles(&rows, 4 * TILE);
        assert_eq!(t.dense, 0);
        assert_eq!(t.dense_share, 0.0);
        assert_eq!(t.occupied, 4);
    }

    // The residual clears every reducer-led column and keeps the rest, renumbered.
    #[test]
    fn residual_is_the_schur_complement_on_free_columns() {
        // Columns 0..4; reducers lead columns 0 and 2. Pair row x0 + 2x1 + 3x2 + x3.
        let r0 = row(&[(0, 1), (1, 1)]);
        let r2 = row(&[(2, 1), (3, 2)]);
        let pair = row(&[(0, 1), (1, 2), (2, 3), (3, 1)]);
        let (out, free, work) = residual(&[&r0, &r2], &[&pair], 4);
        assert_eq!(free, 2);
        // One subtraction of r0 (2 entries) and one of r2 (2 entries).
        assert_eq!(work, 4);
        // Subtract r0: 0 + 1x1 + 3x2 + x3. Subtract 3*r2: x1 + (1 - 6)x3 = x1 + 2x3 mod 7.
        assert_eq!(out, vec![row(&[(0, 1), (1, 2)])]);
    }

    // A pair row in the reducers' span leaves a zero residual.
    #[test]
    fn a_dependent_pair_row_leaves_nothing() {
        let r0 = row(&[(0, 1), (1, 3)]);
        let pair = row(&[(0, 2), (1, 6)]);
        let (out, free, _) = residual(&[&r0], &[&pair], 2);
        assert_eq!(free, 1);
        assert!(out[0].is_zero());
    }

    /// The fully reduced batch of `residual_is_the_schur_complement_on_free_columns`, by hand.
    fn shipped_by_hand() -> SparseMatrix<Zp7> {
        // Pivot x1 + 2x3 clears column 1 from r0: x0 + x1 - (x1 + 2x3) = x0 + 5x3.
        SparseMatrix::new(
            4,
            vec![
                row(&[(0, 1), (3, 5)]),
                row(&[(2, 1), (3, 2)]),
                row(&[(1, 1), (3, 2)]),
            ],
        )
    }

    // The sweep, echelon and back-substitution of D' alone reproduce the full reduction's candidate.
    #[test]
    fn faugere_lachartre_order_matches_the_full_reduction() {
        let r0 = row(&[(0, 1), (1, 1)]);
        let r2 = row(&[(2, 1), (3, 2)]);
        let pair = row(&[(0, 1), (1, 2), (2, 3), (3, 1)]);
        let (rows, free, _) = residual(&[&r0, &r2], &[&pair], 4);
        let mut block = SparseMatrix::new(free, rows);
        let mut statistics = row_echelon_with(Backend::Adaptive, &mut block, usize::MAX).unwrap();
        back_substitute_pivots_within(&mut block, usize::MAX, &mut statistics).unwrap();
        same_candidates("hand", &shipped_by_hand(), &[&r0, &r2], &[], &block);
    }

    // A candidate differing in one coefficient is a defect, not a tolerance.
    #[test]
    #[should_panic(expected = "candidates differ")]
    fn a_differing_candidate_is_caught() {
        let r0 = row(&[(0, 1), (1, 1)]);
        let r2 = row(&[(2, 1), (3, 2)]);
        let wrong = SparseMatrix::new(2, vec![row(&[(0, 1), (1, 3)])]);
        same_candidates("hand", &shipped_by_hand(), &[&r0, &r2], &[], &wrong);
    }

    // A full-rank 3x3 dense echelon: pivot 0 updates 2x2 cells, pivot 1 updates 1x1, pivot 2 none.
    #[test]
    fn dense_echelon_work_counts_the_trailing_updates() {
        assert_eq!(dense_echelon_work(3, 3, 3), 5);
        assert_eq!(dense_echelon_work(3, 3, 0), 0);
    }
}
