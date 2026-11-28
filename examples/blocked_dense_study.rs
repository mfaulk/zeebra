//! #1193: blocked dense elimination on the dense residual of a captured F4 batch.
//!
//! ```text
//! blocked_dense_study lane    <archive.zmat> <vars> <gf31|gf32003>
//! blocked_dense_study split   <archive.zmat> <vars> <gf31|gf32003> [--winograd-from N] [--leaf N]
//!                             [--lane-residual] [--accumulator-sweep] [--verify]
//! blocked_dense_study counts  <archive.zmat> <vars> <gf31|gf32003>    (needs research-work)
//! blocked_dense_study gemm    <gf31|gf32003> <size>[,<size>...] [--winograd-from N]
//! ```
//!
//! `lane` times the shipped lane kernel's forward pass over the whole batch, reducers first. `split`
//! times the sparse top (every pair row swept against the reducer block in `f64` accumulators,
//! `D' = D - C A^-1 B`), then the blocked reduced echelon form of `D'`. `--lane-residual` also times
//! the lane kernel's forward pass and the sparse back-substitution on `D'`, and checks both reduced
//! forms agree entry for entry. `--accumulator-sweep` also times the shipped sweep and checks it
//! gives the same `D'`. `--verify` also runs the lane kernel and a full back-substitution over the
//! whole batch and checks that its rows leading outside the reducer block are exactly the blocked
//! result. `counts` counts the coefficient products of the shipped forward pass, split by pivot
//! origin, and of the shipped sweep. `gemm` times square products. One JSON line per run.
use std::{fs::File, io::BufReader, time::Instant};

use zeebra::{
    fields::{Zp31, Zp32003},
    grobner::f4::macaulay::io::{read_matrix, ReadLimits},
    grobner::f4::matrix_corpus::digest_of,
    linalg::{
        blocked::{
            multiply, reduced_echelon, sweep_to_dense, to_sparse, BlockedCounts, BlockedOptions,
            DenseMatrix, Modulus,
        },
        echelon::sweep_rows_against_pivots,
        lane::LaneKernel,
        sparse::{back_substitute_pivots_within, SparseMatrix, SparseRow},
    },
    FiniteField,
};

struct Args {
    arm: String,
    path: String,
    vars: String,
    field: String,
    options: BlockedOptions,
    lane_residual: bool,
    accumulator_sweep: bool,
    verify: bool,
}

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    if raw.first().map(String::as_str) == Some("gemm") {
        return gemm(&raw[1..]);
    }
    if raw.len() < 4 {
        eprintln!("usage: see the module comment");
        std::process::exit(64);
    }
    let mut args = Args {
        arm: raw[0].clone(),
        path: raw[1].clone(),
        vars: raw[2].clone(),
        field: raw[3].clone(),
        options: BlockedOptions::default(),
        lane_residual: false,
        accumulator_sweep: false,
        verify: false,
    };
    let mut rest = raw[4..].iter();
    while let Some(flag) = rest.next() {
        let mut value = || {
            rest.next()
                .expect("a value")
                .parse::<usize>()
                .expect("a count")
        };
        match flag.as_str() {
            "--winograd-from" => args.options.winograd_from = value(),
            "--leaf" => args.options.leaf_rows = value(),
            "--lane-residual" => args.lane_residual = true,
            "--accumulator-sweep" => args.accumulator_sweep = true,
            "--verify" => args.verify = true,
            other => panic!("unknown flag {other}"),
        }
    }
    macro_rules! dispatch {
        ($($n:literal),*) => {
            match (args.vars.as_str(), args.field.as_str()) {
                $(
                    (stringify!($n), "gf31") => run::<$n, Zp31>(&args),
                    (stringify!($n), "gf32003") => run::<$n, Zp32003>(&args),
                )*
                _ => panic!("unsupported vars/field {} {}", args.vars, args.field),
            }
        };
    }
    dispatch!(12, 15, 18, 20);
}

fn load<const N: usize, F: FiniteField>(path: &str) -> (SparseMatrix<F>, usize, String) {
    let limits = ReadLimits {
        max_rows: 1 << 24,
        max_columns: 1 << 24,
        max_nonzeros: 1 << 31,
        ..ReadLimits::default()
    };
    let file = File::open(path).expect("archive opens");
    let mut matrix =
        read_matrix::<N, F>(&mut BufReader::with_capacity(1 << 20, file), limits).expect("loads");
    let digest = digest_of(&matrix);
    let split = matrix.partition_reducers_first();
    (matrix.matrix_mut().clone(), split, digest)
}

fn lane<F: FiniteField>() -> zeebra::linalg::lane::Lane<F> {
    F::small_prime_lane()
        .or_else(F::prime31_lane)
        .expect("a lane prime")
}

/// Nonzero rows sorted by lead.
fn sorted<F: FiniteField>(
    matrix: &SparseMatrix<F>,
    keep: impl Fn(usize) -> bool,
) -> Vec<SparseRow<F>> {
    let mut rows: Vec<SparseRow<F>> = matrix
        .rows()
        .iter()
        .filter(|r| r.leading_column().is_some_and(&keep))
        .cloned()
        .collect();
    rows.sort_by_key(|r| r.leading_column());
    rows
}

fn run<const N: usize, F: FiniteField>(args: &Args) {
    let (mut matrix, split, input_digest) = load::<N, F>(&args.path);
    let (rows, columns) = (matrix.num_rows(), matrix.num_columns());
    let head = format!(
        "\"arm\":\"{}\",\"archive\":\"{}\",\"field\":\"{}\",\"input_digest\":\"{input_digest}\",\
         \"rows\":{rows},\"columns\":{columns},\"reducer_rows\":{split}",
        args.arm, args.path, args.field
    );
    match args.arm.as_str() {
        "lane" => {
            let clock = Instant::now();
            let statistics = LaneKernel::default()
                .reduce_rows_against_pivots(&lane::<F>(), &mut matrix, split, usize::MAX)
                .expect("no budget");
            let seconds = clock.elapsed().as_secs_f64();
            println!(
                "{{{head},\"forward_seconds\":{seconds:.3},\"rank\":{},\"row_operations\":{}}}",
                statistics.rank, statistics.row_operations
            );
        }
        "split" => split_arm::<F>(args, matrix, split, &head),
        "tune" => tune::<F>(matrix, split, &head),
        "counts" => counts::<F>(matrix, split, &head),
        other => panic!("unknown arm {other}"),
    }
}

/// The blocked echelon of one `D'` under each leaf size and crossover, three interleaved rounds
/// with the order rotated, every output checked against the first.
fn tune<F: FiniteField>(matrix: SparseMatrix<F>, split: usize, head: &str) {
    let lane = lane::<F>();
    let modulus = Modulus::new(lane.modulus()).expect("a prime below 2^26");
    let (mut residual, _) = sweep_to_dense(&lane, &matrix, split, &mut BlockedCounts::default());
    drop(matrix);
    residual.retain_nonzero_rows();
    let mut grid = Vec::new();
    for leaf_rows in [32, 64, 128] {
        for winograd_from in [usize::MAX, 512, 1024, 2048] {
            grid.push(BlockedOptions {
                leaf_rows,
                winograd_from,
            });
        }
    }
    let mut reference = None;
    for round in 0..3 {
        for i in 0..grid.len() {
            let options = grid[(i + round * 5) % grid.len()];
            let mut counts = BlockedCounts::default();
            let clock = Instant::now();
            let (echelon, _) = reduced_echelon(modulus, residual.clone(), options, &mut counts);
            let seconds = clock.elapsed().as_secs_f64();
            let residues = echelon.residues();
            match &reference {
                None => reference = Some(residues),
                Some(first) => assert_eq!(first, &residues, "{options:?} differs"),
            }
            println!(
                "{{{head},\"round\":{round},\"leaf_rows\":{},\"winograd_from\":{},\
                 \"blocked_seconds\":{seconds:.3},\"products\":{},\"additions\":{},\
                 \"winograd_splits\":{}}}",
                options.leaf_rows,
                if options.winograd_from == usize::MAX {
                    -1
                } else {
                    options.winograd_from as i64
                },
                counts.products,
                counts.additions,
                counts.winograd_splits,
            );
        }
    }
}

fn split_arm<F: FiniteField>(args: &Args, matrix: SparseMatrix<F>, split: usize, head: &str) {
    let lane = lane::<F>();
    let modulus = Modulus::new(lane.modulus()).expect("a prime below 2^26");
    let columns = matrix.num_columns();
    let mut reducer_lead = vec![false; columns];
    for row in &matrix.rows()[..split] {
        reducer_lead[row.leading_column().expect("a reducer leads")] = true;
    }

    // The sparse top, in f64 accumulators: D' on the free columns, dense.
    let mut sweep_counts = BlockedCounts::default();
    let clock = Instant::now();
    let (mut residual, free) = sweep_to_dense(&lane, &matrix, split, &mut sweep_counts);
    let sweep_seconds = clock.elapsed().as_secs_f64();
    residual.retain_nonzero_rows();
    let residual_entries = residual.nonzeros();
    let cells = residual.rows() * residual.columns();
    let residual_rows = residual.rows();
    // Cells at or right of each row's lead: the part a dense kernel over the active span touches.
    let span_cells: usize = (0..residual_rows)
        .map(|r| residual.columns() - residual.leading_column(r).expect("nonzero"))
        .sum();
    let residual_sparse: Option<SparseMatrix<F>> = (args.lane_residual || args.accumulator_sweep)
        .then(|| to_sparse(&residual, &free, columns));

    // The dense residual, blocked.
    let mut counts = BlockedCounts::default();
    let clock = Instant::now();
    let (echelon, _) = reduced_echelon(modulus, residual, args.options, &mut counts);
    let blocked_seconds = clock.elapsed().as_secs_f64();
    let ours: SparseMatrix<F> = to_sparse(&echelon, &free, columns);
    drop(echelon);
    let ours_digest = digest(&ours);

    let mut tail = String::new();
    if args.accumulator_sweep {
        let mut swept = matrix.clone();
        let clock = Instant::now();
        sweep_rows_against_pivots(&mut swept, split, usize::MAX).expect("no budget");
        let seconds = clock.elapsed().as_secs_f64();
        let theirs: Vec<SparseRow<F>> = swept.rows()[split..]
            .iter()
            .filter(|r| !r.is_zero())
            .cloned()
            .collect();
        assert_eq!(
            &theirs[..],
            residual_sparse.as_ref().unwrap().rows(),
            "the shipped sweep's D' differs"
        );
        tail += &format!(",\"accumulator_sweep_seconds\":{seconds:.3},\"sweeps_agree\":true");
    }
    if args.lane_residual {
        let mut copy = residual_sparse.unwrap();
        let clock = Instant::now();
        let mut statistics = LaneKernel::default()
            .reduce_rows_against_pivots(&lane, &mut copy, 0, usize::MAX)
            .expect("no budget");
        let forward = clock.elapsed().as_secs_f64();
        let clock = Instant::now();
        back_substitute_pivots_within(&mut copy, usize::MAX, &mut statistics).expect("no budget");
        let backward = clock.elapsed().as_secs_f64();
        let theirs = SparseMatrix::new(columns, sorted(&copy, |_| true));
        assert_eq!(theirs, ours, "the lane route's reduced form of D' differs");
        tail += &format!(
            ",\"lane_residual_forward_seconds\":{forward:.3},\
             \"lane_residual_backward_seconds\":{backward:.3},\"lane_residual_agrees\":true"
        );
    }
    if args.verify {
        let mut whole = matrix;
        let clock = Instant::now();
        let mut statistics = LaneKernel::default()
            .reduce_rows_against_pivots(&lane, &mut whole, split, usize::MAX)
            .expect("no budget");
        let forward = clock.elapsed().as_secs_f64();
        back_substitute_pivots_within(&mut whole, usize::MAX, &mut statistics).expect("no budget");
        let theirs = SparseMatrix::new(columns, sorted(&whole, |c| !reducer_lead[c]));
        assert_eq!(
            theirs, ours,
            "the whole batch's reduced rows outside the reducer block differ"
        );
        tail += &format!(",\"verify_lane_forward_seconds\":{forward:.3},\"verified\":true");
    }
    let o = args.options;
    println!(
        "{{{head},\"free_columns\":{},\"residual_rows\":{residual_rows},\
         \"residual_entries\":{residual_entries},\"residual_density\":{:.4},\
         \"residual_span_fraction\":{:.4},\"residual_span_density\":{:.4},\
         \"sweep_seconds\":{sweep_seconds:.3},\"sweep_products\":{},\
         \"blocked_seconds\":{blocked_seconds:.3},\
         \"leaf_rows\":{},\"winograd_from\":{},\"rank\":{},\"products\":{},\"reductions\":{},\
         \"additions\":{},\"winograd_splits\":{},\"classical_products\":{},\"inversions\":{},\
         \"clearing_products\":{},\"output_digest\":\"{ours_digest}\"{tail}}}",
        free.len(),
        residual_entries as f64 / cells.max(1) as f64,
        span_cells as f64 / cells.max(1) as f64,
        residual_entries as f64 / span_cells.max(1) as f64,
        sweep_counts.products,
        o.leaf_rows,
        if o.winograd_from == usize::MAX {
            -1
        } else {
            o.winograd_from as i64
        },
        ours.num_rows(),
        counts.products,
        counts.reductions,
        counts.additions,
        counts.winograd_splits,
        counts.classical_products,
        counts.inversions,
        counts.clearing_products,
    );
}

/// FNV-1a over the rows' `(column, value)` pairs. Agreement is asserted directly; this only names
/// an output across runs.
fn digest<F: FiniteField>(matrix: &SparseMatrix<F>) -> String {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut eat = |bytes: &[u8]| {
        for &b in bytes {
            hash = (hash ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
        }
    };
    for row in matrix.rows() {
        for (c, v) in row.entries() {
            eat(&(*c as u64).to_le_bytes());
            eat(v.to_string().as_bytes());
            eat(b",");
        }
        eat(b";");
    }
    format!("{hash:016x}")
}

#[cfg(feature = "research-work")]
fn counts<F: FiniteField>(matrix: SparseMatrix<F>, split: usize, head: &str) {
    use zeebra::linalg::{reduce_rows_against_pivots_with, work, Backend};
    let total = |report: &work::WorkReport| {
        let mut phase = report.outside_batch.forward;
        for batch in &report.batches {
            phase.accumulate(&batch.forward);
        }
        phase.coefficient_products
    };
    let mut forward = matrix.clone();
    let (_, report) = work::measure_discovery(|| {
        reduce_rows_against_pivots_with(Backend::Adaptive, &mut forward, split, usize::MAX)
            .expect("no budget")
    });
    let (mut inherited, mut discovered) = (0usize, 0usize);
    for row in report
        .batches
        .iter()
        .chain(std::iter::once(&report.outside_batch))
        .flat_map(|batch| batch.discovery.iter())
    {
        inherited += row.inherited_products;
        discovered += row.discovered_products;
    }
    let forward_products = total(&report);
    drop(forward);
    let mut swept = matrix;
    let (_, report) = work::measure(|| {
        sweep_rows_against_pivots(&mut swept, split, usize::MAX).expect("no budget")
    });
    let sweep_products = total(&report);
    let residual = SparseMatrix::new(
        swept.num_columns(),
        swept.rows()[split..]
            .iter()
            .filter(|r| !r.is_zero())
            .cloned()
            .collect(),
    );
    drop(swept);
    let mut copy = residual;
    let (_, report) = work::measure(|| {
        reduce_rows_against_pivots_with(Backend::Adaptive, &mut copy, 0, usize::MAX)
            .expect("no budget")
    });
    let residual_forward_products = total(&report);
    println!(
        "{{{head},\"forward_products\":{forward_products},\"inherited_products\":{inherited},\
         \"discovered_products\":{discovered},\"sweep_products\":{sweep_products},\
         \"residual_forward_products\":{residual_forward_products}}}"
    );
}

#[cfg(not(feature = "research-work"))]
fn counts<F: FiniteField>(_: SparseMatrix<F>, _: usize, _: &str) {
    panic!("the counts arm needs --features research-work");
}

fn gemm(args: &[String]) {
    let prime = match args.first().map(String::as_str) {
        Some("gf31") => 31,
        Some("gf32003") => 32003,
        _ => panic!("gemm <gf31|gf32003> <sizes> [--winograd-from N]"),
    };
    let modulus = Modulus::new(prime).unwrap();
    let sizes: Vec<usize> = args[1].split(',').map(|s| s.parse().unwrap()).collect();
    let mut options = BlockedOptions::default();
    if args.get(2).map(String::as_str) == Some("--winograd-from") {
        options.winograd_from = args[3].parse().unwrap();
    }
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % u64::from(prime)) as u32
    };
    for n in sizes {
        let a: Vec<u32> = (0..n * n).map(|_| next()).collect();
        let b: Vec<u32> = (0..n * n).map(|_| next()).collect();
        let a = DenseMatrix::from_residues(modulus, n, n, &a);
        let b = DenseMatrix::from_residues(modulus, n, n, &b);
        let mut counts = BlockedCounts::default();
        let clock = Instant::now();
        let c = multiply(modulus, &a, &b, options, &mut counts);
        let seconds = clock.elapsed().as_secs_f64();
        let check: u64 = c.residues().iter().map(|&v| u64::from(v)).sum();
        println!(
            "{{\"arm\":\"gemm\",\"prime\":{prime},\"n\":{n},\"winograd_from\":{},\"seconds\":{seconds:.4},\
             \"gflops_classical_equivalent\":{:.2},\"products\":{},\"winograd_splits\":{},\"checksum\":{check}}}",
            if options.winograd_from == usize::MAX { -1 } else { options.winograd_from as i64 },
            2.0 * (n as f64).powi(3) / seconds / 1e9,
            counts.products,
            counts.winograd_splits,
        );
    }
}
