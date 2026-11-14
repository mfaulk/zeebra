//! Sparse matvec throughput per field, storage format, block width and thread count (#87).
//!
//! Every arm runs dependent Krylov steps `X_{t+1} = A X_t`, so nothing overlaps two products that
//! a Wiedemann sequence could not overlap. Ratios are paired per repetition: each repetition also
//! measures each field's L1-resident multiply-add rate and a streaming read bandwidth at every
//! thread count, and a row's `arith%` and `bw%` divide by the ones measured in the same repetition.
//! Traffic is logical: matrix arrays plus each vector read once and written once, the compulsory
//! minimum. No hardware counter is read.
//!
//! ```text
//! taskset -c 0-63 cargo run --release --example sparse_matvec_throughput -- --csv rows.csv
//! cargo run --release --example sparse_matvec_throughput -- --quick
//! ```

#[path = "support/sparse_matvec.rs"]
mod sparse_matvec;

use std::{
    collections::HashMap,
    hint::black_box,
    mem::size_of,
    sync::Barrier,
    thread,
    time::{Duration, Instant},
};

use rand::{rngs::StdRng, Rng, SeedableRng};
use sparse_matvec::{gather, gather_bits, gather_rows, krylov_parallel, scatter, Csr};
use zeebra::{
    fields::{BabyBear, Bn254Fr, Gf256, Zp18446744069414584321, Zp2},
    grobner::fglm::{FglmOptions, MultiplicationOperator, QuotientAlgebra},
    linalg::sparse::{SparseMatrix, SparseRow},
    util::{isa_floor, peak_resident_bytes},
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

struct Config {
    reps: usize,
    min_ms: f64,
    threads: Vec<usize>,
    max_variables: usize,
    widths: Vec<usize>,
    l2_kib: usize,
    l3_mib: usize,
    dram_mib: usize,
    per_row: usize,
    bandwidth_mib: usize,
    csv: Option<String>,
}

impl Config {
    fn parse() -> Self {
        let mut c = Self {
            reps: 5,
            min_ms: 40.0,
            threads: vec![1, 2, 4, 8, 16, 32, 64],
            max_variables: 7,
            widths: vec![1, 2, 4, 8, 16],
            l2_kib: 256,
            l3_mib: 16,
            dram_mib: 512,
            per_row: 8,
            bandwidth_mib: 2048,
            csv: None,
        };
        let mut args = std::env::args().skip(1);
        while let Some(flag) = args.next() {
            if flag == "--quick" {
                (c.reps, c.min_ms, c.max_variables) = (1, 2.0, 5);
                (c.threads, c.widths) = (vec![1, 2], vec![1, 2]);
                (c.l3_mib, c.dram_mib, c.bandwidth_mib) = (1, 4, 16);
                continue;
            }
            let value = args.next().expect("every other flag takes a value");
            let list =
                |v: &str| -> Vec<usize> { v.split(',').map(|t| t.parse().unwrap()).collect() };
            match flag.as_str() {
                "--reps" => c.reps = value.parse().unwrap(),
                "--min-ms" => c.min_ms = value.parse().unwrap(),
                "--threads" => c.threads = list(&value),
                "--widths" => c.widths = list(&value),
                "--max-variables" => c.max_variables = value.parse().unwrap(),
                "--l2-kib" => c.l2_kib = value.parse().unwrap(),
                "--l3-mib" => c.l3_mib = value.parse().unwrap(),
                "--dram-mib" => c.dram_mib = value.parse().unwrap(),
                "--per-row" => c.per_row = value.parse().unwrap(),
                "--bandwidth-mib" => c.bandwidth_mib = value.parse().unwrap(),
                "--csv" => c.csv = Some(value),
                _ => panic!("unknown flag {flag}; see the module documentation"),
            }
        }
        assert!(c.reps > 0 && c.threads.contains(&1) && c.widths.contains(&1));
        c
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Kind {
    Kernel,
    Arith,
    Bandwidth,
}

/// One timed configuration. `run(steps)` performs `steps` dependent applications.
struct Arm {
    kind: Kind,
    field: &'static str,
    matrix: String,
    format: &'static str,
    width: usize,
    threads: usize,
    n: usize,
    nnz: usize,
    /// Compulsory logical bytes per step.
    bytes: usize,
    /// Multiply-adds per step.
    ops: usize,
    steps: usize,
    run: Box<dyn FnMut(usize) -> Duration>,
}

fn timed(mut f: impl FnMut()) -> Duration {
    let start = Instant::now();
    f();
    start.elapsed()
}

fn load() -> f64 {
    std::fs::read_to_string("/proc/loadavg")
        .ok()
        .and_then(|s| s.split_whitespace().next().and_then(|t| t.parse().ok()))
        .unwrap_or(f64::NAN)
}

/// The lex-last operator of `x_i^5 - x_{i+1}`, `x_{N-1}^5 - x_0 - 1`: the digest-pinned family of
/// `examples/wiedemann_conversion.rs`, whose quotient has dimension `5^N`. Already a grevlex basis.
fn real_operator<F: FiniteField, const N: usize>() -> (MultiplicationOperator<F>, Duration) {
    let names: [String; N] = std::array::from_fn(|i| format!("x{i}"));
    let names: [&str; N] = std::array::from_fn(|i| names[i].as_str());
    let basis: Vec<MultivariatePolynomial<N, F>> = (0..N)
        .map(|i| {
            let tail = if i + 1 < N {
                format!("x{}", i + 1)
            } else {
                "x0-1".into()
            };
            MultivariatePolynomial::parse(&format!("x{i}^5-{tail}"), names).unwrap()
        })
        .collect();
    let start = Instant::now();
    let order = MonomialOrder::GradedReverseLexicographic;
    let algebra = QuotientAlgebra::new(&basis, order, &FglmOptions::unbounded()).unwrap();
    let elapsed = start.elapsed();
    (algebra.operator(N - 1).clone(), elapsed)
}

fn columns_of<F: FiniteField>(op: &MultiplicationOperator<F>) -> Vec<Vec<(usize, F)>> {
    (0..op.dimension()).map(|j| op.column_entries(j)).collect()
}

fn nonzero<F: FiniteField>(rng: &mut StdRng) -> F {
    loop {
        let v = F::random(rng);
        if !v.is_zero() {
            return v;
        }
    }
}

/// Uniformly random columns with the given per-row counts: density matched, structure discarded.
fn synthetic<F: FiniteField>(n: usize, counts: &[usize], seed: u64) -> Csr<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    let rows: Vec<Vec<(usize, F)>> = counts
        .iter()
        .map(|&k| {
            let mut row: Vec<(usize, F)> = (0..k)
                .map(|_| (rng.gen_range(0..n), nonzero(&mut rng)))
                .collect();
            row.sort_by_key(|e| e.0);
            row.dedup_by_key(|e| e.0);
            row
        })
        .collect();
    Csr::from_rows(n, &rows)
}

fn random_block<F: FiniteField>(len: usize, seed: u64) -> Vec<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..len).map(|_| nonzero(&mut rng)).collect()
}

fn csr_gather_arm<F: FiniteField + Send + Sync + 'static>(
    field: &'static str,
    matrix: &str,
    a: &std::sync::Arc<Csr<F>>,
    width: usize,
    threads: usize,
) -> Arm {
    let a = a.clone();
    let n = a.n;
    let x0 = random_block::<F>(n * width, 7 + width as u64);
    let (nnz, bytes) = (a.nnz(), a.bytes() + 2 * n * width * size_of::<F>());
    let run: Box<dyn FnMut(usize) -> Duration> = if threads == 1 {
        let mut x = x0;
        let mut y = vec![F::zero(); n * width];
        Box::new(move |steps| {
            timed(|| {
                for _ in 0..steps {
                    match width {
                        1 => gather::<F, 1>(&a, 0..n, &x, &mut y),
                        2 => gather::<F, 2>(&a, 0..n, &x, &mut y),
                        4 => gather::<F, 4>(&a, 0..n, &x, &mut y),
                        8 => gather::<F, 8>(&a, 0..n, &x, &mut y),
                        16 => gather::<F, 16>(&a, 0..n, &x, &mut y),
                        _ => panic!("width {width} not instantiated"),
                    }
                    std::mem::swap(&mut x, &mut y);
                }
                black_box(&x);
            })
        })
    } else {
        Box::new(move |steps| {
            let (out, time) = match width {
                1 => krylov_parallel::<F, 1>(&a, &x0, steps, threads),
                2 => krylov_parallel::<F, 2>(&a, &x0, steps, threads),
                4 => krylov_parallel::<F, 4>(&a, &x0, steps, threads),
                8 => krylov_parallel::<F, 8>(&a, &x0, steps, threads),
                16 => krylov_parallel::<F, 16>(&a, &x0, steps, threads),
                _ => panic!("width {width} not instantiated"),
            };
            black_box(out);
            time
        })
    };
    Arm {
        kind: Kind::Kernel,
        field,
        matrix: matrix.into(),
        format: "csr-u32 gather",
        width,
        threads,
        n,
        nnz,
        bytes,
        ops: nnz * width,
        steps: 0,
        run,
    }
}

fn csc_scatter_arm<F: FiniteField + 'static>(
    field: &'static str,
    matrix: &str,
    at: &std::sync::Arc<Csr<F>>,
    width: usize,
) -> Arm {
    let at = at.clone();
    let n = at.n;
    let mut x = random_block::<F>(n * width, 9 + width as u64);
    let mut y = vec![F::zero(); n * width];
    Arm {
        kind: Kind::Kernel,
        field,
        matrix: matrix.into(),
        format: "csc-u32 scatter",
        width,
        threads: 1,
        n,
        nnz: at.nnz(),
        bytes: at.bytes() + 2 * n * width * size_of::<F>(),
        ops: at.nnz() * width,
        steps: 0,
        run: Box::new(move |steps| {
            timed(|| {
                for _ in 0..steps {
                    match width {
                        1 => scatter::<F, 1>(&at, &x, &mut y),
                        8 => scatter::<F, 8>(&at, &x, &mut y),
                        _ => panic!("width {width} not instantiated"),
                    }
                    std::mem::swap(&mut x, &mut y);
                }
                black_box(&x);
            })
        }),
    }
}

fn crate_rows_arm<F: FiniteField + 'static>(field: &'static str, matrix: &str, a: &Csr<F>) -> Arm {
    let n = a.n;
    let rows: Vec<SparseRow<F>> = (0..n)
        .map(|i| SparseRow::from_sorted(a.row(i).collect()).expect("canonical"))
        .collect();
    let m = SparseMatrix::new(n, rows);
    let mut x = random_block::<F>(n, 5);
    let mut y = vec![F::zero(); n];
    let s = size_of::<F>();
    Arm {
        kind: Kind::Kernel,
        field,
        matrix: matrix.into(),
        format: "crate SparseMatrix rows",
        width: 1,
        threads: 1,
        n,
        nnz: m.nonzeros(),
        bytes: m.nonzeros() * size_of::<(usize, F)>() + n * size_of::<SparseRow<F>>() + 2 * n * s,
        ops: m.nonzeros(),
        steps: 0,
        run: Box::new(move |steps| {
            timed(|| {
                for _ in 0..steps {
                    gather_rows(&m, &x, &mut y);
                    std::mem::swap(&mut x, &mut y);
                }
                black_box(&x);
            })
        }),
    }
}

fn operator_arm<F: FiniteField + 'static>(
    field: &'static str,
    matrix: &str,
    op: MultiplicationOperator<F>,
) -> Arm {
    let n = op.dimension();
    let nnz = op.stored_entries() + op.standard_columns();
    let mut v = random_block::<F>(n, 3);
    Arm {
        kind: Kind::Kernel,
        field,
        matrix: matrix.into(),
        format: "operator.apply",
        width: 1,
        threads: 1,
        n,
        nnz,
        bytes: op.stored_bytes() + 2 * n * size_of::<F>(),
        ops: nnz,
        steps: 0,
        run: Box::new(move |steps| {
            timed(|| {
                for _ in 0..steps {
                    v = op.apply(&v);
                }
                black_box(&v);
            })
        }),
    }
}

fn bits_arm<F: 'static>(field: &'static str, matrix: &str, a: &std::sync::Arc<Csr<F>>) -> Arm {
    let a = a.clone();
    let n = a.n;
    let mut rng = StdRng::seed_from_u64(17);
    let mut x: Vec<u64> = (0..n).map(|_| rng.gen()).collect();
    let mut y = vec![0u64; n];
    Arm {
        kind: Kind::Kernel,
        field,
        matrix: matrix.into(),
        format: "gf2 bit-packed pattern",
        width: 64,
        threads: 1,
        n,
        nnz: a.cols.len(),
        bytes: 4 * (a.row_ptr.len() + a.cols.len()) + 2 * n * 8,
        ops: a.cols.len() * 64,
        steps: 0,
        run: Box::new(move |steps| {
            timed(|| {
                for _ in 0..steps {
                    gather_bits(&a, &x, &mut y);
                    std::mem::swap(&mut x, &mut y);
                }
                black_box(&x);
            })
        }),
    }
}

/// Independent multiply-adds over L1-resident operands: the field's arithmetic ceiling per core.
fn arith_arm<F: FiniteField + 'static>(field: &'static str) -> Arm {
    const LEN: usize = 1024;
    let a = random_block::<F>(LEN, 1);
    let x = random_block::<F>(LEN, 2);
    let mut y = random_block::<F>(LEN, 3);
    Arm {
        kind: Kind::Arith,
        field,
        matrix: "L1 arrays".into(),
        format: "y[i] += a[i] * x[i]",
        width: 1,
        threads: 1,
        n: LEN,
        nnz: LEN,
        bytes: 0,
        ops: LEN,
        steps: 0,
        run: Box::new(move |steps| {
            timed(|| {
                for _ in 0..steps {
                    for ((yi, ai), xi) in y.iter_mut().zip(&a).zip(black_box(&x)) {
                        *yi += *ai * *xi;
                    }
                }
                black_box(&y);
            })
        }),
    }
}

/// A streaming read of a buffer far beyond L3, split across `threads`: the bandwidth reference.
fn bandwidth_arm(buffer: &std::sync::Arc<Vec<u64>>, threads: usize) -> Arm {
    let buffer = buffer.clone();
    let bytes = buffer.len() * 8;
    Arm {
        kind: Kind::Bandwidth,
        field: "-",
        matrix: format!("{} MiB u64", bytes >> 20),
        format: "streaming read",
        width: 1,
        threads,
        n: buffer.len(),
        nnz: 0,
        bytes,
        ops: 0,
        steps: 0,
        run: Box::new(move |steps| {
            let chunk = buffer.len().div_ceil(threads);
            let barrier = Barrier::new(threads);
            thread::scope(|scope| {
                let handles: Vec<_> = buffer
                    .chunks(chunk)
                    .map(|part| {
                        let barrier = &barrier;
                        scope.spawn(move || {
                            barrier.wait();
                            let start = Instant::now();
                            for _ in 0..steps {
                                let sum = part.iter().fold(0u64, |a, &b| a.wrapping_add(b));
                                black_box(sum);
                                barrier.wait();
                            }
                            start.elapsed()
                        })
                    })
                    .collect();
                let times: Vec<Duration> = handles.into_iter().map(|h| h.join().unwrap()).collect();
                times[0]
            })
        }),
    }
}

struct OperatorStats {
    field: &'static str,
    dimension: usize,
    nnz: usize,
    standard: usize,
    max_row: usize,
    stored_bytes: usize,
    build: Duration,
}

fn add_operator<F: FiniteField + Send + Sync + 'static, const N: usize>(
    field: &'static str,
    c: &Config,
    arms: &mut Vec<Arm>,
    stats: &mut Vec<OperatorStats>,
    largest: bool,
) {
    let (op, build) = real_operator::<F, N>();
    let n = op.dimension();
    let a = std::sync::Arc::new(Csr::from_columns(n, &columns_of(&op)));
    let counts: Vec<usize> = (0..n)
        .map(|i| (a.row_ptr[i + 1] - a.row_ptr[i]) as usize)
        .collect();
    stats.push(OperatorStats {
        field,
        dimension: n,
        nnz: a.nnz(),
        standard: op.standard_columns(),
        max_row: counts.iter().copied().max().unwrap_or(0),
        stored_bytes: op.stored_bytes(),
        build,
    });
    let name = format!("real T_x{} D={n}", N - 1);
    arms.push(operator_arm(field, &name, op));
    add_matrix_arms(field, &name, a, c, arms, largest);
    let matched = format!("matched synthetic D={n}");
    let s = std::sync::Arc::new(synthetic::<F>(n, &counts, 1000 + n as u64));
    add_matrix_arms(field, &matched, s, c, arms, false);
}

fn add_matrix_arms<F: FiniteField + Send + Sync + 'static>(
    field: &'static str,
    name: &str,
    a: std::sync::Arc<Csr<F>>,
    c: &Config,
    arms: &mut Vec<Arm>,
    scaling: bool,
) {
    arms.push(crate_rows_arm(field, name, &a));
    let at = std::sync::Arc::new(a.transpose());
    for w in [1, 8] {
        if c.widths.contains(&w) {
            arms.push(csc_scatter_arm(field, name, &at, w));
        }
    }
    for &w in &c.widths {
        arms.push(csr_gather_arm(field, name, &a, w, 1));
    }
    if field == "GF(2)" {
        arms.push(bits_arm(field, name, &a));
    }
    if scaling {
        for &t in c.threads.iter().filter(|&&t| t > 1) {
            for w in [1, 8] {
                if c.widths.contains(&w) {
                    arms.push(csr_gather_arm(field, name, &a, w, t));
                }
            }
        }
    }
}

fn add_field<F: FiniteField + Send + Sync + 'static>(
    field: &'static str,
    c: &Config,
    arms: &mut Vec<Arm>,
    stats: &mut Vec<OperatorStats>,
) {
    arms.push(arith_arm::<F>(field));
    let top = c.max_variables;
    if top >= 5 {
        add_operator::<F, 5>(field, c, arms, stats, top == 5);
    }
    if top >= 6 {
        add_operator::<F, 6>(field, c, arms, stats, top == 6);
    }
    if top >= 7 {
        add_operator::<F, 7>(field, c, arms, stats, top == 7);
    }
    let entry = 4 + size_of::<F>();
    for (level, bytes) in [
        ("L2", c.l2_kib << 10),
        ("L3", c.l3_mib << 20),
        ("DRAM", c.dram_mib << 20),
    ] {
        let n = (bytes / (c.per_row * entry)).max(16);
        let name = format!("synthetic {level} k={} n={n}", c.per_row);
        let a = std::sync::Arc::new(synthetic::<F>(n, &vec![c.per_row; n], n as u64));
        add_matrix_arms(field, &name, a, c, arms, level == "DRAM");
    }
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let m = v.len() / 2;
    if v.len() % 2 == 1 {
        v[m]
    } else {
        (v[m - 1] + v[m]) / 2.0
    }
}

fn spread(v: &[f64]) -> f64 {
    let lo = v.iter().cloned().fold(f64::INFINITY, f64::min);
    let hi = v.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
    if lo > 0.0 {
        hi / lo
    } else {
        f64::NAN
    }
}

fn git(args: &[&str]) -> String {
    std::process::Command::new("git")
        .args(args)
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_default()
}

fn main() {
    let c = Config::parse();
    let dirty = !git(&["status", "--porcelain", "--untracked-files=no"]).is_empty();
    println!(
        "commit: {}{}",
        git(&["rev-parse", "--short", "HEAD"]),
        if dirty { " (dirty)" } else { "" }
    );
    println!("isa: {}", isa_floor());
    let cpu = std::fs::read_to_string("/proc/cpuinfo")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("model name"))
                .map(|l| l.split(':').nth(1).unwrap().trim().to_string())
        })
        .unwrap_or_default();
    println!(
        "cpu: {cpu}; available parallelism {:?}",
        thread::available_parallelism().map(|n| n.get())
    );
    println!("load at start: {:.2}", load());

    let mut arms = Vec::new();
    let mut stats = Vec::new();
    let build = Instant::now();
    let buffer = std::sync::Arc::new((0..(c.bandwidth_mib << 17) as u64).collect::<Vec<u64>>());
    for &t in &c.threads {
        arms.push(bandwidth_arm(&buffer, t));
    }
    add_field::<Zp2>("GF(2)", &c, &mut arms, &mut stats);
    add_field::<Gf256>("GF(2^8)", &c, &mut arms, &mut stats);
    add_field::<BabyBear>("31-bit BabyBear", &c, &mut arms, &mut stats);
    add_field::<Zp18446744069414584321>("64-bit Goldilocks", &c, &mut arms, &mut stats);
    add_field::<Bn254Fr>("254-bit BN254 Fr", &c, &mut arms, &mut stats);
    println!(
        "built {} arms in {:.1} s",
        arms.len(),
        build.elapsed().as_secs_f64()
    );

    println!("\n## Real operators (construction is a single unpaired snapshot)\n");
    println!("| field | D | nnz | nnz/row | max row | standard cols | stored bytes | build s |");
    println!("|---|---:|---:|---:|---:|---:|---:|---:|");
    for s in &stats {
        println!(
            "| {} | {} | {} | {:.2} | {} | {} | {} | {:.3} |",
            s.field,
            s.dimension,
            s.nnz,
            s.nnz as f64 / s.dimension as f64,
            s.max_row,
            s.standard,
            s.stored_bytes,
            s.build.as_secs_f64()
        );
    }

    // Calibrate once so each repetition times a fixed amount of work.
    for arm in &mut arms {
        let t = (arm.run)(1).as_secs_f64().max(1e-7);
        arm.steps = ((c.min_ms / 1e3 / t).ceil() as usize).max(1);
    }

    // rows[rep][arm] = (seconds, load)
    let mut rows: Vec<Vec<(f64, f64)>> = Vec::new();
    for rep in 0..c.reps {
        let mut order: Vec<usize> = (0..arms.len()).collect();
        order.rotate_left(rep * arms.len() / c.reps);
        let mut results = vec![(0.0, 0.0); arms.len()];
        let started = load();
        for i in order {
            let arm = &mut arms[i];
            let l = load();
            let t = (arm.run)(arm.steps).as_secs_f64();
            results[i] = (t, l);
        }
        eprintln!("rep {rep}: load {started:.2} -> {:.2}", load());
        rows.push(results);
    }

    if let Some(path) = &c.csv {
        let mut out = String::from(
            "rep,load,kind,field,matrix,format,width,threads,n,nnz,bytes_per_step,ops_per_step,steps,seconds\n",
        );
        for (rep, results) in rows.iter().enumerate() {
            for (arm, &(t, l)) in arms.iter().zip(results) {
                out += &format!(
                    "{rep},{l:.2},{:?},{},{},{},{},{},{},{},{},{},{},{t:.9}\n",
                    arm.kind,
                    arm.field,
                    arm.matrix,
                    arm.format,
                    arm.width,
                    arm.threads,
                    arm.n,
                    arm.nnz,
                    arm.bytes,
                    arm.ops,
                    arm.steps
                );
            }
        }
        std::fs::write(path, out).expect("csv written");
    }

    let rate = |rep: usize, i: usize| -> f64 {
        arms[i].ops as f64 * arms[i].steps as f64 / rows[rep][i].0
    };
    let gbps = |rep: usize, i: usize| -> f64 {
        arms[i].bytes as f64 * arms[i].steps as f64 / rows[rep][i].0 / 1e9
    };
    let arith: HashMap<&str, usize> = arms
        .iter()
        .enumerate()
        .filter(|(_, a)| a.kind == Kind::Arith)
        .map(|(i, a)| (a.field, i))
        .collect();
    let bandwidth: HashMap<usize, usize> = arms
        .iter()
        .enumerate()
        .filter(|(_, a)| a.kind == Kind::Bandwidth)
        .map(|(i, a)| (a.threads, i))
        .collect();
    let reps = 0..c.reps;

    println!(
        "\n## Baselines (median of {} paired repetitions; spread = max/min)\n",
        c.reps
    );
    println!("| reference | threads | median | spread |");
    println!("|---|---:|---:|---:|");
    for (i, a) in arms
        .iter()
        .enumerate()
        .filter(|(_, a)| a.kind != Kind::Kernel)
    {
        let (v, unit): (Vec<f64>, &str) = match a.kind {
            Kind::Arith => (
                reps.clone().map(|r| rate(r, i) / 1e6).collect(),
                "M mul-add/s",
            ),
            _ => (reps.clone().map(|r| gbps(r, i)).collect(), "GB/s"),
        };
        let label = if a.kind == Kind::Arith {
            a.field.to_string()
        } else {
            a.format.to_string()
        };
        println!(
            "| {label} | {} | {:.1} {unit} | {:.2} |",
            a.threads,
            median(v.clone()),
            spread(&v)
        );
    }

    println!("\n## Kernels (medians over repetitions; ratios paired within each repetition)\n");
    println!("| field | matrix | format | w | T | nnz | M mul-add/s | GB/s | arith% | bw% | vs w=1 | vs T=1 | spread |");
    println!("|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|");
    for (i, a) in arms
        .iter()
        .enumerate()
        .filter(|(_, a)| a.kind == Kind::Kernel)
    {
        let r: Vec<f64> = reps.clone().map(|rep| rate(rep, i)).collect();
        let g = median(reps.clone().map(|rep| gbps(rep, i)).collect());
        let ar = median(
            reps.clone()
                .map(|rep| 100.0 * rate(rep, i) / (a.threads as f64 * rate(rep, arith[a.field])))
                .collect(),
        );
        let bw = median(
            reps.clone()
                .map(|rep| 100.0 * gbps(rep, i) / gbps(rep, bandwidth[&a.threads]))
                .collect(),
        );
        // Same matrix, same format, width 1 at the same thread count: the block-reuse gain.
        let vs_w1 = arms
            .iter()
            .position(|b| {
                b.kind == Kind::Kernel
                    && b.field == a.field
                    && b.matrix == a.matrix
                    && b.format == a.format
                    && b.threads == a.threads
                    && b.width == 1
            })
            .filter(|_| a.width > 1 && a.format != "gf2 bit-packed pattern")
            .map(|j| {
                median(
                    reps.clone()
                        .map(|rep| rate(rep, i) / rate(rep, j))
                        .collect(),
                )
            });
        let vs_t1 = arms
            .iter()
            .position(|b| {
                b.kind == Kind::Kernel
                    && b.field == a.field
                    && b.matrix == a.matrix
                    && b.format == a.format
                    && b.width == a.width
                    && b.threads == 1
            })
            .filter(|_| a.threads > 1)
            .map(|j| {
                median(
                    reps.clone()
                        .map(|rep| rate(rep, i) / rate(rep, j))
                        .collect(),
                )
            });
        let fmt = |v: Option<f64>| v.map_or("".to_string(), |v| format!("{v:.2}x"));
        println!(
            "| {} | {} | {} | {} | {} | {} | {:.1} | {:.2} | {:.0}% | {:.0}% | {} | {} | {:.2} |",
            a.field,
            a.matrix,
            a.format,
            a.width,
            a.threads,
            a.nnz,
            median(r.clone()) / 1e6,
            g,
            ar,
            bw,
            fmt(vs_w1),
            fmt(vs_t1),
            spread(&r)
        );
    }

    let loads: Vec<f64> = rows.iter().flatten().map(|r| r.1).collect();
    println!(
        "\nload over the sweep: min {:.2}, median {:.2}, max {:.2}",
        loads.iter().cloned().fold(f64::INFINITY, f64::min),
        median(loads.clone()),
        loads.iter().cloned().fold(f64::NEG_INFINITY, f64::max)
    );
    println!("peak RSS: {:?} MiB", peak_resident_bytes().map(|b| b >> 20));
}

#[cfg(test)]
mod tests {
    use super::*;
    use zeebra::{fields::Zp65537, Zero};

    /// The CSR re-packing of a real FGLM operator applies exactly as `MultiplicationOperator::apply`.
    #[test]
    fn test_csr_of_real_operator_matches_apply() {
        let (op, _) = real_operator::<Zp65537, 3>();
        let n = op.dimension();
        let a = Csr::from_columns(n, &columns_of(&op));
        let x = random_block::<Zp65537>(n, 21);
        let mut y = vec![Zp65537::zero(); n];
        gather::<Zp65537, 1>(&a, 0..n, &x, &mut y);
        assert_eq!(y, op.apply(&x));
    }
}
