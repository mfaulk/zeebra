//! #1034 deliverable 4: matrix-level counts for the bilinear cohort, regrouped by bidegree.
//!
//! For every instance this runs three computations, all under grevlex:
//! - conventional F4 with shipping options on the bilinear system, through
//!   `bilinear_census::bidegree_census`;
//! - the same on its perturbed control, which has two same-block products added per generator;
//! - the signature engine on the bilinear system, recording its matrix extents only.
//!
//! Every figure is a count, so the output does not depend on the machine. A run past the wall cap
//! is reported as `censored`, and the remaining instances of that shape and kind are reported as
//! `skipped`.
//!
//! ```text
//! cargo run --profile ci-release --features research-sigf4 --example bilinear_census -- [cap-seconds] > counts.tsv
//! ```
//!
//! Two environment variables re-run part of the cohort past the shipping budgets. Each changes
//! which instances complete, never what a completed instance counts.
//! - `ZB_ENTRIES=<n>` sets F4's live-entry budget to `n` (`F4Options::with_live_entries`) and
//!   lifts the row and column caps.
//! - `ZB_SHAPES=<k>x<n_y>-<kind>,...` runs only those shapes, for example `7x7-affine`.
//!
//! Four more split the cohort into one process per instance and arm, so that an outside watchdog
//! can stop a run inside a batch, where the wall cap cannot, without losing the other arms. None
//! changes what a completed run counts.
//! - `ZB_INSTANCES=<field>/<support>/<seed>,...` runs only those instances.
//! - `ZB_ARMS=bilinear,control,signature` runs only those arms. Without `bilinear` the row's status
//!   is `partial` and its bilinear columns are `-`; the control still runs.
//! - `ZB_WORKERS=<n>` caps F4's forward-elimination and symbolic-preprocessing threads.
//! - `ZB_TRACE=1` prints each batch matrix's degree and rows × columns to stderr as it is built,
//!   so a stopped run still shows the largest matrix it reached.

use std::time::{Duration, Instant};

use zeebra::{
    fields::{Zp2147483647, Zp31, Zp32003},
    grobner::{
        benchmark_systems::{bilinear, BilinearSpec},
        bilinear_census::{BidegreeCensus, CensusSummary},
        f4::{
            f4_observed, BatchObserver, F4Options, MacaulayMatrix, MonicBasis, ParallelForward,
            ParallelSymbolic,
        },
        pairs::CriticalPair,
        planning::BlockSplit,
        sigf4::{sig_f4_reported, SigF4Options},
        SigF4Error,
    },
    FiniteField, MonomialOrder,
};

const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const SUPPORTS: [u32; 3] = [1000, 600, 300];
const SEEDS: [u64; 2] = [1, 2];
const PERTURBATION: usize = 2;

enum Outcome<T> {
    Done(T),
    Censored,
    Failed(String),
    NotRun,
}

fn env_list(name: &str) -> Option<Vec<String>> {
    std::env::var(name)
        .ok()
        .map(|s| s.split(',').map(str::to_owned).collect())
}

fn arm(name: &str) -> bool {
    env_list("ZB_ARMS").is_none_or(|arms| arms.iter().any(|a| a == name))
}

/// The census, with each matrix's size echoed to stderr under `ZB_TRACE`.
struct Traced(BidegreeCensus, bool);

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for Traced {
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]) {
        BatchObserver::<N, F>::batch(&mut self.0, basis, pairs);
    }

    fn matrix(&mut self, matrix: &MacaulayMatrix<N, F>) {
        BatchObserver::<N, F>::matrix(&mut self.0, matrix);
        if self.1 {
            let b = self.0.batches().last().expect("just pushed");
            eprintln!(
                "trace\tdegree {}\t{} x {}\t{}",
                b.degree,
                b.rows,
                b.columns,
                b.area()
            );
        }
    }
}

fn census<const N: usize, F: FiniteField>(
    spec: &BilinearSpec,
    cap: Duration,
) -> (Outcome<(CensusSummary, usize)>, Duration) {
    let system = bilinear::<N, F>(spec).generators;
    let split = BlockSplit::two_blocks(N, spec.x_variables).expect("valid split");
    let mut options = F4Options {
        max_wall_time: Some(cap),
        ..F4Options::default()
    };
    if let Some(entries) = std::env::var("ZB_ENTRIES")
        .ok()
        .and_then(|s| s.parse().ok())
    {
        options = options.with_live_entries::<F>(entries);
        options.max_matrix_rows = usize::MAX;
        options.max_matrix_columns = usize::MAX;
    }
    if let Some(workers) = std::env::var("ZB_WORKERS")
        .ok()
        .and_then(|s| s.parse().ok())
    {
        options.parallel_forward = ParallelForward::Auto {
            max_workers: workers,
        };
        options.parallel_symbolic = ParallelSymbolic::Auto {
            max_workers: workers,
        };
    }
    let mut observer = Traced(
        BidegreeCensus::new(split),
        std::env::var_os("ZB_TRACE").is_some(),
    );
    let start = Instant::now();
    let outcome = match f4_observed(&system, GREVLEX, &options, &mut observer) {
        Ok((basis, _)) => Outcome::Done((observer.0.summary(), basis.len())),
        Err(e) if e.limit_name() == "max_wall_time" => Outcome::Censored,
        Err(e) => Outcome::Failed(format!("{e:?}")),
    };
    (outcome, start.elapsed())
}

fn signature<const N: usize, F: FiniteField>(
    spec: &BilinearSpec,
    cap: Duration,
) -> Outcome<(usize, usize)> {
    let system = bilinear::<N, F>(spec).generators;
    let options = SigF4Options {
        max_wall_time: Some(cap),
        ..SigF4Options::default()
    };
    let (result, statistics) = sig_f4_reported(&system, GREVLEX, &options);
    match result {
        Ok(_) => Outcome::Done((statistics.max_matrix_rows, statistics.max_matrix_columns)),
        Err(SigF4Error::Budget(e)) if e.limit_name() == "max_wall_time" => Outcome::Censored,
        Err(e) => Outcome::Failed(format!("{e:?}")),
    }
}

/// Runs one shape and kind over every field, support and seed.
fn shape<const N: usize>(k: usize, affine: bool, cap: Duration) {
    let mut censored = false;
    let kind = if affine { "affine" } else { "homogeneous" };
    let equations = if affine { N } else { N - 2 };
    if let Ok(only) = std::env::var("ZB_SHAPES") {
        let name = format!("{k}x{}-{kind}", N - k);
        if !only.split(',').any(|s| s == name) {
            return;
        }
    }
    let instances = env_list("ZB_INSTANCES");
    for field in ["31", "32003", "2147483647"] {
        for support in SUPPORTS {
            for seed in SEEDS {
                let instance = format!("{field}/{support}/{seed}");
                if instances
                    .as_ref()
                    .is_some_and(|only| !only.contains(&instance))
                {
                    continue;
                }
                let base = BilinearSpec {
                    x_variables: k,
                    equations,
                    affine,
                    support_per_mille: support,
                    perturbation: 0,
                    planted: affine,
                    seed,
                };
                let prefix = format!(
                    "{k}\t{}\t{N}\t{equations}\t{kind}\t{field}\t{support}\t{seed}",
                    N - k
                );
                if censored {
                    println!("{prefix}\tskipped");
                    continue;
                }
                let control = BilinearSpec {
                    perturbation: PERTURBATION,
                    ..base
                };
                let (bilinear_run, control_run, sig_run, elapsed) = match field {
                    "31" => run::<N, Zp31>(&base, &control, cap),
                    "32003" => run::<N, Zp32003>(&base, &control, cap),
                    _ => run::<N, Zp2147483647>(&base, &control, cap),
                };
                eprintln!("{prefix}\t{:.1}s", elapsed.as_secs_f64());
                match bilinear_run {
                    Outcome::Done((s, basis)) => {
                        let (control_degree, control_area) = match control_run {
                            Outcome::Done((c, _)) => {
                                (c.max_degree.to_string(), c.largest_matrix.to_string())
                            }
                            Outcome::Censored => ("censored".into(), "censored".into()),
                            Outcome::Failed(e) => (format!("failed:{e}"), "-".into()),
                            Outcome::NotRun => ("not-run".into(), "not-run".into()),
                        };
                        let (sig_rows, sig_columns) = match sig_run {
                            Outcome::Done((r, c)) => (r.to_string(), c.to_string()),
                            Outcome::Censored => ("censored".into(), "censored".into()),
                            Outcome::Failed(e) => (format!("failed:{e}"), "-".into()),
                            Outcome::NotRun => ("not-run".into(), "not-run".into()),
                        };
                        println!(
                            "{prefix}\tdone\t{}\t{}\t{}\t{}\t{}\t{:.3}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                            basis,
                            s.matrices,
                            s.max_degree,
                            s.largest_matrix,
                            s.largest_block,
                            s.largest_reduction().unwrap_or(f64::NAN),
                            s.total_area,
                            s.total_block_area,
                            s.columns,
                            s.regrouped_columns,
                            control_degree,
                            control_area,
                            format_args!("{sig_rows}\t{sig_columns}"),
                        );
                    }
                    Outcome::Censored => {
                        censored = true;
                        println!("{prefix}\tcensored");
                    }
                    Outcome::Failed(e) => println!("{prefix}\tfailed\t{e}"),
                    Outcome::NotRun => {
                        let (control_degree, control_area) = match control_run {
                            Outcome::Done((c, _)) => {
                                (c.max_degree.to_string(), c.largest_matrix.to_string())
                            }
                            Outcome::Censored => ("censored".into(), "censored".into()),
                            Outcome::Failed(e) => (format!("failed:{e}"), "-".into()),
                            Outcome::NotRun => ("not-run".into(), "not-run".into()),
                        };
                        println!(
                            "{prefix}\tpartial{}\t{control_degree}\t{control_area}\t-\t-",
                            "\t-".repeat(10)
                        );
                    }
                }
            }
        }
    }
}

#[allow(clippy::type_complexity)]
fn run<const N: usize, F: FiniteField>(
    base: &BilinearSpec,
    control: &BilinearSpec,
    cap: Duration,
) -> (
    Outcome<(CensusSummary, usize)>,
    Outcome<(CensusSummary, usize)>,
    Outcome<(usize, usize)>,
    Duration,
) {
    let start = Instant::now();
    let bilinear_run = if arm("bilinear") {
        census::<N, F>(base, cap).0
    } else {
        Outcome::NotRun
    };
    if matches!(bilinear_run, Outcome::Censored | Outcome::Failed(_)) {
        return (
            bilinear_run,
            Outcome::Censored,
            Outcome::Censored,
            start.elapsed(),
        );
    }
    let control_run = if arm("control") {
        census::<N, F>(control, cap).0
    } else {
        Outcome::NotRun
    };
    let sig_run = if arm("signature") {
        signature::<N, F>(base, cap)
    } else {
        Outcome::NotRun
    };
    (bilinear_run, control_run, sig_run, start.elapsed())
}

fn main() {
    let cap = Duration::from_secs(
        std::env::args()
            .nth(1)
            .map(|s| s.parse().expect("cap in seconds"))
            .unwrap_or(60),
    );
    println!(
        "k\tn_y\tN\tm\tkind\tfield\tsupport\tseed\tstatus\tbasis\tmatrices\tdegree\t\
         largest_matrix\tlargest_block\treduction\ttotal_area\ttotal_block_area\tcolumns\t\
         regrouped_columns\tcontrol_degree\tcontrol_largest_matrix\tsig_max_rows\tsig_max_columns"
    );
    for affine in [false, true] {
        // Ascending N, so a censored shape does not hold up the smaller ones.
        shape::<8>(2, affine, cap); // 1:3
        shape::<9>(3, affine, cap); // 1:2
        shape::<10>(5, affine, cap); // balanced
        shape::<12>(6, affine, cap); // balanced
        shape::<12>(4, affine, cap); // 1:2
        shape::<12>(3, affine, cap); // 1:3
        shape::<14>(7, affine, cap); // balanced
        shape::<16>(8, affine, cap); // balanced
    }
}
