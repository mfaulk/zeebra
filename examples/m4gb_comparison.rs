//! #1030: one dense overdetermined MQ row, one engine, one process; prints one JSON line.
//!
//! ```text
//! cargo run --release --features external-runners --example m4gb_comparison -- \
//!     --n 12 --m 24 --density 1000 --seed 1 --modulus 31 --engine m4gb --workers 1 --wall 180
//! ```
//!
//! `--engine` is `zeebra` (shipping F4 options, in-process), `zeebra-adaptive`
//! (`GradedEngine::Adaptive`: `f4_signature`'s dispatch, which sends these rows to the signature
//! engine), `m4gb` (the pinned reference from `tools/external/provision-m4gb.sh`) or `grobx` (the
//! pinned driver, raw mode). Both references are verified coefficient for coefficient against
//! Zeebra, outside the timed region.
//! `--unplanted` draws the inconsistent variant. `tools/external/m4gb-cohort.py` runs the cohort.
use std::time::Duration;
use zeebra::{
    fields::{PrimeFieldElement32, Zp31, Zp32003},
    grobner::{
        external::{
            contract::generators_agree, corpus::dense_mq_shaped, grobx, ExternalSolver,
            GrobxSolver, Limits, M4gbSolver, RunStatus, Task, ZeebraSolver,
        },
        F4Options, GradedEngine,
    },
    util::Json,
    MonomialOrder,
};

macro_rules! register {
    ($solver:expr, $($n:literal),+) => {{
        let mut solver = $solver;
        $(
            solver = solver.with_instantiation::<$n, Zp31>().unwrap();
            solver = solver.with_instantiation::<$n, Zp32003>().unwrap();
            solver = solver.with_instantiation::<$n, PrimeFieldElement32<65521>>().unwrap();
        )+
        solver
    }};
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let value = |name: &str| {
        args.iter()
            .position(|a| a == name)
            .and_then(|i| args.get(i + 1))
            .cloned()
    };
    let number = |name: &str, default: u64| {
        value(name)
            .map(|v| v.parse::<u64>().expect(name))
            .unwrap_or(default)
    };
    let n = number("--n", 10) as usize;
    let m = number("--m", 2 * n as u64) as usize;
    let density = number("--density", 1000) as u32;
    let seed = number("--seed", 1);
    let modulus = number("--modulus", 31);
    let workers = number("--workers", 1) as usize;
    let wall = number("--wall", 180);
    let planted = !args.iter().any(|a| a == "--unplanted");
    let engine = value("--engine").unwrap_or_else(|| "zeebra".into());

    let instance = dense_mq_shaped(
        n,
        m,
        density,
        seed,
        modulus,
        MonomialOrder::GradedReverseLexicographic,
        planted,
    );
    let limits = Limits::wall(Duration::from_secs(wall)).with_workers(workers);
    let task = Task::ReducedGrobnerBasis;
    let zeebra = || register!(ZeebraSolver::new(), 8, 9, 10, 11, 12, 13, 14, 15, 16);
    let mut verified = None;
    let report = match engine.as_str() {
        "zeebra" => zeebra().measuring_one_row().run(&instance, task, &limits),
        "zeebra-adaptive" => zeebra()
            .with_f4_options(F4Options {
                graded_engine: GradedEngine::Adaptive,
                ..F4Options::default()
            })
            .measuring_one_row()
            .run(&instance, task, &limits),
        "grobx" => {
            let scratch = std::env::temp_dir().join(format!("grobx-{}", std::process::id()));
            let mut solver =
                GrobxSolver::from_env(&scratch, grobx::Mode::Raw).expect("scratch directory");
            let mut report = solver.run(&instance, task, &limits);
            let _ = std::fs::remove_dir_all(scratch);
            // Verified the way the M4GB adapter verifies, after the timed solve.
            if let Some(basis) = report.status.answer().and_then(|a| a.basis.clone()) {
                let trusted = zeebra().run(&instance, task, &Limits { workers: 1, ..limits.clone() });
                let agrees = trusted
                    .status
                    .answer()
                    .and_then(|a| a.basis.as_ref())
                    .is_some_and(|r| generators_agree(r, &basis, modulus).is_ok());
                if !agrees {
                    report.status = RunStatus::Failed(
                        zeebra::grobner::external::RunFailure::Incomplete {
                            detail: "grobx basis disagrees with Zeebra's".into(),
                        },
                    );
                } else if let RunStatus::Complete(answer) = &report.status {
                    verified = Some(answer.basis.as_ref().map_or(0, Vec::len));
                }
            }
            report
        }
        "m4gb" => {
            let scratch = std::env::temp_dir().join(format!("m4gb-{}", std::process::id()));
            let mut solver = M4gbSolver::from_env(&scratch)
                .expect("scratch directory")
                .with_reference(zeebra());
            let report = solver.run(&instance, task, &limits);
            let _ = std::fs::remove_dir_all(scratch);
            report
        }
        other => panic!("unknown engine {other}"),
    };
    let status = match &report.status {
        RunStatus::Verified(..) => "verified".to_string(),
        RunStatus::Complete(..) if verified.is_some() => "verified".to_string(),
        RunStatus::Complete(..) => "complete".to_string(),
        other => format!("{other:?}"),
    };
    let basis_len = report
        .status
        .answer()
        .and_then(|a| a.basis.as_ref())
        .map(|b| b.len());
    let measurement = &report.measurement;
    let line = Json::object([
        ("row", Json::string(&instance.name)),
        ("digest", Json::string(instance.digest())),
        ("n", Json::size(n)),
        ("m", Json::size(m)),
        ("density", Json::int(density as u64)),
        ("seed", Json::int(seed)),
        ("modulus", Json::int(modulus)),
        ("planted", Json::Bool(planted)),
        ("engine", Json::string(&engine)),
        ("workers", Json::size(workers)),
        ("status", Json::string(status)),
        ("basis_len", basis_len.map(Json::size).unwrap_or(Json::Null)),
        ("wall_ns", Json::nanos(measurement.wall)),
        (
            "cpu_ns",
            measurement.cpu.map(Json::nanos).unwrap_or(Json::Null),
        ),
        (
            "peak_rss_bytes",
            measurement
                .peak_rss_bytes
                .map(Json::int)
                .unwrap_or(Json::Null),
        ),
        (
            "stages",
            Json::object(
                measurement
                    .stages
                    .iter()
                    .map(|(k, d)| (k.as_str(), Json::nanos(*d)))
                    .collect::<Vec<_>>(),
            ),
        ),
        (
            "version",
            report
                .version
                .as_ref()
                .map(|v| Json::string(v.to_string()))
                .unwrap_or(Json::Null),
        ),
    ]);
    println!("{}", line.to_json());
}
