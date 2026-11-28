//! #1165: Zeebra's side of the M5GB paper-reference harness, one process per call.
//!
//! ```text
//! # A dense overdetermined row, as one instance JSON line
//! cargo run --release --example m5gb_paper_reference -- emit-dense \
//!     --n 8 --m 16 --density 1000 --seed 116501 --modulus 101 [--unplanted]
//! # Zeebra's reduced grevlex basis for each instance JSON line on stdin
//! cargo run --release --example m5gb_paper_reference -- solve --wall 120 < rows.jsonl
//! ```
//!
//! An instance line is `{"name", "modulus", "variables", "system"}`, with generators in Zeebra's
//! syntax over the listed variables. `solve` prints `{"name", "digest", "status", "basis",
//! "wall_ns"}` per line, from `F4Options::default()` at one worker. The M5GB adapter and the
//! comparison live in `tools/external/m5gb-paper/`; this file only answers for Zeebra.
use std::io::BufRead;
use std::time::Duration;
use zeebra::{
    fields::{Mersenne31, PrimeFieldElement32, PrimeFieldElement64, Zp31, Zp32003},
    grobner::external::{
        corpus::dense_mq_shaped, ExternalSolver, FieldSpec, Instance, Limits, RunStatus, Task,
        ZeebraSolver,
    },
    util::Json,
    MonomialOrder,
};

type Zp101 = PrimeFieldElement32<101>;
type Zp65521 = PrimeFieldElement32<65521>;
type Zp4294967291 = PrimeFieldElement64<4294967291>;

macro_rules! register {
    ($solver:expr, $f:ty, [$($n:literal),+]) => {{
        let mut solver = $solver;
        $(solver = solver.with_instantiation::<$n, $f>().unwrap();)+
        solver
    }};
}

fn zeebra() -> ZeebraSolver {
    let mut solver = ZeebraSolver::new();
    solver = register!(
        solver,
        Zp31,
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16]
    );
    solver = register!(solver, Zp101, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);
    solver = register!(solver, Zp32003, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);
    solver = register!(
        solver,
        Zp65521,
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16]
    );
    solver = register!(solver, Mersenne31, [1, 2, 3, 4, 5, 6, 7, 8]);
    register!(solver, Zp4294967291, [1, 2, 3, 4, 5, 6, 7, 8])
}

fn instance_json(instance: &Instance, modulus: u64) -> Json {
    Json::object([
        ("name", Json::string(&instance.name)),
        ("modulus", Json::int(modulus)),
        (
            "variables",
            Json::Array(instance.variables.iter().map(Json::string).collect()),
        ),
        (
            "system",
            Json::Array(instance.system.iter().map(Json::string).collect()),
        ),
    ])
}

/// `Json::to_json` indents; strings never hold a raw newline, so joining trimmed lines is exact.
fn one_line(json: &Json) -> String {
    json.to_json().lines().map(str::trim_start).collect()
}

fn solve(line: &str, wall: u64) -> Json {
    let row = Json::parse(line).expect("instance JSON");
    let text = |key: &str| row.get(key).and_then(Json::as_str).expect(key).to_string();
    let list = |key: &str| -> Vec<String> {
        row.get(key)
            .expect(key)
            .items()
            .iter()
            .map(|v| v.as_str().expect(key).to_string())
            .collect()
    };
    let modulus = row.get("modulus").and_then(Json::as_int).expect("modulus") as u64;
    let instance = Instance::new(
        text("name"),
        "m5gb-paper",
        FieldSpec::prime(modulus),
        list("variables"),
        list("system"),
        MonomialOrder::GradedReverseLexicographic,
    );
    let limits = Limits::wall(Duration::from_secs(wall)).with_workers(1);
    let report = zeebra().run(&instance, Task::ReducedGrobnerBasis, &limits);
    let (status, basis) = match &report.status {
        RunStatus::Complete(answer) | RunStatus::Verified(answer, ..) => (
            "complete".to_string(),
            answer.basis.clone().map_or(Json::Null, |b| {
                Json::Array(b.iter().map(Json::string).collect())
            }),
        ),
        other => (format!("{other:?}"), Json::Null),
    };
    Json::object([
        ("name", Json::string(&instance.name)),
        ("digest", Json::string(instance.digest())),
        ("status", Json::string(status)),
        ("basis", basis),
        ("wall_ns", Json::nanos(report.measurement.wall)),
    ])
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
    match args.get(1).map(String::as_str) {
        Some("emit-dense") => {
            let n = number("--n", 8) as usize;
            let m = number("--m", 2 * n as u64) as usize;
            let modulus = number("--modulus", 101);
            let instance = dense_mq_shaped(
                n,
                m,
                number("--density", 1000) as u32,
                number("--seed", 1),
                modulus,
                MonomialOrder::GradedReverseLexicographic,
                !args.iter().any(|a| a == "--unplanted"),
            );
            println!("{}", one_line(&instance_json(&instance, modulus)));
        }
        Some("solve") => {
            let wall = number("--wall", 120);
            for line in std::io::stdin().lock().lines() {
                let line = line.expect("stdin");
                if !line.trim().is_empty() {
                    println!("{}", one_line(&solve(&line, wall)));
                }
            }
        }
        _ => panic!("usage: m5gb_paper_reference (emit-dense ... | solve [--wall S])"),
    }
}
