//! One engine and one digest per process; retained rows include complete checked basis artifacts.
use std::{fs, path::PathBuf, time::Duration};
use zeebra::{
    grobner::{
        external::{
            corpus,
            groebner_rs::{control_entry, wide_control},
            CompetitiveBoard, CompetitiveRecord, ExternalSolver, GiacSolver, GroebnerRsSolver,
            Limits, Measurement, RunReport, RunStatus, Task, Unsupported, ZeebraSolver,
        },
        record::Environment,
    },
    util::Json,
    MonomialOrder,
};
#[allow(clippy::assertions_on_constants)]
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let value = |name: &str| {
        args.iter()
            .position(|a| a == name)
            .and_then(|i| args.get(i + 1))
            .cloned()
    };
    let engine = value("--engine").unwrap_or_else(|| "groebner-rs".into());
    let row = value("--row").unwrap_or_else(|| "katsura-4".into());
    let modulus: u64 = value("--modulus")
        .unwrap_or_else(|| "32003".into())
        .parse()
        .expect("modulus");
    let workers: usize = value("--workers")
        .unwrap_or_else(|| "1".into())
        .parse()
        .expect("workers");
    let wall: u64 = value("--wall")
        .unwrap_or_else(|| "30".into())
        .parse()
        .expect("wall");
    let rss: u64 = value("--rss-mib")
        .unwrap_or_else(|| "1024".into())
        .parse()
        .expect("rss");
    let instance = if row == "groebner-rs-wide-control" {
        wide_control(modulus)
    } else {
        corpus::instance(&row, modulus, MonomialOrder::GradedReverseLexicographic)
    }
    .expect("registered control");
    if args.iter().any(|a| a == "--list") {
        println!("{} {}", instance.name, instance.digest());
        return;
    }
    assert!((1..=1024).contains(&workers), "workers must be in 1..=1024");
    let entry = if row == "groebner-rs-wide-control" {
        control_entry()
    } else {
        corpus::ladder()
            .into_iter()
            .find(|entry| entry.name == row)
            .expect("corpus provenance")
    };
    assert_eq!(
        entry.digest_at(modulus),
        Some(instance.digest().as_str()),
        "unpublished or drifted input"
    );
    let limits = Limits::wall(Duration::from_secs(wall))
        .with_workers(workers)
        .with_max_rss_bytes(rss * 1024 * 1024);
    let scratch = PathBuf::from(std::env::var("TMPDIR").expect("set TMPDIR on the build cache"))
        .join(format!("groebner-comparison-{}", std::process::id()));
    let (mut driver, version, startup): (Box<dyn ExternalSolver>, _, _) = if engine == "giac" {
        let mut solver = GiacSolver::from_env(&scratch).unwrap();
        let version = solver.probe_version().expect("install Giac first");
        let startup = solver
            .startup_measurement(&Limits::wall(Duration::from_secs(10)))
            .expect("Giac startup observation");
        (Box::new(solver), version, startup)
    } else {
        let mut solver = GroebnerRsSolver::from_env(&scratch).unwrap();
        let version = solver
            .probe_version()
            .expect("provision the pinned driver first");
        let startup = solver
            .startup_measurement(&Limits::wall(Duration::from_secs(10)))
            .expect("startup observation");
        (Box::new(solver), version, startup)
    };
    let mut environment = Environment::from_git();
    environment.machine = std::env::var("ZEEBRA_MACHINE").expect("ZEEBRA_MACHINE");
    environment.cpu = format!(
        "{}; affinity {}",
        std::fs::read_to_string("/proc/cpuinfo")
            .ok()
            .and_then(|text| text.lines().find_map(|line| line
                .strip_prefix("model name")
                .and_then(|v| v.split_once(':'))
                .map(|(_, v)| v.trim().to_string())))
            .unwrap_or_else(|| "unknown CPU".into()),
        std::env::var("ZEEBRA_AFFINITY").expect("ZEEBRA_AFFINITY")
    );
    environment.concurrency = workers;
    assert!(
        cfg!(all(
            target_feature = "avx2",
            target_feature = "bmi2",
            target_feature = "fma"
        )),
        "build with x86-64-v3"
    );
    environment.build = format!(
        "release; fat LTO; codegen-units=1; x86-64-v3; system allocator; {}",
        String::from_utf8(
            std::process::Command::new("rustc")
                .arg("-Vv")
                .output()
                .unwrap()
                .stdout
        )
        .unwrap()
        .replace('\n', ";")
    );
    environment.policy = format!(
        "#678; one row per process; {}s; {}MiB RSS; {} workers; matched-ISA; driver={}",
        wall,
        rss,
        workers,
        version
            .build
            .as_deref()
            .unwrap_or("Giac upstream package; ISA unspecified")
    );
    if engine == "giac" {
        environment.build = format!(
            "harness {}; Giac upstream package; engine ISA unspecified",
            environment.build
        );
        environment.policy = format!("#740; one row per process; {wall}s per child; {rss}MiB RSS; {workers} workers; exact independent Singular verification");
    }
    let task = Task::ReducedGrobnerBasis;
    let report=match engine.as_str(){
        "groebner-rs"|"giac"=>driver.run(&instance,task,&limits),
        "zeebra" if workers!=1=>RunReport::new("zeebra",&instance,task,&limits,
            RunStatus::Unsupported(Unsupported::Representation{detail:"the configured Zeebra F4 is serial; cannot supply the requested multiworker cohort".into()}),Measurement::unmeasured()),
        "zeebra"=>{let mut solver=ZeebraSolver::new().measuring_one_row();let _=solver.probe_version();solver.run(&instance,task,&limits)},
        _=>panic!("unknown engine")
    };
    let mut board = CompetitiveBoard::new().with_corpus([control_entry()]);
    board.add(CompetitiveRecord::of(&report, &instance, &environment));
    let status_detail = match &report.status {
        RunStatus::Verified(..) => "full-basis-verified".into(),
        _ => format!("{:?}", report.status),
    };
    let artifacts = Json::object([
        ("status_detail", Json::string(status_detail)),
        ("digest", Json::string(instance.digest())),
        (
            "transformation",
            instance
                .transformation
                .as_ref()
                .map(Json::string)
                .unwrap_or(Json::Null),
        ),
        (
            "variables",
            Json::Array(instance.variables.iter().map(Json::string).collect()),
        ),
        ("modulus", Json::int(modulus)),
        (
            "generators",
            Json::Array(instance.system.iter().map(Json::string).collect()),
        ),
        (
            "basis",
            report
                .status
                .answer()
                .and_then(|a| a.basis.as_ref())
                .map(|basis| Json::Array(basis.iter().map(Json::string).collect()))
                .unwrap_or(Json::Null),
        ),
        ("driver_startup_wall_ns", Json::nanos(startup.wall)),
        (
            "driver_startup_cpu_ns",
            startup.cpu.map(Json::nanos).unwrap_or(Json::Null),
        ),
        (
            "driver_startup_rss_bytes",
            startup.peak_rss_bytes.map(Json::int).unwrap_or(Json::Null),
        ),
        ("driver", Json::string(version.to_string())),
        (
            "independent_outputs",
            if engine == "giac" {
                Json::Array(
                    fs::read_dir(&scratch)
                        .unwrap()
                        .filter_map(Result::ok)
                        .filter(|entry| entry.file_name().to_string_lossy().starts_with("verify-"))
                        .flat_map(|entry| {
                            fs::read_dir(entry.path()).unwrap().filter_map(Result::ok)
                        })
                        .filter(|entry| entry.path().extension().is_some_and(|ext| ext == "out"))
                        .map(|entry| Json::string(fs::read_to_string(entry.path()).unwrap()))
                        .collect(),
                )
            } else {
                Json::Null
            },
        ),
        (
            "raw_output",
            report
                .log_path
                .as_ref()
                .and_then(|p| fs::read_to_string(p).ok())
                .map(Json::string)
                .unwrap_or(Json::Null),
        ),
    ]);
    let mut json = board.to_json();
    if let Json::Object(fields) = &mut json {
        fields.push(("artifacts".into(), artifacts));
    }
    if let Some(path) = value("--output") {
        fs::write(path, json.to_json() + "\n").unwrap();
    }
    println!("{}", json.to_json());
    let _ = fs::remove_dir_all(scratch);
}
