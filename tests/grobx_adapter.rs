#![cfg(feature = "external-runners")]
use std::time::Duration;
use zeebra::{
    grobner::external::{
        grobx::Mode, ExternalSolver, FieldSpec, GrobxSolver, Instance, Limits, RunFailure,
        RunStatus, Task,
    },
    MonomialOrder,
};

// A missing optional executable remains an unavailable result, including under an exhausted wall budget.
#[test]
fn absent_grobx_is_not_a_resource_stop_or_answer() {
    let scratch = std::env::temp_dir().join(format!("grobx-absent-{}", std::process::id()));
    let mut solver = GrobxSolver::new(
        scratch.join("absent").to_string_lossy(),
        &scratch,
        Mode::Raw,
    )
    .unwrap();
    let instance = Instance::new(
        "missing",
        "control",
        FieldSpec::prime(32003),
        vec!["x".into()],
        vec!["x".into()],
        MonomialOrder::GradedReverseLexicographic,
    );
    let report = solver.run(
        &instance,
        Task::ReducedGrobnerBasis,
        &Limits::wall(Duration::ZERO),
    );
    assert!(matches!(
        report.status,
        RunStatus::Failed(RunFailure::Unavailable { .. })
    ));
    assert!(!report.status.is_timing_evidence());
}
