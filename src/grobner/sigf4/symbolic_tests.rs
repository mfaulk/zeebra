//! #940: the parallel symbolic closure must reproduce the serial closure on every batch
//! (`docs/research/m32-parallel-symbolic.md` §3, checkpoints T1–T6). Under `check_signatures` the
//! engine re-runs the serial closure on a clone of the reducer cache and asserts the columns, rows
//! in order, handles and cache equal, so every checked run below is a per-batch oracle.

use std::{sync::mpsc, time::Duration};

use super::{
    claim::Adversary,
    engine::symbolic::with_tuning,
    engine::symbolic::Tuning,
    engine::symbolic::{PANIC_AT, TEAM_STARTS},
    sig_f4_reported, SigF4Error, SigF4Options, SigF4Statistics,
};
use crate::{
    fields::{PrimeFieldElement64, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, eco, katsura},
        f4::{f4, F4Error},
    },
    poly::MonomialOrder,
    FiniteField, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const GRADED: [MonomialOrder; 2] = [
    MonomialOrder::GradedReverseLexicographic,
    MonomialOrder::GradedLexicographic,
];

/// The team on every level and every column sort, so small systems exercise it.
const EVERY_LEVEL: Tuning = Tuning {
    min_frontier: 1,
    min_sort: 1,
    min_work: 0,
    min_start: 0,
    max_step: usize::MAX,
    fallback: false,
};

/// Narrow levels straight into the tables on the caller, wide ones on the team in bounded steps
/// (whose remainders may be narrow), in one closure.
const MIXED: Tuning = Tuning {
    min_frontier: 12,
    min_sort: 64,
    min_work: 0,
    min_start: 0,
    max_step: 40,
    fallback: false,
};

type Run<const N: usize, F> = (Vec<MultivariatePolynomial<N, F>>, SigF4Statistics);

/// Design 2 at `workers`, every signature check (and so the per-batch closure oracle) on.
fn checked(workers: usize) -> SigF4Options {
    SigF4Options {
        workers,
        check_signatures: true,
        max_live_bytes: None,
        ..SigF4Options::default()
    }
}

fn solve<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &SigF4Options,
    tuning: Tuning,
) -> Run<N, F> {
    let (result, statistics) = with_tuning(tuning, || sig_f4_reported(system, order, options));
    (result.expect("the engine finishes"), statistics)
}

/// Asserts `run` built and eliminated every batch as the serial engine did.
fn assert_same_batches<const N: usize, F: FiniteField>(
    serial: &Run<N, F>,
    run: &Run<N, F>,
    label: &str,
) {
    assert_eq!(run.0, serial.0, "{label}: reduced basis");
    assert_eq!(
        run.1.batch_trace, serial.1.batch_trace,
        "{label}: batch outcomes"
    );
    assert_eq!(
        (
            run.1.reducer_rows,
            run.1.max_matrix_rows,
            run.1.max_matrix_columns
        ),
        (
            serial.1.reducer_rows,
            serial.1.max_matrix_rows,
            serial.1.max_matrix_columns
        ),
        "{label}: matrix shapes"
    );
}

// T1: with the team on every level, or on the wide levels only, each batch's closure equals the
// serial one (asserted in the engine) at 1–16 workers, both graded orders and two fields; each
// batch eliminates as the serial engine's, and the basis equals shipping F4's.
#[test]
fn test_parallel_closure_equals_serial_on_every_batch() {
    fn check<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>], name: &str) {
        for order in GRADED {
            let serial = solve(system, order, &checked(1), Tuning::default());
            assert_eq!(serial.0, f4(system, order).expect("shipping F4 finishes"));
            assert_eq!(
                serial.1.symbolic_team_levels, 0,
                "{name}: one worker is serial"
            );
            for workers in 1..=16 {
                let label = format!("{name} {order:?} w={workers}");
                let mixed = solve(system, order, &checked(workers), MIXED);
                assert_same_batches(&serial, &mixed, &format!("{label} mixed"));
                let run = solve(system, order, &checked(workers), EVERY_LEVEL);
                assert_same_batches(&serial, &run, &label);
                assert!(mixed.1.symbolic_team_levels <= run.1.symbolic_team_levels);
                assert_eq!(
                    run.1.symbolic_team_levels > 0,
                    workers > 1,
                    "{label}: team levels"
                );
            }
        }
    }
    check(&katsura::<6, Zp32003>(), "katsura-6/32003");
    check(&katsura::<6, Goldilocks>(), "katsura-6/goldilocks");
    check(&cyclic::<5, Goldilocks>(), "cyclic-5/goldilocks");
    check(&eco::<7, Zp32003>(), "eco-7/32003");
}

// T1, under the parallel cascade too: the two parallel stages compose to the serial engine.
#[test]
fn test_parallel_closure_feeds_the_parallel_cascade() {
    let system = katsura::<6, Goldilocks>();
    let serial = solve(&system, GREVLEX, &checked(1), Tuning::default());
    for workers in [2, 5, 16] {
        let options = SigF4Options {
            parallel_cascade: true,
            ..checked(workers)
        };
        let run = solve(&system, GREVLEX, &options, EVERY_LEVEL);
        assert_same_batches(&serial, &run, &format!("w={workers}"));
        assert!(run.1.symbolic_team_levels > 0);
    }
}

// T2: seeded slice-claim permutations, reversed claims and seeded yields in the scan and before
// each merge, at every worker count 1–16, leave every batch's closure equal to the serial one.
#[test]
fn test_adverse_schedules_keep_the_serial_closure() {
    fn check<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>], name: &str) {
        let serial = solve(system, GREVLEX, &checked(1), Tuning::default());
        for workers in 1..=16 {
            let adversaries = [
                Adversary {
                    seed: workers as u64,
                    yield_permille: 200,
                    ..Adversary::default()
                },
                Adversary {
                    reverse: true,
                    ..Adversary::default()
                },
                Adversary {
                    seed: 31 * workers as u64 + 7,
                    yield_permille: 50,
                    reverse: true,
                    ..Adversary::default()
                },
            ];
            for adversary in adversaries {
                let options = SigF4Options {
                    adversary: Some(adversary),
                    ..checked(workers)
                };
                let run = solve(system, GREVLEX, &options, EVERY_LEVEL);
                let label = format!("{name} w={workers} {adversary:?}");
                assert_same_batches(&serial, &run, &label);
                assert_eq!(run.1.symbolic_team_levels > 0, workers > 1, "{label}");
            }
        }
    }
    check(&cyclic::<5, Goldilocks>(), "cyclic-5/goldilocks");
    check(&katsura::<6, Zp32003>(), "katsura-6/32003");
}

// T3: a row limit crossed mid-closure stops with `TooManyRows` and a column limit with
// `TooManyColumns`, in the same batch as the serial engine, at every worker count.
#[test]
fn test_bound_errors_match_the_serial_engine() {
    let system = katsura::<6, Zp32003>();
    let full = solve(&system, GREVLEX, &checked(1), Tuning::default()).1;
    let (rows, columns) = (full.max_matrix_rows, full.max_matrix_columns);
    let limits = [
        (rows - 1, usize::MAX),
        (usize::MAX, columns - 1),
        (rows - 1, columns - 1),
        (rows / 3, columns / 2),
        (10, 10),
    ];
    for (max_rows, max_columns) in limits {
        let options = |workers| SigF4Options {
            max_matrix_rows: max_rows,
            max_matrix_columns: max_columns,
            ..checked(workers)
        };
        let (expected, serial) = with_tuning(Tuning::default(), || {
            sig_f4_reported(&system, GREVLEX, &options(1))
        });
        let expected = expected.expect_err("the limit is crossed");
        assert!(matches!(
            expected,
            SigF4Error::Budget(F4Error::TooManyRows { .. } | F4Error::TooManyColumns { .. })
        ));
        for workers in [2, 3, 8, 16] {
            let (result, s) = with_tuning(EVERY_LEVEL, || {
                sig_f4_reported(&system, GREVLEX, &options(workers))
            });
            let label = format!("rows {max_rows} columns {max_columns} w={workers}");
            assert_eq!(result.expect_err("crossed"), expected, "{label}");
            assert_eq!(s.batches, serial.batches, "{label}: the stopping batch");
            assert_eq!(
                s.batch_trace, serial.batch_trace,
                "{label}: earlier batches"
            );
        }
    }
}

// T4: a crossed wall budget stops the closure at a level boundary of the first batch with
// `TimeBudgetExceeded` at that batch's degree, before anything is inserted.
#[test]
fn test_wall_budget_stops_the_closure_at_a_level_boundary() {
    let options = SigF4Options {
        max_wall_time: Some(Duration::ZERO),
        ..checked(4)
    };
    let (result, s) = with_tuning(EVERY_LEVEL, || {
        sig_f4_reported(&katsura::<5, Zp32003>(), GREVLEX, &options)
    });
    let Err(SigF4Error::Budget(F4Error::TimeBudgetExceeded { degree, .. })) = result else {
        panic!("expected a wall stop, got {:?}", result.map(|b| b.len()));
    };
    assert_eq!(degree, 1, "katsura's first batch is its linear generator");
    assert_eq!((s.batches, s.elements_added), (1, 0));
    assert!(
        s.batch_trace.is_empty(),
        "the stopped batch is abandoned whole"
    );
}

// T4: cancellation at the k-th level boundary of a batch abandons that batch whole, leaving exactly
// the earlier batches' elements; an unstopped run (a large k, or a generous budget) is unaffected.
#[test]
fn test_cancellation_inside_the_closure_inserts_only_complete_batches() {
    let system = katsura::<6, Goldilocks>();
    let serial = solve(&system, GREVLEX, &checked(1), Tuning::default());
    let mut stopped_late = false;
    for (workers, after) in [(2, 1), (4, 2), (16, 3), (3, 4)] {
        let options = SigF4Options {
            adversary: Some(Adversary {
                cancel_after: Some(after),
                ..Adversary::default()
            }),
            ..checked(workers)
        };
        let (result, s) = with_tuning(EVERY_LEVEL, || sig_f4_reported(&system, GREVLEX, &options));
        let label = format!("w={workers} after={after}");
        assert!(
            matches!(
                result,
                Err(SigF4Error::Budget(F4Error::TimeBudgetExceeded { degree, .. })) if degree > 0
            ),
            "{label}: {:?}",
            result.map(|b| b.len())
        );
        assert_eq!(s.batch_trace.len() + 1, s.batches, "{label}");
        assert_eq!(
            s.batch_trace[..],
            serial.1.batch_trace[..s.batch_trace.len()],
            "{label}: the completed batches are the serial engine's"
        );
        stopped_late |= s.batches > 1;
    }
    assert!(stopped_late, "some stop must land past the first batch");
    let never = SigF4Options {
        adversary: Some(Adversary {
            cancel_after: Some(u64::MAX),
            ..Adversary::default()
        }),
        max_wall_time: Some(Duration::from_secs(3_600)),
        ..checked(8)
    };
    let run = solve(&system, GREVLEX, &never, EVERY_LEVEL);
    assert_same_batches(&serial, &run, "unstopped");
}

// T5: the closure's tables and slice scratch are charged to `max_live_bytes`: a small limit is a
// typed refusal that abandons the batch, and a finished run reports a peak within its limit.
#[test]
fn test_live_budget_charges_the_closure() {
    let system = katsura::<5, Zp32003>();
    let limited = SigF4Options {
        max_live_bytes: Some(2_000),
        ..checked(4)
    };
    let (result, s) = with_tuning(EVERY_LEVEL, || sig_f4_reported(&system, GREVLEX, &limited));
    let Err(SigF4Error::Budget(F4Error::TooManyLiveBytes { bytes, limit })) = result else {
        panic!(
            "expected a live-bytes refusal, got {:?}",
            result.map(|b| b.len())
        );
    };
    assert!(bytes > limit && limit == 2_000);
    assert_eq!(
        s.batch_trace.len() + 1,
        s.batches,
        "the refused batch is abandoned"
    );
    let budget = SigF4Options {
        max_live_bytes: Some(64 << 20),
        ..checked(4)
    };
    let (_, s) = solve(&system, GREVLEX, &budget, EVERY_LEVEL);
    assert!(
        s.symbolic_peak_live_bytes > 2_000,
        "{}",
        s.symbolic_peak_live_bytes
    );
    assert!(s.symbolic_peak_live_bytes <= 64 << 20);
}

// T6: when the field cannot cross threads the job runs its serial fallback — today's closure —
// which starts no team, reads no live budget and gives the serial engine's batches.
#[test]
fn test_fallback_runs_the_serial_closure() {
    let system = katsura::<6, Zp32003>();
    let serial = solve(&system, GREVLEX, &checked(1), Tuning::default());
    let fallback = Tuning {
        fallback: true,
        ..EVERY_LEVEL
    };
    let options = SigF4Options {
        max_live_bytes: Some(1),
        ..checked(16)
    };
    let run = solve(&system, GREVLEX, &options, fallback);
    assert_same_batches(&serial, &run, "fallback");
    assert_eq!(run.1.symbolic_team_levels, 0);
}

// A closure that never widens past the default frontier never wakes the team.
#[test]
fn test_narrow_closures_stay_on_the_caller() {
    let system = katsura::<4, Goldilocks>();
    let run = solve(&system, GREVLEX, &checked(16), Tuning::default());
    assert_eq!(run.1.symbolic_team_levels, 0);
    let serial = solve(&system, GREVLEX, &checked(1), Tuning::default());
    assert_same_batches(&serial, &run, "narrow");
}

// A panic on the caller inside a team step propagates out of the solve instead of leaving the team
// parked at a barrier and the scope joining it forever.
#[test]
fn test_a_caller_panic_mid_closure_dismisses_the_team() {
    let (done, finished) = mpsc::channel();
    std::thread::spawn(move || {
        PANIC_AT.set(Some(3));
        let options = SigF4Options {
            check_signatures: false,
            ..checked(8)
        };
        let run = std::panic::catch_unwind(|| {
            with_tuning(EVERY_LEVEL, || {
                sig_f4_reported(&katsura::<6, Goldilocks>(), GREVLEX, &options)
            })
        });
        done.send(run.is_err()).expect("the test waits");
    });
    let panicked = finished
        .recv_timeout(Duration::from_secs(60))
        .expect("the solve returns rather than hanging");
    assert!(panicked, "the injected panic propagates");
}

/// Every level under the work gate.
const NO_WORK: Tuning = Tuning {
    min_work: usize::MAX,
    min_start: usize::MAX,
    ..EVERY_LEVEL
};

// A closure whose every level is under the work gate never starts the team, not even to sort its
// columns, and still builds the serial engine's batches.
#[test]
fn test_levels_under_the_work_gate_never_start_the_team() {
    let system = katsura::<6, Goldilocks>();
    let serial = solve(&system, GREVLEX, &checked(1), Tuning::default());
    TEAM_STARTS.set(0);
    let run = solve(&system, GREVLEX, &checked(8), NO_WORK);
    assert_eq!(run.1.symbolic_team_levels, 0);
    assert_eq!(TEAM_STARTS.get(), 0, "the sort stays on the caller too");
    assert_same_batches(&serial, &run, "gated");
}

// The work gate (step width times the mean row length) is monotone: raising it never adds a team
// level, some threshold puts a closure's wide steps on the team and its narrow ones on the caller,
// and every split builds the serial engine's batches.
#[test]
fn test_the_work_gate_splits_a_closure_by_level_size() {
    let system = katsura::<6, Goldilocks>();
    let serial = solve(&system, GREVLEX, &checked(1), Tuning::default());
    let every = solve(&system, GREVLEX, &checked(8), EVERY_LEVEL)
        .1
        .symbolic_team_levels;
    assert!(every > 0);
    let mut last = every;
    let mut split = false;
    for min_work in [10, 100, 1_000, 3_000, 10_000, 30_000, 100_000] {
        let tuning = Tuning {
            min_work,
            min_start: min_work,
            ..EVERY_LEVEL
        };
        let run = solve(&system, GREVLEX, &checked(8), tuning);
        let levels = run.1.symbolic_team_levels;
        assert!(levels <= last, "min_work {min_work}: {levels} > {last}");
        split |= 0 < levels && levels < every;
        last = levels;
        assert_same_batches(&serial, &run, &format!("min_work {min_work}"));
    }
    assert!(split, "some threshold splits the closure");
    assert_eq!(
        last, 0,
        "the largest threshold keeps every level on the caller"
    );
}

// The start gate and the step gate are separate: a team that may start but may not continue runs
// one step per closure, and one that may continue but may not start never runs.
#[test]
fn test_the_start_gate_admits_the_first_step_only() {
    let system = katsura::<6, Goldilocks>();
    let serial = solve(&system, GREVLEX, &checked(1), Tuning::default());
    let first = Tuning {
        min_work: usize::MAX,
        ..EVERY_LEVEL
    };
    let run = solve(&system, GREVLEX, &checked(8), first);
    assert_eq!(
        run.1.symbolic_team_levels, serial.1.batches,
        "one team step in every closure"
    );
    assert_same_batches(&serial, &run, "first step only");
    let never = Tuning {
        min_start: usize::MAX,
        ..EVERY_LEVEL
    };
    TEAM_STARTS.set(0);
    let run = solve(&system, GREVLEX, &checked(8), never);
    assert_eq!(run.1.symbolic_team_levels, 0);
    assert_eq!(TEAM_STARTS.get(), 0);
    assert_same_batches(&serial, &run, "never started");
}
