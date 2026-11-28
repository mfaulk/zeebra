//! M31-S2 (#904): the parallel cascade must reproduce design 1 row for row in every batch
//! (#902 Theorem 1), under adverse schedules, budgets and cancellation.

use super::{
    claim::{Adversary, Claim, Kind},
    corpus::correctness_constructions,
    engine::{ReducerBlock, Workspace, NONE},
    sig_f4_reported,
    signature::Signature,
    SigF4Error, SigF4Options, SigF4Statistics,
};
use crate::{
    fields::{ConcurrentJob, PrimeFieldElement64, Zp13, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, eco, katsura},
        f4::{certify_f4_output, f4, F4Error},
        reference::buchberger_reference,
    },
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const GRADED: [MonomialOrder; 2] = [
    MonomialOrder::GradedReverseLexicographic,
    MonomialOrder::GradedLexicographic,
];

fn claim(workers: usize) -> SigF4Options {
    SigF4Options {
        workers,
        parallel_cascade: true,
        ..SigF4Options::checked()
    }
}

type Run<const N: usize, F> = (Vec<MultivariatePolynomial<N, F>>, SigF4Statistics);

fn solve<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &SigF4Options,
) -> Run<N, F> {
    // Every system here is small, so graded-lex runs despite #961 (#1049).
    // #1140's stop is timed, so it may end design 1 and the cascade at different batches.
    let options = SigF4Options {
        allow_graded_lex: true,
        lead_ideal_stop: false,
        ..options.clone()
    };
    let (result, statistics) = sig_f4_reported(system, order, &options);
    (result.expect("the engine finishes"), statistics)
}

/// Asserts per-batch equality of `run` with design 1: every target's outcome and exact row.
fn assert_same_rows<const N: usize, F: FiniteField>(
    design_1: &Run<N, F>,
    run: &Run<N, F>,
    label: &str,
) {
    let (expected, d1) = design_1;
    let (actual, s) = run;
    assert_eq!(
        s.batch_trace.len(),
        d1.batch_trace.len(),
        "{label}: batches"
    );
    for (b, (x, y)) in d1.batch_trace.iter().zip(&s.batch_trace).enumerate() {
        assert_eq!(x, y, "{label}: batch {b} differs from design 1");
    }
    assert_eq!(actual, expected, "{label}: reduced basis");
    assert_eq!(
        (
            s.zero_rows,
            s.singular_rows,
            s.elements_added,
            s.syzygy_signatures
        ),
        (
            d1.zero_rows,
            d1.singular_rows,
            d1.elements_added,
            d1.syzygy_signatures
        ),
        "{label}: per-batch outcomes feed the same stores"
    );
}

/// Per batch, the parallel cascade's zero rows, singular discards and new elements equal design
/// 1's exactly, rows included, at every worker count, both graded orders and two fields.
#[test]
fn test_claim_cascade_reproduces_design_1_rows_per_batch() {
    fn check<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>], name: &str) {
        for order in GRADED {
            let d1 = solve(system, order, &SigF4Options::checked());
            assert!(d1.1.batch_trace.iter().map(Vec::len).sum::<usize>() > 0);
            let d2 = solve(
                system,
                order,
                &SigF4Options {
                    workers: 4,
                    ..SigF4Options::checked()
                },
            );
            for workers in [1, 2, 3, 4, 8, 16] {
                let run = solve(system, order, &claim(workers));
                assert_same_rows(&d1, &run, &format!("{name} {order:?} w={workers}"));
                assert_eq!(
                    run.1.coefficient_products, d2.1.coefficient_products,
                    "prereduce + claim performs design 2's products"
                );
            }
        }
    }
    check(&katsura::<6, Zp32003>(), "katsura-6/32003");
    check(&katsura::<6, Goldilocks>(), "katsura-6/goldilocks");
    check(&cyclic::<5, Goldilocks>(), "cyclic-5/goldilocks");
    check(&eco::<7, Zp32003>(), "eco-7/32003");
}

/// The corpus never produces a singular row (the rewrite criterion removes them first), so E2 is
/// covered by the synthetic batches below; the corpus still exercises zero rows and cascades.
#[test]
fn test_corpus_exercises_zero_rows_and_cascades() {
    let (_, s) = solve(&katsura::<6, Zp32003>(), GREVLEX, &claim(4));
    assert!(s.zero_rows > 0, "{s:?}");
    assert!(s.batch_trace.iter().any(|b| b.len() > 1), "{s:?}");
}

/// Forced interleavings and seeded random yields at every worker count 1–16 (plan §9.2): rows
/// stay design 1's, and the announcement and final-row waits (E1) are both taken.
#[test]
fn test_adverse_schedules_keep_design_1_rows() {
    let system = cyclic::<5, Goldilocks>();
    let d1 = solve(&system, GREVLEX, &SigF4Options::checked());
    let mut announcement_waits = 0;
    let mut final_waits = 0;
    for workers in 1..=16 {
        let adversaries = [
            Adversary {
                seed: workers as u64,
                yield_permille: 50,
                ..Adversary::default()
            },
            Adversary {
                reverse: true,
                ..Adversary::default()
            },
            Adversary {
                slow_publication: 40,
                ..Adversary::default()
            },
            Adversary {
                seed: 7 * workers as u64,
                yield_permille: 20,
                slow_announcement: 20,
                reverse: true,
                ..Adversary::default()
            },
        ];
        for adversary in adversaries {
            let options = SigF4Options {
                adversary: Some(adversary),
                ..claim(workers)
            };
            let run = solve(&system, GREVLEX, &options);
            assert_same_rows(&d1, &run, &format!("w={workers} {adversary:?}"));
            if workers == 1 {
                assert_eq!(
                    (run.1.claim_announcement_waits, run.1.claim_final_waits),
                    (0, 0),
                    "one worker in rank order never waits"
                );
            }
            announcement_waits += run.1.claim_announcement_waits;
            final_waits += run.1.claim_final_waits;
        }
    }
    assert!(announcement_waits > 0, "no announcement wait was exercised");
    assert!(final_waits > 0, "no final-row wait was exercised");
}

/// A zero wall budget abandons the first batch at a safe point (E3): typed error, nothing
/// inserted.
#[test]
fn test_wall_budget_abandons_the_batch_before_insertion() {
    let options = SigF4Options {
        max_wall_time: Some(std::time::Duration::ZERO),
        ..claim(4)
    };
    let (result, s) = sig_f4_reported(&katsura::<5, Zp32003>(), GREVLEX, &options);
    assert!(matches!(
        result,
        Err(SigF4Error::Budget(F4Error::TimeBudgetExceeded { .. }))
    ));
    assert_eq!((s.batches, s.elements_added), (1, 0));
    assert!(s.batch_trace.is_empty());
}

/// Cancellation inside a batch, at a pivot safe point mid-cascade, abandons that batch whole:
/// exactly the earlier batches' elements are in the basis (E3).
#[test]
fn test_mid_batch_cancellation_inserts_only_complete_batches() {
    let system = katsura::<6, Goldilocks>();
    for (workers, after) in [(1, 100), (4, 300), (16, 600), (3, 450)] {
        let options = SigF4Options {
            adversary: Some(Adversary {
                cancel_after: Some(after),
                ..Adversary::default()
            }),
            ..claim(workers)
        };
        let (result, s) = sig_f4_reported(&system, GREVLEX, &options);
        assert!(
            matches!(
                result,
                Err(SigF4Error::Budget(F4Error::TimeBudgetExceeded { .. }))
            ),
            "w={workers} after={after}: {:?}",
            result.map(|basis| basis.len())
        );
        assert!(
            s.batches > 1,
            "w={workers}: the stop must land past the first batch"
        );
        assert_eq!(s.batch_trace.len() + 1, s.batches, "w={workers}");
        assert_eq!(s.elements_added, elements_in(&s), "w={workers}");
    }
}

/// Scratch and metadata are charged to the live budget: a small limit is a typed refusal, and a
/// finished run reports a peak within its limit.
#[test]
fn test_live_budget_is_charged_and_typed() {
    let system = katsura::<5, Zp32003>();
    let options = SigF4Options {
        max_live_bytes: Some(2_000),
        ..claim(4)
    };
    let (result, s) = sig_f4_reported(&system, GREVLEX, &options);
    assert!(matches!(
        result,
        Err(SigF4Error::Budget(F4Error::TooManyLiveBytes {
            limit: 2_000,
            ..
        }))
    ));
    assert_eq!(
        s.batch_trace.len() + 1,
        s.batches,
        "the refused batch is abandoned"
    );
    assert_eq!(s.elements_added, elements_in(&s));
    let (_, s) = solve(&system, GREVLEX, &claim(4));
    assert!(s.claim_peak_live_bytes > 2_000);
    assert!(s.claim_peak_live_bytes <= claim(4).max_live_bytes.unwrap());
}

/// RFC §10.1's correctness constructions at GF(32003) and Goldilocks, both graded orders: equal to
/// shipping F4 and certified, at 16 workers with every signature check on.
#[test]
fn test_correctness_corpus_matches_f4_at_16_workers() {
    fn agrees<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>]) {
        for order in GRADED {
            let expected = f4(system, order).expect("shipping F4 finishes");
            let (actual, _) = solve(system, order, &claim(16));
            assert_eq!(actual, expected, "{order:?}");
            let report = certify_f4_output(system, &actual, order);
            assert!(report.checks_passed(), "{:?}", report.first_failure());
        }
    }
    for construction in correctness_constructions() {
        match construction.variables() {
            4 => {
                agrees(&construction.system::<4, Zp32003>());
                agrees(&construction.system::<4, Goldilocks>());
            }
            10 => {
                agrees(&construction.system::<10, Zp32003>());
                agrees(&construction.system::<10, Goldilocks>());
            }
            n => panic!("no arity {n} instantiation for {}", construction.name),
        }
    }
}

/// Small systems equal the independent Buchberger reference through the parallel cascade.
#[test]
fn test_small_systems_match_the_buchberger_reference() {
    for order in GRADED {
        let system = katsura::<3, Zp13>();
        assert_eq!(
            solve(&system, order, &claim(4)).0,
            buchberger_reference(&system, order)
        );
        let system = cyclic::<3, Zp32003>();
        assert_eq!(
            solve(&system, order, &claim(4)).0,
            buchberger_reference(&system, order)
        );
    }
}

fn elements_in(s: &SigF4Statistics) -> usize {
    s.batch_trace
        .iter()
        .flatten()
        .filter(|row| row.contains(" Element "))
        .count()
}

/// A synthetic batch: reducer rows at random leads with random signatures (some equal to a
/// target's, which makes that target singular), and random targets in signature order.
struct Synthetic<F> {
    ncols: usize,
    reducer_rows: Vec<Vec<(u32, F)>>,
    reducer_sigs: Vec<Signature<1>>,
    reducer_at: Vec<u32>,
    targets: Vec<(Signature<1>, Vec<(u32, F)>)>,
}

fn synthetic<F: FiniteField>(seed: u64, ncols: usize, m: usize) -> Synthetic<F> {
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
    let mut next = move |bound: u64| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state % bound
    };
    let sig = |i: u64| Signature::new(Monomial::one(), i as u32);
    let row = |lead: usize, density: u64, next: &mut dyn FnMut(u64) -> u64| {
        let mut entries = vec![(lead as u32, F::new(1 + next(1_000)))];
        for c in lead + 1..ncols {
            if next(100) < density {
                entries.push((c as u32, F::new(1 + next(1_000))));
            }
        }
        entries
    };
    let mut reducer_rows = Vec::new();
    let mut reducer_sigs = Vec::new();
    let mut reducer_at = vec![NONE; ncols];
    for c in 0..ncols {
        if next(100) < 45 {
            let mut r = row(c, 15, &mut next);
            r[0].1 = F::one();
            reducer_at[c] = reducer_rows.len() as u32;
            reducer_rows.push(r);
            // Target signatures are 0..m; a reducer at m or above is admissible for none.
            reducer_sigs.push(sig(next(m as u64 + 4)));
        }
    }
    let targets = (0..m)
        .map(|k| {
            let lead = next(ncols as u64 / 2) as usize;
            (sig(k as u64), row(lead, 30, &mut next))
        })
        .collect();
    Synthetic {
        ncols,
        reducer_rows,
        reducer_sigs,
        reducer_at,
        targets,
    }
}

type Outcomes<F> = Vec<(Kind, Vec<(u32, F)>)>;

impl<F: FiniteField> Synthetic<F> {
    fn block(&self) -> ReducerBlock<'_, 1, F> {
        ReducerBlock {
            order: GREVLEX,
            rows: &self.reducer_rows,
            sigs: &self.reducer_sigs,
            at: &self.reducer_at,
            ncols: self.ncols,
            lane: None,
            field_copies: true,
            layout: None,
            elements: &[],
        }
    }

    /// Design 1's serial pass, written out independently of the engine.
    fn design_1(&self) -> Outcomes<F> {
        let block = self.block();
        let mut workspace = Workspace::new(self.ncols);
        let mut owner: Vec<Option<usize>> = vec![None; self.ncols];
        let mut done: Outcomes<F> = Vec::new();
        for (t, entries) in &self.targets {
            let (mut row, _) = workspace.reduce(entries, |c| {
                block
                    .admissible(c, t)
                    .or_else(|| owner[c].map(|j| done[j].1.as_slice()))
            });
            let kind = block.classify(t, &row);
            if kind == Kind::Element {
                let inverse = row[0].1.inverse();
                row.iter_mut().for_each(|(_, v)| *v *= inverse);
                owner[row[0].0 as usize] = Some(done.len());
            }
            done.push((kind, row));
        }
        done
    }

    fn claim(&self, workers: usize, adversary: Option<Adversary>) -> Outcomes<F>
    where
        F: Send + Sync,
    {
        let block = self.block();
        let job = Claim {
            block: &block,
            targets: &self.targets,
            workers,
            check: true,
            deadline: None,
            live_limit: None,
            fixed_bytes: 0,
            adversary,
        };
        let report = ConcurrentJob::run(job).expect("no budget is set");
        report
            .outcomes
            .into_iter()
            .map(|o| (o.kind, o.row))
            .collect()
    }
}

/// On synthetic batches with singular rows, zero rows and deep cascades (E1, E2), the claim
/// schedule returns design 1's outcome and exact row for every target, at every worker count
/// 1–16, with and without seeded adverse schedules, over two fields.
#[test]
fn test_synthetic_batches_with_singular_rows_match_design_1() {
    fn check<F: FiniteField + Send + Sync>() {
        let (mut singular, mut zero) = (0, 0);
        for seed in 1..=12u64 {
            let batch = synthetic::<F>(seed, 48, 40);
            let expected = batch.design_1();
            singular += expected
                .iter()
                .filter(|(k, _)| *k == Kind::Singular)
                .count();
            zero += expected.iter().filter(|(k, _)| *k == Kind::Zero).count();
            for workers in 1..=16 {
                let adversary = Adversary {
                    seed: seed * 31 + workers as u64,
                    yield_permille: 30,
                    reverse: seed % 2 == 0,
                    slow_announcement: seed % 3,
                    slow_publication: 4 * (seed % 4),
                    cancel_after: None,
                };
                for adversary in [None, Some(adversary)] {
                    assert!(
                        batch.claim(workers, adversary) == expected,
                        "seed {seed} w={workers} {adversary:?}"
                    );
                }
            }
        }
        assert!(singular > 0 && zero > 0, "singular {singular}, zero {zero}");
    }
    check::<Zp32003>();
    check::<Goldilocks>();
}
