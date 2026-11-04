//! Monomial-order conversion: the FGLM pipeline against a direct lexicographic basis.
//!
//! Four groups, answering four different questions.
//!
//! `stages` times the conversion's parts separately — standard monomial enumeration, quotient
//! algebra construction, and the whole conversion — on a source basis computed outside the timed
//! region. §10.2 of `docs/MILESTONE-FGLM-SOLVING.md` found that the algebra construction dominates
//! rather than the linear algebra, which is the kind of claim a benchmark should keep honest.
//!
//! `pipeline` times what a caller actually pays: a grevlex basis plus conversion, against a lex
//! basis computed directly. Both include the Gröbner computation, so the two figures are
//! comparable; a reduced basis is unique, so they produce the same answer.
//!
//! `operator_construction` times each `OperatorConstruction` strategy against the others, on one
//! prepared source basis, having first asserted outside the timed region that they build the same
//! operators. It is where M18-1's claim is kept honest.
//!
//! `verification` times `is_grobner_basis`, which is what `fglm_to_lex_checked` adds over
//! `fglm_to_lex`. It is in its own group because it is not part of either pipeline — it is the
//! price of not trusting the input, and on katsura-7 it exceeds the conversion it protects.
//!
//! katsura-7 appears only where it can: its lex basis crosses F4's default limits, so there is no
//! `pipeline` figure to compare against, and its `verification` cost is nearly a second.
//!
//! `N` is a const generic, so each instance size is a separate instantiation.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura, planted},
        f4,
        fglm::{
            fglm_to_lex, fglm_to_lex_with_options, is_grobner_basis, FglmOptions,
            OperatorConstruction, QuotientAlgebra, QuotientBasis,
        },
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

const SOURCE: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const TARGET: MonomialOrder = MonomialOrder::Lexicographic;

fn planted_point<const N: usize>() -> Vec<F> {
    (0..N).map(|i| F::new(2 * i as u64 + 3)).collect()
}

/// The conversion's stages, on a source basis prepared outside the timed region.
fn bench_stages<const N: usize>(
    c: &mut Criterion,
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
) {
    let source = f4(system, SOURCE).expect("within limits");
    let options = FglmOptions::unbounded();

    let mut group = c.benchmark_group("fglm_stages");
    group.bench_with_input(
        BenchmarkId::new("standard_monomials", name),
        &source,
        |b, s| {
            b.iter(|| {
                QuotientBasis::new(black_box(s), SOURCE, usize::MAX).expect("finite");
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new("quotient_algebra", name),
        &source,
        |b, s| {
            b.iter(|| {
                QuotientAlgebra::new(black_box(s), SOURCE, &options).expect("finite");
            })
        },
    );
    group.bench_with_input(BenchmarkId::new("conversion", name), &source, |b, s| {
        b.iter(|| {
            fglm_to_lex(black_box(s), SOURCE).expect("convertible");
        })
    });
    group.finish();
}

/// What a caller pays: grevlex plus conversion, against direct lex.
fn bench_pipeline<const N: usize>(
    c: &mut Criterion,
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
) {
    // Asserted equal once, outside the timed region, so the two columns are known to be computing
    // the same thing.
    let source = f4(system, SOURCE).expect("within limits");
    let converted = fglm_to_lex(&source, SOURCE).expect("convertible");
    let direct = f4(system, TARGET).expect("within limits");
    assert_eq!(converted, direct, "{}: the two routes disagree", name);

    let mut group = c.benchmark_group("fglm_pipeline");
    group.bench_with_input(
        BenchmarkId::new("grevlex_then_fglm", name),
        system,
        |b, s| {
            b.iter(|| {
                let basis = f4(black_box(s), SOURCE).expect("within limits");
                fglm_to_lex(&basis, SOURCE).expect("convertible");
            })
        },
    );
    group.bench_with_input(BenchmarkId::new("direct_lex", name), system, |b, s| {
        b.iter(|| {
            f4(black_box(s), TARGET).expect("within limits");
        })
    });
    group.finish();
}

/// Each operator-construction strategy, on the same prepared source basis.
///
/// The ablation M18-1 is justified by, as a Criterion comparison rather than a fastest-of-three:
/// the strategies differ by a third at most, which is within the range where a single timing run
/// can mislead. `examples/fglm_border.rs` reports the same comparison with the border counters
/// beside it, and asserts the two strategies agree before printing anything.
fn bench_operator_construction<const N: usize>(
    c: &mut Criterion,
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
) {
    let source = f4(system, SOURCE).expect("within limits");

    // Equality outside the timed region, so a benchmark cannot report a speedup for computing a
    // different answer.
    let reference = QuotientAlgebra::new(
        &source,
        SOURCE,
        &FglmOptions::unbounded().with_operator_construction(OperatorConstruction::PerColumn),
    )
    .expect("finite");
    let deduplicated = QuotientAlgebra::new(
        &source,
        SOURCE,
        &FglmOptions::unbounded()
            .with_operator_construction(OperatorConstruction::DeduplicatedBorder),
    )
    .expect("finite");
    assert_eq!(reference, deduplicated, "{}: the strategies disagree", name);

    let mut group = c.benchmark_group("fglm_operator_construction");
    for construction in [
        OperatorConstruction::PerColumn,
        OperatorConstruction::DeduplicatedBorder,
    ] {
        let options = FglmOptions::unbounded().with_operator_construction(construction);
        let label = match construction {
            OperatorConstruction::PerColumn => "per_column",
            OperatorConstruction::DeduplicatedBorder => "deduplicated_border",
        };
        group.bench_with_input(BenchmarkId::new(label, name), &source, |b, s| {
            b.iter(|| {
                QuotientAlgebra::new(black_box(s), SOURCE, &options).expect("finite");
            })
        });
        group.bench_with_input(
            BenchmarkId::new(format!("{}_conversion", label), name),
            &source,
            |b, s| {
                b.iter(|| {
                    fglm_to_lex_with_options(black_box(s), SOURCE, &options).expect("convertible");
                })
            },
        );
    }
    group.finish();
}

/// The price of `fglm_to_lex_checked` over `fglm_to_lex`.
fn bench_verification<const N: usize>(
    c: &mut Criterion,
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
) {
    let source = f4(system, SOURCE).expect("within limits");
    assert!(is_grobner_basis(&source, SOURCE));

    let mut group = c.benchmark_group("fglm_verification");
    group.bench_with_input(
        BenchmarkId::new("is_grobner_basis", name),
        &source,
        |b, s| {
            b.iter(|| {
                is_grobner_basis(black_box(s), SOURCE);
            })
        },
    );
    group.finish();
}

fn stages(c: &mut Criterion) {
    bench_stages(c, "cyclic-3", &cyclic::<3, F>());
    bench_stages(c, "cyclic-5", &cyclic::<5, F>());
    bench_stages(c, "cyclic-6", &cyclic::<6, F>());
    bench_stages(c, "katsura-4", &katsura::<4, F>());
    bench_stages(c, "katsura-5", &katsura::<5, F>());
    bench_stages(c, "katsura-6", &katsura::<6, F>());
    bench_stages(c, "katsura-7", &katsura::<7, F>());
    bench_stages(c, "planted-6", &planted::<6, F>(&planted_point::<6>()));
    bench_stages(c, "planted-8", &planted::<8, F>(&planted_point::<8>()));
}

fn pipeline(c: &mut Criterion) {
    // katsura-7 is absent: its lex basis crosses F4's default limits, so there is nothing to
    // compare the conversion against. That absence is the milestone's central result and is
    // measured in `examples/solve_one.rs` rather than hidden here.
    bench_pipeline(c, "cyclic-3", &cyclic::<3, F>());
    bench_pipeline(c, "cyclic-5", &cyclic::<5, F>());
    bench_pipeline(c, "cyclic-6", &cyclic::<6, F>());
    bench_pipeline(c, "katsura-4", &katsura::<4, F>());
    bench_pipeline(c, "katsura-5", &katsura::<5, F>());
    bench_pipeline(c, "katsura-6", &katsura::<6, F>());
    bench_pipeline(c, "planted-6", &planted::<6, F>(&planted_point::<6>()));
    bench_pipeline(c, "planted-8", &planted::<8, F>(&planted_point::<8>()));
}

/// katsura and cyclic are where reduction dominates, so they are where deduplication can show.
/// The planted family is here because it is where it cannot: the lex walk is most of its
/// conversion, and a strategy chosen from katsura alone would be chosen on partial evidence.
fn operator_construction(c: &mut Criterion) {
    bench_operator_construction(c, "katsura-5", &katsura::<5, F>());
    bench_operator_construction(c, "katsura-6", &katsura::<6, F>());
    bench_operator_construction(c, "katsura-7", &katsura::<7, F>());
    bench_operator_construction(c, "cyclic-5", &cyclic::<5, F>());
    bench_operator_construction(c, "cyclic-6", &cyclic::<6, F>());
    bench_operator_construction(c, "planted-6", &planted::<6, F>(&planted_point::<6>()));
    bench_operator_construction(c, "planted-8", &planted::<8, F>(&planted_point::<8>()));
}

fn verification(c: &mut Criterion) {
    bench_verification(c, "cyclic-5", &cyclic::<5, F>());
    bench_verification(c, "cyclic-6", &cyclic::<6, F>());
    bench_verification(c, "katsura-5", &katsura::<5, F>());
    bench_verification(c, "katsura-6", &katsura::<6, F>());
    bench_verification(c, "katsura-7", &katsura::<7, F>());
}

criterion_group!(fglm, stages, pipeline, operator_construction, verification);
criterion_main!(fglm);
