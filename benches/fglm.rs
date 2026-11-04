//! Monomial-order conversion: the FGLM pipeline against a direct lexicographic basis.
//!
//! Seven groups, answering seven different questions.
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
//! `operator_storage` times operator *application* under each `OperatorStorage`, on a unit input
//! and on a dense one. Storage itself is exact and needs no benchmark; what needs one is whether a
//! representation that halves the memory also slows the thing the conversion does `O(D)` times.
//!
//! `dependence` times the lex walk's linear algebra on its own, by filling an `IncrementalSpan` to
//! full rank and then testing dependent vectors against it. It is M18-4's benchmark: the
//! triangular combination block is not option-gated, so there is nothing to ablate it against, and
//! what a benchmark can do is keep the quantity it changed under measurement.
//!
//! `recommended` times the configuration a caller gets against `FglmOptions::baseline()`, which is
//! M17's. It is the integration figure M18-5's ablation chose the defaults from, in a form that
//! `cargo bench` can regress against.
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
            fglm_to_lex, fglm_to_lex_with_options, is_grobner_basis, BorderBatch, Dependence,
            FglmOptions, IncrementalSpan, OperatorConstruction, OperatorStorage, QuotientAlgebra,
            QuotientBasis,
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
/// The ablation M18-1 and M18-2 are justified by. `examples/fglm_border.rs` reports the same
/// comparison with the border counters beside it, varies the batch size, and asserts the strategies
/// agree before printing anything.
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

    let mut group = c.benchmark_group("fglm_operator_construction");
    for construction in [
        OperatorConstruction::PerColumn,
        OperatorConstruction::DeduplicatedBorder,
        OperatorConstruction::BatchedBorder,
    ] {
        // `recommended()` rather than `unbounded()` for the batch: 64 targets is the size measured
        // faster than the scalar path everywhere, and an unbounded batch is slower on the planted
        // family. Benchmarking the strategy at a size it is not recommended at would measure the
        // wrong thing.
        let options = FglmOptions::unbounded()
            .with_operator_construction(construction)
            .with_border_batch(BorderBatch::recommended());

        // Equality outside the timed region, so a benchmark cannot report a speedup for computing
        // a different answer.
        assert_eq!(
            QuotientAlgebra::new(&source, SOURCE, &options).expect("finite"),
            reference,
            "{}: {:?} disagrees with the reference",
            name,
            construction
        );

        let label = match construction {
            OperatorConstruction::PerColumn => "per_column",
            OperatorConstruction::DeduplicatedBorder => "deduplicated_border",
            OperatorConstruction::BatchedBorder => "batched_border",
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

/// Each operator-storage strategy, stored and applied.
///
/// Storage is exact and needs no benchmark; what needs one is the *application*, because a
/// representation that halves the memory and slows the thing the conversion does `O(D)` times may
/// not be worth having. Timed on two inputs: a unit vector, as the lex walk starts with, and a
/// vector with every coordinate nonzero, as it ends with. The sparse path skips a zero input
/// coordinate and the dense path still walks `D` cells, so the two inputs need not agree.
fn bench_operator_storage<const N: usize>(
    c: &mut Criterion,
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
) {
    let source = f4(system, SOURCE).expect("within limits");

    let algebras: Vec<(OperatorStorage, QuotientAlgebra<N, F>)> = [
        OperatorStorage::Sparse,
        OperatorStorage::Adaptive,
        OperatorStorage::Dense,
    ]
    .into_iter()
    .map(|storage| {
        let algebra = QuotientAlgebra::new(
            &source,
            SOURCE,
            &FglmOptions::unbounded().with_operator_storage(storage),
        )
        .expect("finite");
        (storage, algebra)
    })
    .collect();

    // Equality outside the timed region: the representations differ, so the *values* differ, and
    // what must agree is every column.
    let d = algebras[0].1.dimension();
    for (storage, algebra) in &algebras[1..] {
        for i in 0..N {
            for j in 0..d {
                assert_eq!(
                    algebra.operator(i).column(j),
                    algebras[0].1.operator(i).column(j),
                    "{}: {:?} disagrees on column {} of T_{}",
                    name,
                    storage,
                    j,
                    i
                );
            }
        }
    }

    let unit = algebras[0].1.one();
    let full: Vec<F> = (0..d).map(|j| F::new(j as u64 + 1)).collect();

    let mut group = c.benchmark_group("fglm_operator_application");
    for (storage, algebra) in &algebras {
        let label = match storage {
            OperatorStorage::Sparse => "sparse",
            OperatorStorage::Adaptive => "adaptive",
            OperatorStorage::Dense => "dense",
        };
        for (input, vector) in [("unit", &unit), ("full", &full)] {
            group.bench_with_input(
                BenchmarkId::new(format!("{}_{}", label, input), name),
                vector,
                |b, v| {
                    b.iter(|| {
                        for i in 0..N {
                            black_box(algebra.operator(i).apply(black_box(v)));
                        }
                    })
                },
            );
        }
    }
    group.finish();
}

/// The dependence test on its own: fill a span to full rank, then test dependent vectors.
///
/// The quantity M18-4 changed. A row's combination is `r + 1` coefficients at rank `r` where M17
/// padded it to `D`, so the inner loop over the combination shortens as well as the allocation —
/// which is why this is timed rather than only counted. It cannot be ablated: the triangular block
/// is not behind an option, and the padded one no longer exists to compare against.
///
/// The vectors are dense and pseudo-random, which is the worst case for the test and not what the
/// walk always hands it: an early candidate's quotient vector is often sparse. `D` stops at 256
/// because filling a span is `O(D^3)` and a dimension of 1,024 would be seconds per iteration.
fn bench_dependence(c: &mut Criterion, dimension: usize) {
    use rand::{prelude::StdRng, SeedableRng};

    // Generated once, outside the timed region, and from a fixed seed so that two runs of the
    // benchmark are two measurements of the same work.
    let mut rng = StdRng::seed_from_u64(0x5eed_1234);
    let independent: Vec<Vec<F>> = (0..dimension)
        .map(|_| (0..dimension).map(|_| F::random(&mut rng)).collect())
        .collect();

    // Probes for the second half: every vector of the dimension is dependent once the span is of
    // full rank, which is exactly the state the lex walk spends most of its candidates in.
    let probes: Vec<Vec<F>> = (0..16)
        .map(|_| (0..dimension).map(|_| F::random(&mut rng)).collect())
        .collect();

    let mut group = c.benchmark_group("fglm_dependence");
    let label = format!("d{}", dimension);

    group.bench_with_input(
        BenchmarkId::new("fill_to_full_rank", &label),
        &independent,
        |b, vectors| {
            b.iter(|| {
                let mut span = IncrementalSpan::<F>::new(dimension);
                for v in vectors {
                    match span.reduce(black_box(v)) {
                        Dependence::Independent {
                            residue,
                            combination,
                        } => span.insert(residue, combination),
                        // Pseudo-random vectors in a field this large are independent with
                        // probability 1 - O(D / p); a dependent one would mean the span was
                        // already full, and silently skipping it would measure less work.
                        Dependence::Dependent { .. } => unreachable!("a dependent random vector"),
                    }
                }
                black_box(span.accepted());
            })
        },
    );

    // The span at full rank, built once: the probe timing is the test and not the filling.
    let mut full = IncrementalSpan::<F>::new(dimension);
    for v in &independent {
        match full.reduce(v) {
            Dependence::Independent {
                residue,
                combination,
            } => full.insert(residue, combination),
            Dependence::Dependent { .. } => unreachable!("a dependent random vector"),
        }
    }
    assert_eq!(full.accepted(), dimension, "the span did not reach rank D");
    assert_eq!(
        full.stored_cells(),
        IncrementalSpan::<F>::cells_at_full_rank(dimension).expect("representable"),
        "the span stores something other than the triangular figure"
    );

    // The same span across every iteration rather than a clone per iteration: `reduce` leaves the
    // rows alone — it only advances the operation counter — and cloning `D^2 + D (D + 1) / 2` cells
    // inside the timed region would be measuring a memcpy.
    group.bench_with_input(
        BenchmarkId::new("test_dependent", &label),
        &probes,
        |b, vectors| {
            b.iter(|| {
                for v in vectors {
                    black_box(matches!(
                        full.reduce(black_box(v)),
                        Dependence::Dependent { .. }
                    ));
                }
            })
        },
    );
    group.finish();
}

/// The configuration a caller gets, against M17's.
///
/// Both halves of the milestone's claim in one place: `recommended()` is `BatchedBorder` with
/// `Adaptive` storage and `baseline()` is `PerColumn` with `Sparse`, and the lex bases are asserted
/// equal outside the timed region. The ablation in `examples/fglm_ablation.rs` is where the
/// defaults were chosen; this is the same comparison under Criterion, so a regression in it fails
/// a `cargo bench` rather than waiting for someone to re-read a table.
fn bench_recommended<const N: usize>(
    c: &mut Criterion,
    name: &str,
    system: &[MultivariatePolynomial<N, F>],
) {
    let source = f4(system, SOURCE).expect("within limits");
    let baseline = FglmOptions::baseline();
    let recommended = FglmOptions::recommended();

    let (reference, _) = fglm_to_lex_with_options(&source, SOURCE, &baseline).expect("convertible");
    let (chosen, statistics) =
        fglm_to_lex_with_options(&source, SOURCE, &recommended).expect("convertible");
    assert_eq!(
        reference, chosen,
        "{}: the recommended configuration changed the lex basis",
        name
    );
    assert_eq!(
        statistics.batches.fallbacks, 0,
        "{}: a batch fell back to the scalar path, so this is not the strategy it claims",
        name
    );

    let mut group = c.benchmark_group("fglm_recommended");
    for (label, options) in [("baseline", &baseline), ("recommended", &recommended)] {
        group.bench_with_input(BenchmarkId::new(label, name), &source, |b, s| {
            b.iter(|| {
                fglm_to_lex_with_options(black_box(s), SOURCE, options).expect("convertible");
            })
        });
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

/// The systems the storage ablation runs on: one family on each side of the half-fill crossover.
fn operator_storage(c: &mut Criterion) {
    bench_operator_storage(c, "katsura-6", &katsura::<6, F>());
    bench_operator_storage(c, "katsura-7", &katsura::<7, F>());
    bench_operator_storage(c, "cyclic-6", &cyclic::<6, F>());
    bench_operator_storage(c, "planted-8", &planted::<8, F>(&planted_point::<8>()));
}

/// The quotient dimensions in the corpus: katsura-7's 64, cyclic-6's 156, planted-8's 256.
fn dependence(c: &mut Criterion) {
    bench_dependence(c, 64);
    bench_dependence(c, 156);
    bench_dependence(c, 256);
}

/// Both sides of the corpus: where reduction dominates, and where the lex walk does.
fn recommended(c: &mut Criterion) {
    bench_recommended(c, "katsura-6", &katsura::<6, F>());
    bench_recommended(c, "katsura-7", &katsura::<7, F>());
    bench_recommended(c, "cyclic-6", &cyclic::<6, F>());
    bench_recommended(c, "planted-8", &planted::<8, F>(&planted_point::<8>()));
}

fn verification(c: &mut Criterion) {
    bench_verification(c, "cyclic-5", &cyclic::<5, F>());
    bench_verification(c, "cyclic-6", &cyclic::<6, F>());
    bench_verification(c, "katsura-5", &katsura::<5, F>());
    bench_verification(c, "katsura-6", &katsura::<6, F>());
    bench_verification(c, "katsura-7", &katsura::<7, F>());
}

criterion_group!(
    fglm,
    stages,
    pipeline,
    operator_construction,
    operator_storage,
    dependence,
    recommended,
    verification
);
criterion_main!(fglm);
