//! Live agreement between Zeebra and the two M25 comparands it drives through adapters.
//!
//! Every test that *drives a tool* is `#[ignore]`d; the ones that only read the frozen corpus run
//! everywhere. The reason for the first half is the same one `src/grobner/differential/mod.rs`
//! gives for its live Singular sweep: **CI has no Julia and no Sagebrush driver, and a test that
//! silently passed when the tool is absent would be worse than no test.** The reason for the second
//! is #386: a corpus defect behind an `#[ignore]` is a defect CI cannot see, so an assertion that
//! needs no tool does not belong behind one. The offline half of each
//! adapter — capability bounds, script and input generation, marker parsing, the missing-binary
//! path — is covered by ordinary unit tests in `src/grobner/external/{groebner_jl,sagebrush}.rs`
//! and runs everywhere.
//!
//! Run them after `tools/external/provision.sh`:
//!
//! ```text
//! ZEEBRA_JULIA=$HOME/.local/opt/zeebra-ext/bin/julia \
//! ZEEBRA_JULIA_DEPOT=$HOME/.local/opt/zeebra-ext/julia-depot \
//! ZEEBRA_SAGEBRUSH_DRIVER=$HOME/.local/opt/zeebra-ext/bin/sagebrush-gb-driver \
//!   cargo test --release --test external_comparands -- --ignored --test-threads 1
//! ```
//!
//! # Why the comparison is term-for-term and not only on leading monomials
//!
//! [`Invariants`] carries leading monomials, basis cardinality and quotient dimension, which is
//! what a *cross-library* check can rely on in general. It is also a weaker test than these tools
//! permit: a reduced Gröbner basis is unique given the ideal and the order, so two correct answers
//! must agree on **every coefficient**. The weaker check is what the contract compares because it
//! survives differences in printing; the stronger one is what these tests assert, because catching
//! a wrong coefficient is worth the normalization code in [`canonical_basis`].

use std::time::Duration;

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        benchmark_systems::katsura,
        differential::{monomial_to_string, polynomial_to_string},
        external::{
            corpus, ExternalSolver, FieldSpec, GroebnerJlSolver, Instance, Invariants, Limits,
            RunFailure, RunStatus, SagebrushSolver, Task,
        },
        f4, f4_with_options, F4Options,
    },
    Monomial, MonomialOrder, MultivariatePolynomial, One, Zero,
};

/// The prime the provisioning smoke test used: 2^30 + 3, inside every comparand's range.
const P: u64 = 1_073_741_827;

/// How long Zeebra's own F4 is given per rung when it is acting as the oracle.
///
/// Not a measurement and not a claim about Zeebra's speed — it is the budget that keeps the sweep
/// runnable. A rung that crosses it has **no oracle**, which is printed, and the comparand's own
/// run is still exercised and still checked for a coherent status.
const ZEEBRA_ORACLE_BUDGET: Duration = Duration::from_secs(120);
type F = PrimeFieldElement64<P>;

/// The corpus's reference field, so a corpus row is checked at the characteristic it was frozen at.
type Ref = PrimeFieldElement64<{ corpus::REFERENCE_CHARACTERISTIC }>;

/// The quotient dimension, or `None` when the ideal is not zero-dimensional.
///
/// Counts the standard monomials — those divisible by no leading monomial of the basis — and gives
/// up as soon as the count shows the staircase is unbounded in some variable, which is the
/// `cyclic-4` case.
fn quotient_dimension<const N: usize>(
    basis: &[MultivariatePolynomial<N, Ref>],
    order: MonomialOrder,
) -> Option<usize> {
    let leads: Vec<Monomial<N>> = basis.iter().map(|f| f.leading_monomial(order)).collect();
    // The staircase is finite exactly when every variable has a pure power in the leading ideal.
    let bounds: Vec<u32> = (0..N)
        .map(|i| {
            leads
                .iter()
                .filter(|m| {
                    m.exponents()
                        .iter()
                        .enumerate()
                        .all(|(j, e)| j == i || *e == 0)
                })
                .map(|m| m.exponents()[i])
                .min()
                .unwrap_or(0)
        })
        .collect();
    if bounds.contains(&0) {
        return None;
    }
    let mut count = 0usize;
    let mut exponents = vec![0u32; N];
    loop {
        let candidate = Monomial::<N>::new(&exponents);
        let divisible = leads.iter().any(|lead| {
            candidate
                .exponents()
                .iter()
                .zip(lead.exponents())
                .all(|(c, l)| c >= l)
        });
        if !divisible {
            count += 1;
        }
        let mut position = 0;
        while position < N {
            exponents[position] += 1;
            if exponents[position] < bounds[position] {
                break;
            }
            exponents[position] = 0;
            position += 1;
        }
        if position == N {
            return Some(count);
        }
    }
}

/// A per-test scratch directory, so two tests never hand the same filename to two processes.
fn scratch(tag: &str) -> std::path::PathBuf {
    let root = std::env::temp_dir().join(format!(
        "zeebra-external-comparands-{}-{}",
        tag,
        std::process::id()
    ));
    std::fs::create_dir_all(&root).expect("a writable scratch directory");
    root
}

/// An [`Instance`] carrying Zeebra's own polynomials as the text every comparand is given.
fn instance<const N: usize>(
    name: &str,
    family: &str,
    system: &[MultivariatePolynomial<N, F>],
    variables: &[&str],
    order: MonomialOrder,
) -> Instance {
    Instance::new(
        name,
        family,
        FieldSpec::prime(P),
        variables.iter().map(|v| v.to_string()).collect(),
        system
            .iter()
            .map(|f| polynomial_to_string(f, variables, order))
            .collect(),
        order,
    )
}

/// Zeebra's own answer, as the invariants a comparand's answer is checked against.
fn zeebra_invariants<const N: usize>(
    system: &[MultivariatePolynomial<N, F>],
    variables: &[&str],
    order: MonomialOrder,
) -> (Invariants, Vec<String>) {
    let basis = f4(system, order).expect("Zeebra computes the basis");
    let leading = basis
        .iter()
        .map(|f| monomial_to_string(&f.leading_monomial(order), variables))
        .collect();
    let elements: Vec<String> = basis
        .iter()
        .map(|f| polynomial_to_string(f, variables, order))
        .collect();
    (
        Invariants::none().with_leading_monomials(leading),
        canonical_basis(&elements),
    )
}

/// A basis as a sorted list of sorted `coefficient*monomial` term lists.
///
/// The three tools spell the same polynomial three ways — Zeebra omits a unit coefficient,
/// Groebner.jl spaces its `+` signs, the Sagebrush driver always prints the coefficient — so a
/// textual diff would report a purely notational disagreement. Normalizing to explicit
/// coefficients over sorted monomials makes the comparison term-for-term over the mathematics.
/// Every tool prints its residues in `[0, p)`, so no sign reconciliation is needed.
fn canonical_basis(elements: &[String]) -> Vec<String> {
    let mut canonical: Vec<String> = elements.iter().map(|e| canonical_polynomial(e)).collect();
    canonical.sort();
    canonical
}

/// One polynomial as a sorted, explicit-coefficient term list.
fn canonical_polynomial(element: &str) -> String {
    let compact: String = element.chars().filter(|c| !c.is_whitespace()).collect();
    let mut terms: Vec<String> = compact
        .split('+')
        .filter(|term| !term.is_empty())
        .map(|term| {
            // A term is `monomial`, `coefficient`, or `coefficient*monomial`. A leading factor that
            // parses as an integer is the coefficient; anything else means the coefficient is one.
            let (head, rest) = match term.split_once('*') {
                Some((head, rest)) => (head, Some(rest)),
                None => (term, None),
            };
            match (head.parse::<u64>(), rest) {
                (Ok(coefficient), Some(monomial)) => format!("{}*{}", coefficient, monomial),
                (Ok(coefficient), None) => format!("{}*1", coefficient),
                (Err(_), _) => format!("1*{}", term),
            }
        })
        .collect();
    terms.sort();
    terms.join("+")
}

/// Zeebra's own answer for a corpus rung, built by **parsing the instance's own text**.
///
/// Stronger than rebuilding the system from the generator function, and more robust. Stronger
/// because the bytes parsed here are the bytes every engine is handed, so an agreement covers
/// Zeebra's parser too rather than assuming it; the corpus renders through
/// `polynomial_to_string` and this reads back through `MultivariatePolynomial::parse`, so a
/// round-trip failure in either shows up as a disagreement rather than as a silently different
/// problem. More robust because the dispatch below is on **variable count**, not on family name:
/// a rung added at an existing width is covered with no edit, which is the failure mode that
/// broke the neighbouring msolve test when the ladder grew.
///
/// `None` when Zeebra's own F4 crosses one of its `F4Options` limits. That is a fact about
/// Zeebra's budget and not a disagreement, so the rung is reported and skipped rather than failed.
///
/// **Zeebra's side is explicitly time-bounded**, by [`ZEEBRA_ORACLE_BUDGET`]. The default
/// `F4Options` limits are *resource* bounds — 20 million live nonzeros, 320 MB — with
/// `max_wall_time` unset, so a hard rung such as fourteen random quadratics in fourteen variables
/// can grind for a long time before crossing either. An oracle that takes longer than the engines
/// it is checking makes the sweep impractical to run at all, which is how a test stops being run
/// and therefore stops being true. Declaring the budget is also symmetric with how the external
/// side is bounded: every comparand gets a `Limits::wall`, so Zeebra gets one too, and a crossing
/// is reported in the same breath rather than inferred from a wall-clock that nobody set.
fn zeebra_for<const N: usize>(instance: &Instance) -> Option<(Invariants, Vec<String>)> {
    let names: Vec<&str> = instance.variable_refs();
    let fixed: [&str; N] = names.clone().try_into().ok()?;
    let system: Vec<MultivariatePolynomial<N, Ref>> = instance
        .system
        .iter()
        .map(|generator| {
            MultivariatePolynomial::parse(generator, fixed).unwrap_or_else(|e| {
                panic!(
                    "Zeebra cannot parse its own corpus text {:?}: {}",
                    generator, e
                )
            })
        })
        .collect();
    let options = F4Options {
        max_wall_time: Some(ZEEBRA_ORACLE_BUDGET),
        ..F4Options::default()
    };
    let (basis, _statistics) = f4_with_options(&system, instance.order, &options).ok()?;
    let leading = basis
        .iter()
        .map(|f| monomial_to_string(&f.leading_monomial(instance.order), &names))
        .collect();
    let mut invariants = Invariants::none().with_leading_monomials(leading);
    if let Some(dimension) = quotient_dimension(&basis, instance.order) {
        invariants = invariants.with_quotient_dimension(dimension);
    }
    let elements: Vec<String> = basis
        .iter()
        .map(|f| polynomial_to_string(f, &names, instance.order))
        .collect();
    Some((invariants, canonical_basis(&elements)))
}

/// Zeebra's answer for any reference-characteristic rung, dispatched on variable count.
///
/// `None` for a rung at some other characteristic, which does not share `Ref`'s field type, or
/// at a width with no compiled instantiation. Both are "no oracle here", never "the tool was wrong".
fn zeebra_oracle(instance: &Instance) -> Option<(Invariants, Vec<String>)> {
    if instance.field.characteristic != corpus::REFERENCE_CHARACTERISTIC {
        return None;
    }
    match instance.variables.len() {
        4 => zeebra_for::<4>(instance),
        5 => zeebra_for::<5>(instance),
        6 => zeebra_for::<6>(instance),
        7 => zeebra_for::<7>(instance),
        10 => zeebra_for::<10>(instance),
        14 => zeebra_for::<14>(instance),
        _ => None,
    }
}

/// A Groebner.jl solver over the provisioned Julia, or `None` if it is not installed.
fn groebner_jl(tag: &str) -> Option<GroebnerJlSolver> {
    let mut solver = GroebnerJlSolver::from_env(scratch(tag)).expect("a scratch directory");
    solver.probe_version().ok().map(|_| solver)
}

/// A Sagebrush solver over the provisioned driver, or `None` if it is not installed.
fn sagebrush(tag: &str) -> Option<SagebrushSolver> {
    let mut solver = SagebrushSolver::from_env(scratch(tag)).expect("a scratch directory");
    solver.probe_version().ok().map(|_| solver)
}

/// The answer a run produced, or a panic naming what happened instead.
fn answered(report: &zeebra::grobner::external::RunReport) -> &zeebra::grobner::external::Answer {
    match &report.status {
        RunStatus::Complete(answer) | RunStatus::Verified(answer, _) => answer,
        other => panic!(
            "{} on {} did not answer: {:?}",
            report.solver, report.instance, other
        ),
    }
}

/// Assert that `theirs` agrees with `ours` on every shared invariant, and that something was
/// shared.
///
/// Two empty `Invariants` agree vacuously, which is not a verification — so the overlap is
/// asserted and not merely computed.
fn assert_agrees(solver: &str, instance: &str, ours: &Invariants, theirs: &Invariants) {
    let overlap = ours.overlap(theirs);
    assert!(
        overlap > 0,
        "{} on {} shares no invariant with Zeebra, so nothing was checked",
        solver,
        instance
    );
    let disagreements = ours.agree(theirs);
    assert!(
        disagreements.is_empty(),
        "{} on {} disagrees with Zeebra on {} of {} shared invariants: {:?}",
        solver,
        instance,
        disagreements.len(),
        overlap,
        disagreements
    );
}

/// The reference system from the provisioning smoke test, in `x > y > z`.
fn smoke_system() -> Vec<MultivariatePolynomial<3, F>> {
    let variables = ["x", "y", "z"];
    let _ = variables;
    let one = F::one();
    let minus_one = F::zero() - one;
    let monomial = |e: [u32; 3]| Monomial::new(&e);
    vec![
        // x^2 + y^2 + z^2 - 1
        MultivariatePolynomial::new(&[
            (monomial([2, 0, 0]), one),
            (monomial([0, 2, 0]), one),
            (monomial([0, 0, 2]), one),
            (monomial([0, 0, 0]), minus_one),
        ]),
        // x*y + y*z + z*x - 1
        MultivariatePolynomial::new(&[
            (monomial([1, 1, 0]), one),
            (monomial([0, 1, 1]), one),
            (monomial([1, 0, 1]), one),
            (monomial([0, 0, 0]), minus_one),
        ]),
        // x*y*z - 1
        MultivariatePolynomial::new(&[
            (monomial([1, 1, 1]), one),
            (monomial([0, 0, 0]), minus_one),
        ]),
    ]
}

/// The asymmetric system whose lex basis differs under a permuted variable order.
///
/// `{x*y - 1, y^2 - z, z^3 - x}`. Under lex with `x > y > z` its leading monomials are
/// `{x, y, z^7}`; with `z > y > x` they are `{z, y, x^7}`. A tool that silently reordered the
/// variables would return the second where the first was asked for, and no invariant other than
/// the leading monomials would notice.
fn asymmetric_system(permuted: bool) -> (Vec<MultivariatePolynomial<3, F>>, Vec<&'static str>) {
    let one = F::one();
    let minus_one = F::zero() - one;
    let monomial = |e: [u32; 3]| Monomial::new(&e);
    // Index 0, 1, 2 are the first, second and third *declared* variables. Under the permuted
    // naming the same polynomials are declared with the names reversed, which is what makes the
    // two runs the same ideal posed under two different orders.
    let system = vec![
        // v0*v1 - 1
        MultivariatePolynomial::new(&[
            (monomial([1, 1, 0]), one),
            (monomial([0, 0, 0]), minus_one),
        ]),
        // v1^2 - v2
        MultivariatePolynomial::new(&[
            (monomial([0, 2, 0]), one),
            (monomial([0, 0, 1]), minus_one),
        ]),
        // v2^3 - v0
        MultivariatePolynomial::new(&[
            (monomial([0, 0, 3]), one),
            (monomial([1, 0, 0]), minus_one),
        ]),
    ];
    let variables = if permuted {
        vec!["z", "y", "x"]
    } else {
        vec!["x", "y", "z"]
    };
    (system, variables)
}

/// Groebner.jl reproduces Zeebra's basis term for term on the reference smoke system.
///
/// The strongest single check available: leading monomials, cardinality, quotient dimension and
/// every coefficient of all six elements.
#[test]
#[ignore = "needs the provisioned Julia and Groebner.jl"]
fn test_groebner_jl_reproduces_zeebras_basis_term_for_term() {
    let Some(mut solver) = groebner_jl("jl-smoke") else {
        panic!("Groebner.jl is not installed; see the module documentation")
    };
    let variables = ["x", "y", "z"];
    let system = smoke_system();
    let order = MonomialOrder::GradedReverseLexicographic;
    let (ours, our_basis) = zeebra_invariants(&system, &variables, order);
    let instance = instance("smoke-3", "smoke", &system, &variables, order);

    let report = solver.run(
        &instance,
        Task::ReducedGrobnerBasis,
        &Limits::wall(Duration::from_secs(120)),
    );
    let answer = answered(&report);
    assert_agrees("groebner.jl", &instance.name, &ours, &answer.invariants);
    assert_eq!(
        answer.invariants.quotient_dimension,
        Some(12),
        "the reference system's quotient algebra has dimension 12"
    );
    assert_eq!(
        canonical_basis(answer.basis.as_ref().expect("a basis")),
        our_basis,
        "term-for-term agreement, every coefficient included"
    );
}

/// Sagebrush reproduces Zeebra's basis term for term on the reference smoke system.
#[test]
#[ignore = "needs the provisioned sagebrush-gb-driver"]
fn test_sagebrush_reproduces_zeebras_basis_term_for_term() {
    let Some(mut solver) = sagebrush("sb-smoke") else {
        panic!("the Sagebrush driver is not installed; see the module documentation")
    };
    let variables = ["x", "y", "z"];
    let system = smoke_system();
    let order = MonomialOrder::GradedReverseLexicographic;
    let (ours, our_basis) = zeebra_invariants(&system, &variables, order);
    let instance = instance("smoke-3", "smoke", &system, &variables, order);

    let report = solver.run(
        &instance,
        Task::ReducedGrobnerBasis,
        &Limits::wall(Duration::from_secs(120)),
    );
    let answer = answered(&report);
    assert_agrees("sagebrush", &instance.name, &ours, &answer.invariants);
    assert_eq!(
        canonical_basis(answer.basis.as_ref().expect("a basis")),
        our_basis,
        "term-for-term agreement, every coefficient included"
    );
}

/// Sagebrush's two routes to a lex basis agree with Zeebra, and with each other, term for term.
///
/// The point of running both: `LexBasis` is the engine's direct lex F4 and `LexBasisByConversion`
/// is `fglm::groebner_fglm`, two different algorithms whose reduced bases must be *identical*
/// because a reduced Gröbner basis is unique given the ideal and the order. So this is a check on
/// Sagebrush against Zeebra and a check of Sagebrush against itself at the same time, and it is the
/// only place in this module where a tool's two independent routes can be compared at all —
/// Groebner.jl 0.10.11 has no FGLM.
///
/// The quotient dimension is asserted explicitly because it is the invariant #315 added: the driver
/// counts the standard monomials itself, Sagebrush exposing only a boolean, so agreeing with
/// Zeebra on it is a genuine third overlap rather than a restatement of the leading monomials.
#[test]
#[ignore = "needs the provisioned sagebrush-gb-driver"]
fn test_sagebrushs_two_lex_routes_agree_with_zeebra_and_with_each_other() {
    let Some(mut solver) = sagebrush("sb-lex") else {
        panic!("the Sagebrush driver is not installed; see the module documentation")
    };
    let variables = ["x", "y", "z"];
    let system = smoke_system();
    let order = MonomialOrder::Lexicographic;
    let (ours, our_basis) = zeebra_invariants(&system, &variables, order);
    let instance = instance("smoke-3-lex", "smoke", &system, &variables, order);

    let mut bases = Vec::new();
    for task in [Task::LexBasis, Task::LexBasisByConversion] {
        assert!(
            solver.supports(&instance, task).is_supported(),
            "{} is offered at the reference characteristic",
            task
        );
        let report = solver.run(&instance, task, &Limits::wall(Duration::from_secs(120)));
        let answer = answered(&report);
        assert_agrees("sagebrush", &instance.name, &ours, &answer.invariants);
        assert_eq!(
            answer.invariants.quotient_dimension,
            Some(12),
            "{}: the reference system's quotient algebra has dimension 12",
            task
        );
        let basis = canonical_basis(answer.basis.as_ref().expect("a basis"));
        assert_eq!(
            basis, our_basis,
            "{}: term-for-term agreement with Zeebra, every coefficient included",
            task
        );
        bases.push(basis);
    }
    assert_eq!(
        bases[0], bases[1],
        "a direct lex F4 and an FGLM conversion must return the same reduced basis"
    );
}

/// Every corpus rung either agrees with Zeebra or is cleanly unsupported — no rung is skipped.
///
/// Driven from `grobner::external::corpus::ladder()`, so a family added to the corpus is covered
/// here without an edit. **That property is the point of the shape**: the msolve adapter's
/// equivalent test matches rung names against compiled instantiations and panics on one it does
/// not know, which broke the moment the corpus grew from seven rungs to eighteen. This test
/// instead splits the ladder into the rungs it can hold Zeebra's own answer for and the rest, and
/// asserts a floor on the first group so growth can never silently empty it.
///
/// Three things are checked for every rung, including the ones with no Zeebra side:
///
/// 1. **The identity digest matches the frozen one**, so a row is the problem the corpus pinned.
/// 2. **`supports()` and the run agree.** A rung the tool cannot represent must come back
///    `Unsupported` with no measurement — never a slow row, and never a wall-clock stop, which
///    would be timing-adjacent for what is a capability gap.
/// 3. **A rung that runs comes back `Complete`** and, for Groebner.jl, has therefore already had
///    its echoed generators checked against the sent system inside the adapter. On the fourteen-
///    variable MQ rungs that makes a `Complete` status *itself* the proof that `x1` and `x10` were
///    read apart.
#[test]
#[ignore = "needs the provisioned Julia and sagebrush-gb-driver"]
fn test_every_corpus_rung_either_agrees_with_zeebra_or_is_cleanly_unsupported() {
    let mut julia = groebner_jl("jl-corpus");
    let mut sage = sagebrush("sb-corpus");
    assert!(
        julia.is_some() || sage.is_some(),
        "neither comparand is installed, so nothing would be checked"
    );
    let order = MonomialOrder::GradedReverseLexicographic;
    // Short enough that the whole ladder finishes in a few minutes. The top rungs are *expected*
    // to stop here, which is why `StoppedByLimit` is handled as an outcome rather than an error.
    let limits = Limits::wall(Duration::from_secs(90));
    let mut compared_against_zeebra = 0;
    let mut ran = 0;
    let mut unsupported = 0;
    let mut stopped = 0;
    let mut reported: Vec<String> = Vec::new();
    let mut no_oracle: Vec<&str> = Vec::new();

    for entry in corpus::ladder() {
        let instance = corpus::instance(entry.name, corpus::REFERENCE_CHARACTERISTIC, order)
            .unwrap_or_else(|| panic!("{} is on the ladder and must build", entry.name));
        assert_eq!(
            Some(instance.digest().as_str()),
            entry.digest_at(instance.field.characteristic),
            "{} is not the problem the corpus froze",
            entry.name
        );

        // Zeebra's own answer, parsed from the instance's own text and dispatched on variable
        // count, so a rung added at an existing width needs no edit here.
        let ours = zeebra_oracle(&instance);
        if ours.is_none() {
            no_oracle.push(entry.name);
        }
        if let Some((ours, _)) = &ours {
            assert_eq!(
                ours.quotient_dimension.is_some(),
                entry.zero_dimensional,
                "{}: Zeebra and the corpus disagree about zero-dimensionality",
                entry.name
            );
        }

        for (name, solver) in [
            (
                "groebner.jl",
                julia.as_mut().map(|s| s as &mut dyn ExternalSolver),
            ),
            (
                "sagebrush",
                sage.as_mut().map(|s| s as &mut dyn ExternalSolver),
            ),
        ] {
            let Some(solver) = solver else { continue };
            let declared = solver.supports(&instance, Task::ReducedGrobnerBasis);
            let report = solver.run(&instance, Task::ReducedGrobnerBasis, &limits);

            if !declared.is_supported() {
                // The capability path. `Unsupported` and not `StoppedByLimit`, and no measurement
                // at all — a zero wall time here would read as an instantaneous success to
                // anything that did not check the status.
                assert!(
                    matches!(report.status, RunStatus::Unsupported(_)),
                    "{} on {}: supports() said no but run() returned {:?}",
                    name,
                    entry.name,
                    report.status
                );
                assert!(!report.status.is_timing_evidence());
                assert!(report.measurement.is_unmeasured());
                assert!(report.was_skipped());
                unsupported += 1;
                continue;
            }

            // Four outcomes are legitimate for a rung the tool accepts, and conflating them is
            // what the status taxonomy exists to prevent. Only the fourth is a test failure.
            match &report.status {
                RunStatus::Complete(answer) => {
                    assert!(
                        !report.status.is_verified(),
                        "{} must stay Complete: an adapter never promotes its own answer",
                        name
                    );
                    ran += 1;
                    if let Some((ours, our_basis)) = &ours {
                        assert_agrees(name, &instance.name, ours, &answer.invariants);
                        assert_eq!(
                            canonical_basis(answer.basis.as_ref().expect("a basis")),
                            *our_basis,
                            "{} on {} differs from Zeebra term for term",
                            name,
                            entry.name
                        );
                        compared_against_zeebra += 1;
                    }
                }
                // Expected at the top of the ladder: the corpus documents `Challenging` as
                // "expected to exhaust at least one engine's limits ... the one that needs
                // `StoppedByLimit` to be a first-class outcome". The wall time here **is** the
                // limit, so the only thing to assert is that nothing downstream may read it as a
                // measurement.
                RunStatus::StoppedByLimit(stop) => {
                    assert!(
                        !report.status.is_timing_evidence(),
                        "a limit stop is a lower bound, never a timing"
                    );
                    assert_ne!(
                        entry.rung,
                        corpus::Rung::Easy,
                        "{} on {} stopped at a limit, which an Easy rung must not do: {}",
                        name,
                        entry.name,
                        stop
                    );
                    stopped += 1;
                }
                // A capability the tool discovers at run time rather than declaring, which for
                // Sagebrush is `exponents too large to pack` once `64 / n` bits will not hold the
                // intermediate degrees. `supports` cannot predict it — a bound there must describe
                // what the tool declares, not what a run will do — so it arrives here, and it is
                // still not a timing.
                RunStatus::Failed(RunFailure::Reported { message }) => {
                    assert!(!report.status.is_timing_evidence());
                    reported.push(format!("{} on {}: {}", name, entry.name, message));
                }
                other => panic!(
                    "{} on {} failed in a way that is not a capability or a limit: {:?}",
                    name, entry.name, other
                ),
            }
        }
    }

    // Floors rather than exact counts, so the corpus can grow without editing this test — but it
    // cannot grow into covering nothing.
    // The floor is the seven Katsura and Cyclic rungs across two tools. Deliberately **not** the
    // 24 this run achieved: whether a rung gets an oracle depends on Zeebra crossing
    // `ZEEBRA_ORACLE_BUDGET`, which is a property of one machine under one load, so pinning the
    // observed number would make the test fail for a reason that is not a regression. Those seven
    // are sub-second benchmarks and are the coverage that is genuinely guaranteed.
    assert!(
        compared_against_zeebra >= 14,
        "only {} rung/solver pairs were checked against Zeebra; the seven Katsura and Cyclic rungs across two tools are the floor",
        compared_against_zeebra
    );
    // And one rung is named rather than counted, because it is the one carrying the load: at
    // fourteen variables `x1` is a prefix of `x10`, and this is the rung that turns that check
    // from "it completed and the echoed generators matched" into a full basis agreement. A count
    // alone would let it vanish into the budget while staying above the floor.
    assert!(
        !no_oracle.contains(&"mq-planted-14"),
        "mq-planted-14 lost its Zeebra oracle, so the fourteen-variable prefix case is no longer \
         checked as a basis agreement; raise ZEEBRA_ORACLE_BUDGET rather than dropping the rung"
    );
    assert!(
        ran > 0 && unsupported > 0,
        "ran {}, unsupported {} — a ladder that is all one or all the other is not exercising both paths",
        ran,
        unsupported
    );
    // Printed rather than asserted: a run-time capability limit is a finding about the tool, and
    // the test's job is to surface it rather than to have an opinion about how many there should be.
    println!(
        "corpus ladder: {} completed, {} compared against Zeebra, {} unsupported, {} stopped by limit, {} tool-reported limits",
        ran,
        compared_against_zeebra,
        unsupported,
        stopped,
        reported.len()
    );
    for line in &reported {
        println!("  tool-reported limit: {}", line);
    }
    // Printed so a rung that quietly lost its oracle is visible rather than merely uncounted.
    if !no_oracle.is_empty() {
        println!(
            "  no Zeebra oracle (other characteristic, or Zeebra hit its own F4 budget): {:?}",
            no_oracle
        );
    }
}

/// Sagebrush refuses a field above `2^62`; **Groebner.jl does not**.
///
/// Groebner.jl's native range is every prime below `typemax(UInt64)`
/// (`src/groebner/parameters.jl:175`), so it **can** represent `2^64 − 353`, and measured directly
/// it returns a correct basis there. Sagebrush stops at `2^62`, msolve and Singular at `2^31`.
///
/// So `supports()` says yes, because [`ExternalSolver::supports`] is a statement about the tool's
/// declared capability and nothing else. Whether a *cross-library timing* may be published is a
/// different question, and a [`corpus::CorpusEntry`]'s `Equivalence` is where it belongs: one
/// engine in range licenses a timing (`SoleComparand`) and does not corroborate it.
#[test]
#[ignore = "needs the provisioned Julia and sagebrush-gb-driver"]
fn test_a_field_above_2_62_is_representable_only_by_groebner_jl() {
    let wide = Instance::new(
        "wide64-pair",
        "wide64",
        FieldSpec::prime(corpus::WIDE_64_CHARACTERISTIC),
        vec!["x1".to_string(), "x2".to_string()],
        vec!["x1^2+x2-3".to_string(), "x2^2-5".to_string()],
        MonomialOrder::GradedReverseLexicographic,
    );

    if let Some(solver) = sagebrush("sb-wide64") {
        // Above Sagebrush's own 2^62 modulus gate, so this is a real capability gap.
        match solver.supports(&wide, Task::ReducedGrobnerBasis) {
            zeebra::grobner::external::Support::No(
                zeebra::grobner::external::Unsupported::Characteristic {
                    supported_below, ..
                },
            ) => assert_eq!(supported_below, 1 << 62),
            other => panic!("Sagebrush cannot represent 2^64 - 353, got {:?}", other),
        }
    }
    if let Some(solver) = groebner_jl("jl-wide64") {
        assert!(
            solver
                .supports(&wide, Task::ReducedGrobnerBasis)
                .is_supported(),
            "Groebner.jl's native range covers every prime below typemax(UInt64)"
        );
    }
}

/// Neither comparand confuses `x1` with `x10`, which is the one error agreement cannot detect.
///
/// **Why this needs its own test.** Every engine is handed the same bytes, so a tokenizer that
/// reads `x1*x10` as `x1*x1*0` misreads it identically everywhere — and the cross-validation this
/// whole milestone rests on then shows four engines agreeing with each other while all four answer
/// a different question. Agreement is blind to it by construction.
///
/// The system is built so a misread is loud rather than subtle: `x1*x10 - 1` with the prefix
/// collapsed becomes `x1^2*0 - 1 = -1`, the ideal becomes the whole ring, and the basis collapses
/// from fifteen elements to `{1}`.
///
/// The corpus tops out at seven variables, so this rung is deliberately hand-rolled: it is testing
/// the two parsers rather than the ladder, and it is here so the hazard is pinned **before** a
/// ten-or-more-variable rung is added rather than after.
///
/// **Both adapters now also check their own generator echo on every run** — Groebner.jl's `@gen`
/// since #260, Sagebrush's `#gen` since #329 — so a `Complete` status on this rung is *itself* the
/// proof that the two names were read apart, for both tools. This test keeps its own assertions
/// anyway: it checks the *consequence* in the computed basis rather than the echo, so it would
/// still fail if a parser read the system correctly and then packed or reduced it wrongly, which
/// the echo cannot see.
#[test]
#[ignore = "needs the provisioned Julia and sagebrush-gb-driver"]
fn test_neither_comparand_confuses_a_variable_with_its_prefix() {
    let mut julia = groebner_jl("jl-prefix");
    let mut sage = sagebrush("sb-prefix");
    assert!(
        julia.is_some() || sage.is_some(),
        "neither comparand is installed, so nothing would be checked"
    );
    let order = MonomialOrder::GradedReverseLexicographic;

    let variables: Vec<String> = (1..=14).map(|i| format!("x{}", i)).collect();
    let names: Vec<&str> = variables.iter().map(String::as_str).collect();
    let mut system = vec!["x1*x10-1".to_string(), "x1^2-x10".to_string()];
    system.extend(
        (1..=14)
            .filter(|i| *i != 1 && *i != 10)
            .map(|i| format!("x{}-1", i)),
    );
    let instance = Instance::new(
        "prefix-collision-14",
        "prefix",
        FieldSpec::prime(P),
        names.iter().map(|v| v.to_string()).collect(),
        system,
        order,
    );

    for (name, solver) in [
        (
            "groebner.jl",
            julia.as_mut().map(|s| s as &mut dyn ExternalSolver),
        ),
        (
            "sagebrush",
            sage.as_mut().map(|s| s as &mut dyn ExternalSolver),
        ),
    ] {
        let Some(solver) = solver else { continue };
        let report = solver.run(
            &instance,
            Task::ReducedGrobnerBasis,
            &Limits::wall(Duration::from_secs(120)),
        );
        // `answered` requires `Complete`, and for both tools reaching `Complete` on this instance
        // means the adapter already compared the echoed generators against the fourteen-variable
        // system it sent. That is the per-run half of this hazard's coverage; the assertions below
        // are the behavioural half.
        let answer = answered(&report);
        let leading = answer
            .invariants
            .leading_monomials
            .as_ref()
            .expect("leading monomials");
        assert_ne!(
            leading.as_slice(),
            ["1".to_string()],
            "{} collapsed the ideal to <1>: it read x1*x10 as a power of x1",
            name
        );
        assert_eq!(
            answer.invariants.basis_cardinality,
            Some(15),
            "{} did not read fourteen distinct variables",
            name
        );
        // The term a prefix misread would annihilate has to survive into the basis.
        let basis = canonical_basis(answer.basis.as_ref().expect("a basis"));
        assert!(
            basis.iter().any(|f| f.contains("x1*x10")),
            "{} lost the x1*x10 term entirely: {:?}",
            name,
            basis
        );
    }
}

/// The Sagebrush driver's echoed generators are the system that was sent, on a live run.
///
/// The unit tests cover the adapter's half against fixtures. This covers the half that cannot be
/// faked: that the **real** driver's `#gen` rendering, after its own parse and pack, canonicalizes
/// to the same thing as Zeebra's renderer did on the way in. A disagreement between the two
/// spellings would make the check reject every honest run, which is the way a check like this
/// usually fails.
///
/// Run on a fourteen-variable system because that is where `x1` is a prefix of `x10`, and the
/// generator `x1*x10-1` is the one a greedy tokenizer annihilates.
#[test]
#[ignore = "needs the provisioned sagebrush-gb-driver"]
fn test_the_sagebrush_driver_echoes_the_system_it_was_sent() {
    let Some(mut solver) = sagebrush("sb-echo") else {
        panic!("the Sagebrush driver is not installed; see the module documentation")
    };
    let variables: Vec<String> = (1..=14).map(|i| format!("x{}", i)).collect();
    let names: Vec<&str> = variables.iter().map(String::as_str).collect();
    let mut system = vec!["x1*x10-1".to_string(), "x1^2-x10".to_string()];
    system.extend(
        (1..=14)
            .filter(|i| *i != 1 && *i != 10)
            .map(|i| format!("x{}^2-x1", i)),
    );
    let instance = Instance::new(
        "echo-14",
        "prefix",
        FieldSpec::prime(P),
        names.iter().map(|v| v.to_string()).collect(),
        system,
        MonomialOrder::GradedReverseLexicographic,
    );

    let report = solver.run(
        &instance,
        Task::ReducedGrobnerBasis,
        &Limits::wall(Duration::from_secs(120)),
    );
    // Reaching `Complete` *is* the assertion: the adapter refuses the run with
    // `SelfInconsistent` if the echo and the sent system disagree, and with `Incomplete` if the
    // installed driver is too old to echo at all.
    match &report.status {
        RunStatus::Complete(_) => {}
        RunStatus::Failed(RunFailure::Incomplete { detail }) => {
            panic!("the installed driver is too old: {detail}")
        }
        other => panic!("the driver did not echo the system it was sent: {other:?}"),
    }
}

/// Groebner.jl honours the declared variable order, checked on a system whose basis depends on it.
///
/// **The most dangerous failure mode in this module.** A tool that reordered the variables would
/// return a mathematically correct basis of the same ideal under a different order, and every
/// invariant except the leading monomials would agree. The two runs below are the same three
/// polynomials declared under `x > y > z` and under `z > y > x`; their lex leading monomials are
/// `{x, y, z^7}` and `{z, y, x^7}`, so the test fails if either run is served the other's answer.
#[test]
#[ignore = "needs the provisioned Julia and Groebner.jl"]
fn test_groebner_jl_honours_the_declared_variable_order() {
    let Some(mut solver) = groebner_jl("jl-order") else {
        panic!("Groebner.jl is not installed; see the module documentation")
    };
    let order = MonomialOrder::Lexicographic;
    let limits = Limits::wall(Duration::from_secs(120));
    let mut seen: Vec<Vec<String>> = Vec::new();

    for permuted in [false, true] {
        let (system, variables) = asymmetric_system(permuted);
        let (ours, our_basis) = zeebra_invariants(&system, &variables, order);
        let instance = instance(
            if permuted { "asym-zyx" } else { "asym-xyz" },
            "asymmetric",
            &system,
            &variables,
            order,
        );
        let report = solver.run(&instance, Task::LexBasis, &limits);
        let answer = answered(&report);
        assert_agrees("groebner.jl", &instance.name, &ours, &answer.invariants);
        assert_eq!(
            canonical_basis(answer.basis.as_ref().expect("a basis")),
            our_basis,
            "groebner.jl on {} differs from Zeebra term for term",
            instance.name
        );
        seen.push(
            answer
                .invariants
                .leading_monomials
                .clone()
                .expect("leading monomials"),
        );
    }

    assert_ne!(
        seen[0], seen[1],
        "the two variable orders must give different leading monomials, or this test proves nothing"
    );
    assert_eq!(
        seen[0],
        vec!["x".to_string(), "y".to_string(), "z^7".to_string()]
    );
    assert_eq!(
        seen[1],
        vec!["x^7".to_string(), "y".to_string(), "z".to_string()]
    );
}

/// The two comparands agree with each other at a 64-bit prime, where nothing else can check them.
///
/// Recorded as a finding and not as a verification: msolve and Singular both stop at `2^31 - 1`, so
/// above it these two are the only implementations in range and their agreement is two
/// implementations agreeing and nothing more. Zeebra is the third party here, which is why this
/// test compares both against Zeebra rather than against each other.
#[test]
#[ignore = "needs the provisioned Julia and sagebrush-gb-driver"]
fn test_both_comparands_agree_with_zeebra_above_the_two_to_the_thirty_first_ceiling() {
    type Wide = PrimeFieldElement64<4_611_624_995_532_046_337>;
    let mut julia = groebner_jl("jl-wide");
    let mut sage = sagebrush("sb-wide");
    assert!(
        julia.is_some() || sage.is_some(),
        "neither comparand is installed, so nothing would be checked"
    );
    let order = MonomialOrder::GradedReverseLexicographic;
    let variables = ["u0", "u1", "u2", "u3"];
    let system = katsura::<4, Wide>();
    let basis = f4(&system, order).expect("Zeebra computes the basis");
    let ours = Invariants::none().with_leading_monomials(
        basis
            .iter()
            .map(|f| monomial_to_string(&f.leading_monomial(order), &variables))
            .collect(),
    );
    let our_basis = canonical_basis(
        &basis
            .iter()
            .map(|f| polynomial_to_string(f, &variables, order))
            .collect::<Vec<String>>(),
    );
    let instance = Instance::new(
        "katsura-4-wide",
        "katsura",
        FieldSpec::prime(4_611_624_995_532_046_337),
        variables.iter().map(|v| v.to_string()).collect(),
        system
            .iter()
            .map(|f| polynomial_to_string(f, &variables, order))
            .collect(),
        order,
    );
    let limits = Limits::wall(Duration::from_secs(300));

    for (name, report) in [
        julia.as_mut().map(|s| {
            (
                "groebner.jl",
                s.run(&instance, Task::ReducedGrobnerBasis, &limits),
            )
        }),
        sage.as_mut().map(|s| {
            (
                "sagebrush",
                s.run(&instance, Task::ReducedGrobnerBasis, &limits),
            )
        }),
    ]
    .into_iter()
    .flatten()
    {
        let answer = answered(&report);
        assert_agrees(name, &instance.name, &ours, &answer.invariants);
        assert_eq!(
            canonical_basis(answer.basis.as_ref().expect("a basis")),
            our_basis,
            "{} differs from Zeebra term for term at the 62-bit prime 4611624995532046337",
            name
        );
        assert!(
            !report.status.is_verified(),
            "{} must stay Complete: an adapter never promotes its own answer",
            name
        );
    }
}

/// The term normalizer treats the three tools' three spellings of one polynomial as one.
///
/// Offline, so it runs in CI: the normalizer is what every agreement assertion above rests on, and
/// a bug in it would make a disagreement invisible.
#[test]
fn test_the_normalizer_identifies_the_three_tools_spellings() {
    let zeebra = "x*y+x*z+y*z+1073741826";
    let groebner_jl = "x*y + x*z + y*z + 1073741826";
    let sagebrush = "1*x*y + 1*x*z + 1*y*z + 1073741826";
    let canonical = canonical_polynomial(zeebra);
    assert_eq!(canonical_polynomial(groebner_jl), canonical);
    assert_eq!(canonical_polynomial(sagebrush), canonical);
    assert_eq!(canonical, "1*x*y+1*x*z+1*y*z+1073741826*1");
}

/// The normalizer is sensitive to a changed coefficient, which is the point of using it.
#[test]
fn test_the_normalizer_distinguishes_a_changed_coefficient() {
    assert_ne!(
        canonical_polynomial("x*y + 2*x*z"),
        canonical_polynomial("x*y + 3*x*z")
    );
    assert_ne!(
        canonical_polynomial("x*y + x*z"),
        canonical_polynomial("x*y + 2*x*z")
    );
}

/// Term order within a polynomial and element order within a basis do not affect the comparison.
#[test]
fn test_the_normalizer_ignores_print_order() {
    assert_eq!(
        canonical_basis(&["y*z + x*y".to_string(), "z^2".to_string()]),
        canonical_basis(&["z^2".to_string(), "x*y + y*z".to_string()])
    );
}
