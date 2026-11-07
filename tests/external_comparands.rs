//! Live agreement between Zeebra and the two M25 comparands it drives through adapters.
//!
//! Every test here is `#[ignore]`d. The reason is the same one `src/grobner/differential/mod.rs`
//! gives for its live Singular sweep: **CI has no Julia and no Sagebrush driver, and a test that
//! silently passed when the tool is absent would be worse than no test.** The offline half of each
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
        benchmark_systems::{cyclic, katsura},
        differential::{monomial_to_string, polynomial_to_string},
        external::{
            ExternalSolver, FieldSpec, GroebnerJlSolver, Instance, Invariants, Limits, RunStatus,
            SagebrushSolver, Task,
        },
        f4,
    },
    Monomial, MonomialOrder, MultivariatePolynomial, One, Zero,
};

/// The prime the provisioning smoke test used: 2^30 + 3, inside every comparand's range.
const P: u64 = 1_073_741_827;
type F = PrimeFieldElement64<P>;

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

/// Both comparands agree with Zeebra on the Katsura rungs, under Zeebra's own convention.
///
/// `katsura::<N, F>()` is **N = n + 1 variables** (`src/grobner/benchmark_systems.rs:66`), so these
/// are the literature's katsura-2, -3 and -4. The instance carries its generators as text, so no
/// tool can apply a different convention — the hazard is in comparing a figure against a published
/// one, not in the run.
#[test]
#[ignore = "needs the provisioned Julia and sagebrush-gb-driver"]
fn test_both_comparands_agree_with_zeebra_on_katsura() {
    let mut julia = groebner_jl("jl-katsura");
    let mut sage = sagebrush("sb-katsura");
    assert!(
        julia.is_some() || sage.is_some(),
        "neither comparand is installed, so nothing would be checked"
    );
    let order = MonomialOrder::GradedReverseLexicographic;
    let limits = Limits::wall(Duration::from_secs(300));

    macro_rules! rung {
        ($n:literal) => {{
            let variables: Vec<String> = (0..$n).map(|i| format!("u{}", i)).collect();
            let names: Vec<&str> = variables.iter().map(String::as_str).collect();
            let system = katsura::<$n, F>();
            let (ours, our_basis) = zeebra_invariants(&system, &names, order);
            let instance = instance(concat!("katsura-", $n), "katsura", &system, &names, order);
            if let Some(solver) = julia.as_mut() {
                let report = solver.run(&instance, Task::ReducedGrobnerBasis, &limits);
                let answer = answered(&report);
                assert_agrees("groebner.jl", &instance.name, &ours, &answer.invariants);
                assert_eq!(
                    canonical_basis(answer.basis.as_ref().expect("a basis")),
                    our_basis,
                    "groebner.jl on {} differs from Zeebra term for term",
                    instance.name
                );
            }
            if let Some(solver) = sage.as_mut() {
                let report = solver.run(&instance, Task::ReducedGrobnerBasis, &limits);
                let answer = answered(&report);
                assert_agrees("sagebrush", &instance.name, &ours, &answer.invariants);
                assert_eq!(
                    canonical_basis(answer.basis.as_ref().expect("a basis")),
                    our_basis,
                    "sagebrush on {} differs from Zeebra term for term",
                    instance.name
                );
            }
        }};
    }

    rung!(3);
    rung!(4);
    rung!(5);
}

/// Both comparands agree with Zeebra on the cyclic rungs, including positive-dimensional cyclic-4.
///
/// **Cyclic-4 is positive-dimensional** (`src/grobner/benchmark_systems.rs:10-15`), so it is a
/// basis row and not a zero-dimensional-solving row. It is included deliberately: a reduced basis
/// is still unique, so the agreement check is as strong as anywhere, and an adapter that assumed a
/// finite quotient dimension would break here. Groebner.jl reports `dimension > 0` and omits
/// `@vdim`; the Sagebrush driver reports no dimension at all.
#[test]
#[ignore = "needs the provisioned Julia and sagebrush-gb-driver"]
fn test_both_comparands_agree_with_zeebra_on_cyclic() {
    let mut julia = groebner_jl("jl-cyclic");
    let mut sage = sagebrush("sb-cyclic");
    assert!(
        julia.is_some() || sage.is_some(),
        "neither comparand is installed, so nothing would be checked"
    );
    let order = MonomialOrder::GradedReverseLexicographic;
    let limits = Limits::wall(Duration::from_secs(300));

    macro_rules! rung {
        ($n:literal) => {{
            let variables: Vec<String> = (0..$n).map(|i| format!("x{}", i)).collect();
            let names: Vec<&str> = variables.iter().map(String::as_str).collect();
            let system = cyclic::<$n, F>();
            let (ours, our_basis) = zeebra_invariants(&system, &names, order);
            let instance = instance(concat!("cyclic-", $n), "cyclic", &system, &names, order);
            if let Some(solver) = julia.as_mut() {
                let report = solver.run(&instance, Task::ReducedGrobnerBasis, &limits);
                let answer = answered(&report);
                assert_agrees("groebner.jl", &instance.name, &ours, &answer.invariants);
                assert_eq!(
                    canonical_basis(answer.basis.as_ref().expect("a basis")),
                    our_basis,
                    "groebner.jl on {} differs from Zeebra term for term",
                    instance.name
                );
            }
            if let Some(solver) = sage.as_mut() {
                let report = solver.run(&instance, Task::ReducedGrobnerBasis, &limits);
                let answer = answered(&report);
                assert_agrees("sagebrush", &instance.name, &ours, &answer.invariants);
                assert_eq!(
                    canonical_basis(answer.basis.as_ref().expect("a basis")),
                    our_basis,
                    "sagebrush on {} differs from Zeebra term for term",
                    instance.name
                );
            }
        }};
    }

    rung!(3);
    rung!(4);
    rung!(5);
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
