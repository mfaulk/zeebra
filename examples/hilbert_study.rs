//! Does a semiregularity model predict what F4 actually finds?
//!
//! M22-B, and **diagnostic only**: nothing here discards work, and the question is whether the
//! prediction is accurate enough and early enough to be worth acting on. The answer decides whether
//! M22-C gets built.
//!
//! Three quantities, kept apart on purpose:
//!
//! - **observed** `H(d)` — the exact Hilbert function of the leading-term ideal of a *computed*
//!   Gröbner basis, by the closed-form recursion in `grobner::hilbert`. Exact, and for a
//!   homogeneous ideal it is the graded dimension of `R/I`.
//! - **predicted** `H(d)` — the positive truncation of `Π(1 − z^{d_i}) / (1 − z)^n`. A theorem for
//!   a regular sequence, a conjecture for a generic overdetermined one, and nothing at all for a
//!   structured one.
//! - **what F4 did** — the per-degree profile from M22-0, which is a property of a run under one
//!   configuration and not of the ideal.
//!
//! ```text
//! tools/fetch-mq-challenge.sh                      # for the Fukuoka sections
//! cargo run --release --example hilbert_study
//! ```
//!
//! # Inhomogeneous input
//!
//! The Fukuoka and Poseidon systems are not homogeneous, so the model does not apply to them as
//! given. What is studied instead is the system of **top forms** — each generator's highest-degree
//! homogeneous component — which is the object the MQ literature's semiregularity assumption is
//! about. That is a *different ideal*: `top_forms` of `x^2 + y` is `x^2`, whose variety is a line
//! where the original's is a parabola. Every table below says which system it is about.

use std::time::Instant;

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        benchmark_systems::katsura,
        classify_ideal, f4_with_options,
        hilbert::{
            is_homogeneous, leading_generators_by_degree, monomials_of_degree, top_forms,
            HilbertComparison, HilbertSeries, SemiregularSeries,
        },
        research::{CicoInstance, MqInstance, Poseidon, PoseidonParameters, KOALABEAR_PRIME},
        F4Options, IdealClass,
    },
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

type Q = PrimeFieldElement64<31>;
type K = PrimeFieldElement64<KOALABEAR_PRIME>;
type P = PrimeFieldElement64<2_147_483_647>;

const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const C1: u64 = 0xC0_9DE4;

/// Degrees to compare over. Beyond the top degree of the quotient both sides are zero, so this is
/// chosen to reach past every instance's finish rather than to bound the computation.
const UP_TO: u64 = 12;

fn options() -> F4Options {
    F4Options {
        profile_degrees: true,
        max_matrix_columns: 60_000,
        max_live_bytes: 400_000_000,
        ..F4Options::default()
    }
}

/// Every monomial of exactly `degree` in `N` variables, for a random homogeneous form.
fn monomials_at<const N: usize>(degree: u32) -> Vec<Monomial<N>> {
    fn walk<const N: usize>(
        position: usize,
        left: u32,
        current: &mut [u32; N],
        out: &mut Vec<Monomial<N>>,
    ) {
        if position + 1 == N {
            current[position] = left;
            out.push(Monomial::new(current));
            return;
        }
        for taken in 0..=left {
            current[position] = taken;
            walk(position + 1, left - taken, current, out);
        }
        current[position] = 0;
    }
    let mut out = Vec::new();
    if N == 0 {
        return out;
    }
    walk(0, degree, &mut [0u32; N], &mut out);
    out
}

/// `count` random homogeneous forms of degree `degree`, with every coefficient uniform.
///
/// "Generic-looking", which is the most that can be said: a random system over a small field is not
/// a generic system, and over GF(31) one coefficient in 31 is zero. The seed is fixed so a
/// disagreement can be reproduced.
fn random_forms<const N: usize, F: FiniteField>(
    count: usize,
    degree: u32,
    seed: u64,
) -> Vec<MultivariatePolynomial<N, F>> {
    let layout = monomials_at::<N>(degree);
    let mut rng = StdRng::seed_from_u64(seed);
    (0..count)
        .map(|_| {
            let terms: Vec<(Monomial<N>, F)> = layout
                .iter()
                .map(|monomial| (*monomial, F::random(&mut rng)))
                .collect();
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

/// Compare the model against the measurement on one homogeneous system, and print the table.
fn study<const N: usize, F: FiniteField>(
    label: &str,
    system: &[MultivariatePolynomial<N, F>],
    note: &str,
) {
    println!("### {}", label);
    println!();
    if !note.is_empty() {
        println!("{}", note);
        println!();
    }

    let homogeneous = is_homogeneous(system);
    let degrees: Vec<u64> = system.iter().map(|p| p.degree()).collect();
    println!(
        "- {} forms in {} variables, degrees {:?}{}",
        system.len(),
        N,
        {
            let mut shown = degrees.clone();
            shown.sort_unstable();
            shown.dedup();
            shown
        },
        if homogeneous {
            ""
        } else {
            " — **not homogeneous**, so the observed column is the Hilbert function of the \
             leading-term ideal and not a graded dimension of this ideal"
        }
    );

    let at = Instant::now();
    let (basis, statistics) = match f4_with_options(system, GREVLEX, &options()) {
        Ok(pair) => pair,
        Err(e) => {
            println!("- F4 did not finish: {}", e);
            println!();
            return;
        }
    };
    let elapsed = at.elapsed();

    let comparison = match HilbertComparison::new(&basis, GREVLEX, &degrees, UP_TO) {
        Ok(comparison) => comparison,
        Err(e) => {
            println!("- the Hilbert computation did not finish: {}", e);
            println!();
            return;
        }
    };

    let class = classify_ideal(&basis, GREVLEX);
    println!(
        "- basis of {} elements in {:.1} ms; the ideal is {}",
        basis.len(),
        elapsed.as_secs_f64() * 1e3,
        match class {
            IdealClass::ZeroDimensional => "zero-dimensional",
            IdealClass::PositiveDimensional => "positive-dimensional",
            IdealClass::Unit => "the whole ring",
        }
    );
    println!(
        "- model's degree of regularity: {}; observed top nonzero degree: {}",
        comparison
            .predicted_degree_of_regularity
            .map(|d| d.to_string())
            .unwrap_or_else(|| format!("none within {}", UP_TO)),
        comparison
            .observed_top_degree()
            .map(|d| d.to_string())
            .unwrap_or_else(|| "-".to_string())
    );
    println!(
        "- F4's highest selection degree: {}; highest matrix monomial degree: {}",
        statistics.max_pair_degree, statistics.max_monomial_degree
    );
    match comparison.first_disagreement {
        None => println!("- **the model agrees at every degree compared**"),
        Some((degree, predicted, observed)) => println!(
            "- **first disagreement at degree {}**: predicted {}, observed {} (error {:+})",
            degree,
            predicted,
            observed,
            predicted - observed
        ),
    }
    println!(
        "- agreement rate over degrees 0..={}: {:.0}%",
        UP_TO,
        100.0 * comparison.agreement_rate()
    );
    println!();

    // New leading generators by their own degree, which is what a prediction of "new elements at
    // this degree" would have to match, against what F4 extracted at each selection degree.
    let generators = leading_generators_by_degree(&basis, GREVLEX);

    println!(
        "| {:>3} | {:>9} | {:>9} | {:>9} | {:>6} | {:>9} | {:>9} | {:>5} | {:>5} | {:>5} |",
        "d",
        "dim R_d",
        "H pred",
        "H obs",
        "err",
        "dim I pred",
        "dim I obs",
        "gens",
        "F4 new",
        "rank+"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(5),
        "-".repeat(11),
        "-".repeat(11),
        "-".repeat(11),
        "-".repeat(8),
        "-".repeat(11),
        "-".repeat(11),
        "-".repeat(7),
        "-".repeat(7),
        "-".repeat(7),
    );
    for entry in &comparison.degrees {
        // Stop once both sides and F4 have nothing at this degree or above.
        let quiet = entry.observed == 0
            && entry.predicted == 0
            && entry.degree > statistics.max_pair_degree;
        if quiet {
            continue;
        }
        let profile = statistics.degrees.get(entry.degree);
        println!(
            "| {:>3} | {:>9} | {:>9} | {:>9} | {:>6} | {:>9} | {:>9} | {:>5} | {:>5} | {:>5} |",
            entry.degree,
            entry.ambient,
            entry.predicted,
            entry.observed,
            format!("{:+}", entry.error()),
            entry.predicted_ideal_dimension,
            entry.observed_ideal_dimension,
            generators.get(&entry.degree).copied().unwrap_or(0),
            profile.map(|p| p.new_basis_elements).unwrap_or(0),
            profile.map(|p| p.candidate_rank_contribution).unwrap_or(0),
        );
    }
    println!();
}

fn mq_directory() -> std::path::PathBuf {
    std::env::var("ZEEBRA_MQ_DIR")
        .unwrap_or_else(|_| "research/instances/mq".to_string())
        .into()
}

fn load_mq(stem: &str) -> Option<MqInstance> {
    let text = std::fs::read_to_string(mq_directory().join(stem)).ok()?;
    MqInstance::parse(&text).ok()
}

/// A planted reduced CICO system.
fn cico<const N: usize>(t: usize, r_f: usize, r_p: usize) -> Vec<MultivariatePolynomial<N, K>> {
    let poseidon = Poseidon::<K>::new(PoseidonParameters {
        prime: KOALABEAR_PRIME,
        alpha: 3,
        t,
        r_f,
        r_p,
    })
    .expect("R_F is even");
    let free: Vec<K> = (0..t - 1).map(|i| K::new(1_000 + i as u64)).collect();
    CicoInstance::planted(
        poseidon,
        1,
        &[K::new(C1)],
        &free,
        Some(PoseidonParameters::bounty_cico()),
    )
    .expect("the right widths")
    .system::<N>()
    .expect("the right dimension")
}

/// §1: the textbook cases, where the formula is a theorem.
fn textbook() {
    println!("## 1. Where the formula is a theorem");
    println!();
    println!(
        "A regular sequence of `m ≤ n` forms has Hilbert series exactly \
         `Π(1 − z^{{d_i}}) / (1 − z)^n`. These rows must agree at every degree, and a disagreement \
         would be a defect in the implementation rather than a finding about the model."
    );
    println!();

    // Pure powers: a regular sequence by construction, with dimension the product of the exponents.
    let generators = [
        Monomial::<4>::new(&[2, 0, 0, 0]),
        Monomial::<4>::new(&[0, 3, 0, 0]),
        Monomial::<4>::new(&[0, 0, 2, 0]),
        Monomial::<4>::new(&[0, 0, 0, 5]),
    ];
    let series = HilbertSeries::of_monomial_ideal(&generators).expect("coprime");
    let predicted = SemiregularSeries::new(4, &[2, 3, 2, 5], UP_TO).expect("in range");
    println!(
        "`<x^2, y^3, z^2, w^5>` in four variables — a regular sequence of pure powers. \
         `dim R/I` = 2·3·2·5 = 60, and the closed form gives {:?}.",
        series.quotient_dimension(&generators).unwrap()
    );
    let observed: Vec<i128> = series.values(UP_TO).unwrap();
    let agree = (0..=UP_TO).all(|d| predicted.raw(d) == series.function(d).unwrap());
    println!();
    println!(
        "- H = {:?}\n- the untruncated model agrees at every degree: **{}**",
        observed, agree
    );
    println!();

    study::<3, P>(
        "three squares in three variables",
        &["x^2", "y^2", "z^2"]
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, ["x", "y", "z"]).unwrap())
            .collect::<Vec<_>>(),
        "A regular sequence. `dim R/I = 8` over degrees 0..=3.",
    );
}

/// §2: random homogeneous quadratics, which is the regime the model is conjectured for.
fn generic_mq() {
    println!("## 2. Random homogeneous quadratics");
    println!();
    println!(
        "Generic-looking, which is the most that can be said: a random system over a finite field \
         is not a generic system, and over GF(2^31 − 1) one coefficient in 2^31 − 1 is zero. Seeds \
         are fixed. These are the rows where the semiregularity conjecture is expected to hold."
    );
    println!();

    study::<5, P>(
        "10 random quadratics in 5 variables",
        &random_forms::<5, P>(10, 2, 1),
        "",
    );
    study::<6, P>(
        "12 random quadratics in 6 variables",
        &random_forms::<6, P>(12, 2, 2),
        "",
    );
    study::<7, P>(
        "14 random quadratics in 7 variables",
        &random_forms::<7, P>(14, 2, 3),
        "",
    );
    study::<6, P>(
        "6 random quadratics in 6 variables (square)",
        &random_forms::<6, P>(6, 2, 4),
        "Square rather than overdetermined, so the formula is the regular-sequence one and is \
         expected to be exact.",
    );
}

/// §3: structured systems that violate the assumption, so the failure mode is visible.
fn counterexamples() {
    println!("## 3. Deliberate counterexamples");
    println!();
    println!(
        "Systems constructed to break semiregularity, so that what the model does when it is wrong \
         can be seen rather than guessed at."
    );
    println!();

    study::<3, P>(
        "x^2, x*y, x*z — a common factor",
        &["x^2", "x*y", "x*z"]
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, ["x", "y", "z"]).unwrap())
            .collect::<Vec<_>>(),
        "`x · <x, y, z>`. `x` is a zero divisor on the quotient by the first form, so the second \
         and third add nothing in degree two. The model is the `m = n` regular-sequence formula.",
    );

    study::<4, P>(
        "squares of four linear forms in a two-variable span",
        &[
            "x^2 + 2*x*y + y^2",
            "x^2 - 2*x*y + y^2",
            "x^2 + 4*x*y + 4*y^2",
            "x^2 + 6*x*y + 9*y^2",
        ]
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, ["x", "y", "z", "w"]).unwrap())
        .collect::<Vec<_>>(),
        "Four quadratics in four variables, every one a form in `x, y` alone — so `z` and `w` are \
         untouched and the quotient is positive-dimensional however many forms are added.",
    );

    study::<4, P>(
        "a quadratic repeated up to scalars",
        &["x*y - z*w", "2*x*y - 2*z*w + x^2", "x^2", "y^2 - z^2"]
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, ["x", "y", "z", "w"]).unwrap())
            .collect::<Vec<_>>(),
        "The second generator is the first plus the third, so the four forms span a \
         three-dimensional space of quadratics and the model counts one form too many.",
    );
}

/// §4: Fukuoka type III, through its top forms.
fn fukuoka() {
    println!("## 4. Fukuoka MQ Challenge, type III over GF(31)");
    println!();
    println!(
        "**Through top forms.** The published instances carry linear and constant terms, so they \
         are not homogeneous and the model does not apply to them as given. The rows below are \
         about the homogeneous quadratic parts — the system the MQ literature's semiregularity \
         assumption is a statement about — and that is a *different ideal* from the one the \
         challenge poses."
    );
    println!();

    for (stem, label) in [
        ("ToyExample-type3-n10-seed0", "type III n=10 seed 0"),
        ("ToyExample-type3-n15-seed0", "type III n=15 seed 0"),
    ] {
        let Some(instance) = load_mq(stem) else {
            println!(
                "`{}` is not present; run `tools/fetch-mq-challenge.sh`.\n",
                stem
            );
            continue;
        };
        match instance.variables {
            10 => {
                let system = instance.system::<10, Q>().expect("ten variables");
                let forms = top_forms(&system);
                study::<10, Q>(
                    &format!("{} — top forms", label),
                    &forms,
                    "20 homogeneous quadratics in 10 variables.",
                );
            }
            15 => {
                let system = instance.system::<15, Q>().expect("fifteen variables");
                let forms = top_forms(&system);
                study::<15, Q>(
                    &format!("{} — top forms", label),
                    &forms,
                    "30 homogeneous quadratics in 15 variables.",
                );
            }
            other => println!("{}: {} variables is not compiled in.\n", label, other),
        }
    }

    // And the inhomogeneous original, to show what the observed column means there.
    if let Some(instance) = load_mq("ToyExample-type3-n10-seed0") {
        let system = instance.system::<10, Q>().expect("ten variables");
        study::<10, Q>(
            "type III n=10 seed 0 — the published inhomogeneous system",
            &system,
            "Shown so the two can be compared. The observed column here is the Hilbert function \
             of the leading-term ideal of the *inhomogeneous* system's basis, which is a \
             legitimate monomial-ideal invariant and **not** a graded dimension of this ideal. \
             The predicted column is the same quadratic model, and it has no claim on this row.",
        );
    }
}

/// §5: reduced-round Poseidon, through its top forms, with the limitation stated.
fn poseidon() {
    println!("## 5. Reduced-round Poseidon CICO over KoalaBear");
    println!();
    println!(
        "**The weakest section, and deliberately included.** These systems are cubic (`alpha = 3`) \
         and inhomogeneous, their generators are highly structured, and the semiregularity model \
         has no standing on them at all. The rows are here to show what the model does on exactly \
         the systems M22 cares about, which is the question §7 of the plan asks."
    );
    println!();

    study::<5, K>(
        "t=2 R_F=2 R_P=0 — top forms",
        &top_forms(&cico::<5>(2, 2, 0)),
        "Five variables. The top form of each S-box equation `v - s^3` is `s^3`, so the top-form \
         system is a system of cubes of linear forms plus one linear output constraint — which is \
         *not* the CICO system in any useful sense.",
    );
    study::<7, K>(
        "t=2 R_F=2 R_P=2 — top forms",
        &top_forms(&cico::<7>(2, 2, 2)),
        "Seven variables.",
    );
    study::<9, K>(
        "t=2 R_F=4 R_P=0 — the published inhomogeneous system",
        &cico::<9>(2, 4, 0),
        "Shown as it is generated, so the observed column can be compared against §4's \
         inhomogeneous row. The predicted column is the cubic model and has no claim on it.",
    );
}

/// §6: the question the plan asks — does the prediction say when a degree is exhausted?
fn the_main_question() {
    println!("## 6. The question");
    println!();
    println!(
        "§7.5 of the plan: *does the Hilbert model reliably identify degrees at which additional \
         critical-pair reductions will contribute no new basis elements?*"
    );
    println!();
    println!(
        "The quantity a selection rule would have to act on is `dim I_d = dim R_d − H(d)`, which \
         bounds how many independent degree-`d` relations exist at all. Three columns above bear on \
         it: `dim I pred`, `dim I obs`, and `gens` — the number of **minimal** generators of the \
         leading-term ideal at degree `d`, which is what a prediction of \"new elements at this \
         degree\" would have to match."
    );
    println!();
    println!(
        "The `F4 new` column is deliberately *not* the same quantity. It is what one run under one \
         configuration extracted at each selection degree, and a batch at degree `d` can produce a \
         relation of degree below `d` — M22-0 measured a third to a half of all new elements \
         arriving that way. So `gens` is a property of the ideal and `F4 new` is a property of a \
         run, and the gap between them is not prediction error."
    );
    println!();

    // One calibration row: katsura-5 is homogeneous in no sense, but it is the system every other
    // measurement in this repository is stated against.
    study::<5, P>(
        "katsura-5, for calibration",
        &katsura::<5, P>(),
        "Not homogeneous and not a quadratic system in the model's sense — two of its generators \
         are linear. Included because it is the instance every other figure in this repository is \
         quoted against.",
    );

    println!("### The ambient dimensions, for scale");
    println!();
    println!(
        "| {:>3} | {:>12} | {:>12} | {:>14} |",
        "d", "n=10", "n=15", "n=20"
    );
    println!(
        "|{}|{}|{}|{}|",
        "-".repeat(5),
        "-".repeat(14),
        "-".repeat(14),
        "-".repeat(16)
    );
    for degree in 0..=8 {
        println!(
            "| {:>3} | {:>12} | {:>12} | {:>14} |",
            degree,
            monomials_of_degree(10, degree).unwrap(),
            monomials_of_degree(15, degree).unwrap(),
            monomials_of_degree(20, degree).unwrap(),
        );
    }
    println!();
    println!(
        "This is why the closed-form recursion exists rather than an enumeration: counting the \
         degree-8 monomials outside a leading-term ideal in twenty variables is 2.7 million \
         divisibility sweeps, and the same count at degree 12 is 141 million."
    );
    println!();
}

fn main() {
    println!("# Hilbert functions: the model against the measurement");
    println!();
    println!(
        "Configuration: `F4Options::recommended()` with `profile_degrees`, grevlex throughout, \
         degrees compared over 0..={}. Reproduce with \
         `cargo run --release --example hilbert_study`.",
        UP_TO
    );
    println!();
    println!(
        "`H pred` is the positive truncation of `Π(1 − z^{{d_i}}) / (1 − z)^n`; `H obs` is the \
         exact Hilbert function of the computed basis's leading-term ideal. `err` is \
         predicted − observed, so **a positive error means the model expects more residue classes \
         than exist** — the direction in which a Hilbert-driven selection would skip pairs it \
         needed."
    );
    println!();

    textbook();
    generic_mq();
    counterexamples();
    fukuoka();
    poseidon();
    the_main_question();
}
