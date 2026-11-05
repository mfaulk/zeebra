//! Import a Fukuoka MQ Challenge instance, solve it, and verify against the published answer.
//!
//! M21-A. Needs the instance data, which this repository does **not** redistribute — the Fukuoka
//! files are "All Rights Reserved" with no stated licence:
//!
//! ```text
//! tools/fetch-mq-challenge.sh
//! cargo run --release --example mq_challenge
//! ```
//!
//! Set `ZEEBRA_MQ_DIR` to read from somewhere other than `research/instances/mq`. With no data
//! present the program says so and exits rather than failing obscurely.
//!
//! Both GF(31) families are run. Type III is overdetermined and solvable outright; type VI is the
//! signature family and **underdetermined**, so it is positive-dimensional and reaches an answer
//! only through M21-E's specialization — which is the point of including it.

use std::{path::PathBuf, time::Instant};

use rand::{prelude::StdRng, SeedableRng};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        research::{solve_slice, Claim, InstanceManifest, MqInstance, Provenance, Specialization},
        solve_one_planned, PlannedSolveOptions, SolveError, SolveOutcome, SolvePolicy,
    },
    FiniteField, Zero,
};

/// GF(31). No new arithmetic was needed for this importer.
type F = PrimeFieldElement64<31>;

fn directory() -> PathBuf {
    std::env::var("ZEEBRA_MQ_DIR")
        .unwrap_or_else(|_| "research/instances/mq".to_string())
        .into()
}

/// Read an instance and its published answer, or `None` if the data is not present.
fn load(stem: &str) -> Option<(MqInstance, Vec<u64>)> {
    let path = directory().join(stem);
    let text = std::fs::read_to_string(&path).ok()?;
    let answer = std::fs::read_to_string(directory().join(format!("{}-answer", stem)))
        .map(|t| MqInstance::parse_answer(&t))
        .unwrap_or_default();
    match MqInstance::parse(&text) {
        Ok(instance) => Some((instance, answer)),
        Err(e) => {
            println!("{}: {}", path.display(), e);
            None
        }
    }
}

/// The manifest for an instance, with everything a reproducible result needs.
fn manifest(
    id: &str,
    archive: &str,
    sha256: &str,
    instance: &MqInstance,
    answer: &[u64],
    objective: &str,
) -> InstanceManifest {
    InstanceManifest {
        id: id.to_string(),
        schema: InstanceManifest::SCHEMA,
        provenance: Provenance {
            source: "Fukuoka MQ Challenge".to_string(),
            version: "toy example, retrieved 2026-11-04".to_string(),
            url: format!("https://www.mqchallenge.org/toy-example/{}", archive),
            sha256: sha256.to_string(),
            redistribution: "All rights reserved; not redistributed — tools/fetch-mq-challenge.sh"
                .to_string(),
        },
        field: instance.field.to_string(),
        characteristic: instance.field.order(),
        extension_degree: 1,
        variables: (0..instance.variables).map(|i| format!("x{}", i)).collect(),
        generators: instance.polynomials,
        monomial_order: instance.order.clone(),
        objective: objective.to_string(),
        witness: (!answer.is_empty()).then(|| answer.to_vec()),
        verification: "evaluate the imported coefficient vectors at the candidate, and compare \
                       against the published answer file"
            .to_string(),
        // Left for the solve below to fill in, because it is an observation and not a fact.
        quotient_dimension: None,
    }
}

/// Type III: overdetermined, solvable outright.
fn encryption() {
    let Some((instance, answer)) = load("ToyExample-type3-n10-seed0") else {
        return;
    };
    println!("## Type III (encryption): {}", instance);
    println!();

    let mut record = manifest(
        "fukuoka-mq-III-n10-seed0",
        "ToyExample-type3-n10.tar.bz2",
        "9436e45dbd4247f152681e954f1db19d92e8cf5e76b2bc35530bed74aae522ba",
        &instance,
        &answer,
        "find any x over GF(31) with F(x) = 0",
    );

    let system = instance.system::<10, F>().expect("GF(31) at n = 10");
    let published: Vec<F> = answer.iter().copied().map(F::new).collect();

    // Check one: the reconstruction vanishes at the published answer. This is what catches a
    // monomial-order translation error, which is silent and wrong everywhere.
    let point: [F; 10] = published.clone().try_into().expect("ten coordinates");
    let vanishes = system.iter().all(|p| p.eval(&point).is_zero());
    println!(
        "Reconstruction vanishes at the published answer: {}",
        vanishes
    );
    assert!(vanishes, "the imported system is not the published one");

    // Check two: the solver finds that point without being told it. A wrong layout could vanish at
    // one point by accident; it could not also be solved to the same one.
    let at = Instant::now();
    let (outcome, plan) = solve_one_planned(
        &system,
        &mut StdRng::seed_from_u64(1),
        &PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback),
    );
    let elapsed = at.elapsed();

    match outcome {
        Ok(SolveOutcome::Point(found)) => {
            assert!(system.iter().all(|p| p.eval(&found).is_zero()));
            println!(
                "Solved in {:?}; the solver's point matches the published one: {}",
                elapsed,
                found.to_vec() == published
            );
        }
        other => println!("Solved in {:?}: {:?}", elapsed, other),
    }
    if let Some(conversion) = plan
        .attempts
        .iter()
        .filter_map(|a| a.statistics.fglm.as_ref())
        .next()
    {
        // An observation from one computation, and tagged as one.
        record.quotient_dimension = Some(Claim::Observed(conversion.quotient_dimension));
    }

    println!();
    println!("{}", plan);
    println!();
    println!("### Manifest");
    println!();
    println!("{}", record);
}

/// Type VI: the signature family, underdetermined, reachable only through specialization.
fn signature() {
    let Some((instance, answer)) = load("ToyExample-type6-n10-seed0") else {
        return;
    };
    println!();
    println!("## Type VI (signature): {}", instance);
    println!();
    println!(
        "{} polynomials in {} variables, so n > m and the ideal is positive-dimensional.",
        instance.polynomials, instance.variables
    );

    let record = manifest(
        "fukuoka-mq-VI-n10-seed0",
        "ToyExample-type6-n10.tar.bz2",
        "9512b6032be415ae8391b72ed8ad4f43357bafa4f0058d60b06dba3537a41af3",
        &instance,
        &answer,
        "find any x over GF(31) with F(x) = 0; the system is underdetermined",
    );

    let system = instance.system::<10, F>().expect("GF(31) at n = 10");
    let published: Vec<F> = answer.iter().copied().map(F::new).collect();
    let point: [F; 10] = published.clone().try_into().expect("ten coordinates");
    assert!(
        system.iter().all(|p| p.eval(&point).is_zero()),
        "the imported system is not the published one"
    );
    println!("Reconstruction vanishes at the published answer: true");
    println!();

    // Unspecialized: refused, correctly.
    let (outcome, _) = solve_one_planned(
        &system,
        &mut StdRng::seed_from_u64(2),
        &PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback),
    );
    match outcome {
        Err(SolveError::PositiveDimensional) => println!(
            "Unspecialized: refused as positive-dimensional, which is the right answer and not\n\
             a resource failure."
        ),
        other => println!("Unspecialized: {:?}", other),
    }
    println!();

    // Fix n - m variables, which squares the system. The count is this program's choice.
    let free: Vec<usize> = (0..instance.variables - instance.polynomials).collect();
    println!(
        "Fixing {} variables ({:?}) leaves {} unknowns against {} equations. That count is a\n\
         choice, not something inferred from the shape.",
        free.len(),
        free,
        instance.variables - free.len(),
        instance.polynomials
    );
    println!();
    println!(
        "| {:>4} | {:>9} | {:<52} |",
        "seed", "elapsed ms", "what this establishes"
    );
    println!("|{}|{}|{}|", "-".repeat(6), "-".repeat(11), "-".repeat(54));

    let options = PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback);
    let mut rng = StdRng::seed_from_u64(31);
    let mut witnesses = 0;
    for seed in 0..8u64 {
        let slice = Specialization::<10, F>::seeded(&free, seed).expect("valid indices");
        let (outcome, plan) = solve_slice(&system, &slice, &options, &mut rng);
        let verdict = match &outcome {
            Ok(o) => {
                if o.is_evidence_about_the_original_system() {
                    witnesses += 1;
                }
                o.to_string()
            }
            Err(e) => format!("inconclusive about the slice — {}", e),
        };
        println!(
            "| {:>4} | {:>9} | {:<52} |",
            seed,
            format!("{:.1}", plan.total_elapsed().as_secs_f64() * 1e3),
            truncate(&verdict, 52)
        );

        // Every witness is checked against the imported coefficient vectors here too.
        if let Ok(o) = &outcome {
            if let Some(found) = o.witness() {
                for p in &system {
                    assert!(p.eval(&found).is_zero(), "{} is not satisfied", p);
                }
            }
        }
    }

    println!();
    println!(
        "{} of eight slices gave a witness for the original system. The rest are statements\n\
         about their own slice: a run of them is not evidence that the system is unsatisfiable,\n\
         and the published answer above shows it is not.",
        witnesses
    );
    println!();
    println!("### Manifest");
    println!();
    println!("{}", record);
}

fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        format!("{}…", s.chars().take(width - 1).collect::<String>())
    }
}

fn main() {
    println!("# Fukuoka MQ Challenge instances, imported and solved");
    println!();

    let directory = directory();
    if !directory.join("ToyExample-type3-n10-seed0").exists() {
        println!(
            "No instance data in {}.\n\n\
             The Fukuoka files are \"All Rights Reserved\" with no stated licence, so this\n\
             repository does not redistribute them. Fetch them with:\n\n\
             \x20   tools/fetch-mq-challenge.sh\n\n\
             or set ZEEBRA_MQ_DIR to where they already are.",
            directory.display()
        );
        return;
    }

    encryption();
    signature();

    println!();
    println!("Both checks matter and they are different. The reconstruction vanishing at the");
    println!("published answer rules out a *wrong* monomial layout; the solver independently");
    println!("recovering that point rules out a layout that vanishes there by accident.");
    println!();
    println!("These are toy examples, published so implementations can check themselves. n = 10");
    println!("is 45 variables short of the smallest unsolved challenge, and nothing here is a");
    println!("competitive result. See docs/research/fukuoka-mq.md.");
}
