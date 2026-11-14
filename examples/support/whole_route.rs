use rand::{rngs::StdRng, SeedableRng};
use std::time::Instant;
use zeebra::{
    grobner::{
        classify_ideal, differential::polynomial_to_string, f4_reported, fglm_to_lex_with_options,
        solve_from_lex_basis, F4Options, FglmOptions, SolveOptions, SolveOutcome,
    },
    util::Json,
    KnownOrder, MonomialOrder, MultivariatePolynomial,
};

fn basis_json<const N: usize, F: KnownOrder>(
    basis: &[MultivariatePolynomial<N, F>],
    names: &[&str; N],
    order: MonomialOrder,
) -> Json {
    let mut basis: Vec<_> = basis
        .iter()
        .map(|p| polynomial_to_string(p, names, order))
        .collect();
    basis.sort();
    Json::Array(basis.into_iter().map(Json::string).collect())
}

fn checkpoint(value: Json) -> std::time::Duration {
    let started = Instant::now();
    use std::io::Write;
    println!("{}", value.to_json().replace('\n', ""));
    std::io::stdout().flush().unwrap();
    started.elapsed()
}

pub fn profile<const N: usize, F: KnownOrder>(
    system: &[MultivariatePolynomial<N, F>],
    names: &[&str; N],
    options: &F4Options,
    route: &str,
    measure_work: bool,
) -> Json {
    let started = Instant::now();
    let mut checkpoint_time = std::time::Duration::ZERO;
    let order = if route == "direct" {
        MonomialOrder::Lexicographic
    } else {
        MonomialOrder::GradedReverseLexicographic
    };
    let f4_started = Instant::now();
    let solve = || f4_reported(system, order, options);
    #[cfg(feature = "research-work")]
    let ((basis, stats), work) = if measure_work {
        let (result, work) = zeebra::linalg::work::measure(solve);
        (result, work.json())
    } else {
        (solve(), Json::Null)
    };
    #[cfg(not(feature = "research-work"))]
    let ((basis, stats), work) = {
        assert!(!measure_work, "--work requires research-work");
        (solve(), Json::Null)
    };
    let f4_elapsed = f4_started.elapsed();
    let mut fields = vec![
        ("route", Json::string(route)),
        ("f4_call_ns", Json::nanos(f4_elapsed)),
        (
            "statistics",
            super::statistics(&stats, options.measure_stages),
        ),
        ("work", work),
        ("point", Json::Null),
        ("basis", Json::Null),
        ("lex_basis", Json::Null),
        ("conversion", Json::Null),
        ("conversion_call_ns", Json::Null),
        ("recovery_call_ns", Json::Null),
        ("independent_substitution_ns", Json::Null),
        ("error", Json::Null),
    ];
    let set = |fields: &mut Vec<(&str, Json)>, key: &str, value| {
        fields.iter_mut().find(|(name, _)| *name == key).unwrap().1 = value;
    };
    let mut outcome = "basis-refusal";
    if let Ok(basis) = basis {
        set(&mut fields, "basis", basis_json(&basis, names, order));
        // Completed outputs survive a later process-tree time or RSS refusal.
        checkpoint_time += checkpoint(Json::object([
            ("checkpoint", Json::string("source-basis")),
            ("basis", basis_json(&basis, names, order)),
            ("f4_call_ns", Json::nanos(f4_elapsed)),
            (
                "statistics",
                super::statistics(&stats, options.measure_stages),
            ),
        ]));
        if !classify_ideal(&basis, order).is_finite_dimensional() {
            outcome = "positive-dimensional";
        } else {
            let fglm_options = FglmOptions {
                measure_stages: options.measure_stages,
                ..Default::default()
            };
            if route == "fglm" {
                checkpoint_time += checkpoint(Json::object([
                    ("checkpoint", Json::string("active-stage")),
                    ("stage", Json::string("conversion")),
                ]));
            }
            let conversion_started = Instant::now();
            let lex = if route == "fglm" {
                match fglm_to_lex_with_options(&basis, order, &fglm_options) {
                    Ok((lex, fglm)) => {
                        let t = fglm.timings;
                        set(
                            &mut fields,
                            "conversion",
                            Json::object([
                                ("quotient_basis_ns", Json::nanos(t.quotient_basis)),
                                ("operator_ns", Json::nanos(t.operator_construction())),
                                ("dependence_ns", Json::nanos(t.dependence)),
                                ("scalar_sequence_ns", Json::nanos(t.scalar_sequence)),
                                (
                                    "scalar_reconstruction_ns",
                                    Json::nanos(t.scalar_reconstruction),
                                ),
                                ("scalar_certificate_ns", Json::nanos(t.scalar_certificate)),
                                (
                                    "route",
                                    Json::string(format!("{:?}", fglm.conversion_route)),
                                ),
                                ("attempts", Json::size(fglm.wiedemann_attempts)),
                                (
                                    "fallback",
                                    Json::string(format!("{:?}", fglm.wiedemann_fallback)),
                                ),
                                ("dimension", Json::size(fglm.quotient_dimension)),
                                ("operator_entries", Json::size(fglm.operator_entries)),
                                ("operator_bytes", Json::size(fglm.memory.operator_bytes)),
                                ("estimated_bytes", Json::size(fglm.estimated_bytes())),
                                ("full_statistics", Json::string(format!("{fglm:#?}"))),
                            ]),
                        );
                        Some(lex)
                    }
                    Err(error) => {
                        outcome = "conversion-refusal";
                        set(&mut fields, "error", Json::string(error.to_string()));
                        None
                    }
                }
            } else {
                Some(basis)
            };
            if route == "fglm" {
                set(
                    &mut fields,
                    "conversion_call_ns",
                    Json::nanos(conversion_started.elapsed()),
                );
            }
            if let Some(lex) = lex {
                set(
                    &mut fields,
                    "lex_basis",
                    basis_json(&lex, names, MonomialOrder::Lexicographic),
                );
                checkpoint_time += checkpoint(Json::object([
                    ("checkpoint", Json::string("lex-basis")),
                    (
                        "lex_basis",
                        basis_json(&lex, names, MonomialOrder::Lexicographic),
                    ),
                    (
                        "conversion",
                        fields
                            .iter()
                            .find(|(key, _)| *key == "conversion")
                            .unwrap()
                            .1
                            .clone(),
                    ),
                    (
                        "conversion_call_ns",
                        fields
                            .iter()
                            .find(|(key, _)| *key == "conversion_call_ns")
                            .unwrap()
                            .1
                            .clone(),
                    ),
                ]));
                checkpoint_time += checkpoint(Json::object([
                    ("checkpoint", Json::string("active-stage")),
                    ("stage", Json::string("recovery")),
                ]));
                let recovery = Instant::now();
                let mut rng = StdRng::seed_from_u64(0);
                let result = solve_from_lex_basis(&lex, system, &SolveOptions::default(), &mut rng);
                set(
                    &mut fields,
                    "recovery_call_ns",
                    Json::nanos(recovery.elapsed()),
                );
                match result {
                    Ok((SolveOutcome::Point(point), _)) => {
                        let checking = Instant::now();
                        assert!(system.iter().all(|p| p.eval(&point).is_zero()));
                        set(
                            &mut fields,
                            "independent_substitution_ns",
                            Json::nanos(checking.elapsed()),
                        );
                        set(
                            &mut fields,
                            "point",
                            Json::Array(
                                point.iter().map(|p| Json::string(p.to_string())).collect(),
                            ),
                        );
                        outcome = "verified-point";
                    }
                    Ok((SolveOutcome::Inconsistent, _)) => outcome = "inconsistent",
                    Ok((SolveOutcome::NoBaseFieldPoint, _)) => outcome = "no-base-field-point",
                    Err(error) => {
                        outcome = "recovery-refusal";
                        set(&mut fields, "error", Json::string(error.to_string()));
                    }
                }
            }
        }
    } else if let Err(error) = basis {
        set(&mut fields, "error", Json::string(error.to_string()));
    }
    fields.extend([
        ("outcome", Json::string(outcome)),
        ("whole_route_ns", Json::nanos(started.elapsed())),
        ("checkpoint_ns", Json::nanos(checkpoint_time)),
    ]);
    Json::object(fields)
}

#[cfg(test)]
mod tests {
    use super::*;
    use zeebra::{fields::Zp32003, MonomialOrder};

    // Scalar subphase clocks refine dependence and never enlarge the conversion partition.
    #[test]
    fn scalar_subphases_do_not_double_count_dependence() {
        let mut t = zeebra::grobner::fglm::FglmStageTimings::default();
        t.dependence = std::time::Duration::from_millis(10);
        t.scalar_sequence = std::time::Duration::from_millis(3);
        t.scalar_reconstruction = std::time::Duration::from_millis(4);
        t.scalar_certificate = std::time::Duration::from_millis(2);
        assert_eq!(t.sum(), std::time::Duration::from_millis(10));
    }

    // Both fixed routes return a point independently satisfying the original generators.
    #[test]
    fn complete_routes_recover_verified_points() {
        let names = ["x", "y"];
        let system: Vec<MultivariatePolynomial<2, Zp32003>> = ["x^2-1", "y-x"]
            .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
            .to_vec();
        for route in ["direct", "fglm"] {
            let report = profile(&system, &names, &F4Options::default(), route, false);
            assert_eq!(
                report.get("outcome").and_then(Json::as_str),
                Some("verified-point")
            );
            assert_eq!(report.get("point").unwrap().items().len(), 2);
            assert!(!report.get("basis").unwrap().items().is_empty());
        }
        let _ = MonomialOrder::Lexicographic;
    }

    // A basis budget refusal retains the refusal stage and never emits a partial answer.
    #[test]
    fn basis_refusal_has_no_point_or_partial_basis() {
        let names = ["x", "y"];
        let system = vec![MultivariatePolynomial::<2, Zp32003>::parse("x^2+y^2-1", names).unwrap()];
        let options = F4Options {
            max_basis_elements: Some(0),
            ..Default::default()
        };
        let report = profile(&system, &names, &options, "fglm", false);
        assert_eq!(
            report.get("outcome").and_then(Json::as_str),
            Some("basis-refusal")
        );
        assert_eq!(report.get("point"), Some(&Json::Null));
        assert_eq!(report.get("basis"), Some(&Json::Null));
    }
}
