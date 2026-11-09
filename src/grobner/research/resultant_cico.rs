//! A Poseidon CICO slice as a bivariate pair, and the experimental degree of its resultant.
//!
//! The general bivariate resultant is [`grobner::resultant`](crate::grobner::resultant); this is
//! the formulation that feeds it from a CICO instance.

use crate::{
    grobner::research::poseidon::{CicoInstance, PoseidonError},
    FiniteField, KnownOrder, Monomial, MultivariatePolynomial,
};

/// The constrained output words of a CICO instance, as polynomials in its first two free inputs.
///
/// **This is the elimination.** Every S-box output of a Poseidon permutation is a polynomial in the
/// inputs — the round function is a straight-line program, so there is nothing to solve for, only
/// to evaluate — and fixing all but two free inputs leaves `k` polynomials in two variables. The
/// 46-equation, 46-variable system M23-B measured becomes two polynomials of degree `3^rounds`.
///
/// That is the trade the S-box-per-variable formulation declines to make: it holds every equation
/// at degree `alpha` and pays one variable per S-box, which is the right call when many inputs are
/// free and the wrong one when two are.
///
/// # Errors
/// [`PoseidonError::WrongStateWidth`] unless `fixed` has `t − k − 2` entries, and whatever the
/// permutation reports.
pub fn cico_bivariate<F: KnownOrder>(
    instance: &CicoInstance<F>,
    fixed: &[F],
) -> Result<Vec<MultivariatePolynomial<2, F>>, PoseidonError> {
    let poseidon = &instance.poseidon;
    let t = poseidon.parameters.t;
    let k = instance.k;
    let free = instance.free_inputs();
    if free < 2 || fixed.len() + 2 != free {
        return Err(PoseidonError::WrongStateWidth {
            expected: free.saturating_sub(2),
            found: fixed.len(),
        });
    }

    let constant = |c: F| -> MultivariatePolynomial<2, F> {
        MultivariatePolynomial::new(&[(Monomial::new(&[0, 0]), c)])
    };
    let variable = |index: usize| -> MultivariatePolynomial<2, F> {
        let mut exponents = [0u32; 2];
        exponents[index] = 1;
        MultivariatePolynomial::new(&[(Monomial::new(&exponents), F::one())])
    };
    let power = |p: &MultivariatePolynomial<2, F>, alpha: u32| -> MultivariatePolynomial<2, F> {
        let mut result = p.clone();
        for _ in 1..alpha {
            result = &result * p;
        }
        result
    };
    let mds = |state: &[MultivariatePolynomial<2, F>]| -> Vec<MultivariatePolynomial<2, F>> {
        poseidon
            .mds
            .iter()
            .map(|row| {
                row.iter()
                    .zip(state)
                    .fold(MultivariatePolynomial::zero(), |acc, (m, word)| {
                        acc + word.scale(m)
                    })
            })
            .collect()
    };

    // The input state: the instance's constrained prefix, the two unknowns, then the fixed values.
    let mut state: Vec<MultivariatePolynomial<2, F>> = Vec::with_capacity(t);
    for i in 0..k {
        state.push(constant(instance.constants[i]));
    }
    state.push(variable(0));
    state.push(variable(1));
    for value in fixed {
        state.push(constant(*value));
    }
    debug_assert_eq!(state.len(), t);

    // The CICO verifier applies the MDS before the first round, as `permutation_plus_linear` does.
    state = mds(&state);

    let alpha = poseidon.parameters.alpha;
    let half = poseidon.parameters.r_f / 2;
    let mut round = 0;
    for _ in 0..half {
        add_constants(&mut state, &poseidon.round_constants[round], &constant);
        for word in state.iter_mut() {
            *word = power(word, alpha);
        }
        state = mds(&state);
        round += 1;
    }
    for _ in 0..poseidon.parameters.r_p {
        add_constants(&mut state, &poseidon.round_constants[round], &constant);
        state[0] = power(&state[0], alpha);
        state = mds(&state);
        round += 1;
    }
    for _ in 0..half {
        add_constants(&mut state, &poseidon.round_constants[round], &constant);
        for word in state.iter_mut() {
            *word = power(word, alpha);
        }
        state = mds(&state);
        round += 1;
    }

    // The constrained words, with their targets subtracted: a common root of these is a solution.
    Ok((0..k)
        .map(|i| &state[i] - &constant(instance.constants[k + i]))
        .collect())
}

/// Add one round's constants to a symbolic state.
fn add_constants<F: FiniteField>(
    state: &mut [MultivariatePolynomial<2, F>],
    constants: &[F],
    constant: &impl Fn(F) -> MultivariatePolynomial<2, F>,
) {
    for (word, c) in state.iter_mut().zip(constants) {
        *word = &*word + &constant(*c);
    }
}

/// JAZ slide 22's experimental resultant degree for a Poseidon CICO slice: `alpha^(2 R_F + R_P)`.
///
/// **Unproven in its source**, whose own authors leave the reason open, and confirmed here on three
/// registered slices — see `docs/research/resultant-elimination.md` §6.3. It is a prediction and
/// not a bound, so nothing may interpolate against it without checking the recovered polynomial
/// off the interpolation domain. [`bivariate_resultant_predicted`] does that and falls back to the
/// proven bound when the check refuses it.
///
/// `None` when the power overflows `usize`.
pub fn predicted_resultant_degree(alpha: u32, r_f: usize, r_p: usize) -> Option<usize> {
    let exponent = u32::try_from(r_f.checked_mul(2)?.checked_add(r_p)?).ok()?;
    usize::try_from(alpha).ok()?.checked_pow(exponent)
}

#[cfg(test)]
mod tests {
    use super::{cico_bivariate, predicted_resultant_degree};
    use crate::{
        fields::PrimeFieldElement64,
        grobner::{
            research::KOALABEAR_PRIME,
            resultant::{
                bivariate_resultant, bivariate_resultant_ntt, bivariate_resultant_ntt_with,
                bivariate_resultant_predicted, sylvester_determinant_at, DegreeSource,
                ResultantOptions, ResultantRoute,
            },
        },
        FiniteField, One, Polynomial, UnivariatePolynomial, Zero,
    };

    type Koala = PrimeFieldElement64<KOALABEAR_PRIME>;

    /// Every registered CICO row's predicted resultant degree is `alpha^(2 R_F + R_P)`.
    ///
    /// The three degrees `resultant-elimination.md` §6.3 confirms are in the list, and the rest
    /// are the predictions #211 costs the six-round rows from.
    #[test]
    fn test_the_predicted_degree_of_each_registered_row() {
        use crate::grobner::research::challenge;

        for (id, degree) in [
            ("poseidon31-cico-t16-rf2-rp0", 81usize),
            ("poseidon31-cico-t16-rf2-rp2", 729),
            ("poseidon31-cico-t16-rf4-rp0", 6_561),
            ("poseidon31-cico-t16-rf2-rp4", 6_561),
            ("poseidon31-cico-t16-rf4-rp2", 59_049),
            ("poseidon31-cico-t16-rf6-rp0", 531_441),
        ] {
            let parameters = challenge(id)
                .expect("registered")
                .poseidon_parameters()
                .expect("a CICO row");
            assert_eq!(
                predicted_resultant_degree(parameters.alpha, parameters.r_f, parameters.r_p),
                Some(degree),
                "{id}"
            );
        }
    }

    /// The predicted count is `degree + 1`, and on `rf2-rp2` that is 730 rather than 1 024.
    ///
    /// The pairing #179 warns about: 730 is not a power of two, so this route interpolates at
    /// arbitrary points and an NTT domain would round up and give back a third of the saving.
    #[test]
    fn test_the_predicted_sample_count_is_not_a_power_of_two() {
        let degree = predicted_resultant_degree(3, 2, 2).expect("fits");
        assert_eq!(degree + 1, 730);
        assert_ne!(730usize.next_power_of_two(), 730);
        assert_eq!(
            predicted_resultant_degree(3, 4, 0).expect("fits") + 1,
            6_562
        );
    }

    /// On the registered two-round slice the predicted count recovers the identical polynomial.
    ///
    /// 82 samples against the proven bound's 163, same coefficients, and the off-domain check
    /// holds.
    #[test]
    fn test_the_predicted_count_agrees_with_the_proven_bound_on_the_registered_slice() {
        use crate::grobner::research::{challenge, Specialization};

        let manifest = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
        let parameters = manifest.poseidon_parameters().expect("a CICO row");
        let instance = manifest.cico_instance::<Koala>().expect("builds");
        let free = instance.free_inputs();
        let variables: Vec<usize> = (2..free).collect();
        let specialization =
            Specialization::<46, Koala>::seeded(&variables, 1).expect("distinct indices");
        let fixed: Vec<Koala> = (2..free)
            .map(|i| specialization.value_of(i).expect("fixed"))
            .collect();
        let outputs = cico_bivariate(&instance, &fixed).expect("two free inputs remain");

        let degree = predicted_resultant_degree(parameters.alpha, parameters.r_f, parameters.r_p)
            .expect("3^4 fits");
        let (predicted, stages) = bivariate_resultant_predicted(
            &outputs[0],
            &outputs[1],
            1,
            degree,
            ResultantOptions::default(),
        )
        .expect("both involve the second");
        assert_eq!(stages.samples, 82, "3^(2·2+0) + 1 points");
        assert_eq!(stages.degree_bound, 162, "the proven bound, not used");
        assert_eq!(
            stages.degree_source,
            DegreeSource::PredictionHeld { degree: 81 }
        );
        assert_eq!(
            predicted,
            bivariate_resultant(&outputs[0], &outputs[1], 1).expect("ok"),
            "the same coefficients as the proven path"
        );
    }

    /// A held prediction gives the identical verdict and the identical resultant at 1, 8 and 32.
    ///
    /// The validation's determinants now go through the same indexed parallel loop as the
    /// interpolation's, so the thing to pin is that spreading them changed neither the decision nor
    /// the polynomial the decision was made about.
    #[test]
    fn test_a_held_verdict_and_its_resultant_are_identical_at_every_concurrency() {
        use crate::grobner::research::{challenge, Specialization};

        let manifest = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
        let instance = manifest.cico_instance::<Koala>().expect("builds");
        let free = instance.free_inputs();
        let variables: Vec<usize> = (2..free).collect();
        let specialization =
            Specialization::<46, Koala>::seeded(&variables, 1).expect("distinct indices");
        let fixed: Vec<Koala> = (2..free)
            .map(|i| specialization.value_of(i).expect("fixed"))
            .collect();
        let outputs = cico_bivariate(&instance, &fixed).expect("two free inputs remain");

        let mut expected: Option<UnivariatePolynomial<Koala>> = None;
        for workers in [1usize, 8, 32] {
            let (resultant, stages) = bivariate_resultant_predicted(
                &outputs[0],
                &outputs[1],
                1,
                81,
                ResultantOptions::with_concurrency(workers),
            )
            .expect("both involve the second");
            assert_eq!(
                stages.degree_source,
                DegreeSource::PredictionHeld { degree: 81 },
                "the same verdict at {workers} workers"
            );
            assert_eq!(
                stages.off_domain_checks,
                ResultantOptions::DEFAULT_OFF_DOMAIN_CHECKS,
                "all eight checks at {workers} workers"
            );
            match &expected {
                None => expected = Some(resultant),
                Some(first) => assert_eq!(&resultant, first, "{workers} workers"),
            }
        }
    }

    /// The elimination's three stage durations sum to the route's measured wall clock, once each.
    ///
    /// The regression test for a double-counted stage: a duration charged to two stages makes the
    /// sum exceed the outer timer, and a duration charged to none makes it fall well short.
    #[test]
    fn test_the_stage_durations_sum_to_the_measured_elapsed() {
        use std::time::Instant;

        use crate::grobner::research::{challenge, Specialization};

        let manifest = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
        let instance = manifest.cico_instance::<Koala>().expect("builds");
        let free = instance.free_inputs();
        let variables: Vec<usize> = (2..free).collect();
        let specialization =
            Specialization::<46, Koala>::seeded(&variables, 1).expect("distinct indices");
        let fixed: Vec<Koala> = (2..free)
            .map(|i| specialization.value_of(i).expect("fixed"))
            .collect();
        let outputs = cico_bivariate(&instance, &fixed).expect("two free inputs remain");

        let started = Instant::now();
        let (_, stages) = bivariate_resultant_predicted(
            &outputs[0],
            &outputs[1],
            1,
            81,
            ResultantOptions::default(),
        )
        .expect("both involve the second");
        let measured = started.elapsed();

        assert_eq!(
            stages.degree_source,
            DegreeSource::PredictionHeld { degree: 81 },
            "the held path is the one that reports a validation cost"
        );
        assert!(
            stages.validation > std::time::Duration::ZERO,
            "the validation is its own reported stage, not folded into the sampling"
        );
        assert!(
            stages.elapsed() <= measured,
            "the stages sum to {:?}, more than the {:?} the route took — something is counted \
             twice",
            stages.elapsed(),
            measured
        );
        assert!(
            stages.elapsed().as_secs_f64() >= 0.5 * measured.as_secs_f64(),
            "the stages sum to {:?} against {:?} measured — more than half the route is \
             unattributed",
            stages.elapsed(),
            measured
        );
    }

    /// A held prediction on the parallel path records that it was validated.
    #[test]
    fn test_a_held_prediction_records_its_checks_on_the_parallel_path() {
        use crate::grobner::research::{challenge, Specialization};

        let manifest = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
        let instance = manifest.cico_instance::<Koala>().expect("builds");
        let free = instance.free_inputs();
        let variables: Vec<usize> = (2..free).collect();
        let specialization =
            Specialization::<46, Koala>::seeded(&variables, 1).expect("distinct indices");
        let fixed: Vec<Koala> = (2..free)
            .map(|i| specialization.value_of(i).expect("fixed"))
            .collect();
        let outputs = cico_bivariate(&instance, &fixed).expect("two free inputs remain");

        let (resultant, stages) = bivariate_resultant_predicted(
            &outputs[0],
            &outputs[1],
            1,
            81,
            ResultantOptions::with_concurrency(8).with_off_domain_checks(3),
        )
        .expect("both involve the second");
        assert_eq!(
            stages.degree_source,
            DegreeSource::PredictionHeld { degree: 81 }
        );
        assert_eq!(stages.off_domain_checks, 3, "the count it was asked for");
        assert_eq!(stages.concurrency, 8);
        assert_eq!(
            resultant,
            bivariate_resultant(&outputs[0], &outputs[1], 1).expect("ok")
        );
    }

    /// The registered `t = 16` slice, end to end: evaluate, eliminate, solve, verify.
    ///
    /// The spike's whole claim in one test. `cico_bivariate` turns the 46-variable system into two
    /// polynomials of degree `3^2 = 9`; their resultant has degree 81, exactly the Bézout bound;
    /// its roots extend to points that the **permutation** accepts. Nothing about this test trusts
    /// the resultant — `is_solution` runs the real permutation on the recovered inputs.
    #[test]
    fn test_the_registered_full_width_slice_end_to_end() {
        use rand::{prelude::StdRng, SeedableRng};

        use crate::{
            fields::PrimeFieldElement64,
            grobner::research::{challenge, Specialization, KOALABEAR_PRIME},
            roots,
        };

        type Koala = PrimeFieldElement64<KOALABEAR_PRIME>;

        let manifest = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
        let instance = manifest.cico_instance::<Koala>().expect("builds");
        let free = instance.free_inputs();

        // The slice M23-B and M23-C measured, from the same seeded stream.
        let variables: Vec<usize> = (2..free).collect();
        let specialization =
            Specialization::<46, Koala>::seeded(&variables, 1).expect("distinct indices");
        let fixed: Vec<Koala> = (2..free)
            .map(|i| specialization.value_of(i).expect("fixed"))
            .collect();

        let outputs = cico_bivariate(&instance, &fixed).expect("two free inputs remain");
        assert_eq!(outputs.len(), 2, "k = 2 constrained words");
        for output in &outputs {
            assert_eq!(output.degree(), 9, "two rounds of a cubic S-box");
        }

        let resultant =
            bivariate_resultant(&outputs[0], &outputs[1], 1).expect("both involve the second");
        assert_eq!(resultant.degree(), 81, "9 x 9, the Bézout bound exactly");

        // Every root is a candidate for the first unknown; the second comes from the first
        // polynomial and is checked against the second. Three of them survive and verify.
        let mut verified = 0;
        for first in roots(&resultant, &mut StdRng::seed_from_u64(7)) {
            let specialized: Vec<Koala> = (0..=9)
                .map(|power| {
                    outputs[0]
                        .terms()
                        .iter()
                        .filter(|(monomial, _)| monomial.exponents()[1] as usize == power)
                        .map(|(monomial, c)| *c * first.pow(monomial.exponents()[0] as u128))
                        .fold(Koala::zero(), |acc, term| acc + term)
                })
                .collect();
            for second in roots(
                &UnivariatePolynomial::new(&specialized),
                &mut StdRng::seed_from_u64(11),
            ) {
                let mut inputs = vec![first, second];
                inputs.extend_from_slice(&fixed);
                if instance.is_solution(&inputs).expect("the right width") {
                    verified += 1;
                }
            }
        }
        assert_eq!(
            verified, 3,
            "the seed-1 slice has three base-field solutions, and the permutation accepts all of \
             them"
        );
    }

    /// The registered two-round slice, end to end on the subgroup route.
    ///
    /// The A/B control: same instance, same seed, same three witnesses through the permutation as
    /// `test_the_registered_full_width_slice_end_to_end`, but interpolated on the subgroup.
    #[test]
    fn test_the_registered_slice_end_to_end_on_the_subgroup_route() {
        use rand::{prelude::StdRng, SeedableRng};

        use crate::{
            grobner::research::{challenge, Specialization},
            roots,
        };

        let manifest = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
        let instance = manifest.cico_instance::<Koala>().expect("builds");
        let free = instance.free_inputs();
        let variables: Vec<usize> = (2..free).collect();
        let specialization =
            Specialization::<46, Koala>::seeded(&variables, 1).expect("distinct indices");
        let fixed: Vec<Koala> = (2..free)
            .map(|i| specialization.value_of(i).expect("fixed"))
            .collect();

        let outputs = cico_bivariate(&instance, &fixed).expect("two free inputs remain");
        let (resultant, stages) =
            bivariate_resultant_ntt(&outputs[0], &outputs[1], 1).expect("both involve the second");
        assert_eq!(stages.route, ResultantRoute::Ntt { log_size: 8 });
        assert_eq!(resultant.degree(), 81, "9 x 9, the Bézout bound exactly");
        assert_eq!(
            resultant,
            bivariate_resultant(&outputs[0], &outputs[1], 1).expect("ok"),
            "the two routes return the same polynomial"
        );

        let mut verified = 0;
        for first in roots(&resultant, &mut StdRng::seed_from_u64(7)) {
            let specialized: Vec<Koala> = (0..=9)
                .map(|power| {
                    outputs[0]
                        .terms()
                        .iter()
                        .filter(|(monomial, _)| monomial.exponents()[1] as usize == power)
                        .map(|(monomial, c)| *c * first.pow(monomial.exponents()[0] as u128))
                        .fold(Koala::zero(), |acc, term| acc + term)
                })
                .collect();
            for second in roots(
                &UnivariatePolynomial::new(&specialized),
                &mut StdRng::seed_from_u64(11),
            ) {
                let mut inputs = vec![first, second];
                inputs.extend_from_slice(&fixed);
                if instance.is_solution(&inputs).expect("the right width") {
                    verified += 1;
                }
            }
        }
        assert_eq!(
            verified, 3,
            "the same three witnesses the reference route finds"
        );
    }

    /// Every witness in the committed fixture is accepted by the instance's own verifier.
    ///
    /// The fixture is the retained artifact for the four-round rows, whose own run takes about a
    /// minute: the coordinates are checked here in milliseconds, by `is_solution` — which runs
    /// `permutation_plus_linear` — and not by anything in this module.
    #[test]
    fn test_the_recorded_witnesses_verify_through_the_permutation() {
        use crate::grobner::research::{challenge, Json, Specialization};

        let text = include_str!("../../../research/witnesses/resultant-cico-t16.json");
        let fixture = Json::parse(text).expect("the committed fixture");
        let witnesses = fixture.get("witnesses").expect("a witness list").items();
        assert!(!witnesses.is_empty());

        for witness in witnesses {
            let id = witness
                .get("challenge")
                .and_then(Json::as_str)
                .expect("an id");
            let seed = witness.get("seed").and_then(Json::as_int).expect("a seed") as u64;
            let first = Koala::new(witness.get("first").and_then(Json::as_int).expect("x") as u64);
            let second =
                Koala::new(witness.get("second").and_then(Json::as_int).expect("y") as u64);

            let manifest = challenge(id).expect("a registered challenge");
            let instance = manifest.cico_instance::<Koala>().expect("builds");
            let free = instance.free_inputs();
            let variables: Vec<usize> = (2..free).collect();
            let specialization =
                Specialization::<46, Koala>::seeded(&variables, seed).expect("distinct indices");
            let mut inputs = vec![first, second];
            inputs.extend((2..free).map(|i| specialization.value_of(i).expect("fixed")));

            assert!(
                instance.is_solution(&inputs).expect("the right width"),
                "{id} witness ({first}, {second}) is not a solution"
            );
        }
    }

    /// The registered slice returns the same resultant and the same witnesses at 1, 8 and 32.
    ///
    /// The end-to-end form of the determinism claim, on a fixed seed and a registered problem:
    /// the witnesses are what a scoreboard row reports, and `is_solution` runs the permutation on
    /// each, so this pins the whole pipeline rather than the sample loop alone.
    #[test]
    fn test_the_registered_slice_gives_the_same_witnesses_at_every_concurrency() {
        use rand::{prelude::StdRng, SeedableRng};

        use crate::{
            grobner::research::{challenge, Specialization},
            roots,
        };

        let manifest = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
        let instance = manifest.cico_instance::<Koala>().expect("builds");
        let free = instance.free_inputs();
        let variables: Vec<usize> = (2..free).collect();
        let specialization =
            Specialization::<46, Koala>::seeded(&variables, 1).expect("distinct indices");
        let fixed: Vec<Koala> = (2..free)
            .map(|i| specialization.value_of(i).expect("fixed"))
            .collect();
        let outputs = cico_bivariate(&instance, &fixed).expect("two free inputs remain");

        let mut expected_resultant: Option<UnivariatePolynomial<Koala>> = None;
        let mut expected_witnesses: Vec<(Koala, Koala)> = Vec::new();
        for workers in [1usize, 8, 32] {
            let (resultant, _) = bivariate_resultant_ntt_with(
                &outputs[0],
                &outputs[1],
                1,
                ResultantOptions::with_concurrency(workers),
            )
            .expect("both involve the second");

            let mut witnesses: Vec<(Koala, Koala)> = Vec::new();
            for first in roots(&resultant, &mut StdRng::seed_from_u64(7)) {
                let specialized: Vec<Koala> = (0..=9)
                    .map(|power| {
                        outputs[0]
                            .terms()
                            .iter()
                            .filter(|(monomial, _)| monomial.exponents()[1] as usize == power)
                            .map(|(monomial, c)| *c * first.pow(monomial.exponents()[0] as u128))
                            .fold(Koala::zero(), |acc, term| acc + term)
                    })
                    .collect();
                for second in roots(
                    &UnivariatePolynomial::new(&specialized),
                    &mut StdRng::seed_from_u64(11),
                ) {
                    let mut inputs = vec![first, second];
                    inputs.extend_from_slice(&fixed);
                    if instance.is_solution(&inputs).expect("the right width") {
                        witnesses.push((first, second));
                    }
                }
            }
            assert_eq!(witnesses.len(), 3, "the seed-1 slice has three witnesses");

            match &expected_resultant {
                None => {
                    expected_resultant = Some(resultant);
                    expected_witnesses = witnesses;
                }
                Some(first) => {
                    assert_eq!(&resultant, first, "{workers} workers");
                    assert_eq!(witnesses, expected_witnesses, "{workers} workers");
                }
            }
        }
    }

    /// The four-round row completes and returns a witness the permutation accepts.
    ///
    /// Ignored by default: 16 384 Sylvester determinants of order 162 is about a minute, which is
    /// not a unit test. It is the generator behind the fixture above, and the degree assertion is
    /// the interesting part — 729, well below the Bézout bound of 6 561.
    #[test]
    #[ignore = "about a minute: 16 384 order-162 determinants"]
    fn test_the_four_round_row_completes_on_the_subgroup_route() {
        use rand::{prelude::StdRng, SeedableRng};

        use crate::{
            grobner::research::{challenge, Specialization},
            roots,
        };

        let manifest = challenge("poseidon31-cico-t16-rf2-rp2").expect("registered");
        let instance = manifest.cico_instance::<Koala>().expect("builds");
        let free = instance.free_inputs();
        let variables: Vec<usize> = (2..free).collect();
        let specialization =
            Specialization::<46, Koala>::seeded(&variables, 1).expect("distinct indices");
        let fixed: Vec<Koala> = (2..free)
            .map(|i| specialization.value_of(i).expect("fixed"))
            .collect();

        let outputs = cico_bivariate(&instance, &fixed).expect("two free inputs remain");
        let (resultant, stages) =
            bivariate_resultant_ntt(&outputs[0], &outputs[1], 1).expect("both involve the second");
        assert_eq!(stages.route, ResultantRoute::Ntt { log_size: 14 });
        assert_eq!(stages.degree_bound, 13_122);
        assert_eq!(resultant.degree(), 729, "below the Bézout bound of 6 561");

        // Independent of the interpolation: the recovered polynomial against the determinant at a
        // point the subgroup does not contain.
        let off_domain = Koala::new(3);
        assert!(!off_domain.pow(1u128 << 14).is_one());
        assert_eq!(
            resultant.eval(&off_domain),
            sylvester_determinant_at(&outputs[0], &outputs[1], 1, off_domain).expect("ok")
        );

        let mut verified = 0;
        for first in roots(&resultant, &mut StdRng::seed_from_u64(7)) {
            let mut specialized: Vec<Koala> = Vec::new();
            for (monomial, c) in outputs[0].terms() {
                let power = monomial.exponents()[1] as usize;
                if specialized.len() <= power {
                    specialized.resize(power + 1, Koala::zero());
                }
                specialized[power] += *c * first.pow(monomial.exponents()[0] as u128);
            }
            for second in roots(
                &UnivariatePolynomial::new(&specialized),
                &mut StdRng::seed_from_u64(11),
            ) {
                let mut inputs = vec![first, second];
                inputs.extend_from_slice(&fixed);
                if instance.is_solution(&inputs).expect("the right width") {
                    verified += 1;
                }
            }
        }
        assert_eq!(verified, 1, "one base-field witness at four rounds");
    }
}
