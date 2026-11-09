//! `ACICO`, the third Anemoi model — faithfulness against the permutation, the published
//! invariants, and the shape-position certificate.
//!
//! The model is Campa and Roy's (eprint 2025/814, Definition 14) and the three things worth
//! separating are separated here by test name: a **faithfulness** test runs the actual permutation
//! and never the model's own algebra; a **reproduction** test checks a number the paper published;
//! and the **certificate** test discharges Theorem 8's hypotheses, which is a deduction rather
//! than the detector's observation. `tests/anemoi_shape_position.rs` holds the observation for the
//! other two models.

use zeebra::{
    fields::{Zp1481823929, Zp18446744073709551263},
    grobner::{
        f4_reported,
        fglm::{
            fglm_to_lex_with_options, separating_variables, shape_lex_basis, shape_report,
            FglmOptions, QuotientAlgebra,
        },
        research::{
            anemoi::{Anemoi, AnemoiParameters, ANEMOI_ACICO_PRIME},
            anemoi_cico::{verify_against_anemoi_trace, AnemoiCico, AnemoiModel},
            proved_acico_quotient_dimension,
        },
        shape_position_hypotheses, F4Options, HilbertSeries,
    },
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial, WeightedTieBreak, Zero,
};

/// The 31-bit prime eprint 2025/814 §7.3 measures over.
type A = Zp1481823929;

/// The 64-bit prime the committed Six Worlds witnesses are over.
type S = Zp18446744073709551263;

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

fn acico<F: zeebra::KnownOrder>(prime: u64, rounds: usize) -> AnemoiCico<F> {
    AnemoiCico::new(
        Anemoi::new(AnemoiParameters::six_worlds_at(prime, rounds)).expect("builds"),
        AnemoiModel::Acico,
    )
}

/// `ACICO`'s non-output generators vanish at a trace of the permutation, at `N = 1..5`.
///
/// Faithfulness against the primitive: the assignment comes from running Anemoi, so a model that
/// merely looked right would not vanish. Only the output constraint may fail at an arbitrary
/// input, and it must — a last equation that vanished everywhere would be a model of nothing.
#[test]
fn test_the_acico_model_vanishes_at_a_trace_of_the_permutation() {
    macro_rules! check {
        ($($rounds:literal => $n:literal;)+) => {$(
            let instance = acico::<A>(ANEMOI_ACICO_PRIME, $rounds);
            assert_eq!(instance.variables(), $n);
            let system = instance.system::<$n>().expect("the right N");
            let point = A::new(7 * $rounds as u64 + 11);
            assert_eq!(
                verify_against_anemoi_trace(&instance, &system, point),
                vec![system.len() - 1],
                "ACICO at N = {}: only the output constraint may fail off a witness", $rounds
            );
        )+};
    }
    check! {
        1 => 3;
        2 => 5;
        3 => 7;
        4 => 9;
        5 => 11;
    }
}

/// `ACICO`'s last generator evaluates to the permutation's first output word, at every input.
///
/// Stronger than "the system vanishes at a witness", which only pins one point: this says the
/// output constraint *computes* the quantity the CICO condition is about. A sign error or a
/// mis-ordered final linear layer would survive the vanishing test at a witness and die here.
#[test]
fn test_the_acico_output_constraint_is_the_permutations_first_output_word() {
    let instance = acico::<A>(ANEMOI_ACICO_PRIME, 3);
    for input in [1u64, 2, 3, 97, 1_000_003, 1_481_823_928] {
        let y = A::new(input);
        let expected = instance.anemoi.permutation(A::zero(), y).0;
        assert_eq!(
            instance.output_word::<7>(y),
            Some(expected),
            "the output constraint disagrees with the permutation at y = {input}"
        );
    }
}

/// `ACICO` vanishes entirely at a published CICO witness, output constraint included.
///
/// The witness is the `N = 2` root the committed Six Worlds lex basis determined
/// (`docs/research/anemoi.md` §4), so this is third-party data rather than a point this crate
/// chose. It is at `p = 2^64 − 353`, not the paper's prime: the model is prime-independent and
/// the only published Anemoi CICO witnesses are over that field.
#[test]
fn test_the_acico_model_vanishes_at_a_published_witness() {
    let witness = S::new(1_761_853_426_583_392_112);
    let instance = acico::<S>(18_446_744_073_709_551_263, 2);
    assert!(
        instance.is_solution(witness),
        "the witness is a CICO solution"
    );
    assert_eq!(
        verify_against_anemoi_trace(&instance, &instance.system::<5>().expect("N = 5"), witness),
        Vec::<usize>::new(),
        "every ACICO generator must vanish at a witness"
    );
}

/// The generator degrees are eprint 2025/814's equations (8) and (9), and flat in `N`.
///
/// `α, 1, 2α, α, …, 2α, α, α`. The contrast with `PCICO`'s `3, 4, 6, 8, 10, …` is the model's
/// reason to exist, so it is asserted rather than described.
#[test]
fn test_the_acico_generator_degrees_are_flat_in_the_round_count() {
    macro_rules! check {
        ($($rounds:literal => $n:literal, $degrees:expr;)+) => {$(
            let instance = acico::<A>(ANEMOI_ACICO_PRIME, $rounds);
            let system = instance.system::<$n>().expect("the right N");
            let degrees: Vec<u64> = system.iter().map(|p| p.degree()).collect();
            assert_eq!(degrees, $degrees, "ACICO at N = {}", $rounds);
            assert_eq!(degrees, AnemoiModel::Acico.generator_degrees($rounds, 3));
        )+};
    }
    check! {
        1 => 3, vec![3, 1, 3];
        2 => 5, vec![3, 1, 6, 3, 3];
        3 => 7, vec![3, 1, 6, 3, 6, 3, 3];
        4 => 9, vec![3, 1, 6, 3, 6, 3, 6, 3, 3];
    }
    // The published degree set does not grow: the largest generator degree is 2α at every rung.
    for rounds in 1..=5 {
        let degrees = AnemoiModel::Acico.generator_degrees(rounds, 3);
        assert_eq!(
            degrees.iter().copied().max(),
            Some(if rounds == 1 { 3 } else { 6 })
        );
    }
}

/// The DRL basis has exactly the leading monomials eprint 2025/814's Proposition 2 predicts.
///
/// `{y_0} ∪ {y_j^α, s_j^α, y_j s_j : 1 ≤ j ≤ N}` — `3N + 1` elements. This is a much stronger
/// reproduction than the dimension alone, because the dimension is a count derived *from* this
/// set and could agree while the set did not.
#[test]
fn test_the_acico_drl_basis_has_the_published_leading_monomials() {
    macro_rules! check {
        ($($rounds:literal => $n:literal;)+) => {$(
            let leads = drl_leading_monomials::<$n>($rounds);
            let mut expected: Vec<Monomial<$n>> = vec![Monomial::univariate(0, 1)];
            for round in 1..=$rounds {
                expected.push(Monomial::univariate(round, 3));
                expected.push(Monomial::univariate($rounds + round, 3));
                let mut exponents = [0u32; $n];
                exponents[round] = 1;
                exponents[$rounds + round] = 1;
                expected.push(Monomial::new(&exponents));
            }
            expected.sort_by(|a, b| ORDER.cmp(a, b));
            let mut found = leads;
            found.sort_by(|a, b| ORDER.cmp(a, b));
            assert_eq!(found, expected, "ACICO at N = {}: Proposition 2's leading monomials", $rounds);
        )+};
    }
    check! {
        1 => 3;
        2 => 5;
        3 => 7;
    }
}

/// The quotient dimension is the **proved** `(α + 2)^N`, at `N = 1..4`.
///
/// Proposition 4, which proves what `anemoi.md` §5 could only measure for the other two models.
/// A figure that differs either way is a defect, not a timing.
#[test]
fn test_the_acico_quotient_dimension_is_the_proved_power() {
    macro_rules! check {
        ($($rounds:literal => $n:literal;)+) => {$(
            let claim = proved_acico_quotient_dimension(3, $rounds, 1);
            assert!(claim.is_proved(), "Proposition 4 is a theorem, not a measurement");
            assert_eq!(
                quotient_dimension::<$n>($rounds),
                i128::try_from(*claim.value()).expect("small"),
                "ACICO at N = {}", $rounds
            );
        )+};
    }
    check! {
        1 => 3;
        2 => 5;
        3 => 7;
        4 => 9;
    }
}

/// Theorem 8's printed hypotheses are discharged on `ACICO` at `N = 1..4`.
///
/// **A deduction, and not a sufficient one.** Zero-dimensionality, a pure-power leader for every
/// variable, and a finite top-form quotient are each decided from the basis. They do *not* imply
/// shape position — `shape_certificate`'s module docs and
/// `test_the_published_hypotheses_are_not_sufficient` show why — so the remaining hypothesis is
/// checked separately by
/// `test_the_acico_shape_route_agrees_with_the_classical_conversion`. Nothing here is a proof
/// about the family: that is the paper's Corollary 2, which inherits the same omission.
#[test]
fn test_the_acico_discharges_the_published_syntactic_hypotheses() {
    macro_rules! check {
        ($($rounds:literal => $n:literal;)+) => {$(
            let instance = acico::<A>(ANEMOI_ACICO_PRIME, $rounds);
            let system = instance.system::<$n>().expect("the right N");
            let (basis, _) = f4_reported(&system, ORDER, &F4Options::default());
            let basis = basis.expect("ACICO's basis is nearly free");
            let hypotheses = shape_position_hypotheses(&basis, ORDER, &F4Options::default())
                .unwrap_or_else(|gap| panic!(
                    "ACICO at N = {} fails a printed hypothesis, which contradicts \
                     Proposition 2 and is a defect: {gap:?}", $rounds
                ));
            assert_eq!(hypotheses.quotient_dimension, 5i128.pow($rounds));
            // Proposition 2: degree one in `y_0`, degree `α` in every other variable.
            let mut expected = vec![3u32; $n];
            expected[0] = 1;
            let exponents: Vec<u32> = hypotheses.pure_powers.iter().map(|p| p.exponent).collect();
            assert_eq!(exponents, expected, "N = {}", $rounds);
            // Theorem 4's strict `deg_≺` condition holds on the `s` variables and on `y_0`, and
            // fails on `y_1 … y_N`, whose degree-α tails carry `y_{j−1}^2 s_j`. That asymmetry is
            // why Corollary 2 argues by back-substitution and not by inspection, and asserting it
            // keeps the published argument's shape visible in the suite.
            let strict = hypotheses.strict_variables();
            let last: usize = $rounds;
            for round in 1..=last {
                assert!(
                    strict.contains(&($rounds + round)),
                    "N = {}: s_{} must be strict — its degree-α tail is degree 2 at most",
                    $rounds, round
                );
            }
            assert!(!strict.contains(&0), "N = {}: y_0's generator is linear", $rounds);
            // `y_j` for `j ≥ 2` carries `y_{j−1}^2 s_j` at degree α exactly. At `N = 1` the
            // corresponding tail is `y_0^2 s_1`, which the degree-one generator eliminates, so
            // that one rung is strict in `y_1` — an artefact of the elimination and not a
            // property of the family.
            for round in 2..=last {
                assert!(
                    !strict.contains(&round),
                    "N = {}: y_{} carries a degree-α tail, so Theorem 4 does not reach it",
                    $rounds, round
                );
            }
        )+};
    }
    check! {
        1 => 3;
        2 => 5;
        3 => 7;
        4 => 9;
    }
}

/// The detector agrees with the certificate, and the Krylov lex basis is the classical one.
///
/// The independent confirmation. `shape_report` is a measurement of the same conclusion the
/// certificate deduces, and the reduced lex basis is unique, so a shape basis differing from the
/// classical conversion's is simply wrong.
#[test]
fn test_the_acico_shape_route_agrees_with_the_classical_conversion() {
    macro_rules! check {
        ($($rounds:literal => $n:literal;)+) => {$(
            let instance = acico::<A>(ANEMOI_ACICO_PRIME, $rounds);
            let system = instance.system::<$n>().expect("the right N");
            let basis = zeebra::grobner::f4(&system, ORDER).expect("a basis");
            let options = FglmOptions::unbounded();
            let algebra = QuotientAlgebra::new(&basis, ORDER, &options)
                .expect("zero-dimensional");
            let report = shape_report(&algebra, $n - 1);
            assert_eq!(report.dimension, 5usize.pow($rounds), "N = {}", $rounds);
            assert_eq!(
                report.minimal_polynomial_degree, report.dimension,
                "N = {}: the lex-last variable does not generate the quotient algebra, which \
                 would contradict the certificate and be a detector defect", $rounds
            );
            let shape = shape_lex_basis(&algebra).expect("shape position");
            let (classical, _) = fglm_to_lex_with_options(&basis, ORDER, &options)
                .expect("the classical route");
            assert_eq!(shape, classical, "N = {}: the two lex bases must agree", $rounds);
            // Reported rather than asserted elementwise: #224 found every variable separating on
            // FCICO/PCICO, and whether ACICO does too is a fact about this family.
            assert!(
                separating_variables(&algebra).contains(&($n - 1)),
                "N = {}: the lex-last variable must separate", $rounds
            );
        )+};
    }
    check! {
        1 => 3;
        2 => 5;
        3 => 7;
    }
}

/// The three models at one round count are three different systems.
#[test]
fn test_acico_is_a_third_problem_and_not_a_relabelling() {
    let tags: Vec<&str> = [AnemoiModel::Fcico, AnemoiModel::Pcico, AnemoiModel::Acico]
        .iter()
        .map(AnemoiModel::tag)
        .collect();
    assert_eq!(tags, vec!["fcico", "pcico", "acico"]);
    for rounds in 1..=5 {
        let variables: Vec<usize> = [AnemoiModel::Fcico, AnemoiModel::Pcico, AnemoiModel::Acico]
            .iter()
            .map(|m| m.variables(rounds, 1))
            .collect();
        assert_eq!(
            variables,
            vec![2 * rounds, rounds + 1, 2 * rounds + 1],
            "ACICO is the widest of the three at every rung"
        );
    }
}

/// `dim F_p[x]/I` for `ACICO` at `rounds` rounds, from the leading-term ideal of the DRL basis.
fn quotient_dimension<const N: usize>(rounds: usize) -> i128 {
    let instance = acico::<A>(ANEMOI_ACICO_PRIME, rounds);
    let system = instance.system::<N>().expect("the right N");
    let basis = zeebra::grobner::f4(&system, ORDER).expect("a basis");
    let leads: Vec<Monomial<N>> = basis
        .iter()
        .map(|p| p.leading_monomial(ORDER))
        .collect::<Vec<_>>();
    HilbertSeries::of_basis(&basis, ORDER)
        .expect("a monomial ideal")
        .quotient_dimension(&leads)
        .expect("within budget")
        .expect("zero-dimensional")
}

/// The leading monomials of `ACICO`'s reduced DRL basis at `rounds` rounds.
fn drl_leading_monomials<const N: usize>(rounds: usize) -> Vec<Monomial<N>> {
    let instance = acico::<A>(ANEMOI_ACICO_PRIME, rounds);
    let system: Vec<MultivariatePolynomial<N, A>> = instance.system::<N>().expect("the right N");
    zeebra::grobner::f4(&system, ORDER)
        .expect("a basis")
        .iter()
        .map(|p| p.leading_monomial(ORDER))
        .collect()
}

/// The solving degree is flat in the round count — and the whole degree sequence is.
///
/// eprint 2025/814's Table 6 reports `d_solv` constant in `N`, and Zeebra reproduces the claim in
/// a stronger form: the **sequence** of F4 step degrees is identical at every `N ≥ 2`, not merely
/// its maximum. `docs/research/degree-profiles.md` has nothing like this — round count drives
/// degree growth on every Poseidon family measured there.
///
/// The figure is `max_pair_degree`, the highest lcm degree a batch was selected at. The published
/// `d_solv = 9` is **not** this quantity: the paper defines it only as "the maximum degree reached
/// during the GB computation" and gives no reduction convention, so the numbers are not comparable
/// and only the flatness is.
#[test]
fn test_the_acico_solving_degree_is_flat_in_the_round_count() {
    let mut sequences = Vec::new();
    macro_rules! check {
        ($($rounds:literal => $n:literal;)+) => {$(
            let instance = acico::<A>(ANEMOI_ACICO_PRIME, $rounds);
            let system = instance.system::<$n>().expect("the right N");
            let (basis, statistics) = f4_reported(&system, ORDER, &F4Options::default());
            let basis = basis.expect("ACICO's basis is nearly free");
            // Proposition 2 counts `3N + 1` basis elements at `ℓ = 1`.
            assert_eq!(basis.len(), 3 * $rounds + 1, "N = {}", $rounds);
            sequences.push(($rounds, statistics.max_pair_degree, statistics.step_degrees));
        )+};
    }
    check! {
        1 => 3;
        2 => 5;
        3 => 7;
        4 => 9;
        5 => 11;
    }
    assert_eq!(
        sequences[0].1, 4,
        "N = 1 has no 2α generator, so it selects no higher"
    );
    for (rounds, maximum, steps) in &sequences[1..] {
        assert_eq!(*maximum, 6, "N = {rounds}: 2α, and it does not grow");
        assert_eq!(
            steps, &sequences[1].2,
            "N = {rounds}: the step-degree sequence must be the N = 2 one exactly"
        );
    }
}

/// `ACICO` above `α = 3` over the weighted order, reproducing Propositions 3 and 4.
///
/// **A gap this issue recorded as closed.** #201 states that "`ACICO` for `α > 3` is stated over
/// weighted-DRL and is therefore unreachable" — true when it was filed and false now: #306 landed
/// [`MonomialOrder::Weighted`], so WDRL is expressible and the `α ∈ {5, 7, 11}` rows run.
///
/// The weights are Definition 15's own, `w(y) = α` and `w(s) = 2`, with the reverse-lexicographic
/// tie-break Definition 15 specifies. Those satisfy `2w_0 ≥ αw_1` with **equality**, and the
/// equality matters: it makes `y_j^2` and `s_j^α` tie on weighted degree, and the revlex tie-break
/// then puts `y_j^2` above — which is what moves the leading monomials from Proposition 2's
/// `{y_j^α, s_j^α}` to Proposition 3's `{y_j^2, s_j^{α+1}}`.
#[test]
fn test_the_weighted_order_reaches_acico_above_alpha_three() {
    let mut checked = 0;
    macro_rules! check {
        ($($alpha:literal, $rounds:literal => $n:literal;)+) => {$(
            let parameters = AnemoiParameters {
                prime: ANEMOI_ACICO_PRIME,
                alpha: $alpha,
                l: 1,
                rounds: $rounds,
            };
            let anemoi = Anemoi::<A>::new(parameters)
                .expect("alpha is coprime to p - 1 at the paper's prime");
            let instance = AnemoiCico::new(anemoi, AnemoiModel::Acico);
            let order = wdrl($alpha, $rounds);
            let system = instance.system::<$n>().expect("the right N");

            // Equations (8) and (9) again, now at this alpha.
            let degrees: Vec<u64> = system.iter().map(|p| p.degree()).collect();
            assert_eq!(
                degrees,
                AnemoiModel::Acico.generator_degrees($rounds, $alpha),
                "alpha = {}, N = {}", $alpha, $rounds
            );

            let (basis, statistics) = f4_reported(&system, order, &F4Options::default());
            let basis = basis.expect("the WDRL basis is nearly free");
            assert_eq!(basis.len(), 3 * $rounds + 1, "alpha = {}, N = {}", $alpha, $rounds);

            // Proposition 3: `{y_0} u {y_j^2, s_j^{alpha+1}, y_j s_j}`.
            let mut expected: Vec<Monomial<$n>> = vec![Monomial::univariate(0, 1)];
            for round in 1..=$rounds {
                expected.push(Monomial::univariate(round, 2));
                expected.push(Monomial::univariate($rounds + round, $alpha + 1));
                let mut exponents = [0u32; $n];
                exponents[round] = 1;
                exponents[$rounds + round] = 1;
                expected.push(Monomial::new(&exponents));
            }
            expected.sort_by(|a, b| order.cmp(a, b));
            let mut found: Vec<Monomial<$n>> =
                basis.iter().map(|p| p.leading_monomial(order)).collect();
            found.sort_by(|a, b| order.cmp(a, b));
            assert_eq!(
                found, expected,
                "alpha = {}, N = {}: Proposition 3's leading monomials", $alpha, $rounds
            );

            // Proposition 4, which covers alpha in {3, 5, 7, 11} over WDRL.
            let claim = proved_acico_quotient_dimension($alpha, $rounds, 1);
            let leads: Vec<Monomial<$n>> =
                basis.iter().map(|p| p.leading_monomial(order)).collect();
            let dimension = HilbertSeries::of_basis(&basis, order)
                .expect("a monomial ideal")
                .quotient_dimension(&leads)
                .expect("within budget")
                .expect("zero-dimensional");
            assert_eq!(
                dimension,
                i128::try_from(*claim.value()).expect("small"),
                "alpha = {}, N = {}", $alpha, $rounds
            );

            // Flat in N here too: the maximum is alpha + 2, the quotient dimension's base.
            assert_eq!(
                statistics.max_pair_degree, u64::from($alpha as u32) + 2,
                "alpha = {}, N = {}", $alpha, $rounds
            );
            checked += 1;
        )+};
    }
    check! {
        5, 1 => 3;
        5, 2 => 5;
        5, 3 => 7;
        7, 1 => 3;
        7, 2 => 5;
        7, 3 => 7;
        11, 1 => 3;
        11, 2 => 5;
        11, 3 => 7;
    }
    assert_eq!(checked, 9, "three exponents at three round counts");
}

/// At `α = 5` over WDRL the detector fires and the two lex bases agree, as at `α = 3`.
#[test]
fn test_the_weighted_acico_is_in_shape_position() {
    macro_rules! check {
        ($($alpha:literal, $rounds:literal => $n:literal;)+) => {$(
            let parameters = AnemoiParameters {
                prime: ANEMOI_ACICO_PRIME,
                alpha: $alpha,
                l: 1,
                rounds: $rounds,
            };
            let instance = AnemoiCico::new(
                Anemoi::<A>::new(parameters).expect("builds"),
                AnemoiModel::Acico,
            );
            let order = wdrl($alpha, $rounds);
            let system = instance.system::<$n>().expect("the right N");
            let basis = zeebra::grobner::f4(&system, order).expect("a basis");
            let options = FglmOptions::unbounded();
            let algebra = QuotientAlgebra::new(&basis, order, &options).expect("zero-dimensional");
            let report = shape_report(&algebra, $n - 1);
            assert_eq!(
                report.dimension,
                (($alpha + 2) as usize).pow($rounds),
                "alpha = {}, N = {}", $alpha, $rounds
            );
            assert_eq!(
                report.minimal_polynomial_degree, report.dimension,
                "alpha = {}, N = {}: the lex-last variable does not generate the quotient algebra",
                $alpha, $rounds
            );
            let shape = shape_lex_basis(&algebra).expect("shape position");
            let (classical, _) = fglm_to_lex_with_options(&basis, order, &options)
                .expect("the classical route");
            assert_eq!(shape, classical, "alpha = {}, N = {}", $alpha, $rounds);
        )+};
    }
    check! {
        5, 1 => 3;
        5, 2 => 5;
        7, 1 => 3;
        7, 2 => 5;
    }
}

/// Definition 15's weighted DRL order at `ℓ = 1`: `w(y_r) = α`, `w(s_r) = 2`, revlex ties.
fn wdrl(alpha: u32, rounds: usize) -> MonomialOrder {
    let mut weights = vec![alpha; rounds + 1];
    weights.extend(std::iter::repeat_n(2u32, rounds));
    MonomialOrder::weighted(&weights, WeightedTieBreak::ReverseLexicographic)
        .expect("the weights are positive")
}
