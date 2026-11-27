//! Weight vectors under which an input system already is a Gröbner basis (#1192).
//!
//! FreeLunch-style bypass on arbitrary input: search for positive integer weights `w` and one
//! leading monomial `m_i` per generator such that `w·m_i > w·m'` for every other monomial `m'` of
//! generator `i`, with the `m_i` pairwise coprime. Under the weighted order those are the leading
//! monomials whatever the tie-break, and Buchberger's first criterion makes the generators a
//! Gröbner basis with no reduction at all.
//!
//! Choosing the `m_i` is combinatorial and bounded by [`DetectorLimits`]; once they are chosen the
//! weights are a linear feasibility problem, solved exactly. Every hit is re-checked against the
//! polynomials under the order it names before it is returned, so a hit is a certificate. A miss
//! means *not found within the limits*, never *not a Gröbner basis under any order*.
//!
//! Opt-in research tooling: nothing on a solving path calls it.

mod lp;

pub use lp::WeightSearchError;

use std::collections::HashSet;

use lp::{smallest_weights, Constraint, LpWork};

use crate::{
    grobner::leading_monomials_are_pairwise_coprime, FiniteField, Monomial, MonomialOrder,
    MultivariatePolynomial, WeightedTieBreak,
};

/// Bounds on the search.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DetectorLimits {
    /// Achievable leading monomials kept per generator, fewest variables first.
    pub candidates_per_generator: usize,
    /// Linear programs solved before giving up.
    pub max_lp_solves: usize,
    /// Nodes of the combinatorial screen before it defers to the LP search undecided.
    pub max_screen_nodes: usize,
}

impl Default for DetectorLimits {
    fn default() -> Self {
        Self {
            candidates_per_generator: 4,
            max_lp_solves: 256,
            max_screen_nodes: 4096,
        }
    }
}

/// A weighted order under which the input is a Gröbner basis, and its leading monomials.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FreeBasis<const N: usize> {
    /// The weights, smallest on their ray; all ones when the plain graded order suffices.
    pub weights: Vec<u32>,
    /// `MonomialOrder::weighted(weights, tie_break)`.
    pub order: MonomialOrder,
    /// Each generator's leading monomial under `order`, in input order. Pairwise coprime.
    pub leading: Vec<Monomial<N>>,
}

/// Why no certificate was returned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DetectionMiss {
    /// No generators.
    Empty,
    /// A zero generator has no leading monomial.
    ZeroGenerator,
    /// A nonzero constant generator: the ideal is the whole ring, out of scope here.
    ConstantGenerator,
    /// More generators than variables, so no pairwise-coprime choice of nonconstant monomials
    /// exists. Decided without any search.
    TooManyGenerators { generators: usize, variables: usize },
    /// The bounded search found nothing.
    NoCertificate,
    /// [`DetectorLimits::max_lp_solves`] ran out first.
    BudgetExhausted,
    /// Exact arithmetic left its range.
    Arithmetic(WeightSearchError),
}

/// What the search did.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DetectionStatistics {
    /// The all-ones order alone decided the hit.
    pub fast_path: bool,
    /// Nodes of the combinatorial screen: coprime choices among divisibility-maximal monomials,
    /// with no linear program. A miss it decides costs no LP at all.
    pub screen_nodes: usize,
    /// Achievable leading monomials kept, summed over generators.
    pub candidates: usize,
    /// Partial assignments the search extended.
    pub nodes: usize,
    /// Linear programs solved.
    pub lp_solves: usize,
    /// Simplex pivots over all of them.
    pub lp_pivots: usize,
}

/// The outcome and its cost.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Detection<const N: usize> {
    pub outcome: Result<FreeBasis<N>, DetectionMiss>,
    pub statistics: DetectionStatistics,
}

/// Search for a weighted order, with ties broken by `tie_break`, under which `system` already is a
/// Gröbner basis by pairwise-coprime leading monomials.
///
/// ```
/// use zeebra::{
///     fields::Zp32003 as F,
///     grobner::{is_grobner_basis, weight_detector::{detect_free_basis, DetectorLimits}},
///     MultivariatePolynomial, WeightedTieBreak,
/// };
///
/// // Under grevlex the leading monomials are x^3 and x^2; under weights (3, 5) they are y^2, x^2.
/// let system: Vec<MultivariatePolynomial<2, F>> = ["y^2 - x^3", "x^2 + y"]
///     .iter()
///     .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
///     .collect();
/// let detection =
///     detect_free_basis(&system, WeightedTieBreak::ReverseLexicographic, &DetectorLimits::default());
/// let hit = detection.outcome.unwrap();
/// assert!(is_grobner_basis(&system, hit.order));
/// ```
pub fn detect_free_basis<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    tie_break: WeightedTieBreak,
    limits: &DetectorLimits,
) -> Detection<N> {
    let mut statistics = DetectionStatistics::default();
    let outcome = search(system, tie_break, limits, &mut statistics);
    Detection {
        outcome,
        statistics,
    }
}

fn search<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    tie_break: WeightedTieBreak,
    limits: &DetectorLimits,
    statistics: &mut DetectionStatistics,
) -> Result<FreeBasis<N>, DetectionMiss> {
    if system.is_empty() {
        return Err(DetectionMiss::Empty);
    }
    if system.iter().any(MultivariatePolynomial::is_zero) {
        return Err(DetectionMiss::ZeroGenerator);
    }
    if system.iter().any(MultivariatePolynomial::is_constant) {
        return Err(DetectionMiss::ConstantGenerator);
    }
    if system.len() > N {
        return Err(DetectionMiss::TooManyGenerators {
            generators: system.len(),
            variables: N,
        });
    }

    // The plain graded order, ties included, before any search.
    let graded = match tie_break {
        WeightedTieBreak::ReverseLexicographic => MonomialOrder::GradedReverseLexicographic,
        WeightedTieBreak::Lexicographic => MonomialOrder::GradedLexicographic,
        WeightedTieBreak::LastVariableFirst => weighted_order(&[1; N], tie_break),
    };
    if leading_monomials_are_pairwise_coprime(system, graded) {
        statistics.fast_path = true;
        return certify(system, vec![1; N], tie_break, None);
    }

    let supports: Vec<Vec<Monomial<N>>> = system
        .iter()
        .map(|g| {
            let mut s: Vec<Monomial<N>> = g.terms().keys().copied().collect();
            s.sort_unstable_by(|a, b| b.exponents().cmp(a.exponents()));
            s
        })
        .collect();
    let mut work = LpWork::default();
    let mut solve = |constraints: &[Constraint], statistics: &mut DetectionStatistics| {
        if statistics.lp_solves >= limits.max_lp_solves {
            return Err(DetectionMiss::BudgetExhausted);
        }
        statistics.lp_solves += 1;
        let result = smallest_weights(constraints, N, &mut work);
        statistics.lp_pivots = work.pivots;
        result.map_err(DetectionMiss::Arithmetic)
    };

    // A monomial dividing another of its generator is never a leading monomial.
    let maximal: Vec<Vec<Monomial<N>>> = supports
        .iter()
        .map(|support| {
            let mut ranked: Vec<Monomial<N>> = support
                .iter()
                .filter(|m| !support.iter().any(|o| o != *m && divides(m, o)))
                .copied()
                .collect();
            ranked.sort_by_key(|m| {
                let vars = m.exponents().iter().filter(|&&e| e > 0).count();
                (vars, std::cmp::Reverse(m.degree()))
            });
            ranked
        })
        .collect();
    let mut budget = limits.max_screen_nodes;
    if screen(&maximal, &mut [false; N], &mut budget, statistics) == Some(false) {
        return Err(DetectionMiss::NoCertificate);
    }

    let mut candidates: Vec<Vec<Candidate<N>>> = Vec::with_capacity(system.len());
    for (support, ranked) in supports.iter().zip(maximal) {
        let mut kept = Vec::new();
        for m in ranked {
            if kept.len() == limits.candidates_per_generator {
                break;
            }
            let constraints = beats(&m, support);
            if solve(&constraints, statistics)?.is_some() {
                kept.push(Candidate {
                    monomial: m,
                    constraints,
                });
            }
        }
        if kept.is_empty() {
            return Err(DetectionMiss::NoCertificate);
        }
        statistics.candidates += kept.len();
        candidates.push(kept);
    }

    // Most constrained generator first.
    let mut visit: Vec<usize> = (0..system.len()).collect();
    visit.sort_by_key(|&i| candidates[i].len());
    let mut chosen: Vec<Option<Monomial<N>>> = vec![None; system.len()];
    let found = extend(
        &visit,
        &candidates,
        &mut [false; N],
        &mut Vec::new(),
        &mut chosen,
        &mut solve,
        statistics,
    )?;
    match found {
        Some(weights) => certify(system, weights, tie_break, Some(&chosen)),
        None => Err(DetectionMiss::NoCertificate),
    }
}

/// Whether some choice of one monomial per generator has pairwise disjoint supports; `None` if the
/// node budget ran out first. Necessary for a hit, and free of linear programs.
fn screen<const N: usize>(
    maximal: &[Vec<Monomial<N>>],
    used: &mut [bool; N],
    budget: &mut usize,
    statistics: &mut DetectionStatistics,
) -> Option<bool> {
    // Most constrained remaining generator first: the one with fewest disjoint candidates.
    let free =
        |m: &Monomial<N>, used: &[bool; N]| (0..N).all(|k| m.exponents()[k] == 0 || !used[k]);
    let Some((i, _)) = maximal
        .iter()
        .enumerate()
        .map(|(i, c)| (i, c.iter().filter(|m| free(m, used)).count()))
        .min_by_key(|&(_, count)| count)
    else {
        return Some(true);
    };
    let (rest, current) = {
        let mut rest = maximal.to_vec();
        let current = rest.remove(i);
        (rest, current)
    };
    let mut undecided = false;
    let open: Vec<Monomial<N>> = current.into_iter().filter(|m| free(m, used)).collect();
    for m in &open {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        statistics.screen_nodes += 1;
        let marked: Vec<usize> = (0..N).filter(|&k| m.exponents()[k] > 0).collect();
        for &k in &marked {
            used[k] = true;
        }
        let found = screen(&rest, used, budget, statistics);
        for &k in &marked {
            used[k] = false;
        }
        match found {
            Some(true) => return Some(true),
            None => undecided = true,
            Some(false) => {}
        }
    }
    if undecided {
        None
    } else {
        Some(false)
    }
}

struct Candidate<const N: usize> {
    monomial: Monomial<N>,
    constraints: Vec<Constraint>,
}

/// Depth-first over coprime assignments, pruning on infeasible partial constraint sets.
fn extend<const N: usize>(
    visit: &[usize],
    candidates: &[Vec<Candidate<N>>],
    used: &mut [bool; N],
    constraints: &mut Vec<Constraint>,
    chosen: &mut [Option<Monomial<N>>],
    solve: &mut impl FnMut(
        &[Constraint],
        &mut DetectionStatistics,
    ) -> Result<Option<Vec<u32>>, DetectionMiss>,
    statistics: &mut DetectionStatistics,
) -> Result<Option<Vec<u32>>, DetectionMiss> {
    let Some((&i, rest)) = visit.split_first() else {
        return solve(constraints, statistics);
    };
    for candidate in &candidates[i] {
        let e = candidate.monomial.exponents();
        if (0..N).any(|k| e[k] > 0 && used[k]) {
            continue;
        }
        statistics.nodes += 1;
        let mark = constraints.len();
        constraints.extend(candidate.constraints.iter().cloned());
        // A single candidate is feasible by construction; the leaf solves either way.
        let feasible = rest.is_empty() || mark == 0 || solve(constraints, statistics)?.is_some();
        if feasible {
            for k in 0..N {
                if e[k] > 0 {
                    used[k] = true;
                }
            }
            chosen[i] = Some(candidate.monomial);
            if let Some(w) = extend(
                rest,
                candidates,
                used,
                constraints,
                chosen,
                solve,
                statistics,
            )? {
                return Ok(Some(w));
            }
            chosen[i] = None;
            for k in 0..N {
                if e[k] > 0 {
                    used[k] = false;
                }
            }
        }
        constraints.truncate(mark);
    }
    Ok(None)
}

/// Re-check a found weight vector against the polynomials themselves.
fn certify<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    weights: Vec<u32>,
    tie_break: WeightedTieBreak,
    chosen: Option<&[Option<Monomial<N>>]>,
) -> Result<FreeBasis<N>, DetectionMiss> {
    let order = weighted_order(&weights, tie_break);
    let leading: Vec<Monomial<N>> = system.iter().map(|g| g.leading_monomial(order)).collect();
    let agrees = chosen.is_none_or(|c| c.iter().zip(&leading).all(|(c, l)| *c == Some(*l)));
    if !agrees || !leading_monomials_are_pairwise_coprime(system, order) {
        debug_assert!(false, "weights {weights:?} failed their own certificate");
        return Err(DetectionMiss::NoCertificate);
    }
    Ok(FreeBasis {
        weights,
        order,
        leading,
    })
}

/// Interned for the process lifetime: one small leak per hit, or per call under
/// [`WeightedTieBreak::LastVariableFirst`], whose all-ones order has no built-in equivalent.
fn weighted_order(weights: &[u32], tie_break: WeightedTieBreak) -> MonomialOrder {
    // Weights come from the solver or are all ones, so they are positive.
    MonomialOrder::weighted(weights, tie_break).expect("positive weights")
}

/// `w·m > w·m'` for every other monomial of the support, minus those `m` already dominates.
fn beats<const N: usize>(m: &Monomial<N>, support: &[Monomial<N>]) -> Vec<Constraint> {
    let mut seen = HashSet::new();
    support
        .iter()
        .filter(|o| *o != m && !divides(o, m))
        .map(|o| difference(m, o))
        .filter(|d| seen.insert(d.clone()))
        .map(Constraint::Positive)
        .collect()
}

fn difference<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> Vec<i64> {
    (0..N)
        .map(|k| a.exponents()[k] as i64 - b.exponents()[k] as i64)
        .collect()
}

fn divides<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> bool {
    (0..N).all(|k| a.exponents()[k] <= b.exponents()[k])
}

/// The positive weights of least sum (up to scaling) under which every generator is
/// weighted-homogeneous, or `None` if there are none.
///
/// All ones exactly when the system is homogeneous. A generator with a constant term and any other
/// term admits no positive weights.
///
/// # Errors
/// [`WeightSearchError`] if exact arithmetic overflowed.
pub fn weighted_homogeneous_weights<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
) -> Result<Option<Vec<u32>>, WeightSearchError> {
    let mut seen = HashSet::new();
    let mut constraints = Vec::new();
    for g in system {
        let mut support = g.terms().keys();
        let Some(first) = support.next() else {
            continue;
        };
        for m in support {
            let d = difference(m, first);
            if seen.insert(d.clone()) {
                constraints.push(Constraint::Zero(d));
            }
        }
    }
    smallest_weights(&constraints, N, &mut LpWork::default())
}

#[cfg(test)]
mod tests {
    use super::{detect_free_basis, weighted_homogeneous_weights, DetectionMiss, DetectorLimits};
    use crate::{
        fields::Zp13,
        grobner::{is_grobner_basis, leading_monomials_are_pairwise_coprime},
        FiniteField, Monomial, MonomialOrder, MultivariatePolynomial, WeightedTieBreak,
    };

    type F = Zp13;
    const REVLEX: WeightedTieBreak = WeightedTieBreak::ReverseLexicographic;

    fn system<const N: usize>(text: &[&str], vars: [&str; N]) -> Vec<MultivariatePolynomial<N, F>> {
        text.iter()
            .map(|s| MultivariatePolynomial::parse(s, vars).unwrap())
            .collect()
    }

    #[test]
    fn grevlex_coprime_input_takes_the_fast_path() {
        let f = system(&["x^2 + y", "y^2 + x"], ["x", "y"]);
        let d = detect_free_basis(&f, REVLEX, &DetectorLimits::default());
        let hit = d.outcome.unwrap();
        assert_eq!(hit.weights, vec![1, 1]);
        assert!(d.statistics.fast_path);
        assert_eq!(d.statistics.lp_solves, 0);
        assert_eq!(
            hit.leading,
            vec![Monomial::new(&[2, 0]), Monomial::new(&[0, 2])]
        );
    }

    #[test]
    fn unequal_weights_make_a_basis_grevlex_does_not() {
        let f = system(&["y^2 - x^3", "x^2 + y"], ["x", "y"]);
        assert!(!leading_monomials_are_pairwise_coprime(
            &f,
            MonomialOrder::GradedReverseLexicographic
        ));
        for tie_break in [
            WeightedTieBreak::Lexicographic,
            WeightedTieBreak::ReverseLexicographic,
            WeightedTieBreak::LastVariableFirst,
        ] {
            let d = detect_free_basis(&f, tie_break, &DetectorLimits::default());
            let hit = d.outcome.unwrap();
            assert!(!d.statistics.fast_path);
            assert_eq!(
                hit.leading,
                vec![Monomial::new(&[0, 2]), Monomial::new(&[2, 0])]
            );
            // 2·w_y > 3·w_x and 2·w_x > w_y.
            let (x, y) = (hit.weights[0], hit.weights[1]);
            assert!(2 * y > 3 * x && 2 * x > y, "{:?}", hit.weights);
            assert!(is_grobner_basis(&f, hit.order));
        }
    }

    #[test]
    fn more_generators_than_variables_are_refused_without_search() {
        let f = system(&["x^2 + y", "y^2 + x", "x*y - 1"], ["x", "y"]);
        let d = detect_free_basis(&f, REVLEX, &DetectorLimits::default());
        assert_eq!(
            d.outcome,
            Err(DetectionMiss::TooManyGenerators {
                generators: 3,
                variables: 2
            })
        );
        assert_eq!(d.statistics.lp_solves, 0);
    }

    #[test]
    fn shared_variables_in_every_choice_are_a_miss() {
        // x*y is g1's only achievable leading monomial and meets both of g2's.
        let f = system(&["x*y + 1", "x + y"], ["x", "y"]);
        let d = detect_free_basis(&f, REVLEX, &DetectorLimits::default());
        assert_eq!(d.outcome, Err(DetectionMiss::NoCertificate));
        // Decided by the combinatorial screen, before any linear program.
        assert_eq!(d.statistics.lp_solves, 0);
        assert!(d.statistics.screen_nodes > 0);
    }

    #[test]
    fn infeasible_weights_on_every_coprime_choice_are_a_miss() {
        // Coprime choices: (x^2, y^2) needs w_x > w_y and 2w_y > 3w_x.
        let f = system(&["x^2 + x*y + y", "x^3 + y^2"], ["x", "y"]);
        let d = detect_free_basis(&f, REVLEX, &DetectorLimits::default());
        assert_eq!(d.outcome, Err(DetectionMiss::NoCertificate));
        assert!(d.statistics.lp_solves > 0);
    }

    #[test]
    fn the_budget_is_honoured() {
        let f = system(&["y^2 - x^3", "x^2 + y"], ["x", "y"]);
        let limits = DetectorLimits {
            max_lp_solves: 1,
            ..DetectorLimits::default()
        };
        let d = detect_free_basis(&f, REVLEX, &limits);
        assert_eq!(d.outcome, Err(DetectionMiss::BudgetExhausted));
        assert_eq!(d.statistics.lp_solves, 1);
    }

    #[test]
    fn degenerate_inputs_are_named() {
        let limits = DetectorLimits::default();
        let empty: Vec<MultivariatePolynomial<2, F>> = Vec::new();
        assert_eq!(
            detect_free_basis(&empty, REVLEX, &limits).outcome,
            Err(DetectionMiss::Empty)
        );
        let f = system(&["x + 1", "0"], ["x", "y"]);
        assert_eq!(
            detect_free_basis(&f, REVLEX, &limits).outcome,
            Err(DetectionMiss::ZeroGenerator)
        );
        let f = system(&["x + 1", "3"], ["x", "y"]);
        assert_eq!(
            detect_free_basis(&f, REVLEX, &limits).outcome,
            Err(DetectionMiss::ConstantGenerator)
        );
    }

    /// Soundness: every hit on random input is a Gröbner basis by the definition.
    #[test]
    fn random_hits_are_grobner_bases() {
        use rand::{rngs::StdRng, Rng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(1192);
        let (mut hits, mut weighted_hits, mut misses) = (0, 0, 0);
        for _ in 0..400 {
            let generators = rng.gen_range(2..=3);
            let f: Vec<MultivariatePolynomial<3, F>> = (0..generators)
                .map(|_| {
                    // A pure power, so that coprime choices exist often enough to exercise hits.
                    let mut terms = vec![(
                        Monomial::univariate(rng.gen_range(0..3), rng.gen_range(1..=3)),
                        F::new(1),
                    )];
                    terms.extend((0..rng.gen_range(1..=3)).map(|_| {
                        let e: [u32; 3] = std::array::from_fn(|_| rng.gen_range(0..=3));
                        (Monomial::new(&e), F::new(rng.gen_range(1..13u64)))
                    }));
                    MultivariatePolynomial::new(&terms)
                })
                .collect();
            let tie_break = [
                WeightedTieBreak::Lexicographic,
                WeightedTieBreak::ReverseLexicographic,
                WeightedTieBreak::LastVariableFirst,
            ][rng.gen_range(0..3)];
            let d = detect_free_basis(&f, tie_break, &DetectorLimits::default());
            match d.outcome {
                Ok(hit) => {
                    assert!(
                        is_grobner_basis(&f, hit.order),
                        "{f:?} under {:?}",
                        hit.weights
                    );
                    let leading: Vec<_> = f.iter().map(|g| g.leading_monomial(hit.order)).collect();
                    assert_eq!(leading, hit.leading);
                    hits += 1;
                    if hit.weights.iter().any(|&w| w != 1) {
                        weighted_hits += 1;
                    }
                }
                Err(_) => misses += 1,
            }
        }
        assert!(
            weighted_hits > 10 && misses > 10,
            "{hits} hits, {weighted_hits} weighted, {misses} misses"
        );
    }

    #[test]
    fn weighted_homogeneity_finds_the_grading() {
        let f = system(&["x^3 - y", "y^2 - x^3*y + z"], ["x", "y", "z"]);
        assert_eq!(weighted_homogeneous_weights(&f), Ok(Some(vec![1, 3, 6])));
        let f = system(&["x^2 + x*y", "y^2"], ["x", "y"]);
        assert_eq!(weighted_homogeneous_weights(&f), Ok(Some(vec![1, 1])));
        let f = system(&["x^2 + y - 1"], ["x", "y"]);
        assert_eq!(weighted_homogeneous_weights(&f), Ok(None));
    }
}
