//! Adversarial harness for Hilbert-count acceptance of randomized zero tests (#1038).
//!
//! The lemmas these tests exercise, and the conditions under which the acceptance rule is sound,
//! are in `docs/research/hilbert-count-acceptance.md`. In short: a degree-by-degree computation
//! that keeps only elements of `I` has `C(e) ≥ H_I(e)` for every degree, where `C(e)` counts the
//! degree-`e` monomials outside its leading-monomial ideal, and for homogeneous generators of
//! degrees `d_i` the Hilbert function `H_I` is lexicographically at least
//! `S = Π(1 − t^{d_i}) / (1 − t)^n`. So `C(e) = S(e)` at every degree up to `d` certifies the
//! computation through `d`, whether or not the input was known to be regular.
//!
//! The toy engine below is F4-shaped, not F4: degree `e`'s rows are `x_j · b` for the previous
//! degree's echelon basis `b`, plus the degree-`e` generators; one row per leading monomial is a
//! reducer and is always kept exactly, and only the remaining "pair" rows go through the
//! zero-test policy under test. It is small and dense so that it can be run exhaustively over
//! GF(2), GF(3) and GF(31), where random linear combinations fail often.

use std::collections::HashMap;

use rand::{rngs::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::{Zp2, Zp31, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, eco, katsura},
        f4,
        f4::MonicBasis,
        f4_observed, top_forms, BatchObserver, CriticalPair, F4Options, HilbertSeries,
        SemiregularSeries,
    },
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

// ------------------------------------------------------------------------------------------------
// The acceptance rule, which is the object under test.
// ------------------------------------------------------------------------------------------------

/// `Π(1 − t^{d_i}) / (1 − t)^n`, untruncated, through `up_to`.
fn regular_series(variables: usize, degrees: &[usize], up_to: usize) -> Vec<i128> {
    let mut numerator = vec![0i128; up_to + 1];
    numerator[0] = 1;
    for &d in degrees {
        for k in (0..=up_to).rev() {
            if k >= d {
                numerator[k] -= numerator[k - d];
            }
        }
    }
    // Divide by (1 − t) once per variable: a running prefix sum.
    for _ in 0..variables {
        for k in 1..=up_to {
            numerator[k] += numerator[k - 1];
        }
    }
    numerator
}

/// The highest degree `d` such that the counts certify every degree `≤ d`, or `None`.
///
/// Degree `e` passes if `C(e) = S(e)` and every lower degree passed, or if `C(e) = 0`, which
/// needs nothing: `0 ≤ H_I(e) ≤ C(e)`. A zero count stays zero at every higher degree, so it
/// certifies all of them, and the result is then the last degree supplied.
fn certified_through(counts: &[i128], series: &[i128]) -> Option<usize> {
    for (e, (&c, &s)) in counts.iter().zip(series).enumerate() {
        if c == 0 {
            return Some(counts.len() - 1);
        }
        if c != s {
            return e.checked_sub(1);
        }
    }
    counts.len().checked_sub(1)
}

// ------------------------------------------------------------------------------------------------
// A dense, homogeneous, F4-shaped toy engine over GF(p).
// ------------------------------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct Gf(u64);

impl Gf {
    fn add(self, a: u64, b: u64) -> u64 {
        (a + b) % self.0
    }
    fn sub(self, a: u64, b: u64) -> u64 {
        (a + self.0 - b) % self.0
    }
    fn mul(self, a: u64, b: u64) -> u64 {
        a * b % self.0
    }
    fn inv(self, a: u64) -> u64 {
        assert_ne!(a, 0);
        let (mut base, mut exponent, mut result) = (a, self.0 - 2, 1);
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = self.mul(result, base);
            }
            base = self.mul(base, base);
            exponent >>= 1;
        }
        result
    }
}

/// The degree-`e` monomials in `n` variables, largest first under grevlex.
struct Space {
    monomials: Vec<Vec<u32>>,
    index: HashMap<Vec<u32>, usize>,
}

fn grevlex_greater(a: &[u32], b: &[u32]) -> bool {
    // Same total degree throughout: the larger has the smaller exponent at the last difference.
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i] < b[i];
        }
    }
    false
}

impl Space {
    fn new(n: usize, e: usize) -> Self {
        fn fill(n: usize, left: u32, prefix: &mut Vec<u32>, out: &mut Vec<Vec<u32>>) {
            if prefix.len() == n - 1 {
                prefix.push(left);
                out.push(prefix.clone());
                prefix.pop();
                return;
            }
            for a in 0..=left {
                prefix.push(a);
                fill(n, left - a, prefix, out);
                prefix.pop();
            }
        }
        let mut monomials = Vec::new();
        fill(n, e as u32, &mut Vec::new(), &mut monomials);
        monomials.sort_by(|a, b| {
            if grevlex_greater(a, b) {
                std::cmp::Ordering::Less
            } else if grevlex_greater(b, a) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        });
        let index = monomials
            .iter()
            .enumerate()
            .map(|(i, m)| (m.clone(), i))
            .collect();
        Self { monomials, index }
    }
    fn len(&self) -> usize {
        self.monomials.len()
    }
}

/// A homogeneous polynomial as `(exponents, coefficient)` terms.
type Poly = Vec<(Vec<u32>, u64)>;

/// Row-echelon form with distinct, normalized pivots: the leading column of each row.
#[derive(Clone, Default)]
struct Echelon {
    rows: Vec<Vec<u64>>,
    pivot: HashMap<usize, usize>,
}

impl Echelon {
    fn reduce(&self, field: Gf, mut v: Vec<u64>) -> Vec<u64> {
        for col in 0..v.len() {
            if v[col] == 0 {
                continue;
            }
            if let Some(&r) = self.pivot.get(&col) {
                let c = v[col];
                for (x, y) in v.iter_mut().zip(&self.rows[r]) {
                    *x = field.sub(*x, field.mul(c, *y));
                }
            }
        }
        v
    }
    /// Reduce `v` and keep it if it is not zero. Returns whether it was kept.
    fn insert(&mut self, field: Gf, v: Vec<u64>) -> bool {
        let mut v = self.reduce(field, v);
        let Some(lead) = v.iter().position(|&x| x != 0) else {
            return false;
        };
        let scale = field.inv(v[lead]);
        for x in &mut v {
            *x = field.mul(*x, scale);
        }
        self.pivot.insert(lead, self.rows.len());
        self.rows.push(v);
        true
    }
    /// Install `v` as a pivot row as it stands. `v`'s leading column must be new.
    fn install(&mut self, field: Gf, mut v: Vec<u64>) {
        let lead = v
            .iter()
            .position(|&x| x != 0)
            .expect("a reducer is not zero");
        assert!(
            !self.pivot.contains_key(&lead),
            "reducers have distinct leads"
        );
        let scale = field.inv(v[lead]);
        for x in &mut v {
            *x = field.mul(*x, scale);
        }
        self.pivot.insert(lead, self.rows.len());
        self.rows.push(v);
    }
    fn rank(&self) -> usize {
        self.rows.len()
    }
    fn drop_pivot(&mut self, which: usize) {
        let row = self.rows.remove(which);
        let lead = row.iter().position(|&x| x != 0).unwrap();
        self.pivot.remove(&lead);
        for r in self.pivot.values_mut() {
            if *r > which {
                *r -= 1;
            }
        }
    }
}

/// How a degree's pair rows are decided.
#[derive(Clone, Copy, Debug)]
enum Policy {
    /// Every pair row is reduced: the deterministic engine.
    Exact,
    /// Only `combos` random linear combinations of the pair rows are reduced, with coefficients
    /// uniform over the field (zero included), and every pair row is then declared zero. This is
    /// grobx's mechanism with a deliberately short supply of combinations.
    Random { combos: usize, seed: u64 },
    /// Exact, then `count` of the degree's new elements are thrown away: a missed pivot that no
    /// randomness produced, which the check must reject.
    Drop { degree: usize, count: usize },
    /// As `Random` at one degree only, exact elsewhere; then the degree is redone exactly when
    /// its count does not match. The Las Vegas retry of the note's §5.
    RandomWithRetry {
        degree: usize,
        combos: usize,
        seed: u64,
    },
}

struct Run {
    /// `C(e)`, the degree-`e` standard-monomial count of the computed leading-monomial ideal.
    counts: Vec<i128>,
    /// The computed degree-`e` subspace of `I_e`.
    spaces: Vec<Echelon>,
    /// Whether any degree's randomized test reduced fewer rows than it had.
    shortcut: bool,
}

fn to_row(space: &Space, poly: &Poly, field: Gf) -> Vec<u64> {
    let mut row = vec![0; space.len()];
    for (m, c) in poly {
        let i = space.index[m];
        row[i] = field.add(row[i], *c % field.0);
    }
    row
}

fn times_variable(from: &Space, to: &Space, row: &[u64], j: usize) -> Vec<u64> {
    let mut out = vec![0; to.len()];
    for (i, &c) in row.iter().enumerate() {
        if c != 0 {
            let mut m = from.monomials[i].clone();
            m[j] += 1;
            out[to.index[&m]] = c;
        }
    }
    out
}

fn run(n: usize, p: u64, system: &[Poly], max_degree: usize, policy: Policy) -> Run {
    let field = Gf(p);
    let spaces: Vec<Space> = (0..=max_degree).map(|e| Space::new(n, e)).collect();
    let degree_of = |f: &Poly| f[0].0.iter().sum::<u32>() as usize;
    let mut computed: Vec<Echelon> = Vec::new();
    let mut counts = Vec::new();
    let mut shortcut = false;

    for e in 0..=max_degree {
        // Rows: x_j times the previous degree's basis, then the degree-e generators.
        let mut multiples = Vec::new();
        if e > 0 {
            for row in &computed[e - 1].rows {
                for j in 0..n {
                    multiples.push(times_variable(&spaces[e - 1], &spaces[e], row, j));
                }
            }
        }
        let generators: Vec<Vec<u64>> = system
            .iter()
            .filter(|f| !f.is_empty() && degree_of(f) == e)
            .map(|f| to_row(&spaces[e], f, field))
            .filter(|r| r.iter().any(|&x| x != 0))
            .collect();

        // One reducer per leading monomial among the multiples; everything else is a pair row.
        let mut reducers = Echelon::default();
        let mut pairs = Vec::new();
        for row in multiples {
            let lead = row.iter().position(|&x| x != 0).unwrap();
            if reducers.pivot.contains_key(&lead) {
                pairs.push(row);
            } else {
                reducers.install(field, row);
            }
        }
        pairs.extend(generators);

        let decide = |policy: Policy, shortcut: &mut bool| -> Echelon {
            let mut basis = reducers.clone();
            match policy {
                Policy::Random { combos, seed }
                | Policy::RandomWithRetry {
                    combos,
                    seed,
                    degree: _,
                } => {
                    let mut rng = StdRng::seed_from_u64(seed ^ (e as u64).wrapping_mul(0x9E37));
                    let take = combos.min(pairs.len());
                    if take < pairs.len() {
                        *shortcut = true;
                    }
                    for _ in 0..take {
                        let mut v = vec![0; spaces[e].len()];
                        for row in &pairs {
                            let c = rng.gen_range(0..p);
                            for (x, y) in v.iter_mut().zip(row) {
                                *x = field.add(*x, field.mul(c, *y));
                            }
                        }
                        basis.insert(field, v);
                    }
                }
                _ => {
                    for row in &pairs {
                        basis.insert(field, row.clone());
                    }
                }
            }
            basis
        };

        let mut basis = match policy {
            Policy::RandomWithRetry { degree, .. } if degree != e => {
                decide(Policy::Exact, &mut shortcut)
            }
            _ => decide(policy, &mut shortcut),
        };
        if let Policy::Drop { degree, count } = policy {
            if degree == e {
                let new = basis.rank() - reducers.rank();
                for _ in 0..count.min(new) {
                    basis.drop_pivot(basis.rank() - 1);
                }
            }
        }

        let mut count = spaces[e].len() as i128 - basis.rank() as i128;
        if let Policy::RandomWithRetry { degree, .. } = policy {
            let series = regular_series(n, &system_degrees(system), e);
            let lower_passed =
                certified_through(&counts, &series[..e]).map_or(e == 0, |d| d + 1 >= e);
            if degree == e && lower_passed && count != 0 && count != series[e] {
                basis = decide(Policy::Exact, &mut shortcut);
                count = spaces[e].len() as i128 - basis.rank() as i128;
            }
        }
        counts.push(count);
        computed.push(basis);
    }

    Run {
        counts,
        spaces: computed,
        shortcut,
    }
}

fn system_degrees(system: &[Poly]) -> Vec<usize> {
    system
        .iter()
        .filter(|f| !f.is_empty())
        .map(|f| f[0].0.iter().sum::<u32>() as usize)
        .collect()
}

// ------------------------------------------------------------------------------------------------
// Systems: random and deliberately structured, so that both regular and non-regular inputs occur.
// ------------------------------------------------------------------------------------------------

fn random_form(rng: &mut StdRng, n: usize, degree: usize, terms: usize, p: u64) -> Poly {
    let space = Space::new(n, degree);
    let mut poly: Poly = Vec::new();
    for _ in 0..terms {
        let m = space.monomials[rng.gen_range(0..space.len())].clone();
        if poly.iter().all(|(x, _)| *x != m) {
            poly.push((m, rng.gen_range(1..p)));
        }
    }
    poly
}

fn multiply(a: &Poly, b: &Poly, p: u64) -> Poly {
    let mut out: HashMap<Vec<u32>, u64> = HashMap::new();
    for (ma, ca) in a {
        for (mb, cb) in b {
            let m: Vec<u32> = ma.iter().zip(mb).map(|(x, y)| x + y).collect();
            let c = out.entry(m).or_insert(0);
            *c = (*c + ca * cb) % p;
        }
    }
    let mut poly: Poly = out.into_iter().filter(|(_, c)| *c != 0).collect();
    poly.sort();
    poly
}

fn variable(n: usize, j: usize) -> Poly {
    let mut m = vec![0; n];
    m[j] = 1;
    vec![(m, 1)]
}

/// A labelled family of systems over GF(p) in `n` variables.
fn systems(n: usize, p: u64, seed: u64) -> Vec<(String, Vec<Poly>)> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut out = Vec::new();
    let dense = Space::new(n, 2).len();
    for m in 1..=n + 2 {
        for sparse in [2, dense] {
            let system = (0..m)
                .map(|_| random_form(&mut rng, n, 2, sparse, p))
                .filter(|f| !f.is_empty())
                .collect();
            out.push((format!("random m={m} terms={sparse}"), system));
        }
    }
    let mixed = vec![
        random_form(&mut rng, n, 1, n, p),
        random_form(&mut rng, n, 2, dense, p),
        random_form(&mut rng, n, 3, 4, p),
    ];
    out.push(("degrees 1,2,3".into(), mixed));
    let f = random_form(&mut rng, n, 2, dense, p);
    out.push(("repeated generator".into(), vec![f.clone(), f.clone()]));
    out.push((
        "multiple of a generator".into(),
        vec![f.clone(), multiply(&variable(n, 0), &f, p)],
    ));
    let l = random_form(&mut rng, n, 1, n, p);
    let g1 = random_form(&mut rng, n, 1, n, p);
    let g2 = random_form(&mut rng, n, 1, n, p);
    out.push((
        "common linear factor".into(),
        vec![multiply(&l, &g1, p), multiply(&l, &g2, p)],
    ));
    let mut x2 = vec![0; n];
    x2[0] = 2;
    let mut xy = vec![0; n];
    xy[0] = 1;
    xy[1] = 1;
    out.push((
        "monomials x^2, xy".into(),
        vec![vec![(x2, 1)], vec![(xy, 1)]],
    ));
    let squares = (0..n)
        .map(|j| {
            let mut m = vec![0; n];
            m[j] = 2;
            let mut f = random_form(&mut rng, n, 2, 2, p);
            f.retain(|(x, _)| *x != m);
            f.push((m, 1));
            f
        })
        .collect();
    out.push(("perturbed squares (regular)".into(), squares));
    out
}

fn degree_bound(n: usize) -> usize {
    match n {
        2 => 7,
        3 => 6,
        _ => 5,
    }
}

const FIELDS: [u64; 3] = [2, 3, 31];

// ------------------------------------------------------------------------------------------------
// Lemma 2 of the note: H_I is lexicographically at least S.
// ------------------------------------------------------------------------------------------------

/// The counterexample search for the lexicographic lower bound, over every system the harness
/// builds. Exact runs compute `H_I`, so each one is a test of the lemma.
#[test]
fn hilbert_function_is_lexicographically_at_least_the_regular_series() {
    let (mut equal, mut above) = (0, 0);
    for p in FIELDS {
        for n in 2..=4 {
            for seed in 0..3 {
                for (label, system) in systems(n, p, seed) {
                    let d = degree_bound(n);
                    let exact = run(n, p, &system, d, Policy::Exact).counts;
                    let series = regular_series(n, &system_degrees(&system), d);
                    match exact.iter().zip(&series).position(|(h, s)| h != s) {
                        None => equal += 1,
                        Some(e) => {
                            assert!(
                                exact[e] > series[e],
                                "GF({p}), n={n}, {label}: H({e}) = {} < S({e}) = {} at the first \
                                 difference",
                                exact[e],
                                series[e]
                            );
                            above += 1;
                        }
                    }
                }
            }
        }
    }
    // The search must have seen both sides of the lemma, or it tested nothing.
    assert!(equal > 20 && above > 20, "equal {equal}, above {above}");
}

// ------------------------------------------------------------------------------------------------
// Theorem 1 of the note: a certified degree is a correct degree.
// ------------------------------------------------------------------------------------------------

fn assert_sound(n: usize, p: u64, system: &[Poly], label: &str, policy: Policy) -> (bool, bool) {
    let d = degree_bound(n);
    let exact = run(n, p, system, d, Policy::Exact);
    let trial = run(n, p, system, d, policy);
    let series = regular_series(n, &system_degrees(system), d);
    let field = Gf(p);

    // The harness's own precondition: everything kept is in the ideal.
    for e in 0..=d {
        for row in &trial.spaces[e].rows {
            assert!(
                exact.spaces[e]
                    .reduce(field, row.clone())
                    .iter()
                    .all(|&x| x == 0),
                "the engine kept an element outside I"
            );
        }
    }
    let wrong = (0..=d).any(|e| trial.counts[e] != exact.counts[e]);
    if let Some(through) = certified_through(&trial.counts, &series) {
        for e in 0..=through {
            assert_eq!(
                trial.counts[e], exact.counts[e],
                "GF({p}), n={n}, {label}, {policy:?}: degree {e} certified with C = {} but \
                 H_I = {}",
                trial.counts[e], exact.counts[e]
            );
        }
    }
    (
        wrong,
        trial.shortcut && certified_through(&trial.counts, &series) == Some(d),
    )
}

/// Short supplies of random combinations, over fields where they collapse often. Every degree the
/// rule certifies must be exactly right, and the adversary must actually have produced wrong
/// states for the rule to reject.
#[test]
fn count_acceptance_never_certifies_a_short_random_reduction() {
    let (mut rejected_wrong, mut certified_shortcuts) = (0, 0);
    for p in FIELDS {
        for n in 2..=4 {
            for (label, system) in systems(n, p, 7) {
                for combos in [0, 1, 2, 3, 5, 8, 13, usize::MAX] {
                    for seed in 0..3 {
                        let (wrong, saved) =
                            assert_sound(n, p, &system, &label, Policy::Random { combos, seed });
                        rejected_wrong += usize::from(wrong);
                        certified_shortcuts += usize::from(saved);
                    }
                }
            }
        }
    }
    assert!(
        rejected_wrong > 100,
        "the adversary produced {rejected_wrong} wrong runs"
    );
    assert!(
        certified_shortcuts > 10,
        "only {certified_shortcuts} runs saved work and were certified to the end"
    );
}

/// Deliberately dropped pivots at every degree: never certified at or above that degree.
#[test]
fn count_acceptance_rejects_every_dropped_pivot() {
    for p in FIELDS {
        for n in 2..=4 {
            for (label, system) in systems(n, p, 11) {
                let d = degree_bound(n);
                let exact = run(n, p, &system, d, Policy::Exact);
                let series = regular_series(n, &system_degrees(&system), d);
                for degree in 0..=d {
                    let trial = run(n, p, &system, d, Policy::Drop { degree, count: 1 });
                    if trial.counts[degree] == exact.counts[degree] {
                        continue; // nothing new at that degree, so nothing to drop
                    }
                    // The deficit is visible exactly where it was made.
                    assert!(trial.counts[degree] > exact.counts[degree]);
                    let through = certified_through(&trial.counts, &series);
                    assert!(
                        !matches!(through, Some(t) if t >= degree),
                        "GF({p}), n={n}, {label}: a pivot dropped at degree {degree} was \
                         certified through {through:?}"
                    );
                    assert_sound(n, p, &system, &label, Policy::Drop { degree, count: 1 });
                }
            }
        }
    }
}

/// A missed pivot can be regenerated at a later degree from other products, so a later degree can
/// count correctly while an earlier one is wrong. The rule stops at the first mismatch; the retry
/// of the failing degree restores certification on regular inputs.
#[test]
fn a_mismatch_is_retried_at_its_own_degree_and_then_certifies() {
    let mut retried = 0;
    for p in FIELDS {
        for n in 2..=4 {
            let d = degree_bound(n);
            for seed in 0..4 {
                for (label, system) in systems(n, p, 100 + seed) {
                    let exact = run(n, p, &system, d, Policy::Exact);
                    let series = regular_series(n, &system_degrees(&system), d);
                    let exact_through = certified_through(&exact.counts, &series);
                    for degree in 1..=d {
                        let policy = Policy::RandomWithRetry {
                            degree,
                            combos: 1,
                            seed,
                        };
                        let trial = run(n, p, &system, d, policy);
                        assert_sound(n, p, &system, &label, policy);
                        // After the retry, the run certifies exactly as far as the exact one.
                        assert_eq!(
                            certified_through(&trial.counts, &series),
                            exact_through,
                            "GF({p}), n={n}, {label}, {policy:?}"
                        );
                        retried += usize::from(
                            trial.counts
                                != run(n, p, &system, d, Policy::Random { combos: 1, seed }).counts,
                        );
                    }
                }
            }
        }
    }
    assert!(retried > 0, "no retry ever changed a run");
}

// ------------------------------------------------------------------------------------------------
// The preconditions are load-bearing.
// ------------------------------------------------------------------------------------------------

/// The one-sided error needs every kept element to be in `I`. A single element from outside it
/// fakes the count.
#[test]
fn an_element_outside_the_ideal_forges_the_count() {
    // I = (x^2) given twice in GF(31)[x, y]: degrees 2, 2, so S = 1, 2, 1, 0, … while
    // H_I = 1, 2, 2, 2, …. The exact count rejects degree 2.
    let p = 31;
    let x2: Poly = vec![(vec![2, 0], 1)];
    let system = vec![x2.clone(), x2];
    let series = regular_series(2, &[2, 2], 4);
    let exact = run(2, p, &system, 4, Policy::Exact);
    assert_eq!(exact.counts, vec![1, 2, 2, 2, 2]);
    assert_eq!(certified_through(&exact.counts, &series), Some(1));

    // Adding y^2, which is not in I, makes C(2) = 1 = S(2) and C(3) = 0: every degree passes.
    let forged = run(
        2,
        p,
        &[vec![(vec![2, 0], 1)], vec![(vec![0, 2], 1)]],
        4,
        Policy::Exact,
    );
    assert_eq!(certified_through(&forged.counts, &series), Some(4));
}

/// On affine input the count can fall *below* the top-form series, so the one-sided error that the
/// homogeneous rule rests on is gone: `(x^2 + y, x^2)` has `C(1) = 1 < S(1) = 2` once its degree
/// fall `y` is found, and `C(1) = 2 = S(1)` at the close of degree 1, before it is.
#[test]
fn affine_degree_falls_break_the_one_sided_error() {
    type F = Zp31;
    let x2 = Monomial::<2>::new(&[2, 0]);
    let y = Monomial::<2>::new(&[0, 1]);
    let system = vec![
        MultivariatePolynomial::<2, F>::new(&[(x2, F::new(1)), (y, F::new(1))]),
        MultivariatePolynomial::<2, F>::new(&[(x2, F::new(1))]),
    ];
    let basis = f4(&system, GREVLEX).unwrap();
    let counts = HilbertSeries::of_basis(&basis, GREVLEX)
        .unwrap()
        .values(3)
        .unwrap();
    let series = regular_series(2, &[2, 2], 3);
    assert_eq!(counts, vec![1, 1, 0, 0]);
    assert_eq!(series, vec![1, 2, 1, 0]);
    assert!(
        counts[1] < series[1],
        "below the series: impossible when homogeneous"
    );

    // Before degree 2 is processed the leading monomials are x^2 and x^2: C(1) = 2 = S(1), and the
    // per-degree rule would certify a degree that is wrong.
    let early = HilbertSeries::of_monomial_ideal(&[x2, x2]).unwrap();
    assert_eq!(early.function(1).unwrap(), series[1]);
}

/// Without the no-fall witness, a full match of the top-form series certifies nothing on affine
/// input. `{x^2, xy, y^3}` lies in `I = (x^2 + y, x^2) = (x^2, y)` and counts `1, 2, 1, 0`, which
/// is `S_top` exactly, yet it is not a Gröbner basis: `y ∈ I` and no leading monomial divides it.
/// Its elements `xy` and `y^3` are multiples of the fall `y`, whose top forms are not in
/// `T = (x^2)`, so Theorem 3's hypothesis rules this basis out.
#[test]
fn affine_count_without_the_no_fall_witness_certifies_a_wrong_basis() {
    type F = Zp31;
    let monomial = |a, b| Monomial::<2>::new(&[a, b]);
    let ideal = f4(
        &[
            MultivariatePolynomial::<2, F>::new(&[
                (monomial(2, 0), F::new(1)),
                (monomial(0, 1), F::new(1)),
            ]),
            MultivariatePolynomial::<2, F>::new(&[(monomial(2, 0), F::new(1))]),
        ],
        GREVLEX,
    )
    .unwrap();
    let wrong: Vec<MultivariatePolynomial<2, F>> = [monomial(2, 0), monomial(1, 1), monomial(0, 3)]
        .into_iter()
        .map(|m| MultivariatePolynomial::new(&[(m, F::new(1))]))
        .collect();
    // I's reduced basis is the monomials {x^2, y}, so a monomial is in I iff one of them divides it.
    let generators: Vec<Monomial<2>> = ideal.iter().map(|g| g.leading_monomial(GREVLEX)).collect();
    assert!(ideal.iter().all(|g| g.terms().len() == 1), "I = (x^2, y)");
    assert_eq!(generators.len(), 2);
    for g in &wrong {
        let m = g.leading_monomial(GREVLEX);
        assert!(
            generators.iter().any(|d| m.checked_div(d).is_some()),
            "{m:?} ∈ I"
        );
    }
    let counts = HilbertSeries::of_basis(&wrong, GREVLEX)
        .unwrap()
        .values(4)
        .unwrap();
    let series = regular_series(2, &[2, 2], 4);
    assert_eq!(
        counts,
        series.iter().map(|s| (*s).max(0)).collect::<Vec<_>>()
    );
    assert_eq!(certified_through(&counts, &series), Some(4));
    let truth = HilbertSeries::of_basis(&ideal, GREVLEX)
        .unwrap()
        .values(4)
        .unwrap();
    assert_ne!(counts, truth, "the count-only check accepted a wrong basis");
}

// ------------------------------------------------------------------------------------------------
// The toy engine is the real Hilbert function.
// ------------------------------------------------------------------------------------------------

fn to_zeebra<const N: usize, F: FiniteField>(poly: &Poly) -> MultivariatePolynomial<N, F> {
    let terms: Vec<(Monomial<N>, F)> = poly
        .iter()
        .map(|(m, c)| (Monomial::new(m), F::new(*c)))
        .collect();
    MultivariatePolynomial::new(&terms)
}

fn agree_with_f4<const N: usize, F: FiniteField>(p: u64) {
    for (label, system) in systems(N, p, 5) {
        let d = degree_bound(N);
        let toy = run(N, p, &system, d, Policy::Exact).counts;
        let zeebra: Vec<MultivariatePolynomial<N, F>> =
            system.iter().map(|f| to_zeebra::<N, F>(f)).collect();
        let basis = f4(&zeebra, GREVLEX).unwrap();
        let exact = HilbertSeries::of_basis(&basis, GREVLEX)
            .unwrap()
            .values(d as u64)
            .unwrap();
        assert_eq!(toy, exact, "GF({p}), n={N}, {label}");
    }
}

#[test]
fn the_toy_engine_computes_the_hilbert_function_zeebra_does() {
    agree_with_f4::<3, Zp2>(2);
    agree_with_f4::<3, Zp31>(31);
    agree_with_f4::<4, Zp31>(31);
}

#[test]
fn the_regular_series_matches_the_crate_expansion() {
    let ours = regular_series(6, &[2, 2, 2, 3], 9);
    let crate_series = SemiregularSeries::new(6, &[2, 2, 2, 3], 9).unwrap();
    for (e, value) in ours.iter().enumerate() {
        assert_eq!(*value, crate_series.raw(e as u64));
    }
}

// ------------------------------------------------------------------------------------------------
// The affine square certificate (the note's Theorem 3) on real F4 runs.
// ------------------------------------------------------------------------------------------------

/// Snapshot of the basis's leading monomials at the start of every batch.
struct Boundaries<const N: usize> {
    batches: Vec<(u64, Vec<Monomial<N>>)>,
}

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for Boundaries<N> {
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]) {
        let degree = pairs.iter().map(|p| p.degree).min().unwrap_or(0);
        self.batches
            .push((degree, basis.leading_monomials().collect()));
    }
}

/// What the affine certificate says about one exact run.
#[derive(Debug, PartialEq, Eq)]
struct AffineVerdict {
    /// A batch of lcm degree `e` produced an element of degree below `e`.
    fell: bool,
    /// Every degree, read at its close, counted `S_top(e)` or zero, and the final basis has no
    /// standard monomials above the last degree `S_top` is positive at.
    counts_match: bool,
}

impl AffineVerdict {
    fn certifies(&self) -> bool {
        !self.fell && self.counts_match
    }
}

fn affine_verdict<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
) -> AffineVerdict {
    let mut observer = Boundaries {
        batches: Vec::new(),
    };
    let (basis, _) = f4_observed(system, GREVLEX, &F4Options::default(), &mut observer).unwrap();
    let degrees: Vec<usize> = system
        .iter()
        .filter(|f| !f.is_zero())
        .map(|f| f.degree() as usize)
        .collect();
    let top = degrees.iter().map(|d| d.saturating_sub(1)).sum::<usize>() + 1;
    let series = regular_series(N, &degrees, top);

    // Falls: an element that appeared during a batch of degree e with leading degree below e.
    let mut snapshots = observer.batches.clone();
    let final_leads: Vec<Monomial<N>> = basis.iter().map(|g| g.leading_monomial(GREVLEX)).collect();
    let mut fell = false;
    for window in snapshots.windows(2) {
        let (degree, before) = &window[0];
        let (_, after) = &window[1];
        fell |= after[before.len()..].iter().any(|m| m.degree() < *degree);
    }
    if let Some((degree, before)) = snapshots.last() {
        fell |= final_leads
            .iter()
            .any(|m| m.degree() < *degree && !before.contains(m));
    }

    // Each degree read at its close: the first snapshot whose batch degree exceeds it.
    snapshots.push((u64::MAX, final_leads.clone()));
    let mut counts_match = true;
    for (e, &s) in series.iter().enumerate() {
        let leads = &snapshots
            .iter()
            .find(|(degree, _)| *degree > e as u64)
            .unwrap()
            .1;
        let c = HilbertSeries::of_monomial_ideal(leads)
            .unwrap()
            .function(e as u64)
            .unwrap();
        counts_match &= c == s.max(0);
    }
    AffineVerdict { fell, counts_match }
}

/// Whether the top forms are a regular sequence, computed independently: their own exact basis has
/// the regular series.
fn top_forms_regular<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
) -> bool {
    let tops = top_forms(system);
    let degrees: Vec<usize> = tops.iter().map(|f| f.degree() as usize).collect();
    let top = degrees.iter().map(|d| d.saturating_sub(1)).sum::<usize>() + 1;
    let basis = f4(&tops, GREVLEX).unwrap();
    let h = HilbertSeries::of_basis(&basis, GREVLEX)
        .unwrap()
        .values(top as u64)
        .unwrap();
    h == regular_series(N, &degrees, top)
        .into_iter()
        .map(|s| s.max(0))
        .collect::<Vec<_>>()
}

/// Katsura's top forms are regular (it attains its Bézout bound), Eco's and Cyclic's are not. The
/// certificate accepts the exact run exactly when the top forms are regular, and never otherwise.
#[test]
fn the_affine_square_certificate_accepts_katsura_and_refuses_eco_and_cyclic() {
    type F = Zp32003;
    let katsura5 = katsura::<5, F>();
    let katsura6 = katsura::<6, F>();
    let eco6 = eco::<6, F>();
    let cyclic5 = cyclic::<5, F>();

    for (label, verdict, regular) in [
        (
            "katsura-5",
            affine_verdict(&katsura5),
            top_forms_regular(&katsura5),
        ),
        (
            "katsura-6",
            affine_verdict(&katsura6),
            top_forms_regular(&katsura6),
        ),
        ("eco-6", affine_verdict(&eco6), top_forms_regular(&eco6)),
        (
            "cyclic-5",
            affine_verdict(&cyclic5),
            top_forms_regular(&cyclic5),
        ),
    ] {
        assert_eq!(verdict.certifies(), regular, "{label}: {verdict:?}");
        if regular {
            assert!(
                !verdict.fell,
                "{label}: regular top forms admit no degree fall"
            );
        }
        assert_eq!(regular, label.starts_with("katsura"), "{label}");
    }
}

/// The corpus's MQ rows are square and affine. Report, for small seeds, which ones the certificate
/// applies to. Run with `--ignored --nocapture`; the benchmark-size rows are in the note.
#[cfg(feature = "external-runners")]
#[test]
#[ignore = "study: prints the applicability of the affine certificate"]
fn applicability_on_small_square_mq() {
    use zeebra::grobner::external::corpus::random_mq_instance;
    fn one<const N: usize>(seed: u64) {
        type F = Zp32003;
        let instance = random_mq_instance(N, seed, 32003, GREVLEX);
        let names: [&str; N] = std::array::from_fn(|i| instance.variables[i].as_str());
        let system: Vec<MultivariatePolynomial<N, F>> = instance
            .system
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
            .collect();
        let verdict = affine_verdict(&system);
        let regular = top_forms_regular(&system);
        let degrees: Vec<u64> = system.iter().map(|f| f.degree()).collect();
        println!(
            "mq n={N} seed={seed} degrees={degrees:?} {verdict:?} top-forms-regular={regular}"
        );
        assert_eq!(verdict.certifies(), regular);
    }
    for seed in 0..6 {
        one::<5>(seed);
        one::<6>(seed);
        one::<7>(seed);
    }
}

/// The benchmark rows #1038 names, loaded as `examples/m29_cost_model.rs` loads them: MQ10 is the
/// sparse ladder generator's `mq-random-10`, MQ11 the dense wide-corpus `mq-random-11` over
/// Goldilocks, Eco-12 the wide-corpus row over the 64-bit prime, and Katsura-11 the ladder row.
/// Slow in debug; run with `--profile ci-release -- --ignored --nocapture`.
#[cfg(feature = "external-runners")]
#[test]
#[ignore = "study: the benchmark rows, optimized build"]
fn applicability_on_the_benchmark_rows() {
    use zeebra::{
        fields::{PrimeFieldElement64, Zp2147483647},
        grobner::external::corpus,
        util::Json,
    };
    type Goldilocks = PrimeFieldElement64<18446744069414584321>;
    type Wide = PrimeFieldElement64<18446744073709551263>;
    const WIDE: &str = include_str!("../research/wide-corpus/cases.json");

    fn parse<const N: usize, F: FiniteField>(
        variables: &[String],
        generators: &[String],
    ) -> Vec<MultivariatePolynomial<N, F>> {
        let names: [&str; N] = std::array::from_fn(|i| variables[i].as_str());
        generators
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
            .collect()
    }
    fn ladder<const N: usize, F: FiniteField>(
        name: &str,
        p: u64,
    ) -> Vec<MultivariatePolynomial<N, F>> {
        let instance = corpus::instance(name, p, GREVLEX).unwrap();
        parse(&instance.variables, &instance.system)
    }
    fn wide<const N: usize, F: FiniteField>(
        field: &str,
        name: &str,
    ) -> Vec<MultivariatePolynomial<N, F>> {
        let cases = Json::parse(WIDE).unwrap();
        let case = cases
            .items()
            .iter()
            .find(|c| {
                c.get("field").and_then(Json::as_str) == Some(field)
                    && c.get("name").and_then(Json::as_str) == Some(name)
            })
            .unwrap()
            .clone();
        let strings = |key| -> Vec<String> {
            case.get(key)
                .unwrap()
                .items()
                .iter()
                .map(|s| s.as_str().unwrap().to_string())
                .collect()
        };
        parse(&strings("variables"), &strings("generators"))
    }
    fn report<const N: usize, F: FiniteField>(
        label: &str,
        system: Vec<MultivariatePolynomial<N, F>>,
    ) {
        let start = std::time::Instant::now();
        let verdict = affine_verdict(&system);
        let run = start.elapsed();
        let regular = top_forms_regular(&system);
        let basis = f4(&system, GREVLEX).unwrap();
        let leads: Vec<Monomial<N>> = basis.iter().map(|g| g.leading_monomial(GREVLEX)).collect();
        // The check's cost on a certified run: one Hilbert series per closed degree, over the
        // minimal leading monomials up to that degree.
        let top = leads.iter().map(|m| m.degree()).max().unwrap_or(0);
        let start = std::time::Instant::now();
        for e in 0..=top {
            let up_to: Vec<Monomial<N>> =
                leads.iter().copied().filter(|m| m.degree() <= e).collect();
            let _ = HilbertSeries::of_monomial_ideal(&up_to)
                .unwrap()
                .function(e);
        }
        let check = start.elapsed();
        let degrees: Vec<u64> = system.iter().map(|f| f.degree()).collect();
        println!(
            "{label}: degrees={degrees:?} {verdict:?} top-forms-regular={regular} leads={} \
             max-lead-degree={top} check/observed-run={:.5}",
            leads.len(),
            check.as_secs_f64() / run.as_secs_f64()
        );
    }
    report(
        "mq-random-10 / 32003",
        ladder::<10, Zp32003>("mq-random-10", 32003),
    );
    report(
        "mq-random-10 / 2^31-1",
        ladder::<10, Zp2147483647>("mq-random-10", 2147483647),
    );
    report(
        "mq-random-11 / goldilocks",
        wide::<11, Goldilocks>("goldilocks", "mq-random-11"),
    );
    report(
        "mq-random-10 / goldilocks",
        wide::<10, Goldilocks>("goldilocks", "mq-random-10"),
    );
    report(
        "katsura-11 / 2^31-1",
        ladder::<11, Zp2147483647>("katsura-11", 2147483647),
    );
    report("eco-12 / wide64", wide::<12, Wide>("wide64", "eco-12"));
}
