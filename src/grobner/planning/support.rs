//! Support and leading-monomial input features: which monomials the generators use, how they
//! overlap, and what the initial pairs look like under the requested order.
//!
//! [`analysis`](super::analysis) counts terms and degrees, [`structure`](super::structure) reads
//! the incidence graph and the linear part. This module adds the rest of #1009's inexpensive
//! descriptors:
//!
//! - [`support_profile`]: per-generator term counts and degree spread, distinct and shared
//!   monomials, overlap between generators, per-variable exponent profiles, homogeneous
//!   (top-degree) density next to affine density, and the monomial, binomial and duplicate
//!   generator counts.
//! - [`leading_profile`]: under one monomial order, how many leading monomials are divisible by
//!   another's, and the degrees of `lcm` and `gcd` over the initial pairs, sampled
//!   deterministically under a hard cap.
//!
//! Every figure is a **presentation statistic**: a predictor of cost, not a property of the
//! ideal. The duplicate count is exact about the *presentation* (a duplicate generates nothing
//! new), and a coprime initial pair is exact about *that pair* (Buchberger's product criterion
//! reduces its S-polynomial to zero), but neither says anything about the ideal beyond that.
//! `docs/research/input-features.md` §5–§7 gives the definitions, costs and invariance.

use std::collections::HashMap;

use crate::{FiniteField, Monomial, MonomialOrder, MultivariatePolynomial};

/// Insertions [`support_profile`] spends on generator overlap before giving up.
///
/// One unit is one (generator, generator) pair recorded through a shared monomial. No record of
/// the #1006 pilot panel reaches the cap, so its cost in time is unmeasured
/// (`docs/research/input-features.md` §8).
pub const DEFAULT_OVERLAP_WORK: u64 = 1 << 20;

/// Initial pairs [`leading_profile`] examines at most.
pub const DEFAULT_PAIR_SAMPLE: u64 = 1 << 14;

/// The supports of a system's generators.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SupportProfile {
    /// Variables in the ring, `N`.
    pub variables: usize,

    /// Nonzero generators. Every other count excludes zero generators.
    pub nonzero_generators: usize,

    /// `(terms, generators with that many terms)`, ascending.
    pub terms_histogram: Vec<(usize, usize)>,

    /// `(max − min term degree, generators with that spread)`, ascending. Spread zero is a
    /// homogeneous generator.
    pub degree_spread_histogram: Vec<(u64, usize)>,

    /// Generators whose terms all have one degree. Every generator homogeneous is
    /// [`crate::grobner::hilbert::is_homogeneous`].
    pub homogeneous_generators: usize,

    /// Terms of each generator's top degree, summed.
    pub top_degree_terms: usize,

    /// Total terms, summed over generators.
    pub terms: usize,

    /// `Σ C(N + d − 1, d)` over generators of degree `d`: the monomials of degree exactly `d`.
    /// Saturating.
    pub homogeneous_capacity: u64,

    /// `Σ C(N + d, d)` over generators of degree `d`: the monomials of degree at most `d`.
    /// Saturating.
    pub affine_capacity: u64,

    /// Distinct monomials across the system, the constant monomial included.
    pub distinct_monomials: usize,

    /// Distinct monomials that occur in two or more generators.
    pub shared_monomials: usize,

    /// The most generators any one monomial occurs in. Zero for the empty system.
    pub max_monomial_multiplicity: usize,

    /// Unordered generator pairs that share a **nonconstant** monomial, or `None` when the work
    /// cap ran out first.
    ///
    /// The constant monomial is left out because nearly every affine generator has one, and
    /// sharing it couples nothing.
    pub overlapping_pairs: Option<u64>,

    /// Per variable, its largest exponent in any term. Length `N`.
    pub max_exponent: Vec<u32>,

    /// Per variable, the sum of its exponents over every term. Length `N`.
    pub exponent_mass: Vec<u64>,

    /// Nonconstant generators with exactly one term.
    pub monomial_generators: usize,

    /// Generators with exactly two terms.
    pub binomial_generators: usize,

    /// Nonzero generators that are a nonzero scalar multiple of an earlier generator.
    ///
    /// Exact over the coefficient field: `x + y` and `x − y` are duplicates in characteristic two
    /// and not otherwise. Removing them leaves the ideal unchanged.
    pub duplicate_generators: usize,
}

impl SupportProfile {
    /// Top-degree terms against the monomials of exactly each generator's degree. One when every
    /// generator's top-degree part is dense, zero for the empty system.
    ///
    /// The density that matters for a homogeneous system, where [`Self::affine_density`] counts
    /// lower-degree monomials the generators cannot have.
    pub fn top_degree_density(&self) -> f64 {
        ratio(self.top_degree_terms as u64, self.homogeneous_capacity)
    }

    /// Terms against the monomials of degree at most each generator's degree, the same figure as
    /// [`SystemShape::monomial_density`](super::SystemShape::monomial_density).
    pub fn affine_density(&self) -> f64 {
        ratio(self.terms as u64, self.affine_capacity)
    }

    /// Nonconstant single-term generators as a fraction of nonzero generators.
    pub fn monomial_fraction(&self) -> f64 {
        ratio(
            self.monomial_generators as u64,
            self.nonzero_generators as u64,
        )
    }

    /// Two-term generators as a fraction of nonzero generators.
    pub fn binomial_fraction(&self) -> f64 {
        ratio(
            self.binomial_generators as u64,
            self.nonzero_generators as u64,
        )
    }

    /// Duplicates as a fraction of nonzero generators.
    pub fn duplicate_fraction(&self) -> f64 {
        ratio(
            self.duplicate_generators as u64,
            self.nonzero_generators as u64,
        )
    }
}

/// `a / b`, zero when `b` is zero.
fn ratio(a: u64, b: u64) -> f64 {
    if b == 0 {
        0.0
    } else {
        a as f64 / b as f64
    }
}

/// The support profile of `system`, with generator overlap capped at `overlap_work` pair
/// insertions.
///
/// One pass over the terms for the counts and exponent profiles, one hash per term for the
/// monomial multiplicities, and expected `O(T)` for duplicates (generators are bucketed by term
/// count and lex-leading monomial, then compared within a bucket). Overlap costs at most
/// `overlap_work` further insertions.
pub fn support_profile<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    overlap_work: u64,
) -> SupportProfile {
    let mut profile = SupportProfile {
        variables: N,
        max_exponent: vec![0; N],
        exponent_mass: vec![0; N],
        ..SupportProfile::default()
    };
    let mut spreads: Vec<u64> = Vec::new();
    let mut term_counts: Vec<usize> = Vec::new();
    // Monomial → generators containing it, in input order.
    let mut holders: HashMap<Monomial<N>, Vec<usize>> = HashMap::new();
    let mut nonzero: Vec<usize> = Vec::new();

    for (index, p) in system.iter().enumerate() {
        if p.is_zero() {
            continue;
        }
        nonzero.push(index);
        let terms = p.terms().len();
        profile.terms += terms;
        term_counts.push(terms);
        match terms {
            1 if !p.is_constant() => profile.monomial_generators += 1,
            2 => profile.binomial_generators += 1,
            _ => {}
        }

        let top = p.degree();
        let mut bottom = top;
        for monomial in p.terms().keys() {
            let d = monomial.degree();
            bottom = bottom.min(d);
            if d == top {
                profile.top_degree_terms += 1;
            }
            for (v, &e) in monomial.exponents().iter().enumerate() {
                profile.max_exponent[v] = profile.max_exponent[v].max(e);
                profile.exponent_mass[v] += u64::from(e);
            }
            holders.entry(*monomial).or_default().push(index);
        }
        spreads.push(top - bottom);
        if top == bottom {
            profile.homogeneous_generators += 1;
        }
        profile.homogeneous_capacity = profile
            .homogeneous_capacity
            .saturating_add(monomials_of_degree(N, top));
        profile.affine_capacity = profile
            .affine_capacity
            .saturating_add(super::monomials_up_to_degree(N, top));
    }
    profile.nonzero_generators = nonzero.len();
    profile.terms_histogram = histogram(term_counts);
    profile.degree_spread_histogram = histogram(spreads);

    profile.distinct_monomials = holders.len();
    for list in holders.values() {
        if list.len() > 1 {
            profile.shared_monomials += 1;
        }
        profile.max_monomial_multiplicity = profile.max_monomial_multiplicity.max(list.len());
    }
    profile.overlapping_pairs = overlapping_pairs(&holders, overlap_work);
    profile.duplicate_generators = duplicates(system, &nonzero);
    profile
}

/// Distinct generator pairs sharing a nonconstant monomial, or `None` past `budget` insertions.
fn overlapping_pairs<const N: usize>(
    holders: &HashMap<Monomial<N>, Vec<usize>>,
    budget: u64,
) -> Option<u64> {
    let mut work: u64 = 0;
    let mut pairs: std::collections::HashSet<(usize, usize)> = std::collections::HashSet::new();
    for (monomial, list) in holders {
        if monomial.is_one() || list.len() < 2 {
            continue;
        }
        let k = list.len() as u64;
        work = work.saturating_add(k * (k - 1) / 2);
        if work > budget {
            return None;
        }
        for (a, &i) in list.iter().enumerate() {
            for &j in &list[a + 1..] {
                pairs.insert((i, j));
            }
        }
    }
    Some(pairs.len() as u64)
}

/// Nonzero generators (indices in `nonzero`) that are a scalar multiple of an earlier one.
fn duplicates<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    nonzero: &[usize],
) -> usize {
    let order = MonomialOrder::Lexicographic;
    // Bucket by (term count, lex-leading monomial): scalar multiples agree on both.
    let mut buckets: HashMap<(usize, Monomial<N>), Vec<MultivariatePolynomial<N, F>>> =
        HashMap::new();
    let mut count = 0;
    for &index in nonzero {
        let p = &system[index];
        let monic = p.scale(&p.leading_coefficient(order).inverse());
        let bucket = buckets
            .entry((p.terms().len(), p.leading_monomial(order)))
            .or_default();
        if bucket.contains(&monic) {
            count += 1;
        } else {
            bucket.push(monic);
        }
    }
    count
}

/// Monomials of total degree exactly `degree` in `variables` variables, `C(variables + degree −
/// 1, degree)`, saturating. One for degree zero, and zero for degree positive in no variables.
fn monomials_of_degree(variables: usize, degree: u64) -> u64 {
    if degree == 0 {
        return 1;
    }
    if variables == 0 {
        return 0;
    }
    // C(v − 1 + d, d) is the count of degree ≤ d in v − 1 variables.
    super::monomials_up_to_degree(variables - 1, degree)
}

/// `(value, occurrences)`, ascending by value.
fn histogram<T: Ord + Copy>(mut values: Vec<T>) -> Vec<(T, usize)> {
    values.sort_unstable();
    let mut out: Vec<(T, usize)> = Vec::new();
    for value in values {
        match out.last_mut() {
            Some((v, count)) if *v == value => *count += 1,
            _ => out.push((value, 1)),
        }
    }
    out
}

/// Leading-monomial statistics of a system under one order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeadingProfile {
    /// The order the leading monomials are taken in.
    pub order: MonomialOrder,

    /// Nonzero generators.
    pub generators: usize,

    /// `(degree of the leading monomial, generators)`, ascending.
    pub leading_degree_histogram: Vec<(u64, usize)>,

    /// Generators whose leading monomial is divisible by another generator's.
    ///
    /// Of generators with *equal* leading monomials, all but the first count. Such a generator can
    /// be top-reduced by another before any pair is formed, so the input is not interreduced. A
    /// nonzero constant has leading monomial 1 and makes every other generator count.
    pub divisible_leading: usize,

    /// Unordered pairs of nonzero generators, `m (m − 1) / 2`.
    pub total_pairs: u64,

    /// Pairs examined: all of them up to the sample cap, otherwise a deterministic, evenly spaced
    /// subset of exactly the cap.
    pub sampled_pairs: u64,

    /// Sampled pairs whose leading monomials are coprime. Exact for each such pair: by the product
    /// criterion its S-polynomial reduces to zero, so no algorithm needs to reduce it.
    pub coprime_pairs: u64,

    /// `(deg lcm(LM_i, LM_j), sampled pairs)`, ascending: the degree each initial pair enters at.
    pub lcm_degree_histogram: Vec<(u64, usize)>,

    /// `(deg gcd(LM_i, LM_j), sampled pairs)`, ascending. Degree zero is the coprime pairs.
    pub gcd_degree_histogram: Vec<(u64, usize)>,
}

impl LeadingProfile {
    /// Coprime pairs as a fraction of sampled pairs, zero if none were sampled.
    pub fn coprime_fraction(&self) -> f64 {
        ratio(self.coprime_pairs, self.sampled_pairs)
    }
}

/// The leading-monomial profile of `system` under `order`, examining at most `pair_sample`
/// initial pairs.
///
/// `O(T)` order comparisons for the leading monomials, `O(m² N)` exponent reads for the
/// divisibility count over `m` nonzero generators, and `O(m + pair_sample · N)` for the pairs.
pub fn leading_profile<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    pair_sample: u64,
) -> LeadingProfile {
    let leading: Vec<Monomial<N>> = system
        .iter()
        .filter(|p| !p.is_zero())
        .map(|p| p.leading_monomial(order))
        .collect();
    let m = leading.len();

    let mut divisible_leading = 0;
    for (j, lj) in leading.iter().enumerate() {
        let reducible = leading
            .iter()
            .enumerate()
            .any(|(i, li)| i != j && divides(li, lj) && (li != lj || i < j));
        if reducible {
            divisible_leading += 1;
        }
    }

    let total_pairs = (m as u64) * (m as u64).saturating_sub(1) / 2;
    let sampled_pairs = total_pairs.min(pair_sample);
    let mut coprime_pairs = 0;
    let mut lcm_degrees = Vec::with_capacity(sampled_pairs as usize);
    let mut gcd_degrees = Vec::with_capacity(sampled_pairs as usize);
    // Walk pair indices in increasing order: row i holds pairs (i, i+1..m), starting at row_start.
    let (mut i, mut row_start) = (0usize, 0u64);
    for s in 0..sampled_pairs {
        let k = if sampled_pairs == total_pairs {
            s
        } else {
            ((u128::from(s) * u128::from(total_pairs)) / u128::from(sampled_pairs)) as u64
        };
        while k >= row_start + (m - 1 - i) as u64 {
            row_start += (m - 1 - i) as u64;
            i += 1;
        }
        let j = i + 1 + (k - row_start) as usize;
        let (a, b) = (leading[i].exponents(), leading[j].exponents());
        let (mut lcm, mut gcd) = (0u64, 0u64);
        for (&x, &y) in a.iter().zip(b) {
            lcm += u64::from(x.max(y));
            gcd += u64::from(x.min(y));
        }
        if gcd == 0 {
            coprime_pairs += 1;
        }
        lcm_degrees.push(lcm);
        gcd_degrees.push(gcd);
    }

    LeadingProfile {
        order,
        generators: m,
        leading_degree_histogram: histogram(leading.iter().map(Monomial::degree).collect()),
        divisible_leading,
        total_pairs,
        sampled_pairs,
        coprime_pairs,
        lcm_degree_histogram: histogram(lcm_degrees),
        gcd_degree_histogram: histogram(gcd_degrees),
    }
}

/// `a` divides `b`.
fn divides<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> bool {
    a.exponents().iter().zip(b.exponents()).all(|(x, y)| x <= y)
}

#[cfg(test)]
mod tests {
    use super::{
        leading_profile, monomials_of_degree, support_profile, DEFAULT_OVERLAP_WORK,
        DEFAULT_PAIR_SAMPLE,
    };
    use crate::{
        fields::{Zp2, Zp2147483647, Zp31},
        grobner::{benchmark_systems::katsura, hilbert::is_homogeneous, planning::analyze},
        FiniteField, MonomialOrder, MultivariatePolynomial,
    };

    type F = Zp2147483647;

    fn parse<const N: usize, K: FiniteField>(
        strings: &[&str],
        vars: [&str; N],
    ) -> Vec<MultivariatePolynomial<N, K>> {
        strings
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, vars).expect("parses"))
            .collect()
    }

    /// Term counts, degree spread and homogeneity per generator; zero generators excluded.
    #[test]
    fn test_terms_and_degree_spread() {
        let mut system =
            parse::<3, F>(&["x^2*y + z", "y - 1", "z^3", "x*y + y*z"], ["x", "y", "z"]);
        system.push(MultivariatePolynomial::zero());
        let profile = support_profile(&system, DEFAULT_OVERLAP_WORK);
        assert_eq!(profile.nonzero_generators, 4);
        assert_eq!(profile.terms, 7);
        assert_eq!(profile.terms_histogram, vec![(1, 1), (2, 3)]);
        // Spreads: 2, 1, 0, 0.
        assert_eq!(
            profile.degree_spread_histogram,
            vec![(0, 2), (1, 1), (2, 1)]
        );
        assert_eq!(profile.homogeneous_generators, 2);
        assert_eq!(profile.top_degree_terms, 1 + 1 + 1 + 2);
    }

    /// The homogeneous count agrees with `hilbert::is_homogeneous` on the whole system.
    #[test]
    fn test_homogeneous_count_agrees_with_is_homogeneous() {
        for strings in [
            &["x^2 + y^2", "x*y"][..],
            &["x^2 + y", "x*y"][..],
            &["x^3 - y^2*x"][..],
        ] {
            let system = parse::<2, F>(strings, ["x", "y"]);
            let profile = support_profile(&system, DEFAULT_OVERLAP_WORK);
            assert_eq!(
                profile.homogeneous_generators == profile.nonzero_generators,
                is_homogeneous(&system),
                "{strings:?}"
            );
        }
    }

    /// Homogeneous density counts only degree-d monomials; affine density counts degree ≤ d and
    /// matches `SystemShape::monomial_density`.
    #[test]
    fn test_top_degree_and_affine_density() {
        // A dense homogeneous quadratic in two variables: all three degree-2 monomials.
        let system = parse::<2, F>(&["x^2 + x*y + y^2"], ["x", "y"]);
        let profile = support_profile(&system, DEFAULT_OVERLAP_WORK);
        assert_eq!(profile.homogeneous_capacity, 3);
        assert_eq!(profile.affine_capacity, 6);
        assert_eq!(profile.top_degree_density(), 1.0);
        assert_eq!(profile.affine_density(), 0.5);
        assert_eq!(
            profile.affine_density(),
            analyze(&system).monomial_density()
        );

        // Katsura's quadratics are affine: the two densities differ, and affine agrees with
        // SystemShape.
        let k = katsura::<5, F>();
        let profile = support_profile(&k, DEFAULT_OVERLAP_WORK);
        assert_eq!(profile.affine_density(), analyze(&k).monomial_density());
        assert!(profile.top_degree_density() > profile.affine_density());
    }

    /// Exactly-degree-d monomial counts, including the edge cases.
    #[test]
    fn test_monomials_of_degree() {
        assert_eq!(monomials_of_degree(2, 2), 3);
        assert_eq!(monomials_of_degree(3, 2), 6);
        assert_eq!(monomials_of_degree(10, 2), 55);
        assert_eq!(monomials_of_degree(4, 0), 1);
        assert_eq!(monomials_of_degree(0, 0), 1);
        assert_eq!(monomials_of_degree(0, 3), 0);
        assert_eq!(monomials_of_degree(1, 7), 1);
    }

    /// Distinct and shared monomials, multiplicity, and overlap that ignores the constant term.
    #[test]
    fn test_support_overlap() {
        let system = parse::<3, F>(
            &["x*y + z - 1", "x*y + 1", "z^2 - 1", "y + 2"],
            ["x", "y", "z"],
        );
        let profile = support_profile(&system, DEFAULT_OVERLAP_WORK);
        // x*y, z, 1, z^2, y.
        assert_eq!(profile.distinct_monomials, 5);
        // x*y in two, 1 in all four.
        assert_eq!(profile.shared_monomials, 2);
        assert_eq!(profile.max_monomial_multiplicity, 4);
        // Only (0, 1) share a nonconstant monomial; the constant couples nothing.
        assert_eq!(profile.overlapping_pairs, Some(1));
        // The cap is honoured.
        assert_eq!(support_profile(&system, 0).overlapping_pairs, None);
    }

    /// Per-variable exponent profiles: the largest exponent and the total over terms.
    #[test]
    fn test_exponent_profiles() {
        let system = parse::<3, F>(&["x^3*y + y^2", "x - y"], ["x", "y", "z"]);
        let profile = support_profile(&system, DEFAULT_OVERLAP_WORK);
        assert_eq!(profile.max_exponent, vec![3, 2, 0]);
        assert_eq!(profile.exponent_mass, vec![3 + 1, 1 + 2 + 1, 0]);
    }

    /// Monomial and binomial generators; a constant is neither a monomial generator nor counted
    /// as one.
    #[test]
    fn test_monomial_and_binomial_fractions() {
        let system = parse::<2, F>(&["x^2", "x*y - 1", "y^3 + x", "x + y + 1", "5"], ["x", "y"]);
        let profile = support_profile(&system, DEFAULT_OVERLAP_WORK);
        assert_eq!(profile.monomial_generators, 1);
        assert_eq!(profile.binomial_generators, 2);
        assert_eq!(profile.monomial_fraction(), 1.0 / 5.0);
        assert_eq!(profile.binomial_fraction(), 2.0 / 5.0);
    }

    /// Duplicates are scalar multiples of an earlier generator, decided over the actual field.
    #[test]
    fn test_duplicates_are_normalized_and_field_exact() {
        let system = parse::<2, F>(
            &[
                "x + y",
                "3*x + 3*y",
                "x - y",
                "x^2 + y",
                "x^2 + y",
                "2*x^2 + 2*y",
            ],
            ["x", "y"],
        );
        let profile = support_profile(&system, DEFAULT_OVERLAP_WORK);
        // 3x+3y duplicates x+y; both later x^2+y copies duplicate the first.
        assert_eq!(profile.duplicate_generators, 3);
        assert_eq!(profile.duplicate_fraction(), 0.5);

        // In characteristic two, x − y is x + y.
        let two = parse::<2, Zp2>(&["x + y", "x - y"], ["x", "y"]);
        assert_eq!(
            support_profile(&two, DEFAULT_OVERLAP_WORK).duplicate_generators,
            1
        );
        // Over GF(31), 16·(2x + 2y) = x + y: scaling by the inverse is exact.
        let small = parse::<2, Zp31>(&["2*x + 2*y", "x + y", "x + 2*y"], ["x", "y"]);
        assert_eq!(
            support_profile(&small, DEFAULT_OVERLAP_WORK).duplicate_generators,
            1
        );
    }

    /// Reordering generators and scaling them leaves every count unchanged.
    #[test]
    fn test_support_profile_invariance_under_reorder_and_scaling() {
        let a = parse::<3, F>(&["x*y + z - 1", "z^2 - x", "y + 2"], ["x", "y", "z"]);
        let b = parse::<3, F>(&["5*y + 10", "x*y + z - 1", "-z^2 + x"], ["x", "y", "z"]);
        assert_eq!(
            support_profile(&a, DEFAULT_OVERLAP_WORK),
            support_profile(&b, DEFAULT_OVERLAP_WORK)
        );
    }

    /// Divisible leading monomials, including equal ones and a constant, which divides all.
    #[test]
    fn test_divisible_leading_monomials() {
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        let system = parse::<2, F>(&["x^2 + y", "x^2*y - 1", "y^3", "x^2 - y"], ["x", "y"]);
        let profile = leading_profile(&system, grevlex, DEFAULT_PAIR_SAMPLE);
        // x^2 | x^2*y; the second x^2 counts, the first does not; y^3 is divisible by none.
        assert_eq!(profile.divisible_leading, 2);
        assert_eq!(profile.leading_degree_histogram, vec![(2, 2), (3, 2)]);

        let with_unit = parse::<2, F>(&["x^2 + y", "y^3", "7"], ["x", "y"]);
        assert_eq!(
            leading_profile(&with_unit, grevlex, DEFAULT_PAIR_SAMPLE).divisible_leading,
            2
        );
    }

    /// The leading monomial, and so divisibility, depends on the order.
    #[test]
    fn test_leading_profile_depends_on_the_order() {
        // Under lex x > y the leading monomials are x and x: one divisible. Under grevlex they are
        // y^2 and x: none.
        let system = parse::<2, F>(&["x + y^2", "x - 1"], ["x", "y"]);
        let lex = leading_profile(&system, MonomialOrder::Lexicographic, DEFAULT_PAIR_SAMPLE);
        let grevlex = leading_profile(
            &system,
            MonomialOrder::GradedReverseLexicographic,
            DEFAULT_PAIR_SAMPLE,
        );
        assert_eq!(lex.divisible_leading, 1);
        assert_eq!(grevlex.divisible_leading, 0);
        assert_eq!(grevlex.coprime_pairs, 1);
        assert_eq!(lex.coprime_pairs, 0);
    }

    /// Pair statistics: lcm and gcd degrees, and coprime pairs, over all pairs when they fit.
    #[test]
    fn test_initial_pair_statistics() {
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        // Leading monomials x^2, x*y, z.
        let system = parse::<3, F>(&["x^2 - 1", "x*y + z", "z + 1"], ["x", "y", "z"]);
        let profile = leading_profile(&system, grevlex, DEFAULT_PAIR_SAMPLE);
        assert_eq!(profile.total_pairs, 3);
        assert_eq!(profile.sampled_pairs, 3);
        // (x^2, xy): lcm x^2 y deg 3, gcd x deg 1. (x^2, z): lcm deg 3, coprime. (xy, z): deg 3,
        // coprime.
        assert_eq!(profile.lcm_degree_histogram, vec![(3, 3)]);
        assert_eq!(profile.gcd_degree_histogram, vec![(0, 2), (1, 1)]);
        assert_eq!(profile.coprime_pairs, 2);
        assert_eq!(profile.coprime_fraction(), 2.0 / 3.0);
    }

    /// Past the cap the sample is exactly the cap, deterministic, and covers more than the first
    /// rows: on a system whose last generator is coprime to the rest, a prefix sample would see
    /// none of its pairs.
    #[test]
    fn test_pair_sampling_is_capped_and_spread() {
        let grevlex = MonomialOrder::GradedReverseLexicographic;
        let mut strings: Vec<String> = (1..=20).map(|e| format!("x^{e} + y")).collect();
        strings.push("z".to_string());
        let refs: Vec<&str> = strings.iter().map(String::as_str).collect();
        let system = parse::<3, F>(&refs, ["x", "y", "z"]);

        let full = leading_profile(&system, grevlex, DEFAULT_PAIR_SAMPLE);
        assert_eq!(full.total_pairs, 21 * 20 / 2);
        assert_eq!(full.sampled_pairs, full.total_pairs);
        assert_eq!(full.coprime_pairs, 20);

        let sampled = leading_profile(&system, grevlex, 40);
        assert_eq!(sampled.total_pairs, 210);
        assert_eq!(sampled.sampled_pairs, 40);
        let histogram_total: usize = sampled.lcm_degree_histogram.iter().map(|&(_, n)| n).sum();
        assert_eq!(histogram_total, 40);
        assert_eq!(
            sampled,
            leading_profile(&system, grevlex, 40),
            "deterministic"
        );
        // gcd(x^(i+1), x^(j+1)) has degree i + 1, so a 40-pair prefix (rows 0 and 1) sees gcd
        // degree at most 2. An evenly spaced sample reaches the late rows.
        let deepest = sampled.gcd_degree_histogram.last().expect("sampled").0;
        assert!(deepest >= 15, "sample stayed in the first rows: {deepest}");
        assert!(sampled.coprime_pairs > 0);
    }

    /// The empty system, and systems of zero generators, are described, not panicked on.
    #[test]
    fn test_the_empty_system() {
        let profile = support_profile::<3, F>(&[], DEFAULT_OVERLAP_WORK);
        assert_eq!(profile.nonzero_generators, 0);
        assert_eq!(profile.overlapping_pairs, Some(0));
        assert_eq!(profile.max_exponent, vec![0; 3]);
        assert_eq!(profile.top_degree_density(), 0.0);
        assert_eq!(profile.duplicate_fraction(), 0.0);

        let zeros = vec![MultivariatePolynomial::<2, F>::zero(); 3];
        let leading = leading_profile(&zeros, MonomialOrder::Lexicographic, DEFAULT_PAIR_SAMPLE);
        assert_eq!(leading.generators, 0);
        assert_eq!(leading.total_pairs, 0);
        assert_eq!(leading.coprime_fraction(), 0.0);

        let one = parse::<2, F>(&["x + 1"], ["x", "y"]);
        let leading = leading_profile(&one, MonomialOrder::Lexicographic, DEFAULT_PAIR_SAMPLE);
        assert_eq!(leading.total_pairs, 0);
        assert_eq!(leading.divisible_leading, 0);
    }
}
