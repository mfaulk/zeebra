//! Certification checks forward inclusion, Buchberger's criterion and reducedness.
//!
//! F4 output assumes reverse inclusion from row derivation. Submitted bases require exact
//! cofactor identities through [`super::membership::certify_submitted_basis_with_witnesses`]
//! before both ideal inclusions are established. The legacy submitted entry point stays incomplete.
//!
//! Product and Gebauer–Möller criteria depend only on leading monomials and are safe to replay.
//! The engine's chain criterion relies on already processed pairs, unavailable to a verifier;
//! enabling it here could silently accept a non-basis. Certification costs are reported separately.

use std::time::{Duration, Instant};

use crate::{
    grobner::{
        pairs::{are_relatively_prime, divides, CriterionCounts, PairCriteria, PairQueue},
        s_polynomial,
    },
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

/// The criteria certification prunes Buchberger's criterion with.
///
/// A constant and not a parameter. For a verifier the criteria are not a tuning knob: the chain
/// criterion's hypothesis cannot be supplied by a verification pass at all, and an option would
/// invite a caller to enable it. See the module documentation for the split.
const CERTIFICATION_CRITERIA: PairCriteria = PairCriteria {
    product: true,
    chain: false,
    gebauer_moller: true,
};

/// Where a basis came from, which decides what certifying it can establish.
///
/// See the module documentation: the runtime checks give `I ⊆ <G>` and cannot give `<G> ⊆ I`, so the
/// legacy report obtains reverse containment only from provenance; the witness route returns
/// a separate combined report.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Provenance {
    /// This crate's F4, run on these generators.
    ///
    /// Licenses the derivation invariant: every F4 matrix row is a monomial multiple of a current
    /// basis element, so every candidate is in the input ideal by induction.
    F4Output,

    /// Anywhere else — a file, another system, a caller's own computation.
    ///
    /// The checks still mean what they say; what they do not mean is that the basis generates the
    /// input ideal rather than a larger one.
    Submitted,
}

/// What certification checked, and what it found.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CertificationReport {
    /// Every input generator reduced to zero modulo the basis.
    pub generators_in_basis: bool,

    /// Every S-polynomial of a pair from the basis reduced to zero modulo it.
    pub buchberger_criterion: bool,

    /// The basis is monic, minimal, and interreduced.
    pub reduced: bool,

    /// Generators checked under [`Self::generators_in_basis`].
    pub generators_checked: usize,

    /// S-polynomials checked under [`Self::buchberger_criterion`].
    ///
    /// Zero when an earlier check already failed: certification stops at the first failure, so a
    /// report's counts describe the work done and not the work a passing run would have done.
    pub s_polynomials_checked: usize,

    /// Pairs a criterion proved redundant, so that no S-polynomial was formed for them.
    ///
    /// With [`Self::s_polynomials_checked`] this accounts for every one of the `|G|(|G|-1)/2` pairs
    /// Buchberger's criterion names, on a run that reached the criterion and completed it. Reported
    /// rather than left to be inferred, because the saving is the reason the criteria are here.
    pub s_polynomials_discarded: usize,

    /// What the checks cost.
    pub elapsed: Duration,

    /// Where the basis came from, as the caller stated it.
    ///
    /// Not something the report discovered. It is recorded so that
    /// [`CertificationReport::is_complete`] can distinguish *verified* properties from the one
    /// property that is *assumed*, rather than quietly folding the two together.
    pub provenance: Provenance,
}

impl Default for CertificationReport {
    /// A report of nothing checked, about a submitted basis.
    ///
    /// `Submitted` rather than `F4Output`: a default that assumed the stronger provenance would
    /// make the weaker claim the one a caller has to opt into, which is the wrong way round for a
    /// claim that cannot be checked.
    fn default() -> Self {
        Self {
            generators_in_basis: false,
            buchberger_criterion: false,
            reduced: false,
            generators_checked: 0,
            s_polynomials_checked: 0,
            s_polynomials_discarded: 0,
            elapsed: Duration::ZERO,
            provenance: Provenance::Submitted,
        }
    }
}

impl CertificationReport {
    /// True if every check this function performs passed.
    ///
    /// Establishes `I ⊆ <G>` and that `G` is a reduced Gröbner basis of `<G>`. Does **not**
    /// establish `<G> ⊆ I` — see the module documentation — so this is the honest result for a
    /// basis of unknown provenance, and it is not on its own a completeness claim.
    pub fn checks_passed(&self) -> bool {
        self.generators_in_basis && self.buchberger_criterion && self.reduced
    }

    /// True if the basis is a reduced Gröbner basis of the ideal the generators generate.
    ///
    /// [`Self::checks_passed`] **and** the reverse containment — which the checks cannot give, so
    /// it comes from [`Provenance::F4Output`]. For a submitted basis this is always false, however
    /// the checks went: `I = <x²>` with `G = {x}` passes all three checks and generates a different
    /// ideal, and nothing a run can measure distinguishes the two.
    pub fn is_complete(&self) -> bool {
        self.checks_passed() && matches!(self.provenance, Provenance::F4Output)
    }

    /// The first check that failed, or why the checks alone are not enough.
    ///
    /// For a submitted basis that passed everything, the "failure" is the unverifiable containment,
    /// which is the honest thing to report rather than `None`.
    pub fn first_failure(&self) -> Option<&'static str> {
        if !self.generators_in_basis {
            Some("an input generator does not reduce to zero modulo the basis")
        } else if !self.buchberger_criterion {
            Some("an S-polynomial of the basis does not reduce to zero modulo it")
        } else if !self.reduced {
            Some("the basis is not reduced")
        } else if !matches!(self.provenance, Provenance::F4Output) {
            Some(
                "the checks passed, but a submitted basis may still generate a larger ideal than \
                 the generators do, which no check here can rule out",
            )
        } else {
            None
        }
    }
}

/// Check a basis **this crate's F4 produced** from `generators`.
///
/// The provenance is a precondition, not a hint: it is what licenses the derivation invariant, and
/// therefore what lets [`CertificationReport::is_complete`] mean "a reduced Gröbner basis of the
/// ideal `generators` generates". Passing a basis from elsewhere here would claim something the
/// checks do not establish — use [`certify_submitted_basis`].
pub fn certify_f4_output<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> CertificationReport {
    certify_with(generators, basis, order, Provenance::F4Output)
}

/// Check a basis of unknown provenance.
///
/// Runs exactly the same checks as [`certify_f4_output`] and reports them the same way. What differs
/// is the conclusion available: [`CertificationReport::is_complete`] is false whatever happens,
/// because `I ⊆ <G>` plus "G is a reduced Gröbner basis of `<G>`" does not give `<G> ⊆ I`.
/// [`CertificationReport::checks_passed`] is the result to read.
pub fn certify_submitted_basis<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> CertificationReport {
    certify_with(generators, basis, order, Provenance::Submitted)
}

/// The checks, under a stated provenance.
///
/// Stops at the first failing check, so the counts in the report describe the work performed.
///
/// See the module documentation for what is checked, what is structural, and why checking
/// Buchberger's criterion alone would not be enough.
fn certify_with<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    provenance: Provenance,
) -> CertificationReport {
    let at = Instant::now();
    let mut report = CertificationReport {
        provenance,
        ..CertificationReport::default()
    };

    // (2) F in <G>. First, because it is linear in the generators and it is the check a truncated
    // basis fails for sure.
    let mut generators_checked = 0;
    for generator in generators.iter().filter(|p| !p.is_zero()) {
        generators_checked += 1;
        if !generator.normal_form(basis, order).is_zero() {
            report.generators_checked = generators_checked;
            report.elapsed = at.elapsed();
            return report;
        }
    }
    report.generators_in_basis = true;
    report.generators_checked = generators_checked;

    // (3) Buchberger's criterion, over the pairs no criterion proves redundant.
    let nonzero: Vec<&MultivariatePolynomial<N, F>> =
        basis.iter().filter(|p| !p.is_zero()).collect();
    let check = check_buchberger_criterion(&nonzero, basis, order, &CERTIFICATION_CRITERIA);
    report.s_polynomials_checked = check.checked;
    report.s_polynomials_discarded = check.discarded;
    if !check.held {
        report.elapsed = at.elapsed();
        return report;
    }
    report.buchberger_criterion = true;

    // (4) Reducedness.
    report.reduced = is_reduced(&nonzero, basis, order);
    report.elapsed = at.elapsed();
    report
}

/// What Buchberger's criterion cost and whether it held.
struct PairCheck {
    /// Every S-polynomial that was formed reduced to zero.
    held: bool,

    /// Pairs whose S-polynomial was formed and reduced.
    checked: usize,

    /// Pairs a criterion proved redundant.
    discarded: usize,
}

/// Buchberger's criterion over the pairs `criteria` does not prove redundant.
///
/// `criteria` is a parameter only so that the tests can exercise each criterion on its own and
/// against the unpruned reference; the one production caller passes
/// [`CERTIFICATION_CRITERIA`]. Stops at the first S-polynomial that does not reduce to zero, so the
/// counts describe the work performed.
fn check_buchberger_criterion<const N: usize, F: FiniteField>(
    nonzero: &[&MultivariatePolynomial<N, F>],
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    criteria: &PairCriteria,
) -> PairCheck {
    debug_assert!(
        !criteria.chain,
        "the chain criterion's witnesses are pairs that have been reduced, and a verification pass \
         has reduced nothing"
    );

    let leads: Vec<Monomial<N>> = nonzero.iter().map(|p| p.leading_monomial(order)).collect();
    let mut counts = CriterionCounts::default();
    let mut queue = PairQueue::<N>::seeded_from_leads(&leads, criteria, &mut counts);
    let mut checked = 0;

    while let Some(pair) = queue.pop() {
        // Gebauer–Möller's criterion F already applies this at insertion, so with both criteria on
        // it never fires. It is here so that the product criterion also stands alone.
        if criteria.product && are_relatively_prime(&leads[pair.left], &leads[pair.right]) {
            counts.product += 1;
            continue;
        }

        checked += 1;
        if !s_polynomial(nonzero[pair.left], nonzero[pair.right], order)
            .normal_form(basis, order)
            .is_zero()
        {
            return PairCheck {
                held: false,
                checked,
                discarded: counts.total(),
            };
        }
    }

    PairCheck {
        held: true,
        checked,
        discarded: counts.total(),
    }
}

/// True if the basis is monic, no leading monomial divides another's, and each element is its own
/// normal form modulo the others.
fn is_reduced<const N: usize, F: FiniteField>(
    nonzero: &[&MultivariatePolynomial<N, F>],
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> bool {
    let leads: Vec<_> = nonzero.iter().map(|p| p.leading_monomial(order)).collect();

    for (index, polynomial) in nonzero.iter().enumerate() {
        if polynomial.leading_coefficient(order) != F::one() {
            return false;
        }
        // Minimality: no other element's leading monomial divides this one's.
        if leads
            .iter()
            .enumerate()
            .any(|(other, lead)| other != index && divides(lead, &leads[index]))
        {
            return false;
        }
        // Interreduced: reducing modulo the others changes nothing.
        let others: Vec<MultivariatePolynomial<N, F>> = basis
            .iter()
            .filter(|p| !p.is_zero() && *p != *polynomial)
            .cloned()
            .collect();
        if polynomial.normal_form(&others, order) != **polynomial {
            return false;
        }
    }

    // And the leading monomials are distinct, which minimality above already implies for distinct
    // elements but not for duplicates.
    let mut sorted = leads.clone();
    sorted.sort();
    let before = sorted.len();
    sorted.dedup();
    sorted.len() == before
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::{
        certify_f4_output, certify_submitted_basis, check_buchberger_criterion, Provenance,
        CERTIFICATION_CRITERIA,
    };
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura},
            buchberger, f4,
            pairs::{are_relatively_prime, CriterionCounts, PairCriteria, PairQueue},
            s_polynomial,
        },
        poly::MonomialOrder,
        FiniteField, Monomial, MultivariatePolynomial,
    };

    type F = Zp2147483647;
    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    /// Gebauer–Möller without the product criterion, so that each can be exercised alone.
    const GEBAUER_MOLLER_ONLY: PairCriteria = PairCriteria {
        product: false,
        chain: false,
        gebauer_moller: true,
    };

    /// Every criterion configuration a verifier may use, plus the unpruned reference.
    const CONFIGURATIONS: [(&str, PairCriteria); 4] = [
        ("none", PairCriteria::NONE),
        ("product", PairCriteria::PRODUCT_ONLY),
        ("gebauer-moller", GEBAUER_MOLLER_ONLY),
        ("certification", CERTIFICATION_CRITERIA),
    ];

    /// Buchberger's criterion over every pair, written out as the reference the pruned check must
    /// agree with.
    ///
    /// Deliberately *not* [`check_buchberger_criterion`] with the criteria off: a reference sharing
    /// the pair-set machinery could not catch a defect in it.
    fn every_pair_holds<const N: usize>(
        basis: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) -> bool {
        let nonzero: Vec<&MultivariatePolynomial<N, F>> =
            basis.iter().filter(|p| !p.is_zero()).collect();
        for (index, f) in nonzero.iter().enumerate() {
            for g in nonzero.iter().skip(index + 1) {
                if !s_polynomial(f, g, order)
                    .normal_form(basis, order)
                    .is_zero()
                {
                    return false;
                }
            }
        }
        true
    }

    /// The pairs certification would reduce, as indices into the nonzero elements.
    fn kept_pairs<const N: usize>(
        nonzero: &[&MultivariatePolynomial<N, F>],
        order: MonomialOrder,
    ) -> HashSet<(usize, usize)> {
        let leads: Vec<Monomial<N>> = nonzero.iter().map(|p| p.leading_monomial(order)).collect();
        let mut counts = CriterionCounts::default();
        let mut queue =
            PairQueue::<N>::seeded_from_leads(&leads, &CERTIFICATION_CRITERIA, &mut counts);
        let mut kept = HashSet::new();
        while let Some(pair) = queue.pop() {
            if are_relatively_prime(&leads[pair.left], &leads[pair.right]) {
                continue;
            }
            kept.insert((pair.left, pair.right));
        }
        kept
    }

    /// Bases with a planted defect: each element dropped in turn, each shifted by a constant, and
    /// each replaced by its difference with its predecessor.
    ///
    /// The shift leaves every leading monomial alone, so the criteria prune exactly the pairs they
    /// prune on the correct basis while the S-polynomials are no longer those of a Gröbner basis —
    /// which is the configuration a silent false pass would need.
    fn planted_defects<const N: usize>(
        basis: &[MultivariatePolynomial<N, F>],
    ) -> Vec<Vec<MultivariatePolynomial<N, F>>> {
        let one = MultivariatePolynomial::<N, F>::one();
        let mut out = Vec::new();
        for dropped in 0..basis.len() {
            let mut defect = basis.to_vec();
            defect.remove(dropped);
            out.push(defect);
        }
        for index in 0..basis.len() {
            let mut defect = basis.to_vec();
            defect[index] = &basis[index] + &one;
            out.push(defect);
        }
        for index in 1..basis.len() {
            let mut defect = basis.to_vec();
            defect[index] = &basis[index] - &basis[index - 1];
            out.push(defect);
        }
        out
    }

    fn parse<const N: usize>(s: &str, vars: [&str; N]) -> MultivariatePolynomial<N, F> {
        MultivariatePolynomial::parse(s, vars).expect("parses")
    }

    /// A basis F4 returns certifies, on every corpus system and every order.
    #[test]
    fn test_f4_bases_certify() {
        let systems: Vec<Vec<&str>> = vec![
            vec!["x^2 - y", "x*y - 1"],
            vec!["x + y + z", "x*y + x*z + y*z", "x*y*z - 1"],
            vec!["x^2 + y", "x^2 + z"],
            vec!["x^2*y + x", "x*y^2 + y"],
            vec!["x^3 - 2*x*y", "x^2*y - 2*y^2 + x"],
            vec!["x*z - y^2", "x^3 - z^2"],
            vec!["x^3 - y", "x^2 - z", "x - y*z", "y^2 - 1"],
            vec!["x^2 + y^2 + z^2", "x*y + y*z"],
            vec!["x", "x - 1"],
        ];

        for order in ALL_ORDERS {
            for strings in &systems {
                let system: Vec<MultivariatePolynomial<3, F>> =
                    strings.iter().map(|s| parse(s, ["x", "y", "z"])).collect();
                let basis = f4(&system, order).expect("within limits");
                let report = certify_f4_output(&system, &basis, order);
                assert!(
                    report.is_complete(),
                    "{:?} under {}: {:?} — {:?}",
                    strings,
                    order.name(),
                    report,
                    report.first_failure()
                );
                assert!(report.generators_checked > 0);
            }
        }
    }

    /// Certification rejects a basis with one element removed, and no criterion changes that.
    ///
    /// The adversarial case the plan asks for, and the reason generator containment is checked and
    /// not only Buchberger's criterion: a truncated basis is still contained in the ideal, so
    /// nothing about *where it came from* distinguishes it. The second half of the loop carries the
    /// same corpus through each pair criterion separately, because pruning a pair whose
    /// S-polynomial does not reduce to zero would turn a rejection into a silent pass.
    #[test]
    fn test_certification_detects_a_truncated_basis() {
        for order in ALL_ORDERS {
            let system: Vec<MultivariatePolynomial<5, F>> = katsura::<5, F>();
            let basis = f4(&system, order).expect("within limits");
            assert!(basis.len() > 1);

            let mut rejected = 0;
            for dropped in 0..basis.len() {
                let mut truncated = basis.clone();
                truncated.remove(dropped);
                let report = certify_f4_output(&system, &truncated, order);
                if !report.is_complete() {
                    rejected += 1;
                }

                let nonzero: Vec<&MultivariatePolynomial<5, F>> =
                    truncated.iter().filter(|p| !p.is_zero()).collect();
                let reference = every_pair_holds(&truncated, order);
                for (configuration, criteria) in CONFIGURATIONS {
                    let check = check_buchberger_criterion(&nonzero, &truncated, order, &criteria);
                    assert_eq!(
                        check.held,
                        reference,
                        "{}: dropping {} under `{}` changed Buchberger's verdict",
                        order.name(),
                        dropped,
                        configuration
                    );
                }
            }
            assert_eq!(
                rejected,
                basis.len(),
                "{}: every truncation must be rejected",
                order.name()
            );
        }
    }

    /// The checks pass for `G = {x}` against `I = <x^2>`, and `is_complete` still refuses to.
    ///
    /// The sharpest case the three runtime checks cannot distinguish: `x^2` reduces to zero modulo
    /// `x`, a one-element basis has no S-polynomial to check, and `x` is monic and reduced — yet
    /// `<x^2>` is not `<x>`. Nothing a run can measure separates the two, so the API does it
    /// instead: as a *submitted* basis the result is `checks_passed` and **not** `is_complete`.
    #[test]
    fn test_the_checks_cannot_separate_a_larger_ideal() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system: Vec<MultivariatePolynomial<2, F>> = vec![parse("x^2", ["x", "y"])];
        let wrong: Vec<MultivariatePolynomial<2, F>> = vec![parse("x", ["x", "y"])];

        // It really is a different ideal: x is not in <x^2>.
        let correct = f4(&system, order).expect("within limits");
        assert!(
            !parse("x", ["x", "y"])
                .normal_form(&correct, order)
                .is_zero(),
            "x was in <x^2> after all, so the test proves nothing"
        );

        let report = certify_submitted_basis(&system, &wrong, order);
        assert!(
            report.checks_passed(),
            "all three checks do pass, which is the point: {:?}",
            report
        );
        assert!(
            !report.is_complete(),
            "but a submitted basis must never be reported complete"
        );
        assert_eq!(report.provenance, Provenance::Submitted);
        assert!(
            report
                .first_failure()
                .expect("a reason must be given")
                .contains("larger ideal"),
            "the reason must name the containment the checks cannot establish"
        );
    }

    /// The same basis under `F4Output` provenance *would* be reported complete — which is why the
    /// provenance is a precondition and not a hint.
    ///
    /// This documents the trust boundary rather than endorsing it: `certify_f4_output` is only
    /// sound when its name is true, and the one call site in this crate is F4's own return path.
    #[test]
    fn test_the_provenance_is_the_whole_difference() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system: Vec<MultivariatePolynomial<2, F>> = vec![parse("x^2", ["x", "y"])];
        let wrong: Vec<MultivariatePolynomial<2, F>> = vec![parse("x", ["x", "y"])];

        let submitted = certify_submitted_basis(&system, &wrong, order);
        let claimed = certify_f4_output(&system, &wrong, order);

        // Identical checks, identical counts, opposite conclusions.
        assert_eq!(submitted.checks_passed(), claimed.checks_passed());
        assert_eq!(
            submitted.s_polynomials_checked,
            claimed.s_polynomials_checked
        );
        assert!(!submitted.is_complete());
        assert!(claimed.is_complete());
    }

    /// Appending a foreign element to a correct basis also passes the checks.
    ///
    /// The milder form of the same gap, kept because it is the case a caller is likeliest to hit:
    /// every generator still reduces to zero in a *larger* ideal.
    #[test]
    fn test_the_checks_cannot_reject_an_appended_foreign_element() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system: Vec<MultivariatePolynomial<3, F>> = vec![
            parse("x^2 - y", ["x", "y", "z"]),
            parse("x*y - 1", ["x", "y", "z"]),
        ];
        let basis = f4(&system, order).expect("within limits");

        // `z` is unconstrained in the original ideal, so `z - 7` is outside it.
        let mut larger = basis.clone();
        larger.push(parse("z - 7", ["x", "y", "z"]));
        assert!(
            !parse("z - 7", ["x", "y", "z"])
                .normal_form(&basis, order)
                .is_zero(),
            "z - 7 was in the original ideal after all"
        );

        let report = certify_submitted_basis(&system, &larger, order);
        assert!(report.checks_passed(), "the checks pass: {:?}", report);
        assert!(!report.is_complete(), "the conclusion does not");
    }

    /// Certification rejects a basis whose elements are not monic.    /// Certification rejects a basis whose elements are not monic.
    #[test]
    fn test_certification_detects_a_non_monic_basis() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system: Vec<MultivariatePolynomial<3, F>> = vec![
            parse("x^2 - y", ["x", "y", "z"]),
            parse("x*y - 1", ["x", "y", "z"]),
        ];
        let basis = f4(&system, order).expect("within limits");

        let scaled: Vec<MultivariatePolynomial<3, F>> = basis
            .iter()
            .enumerate()
            .map(|(index, p)| {
                if index == 0 {
                    p.scale(&F::new(3))
                } else {
                    p.clone()
                }
            })
            .collect();
        let report = certify_f4_output(&system, &scaled, order);
        assert!(report.generators_in_basis, "scaling preserves the ideal");
        assert!(report.buchberger_criterion, "and the criterion");
        assert!(!report.reduced, "but not reducedness");
        assert!(!report.is_complete());
    }

    /// A certified basis agrees with the independent Buchberger engine, and a planted defect in it
    /// is still rejected under each pair criterion.
    ///
    /// The structural invariant `G ⊆ I` is not something a run can check, so this is the closest
    /// an automated check comes: a reduced Gröbner basis is unique for an ideal and an order, so
    /// equality with a basis computed by a different algorithm establishes both containments. The
    /// defects are then carried through each criterion separately, because a criterion that pruned a
    /// pair whose S-polynomial does not reduce to zero would turn a rejection into a silent pass.
    /// Not every defect is one: under lex these bases have pairwise relatively prime leading
    /// monomials, so the product criterion covers every pair and *no* perturbation that leaves the
    /// leading monomials alone can be caught — which is why the corpus is filtered rather than
    /// assumed.
    #[test]
    fn test_certification_agrees_with_buchberger() {
        for order in ALL_ORDERS {
            for (name, system) in [
                ("katsura-4", katsura::<4, F>()),
                ("cyclic-4", cyclic::<4, F>()),
            ] {
                let basis = f4(&system, order).expect("within limits");
                assert!(certify_f4_output(&system, &basis, order).is_complete());
                assert_eq!(
                    basis,
                    buchberger(&system, order),
                    "{} under {}",
                    name,
                    order.name()
                );

                let genuine: Vec<Vec<MultivariatePolynomial<4, F>>> = planted_defects(&basis)
                    .into_iter()
                    .filter(|defect| !every_pair_holds(defect, order))
                    .collect();
                assert!(
                    !genuine.is_empty(),
                    "{} under {}: no planted defect broke the criterion, so nothing is tested",
                    name,
                    order.name()
                );
                for defect in &genuine {
                    let nonzero: Vec<&MultivariatePolynomial<4, F>> =
                        defect.iter().filter(|p| !p.is_zero()).collect();
                    for (configuration, criteria) in CONFIGURATIONS {
                        assert!(
                            !check_buchberger_criterion(&nonzero, defect, order, &criteria).held,
                            "{} under {} with `{}`: a planted defect passed",
                            name,
                            order.name(),
                            configuration
                        );
                    }
                }
            }
        }
    }

    /// Every pair Buchberger's criterion names is accounted for, as checked or as discarded.
    fn assert_the_counts_cover_every_pair<const N: usize>(
        name: &str,
        system: &[MultivariatePolynomial<N, F>],
    ) {
        for order in ALL_ORDERS {
            let basis = f4(system, order).expect("within limits");
            let report = certify_f4_output(system, &basis, order);
            assert!(report.is_complete(), "{} under {}", name, order.name());

            let size = basis.iter().filter(|p| !p.is_zero()).count();
            assert_eq!(
                report.s_polynomials_checked + report.s_polynomials_discarded,
                size * (size - 1) / 2,
                "{} under {}: the counts must cover every pair",
                name,
                order.name()
            );
            assert!(
                report.s_polynomials_discarded > 0,
                "{} under {}: the criteria must prune something",
                name,
                order.name()
            );

            // Ties `kept_pairs` — the model the pruned-pair tests reason with — to the pairs the
            // production check actually reduced, so the two cannot drift apart.
            let nonzero: Vec<&MultivariatePolynomial<N, F>> =
                basis.iter().filter(|p| !p.is_zero()).collect();
            assert_eq!(
                report.s_polynomials_checked,
                kept_pairs(&nonzero, order).len(),
                "{} under {}: the pair set the tests model is not the one that was checked",
                name,
                order.name()
            );
        }
    }

    /// The report accounts for every pair Buchberger's criterion names, and prunes some of them.
    #[test]
    fn test_the_report_accounts_for_every_pair() {
        assert_the_counts_cover_every_pair("katsura-5", &katsura::<5, F>());
        assert_the_counts_cover_every_pair("cyclic-4", &cyclic::<4, F>());
    }

    /// The pruned check and the all-pairs check reach the same verdict, on correct bases and on
    /// every planted defect, under each criterion alone and under both.
    fn assert_the_criteria_never_change_the_verdict<const N: usize>(
        name: &str,
        system: &[MultivariatePolynomial<N, F>],
    ) {
        for order in ALL_ORDERS {
            let basis = f4(system, order).expect("within limits");
            let mut candidates = vec![basis.clone()];
            candidates.extend(planted_defects(&basis));

            let mut genuine_defects = 0;
            let mut discarded_on_defects = 0;

            for (which, candidate) in candidates.iter().enumerate() {
                let reference = every_pair_holds(candidate, order);
                genuine_defects += usize::from(!reference);

                let nonzero: Vec<&MultivariatePolynomial<N, F>> =
                    candidate.iter().filter(|p| !p.is_zero()).collect();
                for (configuration, criteria) in CONFIGURATIONS {
                    let check = check_buchberger_criterion(&nonzero, candidate, order, &criteria);
                    assert_eq!(
                        check.held,
                        reference,
                        "{} under {}, candidate {} with criteria `{}`: the criteria changed the \
                         verdict",
                        name,
                        order.name(),
                        which,
                        configuration
                    );
                    if !reference {
                        discarded_on_defects += check.discarded;
                    }
                }
            }

            assert!(
                genuine_defects > 0,
                "{} under {}: no planted defect was one, so nothing was tested",
                name,
                order.name()
            );
            assert!(
                discarded_on_defects > 0,
                "{} under {}: nothing was pruned on a defective basis, so nothing was tested",
                name,
                order.name()
            );
        }
    }

    /// Pruning the pairs never changes Buchberger's verdict, on correct or defective bases.
    #[test]
    fn test_the_criteria_never_change_the_buchberger_verdict() {
        assert_the_criteria_never_change_the_verdict("katsura-4", &katsura::<4, F>());
        assert_the_criteria_never_change_the_verdict("cyclic-4", &cyclic::<4, F>());
        assert_the_criteria_never_change_the_verdict("katsura-5", &katsura::<5, F>());
    }

    /// A pair the criteria pruned whose S-polynomial does *not* reduce to zero is still caught, by
    /// a pair that was kept.
    ///
    /// The silent false pass this whole module guards against: pruning is only sound because a
    /// defective basis must fail on some *kept* pair too, and this asserts that over a corpus where
    /// the situation genuinely arises rather than trusting the argument.
    #[test]
    fn test_a_defect_on_a_pruned_pair_is_still_caught() {
        let mut occurrences = 0;

        for order in ALL_ORDERS {
            let basis = f4(&katsura::<5, F>(), order).expect("within limits");
            for candidate in planted_defects(&basis) {
                let nonzero: Vec<&MultivariatePolynomial<5, F>> =
                    candidate.iter().filter(|p| !p.is_zero()).collect();
                let kept = kept_pairs(&nonzero, order);

                let mut a_pruned_pair_failed = false;
                for left in 0..nonzero.len() {
                    for right in (left + 1)..nonzero.len() {
                        if kept.contains(&(left, right)) {
                            continue;
                        }
                        if !s_polynomial(nonzero[left], nonzero[right], order)
                            .normal_form(&candidate, order)
                            .is_zero()
                        {
                            a_pruned_pair_failed = true;
                        }
                    }
                }

                if !a_pruned_pair_failed {
                    continue;
                }
                occurrences += 1;
                let check = check_buchberger_criterion(
                    &nonzero,
                    &candidate,
                    order,
                    &CERTIFICATION_CRITERIA,
                );
                assert!(
                    !check.held,
                    "under {}: a pruned pair failed and the pruned check passed anyway — a silent \
                     false pass",
                    order.name()
                );
            }
        }

        assert!(
            occurrences > 0,
            "no planted defect ever landed on a pruned pair, so the test proves nothing"
        );
    }

    /// One criterion, on a basis it prunes pairs from, still does not hide a planted defect.
    fn assert_a_criterion_cannot_hide_a_defect(name: &str, criteria: PairCriteria) {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&katsura::<5, F>(), order).expect("within limits");
        let mut defect = basis.clone();
        defect[0] = &basis[0] + &MultivariatePolynomial::<5, F>::one();

        assert!(
            !every_pair_holds(&defect, order),
            "the planted defect must actually be one, or {} is not being tested",
            name
        );

        let nonzero: Vec<&MultivariatePolynomial<5, F>> =
            defect.iter().filter(|p| !p.is_zero()).collect();
        let all = nonzero.len() * (nonzero.len() - 1) / 2;

        // That the criterion prunes this basis is established independently of the check, which
        // stops at the first failure and so cannot be asked how much it would have pruned.
        let mut counts = CriterionCounts::default();
        let leads: Vec<Monomial<5>> = nonzero.iter().map(|p| p.leading_monomial(order)).collect();
        let queue = PairQueue::<5>::seeded_from_leads(&leads, &criteria, &mut counts);
        let prunable = all - queue.len()
            + (0..nonzero.len())
                .flat_map(|i| ((i + 1)..nonzero.len()).map(move |j| (i, j)))
                .filter(|&(i, j)| criteria.product && are_relatively_prime(&leads[i], &leads[j]))
                .count();
        assert!(
            prunable > 0,
            "{} prunes nothing on this basis, so the test proves nothing",
            name
        );

        let check = check_buchberger_criterion(&nonzero, &defect, order, &criteria);
        assert!(!check.held, "{} hid a planted defect", name);
    }

    /// The product criterion does not hide a planted defect on a basis it prunes pairs from.
    #[test]
    fn test_the_product_criterion_cannot_hide_a_planted_defect() {
        assert_a_criterion_cannot_hide_a_defect(
            "the product criterion",
            PairCriteria::PRODUCT_ONLY,
        );
    }

    /// Gebauer–Möller does not hide a planted defect on a basis it prunes pairs from.
    #[test]
    fn test_gebauer_moller_cannot_hide_a_planted_defect() {
        assert_a_criterion_cannot_hide_a_defect("Gebauer–Möller", GEBAUER_MOLLER_ONLY);
    }

    /// Certification stops at the first failure, and says which one it was.
    #[test]
    fn test_the_report_names_the_first_failure() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system: Vec<MultivariatePolynomial<3, F>> = vec![
            parse("x^2 - y", ["x", "y", "z"]),
            parse("x*y - 1", ["x", "y", "z"]),
        ];
        // The empty basis: the zero ideal, which no nonzero generator reduces into.
        let report = certify_f4_output(&system, &[], order);
        assert!(!report.generators_in_basis);
        assert_eq!(
            report.s_polynomials_checked, 0,
            "the later checks must not have run"
        );
        assert_eq!(
            report.first_failure(),
            Some("an input generator does not reduce to zero modulo the basis")
        );
    }
}
