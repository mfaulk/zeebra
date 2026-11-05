//! Checking that a basis really is a reduced Gröbner basis of the ideal it was built from.
//!
//! F4 as written returns a complete basis or an error, and that rests on the algorithm: every
//! critical pair is processed or discarded by a criterion that is a theorem. M22-C adds a strategy
//! that decides *in what order* pairs are processed on the strength of a **prediction**, and a
//! prediction is not a theorem — so the plan's §8.3 asks for the result to be established
//! independently rather than inferred from the strategy having run.
//!
//! # What has to be established, and what each check gives
//!
//! Write `F` for the input generators, `G` for the returned basis, and `I = <F>`.
//!
//! 1. **`G ⊆ I`.** Structural, and *not* checked here. Every F4 matrix row is a monomial multiple
//!    of a current basis element, so every candidate is an `F`-combination by induction, and the
//!    final interreduction only takes combinations of those. There is nothing a run could check
//!    that would be more convincing than the construction; what the tests do instead is compare
//!    against an independent Buchberger basis on systems small enough for one, which is
//!    `test_certification_agrees_with_buchberger`.
//! 2. **`F ⊆ <G>`** — every generator reduces to zero modulo `G`. With (1) this gives `I = <G>`.
//! 3. **Buchberger's criterion** — every S-polynomial of a pair from `G` reduces to zero modulo
//!    `G`. With `<G> = I` this gives that `G` is a Gröbner basis *of `I`*.
//! 4. **Reducedness** — monic, no leading monomial divisible by another's, and each element its own
//!    normal form modulo the rest. This is what makes the answer unique, hence comparable.
//!
//! (2) is the one that cannot be skipped, and the reason is worth stating: checking only (3) and
//! (4) establishes that `G` is a reduced Gröbner basis of **some** ideal, which is exactly what a
//! truncated computation also produces. `test_certification_detects_a_truncated_basis` drops each
//! element of a correct basis in turn and every truncation is rejected.
//!
//! # What certification cannot catch, and what the API does about it
//!
//! The three runtime checks establish `I ⊆ <G>` and that `G` is a reduced Gröbner basis of `<G>`.
//! They say **nothing about `<G> ⊆ I`** — and they cannot, because every generator of `I` reduces
//! to zero in any ideal containing `I`. Two consequences, and the second is why this module has two
//! entry points:
//!
//! - Appending `z − 7` to a correct basis of `<x² − y, xy − 1>` gives a reduced Gröbner basis of a
//!   strictly larger ideal, and it passes all three checks.
//! - More sharply: for `I = <x²>` the single-element basis `G = {x}` passes all three — `x²`
//!   reduces to zero modulo `x`, a one-element basis has no S-polynomial, and `x` is monic and
//!   reduced — yet `<x²> ≠ <x>`.
//!
//! What excludes both is the derivation invariant (1), which is structural rather than checkable:
//! nothing in F4 can introduce a polynomial outside the ideal, because every matrix row is a
//! monomial multiple of a current basis element. A check for (1) would need an independent basis of
//! `I`, which is the thing being computed.
//!
//! So provenance is a **parameter**, not an assumption:
//!
//! - [`certify_f4_output`] is for a basis this crate's F4 produced from these generators. It
//!   records that the derivation is assumed, and [`CertificationReport::is_complete`] can return
//!   true.
//! - [`certify_submitted_basis`] is for a basis from anywhere else. `is_complete` is then **always
//!   false**, however the checks went, and [`CertificationReport::checks_passed`] is the meaningful
//!   result.
//!
//! A caller who hands in an arbitrary basis therefore cannot get a completeness claim the checks do
//! not support. The structural invariant is itself checked against an independent Buchberger basis
//! in `test_certification_agrees_with_buchberger`.
//!
//! # Cost
//!
//! (3) is `|G|²/2` normal forms and each normal form divides against all of `G`, so certification
//! is quadratic in the basis and not cheap: on a 105-element basis it is some 5 500 divisions.
//! **That is the point of reporting it separately** — the plan's §8.5 requires a strategy that
//! skips work to be compared on its total including the check, and a saving the check erases is not
//! a saving.

use std::time::{Duration, Instant};

use crate::{
    grobner::{pairs::divides, s_polynomial},
    poly::MonomialOrder,
    FiniteField, MultivariatePolynomial,
};

/// Where a basis came from, which decides what certifying it can establish.
///
/// See the module documentation: the runtime checks give `I ⊆ <G>` and cannot give `<G> ⊆ I`, so the
/// reverse containment has to come from provenance or not at all.
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

    // (3) Buchberger's criterion.
    let nonzero: Vec<&MultivariatePolynomial<N, F>> =
        basis.iter().filter(|p| !p.is_zero()).collect();
    let mut checked = 0;
    for (index, f) in nonzero.iter().enumerate() {
        for g in nonzero.iter().skip(index + 1) {
            checked += 1;
            if !s_polynomial(f, g, order)
                .normal_form(basis, order)
                .is_zero()
            {
                report.s_polynomials_checked = checked;
                report.elapsed = at.elapsed();
                return report;
            }
        }
    }
    report.buchberger_criterion = true;
    report.s_polynomials_checked = checked;

    // (4) Reducedness.
    report.reduced = is_reduced(&nonzero, basis, order);
    report.elapsed = at.elapsed();
    report
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
    use super::{certify_f4_output, certify_submitted_basis, Provenance};
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura},
            buchberger, f4,
        },
        poly::MonomialOrder,
        FiniteField, MultivariatePolynomial,
    };

    type F = Zp2147483647;
    const ALL_ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

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

    /// Certification rejects a basis with one element removed.
    ///
    /// The adversarial case the plan asks for, and the reason generator containment is checked and
    /// not only Buchberger's criterion: a truncated basis is still contained in the ideal, so
    /// nothing about *where it came from* distinguishes it.
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

    /// A certified basis agrees with the independent Buchberger engine.
    ///
    /// The structural invariant `G ⊆ I` is not something a run can check, so this is the closest
    /// an automated check comes: a reduced Gröbner basis is unique for an ideal and an order, so
    /// equality with a basis computed by a different algorithm establishes both containments.
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
            }
        }
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
