//! Exact reverse-inclusion identities use the original ordered generators; no engine provenance is trusted.

use super::{certify_submitted_basis, CertificationReport};
use crate::{FiniteField, Monomial, MonomialOrder, MultivariatePolynomial};
use std::{
    collections::BTreeMap,
    time::{Duration, Instant},
};

/// Bounds on witness verification only, excluding caller-owned inputs and legacy basis checks.
#[derive(Clone, Copy, Debug)]
pub struct MembershipLimits {
    /// Total stored terms across targets, generators and cofactors, counted before arithmetic.
    pub max_input_terms: usize,
    /// Total coefficient products across every witness row in one call.
    pub max_term_products: usize,
    /// Maximum nonzero terms in the running identity residual (not an RSS cap).
    pub max_live_terms: usize,
    /// Cooperative deadline checked before every residual insertion and term product.
    pub max_wall_time: Duration,
}

impl Default for MembershipLimits {
    fn default() -> Self {
        Self {
            max_input_terms: 100_000,
            max_term_products: 1_000_000,
            max_live_terms: 100_000,
            max_wall_time: Duration::from_secs(30),
        }
    }
}

/// The witness budget that was exhausted; no mathematical rejection is implied.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WitnessLimit {
    InputTerms,
    TermProducts,
    LiveTerms,
    WallTime,
}

/// Exact evidence outcome, kept separate from the existing basis checks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MembershipStatus {
    Verified,
    Invalid,
    Missing,
    ResourceLimited(WitnessLimit),
}

/// Malformed evidence; field and variable shape are enforced by the common `N, F` types.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WitnessError {
    CofactorCount { expected: usize, actual: usize },
    RowCount { expected: usize, actual: usize },
    OrderArity { expected: usize, actual: usize },
    ExponentOverflow,
}

impl std::fmt::Display for WitnessError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid ideal-membership witness: {self:?}")
    }
}
impl std::error::Error for WitnessError {}

/// Both ideal inclusions plus the reduced Gröbner checks, without assuming F4 provenance.
#[derive(Clone, Debug)]
pub struct WitnessCertificationReport {
    pub membership: MembershipStatus,
    /// Absent when reverse-inclusion evidence is missing, false, or resource-limited.
    /// These legacy checks have no witness-budget enforcement.
    pub certification: Option<CertificationReport>,
    pub witness_elapsed: Duration,
}
impl WitnessCertificationReport {
    pub fn is_complete(&self) -> bool {
        self.membership == MembershipStatus::Verified
            && self
                .certification
                .as_ref()
                .is_some_and(CertificationReport::checks_passed)
    }
}

struct Budget<'a> {
    limits: &'a MembershipLimits,
    at: Instant,
    products: usize,
}
impl Budget<'_> {
    fn deadline(&self) -> Result<(), WitnessLimit> {
        if self.at.elapsed() >= self.limits.max_wall_time {
            Err(WitnessLimit::WallTime)
        } else {
            Ok(())
        }
    }
}

fn insert<const N: usize, F: FiniteField>(
    residual: &mut BTreeMap<Monomial<N>, F>,
    monomial: Monomial<N>,
    coefficient: F,
    budget: &Budget<'_>,
) -> Result<(), WitnessLimit> {
    budget.deadline()?;
    if coefficient.is_zero() {
        return Ok(());
    }
    if let Some(current) = residual.get_mut(&monomial) {
        *current += coefficient;
        if current.is_zero() {
            residual.remove(&monomial);
        }
    } else {
        if residual.len() >= budget.limits.max_live_terms {
            return Err(WitnessLimit::LiveTerms);
        }
        residual.insert(monomial, coefficient);
    }
    Ok(())
}

fn verify_row<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    target: &MultivariatePolynomial<N, F>,
    cofactors: &[MultivariatePolynomial<N, F>],
    budget: &mut Budget<'_>,
) -> Result<MembershipStatus, WitnessError> {
    let mut residual = BTreeMap::new();
    for (&m, &c) in target.terms() {
        if let Err(limit) = insert(&mut residual, m, -c, budget) {
            return Ok(MembershipStatus::ResourceLimited(limit));
        }
    }
    for (generator, cofactor) in generators.iter().zip(cofactors) {
        for (g, &gc) in generator.terms() {
            for (h, &hc) in cofactor.terms() {
                if let Err(limit) = budget.deadline() {
                    return Ok(MembershipStatus::ResourceLimited(limit));
                }
                if budget.products >= budget.limits.max_term_products {
                    return Ok(MembershipStatus::ResourceLimited(
                        WitnessLimit::TermProducts,
                    ));
                }
                budget.products += 1;
                let mut exponents = [0; N];
                for (i, e) in exponents.iter_mut().enumerate() {
                    *e = g.exponents()[i]
                        .checked_add(h.exponents()[i])
                        .ok_or(WitnessError::ExponentOverflow)?;
                }
                if let Err(limit) =
                    insert(&mut residual, Monomial::new(&exponents), gc * hc, budget)
                {
                    return Ok(MembershipStatus::ResourceLimited(limit));
                }
            }
        }
    }
    Ok(if residual.is_empty() {
        MembershipStatus::Verified
    } else {
        MembershipStatus::Invalid
    })
}

/// Verify `target = sum(cofactors[i] * generators[i])` by exact arithmetic.
///
/// Empty generators certify only zero; zero and duplicate generators keep their positions.
/// A unit generator follows the same identity rule. Types bind the field and variable positions;
/// variable names are presentation only. This proves membership, not a Gröbner basis property.
/// Bounds stop before allocations beyond the live-term cap; BTree nodes and coefficient storage
/// still have allocator overhead, so this is not a process-memory bound.
pub fn verify_ideal_membership<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    target: &MultivariatePolynomial<N, F>,
    cofactors: &[MultivariatePolynomial<N, F>],
    limits: &MembershipLimits,
) -> Result<MembershipStatus, WitnessError> {
    check_row_length(generators.len(), cofactors.len())?;
    let mut budget = Budget {
        limits,
        at: Instant::now(),
        products: 0,
    };
    let count = generators
        .iter()
        .chain(std::iter::once(target))
        .chain(cofactors);
    if let Err(limit) = count_terms(count, &budget) {
        return Ok(MembershipStatus::ResourceLimited(limit));
    }
    verify_row(generators, target, cofactors, &mut budget)
}

fn count_terms<'a, const N: usize, F: FiniteField + 'a>(
    polynomials: impl Iterator<Item = &'a MultivariatePolynomial<N, F>>,
    budget: &Budget<'_>,
) -> Result<(), WitnessLimit> {
    let mut total = 0usize;
    budget.deadline()?;
    for p in polynomials {
        budget.deadline()?;
        total = total
            .checked_add(p.terms().len())
            .ok_or(WitnessLimit::InputTerms)?;
        if total > budget.limits.max_input_terms {
            return Err(WitnessLimit::InputTerms);
        }
    }
    Ok(())
}
fn check_row_length(expected: usize, actual: usize) -> Result<(), WitnessError> {
    if expected != actual {
        Err(WitnessError::CofactorCount { expected, actual })
    } else {
        Ok(())
    }
}

/// Certify a submitted basis with one exact cofactor row per basis polynomial.
///
/// `None` means missing evidence; `Some(&[])` proves reverse inclusion for an empty basis.
/// Malformed row counts and order arity return typed errors before comparisons. False or
/// resource-limited evidence never yields completeness. Only after all identities pass do the
/// existing forward-inclusion, Buchberger and reducedness checks run; **those checks are unbounded**.
/// For untrusted large bases use an external process time/memory cap as well.
pub fn certify_submitted_basis_with_witnesses<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    basis: &[MultivariatePolynomial<N, F>],
    witnesses: Option<&[Vec<MultivariatePolynomial<N, F>>]>,
    order: MonomialOrder,
    limits: &MembershipLimits,
) -> Result<WitnessCertificationReport, WitnessError> {
    if let Some(actual) = order.arity() {
        if actual != N {
            return Err(WitnessError::OrderArity {
                expected: N,
                actual,
            });
        }
    }
    let at = Instant::now();
    let mut report = WitnessCertificationReport {
        membership: MembershipStatus::Missing,
        certification: None,
        witness_elapsed: Duration::ZERO,
    };
    let Some(rows) = witnesses else {
        report.witness_elapsed = at.elapsed();
        return Ok(report);
    };
    if rows.len() != basis.len() {
        return Err(WitnessError::RowCount {
            expected: basis.len(),
            actual: rows.len(),
        });
    }
    for row in rows {
        check_row_length(generators.len(), row.len())?;
    }
    let mut budget = Budget {
        limits,
        at,
        products: 0,
    };
    if let Err(limit) = count_terms(
        generators.iter().chain(basis).chain(rows.iter().flatten()),
        &budget,
    ) {
        report.membership = MembershipStatus::ResourceLimited(limit);
    } else {
        report.membership = MembershipStatus::Verified;
        for (target, row) in basis.iter().zip(rows) {
            report.membership = verify_row(generators, target, row, &mut budget)?;
            if report.membership != MembershipStatus::Verified {
                break;
            }
        }
    }
    report.witness_elapsed = at.elapsed();
    if report.membership == MembershipStatus::Verified {
        report.certification = Some(certify_submitted_basis(generators, basis, order));
    }
    Ok(report)
}
