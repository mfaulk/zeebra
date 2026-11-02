//! Faugère's F4 algorithm for computing a Gröbner basis.
//!
//! Buchberger reduces one S-polynomial at a time and throws most of that work away: on katsura-5
//! under grevlex, 39 of 49 reductions produce zero. F4 instead takes a whole batch of critical
//! pairs, works out symbolically which polynomial multiples the batch's reductions could possibly
//! need, lays them out as the rows of one sparse matrix over a finite field, and reduces the lot
//! by Gaussian elimination. The cancellations Buchberger pays full price to rediscover become row
//! operations shared across the batch.
//!
//! The pipeline is one module per stage:
//!
//! - [`symbolic`] turns a batch of pairs into a set of rows closed under reduction.
//! - [`macaulay`] lays those rows out as a sparse matrix with monomials for columns.
//! - [`crate::linalg::sparse`] reduces it.
//! - [`reduction`] extracts the rows whose leading monomial is new.
//!
//! [`super::buchberger`] is unchanged and remains the correctness oracle.
//!
//! See Faugère, J.-C. (1999), *A new efficient algorithm for computing Gröbner bases (F4)*,
//! Journal of Pure and Applied Algebra 139, 61-88, and `docs/MILESTONE-F4.md` for the invariants
//! this implementation is built on.

pub mod macaulay;
pub mod options;
pub mod reduction;
pub mod statistics;
pub mod symbolic;

#[cfg(test)]
mod tests;

pub use macaulay::{BuildBudgetExceeded, MacaulayMatrix};
pub use options::{F4Error, F4Options};
pub use reduction::{reduce_batch, BatchOutcome};
pub use statistics::{BatchStatistics, F4Statistics};
pub use symbolic::{
    symbolic_preprocessing, symbolic_preprocessing_within, MonicBasis, MonicElement, Preprocessed,
    PreprocessedRow, RowBudgetExceeded, RowKind,
};

use crate::{
    grobner::{buchberger::reduce_grobner_basis, pairs::are_relatively_prime, pairs::PairQueue},
    poly::MonomialOrder,
    FiniteField, MultivariatePolynomial,
};

/// The reduced Gröbner basis for the given polynomials, with respect to the given monomial order.
///
/// The same contract as [`super::buchberger`]: zero generators are ignored, duplicates are
/// dropped, the empty basis is returned for the zero ideal, `{1}` for an inconsistent system, and
/// the result is sorted by leading monomial in descending order. A reduced Gröbner basis is unique
/// for a given ideal and order, so the two functions return exactly the same thing.
///
/// # Errors
/// Returns an [`F4Error`] if a matrix or its elimination exceeds a limit in [`F4Options::default`].
/// A successful return is always a complete basis; nothing partial is ever returned as though it
/// were finished.
pub fn f4<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Result<Vec<MultivariatePolynomial<N, F>>, F4Error> {
    f4_with_options(generators, order, &F4Options::default()).map(|(basis, _)| basis)
}

/// As [`f4`], under the given limits, additionally reporting the work performed.
pub fn f4_with_options<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> Result<(Vec<MultivariatePolynomial<N, F>>, F4Statistics), F4Error> {
    let mut statistics = F4Statistics::default();

    // A batch of no pairs makes no progress, so a zero limit is unsatisfiable rather than merely
    // strict. Rejected here, which is also what keeps `PairQueue::select_batch`'s precondition
    // from being reachable through this function.
    if options.max_pairs_per_batch == Some(0) {
        return Err(F4Error::InvalidOptions {
            reason: "max_pairs_per_batch of zero would select no pairs and make no progress",
        });
    }

    // A zero generator contributes nothing to the ideal, and would otherwise reach
    // `leading_coefficient().inverse()` with a zero coefficient. Duplicates are dropped too, so
    // they cannot produce pairs with themselves. Identical to Buchberger's handling, deliberately.
    let mut basis: Vec<MultivariatePolynomial<N, F>> = Vec::new();
    for p in generators.iter().filter(|p| !p.is_zero()) {
        let monic = p.scale(&p.leading_coefficient(order).inverse());
        if !basis.contains(&monic) {
            basis.push(monic);
        }
    }
    if basis.is_empty() {
        return Ok((Vec::new(), statistics));
    }

    // The limit is on the basis, so it applies to the generators the caller supplied and not only
    // to what F4 appends. Checking it solely after an append let a system whose initial basis
    // already exceeded the limit return successfully, provided no candidate was ever produced —
    // `<x, y>` under a limit of one has its only pair eliminated by the product criterion, so
    // nothing is appended and nothing was checked.
    check_basis_size(basis.len(), options)?;

    let mut monic = MonicBasis::new(&basis, order);
    let mut pending = PairQueue::seeded(&basis, order);

    // Terminates because each batch either consumes pairs without adding any, or produces a
    // candidate whose leading monomial is outside the leading-term ideal of the current basis —
    // which therefore grows strictly. An ascending chain of monomial ideals stabilizes, by
    // Dickson's lemma, so only finitely many candidates are ever produced.
    while !pending.is_empty() {
        let selected = pending.select_batch(options.max_pairs_per_batch);
        statistics.pairs_considered += selected.len();

        // Buchberger's first criterion, applied pair by pair before the batch is built: a pair
        // whose leading monomials are relatively prime contributes two rows that cancel to nothing
        // new, so there is no reason to put them in the matrix.
        let batch: Vec<_> = selected
            .into_iter()
            .filter(|pair| {
                statistics.max_pair_degree = statistics.max_pair_degree.max(pair.degree);
                let eliminated = are_relatively_prime(
                    &monic.element(pair.left).leading_monomial,
                    &monic.element(pair.right).leading_monomial,
                );
                if eliminated {
                    statistics.pairs_eliminated_by_product_criterion += 1;
                }
                !eliminated
            })
            .collect();
        if batch.is_empty() {
            continue;
        }
        statistics.pairs_reduced += batch.len();

        // Checked here rather than at the top of the loop, so the limit counts matrices actually
        // built. A pass whose every pair is eliminated by the product criterion builds nothing and
        // must not consume a batch's worth of budget.
        if let Some(limit) = options.max_batches {
            if statistics.batches >= limit {
                return Err(F4Error::TooManyBatches { limit });
            }
        }

        let outcome = reduce_batch(&monic, &batch, order, options)?;
        statistics.record(&outcome.statistics);

        for candidate in outcome.candidates {
            statistics.max_terms = statistics.max_terms.max(candidate.terms().len());
            let added = basis.len();
            // Already monic: elimination normalized every pivot to one.
            monic.push(&candidate, order);
            basis.push(candidate);
            statistics.elements_added += 1;

            check_basis_size(basis.len(), options)?;

            // Only the pairs involving the new element are new.
            pending.push_pairs_with(&basis, added, order);
        }
    }

    Ok((reduce_grobner_basis(&basis, order), statistics))
}

/// Reject a basis larger than `options` allows.
fn check_basis_size(elements: usize, options: &F4Options) -> Result<(), F4Error> {
    match options.max_basis_elements {
        Some(limit) if elements > limit => Err(F4Error::TooManyBasisElements { elements, limit }),
        _ => Ok(()),
    }
}
