//! Exact decomposition of an F4 computation into disjoint variable components (#1036).
//!
//! When the equation–variable incidence graph of the generators splits — every generator lies in
//! `K[X_i]` for exactly one block `X_i` of a partition `X = X_1 ⊔ … ⊔ X_k ⊔ U` of the variables,
//! `U` the unused ones — [`f4_decomposed`] computes each block's reduced basis separately and
//! returns their union. That union **is** the reduced Gröbner basis of the whole ideal under the
//! requested order, not an approximation of it:
//!
//! 1. **Induced order.** The restriction of any monomial order on `K[X]` to the monomials of
//!    `K[X_i]` is a monomial order on `K[X_i]`. Each component runs in the full `N`-variable ring
//!    with only its own generators, so every polynomial it ever forms lies in `K[X_i]` and is
//!    compared by exactly that restriction. Nothing about lex, block or weighted orders needs
//!    translating: the component *is* the requested order on a subring.
//! 2. **Gröbner property.** For `f ∈ K[X_i]` the leading monomial is a monomial in `X_i`. So for
//!    `g ∈ G_i`, `h ∈ G_j`, `i ≠ j`, the leading monomials share no variable and the S-pair
//!    reduces to zero by Buchberger's product criterion. Within a component, `G_i` is a Gröbner
//!    basis of `⟨F_i⟩ ⊂ K[X_i]`, and stays one for the extension `⟨F_i⟩·K[X]` because `K[X]` is
//!    free over `K[X_i]` (equivalently: its S-pairs are the same polynomials in either ring). All
//!    S-pairs of `G = ∪ G_i` therefore reduce to zero, and `⟨G⟩ = Σ ⟨F_i⟩ = ⟨F⟩`.
//! 3. **Reducedness.** Each `G_i` is reduced and monic. A term of `g ∈ G_i` is a monomial in
//!    `X_i`; `LM(h)` for `h ∈ G_j`, `j ≠ i`, is a *nonconstant* monomial in `X_j`, which divides no
//!    monomial in `X_i`. So no term of any element is divisible by another element's leading
//!    monomial, and `G` is reduced. Sorting the union descending by leading monomial reproduces
//!    the undecomposed engine's output order, so the two are equal as vectors.
//! 4. **Unit ideal.** If some `G_i = {1}` then `1 ∈ ⟨F⟩` and the answer is `{1}`. The union would
//!    not be reduced (1 divides everything), so this is a separate route, not a special union.
//! 5. **Degenerate generators.** Zero generators belong to no component and are dropped. A
//!    nonzero constant puts 1 in the ideal before anything is decomposed.
//!
//! # One budget
//!
//! The caller's [`F4Options`] limits are one allowance for the whole call, not one per component:
//!
//! - `max_wall_time` is a deadline from entry; each component and the fallback get what is left.
//! - `max_batches` and `max_basis_elements` are charged with every component's batches and
//!   appended elements, including work later discarded by a fallback.
//! - `max_live_bytes` bounds one batch's matrix. Sequential components keep earlier outputs alive
//!   while a later one runs, so each component's matrix allowance is reduced by the bytes of term
//!   payload already retained (`size_of::<(Monomial<N>, F)>()` per term, the same payload-only
//!   accounting the matrix budget uses). A component that would start with nothing left is refused.
//! - `cancel`, when given, is checked at every batch of every component and of the fallback, and
//!   between components.
//!
//! A component refused by a **resource** limit triggers the undecomposed fallback on the
//! remaining budget: retained outputs are dropped first, so it has the full matrix byte allowance,
//! but never a fresh clock or fresh batch count. Time stops, cancellation, invalid options and
//! certification failures are returned as they are, since the fallback could not do better.
//!
//! Components run one after another. Parallelism across components, if it is ever tried, must
//! split the caller's worker cap rather than give each component the whole of it.
//!
//! # Engines
//!
//! Each component runs the route the options select: conventional F4, or under
//! [`GradedEngine::Adaptive`] the same dispatch [`f4_with_options`](super::f4_with_options) uses.
//! The adaptive dispatch takes no observer, so under it `cancel` is honoured between components
//! and in the fallback only.

use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use crate::{
    grobner::{
        f4::{
            f4_observed_reported, f4_reported, BatchObserver, F4Error, F4Options, F4Statistics,
            GradedEngine, MonicBasis, StopKind,
        },
        pairs::CriticalPair,
        planning::structure::{incidence, IncidenceComponent},
    },
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

#[cfg(test)]
mod tests;

/// Which way [`f4_decomposed`] produced its answer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DecomposeRoute {
    /// A nonzero constant generator, or a component whose basis is `{1}`: the answer is `{1}`.
    Unit,
    /// At most one component, so the caller's route ran once on the whole input.
    Undivided,
    /// Two or more components, each solved on its own, and their bases combined.
    Decomposed,
    /// Component `after` (zero-based) was refused by `refusal`; the undecomposed computation ran
    /// on what remained of the budget.
    FellBack {
        /// The index of the refused component, so `after` components finished before it.
        after: usize,
        /// The refusal that triggered the fallback.
        refusal: F4Error,
    },
}

/// One component as [`f4_decomposed`] ran it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ComponentReport {
    /// Variable indices, ascending.
    pub variables: Vec<usize>,
    /// Indices into the caller's generators, ascending.
    pub generators: Vec<usize>,
    /// What this component's computation cost, on refusal as well as success.
    pub statistics: F4Statistics,
    /// Elements of this component's reduced basis, zero if it was refused.
    pub basis_len: usize,
}

/// What [`f4_decomposed`] did and what it cost.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecomposeReport {
    /// The route taken.
    pub route: DecomposeRoute,
    /// The components that ran, in order, the refused one included. Empty on a constant
    /// generator; for [`DecomposeRoute::Undivided`] the one entry is the whole input.
    pub components: Vec<ComponentReport>,
    /// Variables in no generator, ascending.
    pub unused_variables: Vec<usize>,
    /// The undecomposed fallback's statistics, when it ran.
    pub fallback: Option<F4Statistics>,
    /// The most basis terms held from finished components while a later one ran.
    pub peak_retained_terms: usize,
    /// [`Self::peak_retained_terms`] in payload bytes, as charged to `max_live_bytes`.
    pub peak_retained_bytes: usize,
    /// How long incidence detection took.
    pub detection: Duration,
}

/// The reduced Gröbner basis of `generators` under `order`, computed component by component when
/// the generators split into disjoint variable blocks. See the [module documentation](self) for
/// why the result equals the undecomposed one, and how the budget is shared.
///
/// Returns the report beside the result so the work is visible on refusal too.
///
/// # Errors
/// As [`f4_with_options`](super::f4_with_options), plus [`F4Error::StoppedByObserver`] when
/// `cancel` is set, and [`F4Error::TooManyLiveBytes`] as the refusal that starts the fallback when
/// retained component outputs leave a later component no matrix allowance.
pub fn f4_decomposed<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
    cancel: Option<&AtomicBool>,
) -> (
    Result<Vec<MultivariatePolynomial<N, F>>, F4Error>,
    DecomposeReport,
) {
    let started = Instant::now();
    // Width is not needed here; a zero cap makes it free.
    let structure = incidence(generators, 0);
    let mut report = DecomposeReport {
        route: DecomposeRoute::Undivided,
        components: Vec::new(),
        unused_variables: structure.unused_variables,
        fallback: None,
        peak_retained_terms: 0,
        peak_retained_bytes: 0,
        detection: started.elapsed(),
    };
    if structure.constant_generators > 0 {
        report.route = DecomposeRoute::Unit;
        return (Ok(vec![MultivariatePolynomial::one()]), report);
    }

    let mut budget = Budget::new(options, started);
    if structure.components.len() <= 1 {
        let component = structure.components.into_iter().next().unwrap_or_default();
        let (basis, statistics) = run(generators, order, &budget.options(0), cancel);
        report
            .components
            .push(component_report(component, basis_len(&basis), statistics));
        return (basis, report);
    }

    report.route = DecomposeRoute::Decomposed;
    let term_bytes = size_of::<(Monomial<N>, F)>();
    let mut retained: Vec<MultivariatePolynomial<N, F>> = Vec::new();
    let mut retained_terms = 0usize;
    for (index, component) in structure.components.into_iter().enumerate() {
        if cancel.is_some_and(|c| c.load(Ordering::Relaxed)) {
            return (Err(F4Error::StoppedByObserver), report);
        }
        // F4 always reduces one batch before reading its clock, so a spent deadline is enforced
        // here rather than granting every later component a batch.
        if let Some(stop) = budget.expired() {
            return (Err(stop), report);
        }
        let retained_bytes = retained_terms.saturating_mul(term_bytes);
        report.peak_retained_terms = report.peak_retained_terms.max(retained_terms);
        report.peak_retained_bytes = report.peak_retained_bytes.max(retained_bytes);

        let outcome = if retained_bytes >= options.max_live_bytes {
            report
                .components
                .push(component_report(component, 0, F4Statistics::default()));
            Err(F4Error::TooManyLiveBytes {
                bytes: retained_bytes,
                limit: options.max_live_bytes,
            })
        } else {
            let local: Vec<_> = component
                .generators
                .iter()
                .map(|&g| generators[g].clone())
                .collect();
            let (basis, statistics) = run(&local, order, &budget.options(retained_bytes), cancel);
            budget.charge(&statistics);
            report
                .components
                .push(component_report(component, basis_len(&basis), statistics));
            basis
        };

        match outcome {
            Ok(basis) if basis.len() == 1 && basis[0].is_constant() => {
                report.route = DecomposeRoute::Unit;
                return (Ok(basis), report);
            }
            Ok(basis) => {
                retained_terms += basis.iter().map(|p| p.terms().len()).sum::<usize>();
                retained.extend(basis);
            }
            Err(refusal) if refusal.stop_kind() == StopKind::Resource => {
                drop(retained);
                if let Some(stop) = budget.expired() {
                    return (Err(stop), report);
                }
                report.route = DecomposeRoute::FellBack {
                    after: index,
                    refusal,
                };
                let (basis, statistics) = run(generators, order, &budget.options(0), cancel);
                report.fallback = Some(statistics);
                return (basis, report);
            }
            Err(stop) => return (Err(stop), report),
        }
    }

    retained.sort_by(|a, b| order.cmp(&b.leading_monomial(order), &a.leading_monomial(order)));
    (Ok(retained), report)
}

fn component_report(
    component: IncidenceComponent,
    basis_len: usize,
    statistics: F4Statistics,
) -> ComponentReport {
    ComponentReport {
        variables: component.variables,
        generators: component.generators,
        statistics,
        basis_len,
    }
}

fn basis_len<T>(basis: &Result<Vec<T>, F4Error>) -> usize {
    basis.as_ref().map_or(0, Vec::len)
}

/// The caller's route on one set of generators.
fn run<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
    cancel: Option<&AtomicBool>,
) -> (
    Result<Vec<MultivariatePolynomial<N, F>>, F4Error>,
    F4Statistics,
) {
    if cancel.is_some_and(|c| c.load(Ordering::Relaxed)) {
        return (Err(F4Error::StoppedByObserver), F4Statistics::default());
    }
    match (options.graded_engine, cancel) {
        (GradedEngine::Adaptive, _) | (_, None) => f4_reported(generators, order, options),
        (GradedEngine::Conventional, Some(flag)) => {
            f4_observed_reported(generators, order, options, &mut Cancel(flag))
        }
    }
}

/// The caller's limits, less what earlier components spent.
struct Budget<'a> {
    caller: &'a F4Options,
    started: Instant,
    batches: usize,
    elements: usize,
}

impl<'a> Budget<'a> {
    fn new(caller: &'a F4Options, started: Instant) -> Self {
        Self {
            caller,
            started,
            batches: 0,
            elements: 0,
        }
    }

    fn charge(&mut self, statistics: &F4Statistics) {
        self.batches += statistics.batches;
        self.elements += statistics.elements_added;
    }

    /// The time stop, if the caller's deadline has already passed.
    fn expired(&self) -> Option<F4Error> {
        let limit = self.caller.max_wall_time?;
        let elapsed = self.started.elapsed();
        (elapsed >= limit).then(|| F4Error::TimeBudgetExceeded {
            degree: 0,
            elapsed_millis: elapsed.as_millis().min(u128::from(u64::MAX)) as u64,
            budget_millis: limit.as_millis().min(u128::from(u64::MAX)) as u64,
        })
    }

    /// Options for the next run, `retained_bytes` already held outside its matrices.
    fn options(&self, retained_bytes: usize) -> F4Options {
        let mut options = self.caller.clone();
        options.max_wall_time = self
            .caller
            .max_wall_time
            .map(|limit| limit.saturating_sub(self.started.elapsed()));
        options.max_batches = self
            .caller
            .max_batches
            .map(|limit| limit.saturating_sub(self.batches));
        options.max_basis_elements = self
            .caller
            .max_basis_elements
            .map(|limit| limit.saturating_sub(self.elements));
        options.max_live_bytes = self.caller.max_live_bytes - retained_bytes;
        options
    }
}

/// Stops a conventional F4 run at its next batch once the flag is set.
struct Cancel<'a>(&'a AtomicBool);

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for Cancel<'_> {
    fn batch(&mut self, _basis: &MonicBasis<N, F>, _pairs: &[CriticalPair<N>]) {}

    fn should_stop(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }
}
