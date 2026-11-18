//! Certification checks forward inclusion, Buchberger's criterion and reducedness.
//!
//! F4 output assumes reverse inclusion from row derivation. Submitted bases require exact
//! cofactor identities through [`super::membership::certify_submitted_basis_with_witnesses`]
//! before both ideal inclusions are established. The legacy submitted entry point stays incomplete.
//!
//! Product and Gebauer–Möller criteria depend only on leading monomials and are safe to replay.
//! The engine's chain criterion relies on already processed pairs, unavailable to a verifier;
//! enabling it here could silently accept a non-basis. Certification costs are reported separately.
//!
//! The reductions are independent, so [`certify_f4_output_with_workers`] spreads them over threads;
//! its report, counts included, is the serial one at every worker count (#887).
//!
//! [`certify_f4_output_within`] bounds the checks by their own wall budget, checked between
//! reductions. A stop is a [`CertificationStopped`], a separate type from the report, so running out
//! of time can never be read as a rejection; it says how far the serial order was verified (#899).

use std::{
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
    time::{Duration, Instant},
};

use crate::{
    fields::ConcurrentJob,
    grobner::{
        pairs::{are_relatively_prime, divides, CriterionCounts, PairCriteria, PairQueue},
        s_polynomial,
    },
    poly::{DivisionRoute, MonomialOrder, PreparedDivisors},
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

/// The check a budgeted certification was in when its budget ran out.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CertificationStage {
    /// Reducing the input generators modulo the basis.
    Generators,
    /// Reducing the S-polynomials Buchberger's criterion names.
    BuchbergerCriterion,
    /// Checking that the basis is reduced. Every normal form had been checked.
    Reducedness,
}

/// How far a certification got before its wall budget ran out. **Not a verdict.**
///
/// Returned by [`certify_f4_output_within`] in place of a [`CertificationReport`], so that a stop
/// has no `first_failure` to misread: nothing in it says the basis failed. A defect found before the
/// budget ran out is reported as a stop too unless every reduction before it in the serial order had
/// finished, because only then are the rejection's counts the serial pass's (#887).
///
/// The counts are verified prefixes of the serial order: the first `generators_checked` nonzero
/// generators, and the first `s_polynomials_checked` kept pairs, all reduced to zero. Parallel
/// workers may have finished reductions past the prefix; those are not counted, because they do
/// not extend what is established.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CertificationStopped {
    /// The check in progress when the budget was noticed.
    pub stage: CertificationStage,

    /// Leading nonzero generators verified to reduce to zero.
    pub generators_checked: usize,

    /// Nonzero generators the first check had to reduce.
    pub generators: usize,

    /// Leading S-polynomials, in the serial order, verified to reduce to zero.
    pub s_polynomials_checked: usize,

    /// S-polynomials Buchberger's criterion had to reduce after the criteria pruned the pairs.
    ///
    /// Zero when the stop came before [`CertificationStage::BuchbergerCriterion`]: the pairs are
    /// not formed until the generators pass.
    pub s_polynomials: usize,

    /// Pairs a criterion proved redundant, counted when the pairs were formed.
    pub s_polynomials_discarded: usize,

    /// Wall time from the start of certification to the stop.
    ///
    /// At least `budget`, and may exceed it by one reduction per worker: the deadline is checked
    /// between reductions, and a single normal form is not interruptible.
    pub elapsed: Duration,

    /// The budget that ran out.
    pub budget: Duration,

    /// Where the basis came from, as the caller stated it.
    pub provenance: Provenance,
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
///
/// Runs on the calling thread; [`certify_f4_output_with_workers`] spreads the reductions.
pub fn certify_f4_output<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> CertificationReport {
    certify_with(generators, basis, order, Provenance::F4Output, 1)
}

/// [`certify_f4_output`] with its normal forms spread over up to `workers` threads.
///
/// The report is [`certify_f4_output`]'s, field for field except [`CertificationReport::elapsed`],
/// at every worker count and under any scheduling: the reductions are independent, and a failure
/// is reported at the earliest position in the serial order, after exactly the work the serial
/// check would have done (#887). Zero means one worker. A field that cannot be shared across
/// threads runs on the calling thread.
pub fn certify_f4_output_with_workers<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    workers: usize,
) -> CertificationReport {
    certify_with(generators, basis, order, Provenance::F4Output, workers)
}

/// [`certify_f4_output_with_workers`] bounded by its own wall budget.
///
/// `Ok` carries exactly the report the unbudgeted call returns, timing aside, including a
/// rejection. `Err` means the budget ran out before a verdict, and says how far the checks got; it
/// is never a rejection. The deadline is checked before every reduction, on every worker, so a
/// stop overshoots `budget` by at most one normal form per worker, and every worker is joined
/// before this returns.
///
/// The budget is the certificate's own and starts when this is called; it is independent of
/// [`F4Options::max_wall_time`](super::F4Options::max_wall_time), which bounds the computation.
pub fn certify_f4_output_within<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    workers: usize,
    budget: Duration,
) -> Result<CertificationReport, CertificationStopped> {
    certify_budgeted(
        generators,
        basis,
        order,
        Provenance::F4Output,
        workers,
        Some(budget),
    )
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
    certify_with(generators, basis, order, Provenance::Submitted, 1)
}

/// The division route the certificate reduces by.
///
/// Both routes return the same remainder bit for bit, so this is a cost choice only. With divisors
/// prepared once, the merge certified Eco-12 at sixteen workers in 58 s against the heap's 66 s,
/// and Cyclic-7 in 30 ms against 68 ms (#887).
const CERTIFICATE_ROUTE: DivisionRoute = DivisionRoute::Merge;

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
    workers: usize,
) -> CertificationReport {
    certify_budgeted(generators, basis, order, provenance, workers, None)
        .unwrap_or_else(|_| unreachable!("a certification without a budget cannot run out of one"))
}

/// [`certify_with`], stopping between reductions once `budget` has elapsed.
fn certify_budgeted<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    provenance: Provenance,
    workers: usize,
    budget: Option<Duration>,
) -> Result<CertificationReport, CertificationStopped> {
    let at = Instant::now();
    let deadline = Deadline {
        at: budget.and_then(|budget| at.checked_add(budget)),
        budgeted: budget.is_some(),
    };
    let mut report = CertificationReport {
        provenance,
        ..CertificationReport::default()
    };
    let nonzero_generators: Vec<&MultivariatePolynomial<N, F>> =
        generators.iter().filter(|p| !p.is_zero()).collect();
    let mut stopped = CertificationStopped {
        stage: CertificationStage::Generators,
        generators_checked: 0,
        generators: nonzero_generators.len(),
        s_polynomials_checked: 0,
        s_polynomials: 0,
        s_polynomials_discarded: 0,
        elapsed: Duration::ZERO,
        budget: budget.unwrap_or_default(),
        provenance,
    };
    let stop = |mut stopped: CertificationStopped| {
        stopped.elapsed = at.elapsed();
        Err(stopped)
    };
    let divisors = PreparedDivisors::new(basis, order);

    // (2) F in <G>. First, because it is linear in the generators and it is the check a truncated
    // basis fails for sure.
    match first_irreducible(
        &divisors,
        Dividends::Generators(&nonzero_generators),
        workers,
        deadline,
    ) {
        Scan::Clean => report.generators_checked = nonzero_generators.len(),
        Scan::Irreducible(failure) => {
            report.generators_checked = failure + 1;
            report.elapsed = at.elapsed();
            return Ok(report);
        }
        Scan::Stopped { verified } => {
            stopped.generators_checked = verified;
            return stop(stopped);
        }
    }
    report.generators_in_basis = true;
    stopped.generators_checked = nonzero_generators.len();

    // (3) Buchberger's criterion, over the pairs no criterion proves redundant.
    stopped.stage = CertificationStage::BuchbergerCriterion;
    let nonzero: Vec<&MultivariatePolynomial<N, F>> =
        basis.iter().filter(|p| !p.is_zero()).collect();
    let check = check_buchberger_criterion(
        &nonzero,
        &divisors,
        order,
        &CERTIFICATION_CRITERIA,
        workers,
        deadline,
    );
    if let Some(verified) = check.stopped_at {
        stopped.s_polynomials_checked = verified;
        stopped.s_polynomials = check.checked;
        stopped.s_polynomials_discarded = check.discarded;
        return stop(stopped);
    }
    report.s_polynomials_checked = check.checked;
    report.s_polynomials_discarded = check.discarded;
    if !check.held {
        report.elapsed = at.elapsed();
        return Ok(report);
    }
    report.buchberger_criterion = true;

    // (4) Reducedness. Not interruptible, but it forms no normal form.
    if deadline.expired() {
        stopped.stage = CertificationStage::Reducedness;
        stopped.s_polynomials_checked = check.checked;
        stopped.s_polynomials = check.checked;
        stopped.s_polynomials_discarded = check.discarded;
        return stop(stopped);
    }
    report.reduced = is_reduced(&nonzero, order);
    report.elapsed = at.elapsed();
    Ok(report)
}

/// When a budgeted certification must stop, checked between reductions.
#[derive(Clone, Copy)]
struct Deadline {
    /// `None` with `budgeted` set means the budget is too large to represent, so never expires.
    at: Option<Instant>,
    budgeted: bool,
}

impl Deadline {
    /// No deadline: [`Self::expired`] is always false, and no clock is read.
    #[cfg(test)]
    const NONE: Self = Self {
        at: None,
        budgeted: false,
    };

    fn expired(&self) -> bool {
        self.at.is_some_and(|at| Instant::now() >= at)
    }
}

/// How a scan over the dividends ended.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Scan {
    /// Every dividend reduced to zero.
    Clean,
    /// The earliest dividend, in the serial order, whose normal form is nonzero; every one before
    /// it reduced to zero.
    Irreducible(usize),
    /// The deadline passed first. The first `verified` dividends reduced to zero.
    Stopped { verified: usize },
}

/// What Buchberger's criterion cost and whether it held.
struct PairCheck {
    /// Every S-polynomial that was formed reduced to zero.
    held: bool,

    /// Pairs whose S-polynomial was formed and reduced.
    checked: usize,

    /// Pairs a criterion proved redundant.
    discarded: usize,

    /// Set when the deadline passed first, to the verified prefix of the pairs; `checked` is then
    /// the number of pairs there were to reduce, and `held` is meaningless.
    stopped_at: Option<usize>,
}

/// Buchberger's criterion over the pairs `criteria` does not prove redundant.
///
/// `criteria` is a parameter only so that the tests can exercise each criterion on its own and
/// against the unpruned reference; the one production caller passes
/// [`CERTIFICATION_CRITERIA`]. Stops at the first S-polynomial, in the queue's order, that does not
/// reduce to zero, so the counts describe the work a serial pass performs at every worker count.
fn check_buchberger_criterion<const N: usize, F: FiniteField>(
    nonzero: &[&MultivariatePolynomial<N, F>],
    divisors: &PreparedDivisors<N, F>,
    order: MonomialOrder,
    criteria: &PairCriteria,
    workers: usize,
    deadline: Deadline,
) -> PairCheck {
    debug_assert!(
        !criteria.chain,
        "the chain criterion's witnesses are pairs that have been reduced, and a verification pass \
         has reduced nothing"
    );

    let leads: Vec<Monomial<N>> = nonzero.iter().map(|p| p.leading_monomial(order)).collect();
    let mut counts = CriterionCounts::default();
    let mut queue = PairQueue::<N>::seeded_from_leads(&leads, criteria, &mut counts);

    // The pairs to reduce, in the order a serial pass reduces them, each with the discards counted
    // before it: the queue is drained first so that the reductions can run in any order and a
    // failure can still be reported with exactly the serial pass's counts.
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    let mut discarded_before: Vec<usize> = Vec::new();
    while let Some(pair) = queue.pop() {
        // Gebauer–Möller's criterion F already applies this at insertion, so with both criteria on
        // it never fires. It is here so that the product criterion also stands alone.
        if criteria.product && are_relatively_prime(&leads[pair.left], &leads[pair.right]) {
            counts.product += 1;
            continue;
        }
        pairs.push((pair.left, pair.right));
        discarded_before.push(counts.total());
    }

    match first_irreducible(
        divisors,
        Dividends::SPolynomials {
            nonzero,
            pairs: &pairs,
            order,
        },
        workers,
        deadline,
    ) {
        Scan::Irreducible(at) => PairCheck {
            held: false,
            checked: at + 1,
            discarded: discarded_before[at],
            stopped_at: None,
        },
        Scan::Clean => PairCheck {
            held: true,
            checked: pairs.len(),
            discarded: counts.total(),
            stopped_at: None,
        },
        Scan::Stopped { verified } => PairCheck {
            held: false,
            checked: pairs.len(),
            discarded: counts.total(),
            stopped_at: Some(verified),
        },
    }
}

/// The polynomials a certificate check reduces, by position in the serial order.
#[derive(Clone, Copy)]
enum Dividends<'a, const N: usize, F: FiniteField> {
    Generators(&'a [&'a MultivariatePolynomial<N, F>]),
    SPolynomials {
        nonzero: &'a [&'a MultivariatePolynomial<N, F>],
        pairs: &'a [(usize, usize)],
        order: MonomialOrder,
    },
}

impl<const N: usize, F: FiniteField> Dividends<'_, N, F> {
    fn len(&self) -> usize {
        match self {
            Self::Generators(generators) => generators.len(),
            Self::SPolynomials { pairs, .. } => pairs.len(),
        }
    }

    /// True if the dividend at `position` has a nonzero normal form.
    fn irreducible(&self, position: usize, divisors: &PreparedDivisors<N, F>) -> bool {
        let remainder = match *self {
            Self::Generators(generators) => {
                divisors.normal_form(generators[position], CERTIFICATE_ROUTE)
            }
            Self::SPolynomials {
                nonzero,
                pairs,
                order,
            } => {
                let (left, right) = pairs[position];
                divisors.normal_form(
                    &s_polynomial(nonzero[left], nonzero[right], order),
                    CERTIFICATE_ROUTE,
                )
            }
        };
        !remainder.is_zero()
    }
}

/// The earliest position whose dividend does not reduce to zero, unless the deadline passes first.
///
/// With one worker, or a field that cannot be shared across threads, this is the serial scan.
fn first_irreducible<const N: usize, F: FiniteField>(
    divisors: &PreparedDivisors<N, F>,
    dividends: Dividends<'_, N, F>,
    workers: usize,
    deadline: Deadline,
) -> Scan {
    let search = Search {
        divisors,
        dividends,
        workers: workers.min(dividends.len()),
        deadline,
    };
    if search.workers <= 1 {
        return search.serial();
    }
    F::run_concurrent(search).unwrap_or_else(|search| search.serial())
}

/// [`first_irreducible`] as a job a thread-safe field can run on a team.
struct Search<'a, const N: usize, F: FiniteField> {
    divisors: &'a PreparedDivisors<N, F>,
    dividends: Dividends<'a, N, F>,
    workers: usize,
    deadline: Deadline,
}

impl<const N: usize, F: FiniteField> Search<'_, N, F> {
    fn serial(&self) -> Scan {
        for at in 0..self.dividends.len() {
            if self.deadline.expired() {
                return Scan::Stopped { verified: at };
            }
            if self.dividends.irreducible(at, self.divisors) {
                return Scan::Irreducible(at);
            }
        }
        Scan::Clean
    }
}

impl<const N: usize, F: FiniteField> ConcurrentJob<F> for Search<'_, N, F> {
    type Output = Scan;

    /// Workers claim positions in increasing order, one at a time because a reduction's cost
    /// varies by orders of magnitude, and skip any position past the earliest failure found so far.
    ///
    /// The result is deterministic: a position below the final minimum is never skipped, since
    /// skipping it would need a failure below it, so every position below the minimum was reduced
    /// and found to reduce to zero.
    ///
    /// Under a deadline each worker checks it before claiming, and the first to see it expired
    /// stops the rest at their next claim. Each position is marked when its reduction finishes, so
    /// the verified prefix is read off the marks once the scope has joined every worker. A failure
    /// is reported only if every position below it finished, which is exactly the unbudgeted
    /// result; otherwise the scan is a stop, since a failure whose serial counts are unknown is not
    /// reported as a rejection.
    fn run(self) -> Self::Output
    where
        F: Send + Sync,
    {
        let length = self.dividends.len();
        let next = AtomicUsize::new(0);
        let earliest = AtomicUsize::new(usize::MAX);
        let stopped = AtomicBool::new(false);
        let finished: Vec<AtomicBool> = if self.deadline.budgeted {
            (0..length).map(|_| AtomicBool::new(false)).collect()
        } else {
            Vec::new()
        };
        std::thread::scope(|scope| {
            for _ in 0..self.workers {
                scope.spawn(|| loop {
                    if stopped.load(Ordering::Relaxed) {
                        break;
                    }
                    if self.deadline.expired() {
                        stopped.store(true, Ordering::Relaxed);
                        break;
                    }
                    let at = next.fetch_add(1, Ordering::Relaxed);
                    if at >= length || at > earliest.load(Ordering::Relaxed) {
                        break;
                    }
                    if self.dividends.irreducible(at, self.divisors) {
                        earliest.fetch_min(at, Ordering::Relaxed);
                    }
                    if let Some(mark) = finished.get(at) {
                        mark.store(true, Ordering::Relaxed);
                    }
                });
            }
        });
        let earliest = earliest.into_inner();
        if stopped.into_inner() {
            let verified = finished
                .iter()
                .take_while(|mark| mark.load(Ordering::Relaxed))
                .count();
            if earliest < verified {
                Scan::Irreducible(earliest)
            } else if verified == length {
                Scan::Clean
            } else {
                Scan::Stopped { verified }
            }
        } else if earliest == usize::MAX {
            Scan::Clean
        } else {
            Scan::Irreducible(earliest)
        }
    }
}

/// True if the basis is monic, no leading monomial divides another's, and each element is its own
/// normal form modulo the others.
///
/// The last condition is tested as "no term of an element is divisible by another element's
/// leading monomial", which is the same condition: a normal form never holds such a term, and an
/// element without one is left unchanged by reduction. Testing monomials avoids cloning the basis
/// and rebuilding its reducers once per element, which is quadratic in the basis (#887).
fn is_reduced<const N: usize, F: FiniteField>(
    nonzero: &[&MultivariatePolynomial<N, F>],
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
        // Interreduced: no other element's leading monomial divides any term. Minimality has just
        // cleared the leading term, so this tests the tail.
        if polynomial.terms().iter().any(|(monomial, _)| {
            leads
                .iter()
                .enumerate()
                .any(|(other, lead)| other != index && divides(lead, monomial))
        }) {
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
    use std::{collections::HashSet, time::Duration};

    use super::{
        certify_f4_output, certify_f4_output_with_workers, certify_f4_output_within,
        certify_submitted_basis, CertificationReport, CertificationStage, PairCheck, Provenance,
        CERTIFICATION_CRITERIA,
    };
    use crate::{
        fields::{Zp2147483647, Zp32003},
        grobner::{
            benchmark_systems::{cyclic, katsura},
            buchberger, f4,
            pairs::{are_relatively_prime, CriterionCounts, PairCriteria, PairQueue},
            s_polynomial,
        },
        poly::{MonomialOrder, PreparedDivisors},
        FiniteField, Monomial, MultivariatePolynomial,
    };

    type F = Zp2147483647;

    /// The pruned check against `basis`, on the calling thread, for tests that vary the criteria.
    fn check_buchberger_criterion<const N: usize>(
        nonzero: &[&MultivariatePolynomial<N, F>],
        basis: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
        criteria: &PairCriteria,
    ) -> PairCheck {
        super::check_buchberger_criterion(
            nonzero,
            &PreparedDivisors::new(basis, order),
            order,
            criteria,
            1,
            super::Deadline::NONE,
        )
    }
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
    fn planted_defects<const N: usize, G: FiniteField>(
        basis: &[MultivariatePolynomial<N, G>],
    ) -> Vec<Vec<MultivariatePolynomial<N, G>>> {
        let one = MultivariatePolynomial::<N, G>::one();
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

    /// Worker counts the parallel certificate is compared at; seven does not divide the work evenly.
    const WORKER_COUNTS: [usize; 4] = [1, 2, 7, 16];

    /// A report with its timing removed, which is the only field allowed to vary between runs.
    fn untimed(report: CertificationReport) -> CertificationReport {
        CertificationReport {
            elapsed: Duration::ZERO,
            ..report
        }
    }

    /// The certificate's report, timing aside, is the serial one at every worker count on a basis
    /// that certifies.
    #[test]
    fn test_the_parallel_certificate_agrees_with_the_serial_one() {
        for order in ALL_ORDERS {
            let system: Vec<MultivariatePolynomial<5, F>> = katsura::<5, F>();
            let basis = f4(&system, order).expect("within limits");
            let serial = untimed(certify_f4_output(&system, &basis, order));
            assert!(serial.is_complete());
            for workers in WORKER_COUNTS {
                assert_eq!(
                    untimed(certify_f4_output_with_workers(
                        &system, &basis, order, workers
                    )),
                    serial,
                    "{} workers under {}",
                    workers,
                    order.name()
                );
            }
        }
    }

    /// Every planted defect is rejected at every worker count with the serial report's counts, so
    /// the verdict and the work it describes do not depend on scheduling.
    #[test]
    fn test_the_parallel_certificate_rejects_what_the_serial_one_rejects() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system: Vec<MultivariatePolynomial<4, F>> = cyclic::<4, F>();
        let basis = f4(&system, order).expect("within limits");
        let mut rejected = 0;
        for defect in planted_defects(&basis) {
            let serial = untimed(certify_f4_output(&system, &defect, order));
            if !serial.is_complete() {
                rejected += 1;
            }
            for workers in WORKER_COUNTS {
                assert_eq!(
                    untimed(certify_f4_output_with_workers(
                        &system, &defect, order, workers
                    )),
                    serial,
                    "{workers} workers"
                );
            }
        }
        assert!(rejected > 0, "the corpus must contain a rejected basis");
    }

    /// A non-Gröbner basis whose generators all reduce to zero is rejected on Buchberger's
    /// criterion itself, after the same number of S-polynomials at every worker count.
    #[test]
    fn test_the_parallel_certificate_rejects_a_non_groebner_basis() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let vars = ["x", "y", "z"];
        // The generators as their own basis: each reduces to zero modulo itself, and the pair's
        // S-polynomial reduces to y^2 - x, which no leading monomial divides.
        let system: Vec<MultivariatePolynomial<3, F>> =
            vec![parse("x^2 - y", vars), parse("x*y - 1", vars)];
        let serial = untimed(certify_f4_output(&system, &system, order));
        assert!(serial.generators_in_basis);
        assert!(!serial.buchberger_criterion);
        assert_eq!(serial.s_polynomials_checked, 1);
        for workers in WORKER_COUNTS {
            assert_eq!(
                untimed(certify_f4_output_with_workers(
                    &system, &system, order, workers
                )),
                serial
            );
        }
    }

    /// A basis with a tail term another element's leading monomial divides is not reduced, however
    /// minimal and monic it is.
    #[test]
    fn test_certification_detects_a_tail_that_is_not_interreduced() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let vars = ["x", "y", "z"];
        // {y, x + y}: a Gröbner basis of <x, y> with minimal monic leads whose second element's
        // tail is divisible by the first element's lead.
        let system: Vec<MultivariatePolynomial<3, F>> = vec![parse("x", vars), parse("y", vars)];
        let basis = vec![parse("y", vars), parse("x + y", vars)];
        for workers in WORKER_COUNTS {
            let report = certify_f4_output_with_workers(&system, &basis, order, workers);
            assert!(report.generators_in_basis && report.buchberger_criterion);
            assert!(!report.reduced, "{workers} workers");
        }
    }

    /// A zero certification budget on a basis that certifies is a typed stop before any reduction,
    /// never a rejection, at every worker count and in two fields.
    #[test]
    fn test_a_zero_budget_stops_rather_than_rejects() {
        fn check<G: FiniteField>() {
            let order = MonomialOrder::GradedReverseLexicographic;
            let system: Vec<MultivariatePolynomial<4, G>> = cyclic::<4, G>();
            let basis = f4(&system, order).expect("within limits");
            for workers in WORKER_COUNTS {
                let stopped =
                    certify_f4_output_within(&system, &basis, order, workers, Duration::ZERO)
                        .expect_err("a zero budget cannot finish a certificate");
                assert_eq!(
                    stopped.stage,
                    CertificationStage::Generators,
                    "{workers} workers"
                );
                assert_eq!(stopped.generators_checked, 0, "{workers} workers");
                assert_eq!(stopped.generators, system.len());
                assert_eq!(stopped.s_polynomials_checked, 0);
                assert_eq!(stopped.budget, Duration::ZERO);
                assert!(stopped.elapsed >= stopped.budget);
                assert_eq!(stopped.provenance, Provenance::F4Output);
            }
        }
        check::<F>();
        check::<Zp32003>();
    }

    /// A zero budget on a defective basis is still a stop and not a rejection: the verdict was
    /// never reached, so it is not reported.
    #[test]
    fn test_a_zero_budget_does_not_reject_a_defective_basis() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system: Vec<MultivariatePolynomial<4, F>> = cyclic::<4, F>();
        let basis = f4(&system, order).expect("within limits");
        for defect in planted_defects(&basis) {
            for workers in WORKER_COUNTS {
                assert!(
                    certify_f4_output_within(&system, &defect, order, workers, Duration::ZERO)
                        .is_err(),
                    "{workers} workers"
                );
            }
        }
    }

    /// An ample budget returns exactly the unbudgeted report, timing aside, for passing and
    /// rejected bases at every worker count and in two fields.
    #[test]
    fn test_an_ample_budget_leaves_the_report_unchanged() {
        fn check<G: FiniteField>() {
            let order = MonomialOrder::GradedReverseLexicographic;
            let system: Vec<MultivariatePolynomial<4, G>> = cyclic::<4, G>();
            let basis = f4(&system, order).expect("within limits");
            let mut bases = planted_defects(&basis);
            bases.push(basis);
            for candidate in &bases {
                let unbudgeted = untimed(certify_f4_output(&system, candidate, order));
                for workers in WORKER_COUNTS {
                    let budgeted = certify_f4_output_within(
                        &system,
                        candidate,
                        order,
                        workers,
                        Duration::from_secs(3600),
                    )
                    .expect("an hour is ample");
                    assert_eq!(untimed(budgeted), unbudgeted, "{workers} workers");
                }
            }
        }
        check::<F>();
        check::<Zp32003>();
    }

    /// Whatever a short budget allows, the outcome is either the unbudgeted report or a stop whose
    /// progress is a consistent prefix of the serial order, and a later run on the same inputs is
    /// unaffected (the scoped team was joined, not abandoned).
    #[test]
    fn test_a_short_budget_reports_a_consistent_prefix() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system: Vec<MultivariatePolynomial<5, F>> = katsura::<5, F>();
        let basis = f4(&system, order).expect("within limits");
        let unbudgeted = untimed(certify_f4_output(&system, &basis, order));
        for budget in [1, 20, 200, 2000].map(Duration::from_micros) {
            for workers in WORKER_COUNTS {
                match certify_f4_output_within(&system, &basis, order, workers, budget) {
                    Ok(report) => assert_eq!(untimed(report), unbudgeted),
                    Err(stopped) => {
                        assert!(stopped.elapsed >= budget);
                        assert!(stopped.generators_checked <= stopped.generators);
                        assert!(stopped.s_polynomials_checked <= stopped.s_polynomials);
                        match stopped.stage {
                            CertificationStage::Generators => {
                                assert!(stopped.generators_checked < stopped.generators);
                                assert_eq!(stopped.s_polynomials, 0);
                            }
                            CertificationStage::BuchbergerCriterion => {
                                assert_eq!(stopped.generators_checked, stopped.generators);
                                assert_eq!(stopped.s_polynomials, unbudgeted.s_polynomials_checked);
                                assert!(stopped.s_polynomials_checked < stopped.s_polynomials);
                            }
                            CertificationStage::Reducedness => {
                                assert_eq!(stopped.s_polynomials_checked, stopped.s_polynomials);
                            }
                        }
                    }
                }
                assert_eq!(
                    untimed(certify_f4_output_with_workers(
                        &system, &basis, order, workers
                    )),
                    unbudgeted,
                    "{workers} workers after a budgeted run"
                );
            }
        }
    }
}
