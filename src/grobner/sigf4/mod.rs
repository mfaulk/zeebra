//! Research-only signature-compatible F4 (#857, RFC `docs/research/signature-f4-rfc.md` design 1):
//! batched F4-RB under Schreyer shifted signatures, sig-lead-ratio rewriting, Koszul and zero-row
//! syzygies plus the product criterion, serial regular elimination, then the shipping
//! interreduction. Isolated from the shipping F4: nothing on that path reads this module.
//!
//! Correctness rests on Lairez Thm 62 (Algorithm 8): every row is reduced only by rows of strictly
//! smaller signature, a batch's rows are processed in increasing signature order, and its results
//! join the basis only after the batch. The reduced basis is unique, so the output must equal
//! [`crate::grobner::f4()`]'s coefficient for coefficient.

//!
//! Compiled into every build for [`crate::grobner::f4_signature`], the supported opt-in entry
//! (#905); this module and its research knobs are public only under `research-sigf4`.
#![cfg_attr(not(feature = "research-sigf4"), allow(dead_code))]

#[cfg(all(test, feature = "research-sigf4"))]
mod cascade_tests;
mod claim;
#[cfg(feature = "research-sigf4")]
pub mod corpus;
pub mod dispatch;
mod engine;
#[cfg(feature = "research-sigf4-replay")]
pub mod replay;
pub mod signature;
mod table;
#[cfg(feature = "research-sigf4-replay")]
pub use engine::symbolic_replay;
#[cfg(all(test, feature = "research-sigf4"))]
mod tests;
#[cfg(feature = "research-sigf4-usage")]
pub mod usage;

use std::time::Duration;

use crate::{grobner::f4::F4Error, poly::MonomialOrder, FiniteField, MultivariatePolynomial};

/// Budgets and checks. Not [`crate::grobner::F4Options`]: that struct is not `#[non_exhaustive]`,
/// so this engine takes its own (RFC §6).
#[derive(Clone, Debug)]
pub struct SigF4Options {
    /// Cooperative wall budget, checked between batches and inside interreduction.
    pub max_wall_time: Option<Duration>,
    /// Limit on the signature basis, which may outgrow the reduced basis (RS §B.4).
    pub max_basis_elements: Option<usize>,
    /// Rows per batch matrix, targets plus reducers.
    pub max_matrix_rows: usize,
    /// Columns per batch matrix.
    pub max_matrix_columns: usize,
    /// Run [`crate::grobner::f4::certify_f4_output`] on the result, on `workers` threads, and
    /// refuse a failure.
    pub certify: bool,
    /// The certificate's own wall budget, as [`crate::grobner::F4Options::max_certify_time`]: a
    /// stop is [`F4Error::CertificationTimeBudgetExceeded`], never a rejection.
    pub max_certify_time: Option<Duration>,
    /// Assert the signature discipline on every row operation and re-verify each new element's
    /// signature invariants. Expensive; for tests.
    pub check_signatures: bool,
    /// Threads for design 2's parallel pre-reduction against each batch's reducer block (RFC
    /// §6.1 item 1). `1` is design 1, fully serial. A field that is not `Send + Sync` runs the
    /// same pass serially.
    pub workers: usize,
    /// Finish each batch's cascade on `workers` threads under #902's "prereduce + claim" schedule
    /// (M31-S2, #904) instead of design 2's serial pass. Every result row equals design 1's.
    pub parallel_cascade: bool,
    /// Bytes one batch's elimination may hold, on either cascade: its sparse rows, pre-reduced
    /// and final rows, workspaces and pivot or coordination metadata. Crossing it abandons the
    /// batch with [`F4Error::TooManyLiveBytes`]. `None` is unbounded.
    pub max_live_bytes: Option<usize>,
    /// #1031: census every serial batch's reducer reuse into [`SigF4Statistics::reuse`]. Replays
    /// each elimination three times, so never on in a timed run.
    #[cfg(feature = "research-reuse")]
    pub reuse_census: bool,
    #[cfg(test)]
    pub(crate) adversary: Option<claim::Adversary>,
    /// Tests only: the column-space interreduction's live-entry budget, to force its fallback.
    #[cfg(test)]
    pub(crate) interreduction_live_entries: Option<usize>,
}

impl Default for SigF4Options {
    fn default() -> Self {
        Self {
            max_wall_time: None,
            max_basis_elements: None,
            max_matrix_rows: 2_000_000,
            max_matrix_columns: 2_000_000,
            certify: false,
            max_certify_time: None,
            check_signatures: false,
            workers: 1,
            parallel_cascade: false,
            max_live_bytes: Some(crate::grobner::F4Options::default().max_live_bytes),
            #[cfg(feature = "research-reuse")]
            reuse_census: false,
            #[cfg(test)]
            adversary: None,
            #[cfg(test)]
            interreduction_live_entries: None,
        }
    }
}

impl SigF4Options {
    /// Defaults plus certification and the exhaustive signature checks.
    pub fn checked() -> Self {
        Self {
            certify: true,
            check_signatures: true,
            ..Self::default()
        }
    }
}

/// Why the engine did not return a basis. A caller may fall back to the shipping F4 on any of
/// these (RFC §7).
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum SigF4Error {
    /// The order is not graded, or does not match the ring's arity.
    Unsupported { reason: &'static str },
    /// A budget, a cancellation or certification, in the shipping F4's terms.
    Budget(F4Error),
}

impl std::fmt::Display for SigF4Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported { reason } => {
                write!(f, "unsupported by the signature engine: {reason}")
            }
            Self::Budget(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for SigF4Error {}

/// The plan §2.2 quantities, labelled as RFC §10.1 reports them, plus bookkeeping cost.
#[derive(Clone, Debug, Default)]
pub struct SigF4Statistics {
    pub batches: usize,
    /// Pending signatures generated from basis-element pairs (inputs excluded).
    pub pairs_created: usize,
    /// Pairs whose two multiples have equal signature: not regular, never queued.
    pub pairs_singular: usize,
    /// Rejected by the product criterion: coprime leading monomials (EF §12). A coprime pair's
    /// signature is also its Koszul signature, so this count is the coprime syzygy source too.
    pub rejected_product: usize,
    /// Rejected by the syzygy criterion, the dividing signature being a Koszul syzygy.
    pub rejected_koszul: usize,
    /// Rejected by the syzygy criterion, the dividing signature coming from a zero row.
    pub rejected_zero_row: usize,
    /// Rejected by the sig-lead-ratio rewrite criterion (EF Algorithm 3).
    pub rejected_rewrite: usize,
    /// Pending entries with a signature another entry already holds (one per signature, EF L6.6).
    pub rejected_duplicate: usize,
    /// Rows reduced as S-pair or input reductants.
    pub targets: usize,
    /// Reducer multiples built by symbolic preprocessing.
    pub reducer_rows: usize,
    /// Targets that reduced to zero. Only targets are reduced, so this equals `zero_rows`.
    pub reductions_to_zero: usize,
    pub zero_rows: usize,
    /// Nonzero targets whose lead is singular top-reducible, discarded by EF Lemma 5.1.
    pub singular_rows: usize,
    /// `reductions_to_zero + singular_rows`: targets that added no basis element.
    pub rows_adding_no_rank: usize,
    /// Multiply-accumulates in batch elimination.
    pub coefficient_products: u64,
    pub products_on_zero_rows: u64,
    pub products_on_singular_rows: u64,
    pub max_matrix_rows: usize,
    pub max_matrix_columns: usize,
    pub elements_added: usize,
    pub signature_basis_elements: usize,
    pub reduced_basis_elements: usize,
    /// Columns of the final interreduction matrix (0 when no matrix was needed).
    pub interreduction_columns: usize,
    /// Nonzero entries the interreduction matrix was built with.
    pub interreduction_nonzeros: usize,
    /// Live entries at the interreduction's high-water mark.
    pub interreduction_peak_nonzeros: usize,
    /// Minimal syzygy signatures held at the end.
    pub syzygy_signatures: usize,
    pub peak_pending: usize,
    /// Signatures, ratios and masks on basis elements, the syzygy store and the peak queue.
    pub signature_metadata_bytes: usize,
    /// Pair generation, the queue and every criterion: the bookkeeping RFC §5 leaves unpriced.
    pub bookkeeping: Duration,
    /// The part of `bookkeeping` spent hashing new elements' terms for the monomial table.
    pub element_hashing: Duration,
    pub symbolic: Duration,
    pub elimination: Duration,
    pub interreduction: Duration,
    /// Whether final interreduction ran in the engine's column space (G2-2) rather than falling
    /// back to the polynomial route on a budget refusal.
    pub interreduction_in_columns: bool,
    pub total: Duration,
    /// Parallel cascade only: times a target waited for every earlier target's announcement, and
    /// for an earlier target's final row.
    pub claim_announcement_waits: u64,
    pub claim_final_waits: u64,
    /// The most live bytes any batch held, on either cascade (the serial one since #962).
    pub claim_peak_live_bytes: usize,
    /// Parallel cascade only: phase A's wall and the cascade pass's, summed over batches.
    pub claim_phase_a: Duration,
    pub claim_cascade: Duration,
    /// Per completed batch, each target's outcome and exact row in signature order: the oracle
    /// Theorem 1 of #902 makes per-batch.
    #[cfg(test)]
    pub(crate) batch_trace: Vec<Vec<String>>,
    /// #901's elimination split and glue clocks; collected only under `research-sigf4-split`.
    #[cfg(feature = "research-sigf4-split")]
    pub split: SplitLog,
    /// #936's element-use counts and syzygy-store replay; collected only under
    /// `research-sigf4-usage`.
    #[cfg(feature = "research-sigf4-usage")]
    pub usage: usage::UsageReport,
    /// #1031's census as `(summary, batches)`, when [`SigF4Options::reuse_census`] asked for it.
    #[cfg(feature = "research-reuse")]
    pub reuse: Option<(crate::util::Json, crate::util::Json)>,
}

/// One batch's elimination, split by pivot source. `reducer_*` is work against the batch's reducer
/// block (design 2's parallel pass, plus reducer pivots met in the serial pass); `cascade_products`
/// is work against earlier targets of the same batch, which no design yet parallelizes.
#[cfg(feature = "research-sigf4-split")]
#[derive(Clone, Debug, Default)]
pub struct BatchSplit {
    pub targets: usize,
    pub reducers: usize,
    pub columns: usize,
    /// Nonzero entries of the batch matrix as built, targets and reducers.
    pub entries: u64,
    /// Column index and sparse-row construction before either pass.
    pub setup: Duration,
    pub parallel_pass: Duration,
    pub serial_pass: Duration,
    pub parallel_products: u64,
    pub serial_reducer_products: u64,
    pub cascade_products: u64,
    /// Serial-pass targets that used at least one earlier-target pivot.
    pub cascading_targets: usize,
}

/// One batch's symbolic stage by component (#939). The split build unfuses multiplication from
/// interning (products go to a scratch buffer first) and clocks every reducer lookup, so its
/// symbolic total runs above the timed build's; `total` here is this build's own. The CPU and its
/// `scaling_cur_freq` are read outside the clock, before and after.
#[cfg(feature = "research-sigf4-split")]
#[derive(Clone, Debug, Default)]
pub struct SymbolicSplit {
    pub reducer_search: Duration,
    pub searches: u64,
    pub multiply: Duration,
    pub interning: Duration,
    pub terms: u64,
    pub column_sort: Duration,
    pub total: Duration,
    pub cpu: Option<usize>,
    pub khz_before: Option<u64>,
    pub khz_after: Option<u64>,
}

#[cfg(feature = "research-sigf4-split")]
impl SymbolicSplit {
    /// The CPU this thread runs on and that CPU's current frequency, from procfs and sysfs.
    pub(crate) fn cpu_khz() -> (Option<usize>, Option<u64>) {
        let cpu = std::fs::read_to_string("/proc/thread-self/stat")
            .ok()
            .and_then(|s| {
                // Field 39 (processor), counted after the parenthesised command name.
                let rest = &s[s.rfind(')')? + 2..];
                rest.split_whitespace().nth(36)?.parse().ok()
            });
        let khz = cpu.and_then(|c: usize| {
            let path = format!("/sys/devices/system/cpu/cpu{c}/cpufreq/scaling_cur_freq");
            std::fs::read_to_string(path).ok()?.trim().parse().ok()
        });
        (cpu, khz)
    }

    /// Multiplies `terms` and their additive hashes by `mult` into `scratch`, then interns each
    /// product, clocking each half.
    #[allow(clippy::type_complexity)]
    pub(crate) fn row<const N: usize>(
        &mut self,
        scratch: &mut Vec<(crate::Monomial<N>, u64)>,
        terms: impl Iterator<Item = (crate::Monomial<N>, u64)>,
        (mult, mult_hash): (crate::Monomial<N>, u64),
        mut intern: impl FnMut(crate::Monomial<N>, u64) -> u32,
        out: &mut Vec<u32>,
    ) {
        let clock = std::time::Instant::now();
        scratch.clear();
        scratch.extend(terms.map(|(m, h)| (m * mult, h.wrapping_add(mult_hash))));
        let products = std::time::Instant::now();
        out.extend(scratch.iter().map(|&(m, h)| intern(m, h)));
        self.interning += products.elapsed();
        self.multiply += products - clock;
        self.terms += scratch.len() as u64;
    }
}

#[cfg(feature = "research-sigf4-split")]
#[derive(Clone, Debug, Default)]
pub struct SplitLog {
    pub batches: Vec<BatchSplit>,
    pub symbolic: Vec<SymbolicSplit>,
    /// Input normalization before the first batch.
    pub inputs: Duration,
    /// Converting the signature basis to polynomials, and dropping the engine.
    pub materialize: Duration,
    pub drop: Duration,
    /// #970: products of each element-adding row, in insertion order; then the elements the
    /// reduced basis drops (a lead another element also has, or one a smaller lead divides) and
    /// the products their rows cost, beside those of the elements it keeps.
    pub element_products: Vec<u64>,
    /// Interreduction's minimal-basis selection alone, timed on a copy outside its stage clock.
    pub minimal_selection: Duration,
    pub redundant_elements: usize,
    pub products_on_redundant_elements: u64,
    pub products_on_kept_elements: u64,
}

/// The reduced Gröbner basis under a graded `order`, by the signature engine. Same contract as
/// [`crate::grobner::f4()`].
///
/// # Errors
/// [`SigF4Error::Unsupported`] for a non-graded order; [`SigF4Error::Budget`] for a crossed budget.
pub fn sig_f4<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error> {
    sig_f4_reported(generators, order, &SigF4Options::default()).0
}

/// As [`sig_f4`] under `options`, with statistics returned even on refusal.
pub fn sig_f4_reported<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &SigF4Options,
) -> (
    Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error>,
    SigF4Statistics,
) {
    let mut statistics = SigF4Statistics::default();
    let result = engine::run(generators, order, options, &mut statistics);
    (result, statistics)
}
