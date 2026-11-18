//! Research-only signature-compatible F4 (#857, RFC `docs/research/signature-f4-rfc.md` design 1):
//! batched F4-RB under Schreyer shifted signatures, sig-lead-ratio rewriting, Koszul and zero-row
//! syzygies plus the product criterion, serial regular elimination, then the shipping
//! interreduction. Isolated from the shipping F4: nothing on that path reads this module.
//!
//! Correctness rests on Lairez Thm 62 (Algorithm 8): every row is reduced only by rows of strictly
//! smaller signature, a batch's rows are processed in increasing signature order, and its results
//! join the basis only after the batch. The reduced basis is unique, so the output must equal
//! [`crate::grobner::f4()`]'s coefficient for coefficient.

#[cfg(feature = "external-runners")]
pub mod corpus;
mod engine;
#[cfg(feature = "research-sigf4-replay")]
pub mod replay;
pub mod signature;
#[cfg(test)]
mod tests;

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
    /// Run [`crate::grobner::f4::certify_f4_output`] on the result and refuse a failure.
    pub certify: bool,
    /// Assert the signature discipline on every row operation and re-verify each new element's
    /// signature invariants. Expensive; for tests.
    pub check_signatures: bool,
    /// Threads for design 2's parallel pre-reduction against each batch's reducer block (RFC
    /// §6.1 item 1). `1` is design 1, fully serial. A field that is not `Send + Sync` runs the
    /// same pass serially.
    pub workers: usize,
}

impl Default for SigF4Options {
    fn default() -> Self {
        Self {
            max_wall_time: None,
            max_basis_elements: None,
            max_matrix_rows: 2_000_000,
            max_matrix_columns: 2_000_000,
            certify: false,
            check_signatures: false,
            workers: 1,
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
    /// Minimal syzygy signatures held at the end.
    pub syzygy_signatures: usize,
    pub peak_pending: usize,
    /// Signatures, ratios and masks on basis elements, the syzygy store and the peak queue.
    pub signature_metadata_bytes: usize,
    /// Pair generation, the queue and every criterion: the bookkeeping RFC §5 leaves unpriced.
    pub bookkeeping: Duration,
    pub symbolic: Duration,
    pub elimination: Duration,
    pub interreduction: Duration,
    pub total: Duration,
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
