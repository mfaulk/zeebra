//! Live F4 matrices pinned by canonical digests; capture preserves the exact pre-elimination input.

use crate::{
    fields::KnownOrder,
    fields::{Bn254Fr, Gf256Mq, Mersenne31, Zp18446744073709551557, Zp2, Zp2147483647},
    grobner::{
        benchmark_systems::{cyclic, katsura},
        differential::{CaseField, GeneratedSystem, SystemShape},
        f4::{
            macaulay::MacaulayMatrix,
            observer::{BatchObserver, TracedBatch},
            options::{F4Error, F4Options},
            reduction::build_batch_matrix,
            structured::reducer_rows,
            symbolic::{MonicBasis, ReducerCache},
        },
        pairs::CriticalPair,
    },
    poly::MonomialOrder,
    util::Sha256,
    FiniteField, Monomial, MultivariatePolynomial,
};

/// Which batch of a run an entry takes its matrix from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BatchSelector {
    /// The batch with the most rows, which is where the elimination cost is.
    ///
    /// Resolved in a first pass that records shapes only, so that the second pass knows which
    /// index to clone at. Two runs rather than one, and the resolved index is pinned in the
    /// fingerprint — a selector that silently moved to a different batch would otherwise be
    /// indistinguishable from a matrix that changed.
    Largest,

    /// The batch at this index, counting from zero in the order the run reduced them.
    Index(usize),

    /// Capture this zero-based batch and stop before its elimination; no complete basis is computed.
    Prefix(usize),
}

/// Which option preset built a matrix.
///
/// Carried per entry because the two presets build different matrices, and a corpus that did not
/// say which would be a corpus of matrices from an unspecified configuration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OptionsPreset {
    /// [`F4Options::baseline`] — every optimization off. What every pre-existing stage harness in
    /// this repository uses, and therefore what the existing figures describe.
    Baseline,

    /// [`F4Options::default`], i.e. [`F4Options::recommended`] — what ships.
    Default,

    /// Shipping strategies with explicit live-entry and byte caps for large captures.
    RaisedDefault { entries: usize, bytes: usize },
}

impl OptionsPreset {
    pub fn options(self) -> F4Options {
        match self {
            Self::Baseline => F4Options::baseline(),
            Self::Default => F4Options::default(),
            Self::RaisedDefault { entries, bytes } => F4Options {
                max_live_nonzeros: entries,
                max_live_bytes: bytes,
                ..F4Options::default()
            },
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Self::Baseline => "baseline",
            Self::Default => "default",
            Self::RaisedDefault { .. } => "default-raised-budget",
        }
    }
}

/// The shape/density regime an entry is in the corpus to cover.
///
/// A **checked** classification, not a label: the band is asserted against the captured matrix's
/// own reducer share by `test_every_entry_is_in_the_regime_it_claims`. A regime that was merely
/// written down would drift the first time a selection policy changed, and a corpus whose coverage
/// claim is not checked is a corpus whose coverage claim is not true.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Regime {
    /// Reducer rows are at least 80% of the matrix: tall, reducer-dominated, the shape symbolic
    /// preprocessing produces on graded orders at high degree.
    Scaffolded,

    /// Between 40% and 80% scaffolding.
    Mixed,

    /// Under 40% scaffolding: the matrix is mostly pair halves.
    PairHeavy,
}

impl Regime {
    /// The inclusive-exclusive band on the reducer share this regime asserts.
    pub fn band(self) -> (f64, f64) {
        match self {
            Self::Scaffolded => (0.80, 1.000_001),
            Self::Mixed => (0.40, 0.80),
            Self::PairHeavy => (0.0, 0.40),
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Self::Scaffolded => "scaffolded",
            Self::Mixed => "mixed",
            Self::PairHeavy => "pair-heavy",
        }
    }

    /// The regime a measured reducer share falls in.
    pub fn of(reducer_share: f64) -> Self {
        if reducer_share >= 0.80 {
            Self::Scaffolded
        } else if reducer_share >= 0.40 {
            Self::Mixed
        } else {
            Self::PairHeavy
        }
    }
}

/// What a captured matrix is, in numbers a benchmark can print and a test can pin.
///
/// The digest is over the entries and the column and row labels, so two matrices with the same
/// dimensions and nonzero count but different content have different digests. The counts are
/// carried beside it because a digest mismatch says only *that* something moved, and the counts say
/// what.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MatrixFingerprint {
    /// Which batch of the run this was, counting from zero.
    pub batch_index: usize,

    /// Rows in the matrix as built.
    pub rows: usize,

    /// Columns, i.e. distinct monomials across the rows.
    pub columns: usize,

    /// Of [`Self::rows`], the reducer multiples symbolic preprocessing added.
    pub reducer_rows: usize,

    /// Nonzero entries as built, before elimination fills it in.
    pub nonzeros: usize,

    /// The first 16 hex digits of the sha256 of the canonical encoding.
    pub digest: String,
}

impl MatrixFingerprint {
    /// Of the rows, the share that is reduction scaffolding.
    pub fn reducer_share(&self) -> f64 {
        if self.rows == 0 {
            0.0
        } else {
            self.reducer_rows as f64 / self.rows as f64
        }
    }

    /// Nonzeros over cells, as built.
    pub fn density(&self) -> f64 {
        let cells = self.rows.saturating_mul(self.columns);
        if cells == 0 {
            0.0
        } else {
            self.nonzeros as f64 / cells as f64
        }
    }
}

/// One corpus entry: the instance, the configuration, which batch, and what that matrix is.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MatrixSpec {
    /// `family-variables/order/field/preset`, unique across the corpus.
    pub label: &'static str,

    /// The generator family: `katsura` or `cyclic`.
    pub family: &'static str,

    /// Variables, which is this crate's `N` and not the literature's index — see
    /// [`crate::grobner::external::corpus`] for why the two differ by one.
    pub variables: usize,

    /// The coefficient field's Rust type name, with its width in bits.
    pub field: &'static str,

    /// Bits in the field's order, which is the axis a per-width kernel is specialized along.
    pub field_bits: u32,

    /// The monomial order the run used.
    pub order: MonomialOrder,

    /// Which preset built it.
    pub options: OptionsPreset,

    /// Which batch the entry takes.
    pub selector: BatchSelector,

    /// The shape/density regime this entry covers, asserted against the capture.
    pub regime: Regime,

    /// What the matrix is, pinned.
    pub fingerprint: MatrixFingerprint,
}

/// A matrix as F4 built it, with the inputs it was built from.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CapturedMatrix<const N: usize, F: FiniteField> {
    /// The matrix the live run handed to elimination, before elimination touched it.
    pub matrix: MacaulayMatrix<N, F>,

    /// The basis and pairs of the same batch, so the capture can be checked against a rebuild.
    pub inputs: TracedBatch<N, F>,

    /// The system the run started from.
    ///
    /// Carried so that a harness holding a corpus matrix can also time the whole computation it
    /// came out of. The predictiveness check in `examples/f4_matrix_corpus.rs` is the reason:
    /// comparing a kernel's effect on one matrix against its effect end to end requires both, and
    /// re-deriving the generators at the call site would be a second definition of the instance.
    pub generators: Vec<MultivariatePolynomial<N, F>>,

    /// Matrix hooks observed: the total for complete captures, or the prefix length otherwise.
    pub batches: usize,

    /// Whether the source computation completed rather than stopping at a prefix.
    pub completed: bool,

    /// What the matrix is.
    pub fingerprint: MatrixFingerprint,
}

/// Why a capture did not produce a matrix.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CorpusError {
    /// The computation stopped before producing the matrix.
    Computation(F4Error),

    /// An index or prefix selector named a missing batch, or the run built none.
    NoSuchBatch {
        label: &'static str,
        wanted: usize,
        batches: usize,
    },

    /// The captured matrix is not the one the corpus pins.
    ///
    /// Returned by [`walk_corpus`] rather than panicking, because the caller is usually a
    /// benchmark and a benchmark that reported numbers for a matrix other than the pinned one is
    /// the failure this corpus exists to prevent.
    ///
    /// Boxed: two fingerprints are 144 bytes, and an unboxed variant would widen every
    /// `Result<CapturedMatrix, _>` in this module on the success path as well.
    Drifted(Box<Drift>),
}

/// A captured matrix that is not the one the corpus pins.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Drift {
    /// Which entry.
    pub label: &'static str,

    /// What the corpus says the matrix is.
    pub pinned: MatrixFingerprint,

    /// What capturing it actually produced.
    pub found: MatrixFingerprint,
}

impl From<F4Error> for CorpusError {
    fn from(error: F4Error) -> Self {
        Self::Computation(error)
    }
}

impl std::fmt::Display for CorpusError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Computation(error) => write!(f, "the computation stopped: {:?}", error),
            Self::NoSuchBatch {
                label,
                wanted,
                batches,
            } => write!(
                f,
                "{}: wanted batch {} of {} the run built",
                label, wanted, batches
            ),
            Self::Drifted(drift) => write!(
                f,
                "{}: pinned {}x{} nz {} digest {}, found {}x{} nz {} digest {}",
                drift.label,
                drift.pinned.rows,
                drift.pinned.columns,
                drift.pinned.nonzeros,
                drift.pinned.digest,
                drift.found.rows,
                drift.found.columns,
                drift.found.nonzeros,
                drift.found.digest
            ),
        }
    }
}

impl std::error::Error for CorpusError {}

/// The board's `mq-random-n` system, materialized at this crate's const-generic type.
///
/// The multivariate-quadratic family is here because it is the one where the stage this corpus
/// serves is the whole cost: `docs/research/interreduction-cost.md` §3g.3 at `489ccbd6` puts
/// elimination at **4 531 ms of `mq-random-10` grevlex's 4 851 ms** under the arm #575 made the
/// default, against 7–17% on the katsura and cyclic rungs
/// (`docs/MILESTONE-F4-OPTIMIZATION.md` §8.5). A corpus for an elimination kernel that omitted it
/// would cover every family except the one that matters.
///
/// Reproduced rather than imported: [`crate::grobner::external::corpus::random_mq_instance`] renders
/// its instances to **text** for the external engines and never materializes one at a const `N`.
/// The seed is the variable count and the shape is `max_degree: 2, max_terms: 4n`, which is what
/// that function uses — and `test_the_corpus_mq_system_is_the_boards` pins the agreement by
/// comparing the generated system's rendered text against the registry's own, so a drift in either
/// generator fails rather than quietly producing a different ideal.
///
/// `F` must be the field of `characteristic`: the coefficients are residues of that prime, and
/// instantiating them over a different one is a different ideal with no error to say so.
fn mq_random<const N: usize, F: FiniteField>(
    characteristic: u64,
) -> Vec<MultivariatePolynomial<N, F>> {
    terms_as_system(&generated_mq::<N>(characteristic))
}

/// The `GeneratedSystem` behind [`mq_random`], exactly as `random_mq_instance` builds it.
fn generated_mq<const N: usize>(characteristic: u64) -> GeneratedSystem {
    GeneratedSystem::generate(
        N as u64,
        SystemShape {
            variables: N,
            max_degree: 2,
            max_terms: 4 * N,
        },
        CaseField::prime(characteristic),
    )
}

/// A generated system's terms as polynomials, one for one.
///
/// No merging happens here, because `GeneratedSystem::generate` has already merged duplicate
/// monomials; `test_the_mq_conversion_keeps_every_term` asserts the term counts survive, which is
/// what would break if that stopped being true.
fn terms_as_system<const N: usize, F: FiniteField>(
    generated: &GeneratedSystem,
) -> Vec<MultivariatePolynomial<N, F>> {
    assert_eq!(
        generated.variables.len(),
        N,
        "one variable per type parameter"
    );
    generated
        .polynomials
        .iter()
        .map(|terms| {
            let entries: Vec<(Monomial<N>, F)> = terms
                .iter()
                .map(|term| {
                    let mut exponents = [0u32; N];
                    exponents.copy_from_slice(&term.exponents);
                    (Monomial::new(&exponents), F::new(term.coefficient))
                })
                .collect();
            MultivariatePolynomial::new(&entries)
        })
        .collect()
}

/// The canonical encoding's version, in the digest's first line.
///
/// Bumped only when the encoding changes, which invalidates every pinned digest at once. A change
/// to the encoding that did not bump it would make a matrix that moved indistinguishable from one
/// that did not.
const ENCODING: &str = "zeebra-f4-matrix/1";

/// Why the field's identity is in the digest.
///
/// It was not, in the first cut, and the corpus caught it immediately: `cyclic-5` over `Zp2` and
/// over `Gf256Mq` digested **identically**. Cyclic's coefficients are `±1`, `Display` writes `1` for
/// the one of every field in this crate, and the matrices really are entry-for-entry equal — so a
/// digest over the entries alone cannot tell a GF(2) corpus entry from a GF(2^8) one, and the two
/// would have been interchangeable in a per-field-width comparison. Which is the exact axis #262
/// and H14 exist to measure.
const FIELD_LINE: &str = "field";

/// The digest of a matrix: the first 16 hex digits of the sha256 of its canonical encoding.
///
/// Streamed rather than built as one string, because the largest corpus matrices have hundreds of
/// thousands of entries and the digest must not cost more than the elimination it labels.
///
/// Field elements go in through [`std::fmt::Display`], whose round trip is the `FiniteField`
/// contract — so the encoding is canonical over every field in the crate, including the extensions
/// where an integer embedding is not injective.
pub fn digest_of<const N: usize, F: FiniteField>(matrix: &MacaulayMatrix<N, F>) -> String {
    let mut hasher = Sha256::new();
    let mut line = String::new();

    hasher.update(ENCODING.as_bytes());
    hasher.update(b"\n");
    line.clear();
    line.push_str(&format!(
        "{} {}\ndim {} {} {}\n",
        FIELD_LINE,
        std::any::type_name::<F>(),
        matrix.num_rows(),
        matrix.num_columns(),
        matrix.nonzeros()
    ));
    hasher.update(line.as_bytes());

    for (index, monomial) in matrix.columns().iter().enumerate() {
        line.clear();
        line.push_str(&format!("col {} {}\n", index, monomial));
        hasher.update(line.as_bytes());
    }

    for (index, origin) in matrix.row_origins().iter().enumerate() {
        line.clear();
        line.push_str(&format!(
            "row {} {:?} {} {}\n",
            index, origin.kind, origin.basis_index, origin.multiplier
        ));
        hasher.update(line.as_bytes());

        for (column, value) in matrix.matrix().row(index).entries() {
            line.clear();
            line.push_str(&format!("  {} {}\n", column, value));
            hasher.update(line.as_bytes());
        }
    }

    hasher.hex()[..16].to_string()
}

/// The fingerprint of a matrix, at the given batch index.
pub fn fingerprint_of<const N: usize, F: FiniteField>(
    matrix: &MacaulayMatrix<N, F>,
    batch_index: usize,
) -> MatrixFingerprint {
    MatrixFingerprint {
        batch_index,
        rows: matrix.num_rows(),
        columns: matrix.num_columns(),
        reducer_rows: reducer_rows(matrix),
        nonzeros: matrix.nonzeros(),
        digest: digest_of(matrix),
    }
}

/// Records every batch's shape and nothing else, so a selector can be resolved without clones.
struct Shapes {
    rows: Vec<usize>,
}

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for Shapes {
    fn batch(&mut self, _basis: &MonicBasis<N, F>, _pairs: &[CriticalPair<N>]) {}

    fn matrix(&mut self, matrix: &MacaulayMatrix<N, F>) {
        self.rows.push(matrix.num_rows());
    }
}

/// Keeps one batch: its inputs, and the matrix F4 built from them.
struct At<const N: usize, F: FiniteField> {
    wanted: usize,
    stop_after_capture: bool,
    seen: usize,
    pending: Option<TracedBatch<N, F>>,
    held: Option<(TracedBatch<N, F>, MacaulayMatrix<N, F>)>,
}

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for At<N, F> {
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]) {
        // Cloned only at the wanted index. The basis is the whole basis, so cloning every batch's
        // would make capturing a late batch of a large run cost more than the run.
        self.pending = if self.seen == self.wanted {
            Some(TracedBatch {
                basis: basis.clone(),
                pairs: pairs.to_vec(),
            })
        } else {
            None
        };
    }

    fn matrix(&mut self, matrix: &MacaulayMatrix<N, F>) {
        if self.seen == self.wanted {
            if let Some(inputs) = self.pending.take() {
                self.held = Some((inputs, matrix.clone()));
            }
        }
        self.seen += 1;
    }

    fn should_stop(&self) -> bool {
        self.stop_after_capture && self.held.is_some()
    }
}

/// Run F4 and keep the matrix the selector names, exactly as the run built it.
///
/// [`BatchSelector::Largest`] costs two runs: the first records row counts only, which is what
/// makes the second able to clone one basis instead of all of them. `Index` costs one complete
/// run; `Prefix` stops immediately after constructing the selected matrix.
///
/// # Errors
/// [`CorpusError::Computation`] for any stop except the selected prefix stop;
/// [`CorpusError::NoSuchBatch`] if the selector names a batch the run did not build.
pub fn capture_matrix<const N: usize, F: FiniteField>(
    label: &'static str,
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
    selector: BatchSelector,
) -> Result<CapturedMatrix<N, F>, CorpusError> {
    let wanted = match selector {
        BatchSelector::Index(index) | BatchSelector::Prefix(index) => index,
        BatchSelector::Largest => {
            let mut shapes = Shapes { rows: Vec::new() };
            super::f4_observed(generators, order, options, &mut shapes)?;
            shapes
                .rows
                .iter()
                .enumerate()
                .max_by_key(|(index, rows)| (**rows, std::cmp::Reverse(*index)))
                .map(|(index, _)| index)
                .ok_or(CorpusError::NoSuchBatch {
                    label,
                    wanted: 0,
                    batches: 0,
                })?
        }
    };
    let mut at = At {
        wanted,
        stop_after_capture: matches!(selector, BatchSelector::Prefix(_)),
        seen: 0,
        pending: None,
        held: None,
    };
    let completed = match super::f4_observed(generators, order, options, &mut at) {
        Ok(_) => true,
        Err(F4Error::StoppedByObserver) if at.should_stop() => false,
        Err(error) => return Err(error.into()),
    };
    let batches = at.seen;

    let (inputs, matrix) = at.held.ok_or(CorpusError::NoSuchBatch {
        label,
        wanted,
        batches,
    })?;
    let fingerprint = fingerprint_of(&matrix, wanted);

    Ok(CapturedMatrix {
        matrix,
        inputs,
        generators: generators.to_vec(),
        batches,
        completed,
        fingerprint,
    })
}

/// The matrix a harness gets by rebuilding from the captured inputs, which must be the captured
/// matrix.
///
/// The route every existing stage harness takes. It is here so that the agreement can be asserted:
/// rebuilding takes the options and a cross-batch cache as arguments, and passing different ones
/// produces a different matrix and no error at all. `benches/f4_stages.rs` rebuilds under
/// `F4Options::baseline()` with `ReducerSelection::FirstApplicable` and a disabled cache written
/// out literally, none of which is what the shipping default does.
///
/// The cache is fresh, which is only neutral because the corpus presets have
/// [`CacheMode::Off`](super::symbolic::CacheMode). Under a cache that is on, batch *k* replayed
/// from empty need not be batch *k* of the run, and the assertion below is what would say so.
///
/// # Errors
/// As [`build_batch_matrix`].
pub fn rebuild_matrix<const N: usize, F: FiniteField>(
    captured: &CapturedMatrix<N, F>,
    order: MonomialOrder,
    options: &F4Options,
) -> Result<MacaulayMatrix<N, F>, CorpusError> {
    let mut cache = ReducerCache::new(options.reducer_cache);
    let built = build_batch_matrix(
        &captured.inputs.basis,
        &captured.inputs.pairs,
        order,
        options,
        &mut cache,
    )?;
    Ok(built.matrix)
}

/// Handed each corpus entry in turn, at the entry's own `N` and field.
///
/// A visitor rather than an iterator because `N` is a const generic and the field is a type
/// parameter, so the entries do not have one type and cannot be collected into one sequence. The
/// visitor is monomorphized per entry instead.
pub trait CorpusVisitor {
    /// `captured.fingerprint` has already been checked against `spec.fingerprint`.
    fn visit<const N: usize, F: FiniteField>(
        &mut self,
        spec: &MatrixSpec,
        captured: &CapturedMatrix<N, F>,
    );
}

/// Dispatch one entry at its native arity and field without capturing a matrix.
pub trait MatrixEntryVisitor {
    /// `generators` is lazy: callers loading a cached matrix need not build a polynomial system.
    fn visit<const N: usize, F: KnownOrder>(
        &mut self,
        spec: &MatrixSpec,
        generators: fn() -> Vec<MultivariatePolynomial<N, F>>,
    );
}

/// Capture one entry, refusing it unless it is what the corpus pins.
///
/// `verify` is off in exactly one place: the `pin` mode of
/// `examples/f4_matrix_corpus.rs`, which exists to *derive* the pinned table and therefore cannot
/// require it. Every other caller verifies, which is why [`walk_corpus`] takes no flag.
fn capture_checked<const N: usize, F: FiniteField>(
    spec: &MatrixSpec,
    generators: &[MultivariatePolynomial<N, F>],
    verify: bool,
) -> Result<CapturedMatrix<N, F>, CorpusError> {
    let captured = capture_matrix(
        spec.label,
        generators,
        spec.order,
        &spec.options.options(),
        spec.selector,
    )?;
    if verify && captured.fingerprint != spec.fingerprint {
        return Err(CorpusError::Drifted(Box::new(Drift {
            label: spec.label,
            pinned: spec.fingerprint.clone(),
            found: captured.fingerprint,
        })));
    }
    Ok(captured)
}

/// The corpus, generated from one table so that the metadata and the dispatch cannot drift apart.
///
/// Both [`corpus`] and [`walk_corpus`] come out of this invocation. A spec with no dispatch arm, or
/// an arm with no spec, is not expressible.
macro_rules! corpus {
    ($metadata:ident, $walk:ident, $walk_with:ident, $dispatch:ident; $(
        $label:literal : $system:expr,
        $family:literal, $variables:literal, $field:literal, $bits:literal,
        $order:expr, $preset:expr, $selector:expr, $regime:expr,
        $batch:literal, $rows:literal, $columns:literal, $reducers:literal, $nonzeros:literal,
        $digest:literal ;
    )*) => {
        /// Every entry's metadata and pinned fingerprint, in corpus order.
        ///
        /// Metadata only: no F4 computation is performed. The companion walk captures this set.
        pub fn $metadata() -> Vec<MatrixSpec> {
            vec![$(
                MatrixSpec {
                    label: $label,
                    family: $family,
                    variables: $variables,
                    field: $field,
                    field_bits: $bits,
                    order: $order,
                    options: $preset,
                    selector: $selector,
                    regime: $regime,
                    fingerprint: MatrixFingerprint {
                        batch_index: $batch,
                        rows: $rows,
                        columns: $columns,
                        reducer_rows: $reducers,
                        nonzeros: $nonzeros,
                        digest: $digest.to_string(),
                    },
                },
            )*]
        }

        /// Dispatch a named entry without executing F4; return false for an unknown label.
        pub fn $dispatch<V: MatrixEntryVisitor>(label: &str, visitor: &mut V) -> bool {
            let specs = $metadata();
            let Some(spec) = specs.iter().find(|spec| spec.label == label) else { return false; };
            match label {
                $( $label => visitor.visit(spec, || $system), )*
                _ => unreachable!("every spec has a dispatch arm"),
            }
            true
        }

        /// Capture every entry and hand it to `visitor`, in corpus order.
        ///
        /// Each matrix is checked against its pinned fingerprint before the visitor sees it, so a
        /// benchmark driven through here cannot report a number about a matrix that moved.
        ///
        /// # Errors
        /// The first [`CorpusError`] any entry produces, which stops the walk: a corpus that
        /// carried on past a drifted entry would publish a partial comparison as a whole one.
        pub fn $walk<V: CorpusVisitor>(visitor: &mut V) -> Result<(), CorpusError> {
            $walk_with(visitor, true)
        }

        /// Capture this set with the fingerprint check optional.
        ///
        /// `verify = false` is for deriving the pinned table and nothing else.
        ///
        /// # Errors
        /// The first capture or fingerprint error.
        pub fn $walk_with<V: CorpusVisitor>(
            visitor: &mut V,
            verify: bool,
        ) -> Result<(), CorpusError> {
            let specs = $metadata();
            let mut index = 0usize;
            $(
                {
                    let spec = &specs[index];
                    debug_assert_eq!(spec.label, $label);
                    let captured = capture_checked(spec, &$system, verify)?;
                    visitor.visit(spec, &captured);
                    index += 1;
                }
            )*
            assert_eq!(index, specs.len(), "every spec has a dispatch arm");
            Ok(())
        }
    };
}

/// The characteristic every F4 figure in this repository is taken at: `2^31 - 1`.
///
/// Restated rather than imported from `external::corpus`, because that module sits behind the
/// `external-runners` feature and this one does not. `test_the_reference_prime_is_the_boards`
/// pins the two equal whenever the harness is compiled, so a corpus entry's field and a board
/// row's field still cannot drift apart.
const REFERENCE_CHARACTERISTIC: u64 = 2_147_483_647;
use BatchSelector::Largest;
use MonomialOrder::GradedReverseLexicographic as Grevlex;
use MonomialOrder::Lexicographic as Lex;
use OptionsPreset::{Baseline, Default as Shipping};
use Regime::{Mixed, PairHeavy, Scaffolded};

corpus! { corpus, walk_corpus, walk_corpus_with, visit_corpus_entry;
    // --- 31-bit prime, Mersenne31 in a 32-bit representation -------------------------------
    "katsura-7/grevlex/m31/default": katsura::<7, Mersenne31>(),
        "katsura", 7, "Mersenne31", 31, Grevlex, Shipping, Largest, Mixed,
        4, 361, 369, 263, 10546, "01c80075ca42a4c2";
    "katsura-7/grevlex/m31/baseline": katsura::<7, Mersenne31>(),
        "katsura", 7, "Mersenne31", 31, Grevlex, Baseline, Largest, Scaffolded,
        8, 6810, 6862, 6788, 112200, "746a1103c3b7c6fe";
    "katsura-6/lex/m31/baseline": katsura::<6, Mersenne31>(),
        "katsura", 6, "Mersenne31", 31, Lex, Baseline, Largest, Mixed,
        21, 1954, 945, 828, 64756, "3f5824bd5619b32d";
    "cyclic-6/grevlex/m31/default": cyclic::<6, Mersenne31>(),
        "cyclic", 6, "Mersenne31", 31, Grevlex, Shipping, Largest, PairHeavy,
        7, 159, 175, 57, 6529, "b059ff3c5e16302b";
    "cyclic-6/lex/m31/default": cyclic::<6, Mersenne31>(),
        "cyclic", 6, "Mersenne31", 31, Lex, Shipping, Largest, Scaffolded,
        56, 1026, 1048, 1018, 29696, "b46c8477b7533630";

    // --- 64-bit prime ----------------------------------------------------------------------
    "katsura-7/grevlex/p64/default": katsura::<7, Zp18446744073709551557>(),
        "katsura", 7, "Zp18446744073709551557", 64, Grevlex, Shipping, Largest, Mixed,
        4, 361, 369, 263, 10546, "ee5963facafddbde";
    "cyclic-6/grevlex/p64/default": cyclic::<6, Zp18446744073709551557>(),
        "cyclic", 6, "Zp18446744073709551557", 64, Grevlex, Shipping, Largest, PairHeavy,
        7, 159, 175, 57, 6529, "b851c4a0cbbbf7bd";
    "katsura-6/lex/p64/baseline": katsura::<6, Zp18446744073709551557>(),
        "katsura", 6, "Zp18446744073709551557", 64, Lex, Baseline, Largest, Mixed,
        21, 1954, 945, 828, 64756, "43b5952f8a8b1bde";

    // --- 254-bit prime, BN254's scalar field -----------------------------------------------
    "katsura-6/grevlex/bn254/default": katsura::<6, Bn254Fr>(),
        "katsura", 6, "Bn254Fr", 254, Grevlex, Shipping, Largest, Mixed,
        3, 144, 152, 98, 2461, "7531e274c605e4dc";
    "cyclic-5/grevlex/bn254/baseline": cyclic::<5, Bn254Fr>(),
        "cyclic", 5, "Bn254Fr", 254, Grevlex, Baseline, Largest, Mixed,
        18, 635, 379, 317, 8372, "3e2099571be467d7";

    // --- Multivariate quadratics, the family where elimination IS the cost -----------------
    "mq-random-6/grevlex/p31x64/default": mq_random::<6, Zp2147483647>(REFERENCE_CHARACTERISTIC),
        "mq-random", 6, "Zp2147483647", 31, Grevlex, Shipping, Largest, Scaffolded,
        5, 757, 756, 659, 16074, "62e9d2f6c591d1f6";
    "mq-random-6/grevlex/p31x64/baseline": mq_random::<6, Zp2147483647>(REFERENCE_CHARACTERISTIC),
        "mq-random", 6, "Zp2147483647", 31, Grevlex, Baseline, Largest, Scaffolded,
        10, 3305, 3342, 3269, 66032, "13016bd535663e7d";
    "mq-random-10/grevlex/p31x64/default": mq_random::<10, Zp2147483647>(REFERENCE_CHARACTERISTIC),
        "mq-random", 10, "Zp2147483647", 31, Grevlex, Shipping, Largest, Scaffolded,
        7, 12554, 12020, 11086, 783737, "f9a86d072bdc760f";

    // --- GF(2) ------------------------------------------------------------------------------
    "cyclic-6/grevlex/gf2/default": cyclic::<6, Zp2>(),
        "cyclic", 6, "Zp2", 1, Grevlex, Shipping, Largest, PairHeavy,
        6, 130, 163, 50, 2314, "23a43be1462915fb";
    "cyclic-7/grevlex/gf2/default": cyclic::<7, Zp2>(),
        "cyclic", 7, "Zp2", 1, Grevlex, Shipping, Largest, PairHeavy,
        16, 1146, 795, 372, 84450, "0058c956e245beff";

    // --- GF(2^8), the Fukuoka modulus --------------------------------------------------------
    "cyclic-6/grevlex/gf256/default": cyclic::<6, Gf256Mq>(),
        "cyclic", 6, "Gf256Mq", 8, Grevlex, Shipping, Largest, PairHeavy,
        6, 130, 163, 50, 2314, "688436ee205fd305";
    "cyclic-5/lex/gf256/default": cyclic::<5, Gf256Mq>(),
        "cyclic", 5, "Gf256Mq", 8, Lex, Shipping, Largest, Scaffolded,
        14, 61, 72, 55, 438, "5d08ac9dd7acb1ce";
}

// Large captures use the same spec/dispatch generator, but are never part of walk_corpus.
corpus! { large_corpus, walk_large_corpus, walk_large_corpus_with, visit_large_corpus_entry;
    "mq-random-14/grevlex/p31x64/default-64m": mq_random::<14, Zp2147483647>(REFERENCE_CHARACTERISTIC),
        "mq-random", 14, "Zp2147483647", 31, Grevlex, OptionsPreset::RaisedDefault { entries: 64_000_000, bytes: 1_024_000_000 },
        BatchSelector::Prefix(6), Scaffolded,
        6, 75091, 76194, 67411, 24843682, "b6b0c2aa13296fec";
}

#[cfg(test)]
mod tests {
    use super::{
        capture_matrix, corpus, digest_of, rebuild_matrix, walk_corpus, BatchSelector,
        CapturedMatrix, CorpusError, CorpusVisitor, MatrixSpec, OptionsPreset, Regime,
    };
    use crate::{
        fields::Mersenne31,
        grobner::{
            benchmark_systems::{cyclic, katsura},
            f4::{
                f4_observed,
                options::{F4Options, ReducerSelection},
                structured::{eliminate, BlockPlan},
            },
        },
        linalg::Backend,
        poly::MonomialOrder,
        FiniteField,
    };

    type F = Mersenne31;
    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    // The large capture is pinned, classified from its rows and identical to a fresh rebuild.
    #[test]
    #[ignore = "opt-in large capture; run with an optimized profile and a memory guard"]
    fn test_large_entry_is_pinned_and_rebuilds() {
        struct Check(usize);
        impl CorpusVisitor for Check {
            fn visit<const N: usize, F2: FiniteField>(
                &mut self,
                spec: &MatrixSpec,
                captured: &CapturedMatrix<N, F2>,
            ) {
                self.0 += 1;
                assert!(!captured.completed);
                assert_eq!(captured.batches, spec.fingerprint.batch_index + 1);
                assert!(captured.fingerprint.nonzeros > 10_000_000);
                assert_eq!(
                    Regime::of(captured.fingerprint.reducer_share()),
                    spec.regime
                );
                assert_eq!(
                    rebuild_matrix(captured, spec.order, &spec.options.options()).unwrap(),
                    captured.matrix
                );
            }
        }
        let mut check = Check(0);
        super::walk_large_corpus(&mut check).expect("large entry captures as pinned");
        assert_eq!(check.0, super::large_corpus().len());
    }

    // The opt-in set exceeds ten million entries and cannot leak into the default smoke corpus.
    #[test]
    fn test_large_corpus_is_explicit_and_above_ten_million_entries() {
        let small = corpus();
        let large = super::large_corpus();
        assert_eq!(small.len(), 17);
        assert!(!large.is_empty());
        for spec in large {
            assert!(spec.fingerprint.nonzeros > 10_000_000);
            assert!(!small.iter().any(|entry| entry.label == spec.label));
            assert!(matches!(spec.selector, BatchSelector::Prefix(_)));
            assert!(spec.options.options().max_live_nonzeros >= spec.fingerprint.nonzeros);
        }
    }

    // Prefix capture preserves resource errors before the target and rejects missing batches.
    #[test]
    fn test_prefix_capture_does_not_hide_errors_or_missing_batches() {
        let system = katsura::<4, F>();
        let limited = F4Options {
            max_matrix_rows: 1,
            ..F4Options::default()
        };
        assert!(matches!(
            capture_matrix(
                "limited",
                &system,
                GREVLEX,
                &limited,
                BatchSelector::Prefix(0)
            ),
            Err(CorpusError::Computation(_))
        ));
        assert!(matches!(
            capture_matrix(
                "missing",
                &system,
                GREVLEX,
                &F4Options::default(),
                BatchSelector::Prefix(usize::MAX)
            ),
            Err(CorpusError::NoSuchBatch { .. })
        ));
    }

    // Prefix capture stops before the selected batch is reduced or the batch limit is crossed.
    #[test]
    fn test_prefix_capture_stops_at_the_requested_matrix() {
        let system = katsura::<4, F>();
        let options = F4Options {
            max_batches: Some(1),
            ..F4Options::default()
        };
        let prefix = capture_matrix(
            "prefix",
            &system,
            GREVLEX,
            &options,
            BatchSelector::Prefix(0),
        )
        .expect("first matrix captured before elimination");
        let complete = capture_matrix(
            "complete",
            &system,
            GREVLEX,
            &F4Options::default(),
            BatchSelector::Index(0),
        )
        .unwrap();
        assert!(complete.completed);
        assert_eq!(prefix.fingerprint, complete.fingerprint);
        assert_eq!(prefix.batches, 1);
        assert!(!prefix.completed);
        assert_eq!(
            prefix.matrix,
            rebuild_matrix(&prefix, GREVLEX, &options).unwrap()
        );
        assert!(capture_matrix(
            "complete",
            &system,
            GREVLEX,
            &options,
            BatchSelector::Index(0)
        )
        .is_err());
    }

    // Largest capture agrees with the maximum row count reported by the live run.
    #[test]
    fn test_the_largest_captured_matrix_is_the_largest_the_run_reports() {
        let system = katsura::<5, F>();
        let options = F4Options::default();

        let (_, statistics) = f4_observed(
            &system,
            GREVLEX,
            &options,
            &mut super::super::observer::Ignore,
        )
        .expect("within limits");
        let captured = capture_matrix("test", &system, GREVLEX, &options, BatchSelector::Largest)
            .expect("a batch to capture");

        assert_eq!(captured.fingerprint.rows, statistics.max_matrix_rows);
        assert_eq!(captured.batches, statistics.batches);
        assert!(captured.fingerprint.nonzeros > 0);
    }

    /// Rebuilding a captured batch from its own inputs gives back the captured matrix exactly.
    ///
    /// This is what lets an existing harness keep rebuilding: the route is sound, provided it is
    /// the same route under the same options. `test_a_rebuild_under_a_different_reducer_policy_is_a
    /// _different_matrix` is the other half, and shows the check is not vacuous.
    #[test]
    fn test_rebuilding_from_the_inputs_reproduces_the_captured_matrix() {
        for preset in [OptionsPreset::Baseline, OptionsPreset::Default] {
            let options = preset.options();
            let captured = capture_matrix(
                "test",
                &katsura::<5, F>(),
                GREVLEX,
                &options,
                BatchSelector::Largest,
            )
            .expect("a batch to capture");

            let rebuilt =
                rebuild_matrix(&captured, GREVLEX, &options).expect("within the same budgets");
            assert_eq!(rebuilt, captured.matrix, "{}", preset.name());
            assert_eq!(
                digest_of(&rebuilt),
                captured.fingerprint.digest,
                "{}",
                preset.name()
            );
        }
    }

    /// Rebuilding the same batch under a different reducer policy is a different matrix.
    ///
    /// The teeth of the check above. A harness that hard-codes a reducer selection, a cache mode or
    /// a preset other than the one the matrix came from measures a matrix the live path does not
    /// build — and gets no error for it, which is why the agreement has to be asserted.
    #[test]
    fn test_a_rebuild_under_a_different_reducer_policy_is_a_different_matrix() {
        let options = F4Options::default();
        let captured = capture_matrix(
            "test",
            &katsura::<5, F>(),
            GREVLEX,
            &options,
            BatchSelector::Largest,
        )
        .expect("a batch to capture");

        let wrong = F4Options {
            reducer_selection: ReducerSelection::LargestLeadingMonomial,
            ..options
        };
        let rebuilt = rebuild_matrix(&captured, GREVLEX, &wrong).expect("within the same budgets");
        assert_ne!(
            digest_of(&rebuilt),
            captured.fingerprint.digest,
            "a policy change that left the matrix identical would make this check vacuous"
        );
    }

    /// The two option presets build different matrices on the same instance and order.
    ///
    /// The reason [`MatrixSpec::options`] exists. Every pre-existing stage harness in this crate
    /// runs on `baseline()`, so this is the size of the gap between what they measure and what the
    /// default builds.
    #[test]
    fn test_the_two_presets_do_not_build_the_same_matrix() {
        let baseline = capture_matrix(
            "test",
            &katsura::<5, F>(),
            GREVLEX,
            &F4Options::baseline(),
            BatchSelector::Largest,
        )
        .expect("a batch to capture");
        let shipping = capture_matrix(
            "test",
            &katsura::<5, F>(),
            GREVLEX,
            &F4Options::default(),
            BatchSelector::Largest,
        )
        .expect("a batch to capture");

        assert_ne!(baseline.fingerprint.digest, shipping.fingerprint.digest);
    }

    /// The digest reads the entries, not only the dimensions.
    ///
    /// Eliminating a matrix leaves its labels and its dimensions alone and changes its contents, so
    /// a digest over the shape alone would not notice. One that did not notice would let a harness
    /// pin an echelon form and benchmark it as an input.
    #[test]
    fn test_the_digest_reads_the_entries_and_not_only_the_shape() {
        let options = F4Options::baseline();
        let captured = capture_matrix(
            "test",
            &katsura::<4, F>(),
            GREVLEX,
            &options,
            BatchSelector::Largest,
        )
        .expect("a batch to capture");

        let mut eliminated = captured.matrix.clone();
        eliminate(
            BlockPlan::Baseline,
            Backend::Sparse,
            &mut eliminated,
            usize::MAX,
        )
        .expect("unbounded");

        assert_eq!(eliminated.num_rows(), captured.matrix.num_rows());
        assert_eq!(eliminated.num_columns(), captured.matrix.num_columns());
        assert_ne!(digest_of(&eliminated), captured.fingerprint.digest);
    }

    /// Two fields whose matrices are entry-for-entry equal still digest differently.
    ///
    /// A regression test for a collision the first cut of this corpus actually had. Cyclic's
    /// coefficients are `±1`, `Display` writes `1` for the one of every field in this crate, so
    /// `cyclic-5` over GF(2) and over GF(2^8) build the *same* matrix and digested to the same
    /// sixteen hex digits — which would have made two entries on the per-field-width axis
    /// interchangeable, on the axis the corpus exists to separate.
    #[test]
    fn test_two_fields_with_identical_entries_digest_differently() {
        use crate::fields::{Gf256Mq, Zp2};

        let over_gf2 = capture_matrix(
            "test",
            &cyclic::<5, Zp2>(),
            GREVLEX,
            &F4Options::default(),
            BatchSelector::Largest,
        )
        .expect("a batch to capture");
        let over_gf256 = capture_matrix(
            "test",
            &cyclic::<5, Gf256Mq>(),
            GREVLEX,
            &F4Options::default(),
            BatchSelector::Largest,
        )
        .expect("a batch to capture");

        assert_eq!(
            over_gf2.fingerprint.rows, over_gf256.fingerprint.rows,
            "the premise: the two matrices have the same shape"
        );
        assert_eq!(
            over_gf2.fingerprint.nonzeros,
            over_gf256.fingerprint.nonzeros
        );
        assert_ne!(over_gf2.fingerprint.digest, over_gf256.fingerprint.digest);
    }

    /// The matrix corpus's reference prime is the competitive board's.
    #[test]
    #[cfg(feature = "external-runners")]
    fn test_the_reference_prime_is_the_boards() {
        assert_eq!(
            super::REFERENCE_CHARACTERISTIC,
            crate::grobner::external::corpus::REFERENCE_CHARACTERISTIC
        );
    }

    // All MQ corpus generators reproduce the external registry system, including MQ14.
    #[test]
    #[cfg(feature = "external-runners")]
    fn test_the_corpus_mq_system_is_the_boards() {
        use crate::grobner::external::corpus::{random_mq_instance, REFERENCE_CHARACTERISTIC};

        for n in [6usize, 10, 14] {
            let board = random_mq_instance(n, n as u64, REFERENCE_CHARACTERISTIC, GREVLEX);
            let mine = match n {
                6 => super::generated_mq::<6>(REFERENCE_CHARACTERISTIC),
                10 => super::generated_mq::<10>(REFERENCE_CHARACTERISTIC),
                14 => super::generated_mq::<14>(REFERENCE_CHARACTERISTIC),
                _ => unreachable!(),
            };
            assert_eq!(mine.render(), board.system, "mq-random-{}", n);
            assert_eq!(mine.variables, board.variables, "mq-random-{}", n);
        }
    }

    /// Converting a generated system to polynomials keeps every term and every degree.
    ///
    /// `GeneratedSystem::generate` has already merged duplicate monomials, so the conversion must
    /// not merge again; if it did, the corpus would hold a sparser system than the board's under
    /// the same name.
    #[test]
    fn test_the_mq_conversion_keeps_every_term() {
        let generated = super::generated_mq::<10>(super::REFERENCE_CHARACTERISTIC);
        let system: Vec<_> =
            super::mq_random::<10, crate::fields::Zp2147483647>(super::REFERENCE_CHARACTERISTIC);

        assert_eq!(system.len(), generated.polynomials.len());
        for (polynomial, terms) in system.iter().zip(generated.polynomials.iter()) {
            assert_eq!(polynomial.terms.len(), terms.len());
            assert!(polynomial.degree() <= 2, "max_degree 2 is what makes it MQ");
        }
    }

    /// A batch index past the end of the run is refused rather than silently clamped.
    #[test]
    fn test_an_index_past_the_end_is_refused() {
        let error = capture_matrix(
            "test",
            &katsura::<4, F>(),
            GREVLEX,
            &F4Options::default(),
            BatchSelector::Index(10_000),
        )
        .expect_err("no such batch");
        assert!(matches!(
            error,
            CorpusError::NoSuchBatch { wanted: 10_000, .. }
        ));
    }

    /// A system with nothing to reduce builds no matrices, and the capture says so.
    #[test]
    fn test_a_system_with_no_batches_has_nothing_to_capture() {
        // The zero ideal returns before the main loop, so no matrix is built.
        let system: Vec<crate::MultivariatePolynomial<3, F>> = Vec::new();
        let error = capture_matrix(
            "test",
            &system,
            GREVLEX,
            &F4Options::default(),
            BatchSelector::Largest,
        )
        .expect_err("no batch");
        assert!(matches!(error, CorpusError::NoSuchBatch { batches: 0, .. }));
    }

    /// A spec whose pinned fingerprint does not describe the capture is refused by the walk.
    #[test]
    fn test_a_drifted_fingerprint_is_refused() {
        let mut spec = corpus()
            .into_iter()
            .find(|spec| spec.label == "katsura-7/grevlex/m31/default")
            .expect("the corpus has that entry");
        spec.fingerprint.digest = "0000000000000000".to_string();

        let error = super::capture_checked(&spec, &katsura::<7, F>(), true)
            .expect_err("the digest does not match");
        assert!(matches!(error, CorpusError::Drifted(_)));
    }

    /// The corpus covers the axes its acceptance criteria name.
    ///
    /// Metadata only, so this is free: at least twelve matrices, at least three fields, all three
    /// regimes, both presets, and unique labels.
    #[test]
    fn test_the_corpus_covers_the_axes_it_claims() {
        let specs = corpus();
        assert!(specs.len() >= 12, "{} entries", specs.len());

        let mut labels: Vec<&str> = specs.iter().map(|spec| spec.label).collect();
        labels.sort_unstable();
        let unique = labels.len();
        labels.dedup();
        assert_eq!(labels.len(), unique, "labels are unique");

        let mut widths: Vec<u32> = specs.iter().map(|spec| spec.field_bits).collect();
        widths.sort_unstable();
        widths.dedup();
        assert!(widths.len() >= 3, "field widths: {:?}", widths);

        for regime in [Regime::Scaffolded, Regime::Mixed, Regime::PairHeavy] {
            assert!(
                specs.iter().any(|spec| spec.regime == regime),
                "no entry in the {} regime",
                regime.name()
            );
        }
        for preset in [OptionsPreset::Baseline, OptionsPreset::Default] {
            assert!(
                specs.iter().any(|spec| spec.options == preset),
                "no entry under {}",
                preset.name()
            );
        }
    }

    /// Every entry captures, matches its pinned digest, and sits in the regime band it claims.
    ///
    /// The whole-corpus gate. `#[ignore]`d because it captures seventeen matrices, which is two F4
    /// runs apiece and impractical in a debug build; `Tests (release)` runs it, and
    /// `benches/f4_matrix_corpus.rs` walks the same corpus on every CI run through the benchmark
    /// smoke job, so a drift cannot reach main unnoticed either way.
    ///
    /// ```text
    /// cargo test --release -- --ignored test_every_entry_is_pinned_and_in_its_regime
    /// ```
    #[test]
    #[ignore = "captures the whole corpus; run in release"]
    fn test_every_entry_is_pinned_and_in_its_regime() {
        struct Check {
            entries: usize,
        }
        impl CorpusVisitor for Check {
            fn visit<const N: usize, F2: FiniteField>(
                &mut self,
                spec: &MatrixSpec,
                captured: &CapturedMatrix<N, F2>,
            ) {
                self.entries += 1;

                let share = captured.fingerprint.reducer_share();
                let (low, high) = spec.regime.band();
                assert!(
                    share >= low && share < high,
                    "{}: reducer share {:.3} is outside the {} band {:?}",
                    spec.label,
                    share,
                    spec.regime.name(),
                    (low, high)
                );

                let rebuilt = rebuild_matrix(captured, spec.order, &spec.options.options())
                    .expect("within the same budgets");
                assert_eq!(
                    rebuilt, captured.matrix,
                    "{}: the rebuild diverged from the captured matrix",
                    spec.label
                );
            }
        }

        let mut check = Check { entries: 0 };
        walk_corpus(&mut check).expect("every entry captures as pinned");
        assert_eq!(check.entries, corpus().len());
    }

    /// A cheap representative of the walk above, so the unignored suite still gates the machinery.
    ///
    /// One entry per field width, taken from the corpus by label, with its digest and its regime
    /// band checked the same way. If this passes and the ignored test fails, the corpus moved on an
    /// instance this one does not cover.
    #[test]
    fn test_a_representative_entry_per_field_width_is_pinned() {
        let specs = corpus();
        let find = |label: &str| {
            specs
                .iter()
                .find(|spec| spec.label == label)
                .unwrap_or_else(|| panic!("the corpus has {}", label))
                .clone()
        };

        // `N` and the field are generic parameters, so the two instances cannot share a loop.
        let katsura_7 = find("katsura-7/grevlex/m31/default");
        check_one(&katsura_7, &katsura::<7, F>());
        let over_gf2 = find("cyclic-6/grevlex/gf2/default");
        check_one(&over_gf2, &cyclic::<6, crate::fields::Zp2>());
    }

    /// Capture one spec, verify its digest, and assert its regime band.
    fn check_one<const N: usize, F2: FiniteField>(
        spec: &MatrixSpec,
        system: &[crate::MultivariatePolynomial<N, F2>],
    ) {
        let captured =
            super::capture_checked(spec, system, true).unwrap_or_else(|error| panic!("{}", error));
        let share = captured.fingerprint.reducer_share();
        let (low, high) = spec.regime.band();
        assert!(
            share >= low && share < high,
            "{}: reducer share {:.3} outside {:?}",
            spec.label,
            share,
            (low, high)
        );
    }
}
