//! A strict R1CS v1 profile: wire zero is constant one, and wire i maps to variable i − 1.
//! Custom gates and unknown sections are refused rather than silently losing constraints.

use crate::{util::sha256_hex, KnownOrder, Monomial, MultivariatePolynomial};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    time::{Duration, Instant},
};

/// Structural limits and a cooperative deadline for each parser or expansion operation.
///
/// These do not enforce total process RSS or interrupt an individual field operation. Use an
/// external process supervisor when a hard wall or memory ceiling is required.
#[derive(Clone, Debug)]
pub struct ImportLimits {
    /// Maximum binary input or symbol-sidecar bytes.
    pub max_input_bytes: usize,
    /// Maximum number of wires, including constant wire zero.
    pub max_wires: usize,
    /// Maximum number of original rows.
    pub max_constraints: usize,
    /// Maximum optional symbol-sidecar records, including optimized-out signals.
    pub max_symbols: usize,
    /// Maximum total A-by-B scalar products during expansion, before cancellation.
    pub max_products: usize,
    /// Maximum retained polynomial terms across all rows, after cancellation.
    pub max_expanded_terms: usize,
    /// Cooperative per-operation deadline.
    pub timeout: Duration,
}

impl Default for ImportLimits {
    fn default() -> Self {
        Self {
            max_input_bytes: 16 * 1024 * 1024,
            max_wires: 100,
            max_constraints: 1_000,
            max_symbols: 10_000,
            max_products: 100_000,
            max_expanded_terms: 100_000,
            timeout: Duration::from_secs(60),
        }
    }
}

/// A rejected input, assignment, capacity or resource boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    /// The file does not start with the R1CS magic bytes.
    InvalidMagic,
    /// Only version one is supported.
    UnsupportedVersion(u32),
    /// A requested read extends past the supplied bytes.
    Truncated { offset: usize, needed: usize },
    /// A container or section has unconsumed bytes.
    TrailingBytes,
    /// A required section is absent.
    MissingSection(u32),
    /// A section occurs more than once.
    DuplicateSection(u32),
    /// This profile does not interpret the section.
    UnsupportedSection(u32),
    /// Header counts or field width are inconsistent.
    InvalidHeader(&'static str),
    /// The requested coefficient domain is not a prime field.
    NonPrimeField,
    /// The declared modulus differs from the requested field.
    FieldMismatch,
    /// A row references a nonexistent wire.
    InvalidWire { row: usize, wire: u32 },
    /// Sparse terms are repeated, unordered or exceed the wire count.
    InvalidLinearCombination { row: usize },
    /// A sparse coefficient is zero or outside the canonical residue range.
    NonCanonicalCoefficient { row: usize },
    /// Wire-label mappings are repeated, out of range or violate wire zero's identity.
    InvalidWireMap,
    /// A symbol record is malformed, ambiguous or out of range.
    InvalidSymbol { line: usize },
    /// An assignment does not provide exactly the original wire count.
    AssignmentLength { expected: usize, actual: usize },
    /// Assignment wire zero is not one.
    ConstantWire,
    /// The caller-selected polynomial capacity is too small.
    Arity { needed: usize, capacity: usize },
    /// A structural limit would be exceeded.
    Limit {
        resource: &'static str,
        limit: usize,
    },
    /// The cooperative deadline expired.
    Deadline,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "R1CS: {self:?}")
    }
}
impl std::error::Error for Error {}

/// Original header counts; public and private inputs precede internal wires.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Header {
    /// Canonical field width, in bytes, rounded up to a whole 64-bit limb.
    pub field_bytes: usize,
    /// Wire count including wire zero.
    pub wire_count: usize,
    /// Public output count, starting at wire one.
    pub public_outputs: usize,
    /// Public input count, immediately after the public outputs.
    pub public_inputs: usize,
    /// Private input count, immediately after the public inputs.
    pub private_inputs: usize,
    /// Label identifiers are strictly below this bound.
    pub label_count: u64,
    /// Number of original rows, including rows that expand to zero.
    pub constraint_count: usize,
}

/// A wire's original R1CS role, without identifying private inputs with internal wires.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WireRole {
    /// Implicit constant one.
    Constant,
    /// Public output.
    PublicOutput,
    /// Public input.
    PublicInput,
    /// Private input.
    PrivateInput,
    /// Intermediate witness wire.
    Internal,
}

/// One original sparse dot product, in strictly increasing wire order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LinearCombination<F: KnownOrder> {
    terms: Vec<(u32, F)>,
}

impl<F: KnownOrder> LinearCombination<F> {
    /// Original wire identifiers and canonical nonzero coefficients.
    pub fn terms(&self) -> &[(u32, F)] {
        &self.terms
    }

    fn dot(&self, assignment: &[F]) -> F {
        self.terms
            .iter()
            .fold(F::zero(), |sum, (wire, coefficient)| {
                sum + *coefficient * assignment[*wire as usize]
            })
    }
}

/// A preserved original row `(A·w)(B·w) − C·w = 0`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Constraint<F: KnownOrder> {
    /// Zero-based row index in the input file.
    pub id: usize,
    /// Left dot product.
    pub a: LinearCombination<F>,
    /// Right dot product.
    pub b: LinearCombination<F>,
    /// Subtracted dot product.
    pub c: LinearCombination<F>,
}

/// An optional Circom `.sym` record; aliases and optimized-out signals are retained.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Symbol {
    /// Original signal label.
    pub label: u64,
    /// Witness wire, or `None` for a producer's `-1` optimized-out signal.
    pub wire: Option<u32>,
    /// Producer component identifier.
    pub component: u64,
    /// Original qualified signal name.
    pub name: String,
}

/// A parsed model, kept independently of its polynomial expansion.
#[derive(Clone, Debug)]
pub struct R1cs<F: KnownOrder> {
    header: Header,
    constraints: Vec<Constraint<F>>,
    wire_labels: Vec<u64>,
    symbols: Vec<Symbol>,
    source_digest: String,
    canonical: Vec<u8>,
    limits: ImportLimits,
}

/// Actual expansion work and retained size, without inferring process memory from them.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ExpansionStats {
    /// Total original A, B and C sparse entries.
    pub source_terms: usize,
    /// A-by-B scalar products, including products that later cancel.
    pub products: usize,
    /// Retained terms across all polynomial rows.
    pub expanded_terms: usize,
    /// Largest retained polynomial row.
    pub max_row_terms: usize,
}

/// A caller-sized polynomial system with explicit original-row and active-variable mappings.
#[derive(Clone, Debug)]
pub struct Expansion<const N: usize, F: KnownOrder> {
    /// Exactly one polynomial per original row, including zero polynomials.
    pub polynomials: Vec<MultivariatePolynomial<N, F>>,
    /// Corresponding zero-based original row IDs.
    pub row_ids: Vec<usize>,
    /// Wire IDs for the active prefix of variables; remaining capacity is unused padding.
    pub variable_to_wire: Vec<u32>,
    /// Expansion work and size.
    pub stats: ExpansionStats,
}

struct Deadline {
    start: Instant,
    duration: Duration,
}
impl Deadline {
    fn new(duration: Duration) -> Self {
        Self {
            start: Instant::now(),
            duration,
        }
    }
    fn check(&self) -> Result<(), Error> {
        if self.start.elapsed() >= self.duration {
            Err(Error::Deadline)
        } else {
            Ok(())
        }
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }
    fn take(&mut self, count: usize) -> Result<&'a [u8], Error> {
        let end = self
            .at
            .checked_add(count)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(Error::Truncated {
                offset: self.at,
                needed: count,
            })?;
        let result = &self.bytes[self.at..end];
        self.at = end;
        Ok(result)
    }
    fn u32(&mut self) -> Result<u32, Error> {
        Ok(u32::from_le_bytes(
            self.take(4)?.try_into().expect("four bytes"),
        ))
    }
    fn u64(&mut self) -> Result<u64, Error> {
        Ok(u64::from_le_bytes(
            self.take(8)?.try_into().expect("eight bytes"),
        ))
    }
    fn finish(self) -> Result<(), Error> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(Error::TrailingBytes)
        }
    }
}

fn limit(value: usize, maximum: usize, resource: &'static str) -> Result<(), Error> {
    if value > maximum {
        Err(Error::Limit {
            resource,
            limit: maximum,
        })
    } else {
        Ok(())
    }
}

fn modulus<F: KnownOrder>() -> Result<Vec<u8>, Error> {
    if F::characteristic_limbs() != F::order_limbs() {
        return Err(Error::NonPrimeField);
    }
    let words = F::characteristic_limbs();
    if words.is_empty() || words.len() > 4 || (words.len() == 1 && words[0] < 2) {
        return Err(Error::InvalidHeader(
            "prime field width must be 8 to 32 bytes",
        ));
    }
    Ok(words.iter().flat_map(|word| word.to_le_bytes()).collect())
}

fn decode<F: KnownOrder>(bytes: &[u8]) -> F {
    bytes.iter().rev().fold(F::zero(), |value, byte| {
        value * F::new(256) + F::new(u64::from(*byte))
    })
}

impl<F: KnownOrder> R1cs<F> {
    /// Parse the strict three-section R1CS v1 profile into the requested prime field.
    ///
    /// Sections 1, 2 and 3 are required exactly once in any order. Custom gates and unknown
    /// sections are explicitly unsupported. Coefficients must be sorted, nonzero canonical residues.
    pub fn parse(bytes: &[u8], limits: &ImportLimits) -> Result<Self, Error> {
        let deadline = Deadline::new(limits.timeout);
        deadline.check()?;
        limit(bytes.len(), limits.max_input_bytes, "input bytes")?;
        let prime = modulus::<F>()?;
        let mut reader = Reader::new(bytes);
        if reader.take(4)? != b"r1cs" {
            return Err(Error::InvalidMagic);
        }
        let version = reader.u32()?;
        if version != 1 {
            return Err(Error::UnsupportedVersion(version));
        }
        let section_count = reader.u32()?;
        let mut sections = BTreeMap::new();
        for _ in 0..section_count {
            deadline.check()?;
            let kind = reader.u32()?;
            if !matches!(kind, 1..=3) {
                return Err(Error::UnsupportedSection(kind));
            }
            if sections.contains_key(&kind) {
                return Err(Error::DuplicateSection(kind));
            }
            let size = usize::try_from(reader.u64()?)
                .map_err(|_| Error::InvalidHeader("section size overflows usize"))?;
            sections.insert(kind, reader.take(size)?);
        }
        reader.finish()?;
        for kind in 1..=3 {
            if !sections.contains_key(&kind) {
                return Err(Error::MissingSection(kind));
            }
        }
        let mut header = Reader::new(sections[&1]);
        let field_bytes = header.u32()? as usize;
        if field_bytes != prime.len() {
            return Err(Error::InvalidHeader(
                "noncanonical or unsupported field width",
            ));
        }
        if header.take(field_bytes)? != prime {
            return Err(Error::FieldMismatch);
        }
        let wire_count = header.u32()? as usize;
        let public_outputs = header.u32()? as usize;
        let public_inputs = header.u32()? as usize;
        let private_inputs = header.u32()? as usize;
        let label_count = header.u64()?;
        let constraint_count = header.u32()? as usize;
        header.finish()?;
        let inputs = (public_outputs as u64) + (public_inputs as u64) + (private_inputs as u64);
        if wire_count == 0 || inputs >= wire_count as u64 || label_count < wire_count as u64 {
            return Err(Error::InvalidHeader(
                "wire, role or label counts are inconsistent",
            ));
        }
        limit(wire_count, limits.max_wires, "wires")?;
        limit(constraint_count, limits.max_constraints, "constraints")?;
        let header = Header {
            field_bytes,
            wire_count,
            public_outputs,
            public_inputs,
            private_inputs,
            label_count,
            constraint_count,
        };
        let mut rows = Reader::new(sections[&2]);
        let mut constraints = Vec::new();
        for id in 0..constraint_count {
            deadline.check()?;
            let mut read_lc = || -> Result<LinearCombination<F>, Error> {
                let count = rows.u32()? as usize;
                if count > wire_count {
                    return Err(Error::InvalidLinearCombination { row: id });
                }
                let mut terms = Vec::new();
                let mut previous = None;
                for _ in 0..count {
                    deadline.check()?;
                    let wire = rows.u32()?;
                    if wire as usize >= wire_count {
                        return Err(Error::InvalidWire { row: id, wire });
                    }
                    if previous.is_some_and(|previous| wire <= previous) {
                        return Err(Error::InvalidLinearCombination { row: id });
                    }
                    previous = Some(wire);
                    let bytes = rows.take(field_bytes)?;
                    if bytes.iter().all(|byte| *byte == 0)
                        || bytes.iter().rev().cmp(prime.iter().rev()).is_ge()
                    {
                        return Err(Error::NonCanonicalCoefficient { row: id });
                    }
                    terms.push((wire, decode(bytes)));
                }
                Ok(LinearCombination { terms })
            };
            constraints.push(Constraint {
                id,
                a: read_lc()?,
                b: read_lc()?,
                c: read_lc()?,
            });
        }
        rows.finish()?;
        let mut labels = Reader::new(sections[&3]);
        let mut wire_labels = Vec::new();
        let mut seen = BTreeSet::new();
        for wire in 0..wire_count {
            deadline.check()?;
            let label = labels.u64()?;
            if label >= label_count || !seen.insert(label) || (wire == 0 && label != 0) {
                return Err(Error::InvalidWireMap);
            }
            wire_labels.push(label);
        }
        labels.finish()?;
        deadline.check()?;
        let mut canonical = b"r1cs".to_vec();
        canonical.extend(1u32.to_le_bytes());
        canonical.extend(3u32.to_le_bytes());
        for kind in 1u32..=3 {
            let section = sections[&kind];
            canonical.extend(kind.to_le_bytes());
            canonical.extend((section.len() as u64).to_le_bytes());
            canonical.extend(section);
        }
        let source_digest = sha256_hex(bytes);
        deadline.check()?;
        Ok(Self {
            header,
            constraints,
            wire_labels,
            symbols: Vec::new(),
            source_digest,
            canonical,
            limits: limits.clone(),
        })
    }

    /// Checked original header counts.
    pub fn header(&self) -> &Header {
        &self.header
    }
    /// Original rows, without polynomial expansion or renumbering.
    pub fn constraints(&self) -> &[Constraint<F>] {
        &self.constraints
    }
    /// Original wire-to-label map, indexed by wire ID.
    pub fn wire_labels(&self) -> &[u64] {
        &self.wire_labels
    }
    /// Optional symbol records, ordered by original label ID.
    pub fn symbols(&self) -> &[Symbol] {
        &self.symbols
    }
    /// SHA-256 of the exact input bytes, before normalization.
    pub fn source_digest(&self) -> &str {
        &self.source_digest
    }

    /// Classify an original wire; internal witness wires are not private-input declarations.
    pub fn wire_role(&self, wire: u32) -> Option<WireRole> {
        let wire = wire as usize;
        if wire >= self.header.wire_count {
            return None;
        }
        Some(if wire == 0 {
            WireRole::Constant
        } else if wire <= self.header.public_outputs {
            WireRole::PublicOutput
        } else if wire <= self.header.public_outputs + self.header.public_inputs {
            WireRole::PublicInput
        } else if wire
            <= self.header.public_outputs + self.header.public_inputs + self.header.private_inputs
        {
            WireRole::PrivateInput
        } else {
            WireRole::Internal
        })
    }

    /// Attach a bounded Circom `.sym` sidecar without changing row or wire identity.
    ///
    /// Labels and names must be unique; distinct labels may alias one wire. `-1` retains an
    /// optimized-out signal without inventing a polynomial variable for it.
    pub fn with_symbols(mut self, text: &str) -> Result<Self, Error> {
        let deadline = Deadline::new(self.limits.timeout);
        deadline.check()?;
        limit(text.len(), self.limits.max_input_bytes, "symbol bytes")?;
        let mut labels = BTreeMap::new();
        let mut names = BTreeSet::new();
        for (at, line) in text.lines().enumerate() {
            deadline.check()?;
            limit(at + 1, self.limits.max_symbols, "symbols")?;
            let line_number = at + 1;
            let invalid = || Error::InvalidSymbol { line: line_number };
            let fields: Vec<_> = line.splitn(4, ',').collect();
            if fields.len() != 4 || fields[3].is_empty() {
                return Err(invalid());
            }
            let label: u64 = fields[0].parse().map_err(|_| invalid())?;
            let wire = if fields[1] == "-1" {
                None
            } else {
                Some(fields[1].parse::<u32>().map_err(|_| invalid())?)
            };
            let component: u64 = fields[2].parse().map_err(|_| invalid())?;
            if label >= self.header.label_count
                || wire.is_some_and(|wire| wire as usize >= self.header.wire_count)
                || (label == 0 && wire != Some(0))
                || labels.contains_key(&label)
                || !names.insert(fields[3].to_string())
            {
                return Err(invalid());
            }
            labels.insert(
                label,
                Symbol {
                    label,
                    wire,
                    component,
                    name: fields[3].to_string(),
                },
            );
        }
        self.symbols = labels.into_values().collect();
        deadline.check()?;
        Ok(self)
    }

    /// Evaluate original sparse rows directly; this does not call the polynomial converter.
    pub fn evaluate_assignment(&self, assignment: &[F]) -> Result<Vec<F>, Error> {
        if assignment.len() != self.header.wire_count {
            return Err(Error::AssignmentLength {
                expected: self.header.wire_count,
                actual: assignment.len(),
            });
        }
        if assignment[0] != F::one() {
            return Err(Error::ConstantWire);
        }
        Ok(self
            .constraints
            .iter()
            .map(|row| row.a.dot(assignment) * row.b.dot(assignment) - row.c.dot(assignment))
            .collect())
    }

    /// Expand rows into capacity `N`, replacing wire zero by one and wire i by variable i − 1.
    ///
    /// Padding beyond the active prefix remains unconstrained and is not a new witness wire.
    /// Capacity itself is bounded by `max_wires - 1` to bound per-term monomial storage.
    pub fn expand<const N: usize>(&self) -> Result<Expansion<N, F>, Error> {
        let deadline = Deadline::new(self.limits.timeout);
        deadline.check()?;
        let needed = self.header.wire_count - 1;
        if needed > N {
            return Err(Error::Arity {
                needed,
                capacity: N,
            });
        }
        limit(
            N,
            self.limits.max_wires.saturating_sub(1),
            "polynomial capacity",
        )?;
        let mut result = Expansion {
            polynomials: Vec::new(),
            row_ids: Vec::new(),
            variable_to_wire: (1..self.header.wire_count as u32).collect(),
            stats: ExpansionStats::default(),
        };
        for row in &self.constraints {
            deadline.check()?;
            let products = row
                .a
                .terms
                .len()
                .checked_mul(row.b.terms.len())
                .and_then(|count| result.stats.products.checked_add(count))
                .ok_or(Error::Limit {
                    resource: "products",
                    limit: self.limits.max_products,
                })?;
            limit(products, self.limits.max_products, "products")?;
            result.stats.products = products;
            result.stats.source_terms += row.a.terms.len() + row.b.terms.len() + row.c.terms.len();
            let mut terms = Vec::new();
            for (left, a) in &row.a.terms {
                for (right, b) in &row.b.terms {
                    deadline.check()?;
                    let mut powers = [0u32; N];
                    if *left != 0 {
                        powers[*left as usize - 1] += 1;
                    }
                    if *right != 0 {
                        powers[*right as usize - 1] += 1;
                    }
                    terms.push((Monomial::new(&powers), *a * *b));
                }
            }
            for (wire, coefficient) in &row.c.terms {
                deadline.check()?;
                let mut powers = [0u32; N];
                if *wire != 0 {
                    powers[*wire as usize - 1] = 1;
                }
                terms.push((Monomial::new(&powers), -*coefficient));
            }
            let polynomial = MultivariatePolynomial::new(&terms);
            let count = polynomial.terms().len();
            let expanded = result
                .stats
                .expanded_terms
                .checked_add(count)
                .ok_or(Error::Limit {
                    resource: "expanded terms",
                    limit: self.limits.max_expanded_terms,
                })?;
            limit(expanded, self.limits.max_expanded_terms, "expanded terms")?;
            result.stats.expanded_terms = expanded;
            result.stats.max_row_terms = result.stats.max_row_terms.max(count);
            result.row_ids.push(row.id);
            result.polynomials.push(polynomial);
        }
        deadline.check()?;
        Ok(result)
    }

    /// Canonical three-section R1CS bytes, with sections ordered 1, 2, 3.
    ///
    /// Optional symbols are a sidecar and are excluded; use [`Self::symbol_digest`] to bind them.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.canonical.clone()
    }

    /// SHA-256 of canonical R1CS bytes, independent of section order and optional symbols.
    pub fn canonical_digest(&self) -> String {
        sha256_hex(&self.canonical)
    }

    /// SHA-256 binding a nonempty ordered symbol sidecar to the canonical R1CS identity.
    pub fn symbol_digest(&self) -> Option<String> {
        if self.symbols.is_empty() {
            return None;
        }
        let mut bytes = b"zeebra-r1cs-symbols-v1\0".to_vec();
        bytes.extend(self.canonical_digest().bytes());
        for symbol in &self.symbols {
            bytes.extend(symbol.label.to_le_bytes());
            bytes.extend(symbol.wire.map(i64::from).unwrap_or(-1).to_le_bytes());
            bytes.extend(symbol.component.to_le_bytes());
            bytes.extend((symbol.name.len() as u64).to_le_bytes());
            bytes.extend(symbol.name.bytes());
        }
        Some(sha256_hex(&bytes))
    }
}
