//! What an instance *is*, kept apart from what a machine measured about it.
//!
//! The separation is the whole design. A benchmark instance must not change when a different
//! workstation produces new timings, so a manifest carries only things that are true of the
//! problem — its source, its field, its generators, its known witness — and never a duration or a
//! byte count. Measurements go in an experiment record beside it.
//!
//! # Proved against observed
//!
//! Every claim about an instance's mathematics is tagged. "The quotient dimension is 4096" is
//! usually an *observation* from one computation on one machine; "the system has 20 polynomials in
//! 10 variables" is a *fact* read off the file. A corpus that mixed the two would let an
//! observation harden into an assumption, and M21-0 found exactly that failure mode in the
//! structural analysis — `generators == variables` looks like a dimension claim and is not.
//!
//! # Redistribution
//!
//! [`Provenance::redistribution`] is not paperwork. The Fukuoka files are
//! "COPYRIGHT © 2015 FUKUOKA MQ CHALLENGE All Right Reserved" with no stated licence, so they are
//! **not committed to this repository**; `tools/fetch-mq-challenge.sh` fetches them and the
//! checksum here is what pins the bytes a result was computed against. A corpus that silently
//! redistributed them would be a licensing problem *and* an unpinned one.

use std::fmt::{Display, Formatter};

/// A claim's epistemic status.
///
/// Tagged rather than implied, so that nothing in a report has to be taken on trust about where it
/// came from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Claim<T> {
    /// True of the instance by construction or by reading its definition.
    Proved(T),

    /// Measured, once, somewhere. May be wrong about the instance in general.
    Observed(T),
}

impl<T> Claim<T> {
    /// The value, whatever its status.
    pub fn value(&self) -> &T {
        match self {
            Self::Proved(v) | Self::Observed(v) => v,
        }
    }

    /// Whether this is a fact rather than a measurement.
    pub fn is_proved(&self) -> bool {
        matches!(self, Self::Proved(_))
    }
}

impl<T: Display> Display for Claim<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Proved(v) => write!(f, "{} (proved)", v),
            Self::Observed(v) => write!(f, "{} (observed)", v),
        }
    }
}

/// Where an instance came from, precisely enough to fetch the same bytes again.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Provenance {
    /// Human-readable source, e.g. `"Fukuoka MQ Challenge"`.
    pub source: String,

    /// A version, release date, or commit — whatever that source versions by.
    pub version: String,

    /// Where to get it.
    pub url: String,

    /// SHA-256 of the exact file, lowercase hex.
    ///
    /// The thing that makes a result reproducible. Without it, "we solved type-III n=10 seed 0"
    /// names a file that could have been regenerated.
    pub sha256: String,

    /// Licensing or redistribution terms, in the source's own words where possible.
    ///
    /// `"All rights reserved; not redistributed"` is a complete and useful answer. An empty string
    /// is not, and `Display` says so.
    pub redistribution: String,
}

/// What a benchmark instance is.
///
/// No timings, no memory figures, no machine identity. See the module docs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InstanceManifest {
    /// A stable identifier, e.g. `"fukuoka-mq-III-n10-seed0"`.
    pub id: String,

    /// Schema version, so a stored manifest can be read by a later reader that changed shape.
    pub schema: u32,

    /// Where it came from.
    pub provenance: Provenance,

    /// The base field, as the source names it.
    pub field: String,

    /// The field's characteristic.
    pub characteristic: u64,

    /// The extension degree; 1 for a prime field.
    pub extension_degree: u32,

    /// Variables, in the source's own order. Position is meaningful — it is what a coefficient
    /// vector indexes — so this is a list and not a set.
    pub variables: Vec<String>,

    /// Generators, as a count. The generators themselves live in the source file, which the
    /// checksum pins; copying them here would duplicate data this manifest cannot license.
    pub generators: usize,

    /// The monomial order the source's coefficient layout uses, verbatim from its header.
    pub monomial_order: String,

    /// What solving it means.
    pub objective: String,

    /// A published witness, if the source gives one.
    ///
    /// Coordinates in the same order as [`Self::variables`], as integers so that the manifest is
    /// independent of any coefficient type.
    pub witness: Option<Vec<u64>>,

    /// How a claimed solution is checked independently of zeebra.
    pub verification: String,

    /// `D = dim_F R/I`, when something has said so. **Usually an observation.**
    pub quotient_dimension: Option<Claim<usize>>,
}

impl InstanceManifest {
    /// The current schema version.
    pub const SCHEMA: u32 = 1;

    /// Whether everything a reproducible experiment needs is filled in.
    ///
    /// Returns the names of the fields that are not. A manifest can be constructed incomplete —
    /// it is a record being assembled — and this is what a runner checks before quoting a result
    /// against it.
    pub fn missing(&self) -> Vec<&'static str> {
        let mut missing = Vec::new();
        if self.id.is_empty() {
            missing.push("id");
        }
        if self.provenance.url.is_empty() {
            missing.push("provenance.url");
        }
        if self.provenance.sha256.is_empty() {
            missing.push("provenance.sha256");
        }
        if self.provenance.redistribution.is_empty() {
            missing.push("provenance.redistribution");
        }
        if self.variables.is_empty() {
            missing.push("variables");
        }
        if self.objective.is_empty() {
            missing.push("objective");
        }
        if self.verification.is_empty() {
            missing.push("verification");
        }
        missing
    }

    /// Whether [`Self::missing`] is empty.
    pub fn is_complete(&self) -> bool {
        self.missing().is_empty()
    }
}

impl Display for InstanceManifest {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "instance        {}", self.id)?;
        writeln!(f, "schema          {}", self.schema)?;
        writeln!(
            f,
            "source          {} {}",
            self.provenance.source, self.provenance.version
        )?;
        writeln!(f, "url             {}", self.provenance.url)?;
        writeln!(f, "sha256          {}", self.provenance.sha256)?;
        writeln!(f, "redistribution  {}", self.provenance.redistribution)?;
        writeln!(
            f,
            "field           {} (characteristic {}, degree {})",
            self.field, self.characteristic, self.extension_degree
        )?;
        writeln!(
            f,
            "size            {} generators in {} variables",
            self.generators,
            self.variables.len()
        )?;
        writeln!(f, "monomial order  {}", self.monomial_order)?;
        writeln!(f, "objective       {}", self.objective)?;
        writeln!(
            f,
            "witness         {}",
            match &self.witness {
                Some(w) => format!("published, {} coordinates", w.len()),
                None => "none published".to_string(),
            }
        )?;
        writeln!(f, "verification    {}", self.verification)?;
        if let Some(dimension) = &self.quotient_dimension {
            writeln!(f, "quotient dim    {}", dimension)?;
        }
        let missing = self.missing();
        if missing.is_empty() {
            write!(f, "complete        yes")
        } else {
            write!(f, "complete        no — missing {:?}", missing)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Claim, InstanceManifest, Provenance};

    fn manifest() -> InstanceManifest {
        InstanceManifest {
            id: "fukuoka-mq-III-n10-seed0".to_string(),
            schema: InstanceManifest::SCHEMA,
            provenance: Provenance {
                source: "Fukuoka MQ Challenge".to_string(),
                version: "type III toy example, retrieved 2026-11-04".to_string(),
                url: "https://www.mqchallenge.org/toy-example/ToyExample-type3-n10.tar.bz2"
                    .to_string(),
                sha256: "9436e45dbd4247f152681e954f1db19d92e8cf5e76b2bc35530bed74aae522ba"
                    .to_string(),
                redistribution: "All rights reserved; not redistributed".to_string(),
            },
            field: "GF(31)".to_string(),
            characteristic: 31,
            extension_degree: 1,
            variables: (0..10).map(|i| format!("x{}", i)).collect(),
            generators: 20,
            monomial_order: "graded reverse lex order".to_string(),
            objective: "find any x with F(x) = 0".to_string(),
            witness: Some(vec![22, 22, 28, 12, 9, 2, 1, 18, 11, 25]),
            verification: "evaluate the imported coefficient vectors at the candidate".to_string(),
            quotient_dimension: Some(Claim::Observed(1)),
        }
    }

    /// A manifest with everything filled in is complete, and says so.
    #[test]
    fn test_a_complete_manifest() {
        let manifest = manifest();
        assert!(manifest.is_complete());
        assert_eq!(manifest.missing(), Vec::<&str>::new());
        assert!(manifest.to_string().contains("complete        yes"));
    }

    /// Each required field is reported by name when it is absent.
    #[test]
    fn test_missing_fields_are_named() {
        let mut manifest = manifest();
        manifest.provenance.sha256.clear();
        manifest.verification.clear();
        assert!(!manifest.is_complete());
        assert_eq!(
            manifest.missing(),
            vec!["provenance.sha256", "verification"]
        );
        assert!(manifest.to_string().contains("missing"));

        // Redistribution terms are required, and "unknown" is not the same as absent: an empty
        // string is a gap, and a stated "all rights reserved" is an answer.
        let mut manifest = manifest.clone();
        manifest.provenance.redistribution.clear();
        assert!(manifest.missing().contains(&"provenance.redistribution"));
    }

    /// A claim carries its status, and the two are not interchangeable.
    #[test]
    fn test_claims_distinguish_proved_from_observed() {
        let proved: Claim<usize> = Claim::Proved(20);
        let observed: Claim<usize> = Claim::Observed(1);

        assert!(proved.is_proved());
        assert!(!observed.is_proved());
        assert_eq!(proved.value(), &20);
        assert_eq!(observed.to_string(), "1 (observed)");
        assert_eq!(proved.to_string(), "20 (proved)");

        // The same number with different statuses is not the same claim.
        assert_ne!(Claim::Proved(1), Claim::Observed(1));
    }

    /// A manifest holds nothing a machine measured, which is what keeps it stable.
    ///
    /// Enforced by review rather than by the type system, so this test is a statement of intent
    /// with teeth: it will fail to compile if a timing field is ever added.
    #[test]
    fn test_a_manifest_carries_no_measurements() {
        let manifest = manifest();
        let printed = manifest.to_string();
        for forbidden in ["ms", "seconds", "bytes", "MB", "elapsed", "memory"] {
            assert!(
                !printed.contains(forbidden),
                "a manifest must not carry {}: {}",
                forbidden,
                printed
            );
        }
        // The one number that could be mistaken for a measurement is tagged as one.
        assert_eq!(manifest.quotient_dimension, Some(Claim::Observed(1)));
    }
}
