//! Independently generated public families, with fixed ring identities and recorded full bases.
use super::{
    corpus::{CorpusEntry, Equivalence, Rung},
    FieldSpec, Instance,
};
use crate::{
    fields::Zp32003,
    grobner::{
        benchmark_systems::{eco, noon, reimer},
        differential::polynomial_to_string,
    },
    util::sha256_hex,
    MonomialOrder, MultivariatePolynomial,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Tier {
    Smoke,
    Performance,
}

#[derive(Clone, Copy, Debug)]
pub struct PublicCase {
    pub name: &'static str,
    pub family: &'static str,
    pub variables: usize,
    pub tier: Tier,
    pub digests: &'static [(u64, &'static str)],
    pub basis_sha256: &'static str,
    pub quotient_dimension: u64,
    basis: &'static str,
}

pub const CASES: &[PublicCase] = include!("public_corpus_cases.rs");

impl PublicCase {
    /// A reference is usable only for the exact recorded field, ordered variables and generators.
    pub fn reference_for(&self, input: &Instance) -> Result<Vec<&'static str>, &'static str> {
        if self.digests != [(input.field.characteristic, input.digest().as_str())] {
            return Err("public reference input identity mismatch");
        }
        if sha256_hex(self.basis.as_bytes()) != self.basis_sha256 {
            return Err("public reference basis hash mismatch");
        }
        Ok(self.basis.lines().filter(|s| !s.is_empty()).collect())
    }
}

fn build<const N: usize>(case: &PublicCase) -> Instance {
    let polynomials: Vec<MultivariatePolynomial<N, Zp32003>> = match case.family {
        "eco" => eco(),
        "noon" => noon(),
        "reimer" => reimer(),
        _ => unreachable!("registered family"),
    };
    let names: Vec<_> = (1..=N).map(|i| format!("x{i}")).collect();
    let refs: Vec<_> = names.iter().map(String::as_str).collect();
    let system = polynomials
        .iter()
        .map(|p| polynomial_to_string(p, &refs, MonomialOrder::GradedReverseLexicographic))
        .collect();
    let input = Instance::new(
        case.name,
        case.family,
        FieldSpec::prime(32003),
        names,
        system,
        MonomialOrder::GradedReverseLexicographic,
    );
    if case.family == "noon" {
        input.transformed(
            "Noonburg parameter 11/10; multiply each equation by 10, invertible in GF(32003)",
        )
    } else {
        input
    }
}

/// Only the measured GF(32003), grevlex identity is registered; no field or order is silently substituted.
pub fn instance(name: &str, characteristic: u64, order: MonomialOrder) -> Option<Instance> {
    if characteristic != 32003 || order != MonomialOrder::GradedReverseLexicographic {
        return None;
    }
    let case = CASES.iter().find(|c| c.name == name)?;
    Some(match case.variables {
        3 => build::<3>(case),
        4 => build::<4>(case),
        5 => build::<5>(case),
        6 => build::<6>(case),
        8 => build::<8>(case),
        _ => unreachable!("registered width"),
    })
}

/// Register this opt-in collection with CompetitiveBoard::with_corpus without altering historical ladder rows.
pub fn entries() -> Vec<CorpusEntry> {
    CASES
        .iter()
        .map(|c| CorpusEntry {
            name: c.name,
            family: c.family,
            rung: if c.tier == Tier::Smoke {
                Rung::Easy
            } else {
                Rung::Intermediate
            },
            zero_dimensional: true,
            quotient_dimension: Some(c.quotient_dimension),
            equivalence: Equivalence::LiveOracle {
                tool: "Singular build 44105; complete reduced basis committed",
            },
            digests: c.digests,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        grobner::{
            differential::polynomial_to_string, f4_with_options, fglm::QuotientBasis, F4Options,
        },
        FiniteField,
    };
    const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    // Every registered case has a frozen input identity and a nonempty, hash-checked independent basis.
    #[test]
    fn frozen_public_identities_and_references() {
        assert_eq!(CASES.iter().filter(|c| c.tier == Tier::Smoke).count(), 3);
        assert_eq!(
            CASES.iter().filter(|c| c.tier == Tier::Performance).count(),
            3
        );
        for c in CASES {
            let input = instance(c.name, 32003, ORDER).unwrap();
            assert_eq!(input.variables.len(), c.variables);
            assert_eq!(input.digest(), c.digests[0].1);
            assert!(!c.reference_for(&input).unwrap().is_empty());
        }
    }

    // A field, variable-order or monomial-order mismatch cannot reuse a recorded reference.
    #[test]
    fn references_reject_ring_identity_mismatches() {
        let c = &CASES[0];
        assert!(instance(c.name, 2147483647, ORDER).is_none());
        assert!(instance(c.name, 32003, MonomialOrder::Lexicographic).is_none());
        let input = instance(c.name, 32003, ORDER).unwrap();
        let mut changed = input.clone();
        changed.field = FieldSpec::prime(2147483647);
        assert!(c.reference_for(&changed).is_err());
        let mut changed = input.clone();
        changed.variables.swap(0, 1);
        assert!(c.reference_for(&changed).is_err());
        let mut changed = input;
        changed.order = MonomialOrder::Lexicographic;
        assert!(c.reference_for(&changed).is_err());
    }

    fn check<const N: usize>(c: &PublicCase) {
        let input = instance(c.name, 32003, ORDER).unwrap();
        let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
        let system: Vec<MultivariatePolynomial<N, Zp32003>> = input
            .system
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
            .collect();
        let (basis, _) = f4_with_options(&system, ORDER, &F4Options::default()).unwrap();
        let canonical = |basis: &[MultivariatePolynomial<N, Zp32003>]| {
            let mut text: Vec<_> = basis
                .iter()
                .map(|p| polynomial_to_string(p, &names, ORDER))
                .collect();
            text.sort();
            text
        };
        let reference: Vec<_> = c
            .reference_for(&input)
            .unwrap()
            .iter()
            .map(|s| {
                let p = MultivariatePolynomial::<N, Zp32003>::parse(s, names).unwrap();
                p.scale(&p.leading_coefficient(ORDER).inverse())
            })
            .collect();
        assert_eq!(canonical(&basis), canonical(&reference), "{}", c.name);
        assert_eq!(
            QuotientBasis::new(&basis, ORDER, 10000)
                .unwrap()
                .dimension() as u64,
            c.quotient_dimension
        );
    }

    // Three different public families reproduce complete independent bases without an external executable.
    #[test]
    fn smoke_bases_match_the_independent_oracle() {
        for c in CASES.iter().filter(|c| c.tier == Tier::Smoke) {
            match c.variables {
                3 => check::<3>(c),
                4 => check::<4>(c),
                _ => panic!("unexpected smoke width"),
            }
        }
    }

    // Opt-in full solves check the larger Eco, Noon and Reimer references with the shipped defaults.
    #[test]
    #[ignore = "opt-in public performance tier; run with optimized code and a resource guard"]
    fn performance_bases_match_the_independent_oracle() {
        for c in CASES.iter().filter(|c| c.tier == Tier::Performance) {
            match c.variables {
                5 => check::<5>(c),
                6 => check::<6>(c),
                8 => check::<8>(c),
                _ => panic!("unexpected performance width"),
            }
        }
    }
}
