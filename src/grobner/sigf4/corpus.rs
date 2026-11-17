//! RFC §10.1's deterministic correctness constructions, pinned by canonical SHA-256 before any
//! timing so that a later edit to a generator cannot silently change what was checked.

use crate::{
    fields::{PrimeFieldElement64, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, katsura},
        differential::polynomial_to_string,
        external::{corpus::random_mq_instance, FieldSpec, Instance},
    },
    poly::MonomialOrder,
    KnownOrder, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const SMALL: u64 = 32_003;
const GOLDILOCKS: u64 = 18_446_744_069_414_584_321;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Underdetermined,
    Overdetermined,
    NonRadical,
    PositiveDimensional,
}

/// One RFC §10.1 construction, buildable over GF(32003) or Goldilocks.
#[derive(Clone, Copy, Debug)]
pub struct Construction {
    pub name: &'static str,
    kind: Kind,
}

/// The four constructions, in the order RFC §10.1 lists them.
pub fn correctness_constructions() -> [Construction; 4] {
    [
        Construction {
            name: "katsura-4-minus-last",
            kind: Kind::Underdetermined,
        },
        Construction {
            name: "mq-random-10-plus-seed-1",
            kind: Kind::Overdetermined,
        },
        Construction {
            name: "katsura-4-squared",
            kind: Kind::NonRadical,
        },
        Construction {
            name: "cyclic-4",
            kind: Kind::PositiveDimensional,
        },
    ]
}

/// `(name, characteristic, SHA-256 of the canonical instance)`, recorded in #857's first commit.
pub const PINNED_DIGESTS: [(&str, u64, &str); 8] = [
    (
        "katsura-4-minus-last",
        SMALL,
        "e7622343f1905f69b4a2dc60bdd7e01ea7e4ee8f6829684c012d37c930978c26",
    ),
    (
        "katsura-4-minus-last",
        GOLDILOCKS,
        "0b7a2d34bd0a9479e46f89b37dc82b61b55f163248e4866e928bab79983847f3",
    ),
    (
        "mq-random-10-plus-seed-1",
        SMALL,
        "af500f7ff835b607531261b952dd1b7adf704e62ec8c9df39a94c1a8b7b7b6a9",
    ),
    (
        "mq-random-10-plus-seed-1",
        GOLDILOCKS,
        "9adc9a067d18194040ec6ed88883dca553ecfe020e8f58f6e7cbc71bfda9b473",
    ),
    (
        "katsura-4-squared",
        SMALL,
        "22fce84818fe27cc6a33b31437df07c7bd05207a9ddd6eaea43c042aaa45fb08",
    ),
    (
        "katsura-4-squared",
        GOLDILOCKS,
        "b702babbf7f32d75956ea78f1e0b23c9bf08f9dc498d396e22800e7122eb2908",
    ),
    (
        "cyclic-4",
        SMALL,
        "349d257b6c26e81f293f0e9936462752428375d21cf423a822d6ddfa39d2bcd4",
    ),
    (
        "cyclic-4",
        GOLDILOCKS,
        "756987e9b6f1752de623e69c2f6cc1570cff5dbeab926af1a1c87423a6e19053",
    ),
];

impl Construction {
    /// Number of variables, which fixes the const-generic arity a caller instantiates.
    pub fn variables(&self) -> usize {
        match self.kind {
            Kind::Overdetermined => 10,
            _ => 4,
        }
    }

    fn transformation(&self) -> &'static str {
        match self.kind {
            Kind::Underdetermined => "katsura-4 without its last generator",
            Kind::Overdetermined => {
                "mq-random-10 (seed 10) followed by the 10 generators of mq-random-10 at seed 1"
            }
            Kind::NonRadical => "katsura-4 with each generator squared",
            Kind::PositiveDimensional => "cyclic-4, unchanged",
        }
    }

    /// The system over `F`. Panics if `N` is not [`Self::variables`].
    pub fn system<const N: usize, F: KnownOrder>(&self) -> Vec<MultivariatePolynomial<N, F>> {
        assert_eq!(N, self.variables(), "{} has {} variables", self.name, N);
        match self.kind {
            Kind::Underdetermined => {
                let mut system = katsura::<N, F>();
                system.pop();
                system
            }
            Kind::NonRadical => katsura::<N, F>().iter().map(|p| p * p).collect(),
            Kind::PositiveDimensional => cyclic::<N, F>(),
            Kind::Overdetermined => {
                let p = F::characteristic_u128().expect("a prime field") as u64;
                let mut generators = random_mq_instance(N, 10, p, ORDER).system;
                generators.extend(random_mq_instance(N, 1, p, ORDER).system);
                let names: Vec<String> = random_mq_instance(N, 10, p, ORDER).variables;
                let names: [&str; N] = std::array::from_fn(|i| names[i].as_str());
                generators
                    .iter()
                    .map(|g| MultivariatePolynomial::parse(g, names).expect("generator parses"))
                    .collect()
            }
        }
    }

    /// The canonical instance at `characteristic` (32003 or Goldilocks).
    pub fn instance(&self, characteristic: u64) -> Instance {
        match (self.variables(), characteristic) {
            (4, SMALL) => self.render::<4, Zp32003>(characteristic),
            (4, GOLDILOCKS) => self.render::<4, Goldilocks>(characteristic),
            (10, SMALL) => self.render::<10, Zp32003>(characteristic),
            (10, GOLDILOCKS) => self.render::<10, Goldilocks>(characteristic),
            other => panic!("no instantiation for {other:?}"),
        }
    }

    fn render<const N: usize, F: KnownOrder>(&self, characteristic: u64) -> Instance {
        let names: Vec<String> = if self.kind == Kind::Overdetermined {
            random_mq_instance(N, 10, characteristic, ORDER).variables
        } else {
            (1..=N).map(|i| format!("x{i}")).collect()
        };
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        let generators = self
            .system::<N, F>()
            .iter()
            .map(|p| polynomial_to_string(p, &refs, ORDER))
            .collect();
        Instance::new(
            self.name,
            "sigf4-correctness",
            FieldSpec::prime(characteristic),
            names,
            generators,
            ORDER,
        )
        .transformed(self.transformation())
    }
}
