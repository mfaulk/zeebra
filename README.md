![Zeebra](./zeebra.jpg "Zeebra is ZEro knowledge algeBRA")

# Zeebra

[![CI](https://github.com/mfaulk/zeebra/actions/workflows/rust.yml/badge.svg)](https://github.com/mfaulk/zeebra/actions/workflows/rust.yml)

**High-performance computational algebra for cryptographic security analysis.**

Many cryptographic constructions are secure only if some system of polynomial equations over a
finite field is infeasible to solve. Writing a hash function or signature scheme as such a system
makes its security measurable: you can track how the cost of solving grows with the number of
rounds, or recover a solution when one is within reach. Zeebra's long-term goal is to automate
this kind of algebraic security analysis. Today it is the engine such analysis needs, not a turnkey
attack tool.

Zeebra is a Rust library. It provides arithmetic in prime fields from 31 bits up to the BN254 and
BLS12-381 scalar fields, as well as binary and extension fields. On top of that it offers
polynomial arithmetic, dense and sparse linear algebra, Gröbner bases (Buchberger, F4, FGLM), and
[polynomial system solving](docs/guide/solving-systems.md). Recovered solutions are checked against
the original equations. Gröbner computations take explicit memory, matrix-size and time limits, so
an infeasible instance returns a typed error instead of exhausting the machine.

The planner's `PlanBudget::max_elapsed` gates retries and fallbacks; its first attempt always
starts. It does not tighten F4's separate cooperative `max_wall_time` limit, and FGLM has no wall
budget. Use an external supervisor to bound the complete solve; see the
[planner budget contract](docs/guide/solving-systems.md#letting-the-solver-choose).

## Applications

**Hash functions.** Arithmetization-oriented permutations such as Poseidon, Poseidon2 and Griffin
choose their round counts from estimated algebraic attack costs. Zeebra lets researchers measure
those costs on reduced-round instances, as in this
[Griffin FreeLunch study](docs/research/griffin-freelunch.md).

**Zero-knowledge proofs.** Zeebra can [import R1CS](docs/guide/r1cs.md), check assignments, and
expand constraints into polynomial systems. Solving those systems addresses questions such as
whether a witness is uniquely determined, or whether a circuit admits solutions it should not.

**Post-quantum cryptography.** Multivariate schemes rest on the hardness of MQ and MinRank
problems. Solving small and reduced instances tests the complexity estimates behind parameter
choices. Gröbner-basis attacks threaten some schemes and not others, and measurement helps show
which.

## Quickstart

Zeebra builds on stable Rust 1.91 or newer.

```sh
cargo build
cargo test
cargo run --release --example quickstart
```

Find every point in `GF(13)²` where `x + y` and `xy − 1` both vanish:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{fields::Zp13, grobner::solve, MultivariatePolynomial};

let vars = ["x", "y"];
let system = vec![
    MultivariatePolynomial::<2, Zp13>::parse("x + y", vars).unwrap(),
    MultivariatePolynomial::<2, Zp13>::parse("x*y - 1", vars).unwrap(),
];

let mut rng = StdRng::seed_from_u64(0);
for point in solve(&system, &mut rng) {
    println!("x = {}, y = {}", point[0], point[1]);
}
```

Swap `Zp13` for `Bn254Fr` to run the same code over BN254's 254-bit scalar field. The
[Gröbner basis guide](docs/guide/grobner-bases.md) explains the machinery.

## How Zeebra compares

Singular, Magma, msolve and Groebner.jl are mature, fast Gröbner-basis systems. Zeebra differs
from them in four ways:

- **Cryptographic fields.** Singular and msolve limit prime characteristic to below 2³¹. Zeebra
  runs F4, FGLM and solving over 64-bit primes and over the BN254 and BLS12-381 scalar fields.
- **A library, not a system.** Zeebra is plain stable Rust, with no C dependencies and no external
  algebra system. It is MIT-licensed; Singular, msolve and Groebner.jl are GPL, and Magma is
  commercial.
- **Explicit budgets.** Resource limits are part of the API contract.
- **Evidence.** Published measurements name their commit and can be reproduced. Shared benchmark
  problems are checked for ideal equivalence across engines before they are timed.

The [corpus lineage contract](docs/research/corpus-lineage.md) defines instance provenance and
evaluation splits. Validate a catalog with `python3 tools/corpus_lineage.py validate CATALOG.json`,
or check for leakage with `python3 tools/corpus_lineage.py check CATALOG.json SPLIT.json`.
The [retained-corpus audit](research/corpus-lineage/README.md) records known relationships and
unresolved metadata without running solvers. The [M34 public application panel](research/m34-public-corpus/README.md)
admits exact SymbolicData systems and two generated application families (Chandrasekhar H-equation,
multisite phosphorylation) as lineage-checked catalog records, and the
[controlled structural families](research/m34-structural-corpus/README.md) add seeded generators
that each vary one structural property.

Zeebra is competitive but does not lead. It has outperformed Singular on benchmarks such as
Katsura-11 and random MQ systems. In the
[latest integration report](docs/MILESTONE-COMPETITIVE-BENCHMARKING.md#172-competitive-scoreboard)
(M33), grobx stays 1.08–1.48× ahead at one worker on wide primes (2.35× on a held-out random MQ
row), and msolve 1.9–2.8× ahead on MQ10 at 4–8 workers. Zeebra beat msolve on Katsura-11 at 8 workers, but that win did not
hold on the held-out rows. The [competitive board](research/competitive/COMPETITIVE.md) records
every attempt, including those that failed or hit a limit. The current milestone,
[M34](docs/MILESTONE-GENERALIZABLE-SELECTION.md), measures whether choosing among Zeebra's
algorithms per input pays, and looks for one class of systems where Zeebra leads.

Licensed under the [MIT licence](LICENSE-MIT).
