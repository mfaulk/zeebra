![Zeebra](./zeebra.jpg "Zeebra is ZEro knowledge algeBRA")

# Zeebra — High-performance computational algebra over finite fields
[![CI](https://github.com/mfaulk/zeebra/actions/workflows/rust.yml/badge.svg)](https://github.com/mfaulk/zeebra/actions/workflows/rust.yml)

**Zeebra is a computational algebra library, in Rust, for developing and analyzing advanced
cryptography.** 

Zeebra provides the algebraic primitives that zero-knowledge proof systems are built
from — fast arithmetic over cryptographically large finite fields, polynomials, linear algebra — and
a Gröbner basis engine for the nonlinear systems whose hardness those primitives depend on for
security.

Zeebra is a library rather than a shell: plain Rust, generic over a `FiniteField` trait, stable toolchain, no C
dependencies and no linked algebra system.

## What it is

Zero-knowledge proofs, and the hash functions designed for them, are built almost
entirely out of arithmetic in large finite fields: number systems of 31 to 256 bits in which
addition and multiplication wrap around a prime. Zeebra implements those number systems and the mathematics
needed to build cryptography from them: fast field arithmetic, univariate and multivariate polynomials, dense and sparse
linear algebra, and the number-theoretic transform (the Fast Fourier Transform for finite fields). 

Zeebra is also a solver. A ZK-friendly primitive is an algebraic object, like a low-degree round
function iterated a few times, and its security claim is that the system of polynomial equations
describing it cannot be solved in a feasible length of time. Deciding whether that is true, for a given design
at a given number of rounds, is a computation: build the polynomial system, compute a Gröbner
basis, and read the solutions off it. Zeebra implements that pipeline end to end. Buchberger's
algorithm and Faugère's F4 compute bases under lexicographic, graded, graded-reverse, weighted
and two-block elimination orders. FGLM converts a cheap basis into the lexicographic one that
solves by back-substitution;
resultants offer a second, independent elimination route; and univariate root finding and
factorization finish the job. The solver returns *verified field points*. Every stage carries an explicit resource budget for managing 
the cost of solving systems at the frontier of feasibility. F4 construction refusals report the complete
matrix's entry demand before allocating coefficient rows; elimination refusals report the live count
at the crossing, which is a lower bound on the eventual peak.

Nuts and bolts: Zeebra's coefficient domains run to 256-bit prime fields
in Montgomery and CIOS form (BN254 and BLS12-381 scalar fields, Proth primes, Mersenne-31, 64-bit
primes), binary fields using carry-less multiplication, and general extension fields, with field
equations `x^q - x` available so a quotient dimension counts base-field points. F4 ships
Gebauer–Möller and the chain criterion, symbolic preprocessing over interned monomial handles,
sparse Macaulay matrices with selectable elimination backends, Hilbert-function degree bounds, and
per-stage timing and memory instrumentation. The zero-dimensional pipeline is differentially tested
against Singular, and timed against Singular, msolve, Groebner.jl and Sagebrush on a shared corpus
whose ideals are checked for equivalence before any timing is published.

The competitive sweep includes a univariate-eliminant task at published primes within msolve's
supported range. List it with `cargo run --release --example competitive_sweep -- --characteristic 32003 --list`. Eliminant ratios require matching reported degrees and agreement on all shared
invariants; unsupported engines remain visible as capability rows. See the
[external-engine guide](docs/guide/external-engines.md) for measured runs and board regeneration. Caller-owned
harnesses can add prime-field and variable-width pairs with
`ZeebraSolver::with_instantiation::<N, F>()`; the guide includes a runnable registration example.

The ladder also includes `mq-planted-wide-{6,10,14}` over `2^64 - 353`, checked against
Groebner.jl, groebner-rs and grobx. List those frozen identities with
`cargo run --release --example competitive_sweep -- --characteristic 18446744073709551263 --list`.
The [wide-field run instructions](docs/guide/external-engines.md#wide-planted-mq-ladder) cover
live full-basis verification and recording results with live-oracle provenance. The sweep also
accepts `--engines grobx` to select the pinned grobx driver.

## Quickstart

Zeebra builds on stable Rust 1.91 or newer. No nightly toolchain, no feature gates, no system
libraries.

```sh
cargo build
cargo test
```

Solving a system over a finite field — every point of `F^N` where the polynomials vanish:

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

For workloads that may be positive-dimensional, opt into
`PlannedSolveOptions::with_policy(SolvePolicy::ClassifyThenDirectLex)` with
`grobner::solve_one_planned`. It classifies a grevlex basis before direct lex elimination and
charges both computations to the batch allowance. Finite systems pay for the extra basis; see the
[solver guide](docs/guide/solving-systems.md) and the
[classification comparison](docs/research/classify-before-lex.md).

A Gröbner basis directly, by F4:

```rust
use zeebra::{fields::Zp13, grobner::f4, MonomialOrder, MultivariatePolynomial};

let vars = ["x", "y", "z"];
let system = vec![
    MultivariatePolynomial::<3, Zp13>::parse("x*z - y^2", vars).unwrap(),
    MultivariatePolynomial::<3, Zp13>::parse("x^3 - z^2", vars).unwrap(),
];

let basis = f4(&system, MonomialOrder::GradedReverseLexicographic).unwrap();
```

`cargo run --release --example quickstart` walks through field elements, polynomial arithmetic, a
Gröbner basis, solving, and an explicit resource limit in one program.

Every Rust example in this file and in [`docs/guide/`](docs/guide) is compiled and run by
`cargo test --doc`, so none of them can drift from the API.

Criterion benchmarks cover field arithmetic, polynomial arithmetic, dense and sparse linear algebra,
and Gröbner basis computation:

```sh
cargo bench                      # everything
cargo bench --bench grobner      # one suite
cargo bench --bench f4_stages    # F4, stage by stage
```

Compare monomial evaluation across exponentiation strategies with
`cargo bench --bench pow_strategy -- 'small_exponent/.*/eval/'`.
Evaluation uses fixed addition chains for exponents 0–5 and the field's general exponentiation
for larger exponents; the [evaluation study](docs/research/monomial-evaluation.md) records the gate.

Wall-clock time does not say *why* a Gröbner computation cost what it did, so the algorithmic
counters are reported by examples rather than benchmarks:

```sh
cargo run --release --example f4_statistics   # pairs, reductions, zero reductions, basis size
cargo run --release --example f4_profile      # cost attributed per stage
cargo run --release --example mq10_profile -- 32003 --stages  # current-default MQ10, JSON
cargo run --release --example mq10_profile -- 2147483647     # clocks disabled control
cargo run --release --features research-work --example mq10_profile -- 32003 --stages --work
cargo run --release --example solve_one       # a system in, verified solutions out
```

A pinned [sdiehl/groebner subprocess driver](tools/external/groebner-driver/README.md) adds a Rust
F4 comparand without adding root runtime dependencies. Provision it with
`tools/external/provision-groebner-rs.sh`; the adapter checks the engine's ring and complete reduced
basis independently before retaining a timing result. See the
[external-engine guide](docs/guide/external-engines.md#pinned-rust-f4-comparand) for the focused
comparison, supported tasks and resource policy. The
[initial comparison](docs/research/groebner-rs-comparand.md) retains both measurement cohorts and
the corrected memory provenance.

[`docs/guide/benchmarking.md`](docs/guide/benchmarking.md) is the full list — around fifty
instrumented examples — along with the measurement rules this repository follows: a benchmark lock
so two runs cannot share a machine, a memory ceiling guard, and a lint that refuses a published
figure carrying no commit.

The pinned F4 matrix corpus has a separate opt-in large set. Run
`cargo run --release --example f4_matrix_corpus -- check-large` to capture and verify it;
`check-all` verifies both sets; `list-large` shows the large dimensions and explicit live-entry budgets without computing a basis.
The default corpus walk and benchmark smoke retain the bounded small set. See the
[corpus report](docs/research/f4-matrix-corpus.md) for capture costs and limits.

For the monomial-order dispatch and F4 column-sort replay, build with
`cargo build --release --example monomial_order_width` and follow the pinned run command in the
[benchmarking guide](docs/guide/benchmarking.md#monomial-order-width).

`cargo run --release --example monomial_degree_profile -- katsura-7-grevlex` reports F4
stage times and process peak RSS, and writes the full basis to stdout for comparison across
representations. `cargo run --release --example monomial_packing` compares the production
comparator with experimental order-specific byte-packed keys; unsupported widths or degrees
retain the full comparison. These are measurement tools, not a packed public monomial type.
The [cached-degree study](docs/research/monomial-degree.md) records the rejected cache prototype,
exact basis checks and measured stage/RSS results.

Compare dense and Euclidean Sylvester kernels at the same worker count with
`cargo run --release --example determinant_width -- --compare-kernels --order 162 --width 32`.
The comparison checks every sample and reports a determinant-stage ratio; it excludes interpolation
and root finding. See the [five-axis decision](docs/research/structured-sylvester.md) for the
algorithm choice and the [measurement protocol](docs/guide/benchmarking.md#sylvester-kernel-comparison)
for pinned runs.

Univariate `gcd` uses classical Euclid. Run `cargo run --release --example gcd_crossover`
to compare the experimental half-GCD route over KoalaBear, Goldilocks, and BN254. The
[half-GCD measurements](docs/research/fast-univariate.md#194-experimental-half-gcd)
include the commands for a pinned run.

The FGLM converter uses certified scalar Wiedemann adaptively for large sparse shape-position
quotients. `FglmOptions::conversion_strategy` selects `Adaptive` by default; choose `Classical`
to retain the lex walk. Statistics record the route and fallback reason;
failed projections never return an unchecked basis. The [conversion guide](docs/guide/grobner-bases.md#certified-scalar-wiedemann)
describes budgets and the comparison example. [Paired measurements](docs/research/certified-wiedemann.md)
record the public benchmark inputs and the limits on the performance claims.

For partial elimination, run `cargo run --example block_elimination`. A checked
`BlockOrder` makes the eliminated prefix dominant while allowing lex, grlex or
grevlex within each block. See the [two-block order guide](docs/guide/grobner-bases.md#two-block-elimination-orders)
for validation, extraction of the retained basis, and current adapter/FGLM limits.

### Cargo features

| Feature | Default | What it adds |
|---|---|---|
| `external-runners` | on | Drives msolve, Groebner.jl, Sagebrush and Singular as subprocesses. Uses only `std` and adds no dependency. |
| `proptest` | off | `proptest::arbitrary::Arbitrary` for the public types: field elements, big integers, monomials, polynomials, vectors and matrices. Lets you property-test downstream code with `any::<T>()`. |

```toml
zeebra = { version = "0.1", features = ["proptest"] }
```

`Ring` does not require `Arbitrary`, so you can implement it for your own type whether or not the feature is on.

For a finite `QuotientAlgebra`, bounded variable minimal and characteristic
polynomials retain nilpotent multiplicities over every field characteristic.
Run `cargo run --release --example quotient_spectra -- 4 dense`; the
[quotient operator guide](docs/guide/grobner-bases.md#quotient-operator-polynomials)
describes limits and coefficient conventions.

The isolated F4 [batch-splitting study](docs/research/f4-batch-splitting.md)
can be run with `cargo run --example batch_splitting_study -- cyclic-4 adaptive rows 7`
(requires Singular and GNU `timeout`). It tests transactional construction retries
under fixed matrix allowances; the shipping solver and its defaults are unchanged.

## What is in the box

| Area | Guide |
|---|---|
| Finite fields: 31- to 256-bit primes, binary fields, extension fields | [`finite-fields.md`](docs/guide/finite-fields.md) |
| Polynomials: multivariate arithmetic, GCD, squarefree decomposition, factorization | [`polynomials.md`](docs/guide/polynomials.md) |
| Bounded R1CS v1 import, wire identity, independent assignment checks | [`r1cs.md`](docs/guide/r1cs.md) |
| Linear algebra: dense and sparse matrices, echelon backends | [`linear-algebra.md`](docs/guide/linear-algebra.md) |
| NTT and fast univariate arithmetic, root finding | [`ntt.md`](docs/guide/ntt.md) |
| Gröbner bases: Buchberger, monomial orders, FGLM conversion | [`grobner-bases.md`](docs/guide/grobner-bases.md) |
| F4, its resource budgets, and Hilbert functions | [`f4.md`](docs/guide/f4.md) |
| Solving zero-dimensional systems, and route selection | [`solving-systems.md`](docs/guide/solving-systems.md) |
| Integers, perfect powers, Lenstra's elliptic curve method | [`number-theory.md`](docs/guide/number-theory.md) |
| Reed–Solomon codes over an FFT domain | [`reed-solomon.md`](docs/guide/reed-solomon.md) |

Submitted Gröbner bases can carry exact cofactor witnesses for reverse ideal inclusion.
`grobner::verify_ideal_membership` checks individual identities;
`grobner::certify_submitted_basis_with_witnesses` combines them with the existing basis checks.
See the [witness contract and limits](docs/guide/grobner-bases.md#exact-submitted-basis-witnesses)
and run `cargo run --release --example membership_witness`. Witness budgets do not bound the
existing normal-form certification phase. A [small release sample](docs/research/membership-witnesses.md)
records timing and process-memory context.

## How Zeebra relates to existing systems

Gröbner basis computation already has excellent implementations. **Singular**, **Macaulay2** and
**Magma** are computer algebra systems: you drive them from their own language, interactively or by
script. **msolve** is a C library and command-line tool specializing in solving. **Groebner.jl** is
a Julia package. In Rust, **arkworks** covers field and curve arithmetic for proof systems but not
polynomial system solving. Zeebra occupies the gap between those two groups, and differs in four
ways that matter:

- **It is a library you link, under a permissive licence.** Singular, msolve and Groebner.jl are
  GPL; Magma is commercial. Zeebra is MIT.
- **The coefficient fields are the cryptographic ones.** Singular and msolve cap a prime
  characteristic below 2^31 — a limit visible in this repository's own comparison runs, where both
  decline the 64-bit and 254-bit instances. Zeebra runs F4, FGLM and zero-dimensional solving over
  BN254 and BLS12-381 scalar fields, and over binary and extension fields, with no change of
  representation.
- **It is Rust, with resource behaviour as part of the contract.** One toolchain, no FFI boundary,
  and budgets on matrix entries, bytes and degree that produce a typed error instead of exhausting
  the machine.
- **Correctness is checked against other systems, not asserted.** The zero-dimensional pipeline is
  differentially tested against Singular, and a cross-library corpus of standard families — Katsura,
  Cyclic, random MQ — is checked for ideal equivalence before any comparison is run.

The Cyclic corpus includes seven affine systems over `GF(2)` with no field equations adjoined.
The [characteristic-two results](docs/research/classical-benchmarks.md#10-gf2-the-cyclic-invariants-measured-427)
record a Krull dimension of 4 for Cyclic-10. Use
[`grobner::krull_dimension`](docs/guide/grobner-bases.md#krull-dimension) to compute the dimension from a Gröbner basis.
List the published `GF(2)` systems with `cargo run --release --example competitive_sweep -- --characteristic 2 --list`.

The [competitive board](research/competitive/COMPETITIVE.md) retains cross-engine attempts,
including resource refusals. Affine Cyclic-7 and Cyclic-8 already provide reachable same-machine
comparisons; the [Cyclic family decision](docs/research/classical-benchmarks.md#61-429-the-affine-ladder-makes-a-homogenized-comparison-family-unnecessary)
records why the corpus keeps this formulation. The [upper-rung sweep](docs/research/cross-library-corpus.md#9c-489-the-sweep-taken-and-two-things-it-corrected)
records the per-rung budgets and limitations of its single-run comparisons.
The [matched-ISA Sagebrush re-take](docs/research/sagebrush-matched-isa.md) records
the original public-algebra cells with both engines built at the same ISA floor.

The optional [sylvester F4 comparand](tools/external/sylvester-driver/README.md) supplies raw
reduced bases and independently verified v2 trace certificates through a pinned subprocess.
Provision it with `tools/external/provision-sylvester.sh`; certified records use a separate
objective and include proof production and checking. See the
[adapter guide](docs/guide/external-engines.md#sylvester) and
[retained results](docs/research/sylvester-comparand.md), including the extended certification
work-cap refusal.

The [dense-F4 anchors](docs/research/classical-benchmarks.md#24-441-the-dense-f4-ladder-and-the-conversion-stage-caution)
record Steel's published configurations and MinRank stage split, with a density candidate based on
field cardinality for future planner work. These historical figures provide context; they are not
same-machine comparisons against Zeebra.

The [M26 integration report](docs/MILESTONE-ALGORITHMIC-ELIMINATION.md#14-integration-report-2026-11-11)
scores the shipped Euclidean resultant, root-finding measurements and retained engine records.
It records the state at its evidence snapshot; subsequent certified scalar conversion is described
in the [conversion guide](docs/guide/grobner-bases.md#certified-scalar-wiedemann). An isolated
before/after RSS measurement for the earlier basis-storage change remains missing. Later M27
F4 defaults close the measured Singular gap on the reported MQ cohort; the report identifies that
cohort separately from the historical M26 baseline.

The [M27 integration report](docs/MILESTONE-COMPETITIVE-MQ-SOLVING.md#15-integration-report-2026-11-11)
scores the retained library-scope Minimum and Strong criteria as met. The paired F4 cohort measures
5.86x faster complete MQ basis computation than the old defaults, with increased peak RSS;
conversion gains are reported separately. It records the competitive limits, negative results and
unfinished studies, and recommends bounded current-default profiling before further solver work.
Regenerate the retained competitive board without measuring with
`cargo run --release --example competitive -- --write`.

A pinned [grobx subprocess comparand](tools/external/grobx-driver/README.md) checks full reduced
bases against Singular, or an exact independent cofactor checker at wide primes. Provision it with
`tools/external/provision-grobx.sh`; raw computation and exact-certified computation have separate
IDs and resource keys. The [external-engine guide](docs/guide/external-engines.md#grobx)
documents the bounded comparison and the revision's serial worker contract. The
[retained comparison](docs/research/grobx-comparand.md) records current-default MQ results,
proof costs, successful wide controls and conservative harness refusals separately.

## Contributing and documentation

The [M27 algorithm decision](docs/research/m27-algorithm-decision.md) records why an additional
solver prototype is deferred, the capabilities already implemented, and the measurements that
would justify revisiting the decision.

- [`docs/guide/development.md`](docs/guide/development.md) — building, the test matrix, CI's shorter
  documentation path, build-timing artifacts, and the build configuration
- [`docs/guide/benchmarking.md`](docs/guide/benchmarking.md) — benchmark suites, instrumented
  examples, and the rules for publishing a measurement
- [`docs/guide/external-engines.md`](docs/guide/external-engines.md) — differential testing against
  Singular, and the contract for driving external engines
- [`docs/`](docs) — milestone records and [`docs/research/`](docs/research) notes, where the design
  decisions and their measurements are argued out
- [`CHANGELOG.md`](CHANGELOG.md) — release notes, including breaking changes
- [CLAUDE.md](CLAUDE.md) — repository conventions, including how concurrent coding agents claim work

Licensed under the [MIT licence](LICENSE-MIT).

F4 defaults to 32 million live entries and 512 MB of matrix payload, sized from measured
reduced-row peaks. `baseline()` retains 20 million entries and 320 MB. These are matrix limits;
process RSS also includes basis storage, queues and scratch. See the
[budget decision](docs/research/f4-live-budget.md) for the measurements and remaining refusals.

Measure an F4 entry-budget limit with `cargo run --release --example f4_live_budget --
mq-random-10 20000000 reduced`. The example also accepts caller-supplied polynomial systems and
reports outcomes, exact basis digests, completed-batch entry peaks and process RSS separately.
See [the live-budget protocol](research/live-entry-budget/README.md) for bounded runs and input
provenance.

The [current-default MQ10 profiling report](docs/research/mq10-current-profile.md) gives the
matched stage/control campaign and instruction-profile reproduction commands.

The [grobx trajectory study](docs/research/grobx-trajectory.md) separates algebraic
work, coefficient traffic and live matrix storage, including abandoned signature
runs. Its [reproduction guide](research/grobx-trajectory/README.md) documents optional
passive counters and matched full-basis-verified controls; solver defaults are unchanged.

A completed external process can have unavailable RSS if it exits before sampling. The supervisor
preserves its exit result and leaves the peak unavailable; adapters with child self-high-water
reports validate those reports against the requested memory cap. See the
[external-engine guide](docs/guide/external-engines.md#completed-processes-and-rss-evidence).

The [verified public corpus](research/public-corpus/README.md) adds Eco, Noonburg and Reimer
families, with three offline CI fixtures and three opt-in performance rungs. Run
`cargo run --release --example public_corpus -- --list` to inspect their exact inputs.

The [row-merge experiment](research/row-merge/README.md) uses `row_merge_study` to replay pinned F4 matrices through Sparse, Dense and Adaptive
forward elimination followed by production back-substitution. Use `--matrix LABEL --backend
sparse|dense|adaptive`; `--mode work` additionally verifies a diagnostic replay and separates row
work targeting inherited reducer-pivot columns from newly discovered pivots. The diagnostic
counters model logical tuple work, not hardware bandwidth. `--mode solve --row cyclic-5 --modulus
32003` runs a classical full-basis control with shipped options and a 60-second solver limit.
Sparse row subtraction merges only the target tail starting at the pivot's leading column;
untouched prefixes stay in place, and the merged tail is copied back. Caller-owned scratch and each row's own growth policy are
preserved to avoid propagating a large pivot's buffer capacity across the matrix.

The [elimination-kernel report](docs/research/elimination-kernels.md) records the verified
prefix-merge results, three-field backend measurements, and the distinction between logical tuple
traffic and physical memory bandwidth.

The [remaining H13 kernel study](research/elimination-kernels/README.md) provides nested density
masks on captured matrices and an isolated scalar GF(32003) delayed-reduction pilot. Run
`cargo run --release --example elimination_kernel_study -- m31 k7 8 adaptive` for the unmodified
Katsura-7 capture, or `-- --arithmetic` for the exact arithmetic feasibility check. The pilot overlay
is used only in disposable research builds; the shipping backend and field API are unchanged.

The [measured H13 decision](docs/research/elimination-kernels.md#h13-remainder-density-curves-and-the-scalar-delayed-reduction-gate)
retains the three-field density curves, full-solve controls and the negative delayed-pilot shipping
decision. Regenerate its checked CSV and paired summaries with
`python3 research/elimination-kernels/summarize.py`.

The [randomized-reduction study](research/grobx-randomization/README.md) provides independent
Grobx feature controls, exact residual-span feasibility checks, and a bounded full-basis-verified
campaign. Its GPL experiment remains outside the MIT library; Zeebra's deterministic defaults
are unchanged.
