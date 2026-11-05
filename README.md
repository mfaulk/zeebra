
![Zeebra](./zeebra.jpg "Zeebra is ZEro knowledge algeBRA")

# Zeebra is ZEro-knowledge algEBRA
[![CI](https://github.com/mfaulk/zeebra/actions/workflows/rust.yml/badge.svg)](https://github.com/mfaulk/zeebra/actions/workflows/rust.yml)

Zeebra implements a subset of computational algebra and number theory for zero-knowledge cryptography.

## Why You Should Use Zeebra
As the saying goes, you can either make software so simple that it obviously has no bugs, or so complicated that it has no obvious bugs. Zeebra emphasizes clear documentation,  published references for algorithmic implementations, interoperability with Sage, and property-based testing for exhaustive test coverage.

### Status
- [x] Big Integers
- [x] Integer Factoring
- [x] Finite Field Arithmetic for Large Finite Fields
- [x] Univariate and Multivariate Polynomials over Finite Fields
- [x] Linear Algebra over Finite Fields
- [x] Number-Theoretic Transform (FFT over Finite Fields)
- [x] Grobner Bases
- [x] Polynomial System Solving via Grobner Basis Algorithms
- [x] Sparse Linear Algebra over Finite Fields
- [x] F4 Grobner Bases
- [x] Gebauer-Moller and chain criteria, structured elimination, adaptive linear algebra
- [x] FGLM monomial-order conversion and fallible zero-dimensional solving
- [x] Differential testing of the zero-dimensional pipeline against Singular
- [x] Batched border reduction and adaptive operator storage: 14x on katsura-7's conversion
- [x] 254- and 255-bit prime fields, with F4, FGLM and solving over them end to end

## Building and Testing
Zeebra builds on stable Rust; no nightly toolchain or feature gates are required.

```sh
cargo build
cargo test
```

Development checks, matching what CI enforces:

```sh
cargo fmt --all --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test --doc
```

The Rust examples in this file are **compiled and run** by `cargo test --doc`, through a
`cfg(doctest)` item in `src/lib.rs`, so they cannot drift from the API they document. Blocks that
are illustrative rather than executable are fenced `text`.

CI runs the tests under [cargo-nextest](https://nexte.st) rather than the built-in harness, which
gives a process per test instead of a thread per test: a test that aborts or segfaults is reported
as that one test failing instead of taking the whole binary's results down with it. `--profile ci`
comes from `.config/nextest.toml` and turns off fail-fast, so a run reports every failure rather
than stopping at the first. `cargo test` remains fine for local use; to match CI exactly:

```sh
cargo install cargo-nextest --locked
cargo nextest run --profile ci
```

Nextest cannot run doc examples — rustdoc owns that path — so `cargo test --doc` stays a separate
step in every job that wants them.

CI resolves its toolchain to `stable`, which moves. A clippy run that is clean on an older stable
is therefore **not** evidence that CI is clean — new lints arrive with new releases, and one did
during this project's history. `rustup update stable` before trusting a clean run, or name the
version explicitly:

```sh
rustup run stable cargo clippy --all-targets --all-features -- -D warnings
```

Some tests compare the optimized Gröbner engine against the naive reference implementation, or
factor large integers, on inputs slow enough to take minutes. They are `#[ignore]`d so the default
suite stays fast, and need release mode to finish in reasonable time:

```sh
cargo test --release -- --ignored test_optimized_agrees_with_reference_on_slow_systems
cargo test --release -- --ignored test_f4_on_larger_systems
cargo test --release -- --ignored test_factorization
```

One more is `#[ignore]`d because it needs a local Singular installation rather than because it is
slow. A test that silently passed when its oracle is absent would be worse than no test, so it is
opt-in:

```sh
cargo test --release --lib -- --ignored --exact \
    grobner::differential::tests::test_a_live_sweep_against_singular_agrees
```

One more needs data this repository does not redistribute. The Fukuoka MQ Challenge files are
"All Rights Reserved" with no stated licence, so the test against a genuine instance is opt-in for
the same reason:

```sh
tools/fetch-mq-challenge.sh
cargo test --release --lib -- --ignored --exact \
    grobner::research::mq::tests::test_a_published_instance_is_reproduced
```

Two other `#[ignore]`d tests are unimplemented placeholders — a `BigUInt` sampling distribution
check and a rare division branch — and they panic if run. A bare `cargo test -- --ignored`
therefore reports those two as failures; the commands above select the tests that are meant to
pass.

CI runs the suite twice: once in debug, and once in release in a separate job that also runs the
two Gröbner engine-agreement tests above. Both configurations are checked because a release build
takes different paths — `debug-assertions` and `overflow-checks` are off, so every
`debug_assert`-guarded invariant goes unchecked and integer arithmetic wraps instead of panicking.
Release is also the configuration every benchmark uses, so

```sh
cargo test --release
```

is worth running locally before claiming a measurement.

A third job runs the benchmarks, on pushes to main and on manual dispatch only. The benchmark
targets are declared `test = false`, which keeps them out of `cargo test`: a `[[bench]]` target
defaults to `test = true`, so a bare `cargo test` linked all eight criterion binaries under fat
LTO and executed all 455 cases. That took 168s of the 180s a warm `cargo test --release` spent,
against 2.4s for the 968 tests and 8.9s for the doc examples. Smoke-testing the benchmarks is
still worth doing — it catches one that panics rather than merely failing to compile — so it moved
to its own job rather than being dropped:

```sh
cargo bench -- --test
```

`cargo bench -- --test` and not `cargo test --benches`, which now selects nothing and would pass
vacuously. A benchmark that stops *compiling* still breaks the `cargo build --all-targets` step in
the pull-request jobs.

The release job builds under `[profile.ci-release]` rather than `release`. It inherits `release`,
so `debug-assertions` and `overflow-checks` are off and the job tests exactly what it did before,
but it drops the single codegen unit that makes a `release` build expensive — `Swatinem/rust-cache`
caches dependencies and never the crate under test, so `zeebra` is relinked from scratch on every
run, which was ~318s of a 321s step. Cargo.toml records the four configurations measured and why
this one was chosen; it is a compromise, because the codegen setting that makes the build cheap
also slows the two engine-agreement tests. Benchmarks are unaffected — `cargo bench` resolves
`[profile.bench]`, which still inherits `release`, so every reported number stays comparable.

The suite is not sharded across parallel jobs. Warm the 968 tests take under 3s and the two slow
`#[ignore]`d systems dominate everything else, with all but 0.3s of that being a single test that
no partitioning can divide; a shard would pay a checkout, a toolchain, a cache restore and a
release build to split seconds of test execution.

### Build configuration

`.cargo/config.toml` sets an instruction-set floor of `x86-64-v3` — the Haswell/Excavator feature
level, which brings AVX2, BMI2, FMA, LZCNT and MOVBE — for `x86_64` targets. `[profile.release]`
in `Cargo.toml` turns on fat link-time optimization and a single codegen unit.

Both exist for measurement. Field arithmetic is a handful of small generic functions called from
inner loops in other modules, so without cross-codegen-unit inlining the elimination kernels pay a
function call per field operation. A single codegen unit also makes benchmarks reproducible: with
the default of 16, moving code between modules repartitions the crate and can shift a measurement
for reasons unrelated to the change. The cost is build time.

`x86-64-v3` rather than `native`: `native` makes a build artifact depend on the machine that
produced it, so the same commit benchmarks differently on two machines. To measure with everything
the local CPU has:

```sh
RUSTFLAGS="-C target-cpu=native" cargo bench
```

Note that `RUSTFLAGS` **replaces** the flags in `.cargo/config.toml` rather than adding to them —
cargo takes the first source it finds and does not merge them. Repeat any flag that is still
wanted. This is also why the CI workflow states `-C target-cpu=x86-64-v3` in its `RUSTFLAGS`
alongside `-D warnings`: setting only the latter would silently drop the ISA floor and build CI at
the baseline x86-64 level.

**A consumer of this crate inherits none of this.** `.cargo/config.toml` applies only when cargo
is invoked with this directory as the working directory, and profile settings come from the
workspace being built. A downstream build gets whatever that build configures, so a dependent
crate wanting these settings must set them itself.

### Benchmarks

Criterion benchmarks cover field arithmetic, sparse polynomial operations, dense and sparse linear
algebra, and Gröbner basis computation:

```sh
cargo bench                              # everything
cargo bench --bench grobner              # one suite
cargo bench --bench sparse_linear_algebra
cargo bench --bench f4_stages
cargo bench --bench fglm                 # order conversion: stages, pipeline, strategies,
                                         # dependence, the shipped configuration, verification
cargo bench --bench polynomial_solving   # one solution against all of them, both routes
```

`sparse_linear_algebra` has two groups, and the difference between them matters. `sparse_linalg`
times sparse row echelon beside dense *reduced* row echelon, which performs a back-substitution
pass the sparse side never does; it is indicative of nothing about storage and is kept only for
continuity. `matched_echelon` runs the identical algorithm under each `linalg::echelon` backend on
identical matrices, and times densification and sparsification in their own benchmark, so the
comparison measures representation rather than algorithm or conversion.

`f4_stages` times F4's stages separately — symbolic preprocessing, matrix construction,
elimination under each backend, representation conversion, and a whole batch — replaying the
batches a real computation produced rather than synthetic ones. `grobner` says whether something
got faster; `f4_stages` says whether a change removed cost or moved it from one stage to another.

Wall-clock time alone does not say *why* a Gröbner computation got faster. For the algorithmic
counters — pairs considered, pairs eliminated by Buchberger's first criterion, reductions, zero
reductions, basis size:

```sh
cargo run --release --example grobner_statistics   # Buchberger
cargo run --release --example f4_statistics        # F4, beside Buchberger
cargo run --release --example f4_profile           # F4, cost attributed per stage
cargo run --release --example f4_profile -- list   # the configurations available
cargo run --release --example f4_blocks            # F4, row arrangements of the Macaulay matrix
cargo run --release --example f4_selection         # reducer selection and the reducer cache
cargo run --release --example elimination_density  # how dense an F4 matrix really is
cargo run --release --example pair_criteria        # what each pair criterion discards, F4
cargo run --release --example pair_criteria -- buchberger
cargo run --release --example f4_ablation          # every configuration, one table
cargo run --release --example f4_milestone         # both engines, at matched and default criteria
cargo run --release --example fglm_baseline        # which systems are zero-dimensional, and what
                                                   # a lex basis costs against a grevlex one
cargo run --release --example fglm_baseline -- cyclic-6   # one system per process
cargo run --release --example fglm_operators      # how sparse the multiplication operators are
cargo run --release --example fglm_conversion      # the FGLM pipeline against direct lex F4
cargo run --release --example fglm_profile         # where a conversion's time and memory go
cargo run --release --example fglm_profile -- katsura-7   # one system per process
cargo run --release --example fglm_border          # what deduplicating the border is worth
cargo run --release --example fglm_storage         # operator representations, stored and applied
cargo run --release --example fglm_shape           # shape position, and what that route would save
cargo run --release --example fglm_ablation        # every strategy combination, one table
cargo run --release --example fglm_ablation -- list
cargo run --release --example solve_one            # systems in, verified solutions out, both routes
cargo run --release --example solve_baseline       # both routes with resources and outcome class
cargo run --release --example solve_auto           # four policies against an offline best-of-two
cargo run --release --example specialize_slices    # seeded slices of an underdetermined system
cargo run --release --example mq_challenge         # import and solve a Fukuoka MQ instance
cargo run --release --example poseidon_cico        # reduced-round Poseidon CICO, end to end
timeout 900 cargo run --release --example buchberger_reach -- katsura-6 lex all
```

`solve_baseline` is M21-0's baseline: both routes on every corpus system, reporting what each
*cost* and which of the mathematically distinct outcomes it reached — a verified point, no
base-field point, an inconsistent ideal, a positive-dimensional ideal, or a crossed budget. It
takes about 30 seconds, nearly all of it katsura-7's direct-lex attempt failing. See
[`docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md`](docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md)
§4 for the table and what it decided.

`f4_statistics` prints matrix dimensions, how many reductions each matrix absorbed, how much of
each matrix was reduction scaffolding, and how much elimination filled it in. It asserts that the
two engines agree wherever both can run. It pins itself to `F4Options::baseline()`, because its
columns are the ones `docs/MILESTONE-F4.md` §7.1 records and comparing against them needs that
configuration.

`f4_profile` prints where the time went: symbolic preprocessing, construction, elimination,
candidate extraction, and the final interreduction, with the remainder shown as `other` so an
unattributed cost cannot hide. It takes the name of a configuration — `baseline` by default,
`recommended` for what `F4Options::default()` is — so the effect of one optimization can be read
off against another's. The timing comes from
`F4Options::measure_stages`, which reads a clock four times per batch and is off by default.

`f4_blocks` replays the batches a computation really built and eliminates each one four ways —
rows as preprocessing produced them, reducer rows first, reducer rows taken as established pivots,
and the same with the reducer block interreduced — reporting row operations, peak live nonzeros,
final nonzeros, and time on the identical matrices. Holding the matrix fixed is the point: a
change of row arrangement changes which candidates come out, hence every later batch, so the
whole-computation effect and the per-elimination effect are different measurements.

`elimination_density` reports the density a representation policy would have to read: the
distribution of row densities as built and at each row's own peak during its reduction, the density
of the densest 64x64 blocks, and the three backends' elimination times with representation
conversion in its own column. A global density of a fraction of a percent says nothing about
either. `-- list` names the instances; the largest are excluded by default, because a dense
representation of katsura-7 grevlex is 374 MB for a matrix holding 112k entries.

`f4_selection` compares the two reducer-selection policies and the three cache modes against one
common baseline, on one line each: the closure size, the largest matrix, the peak live entries, the
row operations, the share of reducer multiples that had been needed before, and the stage times.
`f4_profile`'s configurations bundle several options together, so neither effect can be attributed
from it alone.

`f4_ablation` runs twelve configurations over the corpus and asserts every one returns the
baseline's basis, which is what establishes that the optimizations compose rather than conflict.
`f4_milestone` is the headline comparison: both engines on identical inputs in one process, with
the bases asserted equal wherever both can run. It reports **two** ratios, because the pair
criteria are shared machinery and the two functions' defaults do not match — see "Choosing a
strategy" below. `buchberger_reach` runs the classical engine on one hard instance per invocation
so an external timeout can bound it, which is how a dash in that table is shown to mean "does not
finish" rather than "was not tried".

`fglm_baseline` classifies each benchmark system as unit, zero-dimensional, or
positive-dimensional from the leading monomials of its grevlex basis, reports the dimension `D` of
`R/I` as a vector space, and times a lex basis against a grevlex one under both engines. It is the
baseline for the order-conversion work; **cyclic-4 is positive-dimensional**, so FGLM does not
apply to it, and that is measured rather than assumed.

`fglm_profile` attributes a conversion's cost. One table is the shape of the border — how many of
the `N * D` operator columns leave the standard monomials, and how many *distinct* monomials those
are, whose gap bounds what deduplicating them could remove. The other is the stage breakdown
(standard-monomial enumeration, border classification, scalar normal forms, a batch's symbolic
closure, coordinate assembly, the lex walk) beside what the representations hold. Scalar reduction
and batched reduction are the same stage under two strategies, so one column is zero whenever the
other is not and the reported share is of their sum. It profiles the shipped strategies, or M17's
with `-- baseline`. It sets `FglmOptions::measure_stages`, which is off by
default because the operator loop runs `N * D` times and a clock read inside it is not free. The
byte figures are estimates of this crate's own representations;
`zeebra::util::peak_resident_bytes` is the separate, process-wide measurement, and the two are not
interchangeable.

`fglm_border` prices the three `OperatorConstruction` strategies against each other on the same
prepared source basis, having first asserted that they build identical operators, and varies the
batch size — which is the trade that decides the recommended default rather than being left to a
guess. It also answers,
with its own measurement rather than by inference, whether the one-term polynomial built per border
reduction is worth avoiding: 0.07% to 0.38% of the reduction it precedes on the families where
reduction dominates, so no. `cargo bench --bench fglm -- fglm_operator_construction` is the same
comparison under Criterion.

`fglm_shape` is M18-4's research spike, measured. `grobner::fglm::shape` detects **shape
position** — whether a single variable's powers `1, t, ..., t^{D-1}` are a basis of `R/I` — and
where the last variable qualifies it produces the lex basis `p(t), x_0 - h_0(t), ...` from that
variable's Krylov sequence, with no monomial walk and without retaining the accepted quotient
vectors. The whole katsura family qualifies and nothing else in the corpus does; 76 of 120
zero-dimensional differential fixtures do, and the route is checked against Singular on every one.

Detection is **algebraic, not a count of solutions**: `<x - 1, (y - 1)^2>` has one point, dimension
two, and is in shape position, while `<x^2, y^2>` has one point, dimension four, and is not. The
output is verified before it is returned — every polynomial's class in `R/I` must be zero, which
with the leading monomials proves it is the reduced lex basis — so nothing probabilistic is
exposed. It is public and tested but not a `FglmOptions` strategy; `docs/MILESTONE-FGLM-SCALABILITY.md`
§8.5 is the **no-go** on a full sparse-FGLM milestone and the measurements behind it.

`fglm_storage` reports the operator representations three ways: bytes under each strategy, which are
exact; operator *application*, on a unit input and a dense one, because the sparse path skips a zero
input coordinate and the dense path does not; and the whole conversion, where the difference turns
out to be under 1%. `cargo bench --bench fglm -- fglm_operator_application` is the application half
under Criterion.

`fglm_ablation` runs every construction × storage combination on one source basis per system, with
the lex basis and the operators' nonzero count asserted equal to the baseline's on every row, and
reports time and memory side by side. **It is where the defaults came from.** The shipped
configuration is at least as fast as M17's on every system in the corpus — 14.0x on katsura-7, 1.17x
on planted-10 — and never stores more. Two changes cannot be ablated and the example says so: the
compact sparse column and the span's two triangular blocks are not strategies, so they are in every
row including the baseline. `cargo bench --bench fglm -- fglm_recommended` is the same comparison
under Criterion, and `fglm_profile` shows what that left behind: border reduction was 95% of
katsura-7's conversion and is 52%, while planted-10's lex walk is the majority of its own —
M18 did not touch it, and two follow-ups did. Offsetting the span's rows by their pivots took that
walk from 24.3 ms to 12.5 ms and the conversion's dense blocks from 20,484 kB to 16,392 kB, and
reducing into registers the span owns, rather than allocating a residue per candidate, took a
further 1.14x.

Recorded baselines, before/after measurements, and the reasoning behind each optimization are in
[`docs/MILESTONE-ALGEBRA-FOUNDATION.md`](docs/MILESTONE-ALGEBRA-FOUNDATION.md),
[`docs/MILESTONE-F4.md`](docs/MILESTONE-F4.md),
[`docs/MILESTONE-F4-OPTIMIZATION.md`](docs/MILESTONE-F4-OPTIMIZATION.md),
[`docs/MILESTONE-FGLM-SOLVING.md`](docs/MILESTONE-FGLM-SOLVING.md),
[`docs/MILESTONE-FGLM-SCALABILITY.md`](docs/MILESTONE-FGLM-SCALABILITY.md),
[`docs/MILESTONE-SIMD-PARALLELISM.md`](docs/MILESTONE-SIMD-PARALLELISM.md),
[`docs/MILESTONE-LARGE-PRIME-FIELDS.md`](docs/MILESTONE-LARGE-PRIME-FIELDS.md), and
[`docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md`](docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md).

## Finite Fields

`PrimeFieldElement64<P>` holds elements in **Montgomery form** when `P` is odd, storing
`a * 2^64 mod P` rather than `a`. This is an internal representation and is not observable through
the public API: `value()`, `Display`, and the serialized form all give the canonical residue in
`[0, P)`, and the serialized bytes are unchanged by it.

The reason is that multiplication used to compute `(a as u128 * b as u128) % P as u128`. A
const-generic modulus does not save that — LLVM does not strength-reduce a 128-bit remainder, so
every field multiplication compiled to a call to `__umodti3`, compiler-rt's *software* 128-bit
division. Montgomery reduction replaces the division with two multiplications and a shift.

Two consequences worth knowing:

- `value()` is a Montgomery reduction, not a field read. A hot loop should hold field elements and
  convert at the boundary rather than call `value()` per iteration.
- `P = 2` is supported and keeps the wide-remainder path, because `2^64` is not invertible modulo
  an even number. The branch is on a const generic, so it is resolved at compile time.

`PrimeFieldElement128<P>` still reduces a 256-bit product by allocating software long division. It
is not yet converted, and is measurably the slowest field in the crate as a result — slower than
one four times as wide. `cargo bench --bench field_arithmetic`, per operation:

| field | width | mul | add | sub | inverse |
|---|---:|---:|---:|---:|---:|
| `Zp2147483647` | 31 | 1.76 ns | 1.10 ns | 0.95 ns | 246 ns |
| `Zp18446744073709551557` | 64 | 1.71 ns | 1.05 ns | 0.97 ns | 509 ns |
| `PrimeFieldElement128` | 68 | **130.6 ns** | 2.10 ns | 1.90 ns | **17.84 µs** |
| `Bn254Fr` | 254 | 18.71 ns | 3.69 ns | 3.41 ns | 3.77 µs |
| `Bls12_381Fr` | 255 | 19.34 ns | 3.52 ns | 3.27 ns | 3.97 µs |

Read the last three rows together: a 254-bit multiply is **7.0x faster** than the 68-bit one, and
10.9x slower than the 64-bit one. A claim about what field width costs has to say which baseline
it means. Inversion over a wide field is 202 multiplies, so pivot normalization should multiply by
a precomputed inverse rather than divide per entry.

Two other field types gained the same treatment, each measured on the operation rather than on a
whole computation, because both modules are private and no bench target can reach them:

- `BinaryFieldElement<P>` multiplies with `PCLMULQDQ` and reduces by Barrett rather than by a
  bit-at-a-time loop and long division — **212.70 to 2.02 ns** per multiply over GF(2^63). The
  instruction is probed at run time, since it is not implied by the `x86-64-v3` floor, and the
  scalar fallback is kept and tested.
- `ExtensionFieldElement<P, N, M>` reduces once per output coefficient instead of once per partial
  product, O(N) instead of O(N^2), under a compile-time overflow bound; the per-multiplication heap
  allocation is gone.

### 254- and 255-bit prime fields

`PrimeFieldElement256<M>` is the scalar field of a pairing-friendly curve, held in Montgomery form
over four 64-bit limbs — CIOS multiplication, binary extended Euclid inversion, and `R mod p` /
`R^2 mod p` as compile-time constants. Two fields are provided:

```rust
use zeebra::{fields::{Bls12_381Fr, Bn254Fr}, FiniteField, KnownOrder, One};

let a = <Bn254Fr as FiniteField>::from_str("123456789012345678901234567890").unwrap();
assert_eq!(a * a.inverse(), Bn254Fr::one());

// The order does not fit in a machine integer, which is why `KnownOrder` reports limbs.
assert_eq!(Bn254Fr::order_u128(), None);
assert_eq!(Bn254Fr::order_limbs().len(), 4);
assert_eq!(Bls12_381Fr::order_limbs().len(), 4);
```

The modulus arrives through the `PrimeModulus256` trait rather than a const generic, because a
const generic parameter cannot be 256 bits wide — the same device `IrreduciblePolynomial` already
uses for extension fields. A new field is its modulus limbs and nothing else:

```rust
use zeebra::fields::{PrimeFieldElement256, PrimeModulus256};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
struct MyModulus;

impl PrimeModulus256 for MyModulus {
    // Must be an odd prime: R = 2^256 is not invertible modulo an even number.
    const MODULUS: [u64; 4] = [0xffffffff00000001, 0x53bda402fffe5bfe,
                               0x3339d80809a1d805, 0x73eda753299d7d48];
}

type MyField = PrimeFieldElement256<MyModulus>;
```

Any odd prime up to 256 bits works, not only one that fills all four limbs. A narrower modulus
leaves its high limbs zero, and the bit width that `new` and `random` depend on is derived from the
highest occupied limb rather than assumed — the tests cover moduli at one, two, three and four
limbs, with GF(7) checked exhaustively against `PrimeFieldElement64<7>`. Below 2^128 the order
fits a machine integer again, so `KnownOrder::order_u128` starts returning `Some`.

`BN254_FR_MODULUS_DECIMAL` and `BLS12_381_FR_MODULUS_DECIMAL` are public so the compiled-in limbs
can be checked against the published values, which the module's own tests do.

What the representation means for a caller:

- `canonical_limbs()`, `to_bytes_le()` and `Display` are Montgomery reductions, not field reads.
  Hold field elements in a hot loop and convert at the boundary.
- Serialization and `to_bytes_le` emit the **canonical residue**, never the stored Montgomery
  value, so an encoding does not depend on an internal representation choice.
- `from_canonical_limbs` and `try_from_bytes_le` **reject** an input at or above the modulus, as
  does deserialization. `from_limbs_reduced` is the separately named constructor that reduces.
- `random` is masked rejection sampling. Reducing a uniform 256-bit draw modulo a 254-bit prime
  would favour the low residues.
- `primitive_element` and `root_of_unity` are `unimplemented!()`. Finding a generator of the
  multiplicative group means factoring a 254-bit `q - 1`, which no algorithm here needs and which
  should not start by accident.

The whole stack works over these fields, not just the arithmetic:
`grobner::mod`'s `test_the_whole_pipeline_over_bn254_fr` and its BLS12-381 twin take a planted
zero-dimensional system through F4, check the basis against Buchberger's criterion, convert to lex
with FGLM, compare that against a direct lex F4, and then recover a solution with `solve_one` and
re-evaluate it against the original system.

Root finding over a wide field works because `pow_mod_limbs` takes its exponent as little-endian
limbs rather than a `u128`; `roots` passes `F::order_limbs()` straight through. `pow_mod` is now a
thin wrapper over it and is unchanged for callers.

The arithmetic is checked against `ark-ff` as a **dev-dependency oracle**, in the role Singular
already plays for Gröbner bases: 20,000 random cases per field on add, sub, mul, square, negate,
invert and divide, plus the edge residues. Nothing third-party is in the shipped crate.

### `FiniteField` and `KnownOrder`

A coefficient type implements `FiniteField`: arithmetic, inversion, parsing, uniform sampling,
`new`, and exponentiation by a `u128`. The field's *order* is not there. It lives in a separate
trait:

```rust
use zeebra::{fields::Zp2147483647, KnownOrder};

assert_eq!(Zp2147483647::order_limbs(), &[2147483647]);
assert_eq!(Zp2147483647::order_u128(), Some(2147483647));
```

`KnownOrder` gives the order q and the characteristic p as little-endian 64-bit limbs — a width
that covers 64-, 128- and 256-bit orders without allocating — plus `order_u128` and
`characteristic_u128` for callers that need a machine integer and can fail without one, and
`primitive_element` and `root_of_unity`. For an extension field q = p^k, so the order and the
characteristic are genuinely different; both are reported.

The split is there because a 254-bit prime field has no order that fits in a machine integer, and
because **nothing in the algebraic core asks for one**: the multivariate polynomials, the linear
algebra, F4, FGLM and Buchberger are all generic over `FiniteField` alone. Only root finding,
factorization and enumerating the field itself need `KnownOrder`, and they say so in their bounds.
`grobner::mod`'s `test_the_grobner_stack_needs_no_field_cardinality` fails to compile if that
stops being true.

Every field type in the crate implements both traits. Two consequences for anything generic over
`F: FiniteField`:

- `F::order()` and `F::characteristic()` are gone. Add `F: KnownOrder` and call `order_limbs()`,
  or `order_u128()` where the old `u128` is what you want.
- `inverse()` is a required method rather than a provided one. Its only sensible default was
  `a^(q-2)`, which needs the order; a field whose order does not fit in a `u128` cannot have it.

`docs/MILESTONE-LARGE-PRIME-FIELDS.md` records the audit this came out of.

## Gröbner Bases

`grobner::buchberger` computes a reduced Gröbner basis under a chosen monomial order. All three
standard orders are available, and `MonomialOrder` is exported from the crate root:

```rust
use zeebra::{fields::Zp13, grobner::buchberger, MonomialOrder, MultivariatePolynomial};

let vars = ["x", "y", "z"];
let system = vec![
    MultivariatePolynomial::<3, Zp13>::parse("x*z - y^2", vars).unwrap(),
    MultivariatePolynomial::<3, Zp13>::parse("x^3 - z^2", vars).unwrap(),
];

let basis = buchberger(&system, MonomialOrder::GradedReverseLexicographic);
```

The returned basis is reduced and in a deterministic order, so it is reproducible across runs.
Which order you pick matters: graded reverse lexicographic is usually cheapest, while lexicographic
is what makes a system easy to solve by back-substitution and can be dramatically more expensive.

`buchberger_with_statistics` returns the same basis alongside counters describing the computation,
which is useful for understanding cost on a hard system. `buchberger_with_criteria` additionally
takes a `PairCriteria`, so the classical engine can be run under the same pair-elimination
criteria as F4 — and compared against `PairCriteria::NONE`, which reduces every pair. `grobner::benchmark_systems` provides the
standard `cyclic` and `katsura` families plus `planted`, which builds a zero-dimensional system
around a solution you choose. `grobner::reference` holds a deliberately naive textbook
implementation kept as a correctness oracle — use `buchberger` or `f4` for real work.

### Zero-dimensional ideals

A Gröbner basis says whether the quotient `R/I` is finite-dimensional, and if it is, what its
monomial basis is. `grobner::classify_ideal` separates the unit ideal, a proper zero-dimensional
ideal, and a positive-dimensional one; `grobner::QuotientBasis` enumerates the standard monomials —
those divisible by no leading monomial — whose count is the quotient dimension `D`:

```rust
use zeebra::fields::Zp2147483647;
use zeebra::grobner::{classify_ideal, f4, IdealClass, QuotientBasis};
use zeebra::{MonomialOrder, MultivariatePolynomial};

type F = Zp2147483647;
let order = MonomialOrder::GradedReverseLexicographic;

// <x^2, y^2>: one point over the algebraic closure, but a quotient of dimension four.
let system: Vec<MultivariatePolynomial<2, F>> = ["x^2", "y^2"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
    .collect();
let basis = f4(&system, order).unwrap();

assert_eq!(classify_ideal(&basis, order), IdealClass::ZeroDimensional);
let quotient = QuotientBasis::new(&basis, order, 1 << 20).unwrap();
assert_eq!(quotient.dimension(), 4);      // 1, x, y, xy
```

`D` is the dimension of `R/I` as a vector space, **not** the Krull dimension: it counts the zeros
over the algebraic closure with multiplicity, so it is an upper bound on the number of distinct
points rather than a count of them. `<x^2, y^2>` above has one distinct zero and `D = 4`. A
positive-dimensional ideal is rejected with `FglmError::PositiveDimensional` before any
enumeration, since the enumeration would not terminate, and the `max_dimension` argument bounds it
otherwise.

`grobner::QuotientAlgebra` adds the arithmetic: coordinate vectors over those monomials, and the
`N` linear operators that multiply by a variable.

```rust
use zeebra::fields::Zp2147483647;
use zeebra::grobner::{f4, FglmOptions, QuotientAlgebra};
use zeebra::{MonomialOrder, MultivariatePolynomial, Zero};

type F = Zp2147483647;
let order = MonomialOrder::GradedReverseLexicographic;

let system: Vec<MultivariatePolynomial<2, F>> = ["x^2", "y^2"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
    .collect();
let basis = f4(&system, order).unwrap();
let algebra = QuotientAlgebra::new(&basis, order, &FglmOptions::default()).unwrap();

// Multiplication by x is nilpotent here: x is nonzero in R/I but x^2 is not.
let x = algebra.multiply_by_variable(0, &algebra.one());
let x_squared = algebra.multiply_by_variable(0, &x);
assert!(x.iter().any(|c| !c.is_zero()));
assert!(x_squared.iter().all(|c| c.is_zero()));
```

That nilpotence is the point of keeping multiplicities: `<x^2, y^2>` has a single geometric zero,
and an operator with no eigenbasis. `cargo run --release --example fglm_operators` reports how much
storage the operators need — 0.34% of a dense matrix on planted-8, but 57% on the katsura family,
where the sparse representation does not pay for itself.

### Monomial-order conversion (FGLM)

`grobner::fglm_to_lex` converts a zero-dimensional Gröbner basis under any order into the
lexicographic basis, by linear algebra over `R/I` rather than by another Gröbner computation. The
point is that grevlex is usually much cheaper to compute than lex:

```rust
use zeebra::fields::Zp2147483647;
use zeebra::grobner::{f4, fglm_to_lex};
use zeebra::{MonomialOrder, MultivariatePolynomial};

type F = Zp2147483647;
let system: Vec<MultivariatePolynomial<2, F>> = ["x^2 - y", "y^3 - 1"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
    .collect();

let grevlex = f4(&system, MonomialOrder::GradedReverseLexicographic).unwrap();
let lex = fglm_to_lex(&grevlex, MonomialOrder::GradedReverseLexicographic).unwrap();

// A reduced Gröbner basis is unique for an ideal and an order, so this is an equality of values.
assert_eq!(lex, f4(&system, MonomialOrder::Lexicographic).unwrap());
```

The conversion is checked against **29 lexicographic bases computed by Singular**, committed as
literals and regenerable with `Singular -q tools/reference_bases.sing`. Singular's `std` is
Buchberger/slimgb lineage, so those references are independent of Zeebra's F4 in algorithm and not
only in implementation. No external system is needed to run the tests. A further **240 recorded
cases** check every intermediate result rather than only the final basis — see "Differential
testing against Singular" below.

**`fglm_to_lex` trusts its input to be a Gröbner basis under the stated order, and returns a wrong
basis rather than an error if it is not.** Use `fglm_to_lex_checked` for input of unknown
provenance; it verifies Buchberger's criterion first, which costs 0.6x to 27x what computing the
basis cost, and that is why it is not the default. `grobner::is_grobner_basis` is the check on its
own.

#### Building the multiplication operators

Column `j` of the operator `T_i` is the normal form of `x_i b_j`, and almost all of a conversion is
computing those: **95% of katsura-7's**, measured. But the products `x_i b_j` that leave the
standard monomials are not distinct — `x*y` is reached from both `x * y` and `y * x` — and between a
fifth and a third of them repeat a monomial some other column already reduced.
`FglmOptions::operator_construction` chooses whether to notice:

```rust
use zeebra::grobner::fglm::{FglmOptions, OperatorConstruction};

// One normal form per nonstandard column: M17's strategy, kept as the reference.
let per_column = FglmOptions::baseline();

// One normal form per *distinct* border monomial, reused by every column that reaches it.
let deduplicated = FglmOptions::default()
    .with_operator_construction(OperatorConstruction::DeduplicatedBorder);
```

A third strategy shares more than the reductions:

```rust
use zeebra::grobner::fglm::{FglmOptions, OperatorConstruction};

// Border monomials reduced in batches against a shared symbolic closure, with the arithmetic over
// integer column indices rather than through a polynomial's hash map. The default since M18-5.
let batched = FglmOptions::default();
assert_eq!(batched.operator_construction, OperatorConstruction::BatchedBorder);
```

All three build **identical operators**, which the tests assert by comparing whole
`QuotientAlgebra` values rather than the lex bases they lead to. Measured on the whole conversion:

| system | `D` | per-column | deduplicated | batched |
|---|---:|---:|---:|---:|
| katsura-6 | 32 | 3.56 ms | 2.70 ms | **0.52 ms** |
| katsura-7 | 64 | 42.92 ms | 31.58 ms | **2.69 ms** |
| cyclic-6 | 156 | 29.77 ms | 19.60 ms | **2.82 ms** |
| planted-8 | 256 | 3.40 ms | 3.28 ms | 2.86 ms |
| planted-10 | 1,024 | 42.71 ms | 40.47 ms | 36.33 ms |

**Katsura-7's operator construction goes from 34.4 ms to 1.69 ms** under Criterion, a 20x change in
the stage that was 96% of the conversion — and nothing in the corpus is slower.

The batch *size* is what makes that last clause true. A bigger batch shares more closure and wins on
katsura and cyclic; on the planted family a reduction is one step, so the closure is nearly all the
work and a bigger batch is pure overhead — one unbounded batch is 1.3x **slower** than the scalar
path on planted-10. `BorderBatch::recommended()` uses 64 targets, which is within 13% of the best
size on both families and faster than scalar on every system.

`BatchOverflow` decides what happens when a batch's closure crosses a limit, and neither option
drops a target: `Fail` returns `FglmError::BorderBatchExceeded` naming the limit, and `Scalar`
reduces that batch one target at a time and counts that it did.

**`BatchedBorder` at a batch of 64 is the default**, chosen from the integration ablation in
`docs/MILESTONE-FGLM-SCALABILITY.md` §9 rather than from katsura-7 alone: it is the one strategy
that is at least as fast as M17's on every system in the corpus. `FglmOptions::baseline()` names
the M17 configuration, so a measurement still has something fixed to be quoted against.

#### Storing the multiplication operators

A column that leaves the staircase is not necessarily sparse. Measured, a reduced column holds **79%
of `D` on katsura-7 and 0.14% on planted-10** — and a sparse entry carries an index as well as a
coefficient, so it costs twice a dense cell and only saves below half fill.
`FglmOptions::operator_storage` chooses, **per column**:

```rust
use zeebra::grobner::fglm::{FglmOptions, OperatorStorage};

// `(index, coefficient)` pairs for every reduced column: M17's representation, the reference.
let sparse = FglmOptions::baseline();

// Whichever of the two allocates fewer bytes, decided column by column. The default since M18-5.
let adaptive = FglmOptions::default();
assert_eq!(adaptive.operator_storage, OperatorStorage::Adaptive);
```

On katsura-7 the operators go from 264.5 kB to **163.6 kB**, and `Adaptive` beats *both* extremes
there — 163.6 against sparse's 264.5 and an all-dense 172.0 — which only a per-column choice can do.
On the planted family it declines every column and is sparse exactly. All-dense is kept as a
strategy to show that it is ruinous rather than to be used: planted-10 would need 51 MB where it
needs 380 kB.

`max_operator_bytes` is a second budget beside `max_operator_entries`, not a redefinition of it:
entries are mathematical nonzeros and bytes are allocations, and the two diverge once a column is
held densely.

### Differential testing against Singular

`zeebra-differential` generates deterministic polynomial systems, asks a local Singular about each
one, and compares **every intermediate result** — not only the lex basis:

```sh
cargo run --release --bin zeebra-differential -- --help
cargo run --release --bin zeebra-differential -- --systems 500
cargo run --release --bin zeebra-differential -- --seed 777 --systems 240 \
    --max-degree 4 --max-terms 5 \
    --fixtures src/grobner/differential/fixtures.rs   # regenerate the committed cases
```

The comparison runs outwards from the source basis and stops at the first disagreement, so what it
reports is the earliest thing that differs rather than everything downstream of it:

| check | Zeebra | Singular |
|---|---|---|
| source basis | `f4` under grevlex | `std` in a `dp` ring |
| quotient dimension | `QuotientBasis` | `vdim` |
| standard monomials | `QuotientBasis::monomials` | `kbase` |
| border normal forms | `normal_form` of each `u` in `∂B` | `reduce(u, G)` |
| operator columns | each column of each `T_i` | the normal form of the monomial it stands for |
| lex basis | `fglm_to_lex` | `std` in an `lp` ring, cross-checked against Singular's own `fglm` |

**Multiplication-operator columns are compared individually.** Each has a precise mathematical
answer, so a wrong column is caught directly rather than only when it happens to change the lex
basis. On two 1,000-system sweeps under the shipped defaults, over GF(2), GF(3), GF(7), GF(13),
GF(65537) and GF(2^31 - 1) in two to five variables, every system agreed: 949 zero-dimensional, 572
unit ideals, and 479 positive-dimensional ideals that both sides rejected, with no oracle
failures.

**An oracle that did not answer is never agreement.** Singular exits 0 after a script error, so a
successful exit proves nothing: every run must reach an end-of-script marker *and* have printed no
error line, and a timeout, a missing binary, a characteristic above Singular's `2^31` limit, or an
answer Singular's own `fglm` contradicts each make the sweep exit non-zero.

A failing case is written out as a fixture literal, shrunk first — generators dropped, terms
dropped, coefficients flattened, exponents lowered — while it keeps failing *the same* check. The
original system and its seed are kept beside the shrunk one, since a shrunk system is no longer
what the seed generates.

**CI needs no Singular.** A sweep's agreeing cases are emitted as Rust literals into
`src/grobner/differential/fixtures.rs`, and an ordinary test replays the same comparison against
them — a table of constants where the subprocess was. A separate test corrupts a fixture six ways
and requires each to be detected, so a passing table is evidence rather than an absence of
checking. The live sweep is also available as an `#[ignore]`d test:

```sh
cargo test --release --lib -- --ignored --exact \
    grobner::differential::tests::test_a_live_sweep_against_singular_agrees
```

One more needs data this repository does not redistribute. The Fukuoka MQ Challenge files are
"All Rights Reserved" with no stated licence, so the test against a genuine instance is opt-in for
the same reason:

```sh
tools/fetch-mq-challenge.sh
cargo test --release --lib -- --ignored --exact \
    grobner::research::mq::tests::test_a_published_instance_is_reproduced
```

### Solving zero-dimensional systems

`grobner::solve_one` finds one solution and stops; `grobner::solve_zero_dimensional` finds every
distinct one. Both refuse a system that is not zero-dimensional rather than enumerating the field,
and both report every failure as a `Result`:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::fields::Zp2147483647;
use zeebra::grobner::{solve_one, SolveError};
use zeebra::{MultivariatePolynomial, Zero};

type F = Zp2147483647;
let mut rng = StdRng::seed_from_u64(1);

// Two equations, two unknowns, finitely many solutions.
let system: Vec<MultivariatePolynomial<2, F>> = ["x^2 - 4", "y - x"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
    .collect();
let point = solve_one(&system, &mut rng).unwrap().expect("a solution exists");
assert!(system.iter().all(|p| p.eval(&point).is_zero()));

// A curve has infinitely many solutions, so it is refused rather than enumerated.
let curve: Vec<MultivariatePolynomial<2, F>> =
    vec![MultivariatePolynomial::parse("x*y - 1", ["x", "y"]).unwrap()];
assert_eq!(solve_one(&curve, &mut rng), Err(SolveError::PositiveDimensional));
```

`Ok(None)` means the system is zero-dimensional and has **no solution over the base field** — which
is an answer, not a failure. `x^2 + 1` over GF(3) has quotient dimension two and no point in GF(3).
Only `Err` means the computation could not be completed, and `SolveOptions` bounds it: search
branches, returned solutions, and the F4 and FGLM limits underneath. An exceeded budget is an error
rather than a truncated list.

#### Which answer, and what it cost

`Ok(None)` collapses two different answers: the equations may contradict each other, or they may
simply have no base-field solution while the variety is nonempty over an extension.
`solve_one_with_outcome` separates them and returns the diagnostics alongside:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{fields::Zp2147483647, grobner::{solve_one_with_outcome, SolveOptions, SolveOutcome},
             MultivariatePolynomial};

type F = Zp2147483647;
let parse = |s| MultivariatePolynomial::<2, F>::parse(s, ["x", "y"]).unwrap();
let options = SolveOptions::default();

// 1 is in the ideal: the equations contradict each other.
let contradiction = vec![parse("x - 1"), parse("x - 2")];
let (outcome, _) =
    solve_one_with_outcome(&contradiction, &mut StdRng::seed_from_u64(1), &options).unwrap();
assert_eq!(outcome, SolveOutcome::Inconsistent);

// 2^31 - 1 is 3 mod 4, so -1 is not a square: zero-dimensional, and no point in the field.
let no_point = vec![parse("x^2 + 1"), parse("y")];
let (outcome, statistics) =
    solve_one_with_outcome(&no_point, &mut StdRng::seed_from_u64(1), &options).unwrap();
assert_eq!(outcome, SolveOutcome::NoBaseFieldPoint);

// And what the route cost, which `solve_one` discards.
assert!(statistics.f4.is_some());
```

Every `SolveOutcome` variant is an answer; a crossed budget is still an `Err` and can never appear
as one. `SolveStatistics` carries the Gröbner stage's `F4Statistics` and, on the converting route,
the `FglmStatistics`, with `estimated_peak_bytes` the larger of the two stage estimates. That
figure is an estimate of the *representation* — on katsura-7 under lex it is 320 MB against a
measured 1,303 MB of process RSS, so use `util::peak_resident_bytes` when the question is about the
process.

#### Structural analysis, which decides nothing

`grobner::analyze` reads a system's shape off its terms without computing anything:

```rust
use zeebra::{fields::Zp2147483647, grobner::analyze, MultivariatePolynomial};

type F = Zp2147483647;
let system: Vec<MultivariatePolynomial<3, F>> = ["x*y - 1", "x^2 - z"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, ["x", "y", "z"]).unwrap())
    .collect();

let shape = analyze(&system);
assert_eq!(shape.quadratic_generators, 2);
assert_eq!(shape.occurrences, vec![2, 1, 1]);      // per variable, generators it appears in
assert!(!shape.constant_contradiction);
// Least-constrained variable first. A ranking, not a recommendation.
assert_eq!(shape.specialization_candidates(), vec![1, 2, 0]);
```

`constant_contradiction` is the only sound conclusion in `SystemShape` — a nonzero constant
generator puts 1 in the ideal by itself. **Nothing else there bounds the quotient dimension or the
solving degree.** In particular `generators == variables` proves nothing: cyclic-4 is four
equations in four variables and positive-dimensional, katsura-4 is four in four and
zero-dimensional, and the two agree on every column `analyze` reports.

#### Letting the solver choose

`solve_one_planned` picks a route on stated grounds and, if permitted, tries the other one — with
a decision log beside the answer. It is opt-in: the explicit entry points above are untouched.

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{fields::Zp2147483647, grobner::{benchmark_systems::katsura, solve_one_planned,
             PlannedSolveOptions, SolveOutcome, SolvePolicy}};

let options = PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback);
let (outcome, plan) = solve_one_planned(
    &katsura::<7, Zp2147483647>(),
    &mut StdRng::seed_from_u64(1),
    &options,
);

assert!(matches!(outcome, Ok(SolveOutcome::Point(_))));
assert_eq!(plan.attempts.len(), 1);              // the opening route worked
println!("{}", plan);                            // every decision, with its reason and its cost
```

**The conservative opening is grevlex-then-FGLM**, which contradicts `DirectLexF4` being the
`#[default]` strategy described as "the conservative choice". The argument is not that conversion
usually wins — it loses on the whole planted family — but that **its refusals are cheap by
construction**: FGLM's binding budget is the span's `D² + D(D+1)` cells, computed from `D` and
checked before anything is allocated, while F4's is discovered during elimination and so costs the
whole elimination up to the crossing. Measured: katsura-7's direct attempt burns 28.3 s and 1.3 GB
before refusing; planted-12's conversion refuses after 36 ms. The conservative question is not
which route usually wins but **which route's failure is affordable**.

The one decision made on a measured quantity is the conversion's feasibility: after a source basis
exists, `D` is *counted* and the span requirement is a function of `D` alone, so
`SolveError::ConversionInfeasible` means the conversion was never started — distinct from
`Fglm(SpanStorageExceeded)`, which means it ran and crossed the limit.

`PlanBudget` is shared across attempts, and holds only quantities that are *spent* —
`max_elapsed` and `max_total_batches`. A peak is not consumed by an attempt, so the entry and byte
budgets stay per-attempt in `SolveOptions`. `SolvePlan` keeps the same split: `total_batches()`
sums, `peak_estimated_bytes()` maxes. `max_elapsed` is checked *between* attempts, since F4 has no
cooperative time check, so it bounds whether a second route starts rather than how long the first
runs.

An `Err` from the planner means **inconclusive**, never "no solution".
`cargo run --release --example solve_auto` compares all four policies against an offline
best-of-two the planner was not allowed to see.

#### Underdetermined systems, and what a slice establishes

The zero-dimensional solvers refuse a positive-dimensional system, which is the right answer — but
the interesting cryptanalytic systems are underdetermined, so `grobner::research` fixes some
variables and solves the slice:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{fields::Zp2147483647, grobner::{research::{solve_slice, Specialization},
             PlannedSolveOptions}, FiniteField, MultivariatePolynomial};

type F = Zp2147483647;
// A curve: one equation, two unknowns, so positive-dimensional.
let curve: Vec<MultivariatePolynomial<2, F>> =
    vec![MultivariatePolynomial::parse("x*y - 6", ["x", "y"]).unwrap()];

let slice = Specialization::new(&[(0, F::new(2))]).unwrap();
let (outcome, _plan) = solve_slice(
    &curve, &slice, &PlannedSolveOptions::default(), &mut StdRng::seed_from_u64(1),
);
assert_eq!(outcome.unwrap().witness(), Some([F::new(2), F::new(3)]));
```

The slice ideal is `I + <x_i - a_i>`, **not** the substituted generators alone. Because `const N`
is not replaced, a fixed variable does not leave the ring — substitution only removes it from every
monomial, and a variable in no generator is *unconstrained*. `x*y - 6` at `x = 2` substitutes to
`2y - 6`, whose zero set in `F[x, y]` is the line `{(x, 3)}`. So `Specialization::apply` appends
the pinning equations, which generate the same ideal and make the fixed coordinates part of the
answer.

`SliceOutcome` has three variants where a solver has `Option`, and only one of them says anything
about the system you started with:

| outcome | about |
|---|---|
| `Witness(p)` | the **original** system — verified against every original generator |
| `EmptySlice` | this slice: zero-dimensional, no base-field point |
| `SliceInconsistent` | this slice: `1` is in `I_a` |

**A run of dead slices proves nothing.** A section of a nonempty variety can be empty over `F_q`,
and only exhausting all `q^|S|` slices would settle it.
`SliceOutcome::is_evidence_about_the_original_system` returns true for exactly one variant so that
a caller has to pass through it rather than reason about the variants.
`cargo run --release --example specialize_slices` runs ten slices at each of two sizes on one
system — seven witnesses at three fixed, ten dead at six fixed — which closes the argument with
evidence on both sides rather than asserting it. Each slice comes from its own seed, and
`Specialization::seeded` builds the RNG from it, so `seed()` is a promise that the slice
reconstructs; `Specialization::new` takes chosen values and records no seed.

#### Reduced-round Poseidon

`grobner::research::Poseidon` is a port of the 2026 initiative's own cryptanalysis tooling
([`poseidon-tools`](https://github.com/khovratovich/poseidon-tools), Apache-2.0, commit
`60075da7`): KoalaBear, `alpha = 3`, the Grain LFSR round constants, the Cauchy MDS construction,
and the `permutation_plus_linear` variant the CICO verifier uses. **Not toy substitutes**, and that
is checkable rather than asserted — the reference's README records
`permutation([0]*16)[0] == 1393439926` at `t=16, R_F=8, R_P=20`, and the port reproduces it in a
committed test. That one number exercises the LFSR's bit layout, all 448 round constants, the MDS
construction, and the round schedule.

One vector anchors one configuration, though, and the round schedule changes with `R_F` and `R_P`
— so **every** configuration the corpus uses is also checked against vectors generated by the
Python reference, across the whole output state and in both permutation variants.
`Poseidon::new` is bounded on `KnownOrder` and refuses a coefficient type that is not the
parameters' field; `CicoInstance` requires exactly `2k` constants and an exact `N`, since a spare
position is an unconstrained variable that makes the ideal positive-dimensional.

`CicoInstance::system` generates the polynomial system. **Every S-box output is a fresh variable**,
so with `L` the affine form reaching an S-box the equation is `y - L^3 = 0` — degree 3 and no
more, where carrying state words as polynomials would give `3^rounds`. Round constants and the MDS
layer contribute no equations at all; they are affine.

Faithfulness is checked three ways: the system must vanish at a real trace of the permutation
(`verify_against_trace`); corrupting a trace value must break that value's own equation and no
*earlier* one; and any recovered input is verified by running the permutation on it
(`CicoInstance::is_solution`), not by re-evaluating the system. A generator bug cannot make the
last one pass.

Measured frontier, `k = 1`, planted targets:

| reduced to | variables | outcome |
|---|---:|---|
| `t=2 R_F=2 R_P=0` | 5 | solved, 0.8 ms |
| `t=2 R_F=2 R_P=2` | 7 | solved, 156 ms |
| `t=2 R_F=4 R_P=0` | 9 | solved, 371 ms |
| `t=3 R_F=2 R_P=1` | 9 | column budget crossed after ~18 s |

**Nine variables solve at `t = 2` and fail at `t = 3`** — same count, different reach, because the
MDS layer couples three words rather than two. Variable count does not predict reach.

The bounty instance is `t = 16, R_F = 6, R_P = 8`: 104 S-box variables and 118 in total. **No
result on a reduced instance says anything about the full one**, which is why
`CicoInstance::reduced_from` carries the parameters an instance reduced from.

The bounty's *relaxed* CICO verifier is **not** modelled. Its condition is on the low bits of a
field element's canonical integer representative — `(y - c) & mask == 0` — which is not a
polynomial identity over the field. See `docs/research/poseidon.md`.

#### External instances: the Fukuoka MQ Challenge

`grobner::research::MqInstance` imports instances from the
[Fukuoka MQ Challenge](https://www.mqchallenge.org/). The GF(31) families (types III and VI) need
no new arithmetic — `PrimeFieldElement64<31>` already exists — and the GF(2) and GF(2^8) families
are refused by name, because `binary_field` and `extension_field` are not publicly exported.

The coefficient layout is **every monomial of degree at most two in descending grevlex order**,
which is what the file's own `Order` header names. It is implemented by sorting with
`MonomialOrder::GradedReverseLexicographic` rather than as an index pattern, and it was *verified*
rather than assumed: four candidate layouts were evaluated at a published answer and exactly one
makes every polynomial vanish. A monomial-order translation error is the failure mode an importer
has, and it is silent.

On type III `n=10` seed 0 — 20 quadratics in 10 unknowns — zeebra reconstructs the system, confirms
it vanishes at the published answer, and independently recovers that same point in **111 ms** with
`D = 1`. Both directions matter: a wrong layout could vanish at one point by accident, but it could
not also be solved to the same one. This is a *toy* example at 45 variables short of the smallest
unsolved challenge, and is not a competitive result.

**The instance data is not redistributed here** — the files are "All Rights Reserved" with no
stated licence. `tools/fetch-mq-challenge.sh` fetches them into `research/instances/mq/` and
verifies the SHA-256 that `Provenance` pins; the test against a genuine instance is `#[ignore]`d
for the same reason the Singular one is. `docs/research/fukuoka-mq.md` records the format, the
verification, and one quirk worth knowing: coefficients are uniform over `0..=31`, not `0..=30`, so
**zero is twice as likely as any other coefficient** in the published GF(31) data.

`solve_one` is not a convenience wrapper. Time to one solution is dominated by the Gröbner basis
and barely depends on how many solutions exist, while enumerating them all scales with the count —
on a 14-variable system with 16384 solutions that is 1.9 ms against 1.6 s, a factor of **830**.

The older `grobner::solve` is unchanged and still the right call for a positive-dimensional system,
which it handles by enumerating the field.

**Neither strategy dominates.** `SolveStrategy::GrevlexF4ThenFglm` is the only route to katsura-7,
whose lex basis crosses F4's limits; `SolveStrategy::DirectLexF4`, the default, is the only route to
planted-12 and planted-14, whose quotient algebras are too large to build. `cargo run --release
--example solve_one` shows both failures. `solve_one_planned` will choose for you — see
[Letting the solver choose](#letting-the-solver-choose) below — but the choice stays the caller's
by default.

Whether conversion is worth doing depends entirely on the system —
`cargo run --release --example fglm_conversion` measures it. On cyclic-6 the pipeline is **7.4x**
faster than direct lex F4, on katsura-6 **2.5x**, and on katsura-7 direct lex F4 produces **no
basis at all** while the pipeline finishes in 68 ms. On the planted family it loses by up to
**65x**. Automatic selection is opt-in rather than default, and it is not a cost heuristic: it
opens with the route whose *refusal* is cheap and decides the conversion's feasibility from a
counted quotient dimension. See [Letting the solver choose](#letting-the-solver-choose).

### F4

`grobner::f4` computes the same basis by Faugère's F4 algorithm, which replaces individual
S-polynomial reductions with batched symbolic preprocessing and sparse finite-field linear algebra:

```rust
use zeebra::{fields::Zp13, grobner::f4, MonomialOrder, MultivariatePolynomial};

let vars = ["x", "y", "z"];
let system = vec![
    MultivariatePolynomial::<3, Zp13>::parse("x*z - y^2", vars).unwrap(),
    MultivariatePolynomial::<3, Zp13>::parse("x^3 - z^2", vars).unwrap(),
];

let basis = f4(&system, MonomialOrder::GradedReverseLexicographic).unwrap();
```

A reduced Gröbner basis is unique for a given ideal and order, so `f4` and `buchberger` return
exactly the same thing, with the same handling of zero, duplicate, and redundant generators. They
differ only in how they get there, and therefore in cost.

**Which to use.** `buchberger` is the better choice on small systems, where building a matrix costs
more than the reductions it replaces. F4 pays off where Buchberger wastes the most work: on
katsura-5 under lex, Buchberger reduces 1790 S-polynomials and 1725 of them come out zero, while
F4 covers the same ground in 29 matrices. See
[`docs/MILESTONE-F4.md`](docs/MILESTONE-F4.md) for measurements, including the cases where F4
loses.

`f4` returns a `Result`: an F4 matrix can grow far beyond what its inputs suggest, and elimination
can make it denser still, so both are budgeted. Exceeding a budget is an `F4Error` naming the limit
— never a basis that looks complete and is not. `f4_with_options` takes an `F4Options` and returns
`F4Statistics` alongside the basis:

```rust
use zeebra::{fields::Zp13, grobner::{f4_with_options, F4Options}, MonomialOrder, MultivariatePolynomial};

let vars = ["x", "y", "z"];
let system = vec![MultivariatePolynomial::<3, Zp13>::parse("x*z - y^2", vars).unwrap()];
let options = F4Options { max_pairs_per_batch: Some(16), ..F4Options::default() };

let (basis, statistics) =
    f4_with_options(&system, MonomialOrder::GradedReverseLexicographic, &options).unwrap();
println!("{} batches, largest matrix {} x {}",
    statistics.batches, statistics.max_matrix_rows, statistics.max_matrix_columns);
```

`max_pairs_per_batch: Some(1)` reduces one S-polynomial per matrix, which is useful for isolating
the effect of batching; the answer does not change, only the number and shape of the matrices.

#### Entry budgets and byte budgets

The matrix's storage is budgeted twice, and both budgets are enforced. `max_live_nonzeros` counts
mathematical nonzeros; `max_live_bytes` counts what they occupy. An entry is a column index and a
field element, so it costs `size_of::<(usize, F)>()` — **16 bytes over a 64-bit prime field and 40
over BN254** — and an entry budget alone therefore admits 2.5x the memory over the wide field:

```rust
use zeebra::{fields::{Bn254Fr, Zp18446744073709551557}, grobner::F4Options};

let options = F4Options::default();              // 20,000,000 entries and 320 MB
assert_eq!(options.live_entry_allowance::<Zp18446744073709551557>(), 20_000_000);
assert_eq!(options.live_entry_allowance::<Bn254Fr>(), 8_000_000);   // the same 320 MB
```

The two agree over a 64-bit field, which is the width every F4 figure in
[`docs/MILESTONE-F4-OPTIMIZATION.md`](docs/MILESTONE-F4-OPTIMIZATION.md) was measured at, so the
byte budget binds only where it is needed. Whichever budget bound names the error:
`F4Error::TooManyNonzeros` or `F4Error::TooManyLiveBytes`. `FglmOptions` is the same shape —
`max_operator_bytes` beside `max_operator_entries`, and `max_span_bytes` beside `max_span_entries`.

Neither is a ceiling on the process. `F4Statistics::peak_live_bytes` reports what the budget
enforces; `max_dense_buffer_bytes` reports what it deliberately omits — the dense buffer the
elimination backend allocates, which under `Backend::Dense` is `rows * columns` cells and a
function of the shape alone. `max_estimated_bytes` is the two added, per batch, maxed over batches.
None of them accounts for the monomial-to-column map, the basis's term vectors, or allocator
overhead; for the process figure use `util::peak_resident_bytes`.

#### What the computation did before it ran out of room

`f4` and `f4_with_options` discard their counters on the error path, which is the case where they
say most. `f4_reported` keeps them:

```rust
use zeebra::{fields::Zp2147483647, grobner::{benchmark_systems::katsura, f4_reported, F4Error, F4Options},
             MonomialOrder};

let options = F4Options { max_batches: Some(2), ..F4Options::default() };
let (result, statistics) = f4_reported(
    &katsura::<6, Zp2147483647>(),
    MonomialOrder::GradedReverseLexicographic,
    &options,
);

assert_eq!(result.unwrap_err(), F4Error::TooManyBatches { limit: 2 });
assert_eq!(statistics.batches, 2);        // the work done before the refusal
assert!(statistics.max_matrix_rows > 0);
```

A crossed budget still cannot be mistaken for a finished one: the basis lives inside the `Result`,
so an incomplete computation has no basis to hand back, and the statistics beside it describe work
rather than an answer.

#### Choosing a strategy

`F4Options` also selects *how* the computation is performed. A reduced Gröbner basis is unique for
a given ideal and order, so **no strategy changes the answer** — only the cost. Each is a separate
field rather than one "fast" switch, so that the contribution of each can be measured on its own:

| Field | Choices | What it changes |
|---|---|---|
| `elimination` | `Backend::{Sparse, Dense, Adaptive}` | the representation elimination works in: sparse rows throughout, dense rows throughout, or sparse rows reduced through a dense accumulator |
| `reduction` | `ReductionStrategy::{Unstructured, Structured}` | whether reducer rows are established as pivots before the pair rows are reduced against them |
| `reducer_selection` | `ReducerSelection::{FirstApplicable, LargestLeadingMonomial}` | which basis element symbolic preprocessing picks to reduce a monomial. `FirstApplicable` is the default and the faster of the two: picking the largest divisor minimizes the multiplier but maximizes how much of the reducer's tail stays reducible, which grows the matrix |
| `criteria` | `PairCriteria { product, chain, gebauer_moller }` | which criteria may discard a critical pair before a matrix is built |
| `reducer_cache` | `CacheMode::{Off, Count, Store}` | whether reducer multiples are remembered between batches. `Count` measures repetition without serving anything; `Store` currently behaves as `Count`, because building a multiple's terms is an integer addition per variable per term and serving them from a map costs more than that even at a 95% hit rate |
| `measure_stages` | `bool` | whether `F4Statistics::stages` is populated |

`ReductionStrategy::Structured` exploits the fact that symbolic preprocessing gives every reducer
multiple a distinct leading monomial, none of them a critical pair's lcm: putting those rows first,
descending by leading monomial, makes the upper-left block unit upper triangular without any work,
so elimination takes those pivots as given and never reduces the block against anything. It
performs *more* row operations than the one-pass path and far less fill-in — on katsura-7 under
grevlex, 8% of the baseline's peak live entries — which is a net win on the dense grevlex and lex
instances and a small loss under grlex. The per-order numbers are in
[`docs/MILESTONE-F4-OPTIMIZATION.md`](docs/MILESTONE-F4-OPTIMIZATION.md) §7.1.

There are two named configurations, and both are public on purpose:

- **`F4Options::recommended()`**, which is what `default()` is — structured elimination, all pair
  criteria, the dense accumulator. It is the fastest of twelve configurations on ten of eleven
  instances measured; on the eleventh the criteria have already made elimination 9% of the total,
  so the accumulator's gain there is smaller than run-to-run variation.
- **`F4Options::baseline()`**, every strategy off. This is the configuration the measurements are
  taken against, and it is kept reachable so they can be reproduced; a default that absorbed its
  own reference would make the comparison impossible to repeat.

Note that two of the improvements are *not* selectable, because they are not trade-offs: a cheaper
monomial hash in symbolic preprocessing and the rewritten final interreduction apply to
`baseline()` too.

`PairCriteria::NONE` reduces every pair, which is the reference the criteria are checked against: a
criterion is sound exactly when enabling it does not change the basis.

With `default()`, **F4 is faster than `buchberger()` on every system and order measured** — 1.2x
to 236x — and katsura-6 under grevlex, F4's worst case at 0.47x one milestone ago, is 3.8x.

That comparison is between the two functions' defaults, and the two defaults are not
algorithmically matched: the pair criteria are **shared machinery**, and `F4Options::recommended()`
enables `PairCriteria::ALL` while `buchberger()` uses `PRODUCT_ONLY`. Give the classical engine the
same criteria via `buchberger_with_criteria` and it speeds up 2.2x to 13.1x on its own; F4 then
wins on fourteen of sixteen instances by 1.12x to 45x, and loses on two instances under 100
microseconds where there is nothing to amortise. That matched figure is the one that isolates F4's
*matrix algorithm* from the critical-pair selection either engine can use.

The criteria also change what is *reachable*: katsura-7 is within `buchberger`'s range with them
and was not without. The one instance that remains categorically F4's is **katsura-6 under lex** —
the classical engine does not finish it in 900 seconds with every criterion enabled, and F4
returns the same basis in 16 ms.

`cargo run --release --example f4_milestone` reports both columns; §8.3 of
[`docs/MILESTONE-F4-OPTIMIZATION.md`](docs/MILESTONE-F4-OPTIMIZATION.md) has the analysis.

Every backend returns the identical matrix and the identical `EliminationStatistics`, so the choice
is purely a cost one. `Backend::Adaptive` is the fastest on every instance measured — 1.2x to 2.0x
over `Sparse` on the elimination stage — and `Backend::Dense` is slower than `Sparse` everywhere,
which is the honest answer to whether a dense representation pays on F4-shaped matrices. It is kept
because it is the control the other two are compared against. See §7.4 of
[`docs/MILESTONE-F4-OPTIMIZATION.md`](docs/MILESTONE-F4-OPTIMIZATION.md).

The three criteria are Buchberger's first criterion (`product`, relatively prime leading
monomials), Buchberger's chain criterion (`chain`, applied when a batch is selected), and
Gebauer–Möller pair-set minimization (`gebauer_moller`, applied as pairs are inserted). All three
are available to both engines, and `examples/pair_criteria.rs` reports what each discards.
Gebauer–Möller is the strongest of the three in F4 — on katsura-6 under lex it takes the pairs
reduced from 4611 to 231 and the largest matrix from 1954 rows to 92 — and it subsumes what the
chain criterion finds at selection time, so enabling both discards nothing more than enabling
Gebauer–Möller alone. In the classical engine neither dominates: on katsura-5 under lex the chain
criterion reduces fewer pairs than Gebauer–Möller does.

`grobner::solve` still uses `buchberger`. The sparse linear algebra F4 is built on is reusable on
its own, as `linalg::sparse`, with the dense representations as `linalg::dense`;
`linalg::echelon` is the backend-selecting interface over both.

`grobner::trace_batches` runs a computation and returns every batch it reduced, each as the basis
at the time plus the pairs selected. That is what lets a stage be benchmarked or counted on real
input instead of on a synthetic approximation of it; `benches/f4_stages.rs` is built on it.

Field elements reject non-canonical representatives on deserialization. Every value this crate
serializes round-trips unchanged, but bytes encoding an integer outside `[0, P)` are an error
rather than being silently reduced, since they indicate corruption or a mismatched modulus.

## Solving Polynomial Systems
`grobner::solve` finds every point of F^N at which a system of multivariate polynomials
vanishes, over a finite field F:

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

It computes a lexicographic Grobner basis, which is triangular, then assigns variables from the
last backwards. At each step the basis polynomials that have become univariate in the current
variable are solved with `roots`, so only their common roots are tried. An inconsistent system is
detected from its basis being `{1}` and yields no points. The order of the returned points is
unspecified.

A system with finitely many solutions therefore needs no enumeration, and works over fields far
too large to list — the tests cover GF(2^31 - 1) and the largest 64-bit prime.

A system that leaves a variable unconstrained is the exception. Its solution set grows with the
field, so covering a free variable means enumerating, and `solve` refuses above an order of 2^20.
That is a limit on the size of the answer rather than on the method.

## Factoring Univariate Polynomials
`factorize` returns the monic irreducible factors of a univariate polynomial over a finite field,
with multiplicities, and `is_irreducible` tests a single polynomial:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{factorize, fields::Zp7, is_irreducible, FiniteField, UnivariatePolynomial};

// x^3 + 6x^2 + 11x + 6 = (x + 1)(x + 2)(x + 3) over GF(7)
let f = UnivariatePolynomial::<Zp7>::new(&[
    Zp7::new(6), Zp7::new(11), Zp7::new(6), Zp7::new(1),
]);

let mut rng = StdRng::seed_from_u64(0);
for (factor, multiplicity) in factorize(&f, &mut rng) {
    assert!(is_irreducible(&factor));
    println!("({})^{}", factor, multiplicity);
}
```

The distinct irreducible factors of each degree are collected with `gcd(f, x^(q^d) - x)`, then
each group of equal-degree factors is separated by Cantor–Zassenhaus splitting. Because
`x^(q^d) - x` is squarefree, that gcd gives the distinct factors whatever the multiplicities in
`f` are — so no squarefree decomposition is needed, and `x^p` in characteristic `p`, whose
derivative vanishes, needs no special handling. Multiplicities are recovered afterwards by
division.

Splitting is randomized, so this takes an rng and the order of the returned factors is
unspecified.

## Why You *Shouldn’t* Use Zeebra
I wrote Zeebra as an educational exercise. It is not yet complete or mature. It is not necessarily correct. For something more production-ready, please consider:

- **[arkworks-rs/algebra](https://github.com/arkworks-rs/algebra/tree/master)** - Algebraic structures and operations for zkSNARKs
- **[dimforge/nalgebra](https://github.com/dimforge/nalgebra)** - Linear Algebra library for the Rust programming language
- **[tspiteri/rug](https://gitlab.com/tspiteri/rug)** - Arbitrary-precision numbers
- **[axect/peroxide](https://github.com/Axect/Peroxide)** - Linear algebra library for machine learning
