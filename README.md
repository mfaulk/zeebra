
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
- [x] Two-adic roots of unity without factoring `q - 1`, so the NTT runs over the wide fields
- [x] Batch inversion by Montgomery's trick: the inverse NTT now costs what the forward one does
- [x] A frozen registry of public cryptanalysis challenges, and a scoreboard that refuses to
      compare two different problems
- [x] A verified CICO witness at Poseidon-31's official state width `t = 16`, for a registered
      reduced-round instance

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

CI runs the suite twice: once in debug, and once in release in a separate job. Both configurations
are checked because a release build takes different paths — `debug-assertions` and
`overflow-checks` are off, so every
`debug_assert`-guarded invariant goes unchecked and integer arithmetic wraps instead of panicking.
Release is also the configuration every benchmark uses, so

```sh
cargo test --release
```

is worth running locally before claiming a measurement.

The two Gröbner engine-agreement tests above run in that release job, but on pushes to main and on
manual dispatch only, not on pull requests. They take 145s on a shared runner — a quarter of the
job's wall clock, on the critical path of every pull request — and they reuse the build the steps
before them already paid for, so running them after a merge costs almost nothing.

A third job runs the benchmarks, on pushes to main and on manual dispatch only. The benchmark
targets are declared `test = false`, which keeps them out of `cargo test`: a `[[bench]]` target
defaults to `test = true`, so a bare `cargo test` linked all eight criterion binaries under fat
LTO and executed all 455 cases. That took 168s of the 180s a warm `cargo test --release` spent,
against 2.4s for the 968 tests and 8.9s for the doc examples. Smoke-testing the benchmarks is
still worth doing — it catches one that panics rather than merely failing to compile — so it moved
to its own job rather than being dropped:

```sh
cargo bench --profile ci-release -- --test
```

`cargo bench -- --test` and not `cargo test --benches`, which now selects nothing and would pass
vacuously. A benchmark that stops *compiling* still breaks the `cargo build --all-targets` step in
the pull-request jobs.

`--profile ci-release` because this job takes no measurements. A bare `cargo bench` resolves
`[profile.bench]`, which inherits `release`, and links all eight criterion binaries under fat LTO
at one codegen unit — settings that exist to make a measurement reproducible. Cold, for one bench
target, that is 193s against 34s under `ci-release`. The trade is that no CI job compiles the
fat-LTO profile any more, so a failure that appears only at one codegen unit surfaces on the
machine taking the measurement instead; a local `cargo bench` is unchanged.

The release job builds under `[profile.ci-release]` rather than `release`. It inherits `release`,
so `debug-assertions` and `overflow-checks` are off and the job tests exactly what it did before,
but it drops the single codegen unit that makes a `release` build expensive — `Swatinem/rust-cache`
caches dependencies and never the crate under test, so `zeebra` is relinked from scratch on every
run, which was ~318s of a 321s step. Cargo.toml records the four configurations measured and why
this one was chosen; it is a compromise, because the codegen setting that makes the build cheap
also slows the two engine-agreement tests. Reported numbers are unaffected — a local `cargo bench`
resolves `[profile.bench]`, which still inherits `release`, so every measurement stays comparable
with every measurement recorded before this profile existed.

A fourth job checks formatting and runs clippy. Both are in one job because `cargo fmt --all
--check` takes a tenth of a second and needs no cache, so on its own it was almost entirely runner
start-up.

Each pull request and each branch has one run in flight at a time; a new push cancels the one
before it. A stack of dependent pull requests is merged one commit at a time, so pushing a stack
sends a burst of pushes seconds apart — eight merges in 90 seconds spent 135 job-minutes, most of
it on commits that were superseded before the first job finished, and queued 40 jobs against a
20-job ceiling. Cancellation applies on `main` too, so an intermediate merge commit there can go
untested; every commit in a stack is green as a pull request before it is merged, and the tip of
the burst is tested in full.

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
cargo run --release --example f4_degrees           # F4, work and useful work per degree
cargo run --release --example f4_schedule          # critical-pair order, and batch size, apart
cargo run --release --example f4_schedule -- list  # the instances available
cargo run --release --example hilbert_study         # the semiregular model against the measurement
cargo run --release --example cryptanalysis_ladder  # Poseidon and MQ, with every transform inverted
cargo run --release --example hilbert_driven        # a predicted cap against a cap chosen without one
cargo run --release --example hilbert_driven -- list
cargo run --release --example m22_ablation          # every M22 strategy, one table per instance
cargo run --release --example m22_ablation -- list
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
cargo run --release --example field_width          # what a 4-byte field element is worth, per
cargo run --release --example field_width -- axpy  # arm: the kernel, a dense echelon, F4
cargo run --release --example mq_challenge         # import and solve a Fukuoka MQ instance
cargo run --release --example poseidon_cico        # reduced-round Poseidon CICO, end to end
cargo run --release --example univariate_scaling   # univariate cost and memory against degree
cargo run --release --example univariate_scaling -- list
cargo run --release --example batch_inversion      # batch inversion: routine, integration,
cargo run --release --example batch_inversion -- f4   # and the F4 headroom left alone
cargo run --release --example scoreboard           # registered problems, one record each, staged
tools/scoreboard.sh stable --write                 # the same, pinned, updating research/scoreboard
tools/scoreboard.sh ladder --write                 # the nine full-width t = 16 CICO rows
cargo run --release --example resultant_cico       # a resultant against F4 on the same slices
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

`f4_degrees` is M22-0's baseline: one table per system giving, for each lcm degree, the pairs
selected and discarded, the split of matrix rows into reducer scaffolding and pair halves, **the
rank the pair rows added on top of the reducer block**, the pair rows that added nothing, the
largest matrix, the elements extracted, and how many of those came out below the degree that found
them. It covers katsura-5 for calibration, the Fukuoka type III and VI toy instances, and the
controlled Poseidon family — where the `t = 3` and `t = 2` nine-variable instances **do not have
the same algebraic dimension** (`N - E = t - 2k`), so the `t = 3` system is also run with one free
input pinned, which matches the equation counts without changing the round structure. Needs
`tools/fetch-mq-challenge.sh` for the MQ sections; the rest runs without it.

`m22_ablation` is M22-I's: the whole M22 strategy matrix on one table per instance, over the
corpus of §11.2 — katsura-5/6/7, cyclic-5/6, a planted system, a nonradical ideal, a
positive-dimensional one, the Fukuoka type III and specialized type VI instances, and three Poseidon
systems. Every row's basis is **asserted** equal to the baseline's and certified, since a differing
basis is a defect and a column reporting one would bury it. `total ms` is solve plus certification,
which is the only figure a default decision may use. Variable order is held fixed at the generated
layout throughout — M22-E measured it at 1.6x–1.7x, which would otherwise be attributed to whichever
F4 strategy varied alongside it. There is no mutant row, because M22-D added no mutant mode; `D = A`
is printed to make the gap explicit. See
[`docs/MILESTONE-DEGREE-AWARE-F4.md`](docs/MILESTONE-DEGREE-AWARE-F4.md).

`hilbert_study` is M22-B's measurement: the exact Hilbert function of each computed basis's
leading-term ideal against the semiregular prediction, degree by degree, with the first
disagreement and its sign reported. It covers textbook regular sequences, random homogeneous
quadratics, deliberate counterexamples, the Fukuoka type III top forms *and* the published
inhomogeneous instances, and reduced-round Poseidon. See
[`docs/research/hilbert-functions.md`](docs/research/hilbert-functions.md) for the tables.

`f4_schedule` is M22-A's measurement: three deterministic critical-pair orders on one table per
instance, with the computed basis asserted equal to the baseline's on every row. Ordering and batch
sizing get a table each, deliberately — a sort and a cap varied together cannot be attributed —
plus a cross product on one instance to check whether the two interact. `-- list` names the
instances and `-- <name>` runs one per process.

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
M18 did not touch it, and two follow-ups did: offsetting each echelon row's coordinates by its
pivot, and reducing into registers the span owns rather than allocating a residue per candidate.
Together, on one pinned and interleaved protocol, they take planted-10's lex walk from 23.2 ms to
11.1 ms — 2.09x — and the conversion's dense blocks from 20,484 kB to 16,392 kB, which is a fifth
of them and not a quarter.

Recorded baselines, before/after measurements, and the reasoning behind each optimization are in
[`docs/MILESTONE-ALGEBRA-FOUNDATION.md`](docs/MILESTONE-ALGEBRA-FOUNDATION.md),
[`docs/MILESTONE-F4.md`](docs/MILESTONE-F4.md),
[`docs/MILESTONE-F4-OPTIMIZATION.md`](docs/MILESTONE-F4-OPTIMIZATION.md),
[`docs/MILESTONE-FGLM-SOLVING.md`](docs/MILESTONE-FGLM-SOLVING.md),
[`docs/MILESTONE-FGLM-SCALABILITY.md`](docs/MILESTONE-FGLM-SCALABILITY.md),
[`docs/MILESTONE-SIMD-PARALLELISM.md`](docs/MILESTONE-SIMD-PARALLELISM.md),
[`docs/MILESTONE-LARGE-PRIME-FIELDS.md`](docs/MILESTONE-LARGE-PRIME-FIELDS.md),
[`docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md`](docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md),
[`docs/MILESTONE-DEGREE-AWARE-F4.md`](docs/MILESTONE-DEGREE-AWARE-F4.md), and
[`docs/MILESTONE-CRYPTANALYSIS-SCOREBOARD.md`](docs/MILESTONE-CRYPTANALYSIS-SCOREBOARD.md).

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
| `Mersenne31` | 31, in 4 bytes | 1.35 ns | 0.75 ns | 0.75 ns | 227 ns |
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

### A 32-bit prime field

`PrimeFieldElement32<P>` is the same field as `PrimeFieldElement64<P>` for any modulus both can
hold, in half the bytes. Montgomery form with R = 2^32, the representation unobservable in the same
two ways; the one place the arithmetic is not a mechanical substitution is that `t + m*P` needs 65
bits only when P exceeds 2^31, and that predicate is on the const generic, so every declared
modulus gets a reduction with no carry handling in it.

```rust
use zeebra::{fields::{BabyBear, Mersenne31, Zp2147483647}, FiniteField, KnownOrder};

assert_eq!(std::mem::size_of::<Mersenne31>(), 4);
assert_eq!(std::mem::size_of::<Zp2147483647>(), 8);
assert_eq!(Mersenne31::order_u128(), Zp2147483647::order_u128());

let a = Mersenne31::new(827376);
assert_eq!(a.pow(2).value(), 1651245630);   // the canonical residue, not the Montgomery form
assert_eq!(BabyBear::order_u128(), Some(2013265921));
```

Declared: `Zp31` (Fukuoka MQ types III and VI), `Zp65537_32`, `Mersenne31`, `BabyBear`
(`2^31 - 2^27 + 1`) and `KoalaBear` (`2^31 - 2^24 + 1`, the 2026 Poseidon challenge prime). The
last two are NTT-friendly; `Zp65537_32` and `Zp2147483647` are the same mathematical fields as
`Zp65537` and `Mersenne31`'s 64-bit twin, so a caller picks a width rather than a field.

**What it is worth, and where.** `cargo run --release --example field_width`. The kernel is
`target -= factor * source` with the nonzero counters the dense backend maintains, at a fixed
*entry* count so that both widths do the same number of cell updates:

| working set (u32/u64) | u64 ns/entry | u32 ns/entry | u32 GB/s | AVX2 8 lanes | AVX2 GB/s |
|---|---:|---:|---:|---:|---:|
| 8 / 16 KB | 1.802 | 0.765 | 15.7 | **0.264** | 45.4 |
| 256 / 512 KB | 1.770 | 0.751 | 16.0 | **0.253** | 47.5 |
| 16 / 32 MB | 1.783 | 0.753 | 15.9 | **0.262** | 45.8 |
| 128 / 256 MB | 1.897 | 0.786 | 15.3 | **0.446** | 26.9 |

Two things in that table correct the premise it was built on. **The scalar kernel is ALU-bound at
both widths, not bandwidth-bound**: ns/entry is flat to within 7% over a working set spanning four
orders of magnitude — the 256 MB row re-ran at 1.804 — and 15.9 GB/s is well under what one core
can pull. So the 2.36x is not
halved bytes — it is that a 64-bit Montgomery reduction is 128-bit arithmetic that does not
vectorize, and a 32-bit one is 64-bit arithmetic that does. **Only the AVX2 kernel is fast enough
for the bytes to bind**, and it is where halving them pays: 45 GB/s in cache falling to 26.9 GB/s
out of it, which at 24 bytes an entry would have been 0.89 ns rather than 0.446.

That also reverses M19-D's answer. At four lanes over `u64` hand-written AVX2 ran 0.86x to 1.07x
against autovectorization; at eight lanes over `u32` it runs **1.7x to 3.0x**, against a scalar
comparand LLVM did vectorize (`vpmuludq` present in both, verified in the artifact). No intrinsics
are shipped — the kernel lives in the example, cross-checked cell for cell and counter for counter
against the scalar one — but the question is no longer closed.

Whole eliminations, same matrices at both widths:

| | u64 | u32 | ratio |
|---|---:|---:|---:|
| dense echelon, 1500x1500 at 5% | 2515.6 ms, 17.2 MB | 882.9 ms, 8.6 MB | 2.85x |
| dense echelon, 3000x3000 at 2% | 19789.6 ms, 68.7 MB | 6868.0 ms, 34.3 MB | 2.88x |
| F4 elimination, katsura-6 grevlex, `Backend::Dense` | 70.78 ms | 25.27 ms | 2.80x |
| F4 elimination, katsura-6 grevlex, `Backend::Sparse` | 35.03 ms | 25.90 ms | 1.35x |
| F4 elimination, katsura-6 grevlex, `Backend::Adaptive` | 6.60 ms | 6.41 ms | 1.03x |

**The last row is why no benchmark switched its field.** `Backend::Adaptive` is what
`F4Options::default()` selects and it is 4x faster than the dense backend at either width, so it is
the configuration that matters — and it gains nothing, because its cost is sparse-index traversal
and scatter/gather into a buffer rather than cell traffic. The sparse backend gains little for a
related reason: a sparse entry is `(usize, F)`, which the index's alignment pads to **16 bytes at
either width**, so sparse storage does not shrink at all and `F4Options::live_entry_allowance` is
unchanged. The narrower field is a 2-3x win on the dense path, a memory halving wherever cells are
stored bare, and the enabler for eight-lane SIMD. It is not a free 2x on F4 as shipped.

The dense entry-budget conversion in `linalg::dense::rows` does move, and not by the factor a
reader would guess: `cells_per_entry` goes from two to **four**, since the entry cost is pinned at
16 bytes by the index while the cell cost halves.

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
- `primitive_element` is `unimplemented!()`: finding a generator of the multiplicative group
  means factoring a 254-bit `q - 1`, which no algorithm here needs and which should not start by
  accident. `root_of_unity` works for any **power-of-two** order, through the two-adic
  construction below, and panics for any other — that order is the one that needs the
  factorization.

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
`characteristic_u128` for callers that need a machine integer and can fail without one, plus
`primitive_element`, `root_of_unity`, `two_adicity` and `two_adic_root_of_unity`. For an extension
field q = p^k, so the order and the characteristic are genuinely different; both are reported.

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

### Batch inversion

Inversion is the most expensive operation a prime field has. `batch_invert` and `batch_inverse`
apply Montgomery's trick — prefix products turn n inversions into **one** inversion and `3(n-1)`
multiplications:

```rust
use zeebra::{fields::{batch_inverse, batch_invert, Bn254Fr}, FiniteField, One, Zero};

let values = [Bn254Fr::new(3), Bn254Fr::zero(), Bn254Fr::new(5)];
let inverses = batch_inverse(&values);

// Each nonzero element is inverted...
assert!((values[0] * inverses[0]).is_one());
assert!((values[2] * inverses[2]).is_one());
// ...and a zero is left as zero rather than panicking.
assert!(inverses[1].is_zero());

// The in-place form, for a vector you already own.
let mut owned = vec![Bn254Fr::new(7); 4];
batch_invert(&mut owned);
assert!(owned.iter().all(|x| (*x * Bn254Fr::new(7)).is_one()));
```

**A zero is left as zero.** A batch comes from a container, and a container of field elements may
legitimately hold zeros, so panicking would make the routine unusable where it is most wanted.
`FiniteField::inverse` keeps its panic because there the caller named the one element it was asking
about.

The crossover is **n = 2** in every field; a single-element batch loses by a few percent to the
copy. The plateau is the ratio between an inversion and three multiplications — 35x over
Mersenne-31, 38x over the 254-bit fields, up to 90x over Goldilocks, whose inversion is an
exponentiation by a 64-bit exponent.

`FFTDomain::inverse` is where it is wired in, and `fft::interpolate` additionally hoists the one
`1/n` it used to compute per coefficient. Together those make the inverse transform cost what the
forward transform costs; see "Number-Theoretic Transform" below and
[`docs/research/batch-inversion.md`](docs/research/batch-inversion.md) for the measurements and for
why F4's pivot normalization is deliberately *not* batched.

## Dense Matrices

`linalg::Matrix<T>` is a dense matrix over any `T: Ring`, stored row-major, with the `matrix!`
macro for small literals and `zero`, `identity`, `from_diag` and `new` for the rest. Rows are
reachable by `row`, `row_mut`, `rows` and `rows_mut`; columns by `column` and `columns`, which walk
the buffer at a stride of `num_columns` rather than materializing a `transpose()`. Over a
`FiniteField` there are also `rank`, `inverse` and `determinant`.

```rust
use zeebra::{fields::Zp541, linalg::Matrix, matrix, FiniteField};

type F = Zp541;

let a = matrix![
    F::new(1), F::new(2);
    F::new(3), F::new(4)
];
assert_eq!(
    a.column(1).copied().collect::<Vec<F>>(),
    vec![F::new(2), F::new(4)]
);
assert_eq!(a.columns().count(), 2);

// [A | I], the augmented matrix an inversion reduces.
let augmented = a.hconcat(&Matrix::identity(2)).unwrap();
assert_eq!(augmented.shape(), (2, 4));

// The other dimension has to agree, and the error reports both shapes when it does not.
assert!(a.vconcat(&Matrix::identity(3)).is_err());

// The transfer matrix of the Fibonacci recurrence: its nth power holds F(n+1) and F(n).
let fibonacci = matrix![
    F::new(1), F::new(1);
    F::new(1), F::new(0)
];
assert_eq!(fibonacci.pow(10).unwrap()[[0, 1]], F::new(55));
```

`pow` is repeated squaring, so a large exponent costs log-many multiplications; it returns
`Err(NotSquare)` for a non-square matrix, including at exponent zero, where there is no size the
identity could take. `hconcat` and `vconcat` return `Err(IncompatibleShapes)` carrying both shapes.

Two gaps are deliberate. There is no mutable column iterator — handing out disjoint `&mut` down a
strided column of a row-major buffer is where the borrow checker stops being free, and nothing in
the crate needs it yet. And `Matrix<T>` does not implement `Ring`, so a matrix cannot yet be a
polynomial coefficient: `Ring` has no fallible operations, and only *square* matrices form one, so
that wants a `SquareMatrix<T>` type carrying the invariant rather than a runtime check inside
`mul`. [#132](https://github.com/mfaulk/zeebra/issues/132) has the discussion.

## Number-Theoretic Transform

`fft::evaluate` and `fft::interpolate` are the forward and inverse transforms over an `FFTDomain`
of size `2^k`, built from a primitive `2^k`-th root of unity.

Over a 254-bit field there was no way to obtain one: the generic construction raises a *generator*
of the multiplicative group to `(q - 1) / n`, and finding a generator means factoring a 254-bit
`q - 1`. The two-adic construction needs no generator. Writing `q - 1 = 2^s * m` with m odd — both
read off `q - 1` by shifting — the 2-Sylow subgroup is cyclic of order `2^s`, and `z^m` generates it
for any non-square z, which half the field is:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    evaluate, fields::Bn254Fr, interpolate, FFTDomain, KnownOrder, Polynomial,
    UnivariatePolynomial,
};

// Derived from the compiled-in modulus, so it cannot disagree with the field.
assert_eq!(Bn254Fr::two_adicity(), 28);

let mut rng = StdRng::seed_from_u64(1);
// A primitive 8th root of unity. `root_of_unity(8, &mut rng)` reaches the same construction.
let w = Bn254Fr::two_adic_root_of_unity(3, &mut rng);
let domain = FFTDomain::from_generator(w, 8);

let p = UnivariatePolynomial::<Bn254Fr>::rand(7, &mut rng);
let values = evaluate(&p, &domain);
assert_eq!(interpolate(&values, &domain), p);
```

`two_adicity()` is the ceiling on every power-of-two transform over the field, since a primitive
`2^k`-th root of unity exists exactly for `k <= s`:

| field | s | largest transform |
|---|---|---|
| `Mersenne31` / `Zp2147483647` — `2^31 - 1` | **1** | 2 |
| `KoalaBear` — `2^31 - 2^24 + 1` | 24 | 2^24 |
| `BabyBear` — `2^31 - 2^27 + 1` | 27 | 2^27 |
| `Zp18446744069414584321` — Goldilocks | 32 | 2^32 |
| `Bn254Fr` | 28 | 2^28 |
| `Bls12_381Fr` | 32 | 2^32 |

`two_adicity` is a provided method on `KnownOrder`, so it reads the same from a 32-bit, 64-bit or
254-bit backing; `Mersenne31` and `Zp2147483647` are the same field at two storage widths and
report the same s.

**Mersenne-31 admits no transform above size two**, which matters because it is the field most of
this crate's F4 benchmarks use. `BabyBear` and `KoalaBear` — the latter being the prime the 2026
Poseidon challenges are over — are NTT-friendly by construction and are what to reach for when a
transform is wanted over a small field.

`FiniteField::pow_limbs` takes its exponent as little-endian limbs, which is what makes the above
possible at all: the odd part of BN254's `q - 1` is 226 bits, so `pow`'s `u128` cannot hold it.

### What the univariate stages cost

`cargo run --release --example univariate_scaling` sweeps six stages by doubling degree until a
wall-clock budget is exceeded, reporting time, the local scaling exponent, and **peak live heap
bytes** from a counting allocator. On a 64-core/300 GB workstation at one second per measurement:

| stage | exponent | KoalaBear | BN254 `Fr` | peak bytes |
|---|---|---|---|---|
| `mul`, schoolbook | 2 | 2^15 | 2^13 | `4 n B` |
| `div`, long division | 2 | 2^15 | 2^13 | `6 n B` |
| `evaluate` (NTT) | 1 | **2^23** | **2^21** | `7 n B` |
| `interpolate` (iNTT) | 1 | **2^23** | **2^20** | `9 n B` |
| `lagrange_interpolate` | 3 | 2^10 | 2^9 | `8 n B` |
| `roots` | 2 | 2^12 | 2^8 | `12 n B` |

`B = size_of::<F>()` — 8 bytes for a 64-bit field, 32 for a 254-bit one, so **4x**. That is not
the 2.5x the F4 budgets are written in: those count sparse `(usize, F)` entries, whose 8-byte index
word is paid whatever the field is and dilutes the ratio. A dense coefficient array has no index
word, so a byte budget carried over from the F4 side under-estimates this layer by 1.6x.

The two transforms are the only quasi-linear stages, and they now cost the same: at a matched
`2^18`, `interpolate` is within 2–10% of `evaluate` over all three fields, where it used to be
2.4x, 5.2x and 8.6x. The whole gap was the `2n` inversions batch inversion removed — see
[`docs/research/batch-inversion.md`](docs/research/batch-inversion.md) §2.3. Multiplication has no
NTT-based path at all, and interpolation at arbitrary abscissae — what an evaluation-interpolation
resultant needs — is cubic. [`docs/research/fast-univariate.md`](docs/research/fast-univariate.md) has the
full curves, the gap list, and what each stage would need to go further.

The published Graeffe-transform root finder that those stages would serve is read and scoped in
[`docs/research/graeffe-root-finding.md`](docs/research/graeffe-root-finding.md), with the algorithm
as pseudocode, the transform size each registered challenge requires against the ceilings above, a
measured answer to whether this crate's NTT is access-bound, and an explicit no-go on every
registered instance.

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
cargo run --release --bin zeebra-differential -- --systems 500 --jobs 8   # eight at a time
cargo run --release --bin zeebra-differential -- --seed 777 --systems 240 \
    --max-degree 4 --max-terms 5 \
    --fixtures src/grobner/differential/fixtures.rs   # regenerate the committed cases
```

**`--jobs` does not change the answer.** Each system is a Gröbner basis, an FGLM conversion and a
blocking Singular subprocess, and `system(index)` is a pure function of `(seed, index)` — nothing
in a system's check reads another's result, so the sweep fans out over whole systems. Each worker
gets its own `SingularOracle` with its own `worker-<i>` scratch subdirectory, because a run's
scratch files are named from a per-oracle counter and two workers in one directory would overwrite
each other's script. The report is assembled **in index order and not in completion order**, and
the progress callback is held back to index order too: a seeded sweep whose failure list depended
on which worker finished first could not be reproduced. `--jobs 1` is the sequential sweep, which
is the default, and the report is pinned equal across one, four and eight jobs by
`test_a_concurrent_sweep_reproduces_the_sequential_report`. `--jobs` is deliberately *not* recorded
in a generated fixture module's regeneration command, since it cannot change a recorded answer.

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

**Variable count does not predict reach** — but the reason is not the state width. `N - E = t - 2k`,
so at `k = 1` the `t = 2` rows are square and the `t = 3` row has one more variable than equation:
the two nine-variable instances are *not the same kind of system*, and the comparison above is
confounded. Controlling for it, by pinning a single free input of the `t = 3` system — which matches
the equation count without touching the round structure — it becomes **the easiest of the three**:
complete in 13.9 ms at degree 5 and 0.2 MB, against the square `t = 2` instance's 367 ms and 3.8 MB,
where unpinned it crossed the column budget at degree 11 and 155 MB.

So what the frontier measures is the underdetermined direction: one free coordinate takes the
computation from degree 5 to degree 11 and from 0.2 MB to 155 MB. The pinned system's dimension is
read from `classify_ideal` of its computed basis rather than inferred from the counts, and the
pinned value is a *planted* one, so a solution is known to exist on that slice — comparing it
against an arbitrary-target CICO challenge would be comparing different distributions. See
[`docs/research/degree-profiles.md`](docs/research/degree-profiles.md) §4.

The bounty instance is `t = 16, R_F = 6, R_P = 8`: 104 S-box variables and 118 in total. **No
result on a reduced instance says anything about the full one**, which is why
`CicoInstance::reduced_from` carries the parameters an instance reduced from.

The bounty's *relaxed* CICO verifier is **not** modelled. Its condition is on the low bits of a
field element's canonical integer representative — `(y - c) & mask == 0` — which is not a
polynomial identity over the field. See `docs/research/poseidon.md`.

##### Relabelling the variables, and getting the answer back

Which variable is `x_0` changes the Gröbner basis, the matrices and the cost, while changing nothing
about the problem — so variable order is a free parameter of a cryptanalytic experiment.
`research::VariableOrder` makes exploring it safe:

```rust
use zeebra::{fields::Zp2147483647, grobner::{benchmark_systems::planted,
             research::{satisfies, VariableOrder}}, FiniteField};

let point = [Zp2147483647::new(7), Zp2147483647::new(11), Zp2147483647::new(13)];
let system = planted::<3, Zp2147483647>(&point);

// sources[new] = old, checked to be a bijection of 0..N.
let order = VariableOrder::<3>::new("reversed", &[2, 1, 0]).unwrap();
let relabelled = order.apply(&system);

// The plant, moved into the new coordinates, solves the relabelled system — and comes back.
let moved = order.forward(&point);
assert!(satisfies(&relabelled, &moved));
assert_eq!(order.recover(&moved), point);
```

The constructor is the only way in and it rejects anything that is not a bijection, because a
non-bijective "permutation" silently identifies two variables and changes the problem. `recover` is
the only way back, and using `forward` in its place produces a point that satisfies nothing — which
on a system whose answer is not known in advance is indistinguishable from a solver that found
nothing. `RoundLayout` builds the three layouts the Poseidon experiments compare, from the
**per-round** S-box variable counts rather than one width, since a schedule mixes full rounds
introducing `t` variables with partial rounds introducing one.

##### Eliminating the variables an affine generator determines

A CICO instance's `k` output constraints are affine and nothing else in the system is.
`research::eliminate_affine` solves each affine generator for its highest-indexed variable and
substitutes, recording an affine expression in the **surviving** variables for each one eliminated.

**Substituting is not enough, and the reason is worth stating.** F4 already reduces by an affine
basis element; what it cannot do is make the variable stop existing, so it keeps a column in every
Macaulay matrix and a place in the monomial order. Worse, after substitution the variable appears in
no generator — so it is *unconstrained*, and the ideal becomes positive-dimensional. That is the
same trap `Specialization::apply` documents. `AffineElimination::project` removes the variables from
the ring at a smaller compile-time dimension, and `lift` puts a solution back; the dimension is
checked to be exactly the number of survivors, since a spare position is another unconstrained
variable.

The sweep is deliberately bounded: it is Gaussian elimination on the affine part of a generating
set, not a general preprocessor and not nonlinear elimination. An affine relation that appears only
after some nonlinear cancellation is not found, and nothing looks for one. A generator that
substitutes to a nonzero constant is **kept**, so an inconsistent system still reports `{1}`.

#### The challenge registry

`grobner::research::registry` is the frozen list of public problems this project measures itself
against: the three 2026 Poseidon-31 CICO targets, a nine-row faithful reduced-round ladder at the
official state width, the small planted surrogates M21 and M22 measured, and the Fukuoka GF(31)
toy examples. A `ChallengeManifest` says what a **problem** is — objective, parameters, target, and
how a claimed answer is checked by something that is not this crate — where an `InstanceManifest`
says what a *file* is.

Three things keep it honest.

**`BenchmarkClass` is part of every row.** A witness for a `t = 2` planted instance and a witness
for the official `t = 16` target are both "solved" in a column that adds them together, and they
are not comparable in any direction. `Significance` is therefore *computed* from the class and the
external status rather than written by a report:

```rust
use zeebra::{fields::PrimeFieldElement64, grobner::research::{
    challenge, BenchmarkClass, ExternalStatus, Significance, KOALABEAR_PRIME}};

type K = PrimeFieldElement64<KOALABEAR_PRIME>;

let official = challenge("poseidon31-cico-rf6-rp8").expect("registered");
assert_eq!(official.class, BenchmarkClass::Official);
assert_eq!(official.external, ExternalStatus::SolvedExternally { verified: "2026-05-06" });

// 14 free inputs and 16·6 + 8 S-box variables, against those plus two output constraints.
assert_eq!((official.variables(), official.equations()), (Some(118), Some(106)));

// The strongest claim available on a challenge that is already solved publicly.
assert_eq!(official.significance(true),
           Significance::Reproduction { externally_verified: "2026-05-06" });
assert_eq!(official.significance(false), Significance::NoWitness);

// A reduction's witness is a real result about a different problem, and says so.
let reduced = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
assert_eq!(reduced.significance(true),
           Significance::ReducedInstanceWitness { of: "poseidon31-cico-rf6-rp8" });

// The registry is executable: a runner takes its instance from here, so there is no second copy
// of the constants to drift from these.
let instance = official.cico_instance::<K>().expect("builds");
assert_eq!(instance.variables(), 118);
```

**Identity is a digest over the problem, not over the paperwork.** `ChallengeManifest::digest` is
SHA-256 of a canonical form covering the family, the objective tag, the parameters and the target.
A corrected URL, a paid bounty or a reworded verifier leaves it alone; a changed round count does
not. That is what lets a comparison refuse to compare two runs of *different mathematical
problems*, which is the one failure a benchmark harness cannot be allowed to make quietly.

**The generator is pinned separately.** A parameter checksum cannot notice a changed generator: if
the Grain LFSR or the Cauchy construction changed, every registered instance would become a
different permutation with an unchanged identity. `derived_digest` hashes the round constants and
MDS matrix, and three of them are pinned in tests.

`dispatch_cico` bridges the const generic — `CicoInstance::system::<N>()` needs `N` at compile time
and the registry has fifteen distinct `N` — in the same shape as `MqVisitor` does for the MQ family.

**A registered problem need not be one this crate can build.** The initiative ran two bounty
programs with objectives at opposite ends of the state — the 2026 CICO program constrains the
leading words, the 2025 program the trailing ones — and three 2025 tiers are still listed as
unsolved. Those are registered, and `cico_instance` and `dispatch_cico` **refuse** them by name:
building a trailing-constraint objective as a leading-constraint one would produce a different
problem wearing that row's identity, and nothing about the result would look wrong. A scoreboard
that listed only what it can run would hide the only open problems on it.

The registry is frozen by `test_the_registry_is_frozen`, which pins every id and digest, so
redefining a registered problem fails a test rather than silently changing what an earlier
measurement meant. See
[`docs/MILESTONE-CRYPTANALYSIS-SCOREBOARD.md`](docs/MILESTONE-CRYPTANALYSIS-SCOREBOARD.md) for the
full table and for what the three 2026 CICO targets' external status implies about what a result
there could claim.

#### The scoreboard

`grobner::research::Scoreboard` collects what runs established about registered problems, and its
job is to refuse three specific mistakes.

**Comparing different problems.** A `RunRecord` references its problem by identity *digest*, not by
name. `Scoreboard::add` looks the problem up in the registry and refuses a run whose digest no
longer matches — the problem was redefined after the run, so the measurement is about something
else. `Comparison::of` refuses two runs of different problems outright, and deliberately does not
compare ids.

**Ranking unfinished runs.** `Scoreboard::best` returns verified witnesses only. Two computations
that crossed a budget at degrees 9 and 11 are not ordered: a higher degree is not nearer a
solution. Those appear in their own table, under a heading that says it is a diagnostic.

**Quoting a difference the hardware cannot resolve.** `Comparison::runtime_readable` is false inside
±20%, which is the band M22 declined to read on this machine. The comparison is still reported, with
the flag.

```rust
use std::time::Duration;
use zeebra::grobner::research::{
    challenge, Comparison, Environment, GrobnerFrontier, RunOutcome, RunRecord, Stage, StageCost};

fn run(id: &str, formulation: &str, millis: u64, bytes: usize) -> RunRecord {
    let manifest = challenge(id).expect("registered");
    let mut run = RunRecord::new(&manifest, formulation);
    run.outcome = RunOutcome::VerifiedWitness;
    run.stages = vec![StageCost::new(Stage::Grobner, Duration::from_millis(millis))];
    run.frontier = Some(GrobnerFrontier { completed: true, peak_estimated_bytes: bytes,
                                          ..GrobnerFrontier::default() });
    run
}

// Two formulations of one problem: M22-E's last-round-first result on this instance.
let baseline = run("poseidon-t2-rf4-rp0-planted", "as generated", 352, 3_800_000);
let candidate = run("poseidon-t2-rf4-rp0-planted", "last-round-first", 219, 2_900_000);
let comparison = Comparison::of(&baseline, &candidate).expect("the same problem");
assert_eq!(comparison.speedup_per_mille, 1_607);          // 1.607x, as two integers
assert_eq!(comparison.memory_reduction_basis_points, 2_369);
assert!(comparison.runtime_readable);

// A different problem is refused rather than rendered.
let elsewhere = run("poseidon-t2-rf2-rp2-planted", "as generated", 143, 1_700_000);
assert!(Comparison::of(&baseline, &elsewhere).is_err());
```

Costs are recorded **per stage** — generation, Gröbner, conversion, univariate, verification —
because M20 measured that over a wide field the cost is not in the matrices, and a single total
hides the stage that dominates. The runner therefore drives `f4_reported`, then
`fglm_to_lex_with_options`, then `solve_from_lex_basis` itself rather than calling
`solve_one_planned`.

A randomized specialization campaign is summarized by `Campaign`, which reports the slices that
found **nothing** alongside the one that worked: work per witness is the whole campaign's time over
the witnesses, and the success rate carries a 95% Wilson interval. One witness in twenty slices is
a rate of 0.89% to 23.6%, which is a different claim from "solved in 2 seconds".

```sh
tools/scoreboard.sh                    # smoke tier: the surrogates, nothing written
tools/scoreboard.sh stable --write     # adds the published MQ instances, updates the tree
tools/scoreboard.sh ladder --write     # the nine full-width t = 16 rows, one process each
tools/scoreboard.sh campaign poseidon31-cico-t16-rf2-rp0 --seeds 8 --write
tools/scoreboard.sh formulations poseidon31-cico-t16-rf2-rp0 --slice 1 --write
```

The full-width rows run one process each because the wall-clock supervisor stops a run by
abandoning its worker thread and exiting — F4 has no cooperative time check, so there is no other
way — and that is acceptable once per process and not nine times in one. The budget that actually
binds on those rows is the live-entry cap rather than the clock, which is deliberate: an entry
count is reproducible anywhere, a timeout is a fact about one machine.

**The first verified CICO witness at the official state width** came out of that harness:
`t = 16`, `k = 2`, KoalaBear, the challenge's own input constants, the exact objective, `R_F = 2`
and `R_P = 0`, with twelve of the fourteen free inputs fixed at a precommitted seed. Three of eight
slices produced a point that `permutation_plus_linear` accepts, at **81.2 s of expected work per
witness including the five that found nothing**. The official targets are `R_F = 6` with
`R_P ∈ {6, 8, 10}` and all three were solved externally in 2026; this is a witness for a registered
*reduction*, and the scoreboard says so in those words. See
[`docs/research/full-width-poseidon.md`](docs/research/full-width-poseidon.md) for the eighteen-row
ladder, where each row stops, and the formulation comparison — in which M22-E's winning variable
order turns out to be **2.4x worse** at `t = 16` than the layout it beat at `t = 2`.

The tree under `research/scoreboard/` is committed: the registry emitted from code, one JSON record
per run, the accumulated history, and a generated `SCOREBOARD.md`. `Json::parse` reads back what
`Json::to_json` writes — round-tripping is asserted — so the history accumulates rather than being
overwritten, with no dependency to read eighty lines of writer.

#### Elimination that is not a Gröbner basis

`grobner::research::bivariate_resultant` computes `Res_y(f, g)` for two bivariate polynomials, as
the determinant of their Sylvester matrix recovered by interpolating scalar determinants. The
determinant construction rather than a Euclidean algorithm on purpose: evaluating a matrix and
taking its determinant commutes with evaluation *always*, so there is no case to analyse — where
specializing `f` at a point that kills its leading coefficient in `y` drops its degree, and the
specialized resultant is then not the specialization of the resultant.

It exists to answer one question, and the answer is worth knowing. On a registered `t = 16` CICO
slice — twelve of the fourteen free inputs fixed, two unknowns left — the S-box variables can be
*evaluated away* instead of solved for, because the permutation is a straight-line program. That
turns 46 equations in 46 variables into **two polynomials in two variables** of degree `3^rounds`,
and one resultant finishes it:

| route | time on the same slice | witnesses found |
|---|---:|---|
| grevlex F4, then FGLM, then the search | 30 142 ms | the first one |
| straight-line evaluation, then one resultant | **51 ms** | **all three** |

578x, on the same registered problem, with every candidate checked by running the permutation. The
S-box-per-variable formulation exists to hold the degree at 3 and pays 32 extra variables for it;
when only two inputs are free, those variables are the whole cost and the degree it avoids is
affordable. The resultant route's own limit is arithmetic — about `16 · 3^{5·rounds}` field
operations — so it reaches the same two rounds F4 does and not one more: what it changes is the
cost there, not the frontier. See
[`docs/research/resultant-elimination.md`](docs/research/resultant-elimination.md).

#### External instances: the Fukuoka MQ Challenge

`grobner::research::MqInstance` imports instances from the
[Fukuoka MQ Challenge](https://www.mqchallenge.org/). The GF(31) families (types III and VI) need
no new arithmetic — `PrimeFieldElement64<31>` already exists, and `Zp31` is the same field in four
bytes — and the GF(2) and GF(2^8) families
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

Under one stated budget — 200,000 columns and 20,000,000 live entries, the bound that binds —
`n = 15` **recovers the published answer** in 7.9 s, checked coordinate by coordinate against the
answer file it was not given; `n = 20` crosses the entry cap at degree 5 after 67.5 s. So the
published type III examples end at `n = 15` here. Type VI `n = 15` needs a slice, and all eight
precommitted slices crossed the same cap at degree 9 — recorded as a campaign that **reached no
verdict** rather than as eight failures, because a slice that ran out of budget never tested
whether it contains a solution. `Campaign::decided()` is the rate's denominator for exactly that
reason, and `success_rate_basis_points` returns nothing when nothing was decided.

**The instance data is not redistributed here** — the files are "All Rights Reserved" with no
stated licence. `tools/fetch-mq-challenge.sh` fetches them into `research/instances/mq/` and
verifies the SHA-256 that `Provenance` pins; the test against a genuine instance is `#[ignore]`d
for the same reason the Singular one is. `docs/research/fukuoka-mq.md` records the format, the
verification, and one quirk worth knowing: coefficients are uniform over `0..=31`, not `0..=30`, so
**zero is twice as likely as any other coefficient** in the published GF(31) data.

#### Candidate external instances, surveyed but not imported

[`docs/research/additional-benchmarks.md`](docs/research/additional-benchmarks.md) is the shortlist
of published cryptanalysis instances worth importing next, with the rejections and their reasons.
Four candidates are accepted: reduced-round **Anemoi** CICO, whose reference data is raw Magma F4
and FGLM logs under MIT and whose quotient dimension is a published `(α+2)^N` zeebra can be checked
against; reduced-round **Griffin**; Anemoi's `ACICO` model as a second formulation of the first; and
reduced-round **LowMC**, which is blocked on `binary_field` not being exported. UOV, MAYO, Arion and
XHash8 are rejected, each with a recorded reason. The document also states plainly that the
[LowMC challenge](https://lowmcchallenge.github.io/) is a **claimed-complexity competition** — its
results are `log₂ T` and `log₂ M` estimates, several with memory exponents past 65 bits, and there
are no challenge files to solve.

An accepted candidate becomes a `ChallengeManifest` row, so the document also records what each one
would require of [the registry](#the-challenge-registry): an `AnemoiCico` parameters variant with
the algebraic model *inside the digest*, since `FCICO` and `PCICO` are two different polynomial
systems for the same primitive; a new objective tag for LowMC, whose key recovery is neither
`CicoExact` nor `MqRoot`; and one field the registry does not yet have anywhere — the **published
competitor figure**, which `ExternalStatus` cannot carry because it records whether and when a
problem was solved elsewhere and not at what cost.

`tools/check-griffin-reconstruction.py` is that survey's one executable result. It instantiates
Griffin with `(t, α) = (12, 3)` over the 55-bit prime `p = 28407454060060787` from the constants
published in the FreeLunch appendix, and reproduces all five published CICO solutions for
`r ∈ {5, 6, 7}`:

```sh
tools/check-griffin-reconstruction.py            # 43 ms, standard library only
tools/check-griffin-reconstruction.py --verbose  # print each reconstructed output
```

It exists because the specification is *not* complete on its own: the linear layer comes from the
designers' reference implementation, and the paper's `(δ, µ)` index convention is ambiguous. The
published witnesses decide the ambiguity — one reading reproduces 5 of 5 and the other 0 of 5 — so
the instance is reconstructed rather than guessed. That is the argument the document makes for
preferring candidates that publish a witness.

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

#### Degree by degree, and which of the work was useful

Every counter above is a sum or a maximum over the whole run, so none of them can say *at which
degree* the matrices became unaffordable or whether the work there carried new information.
`F4Options::profile_degrees` breaks the same work out by the lcm degree its batch was selected at:

```rust
use zeebra::{fields::Zp2147483647, grobner::{benchmark_systems::katsura, f4_with_options, F4Options},
             MonomialOrder};

let options = F4Options { profile_degrees: true, ..F4Options::default() };
let (_basis, statistics) = f4_with_options(
    &katsura::<5, Zp2147483647>(),
    MonomialOrder::GradedReverseLexicographic,
    &options,
).unwrap();

for degree in statistics.degrees.iter() {
    // Pair rows that added rank, against pair rows that added none.
    let _useful = degree.candidate_rank_contribution;
    let _wasted = degree.dependent_candidate_rows;
}

// Where the computation was largest, and how redundant its rows were overall.
let (_degree, _peak_entries) = statistics.degrees.peak_degree().unwrap();
assert!(statistics.dependent_row_fraction() <= 1.0);
```

**The measure is rank attribution, not zero-row counting.** A batch's rows are of two kinds: the
two halves of each critical pair, and the reducer multiples symbolic preprocessing adds so the
matrix can perform the reductions polynomial division would. Reducer rows have distinct leading
monomials by construction, so they are linearly independent and **none of them ever reduces to
zero** — every zero row is a dependent pair row, and a pair contributes two rows, so the zero-row
count is not a count of useless pairs in either direction. What is informative is how much rank the
pair rows added on top of the reducer block, which is `rank - reducer_rows`; that is exact and does
not depend on the order elimination took the rows in, because rank does not.

##### Mutants, and why they need no mechanism

A matrix built at degree `d` can produce a relation of degree *below* `d` — information arriving
earlier than the schedule expected. `F4Statistics` counts them (`mutant_elements`,
`batches_with_mutants`, `max_mutant_degree_gap`) and, separately, counts what the engine does next:
`degree_regressions` is batches whose selection degree was below the previous batch's, and
`regressions_after_mutants` attributes those that immediately followed a batch which produced one.

The two are kept apart because a regression can also follow an ordinary batch: a new element of the
batch's own degree can pair low with an old one. Without the attribution the mechanism could not be
credited with anything.

The reason no mutant *mode* exists is structural. `PairQueue::select_batch` takes the pairs of the
**lowest pending degree**, so a relation that creates a pair below the current degree is selected at
the very next batch, ahead of any remaining pair of the current degree — immediate priority, with
nothing asked for. That is asserted on a live queue, not inferred from the selection code. See
[`docs/research/mutants.md`](docs/research/mutants.md) for the measurement and for what the
auxiliary-basis form of the idea would require.

Two further quantities are kept apart deliberately:

| Figure | What it is |
|---|---|
| `max_pair_degree` | the highest lcm degree any batch was *selected* at |
| `max_monomial_degree` | the highest degree any monomial reached as a matrix *column* |

The second is in general larger, because reducer multiples carry monomials above the lcm that
produced them. **Neither is the solving degree or the degree of regularity**, which are properties
of the ideal rather than of a run.

`profile_degrees` is off by default for the same reason `measure_stages` is: the shipping path
should contain no profiling. When it is on, it costs a map insertion per batch and one scan of each
matrix's column vector — per batch, not per row. The rank attribution itself is free either way,
since it is arithmetic on counters the elimination already returns. A profiled run returns exactly
the basis an unprofiled one does, which is asserted over the whole correctness corpus.

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
| `schedule` | `PairSchedule::{DegreeThenLcm, SmallMultiplierDegree, LargeMultiplierDegree, SmallMultiplierMonomial, LargeMultiplierMonomial}` | in what order the pending pairs of one degree are taken. Not a criterion — it discards nothing |
| `hilbert` | `HilbertSelection::{Off, Observe, CertifiedLimited, Deferred}` | whether a Hilbert prediction caps how many pairs a degree contributes to one batch. Not a criterion either |
| `certify` | `bool` | whether the returned basis is checked independently before being returned |
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

##### Pair order, which is not a criterion

`PairSchedule` decides which of the pending pairs *at the lowest available degree* is taken first.
The distinction from `PairCriteria` is the whole of its safety argument: a criterion is a theorem
that a pair need not be reduced at all, whereas a schedule only reorders pairs that will all be
reduced. Nothing leaves the queue unprocessed, so every schedule returns the identical basis — which
is asserted over the correctness corpus, under every monomial order and every criterion combination.

The lcm degree stays primary under every schedule. That is not a preference: a batch is formed from
the pairs of one degree, and F4's termination argument is stated in ascending degree.

A pair's two matrix rows are `(lcm / LM g_i) * g_i` and `(lcm / LM g_j) * g_j`. A larger shift moves
a polynomial further up, so more of its monomials are reducible, so symbolic preprocessing adds more
reducer rows — which is why preferring small multipliers is worth trying, given that scaffolding is
40%–99% of all rows. Each `Large…` variant is the control for its `Small…` counterpart: if
small-multiplier-first narrows the matrix then large-multiplier-first should widen it, and a
heuristic that beats the baseline in both directions is measuring run-to-run noise.

**The degree and monomial variants are different strategies, and only the second is the published
one.** Sakata–Takagi rank on the larger then the smaller multiplier *under the monomial order*;
comparing the multipliers' degrees is strictly coarser, and `x^2` against `y^2` is the smallest case
where they part company — equal degree, distinct under grevlex. Measured, they behave differently:
the degree comparator cuts row operations and widens the matrix, while the monomial comparator is
the best schedule on every structural counter on the two largest instances (7%–9.5% less peak
memory, up to 14.5% fewer row operations) with a control that is the *worst* on five of six, by up
to 1.75x. Neither clears the threshold to become a default. See
[`docs/research/pair-scheduling.md`](docs/research/pair-scheduling.md) §2.

A monomial-comparing schedule is the one thing in `PairQueue` that needs a `MonomialOrder`, so
`PairQueue::scheduled` refuses one and `scheduled_in` takes the order — a silent default there would
rank under the wrong order and look like a measurement.

**A schedule is never inert, even with no batch cap.** It is tempting to think it is: without
`max_pairs_per_batch` the batch is every pending pair of its degree whatever the order, so the batch
sets, the row sets, the row spaces, the pivot columns, and therefore the leading monomials of the
new basis elements all agree — `batches` and `pairs_reduced` come out equal, and are asserted to.
But row echelon form depends on the order the rows are taken in, so the candidates' *tails* differ,
and a different tail is a different set of monomials for the next batch to cover. On katsura-5
grevlex the widest matrix is 146 columns under `DegreeThenLcm` and 166 under `SmallMultiplier`, with
every pair and batch count identical. So a schedule has to be measured end to end.

`f4_schedule` does, and measures ordering and batch sizing **separately** — combining a new sort
with a new cap and attributing the whole difference to the sort is the easiest way to get a wrong
answer here. See [`docs/research/pair-scheduling.md`](docs/research/pair-scheduling.md) for the
tables and what they decided.

##### A Hilbert-driven cap, and why it cannot be a criterion

`HilbertSelection` uses the prediction above to decide how many pairs a degree is worth. The
quantity is

```text
N_d = (predicted dim I_d) − dim (current leading-term ideal)_d
```

— an upper bound on how many new leading monomials degree `d` can still produce. The second term is
**exact**, computed from the monomials in hand; the first is the prediction, so `N_d` inherits its
error. On Fukuoka type III `n=10`'s top forms the quota is 20, 65, 20 at degrees 2, 3, 4, and the
measured minimal-generator counts are 20, 65, 20.

**Neither limiting mode discards a pair**, which is what lets the modes be offered at all given that
the prediction is wrong on exactly the systems this is for:

- `CertifiedLimited { slack }` caps the *batch* at `N_d + slack`. The pairs it does not take stay
  **pending**, and the lcm degree is primary under every schedule, so they are the next thing
  selected. A wrong `N_d` costs batches, never the answer.
- `Deferred { slack }` moves the rest of the degree out of the pending set and goes on to the next
  degree. Those pairs are promoted back before the loop can end — its termination test counts them
  as work — they stay visible to Gebauer–Möller while deferred, and they are **not** recorded as
  processed, so the chain criterion cannot use one as a witness. It is a decision about *when*, not
  *whether*.

`Observe` computes the prediction and records how it compared, changing nothing; a run under it is
bit-identical to one under `Off`, which is asserted.

`certify` checks the result independently rather than inferring it from the strategy having run:
every input generator reduces to zero modulo the basis, Buchberger's criterion holds, and the basis
is reduced. **What it cannot check is the reverse containment** — an ideal strictly larger than the
input's has every generator reducing to zero in it. The sharpest case is `I = <x²>` against
`G = {x}`: `x²` reduces to zero modulo `x`, a one-element basis has no S-polynomial, and `x` is
monic and reduced, yet `<x²> ≠ <x>`.

So containment in the input ideal is a **precondition carried by the API, not a measurement**. The
report records a `Provenance`, and the two entry points differ only in what they assert about where
the basis came from:

| entry point | provenance | `checks_passed()` | `is_complete()` |
| --- | --- | --- | --- |
| `certify_f4_output` | `F4Output` | the three checks | the three checks |
| `certify_submitted_basis` | `Submitted` | the three checks | **always false** |

`is_complete` is the only honest conclusion of the pair, and it is the one the solver uses.
`certify_f4_output` is sound because every F4 matrix row is a monomial multiple of a current basis
element, so the output cannot leave the input ideal — and its sole call site in this crate is F4's
own return path. Anything else goes through `certify_submitted_basis`, where passing all three
checks yields `checks_passed()` and a `first_failure()` naming the containment that was not
established. The gap and the provenance's effect are each recorded as their own test rather than
left to be discovered.

Certification is `|G|²/2` normal forms, so it is quadratic in the basis and not cheap.
`F4Statistics::certification` reports its own cost separately from the total **because that is the
comparison that decides anything**: a strategy that skips work has to be judged on its cost
including the check that establishes the result, and a saving the check erases is not a saving.

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

The sweep's F4 options are configurable through `SweepOptions::f4`, the analogue of the `fglm`
field one level up: it is how a workstream points the external oracle at a strategy under
development rather than at the default. M22 uses it to check each of its configurations —
`SmallMultiplierDegree`, `SmallMultiplierMonomial`, `Observe`, `CertifiedLimited`, `Deferred`,
`certify`, and three together — against Singular on random systems over six characteristics, which
is stronger than composing "strategy equals baseline on a fixed corpus" with "baseline agrees with
Singular".

The configuration has to reach the comparison for any of that to be true, and that is the
distinction between two pairs of entry points:

| entry point | source basis computed with |
| --- | --- |
| `verify_case`, `verify_recorded` | `F4Options::default()` |
| `verify_case_with`, `verify_recorded_with` | the caller's `F4Options` |

The `_with` forms are what the sweep calls. An earlier version of the harness took the
configuration, used it for the border query, and then compared a *default-configuration* basis
against the oracle — so every configuration agreed by construction and the sweep was evidence about
the default alone. Two tests now hold the plumbing in place: one runs a configuration F4 cannot
finish under and requires the comparison to fail, and one perturbs an oracle basis element below
its leading term and requires rejection under every configuration. The fixtures also give the
strategy-versus-oracle check with no Singular present, since a fixture is a recorded Singular
answer:

```text
cargo test --lib agrees_with_the_recorded_oracle    # one test per configuration
```

`grobner::solve` still uses `buchberger`. The sparse linear algebra F4 is built on is reusable on
its own, as `linalg::sparse`, with the dense representations as `linalg::dense`;
`linalg::echelon` is the backend-selecting interface over both.

### Hilbert functions

`grobner::hilbert` computes the Hilbert function of a monomial ideal exactly, and the semiregular
prediction for a sequence of given degrees, and compares them. It is **diagnostic**: nothing in the
crate discards work on the strength of a prediction.

```rust
use zeebra::{fields::Zp2147483647, grobner::{benchmark_systems::katsura, f4,
             hilbert::{HilbertComparison, HilbertSeries}}, MonomialOrder};

let order = MonomialOrder::GradedReverseLexicographic;
let basis = f4(&katsura::<5, Zp2147483647>(), order).unwrap();

// Exact, from the computed basis's leading-term ideal.
let series = HilbertSeries::of_basis(&basis, order).unwrap();
assert_eq!(series.values(5).unwrap(), vec![1, 4, 6, 4, 1, 0]);

// Against the model for the generators' degrees: (1, 2, 2, 2, 2).
let comparison = HilbertComparison::new(&basis, order, &[1, 2, 2, 2, 2], 8).unwrap();
assert_eq!(comparison.first_disagreement, None);     // katsura-5 is "generic enough"
assert_eq!(comparison.predicted_degree_of_regularity, Some(5));
```

The exact side is a closed form, not an enumeration: counting the degree-8 monomials outside a
leading-term ideal in twenty variables is 2.7 million divisibility sweeps, and the same count at
degree 12 is 141 million. Instead the series is built as `numerator(z) / (1 − z)^n` by the standard
recursion on `0 → R/(L:p) → R/L → R/(L+<p>) → 0`.

Two budgets bound it, for two different resources. `DEFAULT_NODE_BUDGET` bounds the recursion, which
is exponential in the worst case. `DEFAULT_COEFFICIENT_BUDGET` bounds any one series' length,
because a numerator is one plus the summed generator degrees and a monomial's exponents are `u32` —
so `<x^100000000>` is representable and its honest numerator is 1.6 GB. **F4's matrix budgets do not
cover this**, and under `HilbertSelection` it runs before the first matrix is built. Either crossing
makes the prediction unavailable rather than killing the process: the count lands in
`HilbertCounts::predictions_unavailable` and the computation proceeds as ordinary F4.
The result is cross-checked two ways: against direct enumeration on small ideals, and by summing it
to `dim_F R/I` and comparing with the standard monomials `QuotientBasis` enumerates independently.

**The prediction is a prediction.** `Π(1 − z^{d_i}) / (1 − z)^n` is exact for a regular sequence,
conjectural for a generic overdetermined one, and has no standing on a structured system. Measured
on this repository's corpus it is **exact at every degree** on random homogeneous quadratics and on
the Fukuoka type III top forms, and wrong on every deliberately structured system — and the *sign*
of the error is what matters. Negative error (predicted below observed) overestimates the ideal, so
a selection cap built on it is too large: wasteful, never incomplete. Positive error is the
dangerous direction, and it is the direction the **inhomogeneous** systems fail in. On the published
Fukuoka type III `n=10` instance the model says degree 4 has nothing left, and F4 finds 85 of its
168 basis elements there. See
[`docs/research/hilbert-functions.md`](docs/research/hilbert-functions.md).

Inhomogeneous input has no graded Hilbert function, and the module does not pretend otherwise:
`hilbert::top_forms` gives each generator's highest-degree homogeneous component, which is the
object the MQ literature's semiregularity assumption is about and is a *different ideal* — of
`x^2 + y` it is `x^2`, whose variety is a line where the original's is a parabola.

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

## Permutation Polynomials
An arithmetization-friendly hash is built from a **power permutation**: Poseidon's S-box is
`x -> x^d`, and that map is a bijection of GF(q) exactly when `gcd(d, q - 1) = 1` — it fixes zero,
and on the multiplicative group, which is cyclic of order `q - 1`, raising to the `d`th power is
injective precisely when `d` is invertible modulo the group order. That inverse is the exponent of
the **compositional inverse**, since `(x^d)^e = x^{de} = x` when `de = 1 (mod q - 1)`. The test, the
enumeration of admissible exponents, and the inverse map are therefore all one piece of arithmetic
modulo `q - 1`.

```rust
use zeebra::{
    fields::{BabyBear, KoalaBear},
    inverse_exponent, is_permutation_exponent, permutation_exponents, FiniteField, KnownOrder,
    PowerPermutation,
};

// KoalaBear, the field the 2026 Poseidon challenges use: p - 1 = 2^24 * 127, which 3 does not
// divide, so the challenge's `alpha = 3` is admissible.
let q = KoalaBear::order_u128().unwrap();
assert!(is_permutation_exponent(3, q));
assert_eq!(inverse_exponent(3, q), Some(1420470955));

// The S-box, and the map an attacker inverts.
let sbox = PowerPermutation::<KoalaBear>::new(3).unwrap();
let x = KoalaBear::new(12345);
assert_eq!(sbox.invert(&sbox.apply(&x)), x);
assert_eq!(sbox.inverse().apply(&x), sbox.invert(&x));

// BabyBear factors differently -- p - 1 = 2^27 * 3 * 5 -- so the cube map is not a permutation
// there, and the smallest S-box exponent above the identity is 7.
let q = BabyBear::order_u128().unwrap();
assert!(!is_permutation_exponent(3, q));
assert_eq!(permutation_exponents(q).find(|&d| d > 1), Some(7));
```

`permutation_exponents` is lazy and yields one representative per distinct map — the admissible
residues in `1..=q-2` — which over a 31-bit field is around `2^31` items, so a caller after the
small exponents an S-box would use should stop early rather than collect.

Exponents are `u128` because `FiniteField::pow` takes a `u128` exponent, so a power map over a
field whose order exceeds that is not expressible in the first place. `PowerPermutation::new`
panics for such a field, and the 254- and 255-bit prime fields are out of reach here.

Deciding whether an *arbitrary* polynomial permutes GF(q) is a much larger subject — Hermite's
criterion, and families such as the Dickson polynomials — and none of it is implemented.
`is_permutation_polynomial` accordingly returns `Option<bool>` and answers only for the shapes whose
answer is immediate: a monomial `c x^d` with `c != 0`, which permutes iff `x^d` does, and an affine
`a x + b`, which permutes every field when `a != 0`. Anything else is `None`, and that is "not
decided here" rather than "not a permutation":

```rust
use zeebra::{fields::Zp7, is_permutation_polynomial, FiniteField, UnivariatePolynomial};

let monomial = |d: usize, c: u64| {
    let mut coefficients = vec![Zp7::new(0); d + 1];
    coefficients[d] = Zp7::new(c);
    UnivariatePolynomial::<Zp7>::new(&coefficients)
};

// gcd(5, 6) = 1, and the leading coefficient only composes a bijection with a bijection.
assert_eq!(is_permutation_polynomial(&monomial(5, 3)), Some(true));
// gcd(3, 6) = 3.
assert_eq!(is_permutation_polynomial(&monomial(3, 1)), Some(false));

// x^3 + x happens to permute GF(7), but establishing that is not in scope.
let f = UnivariatePolynomial::<Zp7>::new(&[Zp7::new(0), Zp7::new(1), Zp7::new(0), Zp7::new(1)]);
assert_eq!(is_permutation_polynomial(&f), None);
```

This changes nothing about `grobner::research::poseidon`, whose `alpha` stays what each challenge
specifies: a different exponent is a different cryptographic problem, not a variation on the same
one. What these utilities are for is a sweep that varies `alpha` deliberately and measures what the
solving degree does.

## Why You *Shouldn’t* Use Zeebra
I wrote Zeebra as an educational exercise. It is not yet complete or mature. It is not necessarily correct. For something more production-ready, please consider:

- **[arkworks-rs/algebra](https://github.com/arkworks-rs/algebra/tree/master)** - Algebraic structures and operations for zkSNARKs
- **[dimforge/nalgebra](https://github.com/dimforge/nalgebra)** - Linear Algebra library for the Rust programming language
- **[tspiteri/rug](https://gitlab.com/tspiteri/rug)** - Arbitrary-precision numbers
- **[axect/peroxide](https://github.com/Axect/Peroxide)** - Linear algebra library for machine learning
