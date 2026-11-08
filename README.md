
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
- [x] That oracle over an extension field: a differential case names a field rather than a
      characteristic, and the irreducible polynomial the two sides reduce by is asserted to agree
      rather than conventionally shared
- [x] Batched border reduction and adaptive operator storage: 14x on katsura-7's conversion
- [x] 254- and 255-bit prime fields, with F4, FGLM and solving over them end to end
- [x] Two-adic roots of unity without factoring `q - 1`, so the NTT runs over the wide fields
- [x] Batch inversion by Montgomery's trick: the inverse NTT now costs what the forward one does
- [x] A frozen registry of public cryptanalysis challenges, and a scoreboard that refuses to
      compare two different problems
- [x] A verified CICO witness at Poseidon-31's official state width `t = 16`, for a registered
      reduced-round instance
- [x] Graeffe-transform root finding: one root at degree `3^13` over KoalaBear in 3.1 s, against an
      extrapolated 57 hours for the quadratic finder
- [x] Lenstra's elliptic curve method, with an explicit effort budget that can report the cofactors
      it could not split
- [x] The resultant route's Sylvester determinants in parallel: 92–95% efficiency out to 32 cores,
      the four-round CICO row from 49.7 s to 2.16 s, with the concurrency recorded on the
      scoreboard and a cross-concurrency comparison refused rather than quoted
- [x] The whole solving pipeline in characteristic two, over GF(2) and GF(2^8), and field equations
      `x^q - x` that make a quotient dimension count base-field points
- [x] Text input and exhaustive enumeration over an extension field, on a settled split between the
      integer embedding `FiniteField::new` and the element index `KnownOrder::element_at`
- [x] A contract for driving external Gröbner engines as subprocesses, which separates "this tool
      cannot represent the input" from "this tool was slower", and refuses to quote a ratio against
      a comparand that could not accept the problem
- [x] Multivariate multiplication that collects as it multiplies, so the live set is bounded by the
      product's size and not by the term-product count: the six-round symbolic build from 57.0 GB
      peak resident to 0.32 GB, 179x, for byte-identical output
- [x] That dense accumulator generalized past two variables, which turned out to pay: 1.3x–5.4x
      over the hashing route at three, four and five variables and 8.4x on a trivariate pair dense
      in two variables and linear in the third, with the box-versus-simplex crossover measured
      rather than argued — and one shape where generalizing the layout *loses*, found the same way
- [x] Multivariate `Add`, `Sub` and `scale` collecting into an operand's own map, so a sum that
      cancels to one term out of 11 476 a side allocates nothing at all where materializing held
      594 KB, and an owned accumulator grows in place
- [x] A cross-library corpus of six families whose ideal equivalence is checked before any timing
      is published, with the Katsura indexing and affine-versus-homogenized Cyclic conventions
      resolved against msolve's own distributed input files — now at **two** reference
      characteristics, `2^31 − 1` and `GF(32003)`, each rung frozen at each, because a rung at
      another prime is another ideal and not the same one under a parameter
- [x] The ladder to `katsura-11` and `cyclic-10`, with the quotient dimension **asserted** per rung
      against the published record rather than merely reported: `2^(N−1)` exact at eight consecutive
      Katsura rungs, 70/156/**924** for Cyclic against Björck–Fröberg and Backelin–Fröberg, and the
      cyclic dimension class from Backelin's squarefree criterion — and a **measured ceiling** at
      `cyclic-9`, set by the F4 basis crossing its live-entry budget, which is a bound that crosses
      at the same counter on any machine rather than a wall clock
- [x] Symbolic preprocessing's monomial queue deduplicated on push rather than on pop:
      `fukuoka-mq-III-n20-seed0`'s peak RSS 9.1x lower and its runtime 10% shorter, with the
      symbolic closure checked unchanged batch by batch rather than inferred from the basis
- [x] The published 2 400x Anemoi conversion gap attributed by measuring the same system at three
      characteristics: this crate's conversion/basis ratio is flat to 12% across a 47-bit range of
      primes where the reference's moves 7.3x, so the gap is the reference's field arithmetic — and
      msolve on this machine is 35x faster than either
- [x] Anemoi CICO at six rounds, `D = 15 625`: a witness verified through the permutation in
      1.180 h, reproducing a published 11 775 s conversion, with the pre-recorded cost model landing
      within 4% on the conversion and 1.5% on the operator count
- [x] The Sylvester determinant's cost law measured over five matrix orders instead of two: cubic to
      within the measurement above L2 — `2.9953 ± 0.0285`, worst residual 3.7% — and no cache
      cliff, since order 4 374's 153 MB matrix exceeds L3 and still fits the law. The budget guard
      takes the larger of the fitted and cubic laws, because a model that under-predicts authorizes
      a run nobody costed
- [x] A cost-and-resource-model register in which prediction error is *derived* from the predicted
      and measured columns rather than authored, every figure labelled measured / fitted / predicted
      / extrapolated, and rows append-only — so a re-measurement sits beside the estimate it
      corrects instead of erasing how wrong it was
- [x] Two measured same-machine losses in different subsystems, which is what the comparison was
      for: order conversion ~30x behind msolve, and the basis stage 4.11x behind Singular on random
      MQ — the corpus family closest in shape to a cryptanalytic system
- [x] A competitive board that refuses a ratio against a comparand's own startup floor, measured at
      35.91 ms for Singular, 10.29 ms for msolve and 10.36 ms for Sagebrush from the board's own
      rows — and that states its own roster and counts what its gates excluded, so a run that
      silently lost an engine cannot read as a run that never had it
- [x] The board populated to **five libraries**: 180 measured records over the whole corpus ladder
      x both tasks x Zeebra, Singular 4.4.1, msolve 0.11.0, Groebner.jl 0.10.11 and Sagebrush, one
      row per process under the benchmark lock, all four externals agreeing term-for-term before any
      timing was taken. Of 116 pairs, 89 are disqualified by a startup floor and 19 are ones a
      conclusion may rest on: **13 losses, 1 win**. On random MQ at 10 variables this crate is the
      **slowest of the five** — 348x behind Groebner.jl, 119x behind msolve, 87x behind Sagebrush,
      4.1x behind Singular, every engine agreeing on the answer. And the classical families turn out
      to decide something after all: 15.9x behind Groebner.jl on katsura-7 and 6.2x on cyclic-6,
      where against Singular alone they could decide nothing because Singular was starting up
      through all of it
- [x] Multivariate composition: `x_i -> g_i(x_i)` for univariate `g_i`, and the general form that
      substitutes a polynomial in all `N` variables for each one — so a permutation round can be
      written the way it is defined, with the substituted powers memoized and formed by repeated
      squaring
- [x] Multivariate GCD by recursive primitive PRS, with content, primitive part, the formal partial
      derivative and squarefree decomposition on top of it — the GCD's defining property checked by
      exhaustive enumeration over a small ring rather than against a reference implementation
- [x] Squarefree decomposition in characteristic `p`, where the derivative is blind to every
      multiplicity `p` divides: the invisible part is a `p`-th power, so its root is taken exactly
      and recursed on, and the zero polynomial is the only refusal left
- [x] Collins' subresultant PRS beside the primitive one, which becomes the reference: one exact
      division per Euclidean step rather than a recursive content GCD, with the two routes asserted
      equal exhaustively and the saving stated as an operation count rather than a timing
- [x] Reed-Solomon codes over an FFT domain: encoding, erasure recovery, and a Euclidean
      decoder that verifies its correction rather than returning the nearest codeword

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

The shell tooling under `scripts/agent/` and `tools/` is invisible to every Rust job, so CI's
`agent-scripts` job checks it separately. The shellcheck arguments are globs rather than a file
list, so a script added under either directory is checked without anyone remembering to add it:

```sh
shellcheck -S warning scripts/agent/*.sh scripts/agent/test/*.sh \
  tools/*.sh tools/test/*.sh tools/external/*.sh tools/external/smoke/*.sh
bash scripts/agent/test/zb-claim-test.sh
bash tools/test/rss-guard-test.sh
bash tools/test/merge-base-age-test.sh
bash tools/test/benchlock-test.sh
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

**A process per test is also why CI cannot see a test that mutates process-wide state.** Under
`cargo test` the whole suite is threads of one process, so a `std::env::set_var` anywhere races
every concurrent `getenv` and leaks its value into whatever else happens to be reading the
environment; under nextest each test owns its environment and the same code is green. That
asymmetry made `main` red locally and green in CI for the length of #418 — two adjacent tests, each
setting its own variable, each believing itself the sole writer, and a lookup that returns the
first variable set out of a list. `clippy.toml` therefore disallows `std::env::set_var`,
`remove_var` and `set_current_dir`, which puts the ban on the one check that does run in CI. Code
that needs to vary an environment-derived value takes it as a parameter instead — see
`SagebrushSolver`'s switch probe.

CI resolves its toolchain to `stable`, which moves. A clippy run that is clean on an older stable
is therefore **not** evidence that CI is clean — new lints arrive with new releases, and one did
during this project's history. `rustup update stable` before trusting a clean run, or name the
version explicitly:

```sh
rustup run stable cargo clippy --all-targets --all-features -- -D warnings
```

A test of a property that should hold over *every* field is written once and expanded per field by
`for_each_field!`, or by `for_each_small_field!` where the body enumerates the field. Each
expansion is named after its field, so a failure says which one:

```text
macros::field_types::tests::the_ring_laws_hold::gf13_pow_4 ... ok
macros::field_types::tests::the_ring_laws_hold::bn254_fr ... ok
```

The alternative was a trait law tested for whichever field the author had in mind, which is how the
coverage became uneven in the first place.

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

The debug run checks more than the release one in a second way. F4 validates its whole engine state
once per batch under `cfg(debug_assertions)`: `MonicBasis::check` recomputes every element's leading
monomial, monicity and term ordering and compares them to what is stored, and `PairQueue::check`
recomputes each pending and deferred pair's lcm, degree and multipliers from the leading monomials
it names, confirms the live count against the heap, and confirms the pending and deferred sets are
disjoint. A failure names the field and the index. None of it is compiled in release, so **a
`--release` or `--profile ci-release` run does not perform these checks** — which is a reason to run
the debug suite and not only the fast one.

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

The library and the `zeebra-differential` binary are declared `bench = false`, the mirror of the
`test = false` above. `bench` also defaults to true, so this command used to select ten targets
rather than eight: the lib was built as a bench target and `--test` ran the whole unit suite here,
in one process under the built-in harness, duplicating the nextest jobs with worse isolation. That
broke `util::peak_memory`, whose subject is `VmHWM` — a process-wide high-water mark that, in a
process shared with ~1400 other tests, sits far enough above live RSS that a 32 MB ballast cannot
raise it. The binary has no tests at all, so its entry was a whole-crate link for nothing.
`bench = false` does not affect `cargo test`, which still runs both.

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

### Testing the merged result

A pull-request run **does** test a merged result, which is worth stating because the obvious
assumption is that it does not. `actions/checkout` on a `pull_request` event resolves
`refs/pull/N/merge` and logs `HEAD is now at <sha> Merge <head> into <base>`; the suite runs on that
merge commit, not on the branch tip. What nothing recomputes is the merge when `<base>` advances. A
green check therefore means "this change is consistent with `main` **as it was when this run was
queued**", and with several agents landing work in the same hour the gap between that and "as
`main` will be" is where a semantic conflict lives.

One landed. #324 took `corpus::ladder()` from 7 rungs to 19; #311 added a test that resolved each
rung through an exhaustive match over the 7 that existed when it was written. Each was green. The
merge of both panicked, and git saw no textual conflict because there was none. It then stayed
unnoticed for about forty minutes with every check green, because the test's comparand — msolve —
is absent on the runner, so the test returned early and passed. #338 fixed the instance and made
that early return say `NOT CHECKED` on stderr; #339 is about the class.

GitHub's **"Require branches to be up to date"** closes the gap exactly: it re-runs the suite
against the new base before each merge. It is not used here, and the cost is the reason rather than
an assertion. The release job is **806 s mean over the last 25 successful runs**, worst case 983 s,
and it is the critical path — the debug job is 318 s. A serialized merge queue therefore admits
**4.5 merges an hour**. Against that, the week to 2026-11-07 merged 155 pull requests, **58 of them
on 2026-11-06 alone**, peaking at **14 in one hour**; the median gap between consecutive merges was
686 s, and **59 % of consecutive merges were less than one release job apart**. Re-running before
each of that day's 58 merges is **13.0 hours of CI inside a 24-hour day**. The setting would not
have slowed that day down, it would have made it impossible.

What is used instead is two cheaper things, neither of which subsumes the gate:

- **A staleness notice on every pull request.** `tools/merge-base-age.sh` compares the base this
  run's merge was computed from against the current tip of the base branch, and reports which files
  the pull request changes *also* changed in that gap. The overlap is the signal; a bare
  behind-count is nonzero on nearly every pull request here and would be ignored within a day. The
  `merge-staleness` job takes seconds, needs no toolchain, and is **advisory by construction** — an
  overlapping result is a workflow warning and the job still passes, because a required check would
  be the gate again with extra steps. A failed *read* does fail the job: a staleness check that
  could not read the repository must not be reported as a clean one.

  ```sh
  tools/merge-base-age.sh <tested-base-sha> <head-sha> origin/main
  # 0 current   1 behind   3 behind and overlapping   2 a git read failed   64 usage
  ```

- **A daily run on `main`.** Push runs on `main` already test the merged result within minutes of a
  merge, so they catch the combination after the fact. What they do not catch is a red `main` that
  nobody pushes to afterwards, or drift from resolving the toolchain to `stable`, which moves and
  has delivered a new clippy lint mid-project before. The `schedule` trigger bounds both to a day,
  for one run of **20.7 to 25.9 job-minutes** — measured across the last six successful push runs
  on `main`, which have the same job set a scheduled run gets.

Neither covers the second half of the failure, which is that CI skipped the broken test entirely.
Provisioning the external comparands in ordinary CI is deliberately not done — building GMP, MPFR,
FLINT and msolve on every run is the cost #308 was told not to add, and the ordinary CI path must
not come to depend on an external binary being present. Asserting that coverage is therefore a
**local pre-merge step**, on a machine where `tools/external/provision.sh` has already run:

```sh
ZEEBRA_REQUIRE_MSOLVE=1 cargo nextest run --profile ci --lib -E 'test(/^grobner::external::/)'
```

`ZEEBRA_REQUIRE_MSOLVE=1` turns an absent msolve from a silent early return into a failure, so the
command either exercises the comparand or says it could not. It is 246 tests in 30s once built —
a debug build is enough, because every msolve comparison runs on a corpus rung at or below seven
variables, which `DEFAULT_ORACLE_WIDTH_CEILING` is what bounds; `cyclic-7`, added in #424, is almost
all of those thirty seconds and the rungs above it print `NO ORACLE` rather than being run. So this
is still cheap to run before merging anything that changes the corpus, the challenge registry, or
either engine's side of the comparison. The test that #339 is named for lives here:
`grobner::external::msolve::tests`, driven from `corpus::ladder()`.

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
the baseline x86-64 level. Setting `RUSTFLAGS` to the **empty string** drops it too.

**This warning was not enough, so there are now two checks.** The trap cost #185 a crossover
constant and #231 a set of figures, both measured in shells that set `RUSTFLAGS="-D warnings"` or
`RUSTFLAGS=""` for unrelated reasons. Nothing in the output said so: a 4-byte Montgomery multiply
vectorizes and an 8-byte one does not, so only the narrow-field numbers moved and it looked like a
property of the kernel rather than of the build.

```sh
tools/vec_census.sh target/release/examples/multiplication_dispatch --require
```

counts vector multiplies in an artifact and exits nonzero when there are none — 65 in a build with
the floor, 0 without it. And every measurement example prints `util::isa_floor()` in its header, so
a figure and the ISA it was taken at are never separated:

```text
ISA: x86-64-v3 or better (AVX2)
ISA: baseline x86-64, NO AVX2 — RUSTFLAGS probably displaced the ISA floor
```

Neither is a test asserting AVX2, because the floor is deliberately not inherited by consumers and
such a test would fail for every downstream build.

**A consumer of this crate inherits none of this.** `.cargo/config.toml` applies only when cargo
is invoked with this directory as the working directory, and profile settings come from the
workspace being built. A downstream build gets whatever that build configures, so a dependent
crate wanting these settings must set them itself.

#### An out-of-tree measurement harness

That last paragraph is also **a third way to lose the ISA floor, and the only one with no mistake
to avoid.** A benchmark harness in its own crate outside this worktree, depending on `zeebra` by
path, inherits neither the `rustflags` nor the profile — cargo resolves config from the invocation
directory upward, and `[profile.release]` comes from the crate being built. `RUSTFLAGS` need never
be set. The build succeeds, the tests pass, and the numbers are smooth and self-consistent.

It happened, and because both runs were kept the cost is measured rather than estimated
(#352, [`docs/research/structured-sylvester.md`](docs/research/structured-sylvester.md) §5.5.1):

| build | order-1 458 LU | order-1 458 Euclid | ratio |
|---|---:|---:|---:|
| no `target-cpu`, no LTO | 6.360 s | 3.295 ms | 1 930x |
| `x86-64-v3`, fat LTO, cgu 1 | **2.272 s** | **1.343 ms** | **1 692x** |
| what the flags were worth | **2.80x** | **2.45x** | — |

**2.80x on the determinant**, and 12 % on the ratio — small enough to look plausible, which is the
dangerous size. Nothing in the toolchain objected. What caught it was comparing the baseline column
against an independently measured figure for the same quantity: #312 puts the order-1 458
single-worker determinant at 2.404 s, the first harness said 6.360 s, and 2.6x apart is not a noise
story.

So, for a harness built anywhere but here, in order of what it buys:

1. **State the comparison.** A harness that measures a quantity something else in this repository
   already measures should print both and name the discrepancy. That is what found this, and it is
   the only item on this list that also catches the mistakes nobody has thought of yet.

2. **Print the ISA floor from inside the harness.** `zeebra::util::isa_floor()` is compiled as part
   of *your* build, so it reports your flags and not this repository's — one line in the header and
   a silent miss becomes a visible one:

   ```rust
   println!("ISA: {}", zeebra::util::isa_floor());
   ```

   `zeebra::util::has_isa_floor()` is the predicate, for a harness that would rather refuse to
   record a figure than label it.

3. **Pass the build configuration explicitly.** Either put the settings on the invocation —

   ```sh
   cargo build --release \
     --config 'target."cfg(target_arch = \"x86_64\")".rustflags = ["-C", "target-cpu=x86-64-v3"]' \
     --config 'profile.release.lto = "fat"' \
     --config 'profile.release.codegen-units = 1'
   ```

   — or copy `.cargo/config.toml` into the harness crate **and** restate `[profile.release]` in its
   `Cargo.toml`. Copying the config file alone is not enough and is the trap inside the fix:
   profiles live in `Cargo.toml`, and this repository's `.cargo/config.toml` carries no `[profile]`
   section, so the copy brings the ISA floor and leaves `lto = "fat"` and `codegen-units = 1`
   behind.

   Verified on a throwaway out-of-tree crate, counting VEX-encoded instructions over SIMD registers
   in the resulting binary: **0** for a plain `cargo build --release`, **70** with
   `.cargo/config.toml` copied, **79** with all three settings passed by `--config`. The profile
   half is visible in `cargo build -v`: the `--config` route shows `-C lto=fat` and
   `codegen-units=1` on the rustc command line, and the copied-config route shows neither.

   One trap while checking any of this, which cost a figure here before it was noticed: if the
   environment sets `CARGO_TARGET_DIR` — this workstation's `~/projects/.cargo/config.toml` does,
   to a shared build cache — then `target/release/<name>` does not exist and `objdump` on it
   silently reports nothing, which reads as "no AVX2". Pass `--target-dir` explicitly, or resolve
   the path with `cargo metadata --format-version 1 --no-deps`, and confirm the file exists before
   believing a census of it.

Note that `tools/vec_census.sh` will not catch this for an arbitrary harness. Its signal is vector
*multiplies*, which only exist for an artifact exercising a **4-byte** field — a 32-bit Montgomery
reduction is 64-bit arithmetic LLVM can put in a lane and a 64-bit one is 128-bit arithmetic it
cannot — so it reports zero for an 8-byte-field harness whether the floor is there or not. A
general static probe is harder than it looks, and #385 records the measurements that killed one:
the AVX2 and BMI2 instructions in a baseline-built binary's explicitly dispatched
`#[target_feature]` kernels are indistinguishable, instruction by instruction, from those a real
`x86-64-v3` build emits.

#### No compiler cache, and why that is the measured choice

`.cargo/config.toml` sets `[build] rustc-wrapper = ""`, which **disables** any compiler cache
configured further up the directory tree — `sccache` typically. That is deliberate, and it is a
measurement rather than a preference. Three `cargo build --release --lib` runs into fresh output
directories with a warm `sccache`: **44 of 48 units hit and the wall clock did not move** — 83.1 s,
82.4 s, 79.4 s. The hits are all cheap leaf dependencies. The unit that matters is `zeebra` itself,
**79.2 s of the ~83 s** under fat LTO at one codegen unit, and it misses, because at least one
dependency rlib is not byte-reproducible across output directories and `sccache` hashes `--extern`
rlib *contents* — so every crate downstream of it gets a fresh key. This crate is also the wrong
shape for a compiler cache in the first place: one large crate whose cost is a single whole-crate
codegen, not many small crates compiled repeatedly.

The second cost is larger than the 4% saved. A compiler cache can only cache non-incremental
builds, so using one means `CARGO_INCREMENTAL=0`, and that is paid on every edit: `cargo check`
after a one-line change is **1.9 s** with incremental off against **0.7 s** with it on. Release and
bench builds are unaffected either way, since cargo disables incremental compilation under LTO.

Two things to know if a cache is enabled anyway:

- **The `RUSTC_WRAPPER` environment variable overrides this file.** Cargo takes the environment over
  config, so a shell that exports `RUSTC_WRAPPER=sccache` gets it regardless of what is written
  here. Prefix the command with `RUSTC_WRAPPER=""` in that case.
- **A stale cached `libzeebra` rlib does not look like a cache problem.** It surfaces as an example
  or binary failing to compile against `pub use` items that are plainly present in the source. The
  same symptom comes from sharing one `CARGO_TARGET_DIR` between two checkouts, which is why
  `tools/scoreboard.sh` forces a private target directory and an empty wrapper for anything
  measured.

### Measuring on a busy machine

`tools/benchlock.sh` runs one command at a time, machine-wide, and records that it did:

```sh
tools/benchlock.sh <owner-tag> <command> [args...]

tools/benchlock.sh agentD cargo run --release --example univariate_scaling -- koalabear
```

Two concurrent measurements on one box contend for shared cache and memory bandwidth, so a ratio
taken while something else ran is not a measurement of the change. The script takes an exclusive
`flock`, appends `QUEUED` / `START` / `END` lines with the owner tag and a timestamp to
`$HOME/.zeebra/benchlock.log` (override the directory with `ZEEBRA_BENCHLOCK_DIR`; it must be
outside every worktree), and exits with the command's status so a failing measurement fails the
caller. Two records whose `START`..`END` windows overlap were not taken under this protocol, and
the log is what says so — which is what makes figures taken weeks apart, such as the pre- and
post-#161 revisions in [`docs/research/graeffe-root-finding.md`](docs/research/graeffe-root-finding.md)
§4.4, comparable with each other.

The lock handles contention and nothing else. Also needed, per invocation:

- `CARGO_TARGET_DIR` inside the caller's own worktree and `RUSTC_WRAPPER=""`, as in
  `tools/scoreboard.sh`. The default target directory is keyed by package and profile rather than
  by checkout, so two worktrees overwrite each other's `libzeebra.rlib` and an example links
  against a library built from other source; the symptom is a missing export that is plainly
  present.
- A private scratch directory. Two callers' `tee run1.txt` collide, and a clobbered `tee` is a
  silently wrong figure rather than a crash.
- `timeout --signal=INT --kill-after=60s` on anything long, with a budget-killed run reported as a
  resource-limited result rather than as a measurement. A run left past its budget holds the lock
  against everyone else.
- A memory ceiling enforced by `tools/rss-guard.sh`, not by a hand-rolled `pgrep -f` loop. See
  below.
- **`setsid`, so the run survives its launcher.** See *Why a run ended* below.
- A build whose ISA floor actually survived. `.cargo/config.toml` is not inherited by a harness
  crate built outside this worktree, which is a third route to losing `-C target-cpu=x86-64-v3`
  with no `RUSTFLAGS` mistake to avoid (#352); `tools/benchlock.sh` lists it among the hazards the
  lock does not handle.

#### Why a run ended

An `END` line names its cause, and **`end=exited` rather than `status=0` is what says a measurement
completed**. The distinction is not decorative. A 1.5-hour Anemoi run was killed at 3 177 s of a
5 400 s budget when the agent harness stopped the background shell that had launched it — taking
`benchlock`, `timeout`, `taskset` and the binary with it, since all four were its descendants — and
the log recorded:

```text
2026-11-06T20:01:47-05:00  END  zb-m25-anemoi  pid=2761621  status=0  elapsed=3177s  ...
```

`status=0`, a plausible `elapsed`, and no resource limit anywhere near being crossed. From the
lock's side the measurement had finished; the only clue otherwise was an output file holding eleven
header lines and no stage table. That consumed 53 minutes of a serialized mutex with three other
agents queued behind it *while reporting success*, and it made every historical `END status=0`
retroactively ambiguous — which matters because the resource policy authorizes bounded runs on the
grounds that a budget stop is observable and attributable, and it is not, if a budget stop and an
unrelated kill read the same (#344).

So the cause is now explicit:

| field | meaning |
|---|---|
| `end=exited` | the command ran and returned on its own; `status=` is its own status |
| `end=budget` | status 124, GNU `timeout`'s convention — a resource-attributed stop |
| `end=signalled-child(NAME)` | the command itself died of a signal; `status=` is 128+n |
| `end=launcher-signal(NAME)` | **the lock itself was signalled.** `status=` is forced to 128+n however the command exited, and `child=` keeps the command's own status visible |
| `launcher=gone` | the run outlived the process that launched it |
| `end=aborted`, `route=trap` | the `END` came from the `EXIT` trap, so the lock never reached its own last line and never observed the command return. Never `end=exited`, and `status=` is 128 rather than 0 |

`end=launcher-signal` is the one that closes the incident, and the override is the point: in that
run the child reported **0**, because an intermediate `bash run.sh` with no `set -e` exited on its
own last command after the binary beneath it had died. No exit status reaching the lock could have
been trusted, so a signal to the lock now outranks whatever the command said.

Two cases leave no `END` at all, both honestly. A signal arriving while a caller is still
**queued** leaves a `QUEUED` line and nothing else, which is right: no `START` means no window was
opened, so nothing later can look like it overlapped. And `kill -9` cannot be trapped, so it leaves
a `START` with no `END` — an unterminated window, unhelpful but not a claim that anything finished,
and the one case no script can prevent. Verified by process-group kill:

```text
kill -TERM  ->  status=143 end=launcher-signal(TERM) child=143
kill -HUP   ->  status=129 end=launcher-signal(HUP)  child=129
kill -USR1  ->  status=138 end=launcher-signal(USR1) child=138
kill -KILL  ->  (no END line)
```

`launcher=gone` is a note and not a failure, deliberately — `setsid` reparents a run to init on
purpose, so overriding the status on it would fail the very discipline being recommended:

```sh
setsid nohup bash run.sh > log 2>&1 < /dev/null &
ps -o pid=,sid= -p "$!"   # a session id that differs from this shell's is the confirmation
```

The lock does **not** call `setsid` itself. A detached run that nobody can cancel is its own
hazard, and that trade is worse than the one it would fix; so the lock records what happened rather
than preventing it.

`tools/test/benchlock-test.sh` covers the classification and reproduces the incident end to end —
benchlock in its own session, a measured command whose wrapper swallows the kill and exits 0, and a
signal to the whole process group — asserting that the resulting `END` is not `status=0`. It runs
in CI's `agent-scripts` job, in a throwaway `ZEEBRA_BENCHLOCK_DIR`, so it never takes the real lock
or appends to the real log.

#### Enforcing a memory ceiling

```sh
tools/rss-guard.sh <comm> <id-substring> <ceiling-kb> [--poll <seconds>] [--once] [--wait <seconds>]
                   [--signal <name>] [--kill-pid <pid>] [--dry-run]

tools/rss-guard.sh anemoi_ladder anemoi17-cico-n6-fcico $((16 * 1024 * 1024)) --poll 10
```

`<comm>` is the binary's name as `/proc/<pid>/comm` spells it, truncated to 15 characters by the
kernel and by the script alike; `<id-substring>` is then confirmed against that pid's command line,
so a second concurrent run of the same binary on a different row is not watched. The mark read is
`VmHWM`, the high-water mark, so a peak that has already been released still counts.

**Do not find the process with `pgrep -f`.** A script created and run through a heredoc inside
`bash -c` — how agent sessions launch benchmark runs — has its entire text in the wrapper's
`/proc/<pid>/cmdline`, and `pgrep -f` matches the full command line, so it matches the wrapper on
its own payload. Observed live in #328 while one row was running and the next was still queued:
`pgrep -f` returned two `comm=bash` pids for the queued job and did not return the running binary
at all. The consequences were a monitor reporting queued work as running, and an RSS guard reading
a wrapper's ~4 MB high-water mark — which can never exceed a 16 GiB ceiling, so it silently never
fired and the run proceeded unsupervised while looking supervised.

Hence the exit statuses, which split three ways rather than two:

| status | meaning |
|---|---|
| 0 | watched to completion, the ceiling was never crossed |
| 3 | the ceiling was crossed and the signal was sent |
| 1 | **nothing matched — nothing was guarded.** Not a pass |
| 2 | a read of `/proc` failed |
| 64 | usage error, including a `<comm>` that names a wrapper (`bash`, `timeout`, `taskset`, …) |

Status 1 is the one worth the separate code: "watched and it was fine" and "watched nothing" are
the same output otherwise, and only the first is a guarded run. A guard started before its binary
waits `--wait` seconds (60 by default) for one to appear and then reports `NOT GUARDED` rather than
polling an empty process table forever.

When the launcher and the guard are in the same script, prefer neither form of matching: capture
the pid from `$!` and pass it with `--kill-pid`.

`tools/test/rss-guard-test.sh` covers the pure half against a synthetic `/proc` — including a case
where both wrappers' command lines contain the row id and only the binary is matched — and runs in
CI's `agent-scripts` job.

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
cargo bench --bench sparse_polynomial    # multivariate arithmetic, four arities
```

`sparse_polynomial`'s `mul_dense` arm is separate from `mul` because they are different shapes, not
just different sizes. `mul` draws monomials independently, which is sparse in the total-degree sense
at every size; `mul_dense` builds the dense total-degree simplex, which is what the symbolic
resultant build actually produces and what selects the specialised bivariate multiplication route.
An arm of only the first kind cannot catch a wrong dispatch predicate.

`sparse_linear_algebra` has three groups, and the differences between them matter. `sparse_linalg`
times sparse row echelon beside dense *reduced* row echelon, which performs a back-substitution
pass the sparse side never does; it is indicative of nothing about storage and is kept only for
continuity. `matched_echelon` runs the identical algorithm under each `linalg::echelon` backend on
identical matrices, and times densification and sparsification in their own benchmark, so the
comparison measures representation rather than algorithm or conversion. `sparse_rref` times
`linalg::sparse::reduced_row_echelon`, whose back-substitution pass neither of the others covers,
on two shapes that answer different questions: a random square matrix, which at low density fills
in until it is near-dense and leaves the pass nothing to skip, and a banded matrix, which stays
sparse throughout and is where skipping is worth anything.

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
cargo run --release --example f4_memory            # F4, memory attributed per structure
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
cargo run --release --example certification_criteria  # what they discard from a certification pass
cargo run --release --example certification_criteria -- list
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
cargo run --release --example univariate_scaling -- points=250,500,1000,2000   # lagrange only, exact counts
cargo run --release --example karatsuba_crossover  # Karatsuba against schoolbook, per field width
cargo run --release --example karatsuba_crossover -- bn254
cargo run --release --example multiplication_dispatch  # schoolbook vs Karatsuba vs transform, and the crossings
cargo run --release --example multiplication_dispatch -- koalabear max_log=17
cargo run --release --example multivariate_mul     # multivariate multiply: time and live heap per route
cargo run --release --example multivariate_mul -- chunk         # block size sensitivity
cargo run --release --example multivariate_mul -- max_degree=90 # stop short of the six-round size
cargo run --release --example graeffe_root         # Graeffe root finding, stage by stage, against `roots`
cargo run --release --example graeffe_root -- deflate   # all roots by deflation, #351
cargo run --release --example graeffe_root -- list
cargo run --release --example graeffe_root -- goldilocks degrees=256,1024,4096   # where the method does not pay
cargo run --release --example graeffe_cico         # the univariate CICO route, and the family economics
cargo run --release --example graeffe_cico -- --families 3000 --budget 25
cargo run --release --example graeffe_cico -- --help
cargo run --release --example batch_inversion      # batch inversion: routine, integration,
cargo run --release --example batch_inversion -- f4   # and the F4 headroom left alone
cargo run --release --example scoreboard           # registered problems, one record each, staged
tools/scoreboard.sh stable --write                 # the same, pinned, updating research/scoreboard
tools/scoreboard.sh ladder --write                 # the nine full-width t = 16 CICO rows
cargo run --release --example competitive          # render research/competitive/ from its history
cargo run --release --example competitive -- --write   # and update COMPETITIVE.md in place
cargo run --release --example competitive_sweep -- --list   # corpus x engines x tasks, exploratory
. tools/external/env.sh                            # REQUIRED FIRST, or the sweep sees one engine
tools/benchlock.sh runner cargo run --release --example competitive_sweep -- \
    --row katsura-6 --task reduced-grobner-basis --measure --write   # one measured row
tools/benchlock.sh runner cargo run --release --example competitive_sweep -- \
    --characteristic 32003 --row katsura-6 --task reduced-grobner-basis --measure --write
                                                   # the same rung at the corpus's other identity;
                                                   #   only a PUBLISHED characteristic is accepted
tools/benchlock.sh agentD cargo bench              # anything measured, under the exclusive lock
cargo run --release --example resultant_cico       # a resultant against F4 on the same slices
                                                   #   (two four-round rows, predicted sample count)
cargo run --release --example resultant_cico -- --concurrency 1,8,32   # the determinant scaling study
cargo run --release --example resultant_cico -- --row poseidon31-cico-t16-rf2-rp4 --build-only
cargo run --release --example resultant_cico -- --kernel euclidean --root-finder deflation \
    --row poseidon31-cico-t16-rf4-rp2 --max-samples 59050   # the six-round row, #367
cargo run --release --example determinant_sweep    # the Sylvester determinant cost law,
                                                   #   five matrix orders, fitted with residuals
cargo run --release --example determinant_sweep -- --cost-only   # what the sweep would cost
cargo run --release --example determinant_sweep -- --kernel euclidean   # the O(n^2) kernel
cargo run --release --example f4_profile -- mq     # the competitive MQ instance, per stage
cargo run --release --example f4_profile -- mq-instance   # that instance as canonical text
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
`F4Options::measure_stages`, which reads a clock four times per batch and is off by default. Two
modes take no configuration: `mq` is the digest-pinned `mq-random-10` stage split (#349), and
`mq-instance` prints that instance's canonical text — field, order, variables and generators, the
bytes the identity digest is taken over — so an external engine's own counters can be taken on the
same ideal and compared against these columns. `docs/research/groebner-jl-gap.md` is what that
comparison produced.

`f4_memory` is the same question for bytes rather than for time, and it exists because the answer
turned out not to be the matrix. It runs a tracking `#[global_allocator]` beside the solver's own
counters, measures each batch's symbolic preprocessing and matrix construction on the batches F4
really selected — including the batch that is **refused**, which no `F4Statistics` field describes —
and prints each named structure's share against the measured peak. `ZEEBRA_MAX_ENTRIES` and
`ZEEBRA_WALL_SECONDS` set the entry cap and `max_wall_time`, so a rung of the
`docs/research/f4-resource-scaling.md` ladder reproduces here with the attribution attached. Pass
`mq <instance>` for a registered MQ instance, whose files `tools/fetch-mq-challenge.sh` fetches.

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

`f4_schedule` is M22-A's measurement: every compiled critical-pair order on one table per
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
either. A last table divides each backend's time by the `row_operations` it reported, which is the
per-operation cost a change inside a row operation has to move, and states the pivot index's
storage at the instance's widest matrix. `-- list` names the instances; the largest are excluded by
default, because a dense representation of katsura-7 grevlex is 374 MB for a matrix holding 112k
entries.

`f4_selection` compares every reducer-selection policy and the cache against one common baseline,
on one line each: the closure size, the largest matrix, the peak live entries, the row operations,
the share of reducer multiples that had been needed before, and the stage times. The policies come
from `ReducerSelection::ALL`, so one added to the enum is measured without the program being
edited, and every row's basis is asserted equal to the first row's.
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
[`docs/MILESTONE-DEGREE-AWARE-F4.md`](docs/MILESTONE-DEGREE-AWARE-F4.md),
[`docs/MILESTONE-CRYPTANALYSIS-SCOREBOARD.md`](docs/MILESTONE-CRYPTANALYSIS-SCOREBOARD.md),
[`docs/MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md`](docs/MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md), and
[`docs/MILESTONE-COMPETITIVE-ALGEBRA.md`](docs/MILESTONE-COMPETITIVE-ALGEBRA.md).
[`docs/MILESTONE-ALGORITHMIC-ELIMINATION.md`](docs/MILESTONE-ALGORITHMIC-ELIMINATION.md) is the
current plan rather than a record of measurements taken, and
[`docs/MILESTONE-COMPETITIVE-MQ-SOLVING.md`](docs/MILESTONE-COMPETITIVE-MQ-SOLVING.md) is the next
one. That plan opens by recording that the one before it is unfinished, because its own scope
depends on measurements M26 has not yet reported.

The last of those reproduced a published cryptanalytic attack end to end, extended the verified resultant
frontier from four rounds to **six** with a witness checked through the permutation, and calibrated
against an external solver on identical problems — where the published Anemoi conversion wall
**does not reproduce**: 46 s here against 6.13 h reported, and a within-run conversion/basis ratio
of 1.71 against 2 367.

That milestone's §10.1 is worth reading on its own. It scores the plan's own predictions and finds
that every one about a stage already measured held, while three of four about quantities nobody had
measured were wrong by more than an order of magnitude — one by 838x. The cost-model table exists so
that is visible rather than quietly absorbed.

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

`PrimeFieldElement128<P>` reduces a 256-bit product by allocating software long division, which
made it the slowest field in the crate — slower than one four times as wide. It is **deprecated**
rather than converted (#163); the paragraph after the table says why, and
[`Proth68Fr`](src/fields/prime_field_256.rs) is the replacement.
`cargo bench --bench field_arithmetic`, per operation:

| field | width | mul | add | sub | inverse |
|---|---:|---:|---:|---:|---:|
| `Mersenne31` | 31, in 4 bytes | 1.35 ns | 0.75 ns | 0.75 ns | **100 ns** |
| `Zp2147483647` | 31 | 1.76 ns | 1.10 ns | 0.95 ns | **124 ns** |
| `Zp18446744073709551557` | 64 | 1.71 ns | 1.05 ns | 0.97 ns | **236 ns** |
| `PrimeFieldElement128` — deprecated | 68 | **130.6 ns** | 2.10 ns | 1.90 ns | **17.84 µs** |
| `Bn254Fr` | 254 | 18.71 ns | 3.69 ns | 3.41 ns | 3.77 µs |
| `Bls12_381Fr` | 255 | 19.34 ns | 3.52 ns | 3.27 ns | 3.97 µs |

The three bold inversion figures are from #160 and replace 227, 246 and 509 ns. Those three fields
invert by Fermat, and Fermat went through a *recursive* `pow` when the trait already had the
iterative `pow_limbs` next to it — 2.0x to 2.3x for one line per field, with no change to the
result. The other three rows do not use that route and are unchanged;
`docs/MILESTONE-LARGE-PRIME-FIELDS.md` §4.1.1 has the before/after table, the controls, and why
replacing Fermat with binary extended Euclid measured *slower* at these widths.

Read the last three rows together: a 254-bit multiply is **7.0x faster** than the 68-bit one, and
10.9x slower than the 64-bit one. A claim about what field width costs has to say which baseline
it means. Inversion over a wide field is 202 multiplies, so pivot normalization should multiply by
a precomputed inverse rather than divide per entry.

#### Why the 128-bit field is deprecated rather than converted

#163 asked whether to put `PrimeFieldElement128` into Montgomery form, and the question it asked
be settled first was: *is there a modulus between 2^64 and 2^128 that this crate wants to compute
over, which `PrimeFieldElement256` does not already serve better?* The answer is no.

The type has **no non-test caller** — its only consumers are the field conformance tests, the
`for_each_field!` arm, and the benchmark that measures how slow it is. And `PrimeModulus256` takes
its modulus as `[u64; 4]`, so any prime in that range is simply the low two limbs with the top two
zero. The one candidate justification was an NTT-friendly prime in the range, since `two_adicity`
is a property of the order rather than of the backing width; `Proth68Fr` is exactly that prime
(3*2^66 + 1, two-adicity 66) over `PrimeFieldElement256`.

Measured at `ece0d05`, `cargo bench --bench field_arithmetic` under `tools/benchlock.sh` with
`taskset --cpu-list 0-7`, one criterion process, 256 operations per iteration divided out. The
same modulus on both 68-bit rows, so the comparison is the representation alone:

| field | backing | mul | inverse |
|---|---|---:|---:|
| `Zp18446744073709551557` | 64-bit Montgomery | 1.81 ns | 274 ns |
| `PrimeFieldElement128` — deprecated | `u128`, long division | **136.8 ns** | **18.36 µs** |
| `Proth68Fr` — the replacement | 2-limb CIOS | **14.01 ns** | **847 ns** |
| `Bn254Fr` | 4-limb CIOS | 19.78 ns | 3.825 µs |

Same field, same modulus: **9.8x on multiplication and 21.7x on inversion**, for declaring it as
two limbs of a `PrimeModulus256` instead of a `u128`. `Proth68Fr` also beats `Bn254Fr` by 1.4x and
4.5x, which is what two CIOS limbs against four should do — so the "cost of width" really is a
cost of limbs, and the 68-bit field was never paying it.

The outer rows are **controls**: nothing in this change touches them, and they reproduce the table
above to within this machine's noise (1.81 against 1.71 ns, 19.78 against 18.71 ns), which is what
licenses reading the two middle rows against each other.

Deprecated rather than deleted, because the type is `pub`. The field laws still run over it, and
the `p68` bench row is kept beside the new `p68_mont` so the cost of a dividing multiply stays
visible as recorded history.

Two other field types gained the same treatment, each measured on the operation rather than on a
whole computation, because at the time both modules were private and no bench target could reach
them:

- `BinaryFieldElement<P>` multiplies with `PCLMULQDQ` and reduces by Barrett rather than by a
  bit-at-a-time loop and long division — **212.70 to 2.02 ns** per multiply over GF(2^63). The
  instruction is probed at run time, since it is not implied by the `x86-64-v3` floor, and the
  scalar fallback is kept and tested.
- `ExtensionFieldElement<P, N, M>` reduces once per output coefficient instead of once per partial
  product, O(N) instead of O(N^2), under a compile-time overflow bound; the per-multiplication heap
  allocation is gone.

Both are public now. `Gf32`, `Gf256`, `Gf13Pow4` and `Gf256Mq` are the declared instantiations.

**`Gf256` and `Gf256Mq` are both GF(2^8) and are not interchangeable.** `Gf256` reduces modulo
`x^8 + x^4 + x^3 + x + 1` (`0x11B`, the AES polynomial); `Gf256Mq` modulo
`x^8 + x^4 + x^3 + x^2 + 1` (`0x11D`), which is what the Fukuoka MQ Challenge specifies for its
GF(2^8) families. The two are isomorphic and the arithmetic differs: over the first
`0x57 * 0x83 = 0xc1` (FIPS-197 §4.2), over the second it does not, and more than fifty thousand of
the 65025 nonzero operand pairs separate them. An order check cannot tell them apart — both have
order 256 — so the field is named at the type level rather than inferred.
`docs/research/fukuoka-mq.md` §2.4 has the consequence for importing an instance.

**An integer names an element of an extension field in two different ways, and the API keeps them
apart.** `FiniteField::new` is the image of an integer under the unique ring homomorphism from the
integers — `val mod p` — so over an extension it only ever reaches the prime subfield, and walking
it over `0..q` is not an enumeration. `KnownOrder::element_at` is the bijection from `0..q`, and
`FiniteField::from_str` reads the text `Display` writes, which is the coefficient bit pattern over
GF(2^m) and the bracketed coefficient list over GF(p^k):

```rust
use zeebra::{fields::{Gf13Pow4, Gf256}, FiniteField, KnownOrder, One};

// `new` is the embedding: 5 copies of one, which in characteristic two is one.
assert_eq!(<Gf256 as FiniteField>::new(5), Gf256::one());

// `from_str` is the representation, and inverts `Display`.
let x2_plus_1 = <Gf256 as FiniteField>::from_str("5").unwrap();
assert_eq!(x2_plus_1.to_string(), "5");
assert_eq!(Gf256::element_at(5), Some(x2_plus_1));

// Out of range is a `Result`, not a panic.
assert!(<Gf256 as FiniteField>::from_str("256").is_err());

// Over GF(13^4) a bare decimal is the base-13 digits; `Display`'s own form reads back too.
assert_eq!(
    <Gf13Pow4 as FiniteField>::from_str("170").unwrap().to_string(),
    "[1, 0, 1, 0]",
);
assert_eq!(
    <Gf13Pow4 as FiniteField>::from_str("[1, 0, 1, 0]"),
    <Gf13Pow4 as FiniteField>::from_str("170"),
);
```

`element_at`'s default is `new`, which is that bijection exactly when `q = p`, and returns `None`
for every index over a field whose order and characteristic differ — so a field that has not
overridden it reports that it cannot be enumerated rather than enumerating its prime subfield and
returning a count that is wrong rather than failed.

### Characteristic two in the solver, and field equations

The Gröbner stack is generic over `FiniteField` and had never been run in even characteristic. It
works: `grobner::tests::test_the_whole_pipeline_over_gf2` and its `Gf256` twin take a planted
system through F4, agreement with Buchberger, FGLM, both routes to lex, and `solve_one`, with the
recovered point re-evaluated against the original system. Neither needed a change to the solver.

One trap, asserted rather than described. `benchmark_systems::planted` **degenerates in
characteristic two**: its first generator per variable pair is `x^2 + y^2 - (a^2 + b^2)`, and since
`x^2 + y^2 = (x + y)^2` here that is a perfect square, so the ideal is nonradical. A reader who
assumed the generator behaves the same in every characteristic would mis-read every
characteristic-two measurement taken with it, so
`grobner::tests::test_planted_degenerates_to_a_square_in_characteristic_two` pins it.

A system over `F_q` has two different solution sets — the points of the variety over the algebraic
closure, and the points with coordinates in `F_q` itself. Cryptanalysis asks for the second, which
is cut out by adjoining the field equations `x_i^q - x_i`:

```rust
use zeebra::{
    fields::Zp2,
    grobner::{classify_ideal, f4, field_equations::with_field_equations, IdealClass},
    MonomialOrder, Monomial, MultivariatePolynomial, One,
};

let grevlex = MonomialOrder::GradedReverseLexicographic;

// x*y, in two Boolean variables: positive-dimensional over the closure.
let system: Vec<MultivariatePolynomial<2, Zp2>> =
    vec![MultivariatePolynomial::new(&[(Monomial::new(&[1, 1]), Zp2::one())])];
let bare = f4(&system, grevlex).unwrap();
assert_eq!(classify_ideal(&bare, grevlex), IdealClass::PositiveDimensional);

// Adjoining x^2 - x per variable forces zero dimension.
let extended = with_field_equations(&system).unwrap();
let basis = f4(&extended, grevlex).unwrap();
assert_eq!(classify_ideal(&basis, grevlex), IdealClass::ZeroDimensional);
```

Because `x^q - x` is squarefree and splits completely over `F_q`, the extended ideal is **radical**,
so `dim F_q[x]/I` is exactly the number of `F_q`-rational points — counted once each, however many
times they occur in `I`. That makes a solution count a machine-independent invariant, and
`field_equations`' tests check it against exhaustive enumeration at `n = 8` over GF(2).

**Adjoining them is a judgement about `q`, not a default, and nothing here chooses for the caller.**
The generator has degree `q`, so it only pays when `q` is below the degree the computation would
reach anyway. Over GF(2) that is degree 2 and the answer is essentially always yes. Over GF(31) —
Fukuoka MQ types III and VI — it is degree 31 against measured solving degrees of 4 to 9, so the
answer is no. Over GF(65521), the Courtois MinRank challenge field, degree 65521 is absurd.
`field_equations` refuses outright only when `q` exceeds a monomial exponent, which is a
representation limit rather than a policy.

The *solving* half is covered end to end over both characteristic-two fields by
`tests/boolean_readiness.rs`. Over GF(2), `fglm_to_lex` converts the field-equation ideal and
`solve_zero_dimensional` returns **exactly** the point set an exhaustive walk of all 256 assignments
finds — no dropped solution and none invented over an extension. Over GF(2^8) the degree-256
equations are usable rather than merely representable, and `roots` works, which exercises the
characteristic-two trace splitter at `m = 8` where every earlier test had `m = 1`.

Three caveats a caller should know, each asserted rather than described:

- **GF(2) is `Zp2`, not `BinaryFieldElement<0b11>`.** The two are the same field — the full operation
  tables agree — but `Zp2` is 4 bytes to the other's 8 and needs no carry-less multiply for a field
  where multiplication is `and`.
- **A GF(2^8) coefficient is written as its bit pattern.** `MultivariatePolynomial::parse` works over
  `Gf256`, reading each decimal `0..255` as the coefficient bit pattern `Display` writes — so
  `from_str` inverts `Display` over every field, and over an extension it is deliberately not
  `FiniteField::new`, which only ever reaches the prime subfield. `KnownOrder::element_at` is the
  route that enumerates all `q` elements. #377.
- **Omitting the field equations is diagnosed on both routes, but the default route pays to find
  out.** `SolveStrategy::GrevlexF4ThenFglm` classifies the basis it already has; the default
  `DirectLexF4` exhausts a Macaulay-matrix budget first, and only then computes a grevlex basis to
  tell a crossed budget from a positive-dimensional ideal. Both report `PositiveDimensional`, whose
  remedy is `with_field_equations` rather than a larger limit, and a zero-dimensional ideal that
  really is out of budget still reports a *resource* failure. #376.

[`docs/research/boolean-solving.md`](docs/research/boolean-solving.md) is the readiness write-up:
what runs in characteristic two, what does not and why, and the Singular oracle's position (it has
covered GF(2) all along — 40 of the 240 committed differential fixtures are at characteristic 2 —
and is prime-field only, so there is no GF(2^8) oracle yet: #378).

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

Declared: `Zp2` (GF(2) — Fukuoka MQ types I and IV, LowMC, HFE), `Zp31` (Fukuoka MQ types III and
VI), `Zp32003` (the cross-library corpus's small-prime reference characteristic, and the field every
published Gröbner timing table uses), `Zp65537_32`, `Mersenne31`, `BabyBear` (`2^31 - 2^27 + 1`) and
`KoalaBear` (`2^31 - 2^24 + 1`, the 2026 Poseidon challenge prime). The two Bear fields are NTT-friendly;
`Zp65537_32` and `Zp2147483647` are the same mathematical fields as `Zp65537` and `Mersenne31`'s
64-bit twin, so a caller picks a width rather than a field. `Zp2` is the one declared modulus that
is not odd, so it keeps the wide-remainder path rather than reaching Montgomery form.

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
- `try_primitive_element` returns `Err(RootOfUnityError::NoKnownGenerator)`: finding a generator of
  the multiplicative group means factoring a 254-bit `q - 1`, which no algorithm here needs and
  which should not start by accident. `try_root_of_unity` works for any **power-of-two** order,
  through the two-adic construction below, and refuses any other — that order is the one that
  needs the factorization.

### A generator under an explicit effort budget

`try_primitive_element` has nowhere to put an effort bound, so it still declines. The opt-in entry
point is `try_primitive_element_with_budget::<F>(&EcmBudget, rng)`, which factors `q - 1` with
Lenstra ECM (`integers::factor_with_budget`) and either returns a generator certified against the
**complete** factorization or reports the cofactors the budget could not split:

```rust
use zeebra::{
    fields::{try_primitive_element_with_budget, Bls12_381Fr, Bn254Fr, GeneratorSearchError},
    integers::EcmBudget,
};
use rand::{prelude::StdRng, SeedableRng};

let mut rng = StdRng::seed_from_u64(5);

// BLS12-381's r - 1 = 2^32 * 3 * 11 * 19 * 10177 * 125527 * 859267 * 906349^2 * 2508409
//                     * 2529403 * 52437899 * 254760293^2 — nine decimal digits at worst.
let g = try_primitive_element_with_budget::<Bls12_381Fr, _>(&EcmBudget::for_digits(9), &mut rng);
assert!(g.is_ok());

// BN254's r - 1 has a 29-digit prime factor, past what this ECM reaches. The honest answer names
// what a larger budget would have to split.
let refused = try_primitive_element_with_budget::<Bn254Fr, _>(&EcmBudget::for_digits(9), &mut rng);
assert!(matches!(
    refused,
    Err(GeneratorSearchError::IncompleteFactorization { .. })
));
```

**The cost is not a function of the field's width.** Both fields above are 255 bits and they land on
opposite sides of this, because what the search pays for is the largest prime factor of `q - 1` and
not the size of `q`. So the budget is the caller's to choose, and a budget that does not finish is
an error rather than a weaker guarantee — a partial factorization cannot certify a generator,
since an untested prime divisor is one whose quotient the candidate might fix.

The search itself is HAC Algorithm 4.80, the same one `KnownOrder::try_primitive_element`'s default
runs, lifted off `u128` exponents onto `FiniteField::pow_limbs` so that it reaches a field whose
order a `u128` cannot hold. It is generic over `KnownOrder`, so it is not limited to the 256-bit
fields; it is simply the only place the refusal was load-bearing.

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
`primitive_element`, `root_of_unity`, `two_adicity`, `two_adic_root_of_unity`, the predicates
`is_generator` and `is_primitive_nth_root`, and `sqrt`. For an extension field q = p^k, so the
order and the characteristic are genuinely different; both are reported.

Constructing a generator or a root of unity **fails as a value**. Whether `n` divides `q - 1`, and
whether a field has a generator this crate will look for **without being asked**, are facts about
the field and the requested order rather than programmer errors, so `try_primitive_element`,
`try_root_of_unity` and `try_two_adic_root_of_unity` return `Result<Self, RootOfUnityError>`.
`NoKnownGenerator` is a statement about what the trait method will start unprompted, not about the
field: `try_primitive_element_with_budget` is the opt-in route, and the 256-bit-field section above
has the two cases it separates. The failures as values:

```rust
use zeebra::{fields::{RootOfUnityError, Zp13}, KnownOrder};
use rand::{prelude::StdRng, SeedableRng};

let mut rng = StdRng::seed_from_u64(1);

// 6 divides 12, so Z/13 holds an element of order exactly 6.
let w = Zp13::try_root_of_unity(6, &mut rng).expect("6 divides q - 1");
assert!(w.is_primitive_nth_root(6, &mut rng));

// 5 does not.
assert_eq!(
    Zp13::try_root_of_unity(5, &mut rng),
    Err(RootOfUnityError::OrderDoesNotDivide { n: 5 }),
);
```

The names without `try_` are kept as thin panicking wrappers, so existing call sites are
unchanged; the fallible form is the one an implementation overrides. `is_generator` needs the
factorization of `q - 1` and so is fallible for the same reason, while `is_primitive_nth_root`
factors only `n` and therefore works over the 254-bit fields — which is what makes it the
independent check on the two-adic construction rather than a restatement of it.

#### Square roots, and which elements have one

`sqrt` is Tonelli-Shanks, and one implementation covers every field in the crate because what
changes between them is the two-adicity of `q - 1` rather than the algorithm:

```rust
use zeebra::{fields::{legendre_symbol, Zp65537}, FiniteField, KnownOrder};
use rand::{prelude::StdRng, SeedableRng};

let mut rng = StdRng::seed_from_u64(1);
let x = Zp65537::new(7);

match x.sqrt(&mut rng) {
    Some(r) => assert_eq!(r * r, x),
    None => assert_eq!(legendre_symbol(&x), -1),
}
```

`legendre_symbol` is Euler's criterion: 0 on zero, 1 on the squares, -1 on the rest. Over a prime
field it is the Legendre symbol; over an extension field of odd characteristic it is the same
character on the larger group. In characteristic two squaring is a bijection, so every element is a
square and the root is `x^(q/2)` — a different computation, reached by the same call.

With `q = 3 (mod 4)` the two-adicity is 1, Tonelli-Shanks degenerates to the single exponentiation
`a^((q+1)/4)`, and no random element is consumed at all; the rng is drawn from only to find a
quadratic non-residue, which only the correction loop needs. Of the two roots `±r`, which one is
returned is unspecified.

`integers::jacobi_symbol` is the integer counterpart, by the binary algorithm, so it needs no
factorization. For prime `n` it agrees with `legendre_symbol` on the same residue — two
computations sharing no code, which is how each is checked — and for composite `n` it is not a
residue test at all: `(2/15) = 1` though 2 is not a square mod 15.

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
  `a^(q-2)`, which needs the order — and the order is in `KnownOrder`, not here. A field that has
  one writes Fermat as `pow_limbs` over a `q - 2` subtracted on the limbs, so no width caps that
  route; a field without one, or with a faster inversion, writes its own.

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
copy. The plateau is the ratio between an inversion and three multiplications, so it tracks
whatever inversion costs — and #160 halved inversion over the fields that invert by Fermat.
`field_arithmetic`'s `isolated/inverse` against its `batch/inverse` over the same 256 operands,
before and after #160: **29.6x to 14.8x** over `Mersenne31`, **54.6x to 27.6x** over the largest
64-bit prime, against **60.4x to 60.7x** over BN254 `Fr`, which does not use that route and holds
still. Montgomery's trick still wins by more than an order of magnitude everywhere; it has less to
beat. `docs/research/batch-inversion.md`'s table predates #160 and is its own instrument, so read
its Mersenne-31 and Goldilocks columns as roughly halved rather than substituting these figures
for them.

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

The product is `ikj` with `k` unrolled four deep, not the textbook `ijk`. Row-major storage makes
`ijk`'s innermost loop stride the right operand by `num_columns`, a cache line per multiplication;
`ikj`'s is an axpy over contiguous spans. `benches/linear_algebra.rs` measures it two ways: square
sizes, and a family of `m x k` times `k x n` shapes holding the multiplication count at 2^26 so the
only thing that varies is the right operand's footprint. **The permutation is not the free win it
looks like.** It converts a kernel that is memory-bound out of cache into one that is ALU-bound at
every footprint — over a 31-bit prime, pinned, three interleaved reps, the new kernel is flat at
124-128 ms whether that operand is 256 KiB, 8 MiB or 128 MiB, where `ijk` goes 149 ms → 171 ms →
252-267 ms — which is the §8.2 result in
[`docs/MILESTONE-SIMD-PARALLELISM.md`](docs/MILESTONE-SIMD-PARALLELISM.md) arrived at from the other
side. But in cache it buys little and can cost: 1.31x at square n=32, neutral at n=64, **8% slower
at n=128**, 1.11x at n=256, rising to 2.0x only once the right operand is past L3. `ijk` keeps one
entry of the product in a register where `ikj` reads and writes a whole row of it per `k`, and in
cache that register is worth more than the stride costs; the unroll — four right-hand rows per load
and store of the product row — is what pays most of it back. Plain `ikj` measured 11-18% slower
than `ijk` at square sizes that fit in cache.

Two gaps are deliberate. There is no mutable column iterator — handing out disjoint `&mut` down a
strided column of a row-major buffer is where the borrow checker stops being free, and nothing in
the crate needs it yet. And `Matrix<T>` does not implement `Ring`, so a matrix cannot yet be a
polynomial coefficient: `Ring` has no fallible operations, and only *square* matrices form one, so
that wants a `SquareMatrix<T>` type carrying the invariant rather than a runtime check inside
`mul`. [#132](https://github.com/mfaulk/zeebra/issues/132) has the discussion.

## Number-Theoretic Transform

`fft::evaluate` and `fft::interpolate` are the forward and inverse transforms over an `FFTDomain`
of any size `n`, built from a primitive `n`th root of unity. At a power-of-two size — the common
case, and the fast one — both are the same iterative in-place radix-2 kernel — a bit-reversal permutation followed by `log n` passes of butterflies over the
domain's own powers, read with a stride — so there is no recursion, no per-level allocation, and
one twiddle multiplication per two outputs. `interpolate` is that kernel over the batch-inverted
domain, scaled by `1/n`. Any other size is decomposed into coprime factors first; see
[Sizes that are not a power of two](#sizes-that-are-not-a-power-of-two).

**`1/n` is where the inverse transform can be ill-posed, and it is refused by name.** In
characteristic `p` the scalar `n` is zero whenever `p | n`, so `1/n` does not exist and no inverse
transform of that length is defined — over `GF(2^m)` that is every even size. A domain built from a
primitive root never has this problem, since an `n`th root of unity needs `n | q - 1`; the
unchecked `FFTDomain::new` is the route that reaches it. `try_interpolate` returns
`InterpolateError::SizeNotInvertible` there and `interpolate` panics with the same message, rather
than failing deeper down with "the zero element does not have a multiplicative inverse", which named
the symptom and not the cause ([#396](https://github.com/mfaulk/zeebra/issues/396)). Over `GF(2^m)`
an odd size works: `Gf256`'s group order is `255 = 3 * 5 * 17`, so it hosts 3-, 5-, 15-, 17-point
transforms and no even one at all.

**The transform zero-pads internally.** A polynomial of any degree below `n` is extended to the
domain size inside `evaluate`, so a caller hands over unpadded operands and chooses only `n` — the
domain size is the caller's because only the caller knows how large a result it needs. A polynomial
of degree `n` or more still panics: `n` evaluations cannot determine it. That stays a panic rather
than becoming a `DomainError`-style typed failure because of where #120 drew that line — a fact
about the field is a value, a programmer error is a panic, and a caller that supplied both the
polynomial and the domain already knows whether `deg(p) < n`. The transform also panics on a domain
that is not the powers of a *primitive* `n`th root of unity: `try_from_generator` rejects those, but
`FFTDomain::new` takes a vector of powers unchecked and `FFTDomain::split` returns domains that are
not power sequences at all.

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

**Mersenne-31 admits no power-of-two transform above size two**, which matters because it is the
field most of this crate's F4 benchmarks use. `BabyBear` and `KoalaBear` — the latter being the
prime the 2026 Poseidon challenges are over — are NTT-friendly by construction and are what to
reach for when a transform is wanted over a small field. Sizes drawn from the *odd* part of `q - 1`
are a separate matter and are available on Mersenne-31 too, as the next section shows.

`FiniteField::pow_limbs` takes its exponent as little-endian limbs, which is what makes the above
possible at all: the odd part of BN254's `q - 1` is 226 bits, so `pow`'s `u128` cannot hold it.

### Sizes that are not a power of two

A size `n` with `n | q - 1` needs no padding, whatever its factorization:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    evaluate, fields::PrimeFieldElement64, interpolate, FFTDomain, KnownOrder, Polynomial,
    UnivariatePolynomial,
};

// 65520 = 2^4 * 3^2 * 5 * 7 * 13, so this field hosts a domain of size 12, 105, 2520, ...
type F = PrimeFieldElement64<65521>;

let mut rng = StdRng::seed_from_u64(125);
let w = F::root_of_unity(12, &mut rng);
let domain = FFTDomain::from_generator(w, 12);

let p = UnivariatePolynomial::<F>::rand(11, &mut rng);
let values = evaluate(&p, &domain);
for (i, value) in values.iter().enumerate() {
    assert_eq!(*value, p.eval(&domain[i]));
}
assert_eq!(interpolate(&values, &domain), p);
```

The decomposition is **prime-factor (Good–Thomas)**: for `n = n1 * n2` with `gcd(n1, n2) = 1`,
re-indexing the input by the Chinese remainder isomorphism `Z/n = Z/n1 x Z/n2` turns the length-`n`
DFT into a 2-D transform of `n1`- and `n2`-point DFTs **with no twiddle factors between the
stages** — the entire cost of the split is two permutations. Writing `i = i1 (mod n1)`,
`i = i2 (mod n2)` and `k = k1*n2 + k2*n1 (mod n)`:

```text
w^(i k) = w^(n2 i k1) * w^(n1 i k2) = w_n1^(i1 k1) * w_n2^(i2 k2)
```

since `w_n1 = w^n2` has order `n1` and so only sees its exponent modulo `n1`. Each axis is then
dispatched the same way, recursively, and what it costs depends on the factor:

| factor | route | cost of that stage |
|---|---|---|
| a power of two | the radix-2 kernel | `n log n_i` |
| composite with coprime parts | recurse | — |
| an odd prime power (9, 25, 27) | the `O(m^2)` definition | `n * n_i` |

So `2520 = 2^3 * 3^2 * 5 * 7` costs `n log 8` plus `n * (9 + 5 + 7)`, which is why a size whose
odd factors are small is cheap and **a large prime size is quadratic through this route**.
[Bluestein](#bluestein-a-large-prime-size-without-the-quadratic-cost) is what removes that case,
and it is a separate entry point rather than a decomposition the dispatcher reaches on its own —
see below for why.

Two consequences of allowing any size, both visible in the API:

- `DomainError::SizeNotPowerOfTwo` is gone, since the size is no longer a reason to refuse. A
  domain is refused only when the generator does not have order exactly `n` (`NotAnNthRoot`,
  `NotPrimitive`) or the size is zero (`SizeZero`). Primitivity now costs one `g^(n/p)` check per
  distinct prime `p | n` rather than the single `g^(n/2)`; a root of order 6 at `n = 12` satisfies
  `g^6 != 1` and would otherwise have been accepted.
- `FFTDomain::split` — the radix-2 even/odd split — panics on an odd size, where the halves would
  not be the same length.

### Bluestein: a large prime size without the quadratic cost

Bluestein's algorithm turns a length-`n` transform into a **convolution**, which the radix-2 kernel
runs at a padded power-of-two length. It is `O(n log n)` at every size, prime included, so it is
what the quadratic row of the table above gives way to.

The textbook identity is `jk = (j^2 + k^2 - (k - j)^2) / 2`, whose halved squares need a `2n`-th
root of unity to write down. This uses the **triangular numbers** `T(m) = m(m - 1) / 2` instead:

```text
T(j) + T(k) - T(k - j) = jk - j,     so     jk = T(j) + j + T(k) - T(k - j)
```

giving

```text
X_k = w^T(k) * sum_j (x_j w^(T(j) + j)) * w^(-T(k - j)).
```

Every exponent is an integer and every factor is a power of the `n`th root the caller already
holds, so there is no second root to construct, validate, or fail to find. Nothing is lost by it:
for odd `n`, `n | q - 1` already implies `2n | q - 1`, and for even `n` the convolution length
needs two-adicity at least `log2(n) + 1` — because `2n - 1` is odd and above one, so it is not a
power of two and `L >= 2n` — which is never less than the `2n`-th root's own `v2(n) + 1`. A field
that can host the convolution always has a `2n`-th root; one that cannot never gets far enough to
want it.

So the convolution length is the single demand on the field, and `bluestein_convolution_domain`
is where it is either met or reported:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    bluestein_convolution_domain, bluestein_convolution_length, bluestein_transform,
    fields::KoalaBear, FFTDomain, FiniteField, KnownOrder, Zero,
};

// KoalaBear: q - 1 = 2^24 * 127, so 127 is a size this field has a root of unity for — and the
// one the prime-factor route would spend 127^2 multiplications on.
type F = KoalaBear;
let n = 127;

let mut rng = StdRng::seed_from_u64(127);
let domain = FFTDomain::from_generator(F::root_of_unity(n as u64, &mut rng), n);

// The convolution runs at the least power of two at or above 2n - 1, so that the cyclic
// convolution does not alias the two ends of the chirp onto each other.
assert_eq!(bluestein_convolution_length(n), 256);
let convolution_domain = bluestein_convolution_domain::<F, _>(n, &mut rng).unwrap();

let coefficients: Vec<F> = (0..n).map(|i| F::new(i as u64 + 1)).collect();
let mut values = coefficients.clone();
bluestein_transform(&mut values, &domain, &convolution_domain);

// The same thing the Vandermonde definition gives, in n log n rather than n^2.
for (k, value) in values.iter().enumerate() {
    let mut expected = F::zero();
    for (j, c) in coefficients.iter().enumerate() {
        expected += *c * domain[(j * k) % n];
    }
    assert_eq!(*value, expected);
}
```

A field too shallow in two-adicity to hold a primitive `L`-th root is a fact about the field, so it
is a value rather than a panic — the same line #120 drew for `DomainError`, in the existing
`RootOfUnityError` vocabulary:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    bluestein_convolution_domain,
    fields::{Mersenne31, RootOfUnityError},
    FFTDomain, KnownOrder,
};

// Mersenne-31: q - 1 = 2 * (2^30 - 1), so its two-adicity is 1 and there is no transform here
// beyond size two. A size-5 Bluestein would want a 16-point convolution.
assert_eq!(Mersenne31::two_adicity(), 1);
let mut rng = StdRng::seed_from_u64(2);
assert_eq!(
    bluestein_convolution_domain::<Mersenne31, _>(5, &mut rng),
    Err(RootOfUnityError::TwoAdicityExceeded { log_n: 4, two_adicity: 1 }),
);
```

**It is not yet dispatched to automatically.** `evaluate` and `interpolate` at a prime size still
take the quadratic route, and reaching Bluestein means calling it. Two reasons, both of which want
their own change:

- The crossover against the quadratic definition is **unmeasured**. `dft` is quadratic but
  allocation-free and branch-free, while Bluestein pays three `n`-length chirp passes plus a padded
  convolution of length up to `4n`, so below some size the quadratic route wins. No figure is
  quoted here because none has been measured.
- `prime_factor::transform_any` is generic over `FiniteField`, and constructing a primitive `L`-th
  root needs `KnownOrder` and an rng. Tightening that bound would propagate through `evaluate` and
  `interpolate` into the polynomial API — a breaking change that is a decision, not a side effect.

### What the univariate stages cost

`cargo run --release --example univariate_scaling` sweeps seven stages by doubling degree until a
wall-clock budget is exceeded, reporting time, the local scaling exponent, and **peak live heap
bytes** from a counting allocator. Six of them, on a 64-core/300 GB workstation at one second per
measurement; the seventh is `fftmul`, which only means anything against `mul` at the same degree
and so is in the crossover section below:

| stage | exponent | KoalaBear | BN254 `Fr` | peak bytes |
|---|---|---|---|---|
| `mul`, schoolbook | 2 | 2^15 | 2^13 | `4 n B` |
| `div`, long division | 2 | 2^15 | 2^13 | `6 n B` |
| `evaluate` (NTT) | 1 | **2^24** | **2^22** | `1 n B` |
| `interpolate` (iNTT) | 1 | **2^24** | **2^22** | `2 n B` |
| `lagrange_interpolate` | 2 | 2^14 | 2^12 | `5 n B` |
| `roots` | 2 | 2^12 | 2^8 | `12 n B` |

`fftmul` reaches operand `2^22` over KoalaBear at the same one-second budget, peak `12 n B`. It
used to stop at `2^18`, and that was **its own verification**: the stage asserted the transform's
product against schoolbook, which is `O(n^2)` against a quasi-linear subject, so the reported
ceiling got lower as the multiply got faster. It now checks against schoolbook up to `n = 2^12`
and by evaluation agreement at four random points above that, and **prints which it did** under
each curve — a ceiling set by a checker is not the same figure as one set by the stage. See
[`docs/research/fast-univariate.md`](docs/research/fast-univariate.md) §3.

`B = size_of::<F>()` — 8 bytes for a 64-bit field, 32 for a 254-bit one, so **4x**. That is not
the 2.5x the F4 budgets are written in: those count sparse `(usize, F)` entries, whose 8-byte index
word is paid whatever the field is and dilutes the ratio. A dense coefficient array has no index
word, so a byte budget carried over from the F4 side under-estimates this layer by 1.6x.

**Division is an operator.** `/` and `%` on `UnivariatePolynomial` are the quotient and the
remainder of that `div` row, in all four owned/borrowed combinations plus `/=` and `%=`. Each runs
the whole division, so a caller wanting both halves should call `Polynomial::div_with_remainder`,
which returns the pair. That trait method used to be named `div`; it carries its full name now
because an inherent `div(&self, ..)` loses method resolution to `Div::div`, which takes `self` by
value, and every `p.div(&q)` would otherwise have silently become the quotient alone. `lcm(a, b)`
is `a * b / gcd(a, b)` renormalized monic, and zero when either argument is zero:

```rust
use zeebra::{fields::Zp7, gcd, lcm, Polynomial, UnivariatePolynomial};

type P = UnivariatePolynomial<Zp7>;
let f = P::try_from("1 + 2x + x^2").unwrap(); // (x + 1)^2
let g = P::try_from("6 + x^2").unwrap(); // x^2 - 1 = (x + 1)(x + 6), since 6 = -1 mod 7

assert_eq!(gcd(&f, &g), P::try_from("1 + x").unwrap());
// (x + 1)^2 (x + 6) = x^3 + x^2 - x - 1
assert_eq!(lcm(&f, &g), P::try_from("6 + 6x + x^2 + x^3").unwrap());

// `/` and `%` are the two halves of one long division; `div_with_remainder` returns both.
let (quotient, remainder) = f.div_with_remainder(&g);
assert_eq!(&f / &g, quotient);
assert_eq!(&f % &g, remainder);
```

**The Bézout cofactors, and the middle of the sequence.** `xgcd(a, b)` returns `(g, u, v)` with
`g = u*a + v*b`, and `partial_bezout(a, b, degree_bound)` returns the Euclidean sequence *halted*
at the first remainder of degree below the bound, as the pair `(v, r)`. The halted form is the
primitive: Reed-Solomon decoding solves the key equation `Λ(x)S(x) ≡ Ω(x) mod x^{2t}` by running it
on `(x^{2t}, S(x))` with `degree_bound = t`, taking `Ω` as the remainder and `Λ` as the cofactor,
and rational reconstruction and Padé approximation want the same thing. Only the cofactor of the
second argument is carried through the loop, because that is the one those consumers read; `xgcd`
recovers `u` from the identity with one exact division rather than paying for a second cofactor row
at every step.

```rust
use zeebra::{fields::Zp13, gcd, partial_bezout, xgcd, Polynomial, UnivariatePolynomial};

type P = UnivariatePolynomial<Zp13>;
let a = P::try_from("2 + 3x + x^2").unwrap(); // (x + 1)(x + 2)
let b = P::try_from("3 + 4x + x^2").unwrap(); // (x + 1)(x + 3)

let (g, u, v) = xgcd(&a, &b);
assert_eq!(g, gcd(&a, &b));
assert_eq!(&(&u * &a) + &(&v * &b), g);

// Halted at the first remainder of degree below 2, with its cofactor against `b`.
let (v, r) = partial_bezout(&a, &b, 2);
assert!(r.degree() < 2);
```

Both stay quadratic, and that is a decision rather than an omission. Newton-inversion division is
`O(M(d))` and half-GCD is `O(M(d) log d)`, but `M(d)` *at the operator* is still schoolbook: `Mul`
cannot choose an NTT domain from its signature, and Karatsuba is not wired into it either (§4.1 of
[`docs/research/fast-univariate.md`](docs/research/fast-univariate.md)). With a quadratic `M`
underneath, neither is faster than long division — so both are gated on that dispatch work (#185)
rather than written against a multiplication that would make them slower. They are #193 and #194;
§4.5 of the same document has the arithmetic.

The two transforms are the only quasi-linear stages, and they now cost the same: at a matched
`2^18`, `interpolate` is within 2–10% of `evaluate` over all three fields, where it used to be
2.4x, 5.2x and 8.6x. The whole gap was the `2n` inversions batch inversion removed — see
[`docs/research/batch-inversion.md`](docs/research/batch-inversion.md) §2.3. Replacing the
recursive split with the iterative kernel was worth a further **3.7x to 6.1x on the narrow fields
and 2.0x to 2.7x on BN254**, took the peaks from `7 n B` and `9 n B` to `1 n B` and `2 n B`, and
removed the `n log n` hardware integer divisions the recursion's `i % k` compiled to —
`tools/div_census.sh` counts them in the release artifact, 4 before and 0 after:

```text
cargo build --release --example univariate_scaling
tools/div_census.sh target/release/examples/univariate_scaling
tools/div_census.sh target/release/examples/univariate_scaling zeebra::poly   # any symbol prefix
```

KoalaBear's forward transform now covers the field's entire two-adic range inside one second, and
the schoolbook/NTT crossing moved **down one doubling** — measured product degree 1022 to 510 on an
8-byte element and 510 to 254 on a 32-byte one. The dispatch work recalibrated
`fft_multiplication_crossover` from that observation and found it could not simply adopt those
numbers: the threshold has to be measured against **Karatsuba**, which is the route the dispatcher
actually takes below it. It is now 4096 / 512 / 512 by element width; see the crossover section
below.

Interpolation at arbitrary abscissae — what an evaluation-interpolation resultant needs — is
quadratic: it was cubic, at 2^10 and 2^9, until #162 built the numerator product `prod (x - x_i)`
once and divided it down by synthetic division. An evaluation-interpolation resultant turns out not
to need arbitrary abscissae at all, since it chooses where it samples — `bivariate_resultant_ntt`
takes its Sylvester determinants on a power-of-two subgroup and recovers the polynomial with one
`interpolate` — but on the CICO slices the determinants dominate either way.
[`docs/research/fast-univariate.md`](docs/research/fast-univariate.md) has the full curves, the
superseded figures, the gap list, and what each stage would need to go further; the subproduct tree
that would make it `O(n log^2 n)` is not written.

The published Graeffe-transform root finder that those stages serve is read and scoped in
[`docs/research/graeffe-root-finding.md`](docs/research/graeffe-root-finding.md), with the algorithm
as pseudocode, the transform size each registered challenge requires against the ceilings above, and
a measured answer to whether this crate's NTT is access-bound. That document's §7.2 no-go was
retracted in part: the disclosed solve's working degree is `3^13`, not a resultant's `3^18`, and it
fits inside KoalaBear's `2^24`. The next section is the implementation.

### Root finding by the Graeffe transform

`graeffe_root` finds one root of a univariate polynomial in `F_p` in `O(M(d) log p)` rather than the
`O(log q * d^2)` of `roots`, over a field whose `q - 1` has a large power of two and a **small odd
part**. `graeffe_2` is the order-2 transform on its own and `graeffe_l` the order-`l` one.

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::KoalaBear, graeffe_2, graeffe_root, FiniteField, Polynomial, UnivariatePolynomial, Zero,
};

let mut rng = StdRng::seed_from_u64(1);
let f = UnivariatePolynomial::<KoalaBear>::from_zeros(&[KoalaBear::new(7), KoalaBear::new(11)]);

// GT_2 squares the roots, so the transform of (x - 7)(x - 11) is (x - 49)(x - 121).
let squared = UnivariatePolynomial::from_zeros(&[KoalaBear::new(49), KoalaBear::new(121)]);
assert_eq!(graeffe_2(&f, &mut rng).unwrap(), squared);

let root = graeffe_root(&f, &mut rng).unwrap().expect("f has roots in the field");
assert!(f.eval(&root).is_zero());
```

`GT_2(f) = (-1)^d (f_e^2 - x f_o^2)` for `f(x) = f_e(x^2) + x f_o(x^2)`, which is **three transforms
of size `d + 1`, not of `2d + 1`** — half the size an ordinary product of two degree-`d`
polynomials needs. The `(-1)^d` makes a monic input transform to a monic output, so `prod (x - r_i)`
maps to exactly `prod (x - r_i^2)` and `GT_2 . GT_2 = GT_4` composes without a unit.

Iterating it does **not** separate roots by magnitude, which is what the real-number original is
for. With `q - 1 = 2^k * s`, every base-field root `alpha` has `alpha^(2^k)` in the subgroup of
order `s`, so `k` transforms drive the roots into a subgroup small enough to search outright. The
descent back down is decided by the polynomial rather than guessed: `G_(2^(i-1))` reduced modulo
`x^2 - mu_i` is `a x + b`, and `-b/a` is the one of `mu_i`'s two square roots it vanishes at.

`cargo run --release --example graeffe_root` measures it. On a 64-core/300 GB workstation, one core,
KoalaBear in a `u64`:

| degree | transforms | largest | forward | subgroup | descent | **total** | peak heap |
|---:|---:|---:|---:|---:|---:|---:|---:|
| `3^11` = 177 147 | 72 | `2^18` | 0.38 s | 0.09 ms | 7.5 ms | **0.39 s** | 27 MB |
| `3^12` = 531 441 | 72 | `2^20` | 1.50 s | 0.09 ms | 20.7 ms | **1.53 s** | 80 MB |
| **`3^13`** = 1 594 323 | 72 | **`2^21`** | 3.04 s | 0.10 ms | 58.8 ms | **3.11 s** | 195 MB |

Against `roots` on the same shape of input: it reaches degree 32 768 in 86.8 s and goes no further
inside a 60 s budget, and extrapolating its measured quadratic growth to `3^13` gives **57 hours**.
So about four to five orders of magnitude at that degree — with the quadratic side extrapolated, not
measured.

**97.7% of the time is the forward iteration, i.e. the NTT**, which is why #161 moved this stage
more than it moved anything else: the same rows were **13.85 s and 384 MB** before the iterative
kernel landed, so `3^13` is **4.45x faster and 1.97x smaller** for a change in a file this module
only calls. `docs/research/graeffe-root-finding.md` §4.4 keeps both revisions and §4.4.3 is the
difference. The `u32`-backed KoalaBear — the registered challenge's own type — is **2.27 s and
97 MB**.

**Only over a field whose odd part is small.** KoalaBear's is 127; Goldilocks' is `2^32 - 1`, so the
progressive reduction never bites and the subgroup search falls back to `roots` on a polynomial of
the input's degree — 5.07 s of a 5.09 s call at degree 4 096, so **99.6%** of it. The method is
exact there and buys nothing, which is why the papers give Goldilocks a separate algorithm built on
odd-order transforms. #161 sharpened that finding rather than softening it: making the transforms
5.9x faster made the whole call 3% faster.

#### The multiplication crossover, measured

`multiply` dispatches over three routes by measured threshold — the schoolbook `Mul`, Karatsuba,
then the transform — and the fallback for a field that cannot host a domain is Karatsuba rather
than schoolbook. Where it should switch between Karatsuba and the transform is **not** one number:

| element | Karatsuba base case | transform threshold | measured crossing |
|---|---:|---:|---|
| 4 bytes (KoalaBear) | 48 | **4096** | (2046, 4094] |
| 8 bytes (Goldilocks) | 16 | **512** | (254, 510] |
| 32 bytes (BN254 `Fr`) | 4 | **512** | (254, 510] |

Those thresholds had to be measured against **Karatsuba**, not against schoolbook, and doing so
moved two of the three tiers from where the schoolbook figure would have put them: the 4-byte tier
fell 4x from an unverified 16384, and the 32-byte tier stayed at 512 rather than falling to 256,
because Karatsuba is still 1.18x ahead at product degree 254 there.

```text
cargo run --release --example multiplication_dispatch
cargo run --release --example multiplication_dispatch -- koalabear max_log=17
```

Over **Mersenne-31**, whose two-adicity of 1 rules the transform out at every degree, the fallback
is the whole of what the dispatcher buys: **1.80x** at operand length 16 rising to **11.19x** at
16384, from a route that was previously unreachable there.

The older schoolbook-versus-transform figures are kept below, because they are what the `fftmul`
rows above were taken against. Median of interleaved runs, pinned to one core, product degree
against the ratio of schoolbook to transform time:

| product degree | KoalaBear (4 B) | Zp65537 (8 B) | Goldilocks (8 B) | BN254 `Fr` (32 B) |
|---:|---:|---:|---:|---:|
| 256 | 0.03x | 0.23x | 0.20x | 0.61x |
| 1024 | 0.10x | 0.84x | 0.73x | **2.1x** |
| 2048 | 0.19x | **1.5x** | **1.4x** | 4.1x |
| 8192 | 0.70x | 5.7x | 5.5x | 12.7x |
| 16384 | **1.3x** | 11.7x | 10.4x | 23.6x |

Above 1x the transform is ahead. Schoolbook therefore wins until degree ~460 over a 254-bit field,
~1500 over a 64-bit one, and ~12000 over a 32-bit one — a 26x spread, which is why
`fft_multiplication_crossover::<F>()` is indexed by `size_of::<F>()`. The thresholds those figures
produced — 512, 2048 and 16384 — have since been replaced by the Karatsuba-relative ones above.

Those ratios are medians of 21 interleaved runs pinned to one core, which is what it takes to
resolve a 1.1x difference on this machine; the single-shot sweep above cannot.

The spread is also a finding about the transform rather than about the fields. At degree 16384 it
takes the same 13 ms over KoalaBear, Zp65537 and Goldilocks — three fields whose schoolbook times
at that degree differ by 9x — so this NTT is bound by allocation and recursion, not by field
arithmetic: `evaluate` rebuilds coefficient vectors and splits the domain at every level. The
sweep's `fftmul` row says the same thing in bytes: exponent 1.0 as expected, but a peak of
**26 `n B`** against 4 for schoolbook and 7 for a single `evaluate`, for a computation that is
three transforms. An in-place iterative transform is the work that would move all three crossovers
at once. **#161 did it**, and the re-taken sweep measures `12 n B`; the 26 is the pre-#161 figure,
kept because the ratios in the table above were taken against that transform.

`Mul` covers the first two routes and cannot cover the third. Choosing a domain needs a primitive
`2^k`-th root of unity, which needs `KnownOrder` and a source of randomness — neither of which
`Mul`'s signature can carry, and the first of which the Gröbner core deliberately does not require
of a coefficient type. So the transform is reached through `multiply`, `multiply_above` with an
explicit threshold, or `multiply_over_domain` when one domain serves many products:

```rust
use zeebra::{fields::Zp65537, multiply, FiniteField, Polynomial, UnivariatePolynomial};
use rand::{prelude::StdRng, SeedableRng};

let mut rng = StdRng::seed_from_u64(1);
let a = UnivariatePolynomial::<Zp65537>::new(&[Zp65537::new(1), Zp65537::new(2)]);
let b = UnivariatePolynomial::<Zp65537>::new(&[Zp65537::new(3), Zp65537::new(4)]);

// Degree 2, so this is the schoolbook route — and the same answer either way.
assert_eq!(multiply(&a, &b, &mut rng), &a * &b);
```

Karatsuba owns the band between them. Unlike the transform it needs nothing of the field but a
ring, so it is available over Mersenne-31; at `2^14` it is 10.7x to 22.9x faster than schoolbook,
at a measured exponent of 1.58–1.61 against 2.00, for `6 n B` against `Mul`'s `4 n B`.

```text
cargo run --release --example karatsuba_crossover
```

is the kernel measurement; [`docs/research/fast-univariate.md`](docs/research/fast-univariate.md)
§4.1.1 has the per-width tables and §4.1.2 the dispatched ones.

**`Mul` dispatches too**, since #231: schoolbook below the Karatsuba base case and Karatsuba above
it, so a caller who writes only `a * b` gets the subquadratic route without opting in. Below the
base case it *is* the schoolbook loop, so the operator is bit-identical to what it replaced at
every size.

| stage | KoalaBear | BN254 `Fr` |
|---|---:|---:|
| `roots`, the binding univariate stage | **1.32x–1.67x** | **1.44x–1.66x** |
| `lcm` | 1.17x–1.65x | 1.14x–1.66x |
| `from_zeros` | **2.83x** | 1.04x |
| one product | 2.08x–6.49x | 2.56x–7.31x |
| `div_with_remainder` *(control)* | 0.99x | 1.00x |

Getting there needed two things first, both of which are the interesting part. The agreement tests
in `karatsuba` and `fft::multiply` compared against `&a * &b`, which would have made them check an
implementation against itself, so they were re-based onto an independent oracle in
`test_support`. And dispatching the operator initially measured **0.74x** on `from_zeros` — the
small-product regression the issue predicted — which turned out to be `schoolbook_into` iterating
the longer operand outside; swapping that made the same shape **2.5x** instead. The transform still
cannot live on `Mul`, because choosing a domain needs `KnownOrder` and randomness.

## Multivariate Polynomials

`MultivariatePolynomial<N, F>` is sparse: a monomial-to-coefficient map over `N` variables, held
canonically. No coefficient is ever zero, so the zero polynomial is the empty set of terms and a
monomial whose coefficients cancel is dropped rather than kept at zero. Equality and `Hash` are
over that set, which is why the invariant is not cosmetic — a surviving zero term would make a
polynomial unequal to its own canonical form.

### Multiplication dispatches over four dense layouts and one hash route

Multiplication collects as the products are formed, so the live set is bounded by the output rather
than by the term-product count. *How* it collects is chosen per operand pair, because the choice is
worth 3x–5x and no single answer covers every arity:

| route | index | cells | selected when |
|---|---|---|---|
| `Accumulate` | one hash lookup per product | — | the general case |
| `DenseTriangle` | three integer operations | `(d+1)(d+2)/2` | `N == 2`, dense output |
| `DenseBox` | one add — the index is separable | `∏(d_i + 1)` | dense output, box within 24x the simplex |
| `DenseSimplex` | `2(N-1)` table lookups | `C(d + N, N)` | dense output, otherwise |

The dense routes do no hashing at all: `slots[index(a) + index(b)] += ca * cb` needs no monomial
key. What distinguishes them is that `DenseBox`'s mixed-radix index is **separable** —
`index(a·b) = index(a) + index(b)`, so the left operand's index hoists out of the inner loop and the
per-product cost is one add at any arity — while `DenseSimplex` ranks the monomials of total degree
at most `d` and so allocates the tightest dense array there is, at a non-separable index. The box
pays up to about `N!` in cells for that separability, which is why the crossover between them sits
near five variables rather than being an asymptotic argument.

Measured on one pinned core under `tools/benchlock.sh`, dense `p * p` against the hashing route:

| arity | terms | products | `Accumulate` | `DenseSimplex` | `DenseBox` |
|---:|---:|---:|---:|---:|---:|
| 3 | 2 925 | 8.56e6 | 127.23 ms | 40.95 ms | **23.58 ms** |
| 4 | 715 | 5.11e5 | 7.37 ms | 3.56 ms | **2.35 ms** |
| 5 | 462 | 2.13e5 | 5.66 ms | **1.55 ms** | 1.76 ms |
| 3, degrees (40, 40, 1) | 3 362 | 1.13e7 | 278.83 ms / 17.0 MiB | 61.48 ms / 3.3 MiB | **33.28 ms / 620.9 KiB** |

So there is no arity in this range where the dense accumulator stops being worth it, and the lopsided
trivariate row is where it is worth most: its bounding box is 5 043 cells where its total-degree
simplex is 317 750, so the box is both 8.4x faster and 28x smaller than hashing.

The one shape where generalizing the layout **loses** is one term against many — the Gröbner
reduction inner step. There the products do not collide at all, so there is nothing for a dense
accumulator to merge, and at `N = 3` it costs 55.4 µs against the hash route's 48.6 µs. At `N = 2`
the same shape *wins* (29.1 µs against 44.1 µs) because the triangle's index is three operations, so
this is not a conclusion that transfers between arities. The predicate therefore requires the
product count to be at least twice an upper bound on the output's monomial count before taking a
dense route above `N = 2`, and that threshold is not applied at `N = 2`.

Re-measure any of this with

```sh
cargo run --release --example multivariate_mul                  # every route, per arity and size
cargo run --release --example multivariate_mul -- max_degree=90  # stop short of the six-round size
```

### Add, Sub and scale collect into an operand's own map

`Add`, `Sub`, `Neg` and `scale` **collect into one of their operands' maps** rather than building a
`Vec` of `|a| + |b|` terms and rehashing it into a third map. Which operand is mutated follows the
ownership of the spelling you write, and that is the whole of the optimization:

| spelling | what it allocates |
|---|---|
| `&a + &b`, `&a - &b` | clones one side; for `+` the *larger*, since addition commutes |
| `a + &b`, `a - &b`, `a + b`, `a - b` | nothing — the owned operand's map is merged into |
| `a += &b`, `a -= &b`, `a += b`, `a -= b` | nothing |
| `a.scale(&c)`, `&a * &c`, `&a * c` | clones `a` |
| `a.scale_assign(&c)`, `a * &c`, `a * c` | nothing — the owned polynomial's map is scaled in place |

**`c * a` works too, and allocates what `a * c` does.** The mathematics writes `c·a`, and the
orphan rule is why it took a macro: `impl<F: FiniteField> Mul<MultivariatePolynomial<N, F>> for F`
is rejected, since `F` is a type parameter and so the impl's `Self` type is not local. The impls
are therefore generated per field **struct** — `PrimeFieldElement64<P>` is local for every `P`, so
six invocations in `src/left_scalar_mul.rs` cover every prime, binary modulus and extension the
crate names. Each left-hand spelling delegates to the right-hand one with the *same* ownership, so
`c * a` on an owned `a` reaches `scale_assign` rather than cloning. `scale` stays the route for
code that is generic over `F`, which none of this is reachable from.

It covers `UnivariatePolynomial`, `MultivariatePolynomial`, `Matrix` and `Vector`.

So an accumulator you own grows in place:

```rust
use zeebra::{fields::Zp13, FiniteField, MultivariatePolynomial, Zero};

let vars = ["x", "y"];
let words: Vec<MultivariatePolynomial<2, Zp13>> = ["x^2 + y", "x*y - 1", "y^2 + x"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, vars).unwrap())
    .collect();
let row = [Zp13::new(3), Zp13::new(5), Zp13::new(7)];

// The linear layer of a symbolic permutation: no sum is ever built twice.
let folded = row
    .iter()
    .zip(&words)
    .fold(MultivariatePolynomial::zero(), |acc, (m, word)| acc + word.scale(m));

assert_eq!(
    folded,
    MultivariatePolynomial::parse("3*x^2 + 5*x*y + 7*y^2 + 7*x + 3*y + 8", vars).unwrap()
);

// Scaling by zero is the zero polynomial held as no terms, not as zero coefficients.
let mut vanishing = words[0].clone();
vanishing.scale_assign(&Zp13::zero());
assert!(vanishing.is_zero());
assert!(vanishing.terms().is_empty());
```

### Aliasing

The in-place forms mutate the left operand and never the right, and the borrow checker rules out
the one case that would be ambiguous: `a += &a` does not compile, because `&mut a` and `&a` cannot
coexist. Self-assignment is therefore spelled through a clone — `a += a.clone()` doubles, and
`a -= a.clone()` is the empty polynomial, not a map full of zeros.

What this buys is measured in `tests/multivariate_add_memory.rs` and
`tests/multivariate_mds_fold_memory.rs`, which assert it rather than quoting it. Summing two
11 476-term triangles that cancel to a single term allocates **0 bytes** against **594 944** for
the form that materialized every term, because every merge lands on a monomial already present and
the table never grows — the live set is the output. Folding eight scaled words into one accumulator
peaks at **43 312 bytes** against **84 448**; there the output has to be allocated, so the 2x is
all there is to win.

They are two binaries rather than two tests because the peak is read off a process-wide tracking
`#[global_allocator]`: any allocation anywhere in the process raises it, so a second test's operand
construction lands in the first test's measurement whatever lock guards the measured region. One
test per binary is the only arrangement that makes the counters mean what they say.

### GCD, content, and squarefree decomposition

`F[x_0, ..., x_{N-1}]` is not Euclidean, so `gcd` is recursive: read both polynomials as univariate
in their highest occurring variable, over the polynomial ring in the remaining ones. That
coefficient ring is a UFD and not a field, so the Euclidean step is *pseudo*-division — scale the
dividend by a power of the divisor's leading coefficient instead of dividing by it — and the
content comes out of every remainder, which is what keeps those powers from accumulating. The
classical primitive PRS. The recursion terminates because the coefficients of a polynomial read in
`x_v` do not involve `x_v`, so each content is a GCD in a strictly smaller ring.

| method | what it gives |
|---|---|
| `gcd(&other)` | the GCD, normalized so the lexicographic leading coefficient is one |
| `gcd_by(&other, route)` | the same, by a named `GcdRoute` |
| `content(i)` / `primitive_part(i)` | the GCD of the coefficients in `x_i`, and the quotient by it |
| `degree_in(i)` / `coefficients_in(i)` | the univariate-in-`x_i` view the recursion is built on |
| `exact_div(&divisor)` | the quotient, or `None` when the division leaves a remainder |
| `derivative(i)` | the formal partial derivative |
| `squarefree_part()` / `squarefree_decomposition()` | the radical, and the factors with multiplicities |
| `squarefree_decomposition_by_radicals()` | the reference route the above is tested against |
| `pth_root()` | the `p`-th root of a `p`-th power, or `None` |

```rust
use zeebra::{fields::Zp13, MultivariatePolynomial};

let vars = ["x", "y"];
let parse = |s| MultivariatePolynomial::<2, Zp13>::parse(s, vars).unwrap();

// Two products sharing one factor.
let shared = parse("x + y");
let f = &parse("x - y") * &shared;
let g = &parse("x*y + 1") * &shared;
assert_eq!(f.gcd(&g), shared);

// Coprime inputs have GCD one, and a nonzero constant is a unit.
assert!(parse("x + 1").gcd(&parse("y + 1")).is_one());

// Read in y, x*y^2 + x is x*(y^2 + 1): the content is x and the primitive part y^2 + 1.
let h = parse("x*y^2 + x");
assert_eq!(h.content(1), parse("x"));
assert_eq!(h.primitive_part(1), parse("y^2 + 1"));

// (x + 1) * (y + 1)^2, decomposed by multiplicity.
let repeated = &parse("x + 1") * &(&parse("y + 1") * &parse("y + 1"));
let mut decomposition = repeated.squarefree_decomposition().unwrap();
decomposition.sort_by_key(|(_, multiplicity)| *multiplicity);
assert_eq!(decomposition, vec![(parse("x + 1"), 1), (parse("y + 1"), 2)]);
```

#### Characteristic `p`, where the derivative is blind

Differentiation multiplies a factor of multiplicity `e` by `e`, and in characteristic `p` that is
zero whenever `p` divides `e`. So `f / gcd(f, ∂f/∂x_0, ..., ∂f/∂x_{N-1})` is **not** the radical
in general: for `f = ∏ g_i^(e_i)` that GCD is
`∏_{p | e_i} g_i^(e_i) * ∏_{p ∤ e_i} g_i^(e_i - 1)`, so the quotient is the product of only the
factors whose multiplicity `p` does not divide. Over GF(2) every *even* multiplicity is invisible,
and over GF(2) and GF(2^8) is where this crate runs the whole solving pipeline.

Both are nonetheless computed, because the decomposition exists in characteristic `p` and only the
*method* was restricted. What the GCD leaves is `∏_{p | e_i} g_i^(e_i)`, in which every
multiplicity is a multiple of `p` — so it is a `p`-th power, `pth_root` takes the root exactly, and
recursing on the root finds those factors with their multiplicities divided by `p`. The only
refusal left is the zero polynomial, which is divisible by every square.

```rust
use zeebra::{fields::Zp2, MultivariatePolynomial, SquarefreeError};

let vars = ["x", "y"];
let parse = |s| MultivariatePolynomial::<2, Zp2>::parse(s, vars).unwrap();

// Over GF(2) the whole gradient of x^2 vanishes, and the factor is recovered anyway.
let x = parse("x");
let square = &x * &x;
assert!(square.derivative(0).is_zero() && square.derivative(1).is_zero());
assert_eq!(square.squarefree_decomposition().unwrap(), vec![(x.clone(), 2)]);

// A visible multiplicity and an invisible one in the same polynomial.
let shifted = parse("x + 1");
let f = &square * &(&shifted * &(&shifted * &shifted));
let mut decomposition = f.squarefree_decomposition().unwrap();
decomposition.sort_by_key(|(_, multiplicity)| *multiplicity);
assert_eq!(decomposition, vec![(x, 2), (shifted, 3)]);

// The zero polynomial is the only refusal.
assert_eq!(
    MultivariatePolynomial::<2, Zp2>::zero().squarefree_part(),
    Err(SquarefreeError::Zero)
);
```

The visible half costs **one GCD per multiplicity**: with `P_1` the visible part and
`Q_1 = f / P_1`, the ladder `P_{j+1} = gcd(P_j, Q_j)`, `Q_{j+1} = Q_j / P_{j+1}` has `P_j` the
product of the visible factors of multiplicity at least `j`, so `P_j / P_{j+1}` is the one of
multiplicity exactly `j`. `squarefree_decomposition_by_radicals` is #128's repeated-radical form,
kept as the reference the two are differentially tested against: it pays a whole radical — `N + 1`
GCDs over operands that do not shrink — for each multiplicity, and it still refuses in small
characteristic, which is a true statement about *that* method.

**Not Yun's algorithm, deliberately.** Yun's recurrence is univariate; generalized to `N` variables
honestly it carries a `d_i` per variable and needs `gcd(b_i, d_i^(0), ..., d_i^(N-1))` — `N` GCDs
per multiplicity, worse than the ladder and no better than the radicals it was meant to replace.
The ladder reaches the cost Yun's is wanted for with the gradient taken once rather than once per
level.

The GCD's correctness is pinned by an exhaustive check rather than by a reference implementation:
over a two-variable ring on a three-element field, `multivariate_gcd.rs` enumerates every candidate
divisor and asserts the defining property — the result divides both inputs, and *every* common
divisor divides the result. That is the property to test, because a GCD is only unique up to a unit
and several candidates share the maximal degree.

#### Two remainder sequences

`GcdRoute` picks which polynomial-remainder sequence the Euclidean step runs. Both are the same
recursion and return the same value — a reduced GCD is unique once normalized — and differ only in
what they do to a pseudo-remainder before the next step.

| route | per step | coefficient bound |
|---|---|---|
| `PrimitivePrs` | divide out the content, which is a recursive GCD | by construction: nothing grows |
| `SubresultantPrs` (default) | divide by `g * h^delta`, one exact division | by a theorem: the entries are subresultants |

Collins' subresultant PRS carries `g = lc(a)` and `h = h^(1-delta) * g^delta` across steps, and the
fundamental theorem of subresultants is what makes the division by `g * h^delta` exact. The entries
of the sequence then *are* subresultants — determinants of submatrices of the inputs' Sylvester
matrix — so Hadamard's inequality bounds them in terms of the inputs alone. The primitive PRS
instead makes every remainder primitive, which cannot grow at all, and pays a recursive GCD in a
smaller ring for each step.

It needs a pseudo-remainder with **exactly** `delta + 1` powers of the divisor's leading
coefficient, which is what the theorem is stated over. The primitive route's pseudo-remainder
multiplies once per division *step*, and a step that skips a degree leaves the power short —
`x^6 + 1` against `x^2 + 1` takes three steps where `delta + 1` is five — so the two
pseudo-remainders are not interchangeable and the subresultant route has its own.

**The subresultant route is the default on correctness evidence, not on a measurement.** The two
are asserted to return the same value by the exhaustive brute force, by `for_each_field!` at two
arities, and case by case including the degree-gap cases. What is also asserted is the *operation
count*: on a degree-five-against-degree-two pair the primitive route takes 18 recursive content
GCDs and the subresultant route 6. That is a count and not a duration. **No timing is published
for either route**, and whether the wall clock follows the operation count on any particular
machine is exactly what has not been measured.

Brown's modular algorithm — evaluate all but one variable at points over a prime field, take
univariate GCDs, interpolate back, with degree bounds and a check against bad evaluation points —
is the route that changes the asymptotics and is not implemented.

### Composition

`compose_univariate` substitutes one univariate polynomial per variable, `x_i -> g_i(x_i)`, and
`compose` is the general form, replacing each `x_i` by a polynomial in all `N` variables at once.
Both are simultaneous rather than sequential: a substitution's own variables are not themselves
substituted. `from_univariate(i, &g)` is the lift the univariate form is built on — the same `g`
read as a polynomial in variable `i` alone.

A round of a sponge permutation is exactly this shape: an S-box `x -> x^d` per state word followed
by an affine layer.

```rust
use zeebra::{fields::Zp13, FiniteField, MultivariatePolynomial, Polynomial, UnivariatePolynomial};

let vars = ["x", "y"];
let p: MultivariatePolynomial<2, Zp13> =
    MultivariatePolynomial::parse("x^2*y + 3*x + 2", vars).unwrap();

// x -> x + 1, y -> y^2, written as coefficients in ascending order.
let shift = UnivariatePolynomial::new(&[Zp13::new(1), Zp13::new(1)]);
let square = UnivariatePolynomial::new(&[Zp13::new(0), Zp13::new(0), Zp13::new(1)]);
assert_eq!(
    p.compose_univariate(&[shift, square]),
    MultivariatePolynomial::parse("x^2*y^2 + 2*x*y^2 + y^2 + 3*x + 5", vars).unwrap()
);

// The general form can mix variables: x*y under x -> x + y, y -> x - y is x^2 - y^2.
let product: MultivariatePolynomial<2, Zp13> = MultivariatePolynomial::parse("x*y", vars).unwrap();
let sum = MultivariatePolynomial::parse("x + y", vars).unwrap();
let difference = MultivariatePolynomial::parse("x - y", vars).unwrap();
assert_eq!(
    product.compose(&[sum, difference]),
    MultivariatePolynomial::parse("x^2 - y^2", vars).unwrap()
);
```

Degree grows multiplicatively — `deg(p(g_0, ..., g_{N-1}))` is bounded by the largest
`sum_i e_i * deg(g_i)` over the monomials `x^e` of `p` — so forming the powers `g_i^(e_i)` is where
the work is. They are memoized per variable and built by repeated squaring, which makes a distinct
exponent `e` cost `O(log e)` multiplications and a repeated one cost none. Cancellation is handled
by the same canonical invariant as everything else: a composition that collapses returns the zero
polynomial as no terms at all.

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
cargo run --release --bin zeebra-differential -- --fields 2^8/283 --seed 3780 --systems 40 \
    --max-degree 4 --max-terms 5 --fixture-table FIXTURES_GF256 \
    --fixtures src/grobner/differential/fixtures_gf256.rs   # the GF(2^8) table
```

**`--fields` names a field and not a characteristic**, because a characteristic does not determine
one: `GF(2)` and `GF(2^8)` share it, and `2^8/283` and `2^8/285` are two fields of the same order in
which the same byte has two different squares — `Gf256` and `Gf256Mq`. A case records its modulus,
and the modulus is *asserted* to agree on both sides rather than assumed: Zeebra's end by
multiplying (`x^m = r` determines `P = x^m + r`, so one exponentiation accepts exactly one modulus),
and Singular's by declaring `ring R = (2,a),...` with an explicit `minpoly` — its own `(2^8,a)`
Galois fields take theirs from an internal table a script cannot choose — and comparing the echo.
A ring reducing by something else is an oracle failure and never a comparison. `--characteristics`
is still accepted as the old name, so the committed tables' regeneration commands keep running.

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

### Other external engines, for comparison

Singular is the oracle above because it is the one this repository has always had installed.
Three more comparands — **msolve**, **Groebner.jl** and **Sagebrush** — are provisioned into a
user prefix by one script, with pinned versions and no root:

```sh
tools/external/provision.sh          # ~5 min cold, 0.2 s warm; no root needed
. tools/external/env.sh              # PATH, LD_LIBRARY_PATH, JULIA_DEPOT_PATH
tools/external/smoke/smoke.sh        # all four on one system; non-zero exit on disagreement
```

Nothing is linked and nothing is vendored: every one of them is run as a **separate process**,
which is what makes a GPL engine usable from an MIT crate at all. The rules are
`docs/research/external-provenance-policy.md`; what got installed, how to invoke each tool for a
basis, for an eliminant and for solutions, what each one means by "degrevlex", the prime-field
ceilings (msolve and Singular both stop at 2^31 − 1), and the smoke-test agreement are in
`docs/research/external-comparands.md`.

Each engine is driven through one trait, `grobner::external::ExternalSolver`, behind the
`external-runners` feature — on by default, and adding no dependency, because the interface to
every one of these tools is text. **Zeebra goes through the same trait**, so the in-crate row
cannot acquire a privilege the subprocess rows lack — including the refusals: `ZeebraSolver` serves
the basis, lex-basis, conversion and univariate-eliminant tasks and refuses the two solution tasks
(no comparand offers either) and the cryptanalytic witness (it belongs to the other scoreboard).
The eliminant is served as the *projection* it is — `I ∩ k[x_n]` is generated by the one element of
a reduced lex basis involving no other variable — so it adds no algorithm; it was previously refused
alongside the solution tasks under a reason that was true for them and false for it, which left the
one task with two external engines and no in-crate operand (#465). Note the field that comparison
lives at: msolve's eliminant bound is below 2^31 − 1, so it is the corpus's `2^30 + 3` and not the
reference prime, and `ZeebraSolver` compiles the ladder's dimensions at both for that reason.
`msolve::tests::test_a_real_msolve_and_zeebra_return_the_same_eliminant` compares the two
engines' eliminants as **polynomials** rather than as text.

`SingularSolver` is the reference adapter and `MsolveSolver` the one with the most to say:

```rust
use std::time::Duration;
use zeebra::grobner::external::{ExternalSolver, FieldSpec, Instance, Limits, MsolveSolver, Task};
use zeebra::MonomialOrder;

let mut solver = MsolveSolver::new("msolve", std::env::temp_dir().join("zb-msolve-doc"));
let instance = Instance::new(
    "pair",
    "doc",
    FieldSpec::prime(1073741827),
    vec!["x".to_string(), "y".to_string()],
    vec!["x^2-2".to_string(), "y-x-1".to_string()],
    MonomialOrder::GradedReverseLexicographic,
);

// Capability is answered without running anything, and a `no` is never a timing.
assert!(solver.supports(&instance, Task::ReducedGrobnerBasis).is_supported());
// msolve has no lex order at all, so a lex basis is a capability gap rather than a slow row.
assert!(!solver.supports(&instance, Task::LexBasis).is_supported());

// An absent binary is reported, never fatal — so a sweep continues past it.
let report = solver.run(&instance, Task::ReducedGrobnerBasis, &Limits::wall(Duration::from_secs(30)));
assert!(report.status.answered() || report.was_skipped());
```

`RunReport::was_skipped()` is true for the three outcomes that mean **the tool did not run**:
`Unsupported` (the input is unrepresentable), `RunFailure::Unavailable` (the tool is absent) and
`RunFailure::Environment` (the harness's own environment would have invalidated the measurement).
The last is why it exists: an adapter can set a child's environment but cannot *clear* it, so an
inherited switch that selects a different algorithm — or writes a trace into the stream the basis
is parsed from — cannot be undone from inside the run, and the honest answer is to refuse rather
than to measure something no user of the tool gets. It is deliberately not `Reported`, which means
"the tool printed an error"; there was no execution to print one. The variant names the variable so
an operator knows what to unset and the effect so the refusal can be judged. Sagebrush has seven
such switches (`sagebrush::PINNED_SWITCHES`), every one read with `env::var(..).is_ok()` — truthy
if set, so `SB_SIGF4=0` *enables* the experimental signature path.

Two msolve-specific facts the adapter encodes as named constants, because both are capability
bounds rather than slow paths and both are narrower than they look:

* `msolve::MAX_CHARACTERISTIC` is `2^31` — a basis works for any `p` below it.
* `msolve::MAX_CHARACTERISTIC_ELIMINANT` is `1515531529`. msolve's sparse-FGLM refuses primes at
  or above `1518500213` and its genericity handler then retries **without bound** rather than
  failing, so the eliminant task is refused instead of being allowed to burn a wall limit; the
  constant is the tighter *documented-safe* accumulation bound rather than msolve's own guard,
  because primes between the two run with no accumulation guarantee. `Mersenne31` and
  `Zp2147483647` are both above it.

msolve also has **three** failure modes that exit 0. On a staircase that is not generic enough it
permutes the variables and appends a new one carrying a random linear form, then writes a
well-formed parametrization of the ideal it substituted — so the adapter compares the output's
variable list against the instance's on every run. Its sparse-FGLM refuses a too-large prime and
then retries forever rather than failing. And a generator naming a variable that is not on line 1
has that factor **silently dropped**, so `supports()` checks every identifier in every generator
against the declared order before anything runs.

That last one is also why msolve is safe at ten or more variables, where `x1` is a prefix of `x10`:
it matches factor names with a full `strcmp` rather than greedily, verified by handing it 53
distinct degree-2 monomials over `x1..x14` and getting the same set back. Cross-engine agreement
cannot catch a tokenizer bug — every engine is handed the same bytes, so all of them agree on the
same wrong ideal — which is why that check is against the input rather than against another tool.

All three, the mapping from msolve's F4 stage names onto Zeebra's, and what of its design is worth
reimplementing are in `docs/research/msolve-implementation.md`.

The msolve adapter's corpus agreement test builds **Zeebra's side by parsing the rung's own text**
and dispatching on **variable count**, so a corpus family added at a width already present — 4, 5,
6, 7, 10 or 14 — gets an oracle with no edit. It is also the stronger check: the bytes parsed are
the bytes every engine is handed, so a round-trip failure in either direction shows up as a
disagreement rather than as a silently different problem. The rungs with no oracle are only the
Poseidon and Anemoi ones, which carry their own fields (KoalaBear and `2^64 - 353`) and so need a
second field *type* rather than a second match arm.

That test is not `#[ignore]`d — it runs whenever msolve is installed — so by default it builds
oracles only up to seven variables, which is 1.4 s for nine rungs where `mq-random-10` alone did
not finish in ten minutes. **`ZEEBRA_FULL_CORPUS_ORACLE=1` lifts that ceiling** for a machine that
wants the ten- and fourteen-variable rungs covered. Rungs left out are printed with the remedy,
never silently dropped. (`F4Options::max_wall_time` does not substitute for the ceiling: it is
checked once per batch, so one long matrix reduction overruns it.)

`GroebnerJlSolver` and `SagebrushSolver` are built the same way, and both read what
`tools/external/env.sh` exports: `GroebnerJlSolver::from_env(work_dir)` and
`SagebrushSolver::from_env(work_dir)`. Two things about them are worth knowing before reading
a figure from either.

**Groebner.jl's process wall time is a measurement of the Julia compiler.** On the smoke system it
is 5.47 s against an inner `groebner` call of 0.18 ms. The adapter therefore warms the JIT on a
proxy system in the same ring and reports the *timed call* as the run's wall time, keeping the
process wall and CPU as stages so nothing is excluded without being recorded; the measured residue
after the warm-up is about 0.17 ms, an absolute constant rather than a factor. It is the one
adapter in the module where `wall` is not the process's, and
`src/grobner/external/groebner_jl.rs` says so at the top.

**Sagebrush is the only permissively licensed comparand, and the only one with no release.** It is
five weeks old, every engine crate is `0.1.0`, its `f4.rs` carries six tests, and no committed
oracle run in its own repository exercises the elimination. It also agrees with Zeebra **term for
term, every coefficient included** on every Katsura and Cyclic rung of the shared corpus, plus the
reference smoke system, a 62-bit prime and a fourteen-variable system — ten instances — and across
the full ladder — eighteen rungs then, twenty-six since #424 — it has **disagreed with nothing**. Both halves belong in any table that
quotes it: report its rows with the pinned SHA, and do not make it the denominator of a headline
speedup. The verdict is `docs/research/sagebrush-implementation.md` §6.3.

**It is also the only comparand that offers both routes to a lex basis.** The driver takes
`--order lex|deglex|degrevlex` and `--route f4|fglm`, so `SagebrushSolver` covers
`ReducedGrobnerBasis` under any of Zeebra's three orders, `LexBasis` by the engine's direct lex F4,
and `LexBasisByConversion` by `fglm::groebner_fglm` — which gives that last task a second comparand
beside Singular, Groebner.jl 0.10.11 having no FGLM at all. The two routes are deliberately
separate tasks: they return the same basis by different algorithms, so a column that mixed them
would compare two complexities under one heading, and the adapter checks the driver's echoed
`#route:` line on every run for exactly that reason. FGLM carries its **own** field ceiling of
`2^31`, an eighth of the basis route's `2^62`, and the adapter declares it per task rather than
letting a sweep discover it as a wall-clock stop.

Neither tool confuses `x1` with `x10`, which matters because the corpus has fourteen-variable
rungs and **cross-engine agreement cannot catch a tokenizer bug** — every engine is handed the same
bytes, so all of them would agree on the same wrong ideal. **Both adapters now check their echoed
generators against the sent system on every run**, comparing canonical term multisets so that
`x1*x10-1` and `1*x1*x10 + 1073741826` count as the same polynomial, and reporting a mismatch as
`RunFailure::SelfInconsistent`. So a `Complete` status on a fourteen-variable rung is itself the
proof, for Groebner.jl's `@gen` echo and for the Sagebrush driver's `#gen` echo alike. The
behavioural test remains, because it checks the *consequence* in the computed basis and would still
fail if a parser read the system correctly and then packed it wrongly.

Because the Sagebrush driver lives in the provisioning prefix rather than in this repository, it
prints a `#driver contract:` version that the adapter **requires**: an adapter that checked the echo
only when it happened to be present would silently stop checking against an older installed binary,
which is worse than not checking at all. A driver predating the marker fails with
`RunFailure::Incomplete` naming `tools/external/provision.sh`, so the remedy is in the error.

The agreement checks are live tests, `#[ignore]`d because CI has neither tool installed and a test
that silently passed when the tool is absent would be worse than no test:

```sh
. tools/external/env.sh
cargo test --release --test external_comparands -- --ignored --test-threads 1
```

What is inside each engine — Groebner.jl's monomial encodings, hashtable and learn/apply traces,
and which of those are msolve's rather than its own; Sagebrush's F4, its 2^62 modulus ceiling, and
what reusing any of it would require — is in `docs/research/groebner-jl-implementation.md` and
`docs/research/sagebrush-implementation.md`.

`tools/external/groebner-jl-counts.jl` takes the other side of the comparison: it reads the
canonical text of a digest-pinned instance (`f4_profile -- mq-instance`), rebuilds it in the same
ring and ordering the adapter uses, and reports **Groebner.jl's own** pair, matrix and row counters
plus its per-stage split — the latter by enabling the package's own `TimerOutputs` timer at runtime,
which needs no patched build. It is a measurement instrument on no build path, and
`docs/research/groebner-jl-gap.md` is what it produced: the 348x on `mq-random-10` decomposed into
randomized linear algebra (4.89x, declined by policy), interreduction done by division rather than
by one Macaulay matrix (5.03x), and a per-operation representation constant (14.0x).

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

**`DisclosedMethod` is separate from `ExternalStatus`.** A program can verify a submission without
naming the submitter, and a paper can describe an attack at the same parameters without being that
submission — so "verified on this date" and "this is how it was done" are two claims, and the
registry keeps them apart:

```rust
use zeebra::grobner::research::{challenge, DisclosedMethod};

// The R_P = 8 target was solved by a univariate route, published by Sanso and Vitto.
let rp8 = challenge("poseidon31-cico-rf6-rp8").expect("registered");
match rp8.method {
    DisclosedMethod::Published { method, attributed_to_submission, .. } => {
        assert!(method.contains("Graeffe"));
        // The program does not name first submitters, so this is an attack at the same
        // parameters and not, on the present evidence, *the* verified submission.
        assert!(!attributed_to_submission);
    }
    other => panic!("expected a published method, got {}", other),
}

// R_P = 10 is solved and verified externally, and no method has been published. `Unknown` is the
// honest value; it is not a synonym for brute force or for anything else.
let rp10 = challenge("poseidon31-cico-rf6-rp10").expect("registered");
assert_eq!(rp10.method, DisclosedMethod::Unknown);
```

Disclosing a method never changes a problem's identity, which
`test_disclosing_a_method_does_not_change_identity` pins.
[`docs/research/elimination-beyond-grobner.md`](docs/research/elimination-beyond-grobner.md) §2 has
every published method and its reported cost.

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

**Reading an `environment.policy` written before #469.** Those records say `400 MB live`, and the
budget that actually bound was **320 MB**: the runner set `max_live_bytes` to 400 MB and left
`max_live_nonzeros` at its default 20 000 000, and the effective limit is the `min` of the two
(#322) — 20 000 000 entries over the 16-byte entry every row on this board uses. So a
`stopped_at_limit` row from before #469 must be reconciled against 320 MB, not against the figure
its own policy string quotes. Nothing about those runs or their timings changed; the overstatement
was in the prose alone, which is why the records are left as emitted rather than rewritten by hand
(#334). Since #469 the string is derived from the options by `F4Options::live_budget_policy`, which
reports the allowance that binds and names the budget it came from, so the two cannot drift apart
again.

#### The cost model: predicted against measured, with the difference attributed

```bash
cargo run --release --example cost_model                  # render research/cost-model/COST-MODEL.md
cargo run --release --example cost_model -- --write       # regenerate the register from its records
cargo run --release --example cost_model -- --write --seed  # append any transcribed row not yet held
```

`grobner::research::cost_model` keeps one row per **claim** about what a stage would cost, against
what it cost. Every figure carries a `FigureBasis` — `Measured`, `Fitted`, `Predicted` or
`Extrapolated` — because the failure it exists to prevent is documented rather than hypothetical:
M24 found that every prediction about a stage already measured held, and every prediction about an
unmeasured quantity was wrong, three of four by more than an order of magnitude, because all ten
were written in the same prose with the same confidence. A `measured_` field holds only a measured
figure and a `predicted_` field never holds one; a row violating either does not load.

Three further rules are code rather than convention. **Peak allocated and peak resident do not
share a column**, since #237 measured 21 674 MiB allocated against 13 996 MiB resident on one row.
**The resource-limiting stage is a closed set**, so "memory" and "the monomial queue of one refused
batch" cannot be written in the same field. **Prediction error is derived** — nothing in
`research/cost-model/results/history.json` is an error column, and `CostRow::prediction_errors`
computes it from the predicted and measured fields. The history is append-only: a re-measurement is
a new row with a new commit, which is what keeps #318's two figures for the same measurement both
visible.

#### Elimination that is not a Gröbner basis

`grobner::research::bivariate_resultant` computes `Res_y(f, g)` for two bivariate polynomials, as
the determinant of their Sylvester matrix recovered by interpolating scalar determinants;
`bivariate_resultant_ntt` computes the same resultant with the samples taken on a power-of-two
subgroup, so the recovery is an inverse NTT rather than a cubic solve. The
determinant construction needs no case analysis: evaluating a matrix and taking its determinant
commutes with evaluation *always*, where specializing `f` at a point that kills its leading
coefficient in `y` drops its degree, and the specialized resultant is then not the specialization of
the resultant.

**Which per-sample kernel evaluates that scalar is now a choice**, `ResultantOptions::kernel`:

- `DeterminantKernel::Dense` — dense LU on the `(m + n)`-square matrix, `O(n³)`. The **default**, so
  a figure taken before the alternative existed reproduces unchanged.
- `DeterminantKernel::Euclidean` — `poly::resultant_from_coefficients`, driving `f mod g` down the
  polynomial remainder sequence in `O(n²)`.

Both return the same scalar, including at the specialization points, where the fixed Sylvester order
and the fallen true degrees differ by a correcting power of a leading coefficient — the case analysis
the dense route avoids, closed in `O(1)` per sample by `poly::resultant_at_formal_degrees` and
asserted against an explicitly built determinant over all 15 625 degree-drop combinations. Measured
same-binary on one pinned core, the Euclidean kernel is **137× faster at order 162 and 2 094× at
order 1 458**, with fitted exponents of **2.94** and **1.85** — the ratio grows with the order
because the kernels differ by a power of it. It does **not** raise the reachable round count: the
six-round route becomes 78% root finding, so the row gains ~3×. See
`docs/research/structured-sylvester.md` §5.6.

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
affordable.

**The four-round rows now complete, with verified witnesses** — `poseidon31-cico-t16-rf2-rp2` in
about 40 s and `-rf4-rp0` in about 41 s, where F4 stops at two rounds and this route previously did
too. Each witness is checked by `CicoInstance::is_solution`, which runs `permutation_plus_linear`;
the coordinates are committed under `research/witnesses/` and re-checked by the test suite. The
enabling change is #162 making `lagrange_interpolate` quadratic. The route's own limit is still
arithmetic — about `16 · 3^{5·rounds}` field operations, now almost entirely the determinants — so
six rounds remains `3.3 × 10^15` and out of reach.

`bivariate_resultant_ntt` moves where the samples are taken: the *same* Sylvester determinants on a
power-of-two multiplicative subgroup, recovered with one `fft::interpolate`, with
`interpolation_route` falling back to `bivariate_resultant_reference` on a field whose two-adicity
admits no domain — Mersenne-31's is 1. **Single-threaded it is measured slower than the reference,
by 1.23x–1.40x**: the sample count goes as `2d²` and each sample is an order-`2d` determinant, so
determinant work grows as `d^5` against a quadratic interpolation's `d^4`, and padding 13 123
samples up to 16 384 costs 10.4 s of determinants to remove 1.5 s of interpolation. Both routes are
retained and `examples/resultant_cico.rs` runs them side by side in one process.

**That sign flips under concurrency, and retaining both routes is why it could be seen.**
`ResultantOptions::concurrency` spreads the independent determinants over worker threads and
defaults to 1, so every figure above reproduces unchanged. The samples are written into their own
index rather than collected as they finish, so the recovered polynomial does not depend on the
worker count — asserted byte-identical, with the identical witness set, at 1, 8 and 32. Measured on
a 32-core pinned set under the benchmark lock, the four-round determinant stage runs at **92–95%
parallel efficiency out to 32 of this box's 128 cores**, taking `rf2-rp2` end to end from 49.7 s to
**2.16 s**. The shortfall is the all-core clock and not bandwidth: per-determinant core time steps
up 4% once eight cores are busy and is then flat to 32, and the live working set is 27 MB against a
256 MB L3. The subgroup route then *wins* by 1.7–1.8x, because its extra determinants parallelize
and the reference route's 1.6 s Lagrange solve does not — at 32 workers the reference route is more
than half serial interpolation.

Timings carry the concurrency onto the scoreboard rather than hiding it. `Environment::concurrency`
is recorded on every run and reads back as 1 for records written before it existed;
`Comparison::of` **refuses** two runs that disagree on it, with `DifferentConcurrency`, since the
ratio would be a core count rather than a speedup; and `Scoreboard::best` — the headline the
rendered table quotes — considers uncontended runs only, so a 30x of cores cannot displace the
single-core figure it is not comparable with. `Scoreboard::best_at` reaches the parallel rows on
purpose.

Two other results from the same run: the resultant's degree matches the **published, unproven**
`d^{2R_F+R_P}` on all three rows measured — 729 against a Bézout bound of 6 561 on the row with
partial rounds — and that makes the sample count predictable rather than merely loose. See
[`docs/research/resultant-elimination.md`](docs/research/resultant-elimination.md).

`bivariate_resultant_predicted` acts on that. `predicted_resultant_degree(alpha, r_f, r_p)` returns
`alpha^(2 R_F + R_P)` from the instance's own parameters, and the route samples one point more than
that rather than the Bézout-sized `2d²` — **730 determinants instead of 13 123** on
`poseidon31-cico-t16-rf2-rp2`, and 6 562 instead of 13 123 on `-rf4-rp0`. Against the 16 384 the
subgroup route used by default those are 22.4x and 2.5x. The predicted count is not a power of two,
so it pairs with arbitrary-point Lagrange and not with an NTT domain, which would round 730 up to
1 024 and return a third of the saving.

The formula is **experimental and unproven in its source**, so the route validates rather than
trusts it: the recovered polynomial is checked against a direct Sylvester determinant at points the
interpolation never sampled, the check is part of the route rather than a flag —
`ResultantOptions::with_off_domain_checks(0)` panics rather than disabling it — and on disagreement
the proven `2d²` path produces the answer with `DegreeSource::PredictionFalsified` recording that
the published formula did not hold on that row. A falsification would be a result worth more than
the samples it saved, so it is recorded rather than silently repaired.

The check's own determinants go over the **same** worker pool as the interpolation's samples:
`off_domain_abscissae` is pure in the sample count and the fixed seed, so the points are drawn
before anything is evaluated and then partitioned through the one indexed `sample_determinants`
loop. At order 1 458 eight checks measure 19.97 s serial against 2.82 s at eight workers, which
takes a six-round row's validation share from 3.1% to 0.5%. Every check is evaluated before any is
compared, so the verdict cannot depend on which worker finished first, and the draws are distinct
rather than merely off-domain. It remains a **probabilistic consistency check and not a proof of a
polynomial identity** — eight agreements bound the failure probability by `(bound/p)^8`, which is
`4 × 10^-27` at six rounds: overwhelming evidence, and not the certificate that the proven-bound
routes get from uniqueness of interpolation.

`examples/resultant_cico` selects what it attempts: `--row <challenge-id>` (repeatable),
`--max-samples` and `--wall-budget`, with a row over either **costed and skipped** and its
arithmetic printed. `--build-only` times `cico_bivariate` alone, which is the bounded measurement a
row past the budget still supports. There is no `--all` — it removed the guard entirely, which put
a 12.9-day row beside a bounded one.

What the guard costs a row with is **measured rather than assumed**. `examples/determinant_sweep`
times the Sylvester determinant kernel at orders 18, 162, 486, 1 458 and 4 374 on random bivariate
pairs and fits a power law with per-point residuals, and the answer is piecewise: above the L2
footprint the exponent is **2.9953 ± 0.0285** with a worst residual of 3.7% — cubic to within the
measurement, including at order 4 374 whose 153 MB matrix exceeds a CCX's L3, so there is no cache
cliff to model — and below it 2.79, which is fixed per-determinant overhead the small orders cannot
amortize. `determinant_core_ms` takes the **larger** of the fitted and cubic laws, because 2.9953 is
below 3 and a cost model that under-predicts authorizes a run nobody costed, times a measured
core-time penalty for running wide (2.404 s, 2.821 s and 3.148 s a determinant at order 1 458 on 1,
8 and 32 workers). The six-round rows come out at 12.0 min (`rf2-rp4`), 1.79 h (`rf4-rp2`) and
16.15 h (`rf6-rp0`) on 32 workers; the eight-round rows at order 13 122 are 490 and 4 415 days, out
of reach by three orders of magnitude rather than by a factor the sample count could recover. See
[`docs/research/resultant-elimination.md`](docs/research/resultant-elimination.md) §6.9, which also
records that the figures on record are about 1.2x faster than the same measurements today, and that
the 2.868 ms order-162 anchor every earlier projection used does not reproduce.

#### External instances: the Fukuoka MQ Challenge

`grobner::research::MqInstance` imports instances from the
[Fukuoka MQ Challenge](https://www.mqchallenge.org/). The GF(31) families (types III and VI) need
no new arithmetic — `PrimeFieldElement64<31>` already exists, and `Zp31` is the same field in four
bytes. The GF(2^8) families (types II and V) import since #414; only GF(2) is still refused by
name, and **not for want of an export**: `binary_field` and `extension_field` are public, and that
claim was stale here long after it stopped being true (`docs/research/boolean-solving.md` §1). GF(2)
needs only the import path written, against `Zp2` (§8 of the same document decides that).

GF(2^8) took three things, and they had to land together. The real header is
`GF(2)[x] / x^8 + x^4 + x^3 + x^2 + 1` rather than `GF(2^8)`, so no genuine file parsed at all.
Coefficients are two-digit **hex** bytes, and because 100 of the 256 bytes have an all-decimal
spelling, accepting the header without also switching the base would have turned a loud
`BadHeader` into a system silently built from different field elements — `MqField::radix` now
decides the base of a coefficient row and of an answer vector alike (#415 did the latter). And the
coefficient route is `KnownOrder::element_at`, not `FiniteField::new`: over an extension the trait
`new` is the prime-subfield embedding, so `Gf256Mq::new(0xa7)` is `1` and a byte-wise read through
it would collapse every coefficient to a bit.

The upside is bigger than the defect was. Because the header *states* the modulus,
`MqInstance::check_coefficient_field` **verifies** it against the coefficient type instead of
assuming one: it derives the type's own modulus from arithmetic and reports `MqError::WrongModulus`
on a mismatch, so `Gf256` (AES, `0x11B`) is refused for a challenge file and `Gf256Mq` (`0x11D`) is
accepted. No order comparison could separate them — the two fields have the same order.
[`docs/research/fukuoka-mq.md`](docs/research/fukuoka-mq.md) §2.4 settles which is right against a
published answer: all 20 polynomials of type II `n = 10` vanish under `0x11D` and none under
`0x11B`.

The coefficient layout is **every monomial of degree at most two in descending grevlex order**,
which is what the file's own `Order` header names. It is implemented by sorting with
`MonomialOrder::GradedReverseLexicographic` rather than as an index pattern, and it was *verified*
rather than assumed: four candidate layouts were evaluated at a published answer and exactly one
makes every polynomial vanish. A monomial-order translation error is the failure mode an importer
has, and it is silent.

On type III `n=10` seed 0 — 20 quadratics in 10 unknowns — zeebra reconstructs the system, confirms
it vanishes at the published answer, and independently recovers that same point in **111 ms** with
`D = 1`. Both directions matter: a wrong layout could vanish at one point by accident, but it could
not also be solved to the same one. This is a *toy* example 24 variables short of the smallest
published type III challenge, which starts at `n = 34` — not `n = 55`, which is type I's range —
and is not a competitive result.

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

That quirk is no longer an inference. The challenge publishes its own **coefficient generator**, and
every instance is reproducible from `(type, n, seed)` plus a 200 Mbit file of π it distributes —
confirmed against all six types' toy examples, coefficient for coefficient
([`docs/research/fukuoka-mq.md`](docs/research/fukuoka-mq.md) §7). So the redistribution problem has
a cheaper answer than a download recipe, and `research/fukuoka-mq/solved-instances.tsv` records all
37 published solves of types II, III, V and VI — parameters, dates, solvers, algorithms, hardware
and figures, with no instance data — checked by `tests/fukuoka_mq_records.rs`.

#### Candidate external instances, surveyed but not imported

[`docs/research/additional-benchmarks.md`](docs/research/additional-benchmarks.md) is the shortlist
of published cryptanalysis instances worth importing next, with the rejections and their reasons.
Four candidates are accepted: reduced-round **Anemoi** CICO, whose reference data is raw Magma F4
and FGLM logs under MIT and whose quotient dimension is a published `(α+2)^N` zeebra can be checked
against; reduced-round **Griffin**; Anemoi's `ACICO` model as a second formulation of the first; and
reduced-round **LowMC**, recorded there as blocked on `binary_field` not being exported — which it is
not: the module is public and LowMC is over GF(2), where the whole solve path works
(`docs/research/boolean-solving.md` §6). UOV, MAYO, Arion and
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

#### Courtois MinRank A–F, where the challenge is a parameter set and not a file

[`docs/research/minrank.md`](docs/research/minrank.md) is the provenance record for the six MinRank
challenges Courtois proposed in 2001, read from the original publication rather than from the
literature that cites it. The parameters are verified and are committed, machine-readable, in
`research/minrank/courtois-challenges.tsv`; `tests/minrank_challenges.rs` re-derives the paper's own
solution-probability column from them, so a transcription slip in any of `q`, `η`, `n`, `m` or `r`
fails a test instead of propagating.

The finding that matters is negative. The paper proposes "six **sets of parameters** A-F"; it
publishes no matrices, offers no prize, and the scheme's official page — archived eight times
between 2001 and 2003 — carries papers and slides only. **No authentic instance of any of A–F was
ever published**, and the construction that would regenerate one needs a 160-bit seed and a
generator the paper names neither of. Every published break ran on an instance its authors generated — the only
executed solve of C, Steel's of 23 August 2014, on "a random instance over `GF(65521)`", and the
2026 one on D, whose abstract says so in as many words ("**an** instance"); the 2010 result on C is
a method and a projection, not a completed run. So a same-parameter instance here is not a degraded substitute — it is the same kind of
object every published result used — but the published costs stay a **difficulty scale and not a
comparand**, and nothing is in [the registry](#the-challenge-registry) until a generator exists to
digest. The document also corrects the verifier: the condition is `rank(Σ αᵢ Mᵢ − M₀) ≤ r` over
`1 + m` matrices, so challenge A is eleven `6 × 6` matrices over `GF(65521)`, not ten.

#### Anemoi, the first candidate actually imported

`grobner::research::anemoi` is the permutation half of candidate 1: Anemoi at `ℓ = 1` over
`p = 2^64 − 353`, `α = 3`, transcribed from the designers' reference implementation (MIT,
`3e86ff0c`) and the CRYPTO 2023 paper. The round constants are **derived, not tabulated** — they
come out of the first two hundred digits of π — and the modulus is odd, so
`Zp18446744073709551263` holds it in Montgomery form with no new field arithmetic.

```rust
use zeebra::{
    fields::Zp18446744073709551263,
    grobner::research::{Anemoi, AnemoiParameters},
    FiniteField,
};

let anemoi = Anemoi::<Zp18446744073709551263>::new(AnemoiParameters::six_worlds(4)).unwrap();
assert!(anemoi.is_cico_solution(Zp18446744073709551263::new(8251407552160637060)));
```

The one choice the paper leaves open is `g`, "a generator of the multiplicative subgroup"; the
reference takes Sage's smallest primitive root, which is `g = 5` here. That is a **convention rather
than a specification**, so `smallest_primitive_root` reproduces the convention and
`Anemoi::derived_digest` pins what it produced — a parameter checksum covers `p`, `α`, `ℓ` and `N`
and would not notice a changed generator moving every constant.

Verification does not rely on the transcription being read correctly. The Six Worlds logs
(<https://github.com/IAIK/six-worlds-anemoi>, MIT `fa056e6f`) print complete lexicographic Gröbner
bases, and four CICO witnesses were extracted from them by rooting the lex univariate and reading
each root back into the permutation's own input coordinates. The witness **count** matches the logs'
own `nsols` line at every rung — 2, 1, 0 and 1 at `N = 1, 2, 3, 4` — including the rung with no
solution. [`docs/research/anemoi.md`](docs/research/anemoi.md) records every source URL, the
ideal-membership check that needs no roots, and one trap: the logs' variable labels are positionally
permuted relative to the model's own names, and the two orders coincide at `N = 1`.

Ten rows are registered — `N = 1 … 5` in both published models — and frozen by
`test_the_registry_is_frozen` **before** anything is run. Two registry changes were needed:

- **`ChallengeParameters::AnemoiCico` carries the algebraic model, so the model is inside the
  identity digest.** `FCICO` at `N = 5` is ten generators of degree three; `PCICO` is six of degrees
  up to ten. Same primitive, same solutions, two systems a solver meets completely differently — so
  without the model in `canonical_lines` the two digests would collide and a comparison tool keyed
  on the digest would compare them.
- **`ReferencePoint` is where a published competitor figure lives.** `ExternalStatus` records
  *whether and when* a problem was solved elsewhere and carries no time, no memory and no hardware,
  so "22 057 s of FGLM at `N = 5` on an Intel Xeon E5-2630 v3 under Magma V2.26-2" had nowhere to
  go. It sits **outside** `canonical()`, for the same reason a bounty does: a corrected
  extrapolation must not change what a problem *is*. The basis step and the conversion step are
  separate points — the finding is that they are 2 400x apart — and `reported_memory` is `None` on
  every row, because the logs report peak resident once per sweep and not per row.

The class is `Official` rather than `FaithfulReduction`: the registered object *is* the published
object — Six Worlds ran those round counts and reported them as its own experiment — and there is no
registered full-round Anemoi for a reduction to name. `ExternalStatus::PublishedWithAnswer` then
makes a verified witness a `Reproduction`, which is the strongest honest claim on a solved reduced
instance. The caveat a reduction would have carried structurally is in each row's notes: a result at
`N = 5` says nothing about full-round Anemoi, which is 21 rounds.

##### The machine-independent check, which is read first

`dim F_p[x]/I` does not depend on the machine, the library or the wall clock, so it is the one
number zeebra can be right or wrong about with no reference to a clock — and a disagreement is a
**defect in zeebra or in the model, not a performance difference**. The published value is
`(α+2)^N`, and zeebra's own figure agrees at **all ten registered rows**, both models, `N = 1 … 5`:
5, 25, 125, 625, 3125.

```sh
cargo run --release --example anemoi_ladder list        # the ten rows and their published figures
cargo run --release --example anemoi_ladder dimensions  # the gate; pins no environment, needs none
ZEEBRA_MACHINE=... ZEEBRA_AFFINITY=... tools/benchlock.sh \
    cargo run --release --example anemoi_ladder row anemoi64-cico-n3-fcico
```

`row` runs F4, then FGLM, then root finding, each timed separately — separately because the
published finding is that the conversion costs 2 400x the basis at `N = 5`, and a combined figure
would hide it — and checks any recovered point **through the permutation** rather than through the
system that produced it. At `N = 1` it lands on `8431162935045355170`, which is the witness the
reference's own lex basis determines: zeebra reaches a reference point through a different pipeline.

**`row` refuses to print a single number unless `ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY` are set**, and
exits 2 if they are not. An unpinned wall-clock figure is not a measurement, and one produced by
accident is one that gets quoted later; measurements must also be serialized under
`tools/benchlock.sh`. The timed ladder is a follow-up, and `(α+2)^N` is checked at `N = 1 … 4` by a
unit test so a regression fails CI rather than appearing as a table row.

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
`F4Error::TooManyNonzeros` or `F4Error::TooManyLiveBytes`.

**That agreement is also a trap, so set the two together.** The effective limit is the `min`, and at
the default over a 16-byte entry the two are numerically *identical* — `320_000_000 / 16` is exactly
`20_000_000` — so **assigning one field alone changes the limit by nothing**, while the error goes on
reporting the limit that actually bound. A caller who raised `max_live_nonzeros` from 20 M to 200 M
on Anemoi `N = 6`, re-ran, and was refused at ~20 M entries had to read the source to find out why
([#322](https://github.com/mfaulk/zeebra/issues/322)). Two constructors set the pair from one
number, each deriving the other side from the field's entry cost:

```rust
use zeebra::{fields::{Bn254Fr, Zp18446744073709551557}, grobner::F4Options};

let budget = F4Options::default().with_live_budget::<Zp18446744073709551557>(3_200_000_000);
assert_eq!(budget.max_live_nonzeros, 200_000_000);     // derived, so nothing to keep in step

let entries = F4Options::default().with_live_entries::<Bn254Fr>(200_000_000);
assert_eq!(entries.max_live_bytes, 200_000_000 * 40);  // a wide entry, costed as one
```

`FglmOptions` is the same *shape* — `max_operator_bytes` beside `max_operator_entries`, and
`max_span_bytes` beside `max_span_entries`, at the same two numbers — and deliberately **not** the
same coupling: each is a separate comparison against its own requirement in its own unit, so a lift
of one there does take effect. `fglm::conversion`'s
`test_lifting_one_span_budget_leaves_the_other_binding_in_its_own_unit` is what keeps that true.

**`FglmOptions::max_quotient_dimension` is derived from the budget beside it, not from the
corpus.** It used to be justified as "26x the largest quotient dimension in the benchmark corpus,
which is cyclic-6's 156", and that stopped being true the moment #261's cross-library corpus added
rungs at 16,384 — four times the cap rather than a fraction of it. A default whose stated reason is
a corpus figure goes stale on every corpus expansion, and nothing was checking it (#348). So the
cap is now `RECOMMENDED_MAX_QUOTIENT_DIMENSION`, the next power of two at or above what
`max_span_entries` itself admits:

```rust
use zeebra::grobner::{largest_quotient_dimension_within, FglmOptions,
                      RECOMMENDED_MAX_QUOTIENT_DIMENSION, RECOMMENDED_MAX_SPAN_ENTRIES};

// `D^2 + D (D + 1)` cells reaches 20,000,000 at D = 3,162.
assert_eq!(largest_quotient_dimension_within(RECOMMENDED_MAX_SPAN_ENTRIES), 3_162);
assert_eq!(RECOMMENDED_MAX_QUOTIENT_DIMENSION, 4_096);
assert_eq!(FglmOptions::recommended().max_quotient_dimension, 4_096);
```

Note what that ordering means: **the dimension cap is not the limit that bounds memory**, and is
not meant to be. `max_span_entries` admits at most D = 3,162 and `max_span_bytes` at most 2,235
over BN254, so one of those binds first on every dimension the cap allows. The cap sits above them
as the pre-enumeration tripwire for a walk so far out of envelope that enumerating `N * D` operator
columns is itself the waste. `test_the_span_budget_binds_before_the_dimension_cap` asserts that
ordering rather than asserting it in a comment, which is how the previous justification came to be
false without anything noticing.

**The corpus reaches past the cap, deliberately.** The planted MQ family's quotient dimension is
`2^N`, so `mq-planted-14` is 16,384 and the conversion declines it. That refusal is the budget
working: Singular converts the same instance in 45.8 s and 10.4 GB, and Zeebra's own `DirectLexF4`
route solves it, so declining the conversion is a budget decision rather than an inability — and it
is recorded as a limit stop, not a failure (#347). `test_the_corpus_reaches_past_the_recommended_cap`
and `test_every_planted_rung_has_a_declared_quotient_dimension` keep that relationship pinned to
the ladder, so adding a planted rung forces the decision instead of silently invalidating a
sentence. Five rungs — the poseidon and anemoi ones — have no recorded quotient dimension in this
tree and are therefore outside that trap; that is #473.

Neither is a ceiling on the process. `F4Statistics::peak_live_bytes` reports what the budget
enforces; `max_dense_buffer_bytes` reports what it deliberately omits — the dense buffer the
elimination backend allocates, which under `Backend::Dense` is `rows * columns` cells and a
function of the shape alone. `max_estimated_bytes` is the two added, per batch, maxed over batches.
None of them accounts for the monomial-to-column map, the basis's term vectors, or allocator
overhead; for the process figure use `util::peak_resident_bytes`.

**How much that omits, measured.** On Fukuoka MQ type III `n = 20` at the default 20,000,000-entry
budget, the accounted figure is 195 MB and the process peaks at **14.75 GB — 75x more**. The
omission also does not move with the budget: three caps spanning 5x all peak within 0.01% of each
other. So the entry budget cannot be scaled as a proxy for memory even roughly — what it omits is
not a function of what it bounds.

**Where it goes, attributed.** 88% of that peak is **one `VecDeque<Monomial<20>>`**: symbolic
preprocessing enqueues every term of every row and deduplicates only on pop, so the queue reaches
162 million monomials at 80 bytes each while the matrix it is building does not exist yet. The basis
— held twice, and three times during interreduction — is another 6.5%. The pair heap, the obvious
suspect at `O(|G|²)` pairs, is **0.03%**. `F4Statistics` reports the counts:
`max_pending_monomials`, `monomials_enqueued`, `peak_pair_queue`, `peak_basis_terms`.
[`docs/research/f4-resource-scaling.md`](docs/research/f4-resource-scaling.md) §9 has the full table
and the method; `cargo run --release --example f4_memory` reproduces it on any system.

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

#### Stopping on a wall clock, and keeping the report

`F4Options::max_wall_time` is `None` by default, so no clock is read on the shipping path. When it
is set it is checked in **two** places: **once per batch** in the main loop, which is what makes the
counters a crossing leaves behind describe whole batches rather than a matrix caught halfway through
being built; and **once per basis element during final interreduction**, which runs after the loop
has finished. One batch is always reduced before the batch check can fire, so the report is never
empty:

```rust
use std::time::Duration;
use zeebra::{fields::Zp2147483647, grobner::{benchmark_systems::katsura, f4_reported, F4Options, StopKind},
             MonomialOrder};

let options = F4Options { max_wall_time: Some(Duration::ZERO), ..F4Options::default() };
let (result, statistics) = f4_reported(
    &katsura::<5, Zp2147483647>(),
    MonomialOrder::GradedReverseLexicographic,
    &options,
);

let error = result.unwrap_err();
assert_eq!(error.stop_kind(), StopKind::Time);   // never StopKind::Resource
assert_eq!(error.limit_name(), "max_wall_time");
assert_eq!(statistics.batches, 1);               // the report is never empty
assert!(statistics.max_matrix_rows > 0);
```

**A time stop is type-level distinct from a resource stop**, through `F4Error::stop_kind`. An entry
or byte count is a property of the system and crosses at the same degree on any machine; an elapsed
time is a fact about one box under one load. A consumer that ranks stops against each other matches
`StopKind` rather than enumerating variants, so a wall clock can never be ranked against a budget.

It does not replace an external supervisor: a single batch can be arbitrarily long, so the elapsed
time at a crossing is the budget *plus* whatever the batch in progress still needed, and both are
reported. What the cooperative stop adds is that it **returns**, and a return carries the statistics
an abandoned worker thread cannot.

The two stages report **different variants**, because they can name different things.
`F4Error::TimeBudgetExceeded` carries the selection `degree` of the batch the budget was noticed at;
`F4Error::InterreductionTimeBudgetExceeded` carries `elements_reduced` of `elements`, because that
stage has no batch and no selection degree, and inventing one would be a fabrication. Both are
`StopKind::Time` and both answer `"max_wall_time"` to `limit_name()`, so a consumer that classifies
by kind or by name sees one thing and a consumer that wants to know *where* can tell them apart.

Interreduction was unchecked until #395, and the gap was not academic: #349 measured that stage at
**80.4%** of `mq-random-10`, so a budget honored at every batch could be overrun by four fifths of
the computation.

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

Three further quantities are kept apart deliberately:

| Figure | What it is |
|---|---|
| `max_pair_degree` | the highest lcm degree any batch was *selected* at |
| `max_monomial_degree` | the highest degree any monomial reached as a matrix *column* |
| `step_degrees` | the selection degree of **every** batch, in the order the batches ran |

The second is in general larger than the first, because reducer multiples carry monomials above the
lcm that produced them. **None of the three is the solving degree or the degree of regularity**,
which are properties of the ideal rather than of a run.

`step_degrees` is the sequence Magma's `GroebnerBasis` added as a second return value in V2.26 —
"the integer sequence of degrees encountered in each step of the F4 algorithm" — and a mature
engine choosing the sequence over the maximum is the argument for having it: the degree a system
stalls at, whether it climbed monotonically or jumped, and where a degree-fall happened are all
invisible in a maximum. `degrees` is not a substitute, because it is keyed *by* degree, so a degree
revisited after a drop appears once and the order is gone.

It is collected **unconditionally** — one `u64` push per batch against batch counts in the hundreds
— unlike `degrees`, which a measurement has to remember to enable. `step_degrees.len() == batches`
by construction: a selection every pair criterion discarded built no matrix and is not a step,
which is also the one way `observed_solving_degree()` — the sequence's maximum — can fall *below*
`max_pair_degree`, since that field is accumulated over the pairs as selected, before the criteria
run. On every system in the corpus the two agree; the inequality is the invariant.
`CostRow::with_solving_degree_from` reads it, so a cost-model row's `solving_degree` comes from a
run rather than from a hand-typed literal.

`examples/f4_profile.rs` prints the sequence run-length encoded — `5x3` is three consecutive
batches at degree five — as a third table beside the stage times and the diagnostics, and in its
`mq` mode for the `mq-random-10` instance the competitive record was taken on:

```text
cargo run --release --example f4_profile            # all three tables, every system
cargo run --release --example f4_profile -- mq      # the #349 instance, including its sequence
```

**The sequence for `mq-random-10`**, the competitive-board instance at digest
`72d0ad315fc25409` — the same instance and the same digest #349's stage split and #436's
interreduction figure were taken on:

```text
system       order    batches maxdeg obsdeg  degrees per step
mq-random-10 grevlex       10      8      8  2, 3, 4, 5, 6x3, 7x2, 8
```

Ten batches, a strictly monotone climb from degree two to degree eight, with degree six split
across three batches and degree seven across two. **No degree-fall anywhere**, so on this instance
the mutant mechanism had nothing to act on — which a maximum of eight could not have told you
either way. Taken at `F4Options::default()` with `measure_stages` on, affinity 0-7, which is the
configuration the record was taken under.

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
| `reducer_selection` | `ReducerSelection::{FirstApplicable, LargestLeadingMonomial, FewestTerms, MostTerms}` | which basis element symbolic preprocessing picks to reduce a monomial. `FirstApplicable` is the default. `LargestLeadingMonomial` minimizes the multiplier but maximizes how much of the reducer's tail stays reducible, which grows the matrix; `FewestTerms` picks the sparsest divisor instead, which is a third less peak memory on katsura grevlex and a 25%–30% regression on the same systems under grlex. `MostTerms` is `FewestTerms`'s control |
| `criteria` | `PairCriteria { product, chain, gebauer_moller }` | which criteria may discard a critical pair before a matrix is built |
| `schedule` | `PairSchedule::{DegreeThenLcm, SmallMultiplierDegree, LargeMultiplierDegree, SmallMultiplierMonomial, LargeMultiplierMonomial, ShortPair, LongPair}` | in what order the pending pairs of one degree are taken. Not a criterion — it discards nothing |
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

`ShortPair` ranks by a different quantity — `terms(i) + terms(j) - 2`, which is `slimgb`'s
`pair_weighted_length` over a prime field — and `LongPair` is its control. **Measured and rejected
as a default:** it raises peak live entries on all seven instances and its control is inverted on
two of them, which is the noise signature above. The same term-count axis on the *reducer* side
(`ReducerSelection::FewestTerms`) does have an effect. Both are selectable so the result can be
reproduced; see [`docs/research/pair-scheduling.md`](docs/research/pair-scheduling.md) §2 and §6.

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

Buchberger's criterion names `|G|(|G|−1)/2` pairs, and certification **prunes them with the
criteria that transfer to a static basis** — the product criterion and Gebauer–Möller's
lcm-divisibility criteria, both functions of the leading monomials alone. The chain criterion does
not transfer: it justifies a discard by a pair that has already been *processed*, and a verification
pass has processed nothing. The strict, history-free form that would be sound is measurably empty on
this corpus, so it is deferred; `cargo run --release --example certification_criteria` is the
measurement, and the module documentation of `grobner::f4::certify` has the argument. A criterion
wrongly applied here is a silent false pass rather than an incomplete basis, so the pruned check is
asserted to reach the same verdict as the all-pairs check on planted defects as well as on correct
bases.

| instance | basis | pairs | pruned | all pairs ms | pruned ms | ratio |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| katsura-5 | 13 | 78 | 66.7% | 4.3 | 1.2 | 3.6x |
| katsura-6 | 22 | 231 | 72.3% | 62.6 | 9.9 | 6.3x |
| cyclic-5 | 20 | 190 | 76.3% | 9.0 | 2.2 | 4.1x |
| Poseidon `t=2 R_F=2 R_P=2` | 70 | 2 415 | 88.1% | 7 796.3 | 251.6 | **31.0x** |
| Poseidon `t=2 R_F=4 R_P=0` | 102 | 5 151 | **89.0%** | 27 993.7 | 831.2 | **33.7x** |

The time falls further than the pair count because the pruned pairs are the expensive ones: a
relatively prime pair's lcm is the product of the two leading monomials, so its S-polynomial is the
largest the basis has, and Gebauer–Möller's are the pairs with non-minimal lcms. Certifying the
larger Poseidon instance drops from 28.0 s to 0.83 s, which is the same order as its solve rather
than dozens of times it.

`CertificationReport::s_polynomials_checked` and `s_polynomials_discarded` report the two counts, so
the saving is visible rather than inferred; together they cover every pair on a completed check.
What remains is still quadratic in the basis, so `F4Statistics::certification` still reports its own
cost separately from the total **because that is the comparison that decides anything**: a strategy
that skips work has to be judged on its cost including the check that establishes the result, and a
saving the check erases is not a saving.

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
`certify`, and three together — against Singular on random systems over every supported field,
which is stronger than composing "strategy equals baseline on a fixed corpus" with "baseline agrees
with Singular". Seven fields since the oracle reached `GF(2^8)`, and the sweep's size is the cross
product of variable counts and fields rather than a round number, so adding a field widens the
coverage instead of displacing some of it.

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

## Integer Roots and Perfect Powers
`BigUInt::isqrt` and `BigUInt::nth_root` return the floor of the root, and `perfect_power` writes
`n` as `m^k` with the largest `k` it can:

```rust
use zeebra::integers::{big_uint::BigUInt, perfect_power};

assert_eq!(BigUInt::new_from_u64(26).nth_root(3), BigUInt::new_from_u64(2));
assert_eq!(BigUInt::new_from_u64(17).isqrt(), BigUInt::new_from_u64(4));

// 64 = 8^2 = 4^3 = 2^6, and only the last has a base that is not itself a perfect power.
let (base, exponent) = perfect_power(&BigUInt::new_from_u64(64)).unwrap();
assert_eq!((base, exponent), (BigUInt::new_from_u64(2), 6));

assert_eq!(perfect_power(&BigUInt::new_from_u64(12)), None);
```

Both roots are Newton's iteration started at `2^ceil(bits/k)`, which is above the root — the side
on which the iteration decreases monotonically, so it terminates at the floor with no correction
step. Zero and one are not perfect powers: every exponent would answer for them.

`perfect_power` tests only **prime** exponents, which loses nothing because `m^(ab)` is `(m^a)^b`,
and recurses on the base to recover a composite exponent. That is why `64` is reported as `2^6`
rather than as the `8^2` the `k = 2` pass finds.

`factor` runs the test before Pollard rho, which is what the test is for: rho needs about
`p^(1/2)` iterations to split `p^k`, so `p^3` for a 20-digit prime does not factor in any practical
time without it and factors in a single primality check with it
(`test_factorization_of_a_prime_power_rho_cannot_reach`).

## Lenstra's Elliptic Curve Method
Pollard rho costs about `p^(1/2)` iterations in the smallest prime factor `p`, so it reaches
20-digit factors and not 40-digit ones. ECM's expected cost depends on the size of the factor it
finds rather than on the size of `n`, which makes it a complement to rho rather than a replacement.
The workload it is here for is the factorization of `q - 1` for a wide prime field `q`, which is
what finding a generator of the multiplicative group needs.

`ecm_find_factor` returns one non-trivial factor, and `None` when the budget ran out without
finding one. That `None` is an ordinary outcome, not an error:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::integers::{big_uint::BigUInt, ecm_find_factor, factor_with_budget, EcmBudget};

let mut rng = StdRng::seed_from_u64(20260131);
let budget = EcmBudget { b1: 200, b2: 20_000, curves: 40 };

// 10_007 * 10_009, past the small-prime table that trial division uses.
let n = BigUInt::new_from_u64(10_007) * &BigUInt::new_from_u64(10_009);
let factor = ecm_find_factor(&n, &budget, &mut rng).unwrap();
assert!(factor > BigUInt::one() && factor < n);
assert!((&n % &factor).is_zero());

// A prime has no factor to find, so the budget is spent and the answer is honest.
assert_eq!(ecm_find_factor(&BigUInt::new_from_u64(1_000_003), &budget, &mut rng), None);
```

`factor_with_budget` drives trial division, the perfect-power test and ECM together. What it could
not split is reported rather than dropped, so `product()` always returns the input:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::integers::{big_uint::BigUInt, factor_with_budget, EcmBudget};

let mut rng = StdRng::seed_from_u64(3883);
let budget = EcmBudget::for_digits(10);

let n = BigUInt::new_from_u64(1_290_159_361_801_237); // 4409^3 * 15053
let factorization = factor_with_budget(&n, &budget, &mut rng);
assert!(factorization.is_complete());
assert_eq!(factorization.primes, vec![BigUInt::new_from_u64(4409), BigUInt::new_from_u64(15053)]);
assert_eq!(factorization.powers, vec![3, 1]);
assert_eq!(factorization.product(), n);

// A budget too small for the cofactor leaves it in `unfactored`, and the product still holds.
let tiny = EcmBudget { b1: 100, b2: 0, curves: 1 };
let hard = BigUInt::from_dec_str("1000000000000000003").unwrap()
    * &BigUInt::from_dec_str("1000000000000000009").unwrap();
let partial = factor_with_budget(&(BigUInt::new_from_u64(12) * &hard), &tiny, &mut rng);
assert!(!partial.is_complete());
assert_eq!(partial.unfactored, vec![(hard, 1)]);
assert_eq!(partial.product(), BigUInt::new_from_u64(12) * &partial.unfactored[0].0);
```

That budget is the point of the API shape. `prime_field_256`'s `try_primitive_element` returns
`Err(RootOfUnityError::NoKnownGenerator)` rather than searching, because finding a generator means
factoring a 254-bit `q - 1` and that should not start by accident. ECM does not change that: a
factorization of a 254-bit `q - 1` is still something a caller has to ask for, which is why the
entry point makes the effort explicit and can say "I did not finish". Wiring the two together is
tracked separately (#405); nothing in the crate calls it yet.

### How it works
Stage 1 multiplies a point on a **Montgomery curve** `B y^2 = x^3 + A x^2 + x` by every prime power
up to `b1`, using the Montgomery ladder over `XZ`-only projective coordinates. If the curve's order
modulo some prime factor `q` of `n` is `b1`-smooth, the point reaches the identity modulo `q`, and
`q` then divides the resulting `Z` while `n` does not — so `gcd(Z, n)` names it. The `y`-coordinate
is never needed, because `B` drops out of the `x`-only formulas.

Stage 2 is the **standard continuation**, which additionally catches an order that is `b1`-smooth
apart from a single prime in `(b1, b2]`. Writing such a prime as `p = v*D ± u` for a stride
`D = 210` and a `u < D/2` coprime to it, `[p]Q` being the identity modulo `q` means `[v*D]Q` and
`[u]Q` share an `x`-coordinate there — either sign of `u` will do, since `[-u]Q` and `[u]Q` have the
same `x`. Sharing an `x` is `X_vD * Z_u - X_u * Z_vD` vanishing, and those differences accumulate
into one product, so the whole stage costs a single gcd. A difference that is zero modulo *all* of
`n` is skipped rather than multiplied in, since its gcd is `n` and it would erase what every other
pair found. Coverage starts at `D/2 = 105`, so a `b1` below that would leave a gap; any realistic
`b1` is far above it.

Curves come from **Suyama's parameterization**, which forces the order to be divisible by 12 and so
raises the chance of smoothness. It needs `(A + 2) / 4`, and `BigUInt` has no modular inverse — so
the constant is carried as an unreduced fraction `num / den` and cleared projectively by scaling
both coordinates of the doubling by `den`. That costs one multiply per doubling and buys more than
it costs: inversion would fail exactly when `den` shares a factor with `n`, and that gcd is itself
the factor being hunted, so the degenerate case returns an answer instead of an error. It is also
why an even `n` is split immediately — `den` carries a factor of 16.

`EcmBudget::for_digits` follows the usual ECM parameter table (`b1` of 2e3, 1.1e4, 5e4 and 2.5e5 for
the 15-, 20-, 25- and 30-digit levels, with `b2 = 100 * b1`). Those are the asymptotically motivated
choices from the literature and **not** measurements of this implementation: the inner loop here is
a `BigUInt` multiply and remainder rather than Montgomery arithmetic, so a given budget costs
considerably more wall-clock time than a tuned implementation would pay. Treat the digit levels as
the shape of the parameter curve, not as a promise about runtime.

Quadratic Sieve is deliberately absent. Its cost depends on the size of `n`, which makes it the
right tool for a hard semiprime — and `q - 1` is not that. It is semi-smooth: a few small primes
and a handful of middling ones, which is exactly the shape ECM is for.

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

## Error-Correcting Codes

`codes::ReedSolomon` is an `[n, k]` Reed-Solomon code in evaluation form: a codeword is a
polynomial of degree below `k` evaluated on an FFT domain of `n` points. The domain is the
caller's, as it is for `evaluate` and `interpolate` — only the caller knows which field it is
working over and which sizes that field can host.

```rust
use zeebra::{
    codes::{CodeError, ReedSolomon},
    fields::Zp65537,
    FFTDomain, FiniteField, KnownOrder,
};
use rand::{prelude::StdRng, SeedableRng};

let mut rng = StdRng::seed_from_u64(1);

// A [16, 10] code: six parity symbols, so three errors or six erasures.
let domain = FFTDomain::from_generator(Zp65537::two_adic_root_of_unity(4, &mut rng), 16);
let code = ReedSolomon::new(domain, 10).unwrap();
assert_eq!((code.distance(), code.max_errors(), code.max_erasures()), (7, 3, 6));

let message: Vec<Zp65537> = (1..=10).map(Zp65537::new).collect();
let codeword = code.encode(&message).unwrap();

// Three errors at unknown positions are located and corrected.
let mut received = codeword.clone();
received[2] += Zp65537::new(9);
received[7] += Zp65537::new(1234);
received[13] += Zp65537::new(5);
let decoded = code.decode(&received).unwrap();
assert_eq!(decoded.message, message);
assert_eq!(decoded.error_positions, vec![2, 7, 13]);

// A fourth error is past the radius, and is reported rather than mis-corrected.
received[0] += Zp65537::new(7);
assert_eq!(code.decode(&received), Err(CodeError::Uncorrectable));

// Six erasures are twice as many, because a known position needs no locator. The values at the
// erased positions are ignored, so any placeholder will do.
let mut punctured = codeword.clone();
for position in [0, 1, 4, 9, 11, 15] {
    punctured[position] = Zp65537::new(0);
}
let recovered = code.recover_erasures(&punctured, &[0, 1, 4, 9, 11, 15]).unwrap();
assert_eq!(recovered.codeword, codeword);
```

`encode` reads the message as the polynomial's coefficients, so it does not appear in the codeword.
`encode_systematic` reads it as the polynomial's values on the first `k` domain points instead, at
which point `codeword[..k]` *is* the message — one `O(k^2)` interpolation bought in exchange for
being readable without decoding.

### Why the syndromes are already there

Interpolating a received word over the domain gives `r(x)` with `r_j = (1/n) * sum_i y_i w^{-ij}`.
A codeword's `r_j` vanishes for `j >= k` by definition, so the top `n - k` coefficients of `r`
*are* the syndromes, and the decoder needs no transform the encoder did not already need. Writing
out the `j`th of them for an error `e` supported on a set `E`:

```text
S_j = r_{k+j} = sum_{i in E} Y_i X_i^j,   X_i = w^{-i},   Y_i = e_i w^{-ik} / n
```

which is the classical syndrome form, so the classical key equation
`Λ(x)S(x) ≡ Ω(x) mod x^{2t}` applies unchanged. It is solved here by the extended Euclidean
sequence on `(x^{2t}, S(x))`, halted at the first remainder of degree below `t` — which is
`gcd.rs`'s algorithm stopped early, rather than a second recurrence in Berlekamp-Massey's shape.
Error positions then come from evaluating the locator on the domain rather than from `roots`: the
roots of `Λ` are exactly domain points, so a scan is both cheaper than general root finding and
unable to return a root that is not a position. Magnitudes come from Forney's formula.

### A correction is a candidate until it is verified

Past `t` errors the nearest codeword need not be the transmitted one, so there is nothing a decoder
could return that would be *right*. The Euclidean step does not know that — it still produces some
locator of degree at most `t` — so `decode` re-interpolates its candidate and checks it is a
codeword before answering, and returns `CodeError::Uncorrectable` when it is not. Together with the
degree bound that caps the locator, and hence the number of symbols touched, at `t`, that is the
whole correctness argument: a word verified to be a codeword and at distance at most `t` from the
received word is the only such codeword, because two of them would be within `2t < d` of each
other.

The practical consequence is that a code of **odd** redundancy detects one more error than it can
locate. All `n - k` syndromes are checked, while only `2t = n - k - 1` of them feed the key
equation, so the spare one is left over to veto a correction that explains the others. Erasure
recovery spends its surplus the same way: `k` surviving symbols determine the codeword polynomial,
and every survivor beyond those `k` checks the answer, so an error at an *unerased* position is
reported rather than quietly interpolated into a different codeword.

### Cost, and the one block length to avoid

Encoding and syndrome extraction are one transform each, so they cost whatever `evaluate` costs at
the chosen block length: `O(n log n)` for a power of two or a product of small coprime factors, but
`O(n^2)` for a block length with a large prime factor, which `fft::prime_factor` handles by the
definition. `bluestein_transform` removes that case and is not dispatched to automatically, so a
prime block length is a choice to make deliberately rather than one to stumble into.

Not implemented: combined errors-and-erasures decoding, list decoding past `t`, and any code other
than Reed-Solomon. Characteristic two is also out for now — `interpolate` scales by `F::new(n)`,
and `FiniteField::new` is unimplemented for `BinaryFieldElement`, so the inverse transform has no
`1/n` to use over `GF(2^m)`.

## Parallel Development

Several coding agents work this repository against one shared board, so issues double as the
coordination substrate: an agent claims an issue before starting, keeps the claim alive while it
works, and releases it when done. Claims carry a four-hour lease and expire, so an agent that dies
mid-task does not strand the work behind a label nobody can clear.

```sh
./scripts/agent/zb-claim.sh orient                 # open, unclaimed, unblocked, best first
./scripts/agent/zb-claim.sh claim 119 "<intent>"   # comment + label + board In Progress
./scripts/agent/zb-claim.sh heartbeat 119          # extend the lease
./scripts/agent/zb-claim.sh reap                   # claims whose lease expired
./scripts/agent/zb-claim.sh release 119            # finished; or --abandon to hand back
./scripts/agent/zb-claim.sh token                  # this checkout's claim token
```

An agent's id is `worktree@branch`, which is *derived* and so can change under it — a branch
rename, a rebase onto a new base, a retargeted PR. Each claim therefore also records a **claim
token**, minted once per checkout and kept in that worktree's own git directory, so ownership is
proved rather than re-derived. Without it a rename orphaned the agent's own markers and `verify`
reported `LOST RACE` against the agent itself, which is the dangerous direction for that signal to
fail in: agents are told to obey it, so a spurious one trains the operator to override a signal
that may next time be real.

The protocol, the staleness rule, and the rules for fanning out writers are in
[CLAUDE.md](CLAUDE.md#multi-agent-coordination-claiming-work). The one invariant worth repeating
here: every read exits **0 = data, 1 = genuinely empty, 2 = the read failed**, because a
rate-limited `gh` prints nothing and exits 0, and treating that as "nothing is claimed" would hand
the same issue to every agent at once.

That invariant had to grow a fourth case it was not written against: **succeeded, returned data,
and was incomplete.** GraphQL caps `first:` at 100 per page, and once the repository passed 100
open issues `orient` returned the oldest 100 and exited 0 with a queue that looked whole — dropping
precisely the newest issues, which are the follow-ups agents file for each other (#448). It now
walks `pageInfo.hasNextPage`, and a walk it cannot finish — no cursor to resume from, or more than
`ZB_ORIENT_MAX_PAGES` pages (default 20) — is status **2**, never a short list. Silent truncation
was the bug, so the only safe way to be incomplete is loudly.

## Why You *Shouldn’t* Use Zeebra
I wrote Zeebra as an educational exercise. It is not yet complete or mature. It is not necessarily correct. For something more production-ready, please consider:

- **[arkworks-rs/algebra](https://github.com/arkworks-rs/algebra/tree/master)** - Algebraic structures and operations for zkSNARKs
- **[dimforge/nalgebra](https://github.com/dimforge/nalgebra)** - Linear Algebra library for the Rust programming language
- **[tspiteri/rug](https://gitlab.com/tspiteri/rug)** - Arbitrary-precision numbers
- **[axect/peroxide](https://github.com/Axect/Peroxide)** - Linear algebra library for machine learning
