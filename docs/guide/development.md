# Building, testing and CI

How to build and test Zeebra, what CI enforces, and how the build is configured.

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
bash tools/test/check-measurement-provenance-test.sh
bash tools/check-measurement-provenance.sh      # the documents, not the script
```

The Rust examples in `README.md` and in every file under `docs/guide/` are **compiled and run** by
`cargo test --doc`, through a `cfg(doctest)` item in `src/lib.rs`, so they cannot drift from the API
they document. Blocks that are illustrative rather than executable are fenced `text`. A guide file
added without its `include_str!` line in `src/lib.rs` would have examples nothing compiles, so
`tests/documentation.rs` asserts the list is complete in both directions.

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
cargo test --release --lib -- --ignored --exact \
    grobner::research::mq::tests::test_the_real_n24_challenges_import
# the three #197 added: the modulus oracle, the GF(2) families, and the two real m = 16 instances
# checked against the answer vectors their 2015 solver published
cargo test --release --lib -- --ignored --exact \
    grobner::research::mq::tests::test_the_published_answer_vanishes_only_under_the_challenges_modulus
cargo test --release --lib -- --ignored --exact \
    grobner::research::mq::tests::test_the_published_gf2_instances_import
cargo test --release --lib -- --ignored --exact \
    grobner::research::mq::tests::test_the_real_m16_challenges_vanish_at_their_published_answers
```

The second covers the two *real* challenge files at `m = 16` — type VI over GF(31) and type V over
GF(2^8), both `n = 24` — and asserts the import rather than a solve: header, shape, 325
coefficients per polynomial, the compiled dimension reached through `dispatch`, and the AES modulus
refused in favour of the challenge's `0x11D`.

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

A third job runs the benchmarks, on pull requests as well since #586: compilation was always
covered, but a benchmark that compiles and then *panics* was not, and such a commit is
unmeasurable without cherry-picking the fix onto it. The benchmark
targets are declared `test = false`, which keeps them out of `cargo test`: a `[[bench]]` target
defaults to `test = true`, so a bare `cargo test` linked all eight criterion binaries under fat
LTO and executed all 455 cases. That took 168s of the 180s a warm `cargo test --release` spent,
against 2.4s for the 968 tests and 8.9s for the doc examples. Smoke-testing the benchmarks is
still worth doing — it catches one that panics rather than merely failing to compile — so it moved
to its own job rather than being dropped:

```sh
cargo bench --profile ci-release -- --test
```

`cargo bench -- --test` and not `cargo test --benches`. The reason is the profile and not, as this
paragraph used to say, that `test = false` makes the latter select nothing: #586 measured that, and
`test = false` governs what a bare `cargo test` picks up rather than what an explicit `--benches`
selects, so `cargo test --benches` does build and run every case — in the **dev** profile, which
made it 382.0s against 26.3s. A benchmark that stops *compiling* still breaks the
`cargo build --all-targets` step in the pull-request jobs.

The library and the `zeebra-differential` binary are declared `bench = false`, the mirror of the
`test = false` above. `bench` also defaults to true, so this command used to select ten targets
rather than eight: the lib was built as a bench target and `--test` ran the whole unit suite here,
in one process under the built-in harness, duplicating the nextest jobs with worse isolation. That
broke `util::peak_memory`, whose subject is `VmHWM` — a process-wide high-water mark that, in a
process shared with ~1400 other tests, sits far enough above live RSS that a 32 MB ballast cannot
raise it. The binary has no tests at all, so its entry was a whole-crate link for nothing.
`bench = false` does not affect `cargo test`, which still runs both.

`--profile ci-release` because this job takes no measurements. A bare `cargo bench` resolves
`[profile.bench]`, which inherits `release`, and links all ten criterion binaries under fat LTO
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

## Testing the merged result

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

## What a pull request validates in `benches/`, and what it used to not

Both halves, since #586. The `Benchmarks run` job is no longer gated to `push`:

| | covered on a pull request | by what |
|---|---|---|
| a benchmark that stops **compiling** | yes, always was | `cargo build --all-targets` and `cargo clippy --all-targets`, which build `benches/` because `test = false` keeps them out of the *test* run and not out of the build |
| a benchmark that compiles and then **panics in setup** | **yes, since #586** | `Benchmarks run` — `cargo bench --profile ci-release -- --test` |
| a benchmark **figure** | **no, deliberately** | nothing. `--test` runs each case once and samples nothing; a shared runner's numbers are not comparable to a `tools/benchlock.sh`-serialized workstation's, so CI never produces one |

The second row was the gap, and it had cost twice. `14f69182` asked `random_poly` for 48 distinct
monomials where 25 exist at N = 2, its own assert fired, and the branch was green through review
and merge with `main` going red on the push run afterwards. Worse, every commit in such a window is
**unmeasurable** without cherry-picking the fix onto it, which is how #363's A/B could not be taken
against the tree it was meant to measure — a red job after a merge is an inconvenience, a
historical commit whose benchmarks cannot run is a hole in the record.

The job was verified non-vacuous by reinstating that exact defect: `cargo build --all-targets`
exits **0** with it present and `cargo bench --profile ci-release -- --test` exits **101**, naming
the assert. So the compile coverage alone would not have caught it.

It costs job-minutes and **no wall clock**: **4m17s and 5m14s** on the two runs that enabled it,
against `Tests (release)`'s 25–27 minutes on the same run, so it finishes well inside the critical
path. A pull request's job set is now the push set apart from one step (`Gröbner engines agree on
the slow systems`, still `push`-only), which is what makes the 20.7–25.9 figure above the right
baseline for a PR run too — this job is already inside it.

## Build configuration

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

### An out-of-tree measurement harness

That last paragraph is also **a third way to lose the ISA floor, and the only one with no mistake
to avoid.** A benchmark harness in its own crate outside this worktree, depending on `zeebra` by
path, inherits neither the `rustflags` nor the profile — cargo resolves config from the invocation
directory upward, and `[profile.release]` comes from the crate being built. `RUSTFLAGS` need never
be set. The build succeeds, the tests pass, and the numbers are smooth and self-consistent.

It happened, and because both runs were kept the cost is measured rather than estimated
(#352, [`docs/research/structured-sylvester.md`](../research/structured-sylvester.md) §5.5.1):

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

### No compiler cache, and why that is the measured choice

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
[CLAUDE.md](../../CLAUDE.md#multi-agent-coordination-claiming-work). The one invariant worth repeating
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
