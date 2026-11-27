# Building, testing and CI

How to build and test Zeebra, what CI enforces, and how the build is configured.

Zeebra builds on stable Rust; no nightly toolchain or feature gates are required.

```sh
cargo build
cargo test
```

Development checks, matching what CI enforces. The "Format and lint" job runs
`scripts/ci-lint.sh`, one step per subcommand, so the same commands run locally:

```sh
scripts/ci-lint.sh all     # fmt clippy clippy-no-default proptest-graph rustdoc package
scripts/ci-lint.sh fmt rustdoc   # or any subset, in order
cargo test --doc
cargo +1.91.0 check --lib --all-features --locked   # the declared MSRV
```

`ci-lint.sh` honors the caller's `CARGO_TARGET_DIR` and `TMPDIR`. Off CI, an unset
`CARGO_TARGET_DIR` defaults to `/buildcache/cargo-target/zeebra-lint-<worktree>` when that
directory exists, never to the worktree under `$HOME`.

### Pre-push hook

`.githooks/pre-push` runs the cheap half of that job before a push, judged by the pushed commits'
diff against `origin/main`:

| Pushed diff touches | Runs |
|---|---|
| any `*.rs` | `fmt`, `rustdoc` |
| `Cargo.toml`, `Cargo.lock`, `.cargo/`, other files under `src/`, `README.md`, `docs/guide/*.md` | `rustdoc` |
| none of these (research prose, scripts, records) | nothing; exits at once |

Clippy is deliberately left out: it is too heavy to run on every push across concurrent agents,
so run it yourself before pushing Rust changes. The checks run on the working tree, so push from
a clean one. Enable the hook once per clone; the setting lives in the shared repository config,
so every worktree picks it up:

```sh
git config core.hooksPath .githooks
```

Keep the path relative. Git resolves it against the pushing worktree, so each branch runs its own
copy of the hook. An absolute path (`/…/zeebra/.githooks`) makes every worktree run the main
checkout's copy instead, and the hook stops running altogether when the main checkout is on a
branch without `.githooks/`. If the pushing branch predates `scripts/ci-lint.sh`, the hook prints
a notice and lets the push through, since CI runs the same checks.

`git push --no-verify` skips it. `bash scripts/test/pre-push-test.sh` tests the classification.

The shell tooling under `scripts/agent/` and `tools/` is invisible to every Rust job, so CI's
`agent-scripts` job checks it separately. The shellcheck arguments are globs rather than a file
list, so a script added under either directory is checked without anyone remembering to add it:

```sh
shellcheck -S warning scripts/agent/*.sh scripts/agent/test/*.sh \
  tools/*.sh tools/test/*.sh tools/external/*.sh tools/external/smoke/*.sh
bash scripts/agent/test/zb-claim-test.sh
bash scripts/test/pre-push-test.sh
bash tools/test/rss-guard-test.sh
bash tools/test/merge-base-age-test.sh
bash tools/test/benchlock-test.sh
bash tools/test/check-measurement-provenance-test.sh
bash tools/test/ci-scope-test.sh
bash tools/test/cpu-context-test.sh
bash tools/test/bench-reserve-test.sh
bash tools/test/bench-isolation-audit-test.sh
bash tools/test/bench-clock-test.sh
python3 tools/test/bench-contamination-test.py
python3 tools/test/bench-stats-test.py
python3 tools/test/corpus-lineage-test.py
python3 tools/test/m34-public-corpus-test.py
python3 tools/test/m34-structural-corpus-test.py
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


Two other `#[ignore]`d tests are unimplemented placeholders — a `BigUInt` sampling distribution
check and a rare division branch — and they panic if run. A bare `cargo test -- --ignored`
therefore reports those two as failures; the commands above select the tests that are meant to
pass.

## CI coverage and runtime

PR CI is kept fast so agents are not blocked on it (#924). Agents build and test locally before
opening a PR (see *Before opening a PR* below), so PR CI is a backstop, and the slow checks run in
the nightly scheduled run (`17 9 * * *`, UTC) and on manual dispatch instead.

| Run | Checks |
|---|---|
| PR or push to `main`, code change | Debug tests (`--tests`), debug doctests, Clippy, Rustdoc, package, MSRV and shell/provenance checks |
| PR or push to `main`, only `README.md` or guide Markdown | Debug doctests, guide-inclusion test, formatting, Rustdoc, shell/provenance checks |
| PR or push to `main`, only other prose (`docs/` outside the guides, `research/` Markdown, `CHANGELOG.md`, `CLAUDE.md`) | Shell/provenance checks and merge-staleness notice |
| Nightly and manual dispatch | Everything above, plus `cargo build --all-targets`, the optimized tests, the research-artifact checks, the comparand replay, the benchmark smoke run and the 2-attempt `bench-job` smoke (`tools/bench-job-smoke.sh`, timing ignored) |
| Manual, local only | Performance campaigns and gates (`tools/bench-job` under a reservation). No GitHub job times anything: there is no self-hosted runner, and shared-runner timing is meaningless |

`Classify changes` reads the full PR diff with NUL-separated paths. `tools/ci-scope.sh` uses a
conservative allowlist; unknown paths, code, config, scripts and measurement JSON select the code
row. Empty or malformed input also selects it, and a failed git read fails CI. Pushes to `main`
select the code row; its `nightly` output is true only for the schedule and manual dispatch.

To run the nightly checks on a branch before merging — worth it for a change to release-only
arithmetic, a research feature or a benchmark — dispatch the workflow on it:
`gh workflow run rust.yml --ref <branch>`.

A scheduled run with a failed job opens an issue titled `Nightly CI failed`, or comments on the
open one, so the failure reaches `orient` rather than only the owner's email. Close it when main is
green again.

`CI complete` always runs and fails if any dependency failed or was cancelled. Intentionally
skipped jobs are accepted.

`main` is protected: every change lands through a pull request, and `CI complete` and
`No coding-agent authors or co-authors` must pass first. The rules bind admins too, which matters
because every agent works under the owner's admin token. Force-pushes and deleting `main` are
blocked. Branches need not be up to date with `main` before merging; see *Testing the merged
result* for why.

`Agent authorship` (`.github/workflows/agent-authorship.yml`) fails a pull request or a push to
`main` when a commit names a coding agent — Claude, Codex, Gemini, DeepSeek, Copilot and the like —
as author, committer or `Co-authored-by:`, or when the pull request body carries such a line, which
a squash merge would copy onto `main` (#1058). It is its own workflow so that editing the body
re-runs it without the test suite. `tools/check-agent-authorship.sh <base> <head>` runs the same
check locally; names a person can also have, such as Claude or Devin, count only when nothing but
product words or version numbers accompany them.

`Research artifacts` runs the research-instrument tests, artifact summaries and the delayed-reduction
pilot. It is a matrix with one runner per set in `tools/ci-research.sh` — `default`,
`delayed-reduction`, `comparand-replay` and one per `research-*` feature — because every feature set
recompiles the whole crate, and run in one job they took 15–38 minutes (#922). A set compiles only
under its own feature, and a new `research-*` feature needs a set of its own;
`tools/test/ci-research-test.sh` enforces both and that the workflow matrix matches the script.
`Swatinem/rust-cache` saves caches only from `main` (scheduled runs included): PR saves overflowed
the repository's 10 GB cache quota and evicted `main`'s, which every PR restores from.

The suite runs under Nextest in debug on every code change and under `ci-release` nightly. Both
matter: release arithmetic has `debug-assertions` and `overflow-checks` disabled. The nightly
optimized and smoke jobs override `ci-release` with `CARGO_PROFILE_CI_RELEASE_OPT_LEVEL=3` and
`CARGO_PROFILE_CI_RELEASE_LTO=thin`. In debug, F4 additionally recomputes basis leaders, monicity and
ordering and validates the critical-pair queue each batch; optimized tests do not run those checks.

Both test jobs select `--tests`: the library, binary, integration tests and the examples marked
`test = true`. A bare `cargo test` also compiles every `test = false` example, which runs nothing
and was 60% of the optimized job's compile time (#921). Clippy checks all targets with all features
and again without default features, so those examples still compile-check on every code change;
the nightly `cargo build --all-targets --timings` catches example-only linker errors.

### Before opening a PR

Run locally what PR CI no longer runs for the change at hand, with a private `CARGO_TARGET_DIR`:

```sh
cargo nextest run --profile ci --tests                    # always, for a code change
cargo test --doc -j24 -- --test-threads=16
scripts/ci-lint.sh clippy clippy-no-default
# Arithmetic, F4 or linear-algebra kernels: the optimized suite
cargo nextest run --profile ci --cargo-profile ci-release --tests
# A research feature, record or summary: its set (list them with --sets)
bash tools/ci-research.sh <set>
# A benchmark target
cargo bench --profile ci-release -- --test
```

Other CI commands:

```sh
cargo test --profile ci-release --tests --no-run --timings
CARGO_PROFILE_CI_RELEASE_OPT_LEVEL=3 CARGO_PROFILE_CI_RELEASE_LTO=thin \
  cargo test --profile ci-release --doc -- --test-threads=4
cargo build --all-targets --timings
bash tools/test/ci-research-test.sh
bash tools/test/ci-scope-test.sh
bash tools/test/cpu-context-test.sh
bash tools/test/bench-reserve-test.sh
bash tools/test/bench-isolation-audit-test.sh
bash tools/test/bench-clock-test.sh
python3 tools/test/bench-contamination-test.py
```

Release compilation and execution are separate steps. Cargo's HTML build-timing reports are
uploaded as `release-build-timings` and `debug-build-timings` from nightly runs. Compare compiler
time plus test time when tuning a CI profile. Shared runners provide CI latency evidence, not
publishable algebra benchmark measurements. Local `cargo bench` and `cargo test --release` still use
the production release profile, with fat LTO and one codegen unit.

The benchmark smoke run executes because compilation alone missed a setup panic in #586.
`cargo bench --profile ci-release -- --test` executes each case once and takes no samples;
`cargo test --benches` instead uses the unoptimized dev profile. `test = false` excludes benches
from a plain `cargo test`, while `bench = false` on the library and binary prevents duplicate unit
runs in the benchmark job. The isolated Nextest tests are important for process-wide peak-memory
checks; a shared-process benchmark harness cannot substitute for them.

The lint job also checks that the optional `proptest` dependency stays out of a default consumer's
normal dependency graph, builds Rustdoc with warnings denied, and runs `cargo package --locked`
to validate the packaged source in isolation. The MSRV job checks only the library at Rust 1.91.0;
tests, benches and dev-dependencies may use newer Rust. Raising that MSRV belongs in `CHANGELOG.md`.

Each PR and branch has one run per event in flight; a newer push cancels its predecessor. Main
receives the fast push checks and the nightly run. The suite is not sharded: duplicate compilation
would be the dominant cost, so splitting test execution is not the first optimization to apply.

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
an assertion. At the original 2026-11-07 decision, the release job averaged **806 s over 25
successful runs**, worst case 983 s, and the debug job took 318 s. That historical configuration
would admit
**4.5 merges an hour**. Against that, the week to 2026-11-07 merged 155 pull requests, **58 of them
on 2026-11-06 alone**, peaking at **14 in one hour**; the median gap between consecutive merges was
686 s, and **59 % of consecutive merges were less than one release job apart**. Re-running before
each of that day's 58 merges is **13.0 hours of CI inside a 24-hour day**. These figures explain the original decision; they are not a current latency estimate.

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
  with the full check set. Its current cost is visible in Actions; the earlier 20.7–25.9
  job-minute estimate predates the expanded suite and is not a current budget.

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
is still cheap to run before merging anything that changes the corpus or
either engine's side of the comparison. The test that #339 is named for lives here:
`grobner::external::msolve::tests`, driven from `corpus::ladder()`.

## What a pull request validates in `benches/`

Code PRs get both all-target Clippy checks and actual benchmark smoke execution. These catch
different failures: a missing import fails compilation, but the impossible random-polynomial setup
in #586 compiled and then panicked. The smoke job runs on every code PR, so a benchmark remains
runnable when its commit becomes a measurement baseline. Documentation-only PRs skip it according
to the allowlist above; a changed benchmark source always selects the full suite.

CI never publishes benchmark figures: `--test` executes each case once without sampling. Real
measurements still use the production profile and `tools/benchlock.sh`: a quiet machine for an
absolute figure, or a reserved CCD (`tools/bench-reserve.sh`) for an interleaved A/B ratio — see
`docs/guide/benchmarking.md`, *Reserved CCDs*.

## Gating a performance candidate

A milestone plan or anchor issue fixes a candidate's gates before the read they govern; how a
ratio becomes a verdict is in [`benchmarking.md`](benchmarking.md), *Statistics and verdicts*.
This section is the shape those gates take. It comes from a review of about twenty rejected or
deferred candidates (#1195), several of which were rejected on a question they never asked.

Before the read, a plan's gate section states for each candidate: whether it is global or
conditional; for a conditional one, its regime rows, the properties its rule may read and its
controls; each gate's comparator; any bundle it belongs to; and the thresholds.

**Global or conditional.** A *global* candidate runs on every input its route accepts. Its
adverse controls are measured with it on, and a regression there is evidence against it. A
*conditional* candidate is meant to run only on a regime — a field band, an input shape, an order,
a batch size — and has two gates, scored and reported separately:

- **Regime gate.** It wins by its declared margin on development and held-out rows of the regime
  it claims.
- **Dispatch gate.** A frozen rule over properties known before the solve or per batch admits the
  regime rows and keeps the mechanism off the rows it hurts. The adverse controls are measured
  **with the rule applied**, and the rule's own cost — feature extraction, a discarded probe,
  conversion — is inside complete-task time. Variable count or family name alone is not a
  property a rule may read.

A control measured with a conditional mechanism forced on is diagnostic: it specifies the rule and
decides nothing. #945's lane kernel gained 2.8–3× on dense rows and lost 3.6–7.3% on Katsura-8 and
Cyclic-6 with the lane forced on. Those losses are #1123's specification, not a finding against the
kernel.

| Regime gate | Dispatch gate | Disposition |
|---|---|---|
| pass | pass | eligible for default adoption under the plan's adoption rule |
| pass | fail, or not yet scored | opt-in; the rule failed, not the mechanism |
| fail | — | rejected for that regime |
| untested | — | deferred |

**One comparator per rule.** Each gate names one comparator: the frozen Zeebra baseline, or the
best qualified Zeebra configuration, for an adoption claim; a named external route (grobx,
msolve) for a competitive claim. No rule requires both. The other ratio is reported beside the
verdict and decides nothing. #1030's M4GB reference was 5.8–16× faster than Zeebra's best qualified
arm on held-out dense MQ and was rejected because its rule also required beating grobx, which
answered whether M4GB is the fastest engine and left open whether its organization would help
Zeebra.

**Bundles.** A per-candidate wall threshold rejects independent gains that would clear it
together: M33's 8% Gate A bar stopped interreduction in column space at −5.2% on Eco-12 until a
different target row was named (G2-2, then adopted). A plan may declare, before the read, a bundle
of independent candidates — different stages or mechanisms — scored jointly against the wall
threshold. The bundle is measured as one build, never multiplied from its parts, and each
component's own paired ratio must have an upper 95% bound ≤ 1.0, so no component is carried by the
others. M35 §9.9 is the worked form.

**Untested is not rejected.** A conditional mechanism whose trigger fires on no held-out row has
produced no evidence about itself, and is recorded as *untested* with the rows it was tried on:
#1134's refusal fallback fired on none of 14 out-of-sample rows. A frozen rule that admits no
held-out regime row likewise leaves the regime gate untested. Both are deferrals, never rejections.
Insufficient precision at the budget cap is *inconclusive* under the plan's stopping rule, which
is also a deferral.

## Build configuration

`.cargo/config.toml` sets an instruction-set floor of `x86-64-v3` — the Haswell/Excavator feature
level, which brings AVX2, BMI2, FMA, LZCNT and MOVBE — for `x86_64` targets. `[profile.release]`
in `Cargo.toml` turns on fat link-time optimization and a single codegen unit.

Both exist for measurement. Field arithmetic is a handful of small generic functions called from
inner loops in other modules, so without cross-codegen-unit inlining the elimination kernels pay a
function call per field operation. A single codegen unit also makes benchmarks reproducible: with
the default of 16, moving code between modules repartitions the crate and can shift a measurement
for reasons unrelated to the change. The cost is build time.

Which profile a figure was taken under is recorded, not assumed: `build.rs` resolves the concrete
`lto`, `codegen-units` and `opt-level` of the profile being built, and `zeebra::util::build_profile()`
returns them for a measurement record's `build` field. Override profile settings through
`CARGO_PROFILE_<NAME>_<KEY>` or the manifest, which the stamp reads; a `--config` override is only
partly visible to it (`docs/research/external-comparison-protocol.md` §10.4).

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

`[profile.dev]` sets `debug = "line-tables-only"`, which `test` inherits. Full debuginfo made each
test and example binary about 1.4 GB, and `cargo test` links over a hundred of them, so linking
dominated the edit loop. On 2026-11-16, measured with mold and without sccache, `cargo test
--no-run` after a one-line edit fell from 73–103 s to 15–16 s, and `target/debug` shrank from 65 GB
to 24 GB. Backtraces still carry file and line. For a debugger session that needs local
variables, restore full debuginfo for that invocation:

```sh
CARGO_PROFILE_DEV_DEBUG=true cargo test --lib -- <filter>
```

While iterating, `cargo test --lib` or `cargo nextest run --lib` also skips building the ~90
examples that a plain `cargo test` compiles and links.

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
  anything measured runs with a private target directory and an empty wrapper.


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

The release job also runs the ignored reduced-batch resource regression on every Rust PR. It
checks the measured 109-element basis under the recommended live budget and confirms that an
explicit historical 20-million-entry cap still refuses. The debug suite leaves that workload
ignored for cost; run it locally with the command in
[`src/grobner/f4/test-data/README.md`](../../src/grobner/f4/test-data/README.md).

## Retrieving IACR ePrint papers

`eprint.iacr.org` answers HTTP 403 to automated PDF requests from agent sessions (its HTML abstract
pages still load). [`scripts/fetch-eprint`](../../scripts/fetch-eprint) fetches the PDF from the
public read-only mirror [eprint.iacr.asia](https://eprint.iacr.asia/about.html) instead, whose
`robots.txt` disallows only `/archive/`, and caches it for every checkout on the machine.

```bash
scripts/fetch-eprint 2025/2340                              # prints ~/.cache/eprint/2025-2340.pdf
scripts/fetch-eprint https://eprint.iacr.org/2025/2340.pdf  # same paper, same file
scripts/fetch-eprint --text 2025/2340                       # prints a cached pdftotext -layout file
scripts/fetch-eprint --refresh 2025/2340                    # download again (a newer revision)
scripts/fetch-eprint --import ~/Downloads/paper.pdf 2025/2340  # install a copy found elsewhere
```

Accepted inputs are `YYYY/N` and `http(s)://eprint.iacr.org/YYYY/N[.pdf]` or the same on
`eprint.iacr.asia`; anything else is refused with status 64 before any request. The PDF path (or
text path) is the only stdout; diagnostics go to stderr.

**Cache.** `$XDG_CACHE_HOME/eprint/` (default `~/.cache/eprint/`), named `YYYY-NNN.pdf` with the
number zero-padded to three digits, so `2021/51` and `2021/051` are one file. A valid cached copy is
returned without a network request, including when the mirror is down. Downloads go to a `.part`
file in the cache directory, are validated, and are renamed into place, so a reader never sees a
partial file. A per-paper `flock` makes concurrent fetches of one paper download it once; the empty
`.YYYY-NNN.lock` files it leaves are harmless. A cached file that is not a complete PDF is discarded
and fetched again. Inspect with `ls ~/.cache/eprint`; clear with `rm -r ~/.cache/eprint`.
`EPRINT_CACHE_DIR` overrides the location.

**Validation and retries.** A download is accepted only on HTTP 200 with a body that starts with
`%PDF-` and has `%%EOF` in its last 2 KiB. An HTML body served with 200 (an error or challenge
page) is rejected at once. 429, 5xx, timeouts, connection failures and truncated PDFs are retried up
to three attempts with 2 s / 4 s back-off (`EPRINT_RETRIES`, `EPRINT_RETRY_DELAY`); 403 and 404 are
not retried.

| Exit | Meaning |
|---:|---|
| 0 | path printed |
| 1 | the mirror does not have it (403, 404, HTML, not a PDF) |
| 2 | network or lock failure after the bounded retries |
| 3 | `--text` requested but `pdftotext` is missing or produced nothing; the PDF is cached |
| 64 | malformed id, URL, host or option |

On status 1 or 2 the diagnostic gives the paper's abstract URL and the next step: find an authorized
copy (arXiv, `tosc.iacr.org` / `tches.iacr.org`, HAL, an author's page) and install it with
`--import`, which validates it like a download.

**Dependencies.** `bash`, `curl`, `flock` (util-linux); `pdftotext` (poppler-utils) only for
`--text`. Tests: `bash scripts/test/fetch-eprint-test.sh` (needs `python3` for a local fixture
server; never touches the network).

**Text extraction is lossy.** `pdftotext -layout` keeps tables and paragraph layout well enough to
grep, but equations, subscripts, finite-field notation, algorithms set in pseudo-code and figures
come out mangled or missing. Read the PDF itself before quoting a formula, a complexity estimate or
a table entry.
