# Changelog

All notable changes to this crate are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the crate follows
[Semantic Versioning](https://semver.org/spec/v2.0.0.html): while the version is `0.y.z`, a
change to `y` may break the public API.

## [Unreleased]

### Added

- `util::build_profile()`: the concrete cargo profile the artifact was built with
  (`profile=…; opt-level=…; lto=…; codegen-units=…; debug-assertions=…; rustflags=…`), resolved by
  a new `build.rs` from `Cargo.toml` and the `CARGO_PROFILE_*` overrides. The comparison harnesses
  write it into `Environment::build` instead of a hand-typed "release; fat LTO" (#1172).
- `fglm_to_lex_with_control` and `FglmControl`: a cooperative wall deadline and `AtomicBool`
  cancellation for one FGLM conversion (#1167). One control spans enumeration, operator
  construction (batch workers poll and are joined), every Wiedemann attempt and the classical
  fallback, which gets no fresh allowance. A stop is the new `FglmError::DeadlineExceeded` or
  `FglmError::Cancelled`, naming an `FglmStage`, and `FglmStatistics::stopped_at` records it with
  partial statistics; an unlimited control changes neither basis nor statistics. The planner does
  not use it. Breaking: an exhaustive `FglmError` match or `FglmStatistics` literal needs the new
  variants or field.

- Behind `research-sigf4`, `SigF4Options::lead_ideal_stop` (on by default, graded-lex only): once
  a signature degree adds no new minimal lead, the engine finishes with conventional F4 over its
  elements at minimal leads and the inputs, which returns the same basis (#1140).
  `SigF4Statistics::lead_ideal_stop`, `lead_ideal_complete` and `lead_ideal_handoff` report it.
  Breaking: an exhaustive `SigF4Options` or `SigF4Statistics` literal needs the new fields.

- `linalg::lane`: a dense small-prime "lane" kernel for primes up to 46337, using `u32` delayed
  reduction (#945). `FiniteField::small_prime_lane()` returns `None` by default; it is implemented
  for `PrimeFieldElement32`. Behind `research-sigf4`, `SigF4Options::small_prime_lane` runs the
  signature engine's reductions in it. The option is **off by default**, and nothing selects it
  automatically. It gives the same basis and about 3× on dense MQ at 16 workers, but up to 7% slower
  on 6–16 ms sparse solves, which fail #945's gate. Retained opt-in by owner decision; automatic
  dispatch is #1123. Breaking: an exhaustive `SigF4Options` literal needs the new field.

- `PackedGf2Statistics::xor_words` and `linalg::gf2::PackedStatistics::xor_words`: the `u64`
  words the packed `GF(2)` kernels' `xor`s write, and `PackedGf2Statistics::residual`, the
  residual-width sweep's counters (#1077). Breaking: an exhaustive literal of either statistics
  struct needs the new field.

- `F4Options::graded_engine` and `GradedEngine`: with `GradedEngine::Adaptive`, `f4_with_options`,
  `f4_reported` and the solvers built on them run graded orders (grevlex, graded-lex) through
  `f4_signature`'s pre-solve dispatch, with the same reduced basis; `F4Statistics::graded_route`
  records the decision. Off by default at every preset, so nothing changes unless a caller opts in;
  Lex, `Weighted` and `Block`, `f4` and the observer entry points keep conventional F4. Breaking:
  an exhaustive `F4Options` or `F4Statistics` literal needs the new field (#941). Graded-lex
  always runs conventional F4 (`ShippingReason::Order`, #961), and the signature route charges
  the live-byte budget at every worker count (#962).

- `F4Options::max_certify_time`, a wall budget for the `certify` check separate from
  `max_wall_time`, checked between reductions. Running out is the new
  `F4Error::CertificationTimeBudgetExceeded { progress }` (`StopKind::Time`), never
  `CertificationFailed`; `progress` is a `CertificationStopped` saying which check was running and how
  far it got. `certify_f4_output_within` is the direct entry point (#899). Breaking: an exhaustive
  match on `F4Error` or an exhaustive `F4Options` literal needs the new variant or field;
  `CertificationReport` is unchanged.

- `certify_f4_output_with_workers` and `ParallelForward::max_workers`. F4's `certify` option now
  reduces against divisors prepared once and spreads the reductions over the call's workers, with
  the serial report at every worker count; Eco-12 and MQ11 certify inside the 600 s budget (#887).

- `berlekamp_massey`, the minimal recurrence of a sequence, and half-GCD routes for `xgcd` and
  `partial_bezout` above measured per-width crossovers; Wiedemann reconstruction uses both (#815).

- `MultiplicationOperator::column_entries`, a sparse view of one operator column, and the
  `sparse_matvec_throughput` example measuring CPU sparse matvec throughput per field, storage
  format, block width and thread count (#87).

- Checked bounded R1CS v1 import with original-wire/row identity, independent sparse-row assignment
  evaluation and caller-sized polynomial expansion (#725).

- Checked two-block product orders for direct F4 partial elimination, canonical order identities,
  and a runnable suffix-basis extraction example (#680).

- A pinned standalone sdiehl/groebner F4 comparand with full independent reduced-basis checking,
  explicit Rayon worker counts, wide-prime controls and recorded build identities (#678).
- Completed driver runs report child kernel RSS snapshots, and competitive history regeneration
  preserves the original RSS measurement provenance.
- Optional sampled child RSS enforcement in the subprocess supervisor, with memory stops
  distinguished from wall limits and solver failures.

- Opt-in large F4 matrix captures with pinned fingerprints, explicit budgets and prefix selection
  that stops before eliminating the selected matrix (#640). The large entry uses an explicit
  64-million-entry / 1.024 GB allowance without changing ordinary defaults. Observers can request this stop with
  `BatchObserver::should_stop`; F4 reports `F4Error::StoppedByObserver` rather than a partial basis.

- Certified scalar Wiedemann order conversion with explicit strategy selection, bounded projection
  retries, classical fallback, workspace budgets and route statistics; a reproducible comparison
  example with optional exact msolve eliminant checks.

### Changed

- The packed `GF(2)` route (`Gf2Elimination::Auto`, the default, and `Packed`) sweeps its pair
  rows against the reducer block on the residual columns only, the columns no reducer leads,
  instead of at the full width (#1092). Same eligibility, budgets, batch choice and basis. The
  bench host measured `Auto` 1.03x, 1.06x and 1.19x faster in total on #1077's development,
  held-out n = 15 and n = 16/17 square MQ sets, with peak RSS 0.89x–1.07x
  (`docs/research/gf2-residual-packing.md` §5). The full-width sweep stays reachable for
  measurement as the new `Gf2Elimination::FullWidth` and `AutoFullWidth`. The
  `research-gf2-residual` feature and its `Residual`/`AutoResidual` variants are removed. Breaking:
  an exhaustive match on `Gf2Elimination` needs the new variants.

- The signature engine (`research-sigf4`) refuses `GradedLexicographic` with
  `SigF4Error::Unsupported` unless the new `SigF4Options::allow_graded_lex` is set, so forcing it
  through `sig_f4`/`sig_f4_reported` no longer reaches #961's memory exhaustion. The dispatcher
  already sent graded-lex to conventional F4 and is unchanged. Breaking for `research-sigf4`: an
  exhaustive `SigF4Options` literal needs the new field (#1049).

- `MonomialOrder` adds a `Block` variant; exhaustive downstream matches need a corresponding arm.
  F4 rejects fixed-arity order/ring mismatches with `F4Error::InvalidOptions` before comparison.

- External measurement APIs add RSS snapshot/provenance fields and a recorded-stop outcome;
  exhaustive outcome/RSS matches and external record struct literals must accommodate them.
- F4's recommended/default live allowance is 32 million entries and 512 MB, sized from measured
  reduced-row peaks (#659, #490). `baseline()` retains 20 million entries and 320 MB; explicit
  caller budgets remain enforced. The allowance bounds matrix payload, not process RSS.
- `f4_signature` and `GradedEngine::Adaptive` send graded-lex to conventional F4, reported as the
  new `ShippingReason::Order`: the signature engine passed 8 GiB there on katsura-9, katsura-11
  and MQ11 (#961). Grevlex routing is unchanged. Breaking only for an exhaustive in-crate match;
  `ShippingReason` is `#[non_exhaustive]`.
- The signature engine's serial cascade, which `f4_signature` runs at one worker, now charges
  `max_live_bytes` (and a tightened `max_live_nonzeros`, through the dispatch) and refuses with
  `TooManyLiveBytes`, from which the dispatch falls back to conventional F4 (#962).
  `SigF4Statistics::claim_peak_live_bytes` now reports either cascade's peak.

### Fixed

- Every worker team (F4's parallel symbolic preprocessing, forward elimination, candidate finishing
  and certification; the signature engine; FGLM batches; resultant sampling) now joins each worker
  thread before its call returns. Before, a team joined only implicitly by `std::thread::scope` let
  its threads finish exiting beside the next team, so more than `workers` threads could run at once
  (#1002).

## [0.1.0] - 2026-11-10

The first release on crates.io. Before it, the crate was used only as a git dependency, and the
breaking changes below matter only to anyone who built against a git revision.

### Added

- Finite fields (prime, 256-bit prime, binary and odd-characteristic extension fields), big
  integers, number theory, univariate and sparse multivariate polynomials, NTT/FFT, dense and
  sparse linear algebra, Reed–Solomon codes, Gröbner bases (Buchberger, F4, FGLM) and
  zero-dimensional polynomial system solving.
- `external-runners` feature (default, no dependencies): drive msolve, Groebner.jl, Sagebrush
  and Singular as subprocesses.
- `proptest` feature: `Arbitrary` impls for the public types.
- Minimum supported Rust version 1.91, checked in CI.

### Changed

- **Breaking:** the `proptest` `Arbitrary` impls are behind the optional `proptest` feature, so a
  default build no longer compiles proptest (#676).

### Removed

- **Breaking:** `grobner::research` — the cryptanalysis research moved out of the crate into a
  separate repository (#671).

[0.1.0]: https://github.com/mfaulk/zeebra/releases/tag/v0.1.0
