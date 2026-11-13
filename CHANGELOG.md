# Changelog

All notable changes to this crate are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the crate follows
[Semantic Versioning](https://semver.org/spec/v2.0.0.html): while the version is `0.y.z`, a
change to `y` may break the public API.

## [Unreleased]

### Added

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

- `MonomialOrder` adds a `Block` variant; exhaustive downstream matches need a corresponding arm.
  F4 rejects fixed-arity order/ring mismatches with `F4Error::InvalidOptions` before comparison.

- External measurement APIs add RSS snapshot/provenance fields and a recorded-stop outcome;
  exhaustive outcome/RSS matches and external record struct literals must accommodate them.
- F4's recommended/default live allowance is 32 million entries and 512 MB, sized from measured
  reduced-row peaks (#659, #490). `baseline()` retains 20 million entries and 320 MB; explicit
  caller budgets remain enforced. The allowance bounds matrix payload, not process RSS.

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
