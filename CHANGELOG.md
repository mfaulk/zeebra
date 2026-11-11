# Changelog

All notable changes to this crate are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the crate follows
[Semantic Versioning](https://semver.org/spec/v2.0.0.html): while the version is `0.y.z`, a
change to `y` may break the public API.

## [Unreleased]

### Added

- Certified scalar Wiedemann order conversion with explicit strategy selection, bounded projection
  retries, classical fallback, workspace budgets and route statistics; a reproducible comparison
  example with optional exact msolve eliminant checks.

### Changed

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
