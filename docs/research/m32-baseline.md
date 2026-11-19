# M32-0: baseline, corpus pin and signature-F4 performance model (#939)

**Status:** in progress. Deliverables 1 (freeze) and 2 (corpus pin) are complete; the baseline
cohort, the symbolic-stage attribution, the cost model, #934 and #935 follow under #939.
**Measured at:** `f26b8d80` (tag `measured/939-pin`; the baseline `7b25a1ee`'s library plus the
held-out inputs in `examples/sig_f4_study.rs`), the held-out admission read only, 2026-11-19, one `bench-reserve` session on CCDs 1–2 (`zb-939`).
Executable SHA-256s, toolchain and options:
[`research/m32-baseline/identities.json`](../../research/m32-baseline/identities.json).
**Plan:** [`MILESTONE-ADAPTIVE-F4.md`](../MILESTONE-ADAPTIVE-F4.md) §7.1, §8.3, §10.
**Records:** [`research/m32-baseline/`](../../research/m32-baseline/) (every figure below is from
[`pins.json`](../../research/m32-baseline/pins.json)).

## 1. Freeze (F0)

- **M31 reference:** `8715c8ed`, M31's final `main` (#926).
- **M32 baseline:** `7b25a1ee`, `main` at the freeze (#943). Its timed `src/` equals the planning
  base `e59a90a1`'s and differs from the reference only in documentation: eight added lines, a
  performance caveat in `f4_signature`'s doc comment and one `#[doc = include_str!(…)]` in
  `src/lib.rs`. No code line differs; `Cargo.toml`, `Cargo.lock` and `.cargo/` are identical.

Both are built from `git archive` (release, fat LTO, one codegen unit, `x86-64-v3`,
`research-sigf4`); the executables' SHA-256s are in the research README.

## 2. Corpus pin

The development set is plan §10.1's, unchanged. The held-out candidates were built by the public
generators the plan names and admitted by its fixed rule (conventional F4 at 16 workers completes in
20 ms–60 s, both engines accept the field). Pins, generators and the admission evidence:
[`research/m32-baseline/README.md`](../../research/m32-baseline/README.md) §2.

| Held-out candidate | Field | F4-16 median process wall | Verdict |
|---|---|---|---|
| mq-random-10 | Goldilocks | 930.5 ms | kept |
| mq-random-12 | 2⁶⁴−353 | 104554.0 ms | dropped |
| mq-random-9 | GF(32003) | 3.1 ms | dropped |
| katsura-10 | GF(2³¹−1) | 242.4 ms | kept |
| eco-11 | GF(2³¹−1) | 427.4 ms | kept |
| cyclic-6 | Goldilocks | 7.6 ms | dropped |

Three rows are held out: MQ10 at Goldilocks, Katsura-10 and Eco-11 at GF(2³¹−1). MQ12 at 2⁶⁴−353 is
over the 60 s bound, so the held-out set has no dense MQ beyond the crossover. Cyclic-6 and the
seed-9 MQ9 (an inconsistent system, basis {1}) are under 20 ms. None is replaced.

## 3. Baseline cohort, attribution and cost model

Not yet measured (#939 deliverables 3–5).
