# #966 M33-0: aligned timed region, admission draw, comparand pins and thread census

Plan: [`docs/MILESTONE-COMPETITIVE-BENCHMARKING.md`](../../docs/MILESTONE-COMPETITIVE-BENCHMARKING.md)
§5, §9.1, §11. This directory holds Part 1. The baseline cohort (Part 2) is added by a later PR.

**Measured at:** the harness builds `3cd261a7` (census inputs only) and `b3c15ff3` (timed-region
check, admission), both `git archive` builds whose `src/` equals F0 `31e334bd` (M32 final main,
#960), on 2026-11-21. Comparands as in [pins.json](pins.json). The census and the timed-region
check ran on CPUs 24–39 beside other sessions' builds, because another campaign held the CCD 1–2
reservation; their walls are not timing results. **Host:** Threadripper PRO 5995WX.

## Files

| File | What |
|---|---|
| [`tools/external/basis_digest.py`](../../tools/external/basis_digest.py), [`examples/support/basis_digest.rs`](../../examples/support/basis_digest.rs) | `m33-basis-v1`, the one basis digest every M33 solver is compared by; Python reads any solver's text, Rust reads Zeebra's basis without rendering it |
| [admission.py](admission.py) | `pool` → [candidates.json](candidates.json), `run` → `admission.jsonl`, `draw` → `held-out.json` |
| [census.py](census.py) → [census.jsonl](census.jsonl) | per-thread CPU ticks of msolve at 1/4/8/16 and of grobx under a 16-worker request |
| [grobx-pin.sh](grobx-pin.sh), [grobx-0.155.1.Cargo.lock](grobx-0.155.1.Cargo.lock) | builds the grobx driver at the M33 pin beside the repository's own |
| [pins.json](pins.json) | comparand commits, versions, build flags and executable SHA-256s |
| [timed-region.json](timed-region.json) | the one-row check of the aligned timed region (Eco-12) |
| [test_admission.py](test_admission.py) | unit tests for the draw rule and the digest encoding; run in CI |

## 1. Aligned timed region (plan §11.3)

`sig_f4_study --digest-only` renders nothing. It prints `basis_m33` instead, computed in process
and timed as `basis_m33_ns`. `--write-basis` writes the text for a separate verification run.
msolve writes its basis file and grobx builds its basis text inside its own call; neither can be
avoided, so every M33 row reports the Zeebra ratio both with and without `basis_m33_ns`.

The digest hashes a compact binary encoding (LEB128 exponents, decimal coefficients) rather than
text, because hashing dominates its cost: Eco-12's reduced basis has 400,000 terms (12 MB as
text). Two earlier encodings cost more than the render they replaced (200 ms as sorted tuples with a
string round trip, 150 ms with u32 exponents); the LEB128 form costs about 90 ms.

One-row check, wide64/eco-12, `--engine entry --workers 1`, n = 5 each, alternated:

| Arm | Process wall (median) | Render | Digest |
|---|---:|---:|---:|
| render (M32 harness behaviour) | 2,785 ms | 152 ms | 91 ms |
| `--digest-only` | 2,588 ms | 0 | 92 ms |

`basis_m33` from the process equals `basis_digest.py` over the rendered basis. The process wall
drops by 197 ms (7.1%), and no render remains inside it.

## 2. Comparand pins

| Solver | Pin | Latest upstream | Change |
|---|---|---|---|
| grobx | **0.155.1** `8005a2a1` (M33 current) | the same (2026-11-20; no release tags) | 0.73.3 → 0.155.1 in one upstream commit, 300 files; its notes claim GF(p) calls 1.43× faster than 0.73 |
| grobx | 0.73.3 `1854835d` (repository pin, M31 continuity) | — | unchanged; the repository pin is not moved here |
| msolve | 0.11.0 | 0.11.0 (2026-10-09) is still the latest release | unchanged |

The driver builds against 0.155.1 with no source change. Moving the repository's own pin
(`src/grobner/external/grobx.rs`, `tools/external/wide-corpus.py`, the driver) is left to a
follow-up issue, so this PR changes no library constant.

## 3. Thread census (plan §11.5)

`active` counts threads that gained a CPU tick during the attempt; `concurrent` is the most that
gained a tick within one 50 ms interval. n = 3 per cell; all 66 attempts exited 0.

| Solver | Rows | Request | active | concurrent |
|---|---|---|---:|---:|
| msolve 0.11.0 | MQ10, Katsura-11 at GF(32003) and GF(2³¹−1) | `-t 1/4/8/16` | 1 / 4 / 8 / 16 | 1 / 4 / 8 / 16 |
| grobx 0.73.3 | Eco-12, Katsura-11 at 2⁶⁴−353; MQ11 at Goldilocks | 16 workers | 1 | 1 |
| grobx 0.155.1 | same | 16 workers | 1 | 1 |

msolve uses exactly the threads it is given. grobx computes on one thread whatever it is asked
for; 0.155.1's own source says so (`src/call.rs:172`). Track G therefore stays at one worker, and the
go/no-go rule's multi-worker branch does not apply.

Two side observations, from walls taken beside builds and not timing results:

- **Katsura-11 at 16 workers.** msolve runs it 3.8× slower than at 8 (GF(32003): 2.49 s against
  0.66 s; GF(2³¹−1): 3.51 s against 0.91 s). This is the scaling anomaly §8.4 guards against.
- **MQ10 / GF(32003) at 4 and 8 workers.** msolve finishes in about 150 ms, under §5.2's 300 ms
  floor. If the baseline confirms this, MQ10 / GF(32003) cannot score a win at those counts, and
  Katsura-11 becomes the likelier Track M primary.

## 4. Candidate pool and held-out draw (plan §5.2, §5.4)

[candidates.json](candidates.json) lists 76 candidates per track:

- **Families:** Katsura 8–12, Eco 10–13, Cyclic 6–8, Noon 7–8, and MQ 9–11 at fresh seeds 1–8.
- **Fields:** wide64 and Goldilocks for Track G; GF(32003) and GF(2³¹−1) for Track M.
- **Form:** each instance is built by `sig_f4_study --generate`, in the external contract's
  canonical form.

A family size named anywhere in M29–M32's research directories, findings or plan is excluded at
every field. That is stricter than the plan's per-instance rule, so no field twin of a tuned row is
drawn. 56 candidates per track remain.

`admission.py run` walks each track in draw order until two pass, with at most one MQ. It
retains only pass/fail per criterion and the basis digests; no wall is recorded.

The criteria:

- **Zeebra** (`--engine entry`, digest-only): at 1 worker for Track G; at 1 and 16 workers for
  Track M.
- **Competitor:** grobx raw at 1 worker; msolve at 1 and 16 workers.
- **Floors and ceilings:** the competitor at ≥ 300 ms; both sides at ≥ 2× their own Katsura-4
  control; everything within 180 s and 8 GiB.
- **Reference digest:** grobx certified (wide fields) or Singular (below 2³¹), agreeing with both
  sides.

The drawn rows and their outcome are in `held-out.json` and posted on #965.
