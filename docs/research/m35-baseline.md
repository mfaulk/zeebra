# M35-A: Z0, the M35 panel and the one-worker gap to grobx (#1162)

**Measured at:** `184b5555` (tag `measured/1162-harness`; `src/` identical to Z0 `125658bb` = tag
`measured/1162-z0`). grobx 0.155.1 at `8005a2a1` (installed `grobx-driver`, sha256 `e2572de9e89a2be2…`).
Every figure below is a **development-mode** probe (§1): it places rows in time bands and
attributes phases. **None of it is a deciding timing.**
**Plan:** [`MILESTONE-FINITE-FIELD-COMPETITIVENESS.md`](../MILESTONE-FINITE-FIELD-COMPETITIVENESS.md)
§7.1. **Tracker:** #1161. **Data:** [`research/1162-m35-baseline/`](../../research/1162-m35-baseline/README.md).

## Summary

- **Z0 is `125658bb`.** It is source-identical to `aa50a509`: the only change in between is the
  plan document. The release library suite passes at Z0 (3158 passed, 0 failed, 28 ignored).
- **The one-worker gap to grobx's default is mostly a characteristic effect.** On structured rows
  at p ≈ 2³¹, grobx is 2.5–7× faster than Zeebra's best route (Cyclic-8: 15×). At p ≈ 2⁶⁴ the
  same rows are 1.0–1.4×. Zeebra's signature engine runs at about the same speed at both primes: its 2³¹/2⁶⁴ time ratio
  is 0.88–1.05 (Eco-12: 1.93 s and 1.89 s). grobx is 2–7× faster on its 31-bit kernel than on its
  64-bit one: its ratio is 0.15–0.53.
- **Dense and sparse MQ carry the largest residual gap.** Dense MQ is 18–24× at n = 15–18, and
  96–98% of Zeebra's time there is elimination, with 80–86% of coefficient products landing on
  rows that reduce to zero. Sparse MQ is 8–10× at n = 11–12.
- **grobx's default is probabilistic.** Every grobx default run used `reduce=tests`, `sketches`
  or `combinations`. grobx's exact mode (deterministic `rows` reduction plus its exact checker) is
  slower than Zeebra wherever it finished: dense MQ n = 15 took 10.5 s against Zeebra's 3.3 s, and
  Chandrasekhar-H 11 took 133 s against 1.25 s. It did not finish in 300 s on six of nine rows.
  The primary score therefore compares an exact Zeebra against a randomized grobx.
- **Frontiers.** Under Zeebra's default limits, several rows stop on a size limit while grobx
  completes them: dense MQ n = 20 (grobx 29 s), GF(2) MQ n = 14 (110 s), Noon-10 (24 s) and
  Ellipsoid-m2 (0.5 s). Sparse MQ n = 14 and 16 at 2³¹ defeat both systems.

## 1. Method

- **Harness.** [`examples/m34_matrix.rs`](../../examples/m34_matrix.rs) gains two things:
  - `--stages`: F4's stage clocks and always-on counters, plus `SigF4Statistics` for `sig`.
  - GF(2) and GF(32003) instantiations.

  `research/1162-m35-baseline/catalog.py` writes every panel row as a `corpus-instance-v1`
  record, so Zeebra and grobx solve byte-identical inputs. `probe.py` runs each record in fresh
  processes, each pinned to one CPU.
- **Arms.**
  - `f4`: the shipping default.
  - `adaptive`: `GradedEngine::Adaptive`.
  - `f4-stages` and `sig-stages`: attribution only. The F4 stage clocks cost 4–12%, so these are
    never timing records.
  - `grobx`: raw, which is its default.
  - `grobx-certified`: grobx's exact mode. It changes grobx's trajectory, so it is the
    exact-guarantee comparator, not a passive view of the default.
- **Development mode.** There was no CCD reservation and no load gate. Another agent held CCDs 1–2
  throughout; this probe used CPUs 40–47, with a load average of about 10–19. One attempt per arm
  per row. Ratios between arms run back to back on one CPU are more robust than the absolute
  figures, and neither decides anything.
- **Correctness.** Every completed attempt's `reduced-basis-v1` digest agrees across all arms,
  grobx and grobx-certified included. No digest disagreed.

## 2. Gap table: what each candidate can plausibly remove

The plan's admission rule (§7.1) needs ≥ 20% of current solve time in the affected phase, or a
concrete fixed-budget completion limitation. The shares below are upper bounds on what a
mechanism could remove. An operation count is evidence of mechanism, not a speedup promise.

| Candidate | Affected phase, as measured | Where it is ≥ 20% | Verdict for the deciding read |
|---|---|---|---|
| **B: certified zero skipping (#1080)** | Products on zero rows × elimination share. Signature route: dense MQ 80–86% × 96–98%; Chandrasekhar-H 77% × 51–63%; Eco 55–56% × 68–80%; Katsura-12 39% × 82–84%. F4 route: 85–90% of reduced rows are zero | All in-band targets and the in-band Katsura, Eco and Cyclic controls | **Admitted.** Largest share on dense MQ (about 80% of time) and Chandrasekhar-H (about 40%). Hilbert counts need regular inputs, so the reachable share is smaller on non-regular rows |
| **C: carry signature work into conventional F4 (#1076)** | Rows whose shipping route is conventional F4: Cyclic-8 (`DegreeSpread`, 15×, forward 75%); sparse MQ n = 11–12 (signature falls back on `TooManyRows`; F4 78–98 s against grobx 8.6–9.3 s, forward 91%) | Cyclic-8 and sparse MQ | **Admitted, narrowly:** on rows the dispatcher sends to conventional F4. On signature-routed rows C has no affected phase |
| **D: matrix copying and storage traffic (#1078)** | F4 `construction` + `extraction` ≤ 4% on every in-band row. Signature `symbolic` 1–15% on in-band targets; 69% on grid-5×5 and 32% on Noon-9 | Only grid-5×5 and Noon-9, both under 2.5 s | **Not admitted as a copying mechanism** on this evidence. No counter isolates coefficient and index copying (`construction` + `extraction` is the closest proxy). The coefficient-width half of D is the same lever as E |
| **E: small-prime lane after conversion (#1123)** | Elimination 51–84% of signature time on structured rows. Zeebra's 2³¹ / 2⁶⁴ time ratio is 0.88–1.05, while grobx's is 0.15–0.53 (Eco-12 0.44 / 1.79 s; Katsura-12 0.69 / 4.16 s; Chandrasekhar-H 12 2.09 / 6.99 s) | Every in-band structured row at p ≈ 2³¹ | **Admitted, and the largest structured-row lever.** Closing grobx's 31-bit lane advantage would bring the 2³¹ rows to the 2⁶⁴ ratios (1.0–1.4×) |
| **F: one structural feasibility decision (#1034)** | No bilinear or decomposable row is in this panel | — | **No evidence here.** F proceeds on its own count decision (plan §7.6) |

**Fixed-budget completion limitations** (the rule's second clause):
- **Noon-10.** Adaptive's signature attempt falls back on `TooManyRows`, then shipping F4 stops on
  `TooManyColumns`. The forced signature engine completes it in 22.5 s, against grobx's 24 s. This
  is a routing and limit interaction, not an arithmetic gap.
- **Dense MQ n = 20.** Stops on `TooManyLiveBytes` (619 MB against a 512 MB limit).
- **GF(2) MQ n = 14.** Stops on `TooManyNonzeros` (32.0 M against a 32 M limit).

Raising a limit is never credited as an algorithmic improvement (plan §8.3).

## 3. Band and ratio table (development mode)

Seconds are library-call time (`call_ns`). "Best Zeebra" is the faster of `f4` and `adaptive`.
Full table: `summarize.py probe-dev.jsonl`.

| Row | Best Zeebra (s) | grobx default (s) | Ratio | Zeebra route |
|---|---:|---:|---:|---|
| `mq-dense-15-s15@m31` | 3.31 | 0.19 | 17.8 | f4 |
| `mq-dense-15-s15@gf32003` | 3.91 | 0.19 | 20.4 | f4 |
| `mq-dense-18-s18@m31` | 76.42 | 3.18 | 24.0 | Signature |
| `mq-random-11-s11@m31` | 78.38 | 9.31 | 8.4 | f4 |
| `mq-random-12-s12@m31` | 88.20 | 8.57 | 10.3 | f4 |
| `mq-random-12-s12@gf2` | 14.62 | 0.58 | 25.2 | f4 |
| `gen-chandrasekhar-h-11@p31` / `@p64` | 1.50 / 1.63 | 0.53 / 1.47 | 2.8 / 1.1 | Signature |
| `gen-chandrasekhar-h-12@p31` / `@p64` | 5.85 / 8.02 | 2.09 / 6.99 | 2.8 / 1.1 | Signature |
| `gen-chandrasekhar-h-13@p31` / `@p64` | 43.36 / 40.92 | 17.70 / 33.56 | 2.5 / 1.2 | Signature |
| `noon-9@m31` | 2.29 | 0.89 | 2.6 | Signature |
| `katsura-12@m31` / `@w59` | 3.15 / 4.20 | 0.69 / 4.16 | 4.5 / 1.0 | Signature |
| `eco-12@m31` / `@w59` | 2.05 / 2.12 | 0.44 / 1.79 | 4.6 / 1.2 | Signature |
| `eco-13@m31` / `@w59` | 12.64 / 17.64 | 1.91 / 12.96 | 6.6 / 1.4 | Signature |
| `cyclic-8@m31` | 5.32 | 0.35 | 15.1 | Shipping (DegreeSpread) |
| `zb-col-grid-5x5@p31` | 0.96 | 2.15 | 0.4 | Signature |

**The 1–300 s band.** 13 of the 14 non-frontier target rows have a best-Zeebra time of 1–300 s:
dense MQ n = 15 at both fields and n = 18; sparse MQ n = 11 and 12; Chandrasekhar-H 11–13 at both
fields; Noon-9; GF(2) n = 12. GF(2) n = 10 is below the band (0.08 s). That is well above the
plan's one-third. Zeebra wins only on graph colouring: grid-4×5 and grid-5×5, at 0.4–0.5×.

## 4. Declared panel

[`research/1162-m35-baseline/panel.json`](../../research/1162-m35-baseline/panel.json) is the
declaration. Each family states why it matters.

- **Targets** (development split):
  - Dense MQ n = 15, 18 at 2³¹ − 1, plus n = 15 at 32003.
  - Sparse MQ n = 11, 12.
  - Chandrasekhar-H 11, 12, 13 at p31 and p64. This is the application-derived public family,
    from M34 #1006.
  - Noon-9 (mixed degree).
  - GF(2) MQ n = 10, 12.
- **Adverse controls:**
  - Katsura 9 and 12, and Eco 8 and 12, each at 2³¹ − 1 and 2⁶⁴ − 59.
  - Cyclic 7 and 8.
  - Low-term MQ n = 10.
  - Hairer-2 and Butcher: degree-fall, and the failed forced-signature control from #1146.
  - Graph 3-colouring grid-4×5 and grid-5×5.
  - Phosphorylation-7 and Segre-4×4 slice (small sparse).
- **Frontiers**, reported under default limits:
  - Dense MQ n = 20.
  - Sparse MQ n = 14 and 16, at 2³¹ − 1 and GF(2).
  - Noon-10, Eco-13 and Ellipsoid-m2.

  Not all of these are refused. Eco-13 completes at 12.6–17.6 s on the adaptive route. Chandrasekhar-H
  13 also completes on the adaptive route although shipping F4 stops on it, so it is a target, not
  a frontier.
  The research envelope (900 s, 64 GiB) is declared in `panel.json`. No row has been run under it
  yet; that run belongs to the frontier portion of the priced manifest.
- **Splits.** Development is the M34 development families plus the M35 MQ lineages. M34's sealed
  validation cohort is allocated to B–F, and its sealed untouched cohort to G (#1163), by owner
  decision on #1161 before any timing was read. #1162 read neither.
- **Lineage overlap (recorded).** The dense and sparse MQ generators (`corpus::dense_mq_instance`,
  `random_mq_instance`) share their construction mechanism with M34's `zb/planted-dense` and
  `zb/planted-sparse`. Those families are now in G's confirmation, so G's read of them is not
  independent of M35's MQ development (owner decision, #1161).
- **Characteristic ladder at Z0:**
  - Reachable: 2, 32003, 2³¹ − 1, 2⁶⁴ − 59, and Goldilocks on ladder rows.
  - **Gaps:**
    - Characteristic 31 is not reachable through either study harness.
    - 65521 works only through `examples/m4gb_comparison.rs`.
    - No field near 2⁶¹ is compiled: the nearest is `Zp4611624995532046337`, about 2⁶², with no
      CLI.
    - Dense MQ cannot be generated above 2⁶³, because `dense_mq_shaped` asserts p < 2⁶³.

  E (#1123) needs a field near 2⁶¹ before it can measure that boundary.

## 5. Priced manifest

Priced from the development times: `summarize.py probe-dev.jsonl --price panel.json`.

- **Arms:** `f4`, `adaptive`, `grobx` (default).
- **Repetitions:** 9 when an arm's time is under 60 s, 3 above. A frontier row gets 1 repetition,
  because it records whether a limit binds, not a timing.
- **Charges:** a completed or limit-stopped attempt costs its measured call; a timeout costs the
  300 s cap. Harness overhead is 1.9 s per attempt, the upper end of #1158's 1.4–1.9 s.

| Group | Rows | Arms | Attempts | Solve (h) | Harness (h) | Total (h) |
|---|---:|---:|---:|---:|---:|---:|
| target | 14 | 3 | 336 | 1.51 | 0.18 | 1.69 |
| control | 20 | 3 | 528 | 0.32 | 0.28 | 0.59 |
| frontier | 8 | 3 | 24 | 0.50 | 0.01 | 0.52 |
| **primary total** | | | | | | **2.79** |
| secondary: grobx exact checker (8 rows × 3) | 8 | 1 | 24 | 0.64 | 0.01 | 0.66 |

That is about 3.5 h of publication time, within A's 6 h budget (plan §12.1). The secondary panel
uses rows where grobx-certified finished or is likely to. Its unmeasured rows are priced at
60× grobx's raw time, capped at 300 s.

**Not yet done:**
- The publication-mode run of this manifest. It needs the exclusive lock and a CCD reservation,
  and another agent held one throughout this session.
- The research-envelope frontier run.

Until both are done, every ratio above is a development hypothesis.

## 6. Hypotheses carried into B–F (not established here)

1. The 2³¹ gap on structured rows is grobx's 31-bit arithmetic lane (E). Test: Zeebra's own
   2³¹/2⁶⁴ ratio after E should fall towards grobx's 0.15–0.53.
2. Dense MQ's residual after E is zero-row work (B) plus grobx's probabilistic reduction. Dense
   MQ cannot be generated at 2⁶⁴ − 59, so the arithmetic-lane share and the algorithmic share are
   not separated here.
3. Noon-10's refusal is a fallback-order defect (signature, then F4), not a missing mechanism.
   The forced signature engine completes it.
