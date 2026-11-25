# #1141: held-out check of a term-count `WorkerCrossover` rule (not confirmed)

**Measured at:** `e98322f4` (`main` `a63c5568` plus this directory's harness), AMD Threadripper PRO
5995WX, rustc 1.99.1, `sig_f4_study` built `--release --features research-sigf4`. CCDs 1–2 reserved
with `tools/bench-reserve.sh`; each child pinned to CPUs 8..8+w−1 (`provenance.txt`). The rule, the
set, the floor and the pass criterion were posted on #1141 before any timed run (issue comment
7169381783).

**Rule tested.** Inside the band (10 variables, degree 2, infinity witness), the shipping F4 when
`workers >= 16`, or `workers >= 4` and `terms < 114`; otherwise the signature engine. Fitted on
ladder MQ seeds 10–13, where only `terms` separates the seeds F4 wins at 4 w (95, 107) from the
ones it loses (120, 121). Monomials and the quadratic-generator count do not: seed 12 has MQ10's
605 and 9.

**Verdict: not confirmed.** Of 60 scored cells (20 held-out rows, ladder MQ seeds 14–25 except the
floor-dropped 21 and 23, over GF(32003) and GF(2³¹−1), at 4/8/16 w) the candidate agrees on 53
(88%, criterion ≥ 90%), against the incumbent's 35. Four cells exceed the 1.25× bound:

- seed 18 (115 terms, one above the threshold) at 8 w: the signature engine is 1.30× / 1.51× slower;
- seed 24 at 16 w: the shipping F4 is 1.40× / 1.30× slower (sigf4 ÷ f4 0.713 / 0.767), and seed 14
  at 16 w also prefers the signature engine (0.83 / 0.93), so the `workers >= 16` clause is wrong too.

What the data does show (descriptive, not a fitted claim):

- The band still matters. Low-term rows lose badly on the signature engine: seed 22 (94 terms)
  13–23×, seed 16 (90 terms) 2.5–4.4×, seed 20 (97 terms) 1.3–2.3× from 8 w. Removing the band would
  agree on 30 of 60 cells.
- High-term rows (≥ 117 terms) favour the signature engine or tie with F4 (≤ 0.96) at 4 and 8 w on every cell, by up to
  3.0× (seed 24 / GF(32003), 4 w), where the incumbent sends them to F4.
- MQ10 itself (control, 95 terms) now favours the signature engine at 4 w (0.66 / 0.75) and is at
  parity at 8 w (0.90 / 1.01); M32's parity at 4 w, the basis of `SIGNATURE_CROSSOVER_WORKERS = 4`,
  no longer reproduces at this commit. katsura-10 (control) stays at 0.24–0.41.

| File | What |
| --- | --- |
| `features.py` | Pre-solve features from `sig_f4_study --input-only` (the `DispatchFeatures` fields, plus counts) |
| `run.py` | Controller: `--probe` (features and one `f4` / `sigf4` solve at 16 w per row, fixing the 20 ms floor and 30 s ceiling), then `f4` and `sigf4` at 4/8/16 w, 9 fresh processes each, arms rotated per repetition |
| `probe.jsonl.gz`, `held.jsonl.gz` | Every child, with `cpu-context` before and after and the 1-minute load at its start |
| `summarize.py` → `tables.md` | Per-cell medians, sigf4 ÷ f4 with a 95% bootstrap CI, both rules' picks and the pre-declared verdict |
| `provenance.txt` | Commit, binary SHA-256, placement, session start and end |

Reproduce:

```bash
export CARGO_TARGET_DIR=<private dir> RUSTC_WRAPPER=""
cargo build --release --features research-sigf4 --example sig_f4_study
tools/bench-reserve.sh reserve
cd research/1141-worker-crossover
../../tools/bench-reserve.sh run 1141 8-23 python3 run.py \
    --sig "$CARGO_TARGET_DIR/release/examples/sig_f4_study" --output probe.jsonl --probe
../../tools/bench-reserve.sh run 1141 8-23 python3 run.py \
    --sig "$CARGO_TARGET_DIR/release/examples/sig_f4_study" --output held.jsonl --reps 9 --rows <rows>
../../tools/bench-reserve.sh release
python3 summarize.py probe.jsonl held.jsonl e98322f4
```

`<rows>` is every `run.py` row except the four the probe drops (seeds 21 and 23, both fields: no
witness, about 5 ms on either engine).
