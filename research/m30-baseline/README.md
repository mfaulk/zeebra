# M30-0 post-M29 baseline (#855)

**Measured at:** `4f5784c5`. Every figure in this directory comes from executables built at
`4f5784c5` (origin/main at M30 start). Its `src/`, `examples/` and `Cargo.lock` are identical to
M29's close at `adfa6a60` and to the production source of #837's final cohort at `88bc45de`. The
controllers ran on this branch, whose only additions are under `research/`, `docs/` and the
verification-only `--certify` flag (below). 2026-11-17, 10:22–11:42 EST, one
`tools/benchlock.sh zb-855` window per suite ([benchlock.log](benchlock.log)), CCDs 1–2 reserved
with `tools/bench-reserve.sh` for the whole session and released afterwards.
**Host:** Threadripper PRO 5995WX, `ZEEBRA_MACHINE=5995wx`. Protocol:
[`docs/research/m30-protocol.md`](../../docs/research/m30-protocol.md).

## Headline (n=9, process wall, medians [95%])

| Instance | Zeebra (16 workers) | Comparand | Ratio [95%] | M29 §14 ratio [95%] | Drift |
|---|---:|---:|---:|---:|---|
| MQ10 / GF(32003) | 290.0 ms | msolve 116.4 ms (8w, exact) | 2.49× [2.46, 2.52] | 2.51× [2.47, 2.55] | inside |
| MQ10 / GF(2³¹−1) | 276.7 ms | msolve 157.8 ms (4w, exact) | 1.75× [1.62, 1.78] | 1.68× [1.64, 1.78] | inside |
| Eco-12 / 2⁶⁴−353 | 3,107 ms | grobx 1,628 ms (1w, raw randomized) | 1.91× [1.89, 1.95] | 1.88× [1.67, 1.89] | slower: explained below |
| MQ11 / Goldilocks | 5,747 ms | grobx 2,934 ms (1w, raw randomized) | 1.96× [1.95, 1.99] | 1.93× [1.80, 1.94] | slower: explained below |

The grobx rows compare 16 Zeebra workers against one grobx worker. They are not equal-worker rows.
The equal-worker rows are Zeebra at one worker: 13,369 ms on Eco-12 and 42,048 ms on MQ11
([tables.md](tables.md)).

## Drift against M29 (#837), per cell

[drift.md](drift.md) compares all 46 cells by median against M29's 95% interval. 23 are inside, 8
are faster and 15 are slower. The pattern has one cause, and it does not touch the 16-worker
headline cells beyond ±1.2%.

- **12 of the 15 slower cells are Zeebra cost-model children.** At 1 and 4 workers they are
  +0.7% to +7.4%, and on the wide targets at 8 and 16 workers +0.5% to +1.4%. The other three are
  in the MQ10 window: Zeebra at one worker on 32003 (+0.2%, just past a tight interval) and
  groebner-rs at 1 and 4 workers on 2³¹−1 (+1.3%, +5.6%). 56% of
  this cohort's `walls` children started while another session's compiler ran on the unreserved
  CCDs. In M29 the figure was 6%. The reservation fences cache and cores. It does not fence the
  package power budget, and the median clock of 1-worker children fell from 4,538 to 4,430 MHz
  (−2.4%). The children that started with no compiler running reproduce M29 closely. On Eco-12 at
  one worker, the no-compiler median is 12,825 ms against 12,642 ms (n=3 against 8), and the
  compiler-overlapped median is 13,873 ms (n=6). This matches the bench-reserve calibration
  (1-worker MQ10 runs 1.09× beside builds,
  [`docs/guide/benchmarking.md`](../../docs/guide/benchmarking.md) *Calibration*). The 8- and
  16-worker cells move −0.6% to +1.4%: they run at the all-core clock, which builds elsewhere
  change less.
- **The two wide ratios fall just outside M29's intervals.** Zeebra at 16 workers is +1.2% on
  Eco-12 and +0.5% on MQ11, and grobx is −0.4% and −1.2%. M29's grobx samples had a slow tail
  (intervals [1,628, 1,847] and [2,943, 3,172]), which widened its ratio intervals downward. This
  cohort's grobx tail is tight. Neither ratio moves by more than 0.03×, and neither verdict moves.
- **The 8 faster cells are comparands, plus Zeebra on MQ10 at 8 or 16 workers (−0.6%, −0.6%).**
  groebner-rs and grobx in the `wide` suite are −0.4% to −3.9%. That suite started at load 2.78
  with no compilers. groebner-rs at 8 workers on 2³¹−1 is −1.8%. msolve at 16
  workers on 2³¹−1 is bimodal in both cohorts (M29 interval [225, 437]), so a single-cell move
  there carries no information.

No source changed between the cohorts. These moves are measurement conditions. They are recorded
here and not folded into a new figure. An M30 experiment compares against a baseline built from
`4f5784c5` and run interleaved beside it (protocol §2), not against these absolute walls.

## Verification

- **MQ10, both fields.** Every Zeebra, msolve and groebner-rs answer and every one-worker grobx
  answer in `mq10-try1` (234 attempts) is `verified` coefficient for coefficient against the
  Singular references by `comparand-scaling.py`. The other 54 attempts are grobx at 4, 8 and 16
  workers, which are `unsupported`: the adapter refuses more than one worker.
- **Wide fields.** See [verification.json](verification.json), produced by
  [verify_wide.py](verify_wide.py) outside the timed campaign. (a) Every timed Zeebra run returned
  the same basis digest at every worker count. Both digests equal M29's (`3bf17412…` for Eco-12,
  `ddef89cb…` for MQ11; see [pins.json](pins.json)). (b) grobx certified mode (independent exact
  checker with cofactors, admitted by `comparand-scaling.py`'s `certified_basis`, 600 s / 8 GiB,
  one run per target) returns a basis whose sorted text has the same SHA-256. **Wide-field
  correctness rests on (a) and (b): one Zeebra digest across every run, textually identical to a
  grobx-certified basis.** MQ11 / Goldilocks meets this: 767 elements, admitted, digest identical,
  456 s. **Eco-12 / 2⁶⁴−353 does not.** Its certified run hit the declared 8 GiB cap
  (`"stopped":"memory"` at 94 s, kernel peak 8.59 GB) and returned no basis. That is a resource
  stop, recorded in `verification.json` as `admitted: false`. Eco-12's answer is therefore
  supported only by (a) and by text identity with grobx **raw**, which the protocol does not accept
  alone. grobx raw matches the Zeebra digest in all 18 passes, and groebner-rs agrees
  canonically (`wide-corpus.py` `verify_bases`). Certification walls in `verification.json` are
  verification cost and are never part of a solve's wall.
- **Zeebra's own certificate.** `m29_cost_model --certify` (`certify_f4_output`, a serial check of
  Buchberger's criterion over the 743-element basis) on Eco-12 at 16 workers, built from
  `4f5784c5` plus the flag, was still running at the declared 600 s verification budget. It was
  stopped at 660 s, 2026-11-17 ~11:43–11:54 EST. **That is a budget stop, not a failure.** No check
  had reported a failure, and F4's `max_wall_time` does not bound the certificate. It was not
  retried, and MQ11 was not attempted. `verify_wide.py` reports it as `zeebra_certified` when it is
  given `--certifier`.

## Files

| File | What |
|---|---|
| [pins.json](pins.json) | inputs (SHA-256), held-out Katsura-11 and Cyclic-7 / 2⁶⁴−353, budgets, cohort plan; committed before any timed run |
| [identities.json](identities.json) | `research/m29-baseline/identities.py`: Zeebra executables, toolchain, comparands, host |
| [overlays.json](overlays.json) | grobx upstream pin and the research overlays #716 will use, by recipe-file SHA-256 |
| `walls.jsonl.gz` | `costmodel.py` walls: four targets × 1/4/8/16 workers × 9, fresh process, CCD-aligned `taskset`, full instrument JSON and CPU context per child (144 of 144 complete) |
| `wide-attempts.json` | `extract.py` over nine `wide-corpus.py` passes (grobx and groebner-rs, one worker; 36 of 36 complete) |
| `mq10-attempts.json` | `extract.py` over the one `comparand-scaling.py` window, `mq10-try1`, which completed with no compiler interruption (288 attempts) |
| `suite-starts.jsonl` | CPU context at each suite's start, inside the lock |
| [tables.md](tables.md) | `research/m29-baseline/summarize.py` (its wide heading still says "three passes"; this cohort has nine) |
| [verdicts.md](verdicts.md) | `research/m29-final/verdicts.py`, unchanged |
| [drift.py](drift.py) → [drift.md](drift.md) | the per-cell comparison above |
| [verify_wide.py](verify_wide.py) → [verification.json](verification.json) | wide-field certification |

Executable notes. `zeebra_driver` and `wide_corpus` are byte-identical to #837's.
`m29_cost_model` differs only because `env!("CARGO_MANIFEST_DIR")` embeds the worktree path of
`research/wide-corpus/cases.json`. The source diff from `88bc45de` is empty. The certifier
`m29_cost_model_certify` (SHA-256 `c46ee805…`) was built from this branch's
`examples/m29_cost_model.rs`, which adds only `--certify`. It was built before a rustfmt-only
reflow of that file, and it never produced a timed figure.

## Reproduce

```sh
T=/buildcache/cargo-target/zeebra-855      # never under $HOME or /tmp
export RUSTC_WRAPPER="" CARGO_TARGET_DIR=$T TMPDIR=$T/tmp CARGO_INCREMENTAL=0
# build exactly as research/m29-baseline/README.md, at 4f5784c5; copy the #834 grobx and
# groebner-rs drivers into $T/bin; build m29_cost_model at this branch into $T/bin/m29_cost_model_certify
tools/bench-reserve.sh reserve
for s in walls wide; do
  tools/bench-reserve.sh run zb-855 8-23 env CARGO_TARGET_DIR=$T OUT=$T/m30 REPS=9 TMPDIR=$T/tmp \
    timeout --signal=INT --kill-after=60s 5400 bash research/m29-baseline/run.sh $s
done
# wait for zero compilers machine-wide; on exit 75 increment MQ10_TRY and retry, keeping every window
tools/bench-reserve.sh run zb-855 8-23 env CARGO_TARGET_DIR=$T OUT=$T/m30 MQ10_REPS=9 MQ10_WALL=3600 \
  MQ10_TRY=1 TMPDIR=$T/tmp timeout --signal=INT --kill-after=60s 5400 bash research/m29-baseline/run.sh mq10
tools/bench-reserve.sh run zb-855 8-23 env TMPDIR=$T/tmp timeout --signal=INT --kill-after=60s 1800 \
  python3 research/m30-baseline/verify_wide.py --walls $T/m30/walls.jsonl \
  --grobx $T/bin/grobx-driver --scratch $T/m30/verify > research/m30-baseline/verification.json
# add --certifier $T/bin/m29_cost_model_certify for Zeebra's own certificate (over budget on Eco-12)
tools/bench-reserve.sh release
python3 research/m29-baseline/extract.py $T/m30 research/m30-baseline
gzip -n -c $T/m30/walls.jsonl > research/m30-baseline/walls.jsonl.gz
python3 research/m29-baseline/summarize.py research/m30-baseline > research/m30-baseline/tables.md
python3 research/m29-final/verdicts.py research/m30-baseline > research/m30-baseline/verdicts.md
python3 research/m30-baseline/drift.py research/m29-final research/m30-baseline > research/m30-baseline/drift.md
```

The controller archives (`mq10-try1.json.gz`, `wide-*-pass*.json.gz`) hold full inputs and bases
and are kept outside the repository. `mq10-attempts.json` and `wide-attempts.json` name each one by
SHA-256.
