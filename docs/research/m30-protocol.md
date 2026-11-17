# M30 competitive measurement protocol (#855)

**Measured at:** `4f5784c5`. This document fixes method. Its one figure is the §7 budget stop.
Every baseline figure is in [`research/m30-baseline/`](../../research/m30-baseline/README.md),
measured at the same commit.

Plan: [`docs/MILESTONE-SIGNATURE-SYMBOLIC-F4.md`](../MILESTONE-SIGNATURE-SYMBOLIC-F4.md) §10, §14.
Every M30 comparison (#716, #859, #862 and their children) is paired against the one source
revision and the one set of comparand identities frozen below, measured by M29's infrastructure.
M30 builds no new harness. An issue that cannot follow a rule here says so in its own report,
with the reason; it does not quietly do something else.

## 1. The freeze

| Item | Frozen value | Where recorded |
|---|---|---|
| Zeebra source | `4f5784c5` (origin/main at M30 start; `src/`, `examples/`, `Cargo.lock` identical to M29's `adfa6a60`) | [`pins.json`](../../research/m30-baseline/pins.json) |
| Zeebra executables | `m29_cost_model`, `m29_cost_model_work`, `zeebra_driver`, `wide_corpus`, debug `competitive_sweep`, built at the freeze | [`identities.json`](../../research/m30-baseline/identities.json), SHA-256 each |
| Toolchain and profile | the host's default `rustc` (version in `identities.json`); release, fat LTO, one codegen unit; `-C target-cpu=x86-64-v3` (`.cargo/config.toml`); `RUSTC_WRAPPER=""`, `CARGO_INCREMENTAL=0` | `identities.json` (`zeebra.rustc`, `zeebra.build`) |
| F4 configuration | `F4Options::default()`; forward elimination `Serial` at one worker and `Auto { max_workers: w }` above; 180 s F4 wall | every child's report (`options`) |
| msolve | 0.11.0, exact mode (`-g 2 -l 2`) | `identities.json` |
| grobx | driver at upstream `1854835d` (0.73.3), raw randomized mode, seed 0, one worker; certified mode separately | `identities.json`, [`overlays.json`](../../research/m30-baseline/overlays.json) |
| grobx research overlays | passive work counters (#713) and `research/randomization`, by recipe-file SHA-256; #716's handover-off overlay records its own identity against this freeze | `overlays.json` |
| groebner-rs | driver at `c3e1d630`, one worker | `identities.json` |
| Singular | 4.4.1, references only | `identities.json` |
| Inputs | MQ10 at 32003 and 2³¹−1, Eco-12 / 2⁶⁴−353, MQ11 / Goldilocks; held-out Katsura-11 and Cyclic-7 / 2⁶⁴−353 | `pins.json` (input SHA-256s, committed before any timed run) |
| Host | Threadripper PRO 5995WX, `performance` governor, boost on, `amd-pstate-epp` | `identities.json` (`host`) |

A change to any row is a new baseline, not a continuation. Comparisons across hardware, compiler or
comparand identities are never treated as paired.

## 2. Arms

- **Zeebra baseline (M30-0).** The frozen executables. An experiment that changes the library
  rebuilds the instrument at its own head and runs it **beside** a baseline built from the freeze in
  its own target directory, interleaved; it does not compare against this directory's published
  walls, which were taken at another time under another load.
- **Experimental arms.** One option or one source change per arm, named with the option value or
  the commit. The shipping configuration is an arm of its own whenever it differs from the baseline.
- **msolve, exact mode.** Workers 1, 4, 8 and 16; the fastest median is the comparand.
- **grobx.** Raw randomized mode (the adapter default) is the timing comparand. Certified mode,
  research overlays (#716's arms 1–4) and `Params.signatures=false` are separate rows, each labelled,
  never folded into the raw row.
- **groebner-rs.** One worker (its adapter refuses more).

## 3. Repetitions, order and windows

- A fresh process per run. n ≥ 5 per arm for an ablation, n ≥ 9 for milestone acceptance.
- Arms interleaved and their order rotated per repetition (`research/m29-baseline/costmodel.py`
  `plan()`; `comparand-scaling.py` and `wide-corpus.py` as shipped).
- A **window** is one `tools/benchlock.sh` acquisition. Samples are never pooled across windows.
- `comparand-scaling.py` stops a window when any compiler starts on the machine (exit 75). That
  window is a **compiler-interrupted window**: its attempts are retained and reported, and the next
  try is a new window with its own number (`MQ10_TRY=n`).
- Every attempt is retained: completed, timed out, refused, out of memory, unsupported, interrupted.
  No resampling until a result looks good, and nothing inferred from an incomplete run.

## 4. Placement, load and what a figure may claim

- `tools/bench-reserve.sh reserve 1,2` for the measurement session (CPUs 8-23 and their siblings),
  released when it ends. A w-worker Zeebra child runs on CPUs 8..8+w−1: one thread per physical
  core, siblings idle. Every engine's worker count is stated in every row.
- `tools/cpu-context.sh` is recorded at each suite's start inside the lock and around each
  cost-model child (load, compilers, frequency).
- Per `docs/guide/benchmarking.md` *Calibration*: an interleaved A/B ratio on reserved CCDs is
  publishable beside builds; an absolute wall taken beside builds is labelled so. A 16-worker
  Zeebra row against a one-worker grobx row is reported as such, never as equal-worker; an
  equal-worker row is reported beside it.

## 5. Seeds

Zeebra's F4 is deterministic. Inputs are fixed by name and SHA-256 (the corpus's generators take
their seed from the row name). grobx runs with its upstream default seed 0. msolve runs with its
defaults. groebner-rs's randomized row combinations use the pinned crate's internal generator,
which the adapter does not expose; its answer is verified, so the seed affects time only.

## 6. Caps

Declared before execution in `pins.json` and per issue for new arms:

| Engine / harness | Cap |
|---|---|
| Zeebra (`m29_cost_model`) | 180 s F4 wall per child |
| comparands under `wide-corpus.py` | 60 s and 2 GiB per attempt |
| comparands and Zeebra under `comparand-scaling.py` | 60 s and 2 GiB per child; 3,600 s per window |
| every suite | `timeout --signal=INT --kill-after=60s 5400` |

An arm that needs a larger cap than the baseline reports that as a result.

## 7. Verification, per field

| Field | Zeebra | Comparand |
|---|---|---|
| GF(32003), GF(2³¹−1) | coefficient for coefficient against the Singular reference bases (`research/comparand-scaling/singular-reference*-v1.json.gz`), by `comparand-scaling.py` | the same |
| 2⁶⁴−353, Goldilocks | (a) the timed runs return one basis digest across every run and every worker count; (b) grobx **certified** mode on the same input returns, through its independent exact checker and cofactors, a basis with the same sorted-text SHA-256 (`research/m30-baseline/verify_wide.py`) | grobx raw: basis text digest equal to the certified basis; groebner-rs: canonical agreement (`wide-corpus.py` `verify_bases`) |

**Wide-field correctness rests on (a) and (b): a single Zeebra digest, textually identical to a
grobx-certified basis.** Zeebra's own certificate (`certify_f4_output` via
`m29_cost_model --certify`) is not part of the rule. At `4f5784c5`, on Eco-12 / 2⁶⁴−353 at 16
workers, it was a **budget stop at 660 s, not a failure**: it was still checking Buchberger's
criterion serially over the 743-element basis when the declared 600 s verification cap (plus 60 s
grace) expired, and no check had failed. An M30 arm that changes the basis re-establishes (b) for
its own output. Matching the baseline digest suffices only when the digest is unchanged.
grobx certified mode needs more than 8 GiB on Eco-12. At `4f5784c5` it stopped on memory at 8 GiB,
and at 32 GiB, the cap raised after that resource stop, it peaked at 11.4 GB. A new certified run on
Eco-12 declares 32 GiB in advance.

Verification time is never inside a solve's wall. Agreement of two raw outputs is not accepted
alone. A configuration whose certification changes the solver (grobx certified) is a separate row.

## 8. Statistics and drift

- Medians with 95% bootstrap intervals, each arm resampled independently, 20,000 draws, seeded by
  the CRC-32 of the cell name (`research/m29-final/verdicts.py`, reused unchanged).
- **Drift** against a published baseline is read per cell. A median outside the baseline's
  interval is explained (load, placement, identity), not absorbed into the new figure.

## 9. Scoreboard columns (plan §14)

Every M30 scoreboard row carries:

| Column | Source |
|---|---|
| instance, field, input SHA-256 | `pins.json` |
| engine, mode, worker count | the arm |
| process wall median, n, 95% interval | the timed campaign |
| ratio to the comparand, with its interval | `verdicts.py` |
| peak RSS | the timed campaign (Zeebra: `peak_rss_bytes`; external: the controller's tree peak) |
| verification status | §7 |
| symbolic-preprocessing time | a separate stage-clock campaign (`--stages`), never the timed one |
| coefficient work | `research-work` census (Zeebra); passive counters (grobx overlay, `Gf31` only) |
| reductions to zero | C1 `--discovery` census |
| zero rows | `F4Statistics::zero_rows`; grobx matrix census |
| pair rejections by mechanism | `examples/pair_criteria.rs`; grobx overlay pair decisions |

Where a column is not available for an engine it says `n/a` with the reason, not a blank. The four
§2.2 quantities are distinct columns and are never merged.

## 10. Reproducing the baseline

[`research/m30-baseline/README.md`](../../research/m30-baseline/README.md) has the build and run
recipe.
