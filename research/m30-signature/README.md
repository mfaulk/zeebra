# M30-S1 evidence: grobx signature on / off / no-handover (#716)

Report: [`docs/research/m30-signature-attribution.md`](../../docs/research/m30-signature-attribution.md).
Plan: [`MILESTONE-SIGNATURE-SYMBOLIC-F4.md`](../../docs/MILESTONE-SIGNATURE-SYMBOLIC-F4.md) §6.1.

**Measured at:** controller `c143b178` (primary), `dd951927` (extension, census); production `src/` identical to the M30 freeze `4f5784c5`; grobx pin
`1854835d`, research overlay recipe digest in `cohort.json.gz` → `binaries.research.version`.

| File | What it is | Reproduce |
|---|---|---|
| `references.json` | wide-field request and canonical-basis SHA-256 per case, frozen from the multi-engine-agreed answers in `research/wide-corpus/campaign.json.gz` | `python3 tools/external/grobx-signature-study.py --prepare` |
| `cohort.json.gz`, `cohort-proofs/` | every primary attempt (request, process wall, tree RSS, decoded report, ledger, verdict); answers packed by content | see below |
| `extension.json.gz`, `extension-proofs/`, `extension-summary.json` | the declared MQ11 combination-free extension (n=5 x 3 arms), run after the primary cohort at `dd951927` | `--cohort extension --cases mq11-goldilocks` |
| `cohort-summary.json` | per-arm medians, Gate A1 rows, stock-vs-overlay controls | `python3 research/m30-signature/summarize.py research/m30-signature/cohort.json.gz` |
| `diagnostic/pilot-1.json.gz` | the declared one-attempt-per-arm pilot, answers stripped; 11 attempts failed only on a ledger decoder bug (plain combination rounds print no `zero-rows`) | |
| `census.sh`, `census.jsonl.gz` | Zeebra serial `--discovery` records for katsura-5, cyclic-5 (2³¹−1), Eco-12, MQ11 from one binary | `tools/bench-reserve.sh run zb-716 8 research/m30-signature/census.sh <m29_cost_model> out.jsonl` |
| `reconcile.py` | #223's pair-row fraction beside C1's per-pair and per-product fractions, per census record | `python3 research/m30-signature/reconcile.py research/m30-signature/census.jsonl.gz` |
| `benchlock.log` | the `zb-716` lock windows | |

Builds (private targets, never under `$HOME`):

```sh
python3 tools/external/grobx-driver/research/provision.py --source <pinned grobx git dir> \
  --target /buildcache/cargo-target/zeebra-716/grobx --randomization --signature --test
ZEEBRA_GROBX_TARGET=/buildcache/cargo-target/zeebra-716/stock \
  ZEEBRA_EXT_PREFIX=/buildcache/cargo-target/zeebra-716/prefix tools/external/provision-grobx.sh
RUSTC_WRAPPER="" CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-716 \
  cargo build --release --features external-runners,research-work --example m29_cost_model
```

Campaign (CPU 8 inside the reserved CCD 1, fresh process per attempt, five rotated and alternately reversed repetitions):

```sh
tools/bench-reserve.sh run zb-716 8 env ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=8 \
  timeout --signal=INT --kill-after=60s 3600s \
  python3 tools/external/grobx-signature-study.py --cohort primary --repeats 5 \
    --grobx-stock <stock grobx-driver> --grobx-research <research grobx-driver> \
    --scratch /buildcache/cargo-target/zeebra-716/run-primary \
    --output /buildcache/cargo-target/zeebra-716/out/primary/cohort.json.gz
```
