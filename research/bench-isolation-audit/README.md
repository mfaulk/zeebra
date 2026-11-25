# Bench isolation audit data (#1104)

Raw data behind [`docs/research/bench-isolation-audit.md`](../../docs/research/bench-isolation-audit.md).
Measured at `a63c5568`, with `tools/bench-isolation-audit.sh` as added in the same change (#1104), on 2026-11-25.

| Path | What |
|---|---|
| `inventory-unreserved-initial.json` | `bench-isolation-audit.sh inventory 8-23,72-87`, no reservation |
| `window1.sh` | reservation window 1: transitions, three H-A1 inventories, H-A2 sample under a build loop |
| `window1/inventory-reserved-{1,2,3}.json` | H-A1 snapshots at +1, +8 and +15 min. They predate zombie handling, so a desktop app's sandbox zombie is still listed as an escape |
| `window1/sample-8-23,72-87.json` | H-A2: 1,020 s, 752 snapshots |
| `window1/transition-*.txt`, `transition-taskset.txt`, `hold.txt` | affinity of the transition subjects, and the `taskset`/`systemd-run` probes |
| `window1/build-loop.log`, `events.log` | the `cargo clean; cargo build -j48 --tests` loop on the rest CPUs, and the window timeline |
| `window2.sh`, `window2/` | what `release` gives back, including a mask set while reserved |
| `harness-cost/` | `hcost.py` + `hbusy.c`: in-window harness CPU of `run_child`, harness pinned to the child's CPUs (H-A3, no spare) |
| `journal-harness/` | `summarize.py` over every retained `/buildcache/bench-jobs` journal, and its output |
| `policy.txt` | `bench-isolation-audit.sh policy 1 2 4 8 9 12 16` |

Reproduce the summaries:

```bash
tools/bench-isolation-audit.sh inventory 8-23,72-87 | jq '.escapes'
python3 -I research/bench-isolation-audit/journal-harness/summarize.py /dev/null
gcc -O1 -pthread -o /buildcache/hbusy research/bench-isolation-audit/harness-cost/hbusy.c
TMPDIR=/buildcache/cargo-target/<you>/tmp python3 -I research/bench-isolation-audit/harness-cost/hcost.py \
  "$PWD" /buildcache/hbusy 8-23 out.json 15
```

`window1.sh` reserves CCDs 1–2 for about 19 minutes. Run it only when `tools/bench-reserve.sh status`
is `released` and no bench job is queued. It takes `<repo> <outdir> <hbusy>`.

**Redaction.** Inside the fenced user slices, the committed inventories keep class, group counts
and affinities. Desktop-application group names and the process names in those slices are
replaced with `<desktop app, redacted>` / `<redacted>`. Terminal, runner and `run-*` scope names
are kept, so the classification can still be checked. Every count is unchanged.
