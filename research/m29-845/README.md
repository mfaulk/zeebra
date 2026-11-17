# Parallel candidate finishing (#845): raw A/B records

**Measured at:** base `6a78e91a` (`origin/main`); new = `6efb70a5`. The measured binary was built
from that commit's tree before `cargo fmt`, a test-only `is_multiple_of` rewrite and the two new
`m29_cost_model` JSON fields; no production statement differed. 2026-11-17, 00:54–00:59 EST.
**Host:** Threadripper PRO 5995WX, `taskset -c 8-23` (16 workers), Rust 1.99.1, release, fat LTO,
`x86-64-v3`, `RUSTC_WRAPPER=""`, `CARGO_INCREMENTAL=0`, private target dirs.

- `ab845.sh` — the runner: three arms per target from two binaries (`base`, `new`, and `basefl` =
  base with `--batch-order fl`, i.e. #843's parallel FL), rotated order, fresh process per run,
  `/usr/bin/time` peak RSS.
- `walls.jsonl.gz` — n=5 per arm, stage clocks off (process wall and RSS).
- `stages.jsonl.gz` — n=3 per arm, `--stages` (stage clocks; walls not used for ratios).
- `benchlock.log` — the two `tools/benchlock.sh zb-845` windows. One-minute load was 1.2–7.4, with
  no compiler running during either window.
- `summarize.py` — `python3 research/m29-845/summarize.py <(zcat walls.jsonl.gz)`; add any second
  argument to print stage medians.

Every run in both files returned one basis digest per target, the production one.
The report is [`docs/research/m29-baseline-cost-model.md`](../../docs/research/m29-baseline-cost-model.md) §6b.
