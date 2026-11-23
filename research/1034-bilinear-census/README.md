# #1034 bidegree census of F4 batch matrices

**Measured at:** `73a14be0` (branch `feat/1034-bidegree-census`). The binary was built from that
tree before `cargo fmt` reformatted it, so the code is the same and only the whitespace differs.
Machine: macOS/arm64 laptop, unpinned. Every figure here is a **count**, not a time, and does not
depend on the machine. The wall cap decides only which instances complete.

Report: [`docs/research/bilinear-feasibility.md`](../../docs/research/bilinear-feasibility.md) §5.
Criteria: pre-declared on #1034 before any count was read.

```sh
CARGO_TARGET_DIR=<private> RUSTC_WRAPPER="" cargo build --profile ci-release \
  --features research-sigf4 --example bilinear_census
target/ci-release/examples/bilinear_census 60 > counts.tsv
python3 summarize.py counts.tsv > tables.md
```

- `counts.tsv`: one row per instance (288 in all). The status is `done`, `failed` (a shipping F4
  budget refused it, with the error), `censored` (past the 60 s wall cap) or `skipped` (after a
  censored instance of the same shape and kind).
- `tables.md`: the per-shape summary, and the decision under the pre-declared rule.

**Not measured here.** The affine 7 × 7 and 8 × 8 instances, homogeneous 8 × 8, and every control
of the 6 × 6, 3 × 9 and 4 × 8 shapes were refused by F4's shipping live-entry budget (32 M). A
re-run with a 256 M budget (`ZB_ENTRIES`) spent more than 30 minutes inside a single batch of the
first 6 × 6 instance, where the wall cap cannot interrupt. It was stopped and recorded nothing.
Those instances need the bench host.
