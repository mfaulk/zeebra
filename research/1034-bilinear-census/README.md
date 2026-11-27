# #1034 bidegree census of F4 batch matrices

**Measured at:** `73a14be0` (tag `measured/1034-bilinear-census`) and `efa2478d` (tag
`measured/1034-bilinear-census-2`). Every figure here is a **count**, not a time, and does not
depend on the machine, the worker count or the build profile. The run limits decide only which
instances complete. Machine: macOS/arm64 laptop, unpinned.

Report: [`docs/research/bilinear-feasibility.md`](../../docs/research/bilinear-feasibility.md) §5–§6.
Criteria: pre-declared on #1034 before any count was read.

## Run 1 (`73a14be0`): the whole cohort at shipping budgets

The binary was built from that tree before `cargo fmt` reformatted it, so the code is the same and
only the whitespace differs.

```sh
CARGO_TARGET_DIR=<private> RUSTC_WRAPPER="" cargo build --profile ci-release \
  --features research-sigf4 --example bilinear_census
target/ci-release/examples/bilinear_census 60 > run1.tsv
```

## Run 2 (`efa2478d`): what run 1 did not complete, one process per instance and arm

`split_run.py` runs one instance and arm per process, polls the child's RSS, and kills it at the
RSS ceiling or past the wall cap, which F4 cannot enforce inside a batch. It applies the
pre-declared censor-then-skip rule per shape, kind and arm. Limits, fixed before the run: F4's
live-entry budget 400 M, RSS ceiling 12 GB, wall cap 1,800 s, 6 workers.

```sh
CARGO_PROFILE_CI_RELEASE_LTO=thin cargo build --profile ci-release \
  --features research-sigf4 --example bilinear_census
B=target/ci-release/examples/bilinear_census
LIMITS="--cap 1800 --rss-gb 12 --entries 400000000 --workers 6"
python3 split_run.py $B runs.tsv $LIMITS --task 6x6-affine:control \
  --task 7x7-affine:bilinear --task 7x7-affine:control --task 8x8-affine:bilinear \
  --task 6x6-homogeneous:control
python3 split_run.py $B runs.tsv $LIMITS --task 7x7-homogeneous:bilinear \
  --task 4x8-affine:control --task 3x9-affine:control --task 4x8-homogeneous:control \
  --task 3x9-homogeneous:control --task 8x8-homogeneous:bilinear
python3 split_run.py $B runs.tsv $LIMITS --task 7x7-homogeneous:control
python3 merge.py run1.tsv runs.tsv > counts.tsv
python3 summarize.py counts.tsv > tables.md
```

## Files

- `counts.tsv`: one row per instance (288 in all), both runs merged. The status is `done`,
  `failed` (F4's live-entry budget refused it, with the error, or `refused:rss`), `censored`
  (past the wall cap) or `skipped` (after a stopped instance of the same shape and kind). A
  control or signature column holds a count, `failed:<error>`, `refused:rss`, `skipped` or
  `not-run`.
- `runs.tsv`: run 2's raw per-arm rows, as `split_run.py` wrote them.
- `tables.md`: the per-shape summary, and the decision under the pre-declared rule.

**Not measured here.** The 7 × 7 and 4 × 8 affine controls, the 8 × 8 shapes and some unbalanced
homogeneous controls exceed the 12 GB ceiling or F4's 400 M budget; `tables.md` lists each. The
signature arm ran only in run 1.
