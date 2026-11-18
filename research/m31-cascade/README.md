# #902 cross-target cascade replay: records

Findings: [`docs/research/m31-parallel-signature-elimination.md`](../../docs/research/m31-parallel-signature-elimination.md).
**Measured at:** `0e75b3b6` (tag `measured/902-cascade-replay`), 2026-11-18. Counts only: no wall time is taken or recorded here, so
no benchlock window was needed. The counts are deterministic (identical across the two fields of
each family, and independent of design 2's worker count).

| file | what |
|---|---|
| `<field>-<name>.json` | one `sig_f4_study --replay --workers 2` run: design 1 and design 2 statistics, per-batch `BatchRecord`s for both, and the schedule ceilings at 4/8/16 workers |
| [summarize.py](summarize.py) | the two tables of the findings' §6 |
| [binaries.sha256](binaries.sha256) | the executable that produced every record |

Regenerate a record (the run refuses if recording moved any algebraic quantity or the basis):

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-902 RUSTC_WRAPPER=""
cargo build --release --features research-sigf4-replay --example sig_f4_study
$CARGO_TARGET_DIR/release/examples/sig_f4_study --field wide64 --name eco-12 \
  --engine sigf4 --workers 2 --replay > research/m31-cascade/wide64-eco-12.json
python3 research/m31-cascade/summarize.py wide64-eco-12 goldilocks-katsura-11
```
