# Multirow reuse evidence (#715)

The report is [`docs/research/multirow-reuse.md`](../../docs/research/multirow-reuse.md).

- `native.json.gz` — the three-arm cohort plus feature-absent control, 120 verified attempts and
  three excluded (contaminated by a concurrent build) attempts; full answers under `native-proofs/`.
- `extension.json.gz` — the declared ten-pair `single`/`band4` MQ10 extension; answers under
  `extension-proofs/`.
- `probe.json.gz` — one MQ14 attempt per arm and prime; every arm is refused by the live-entry
  budget, so no answer exists to verify.
- `summarize.py` regenerates `summary.json` and `table.md` from the cohorts without running anything.

Each cohort's `identity` binds the controller commit, the build commit `c45bf1eb`, both binary
SHA-256 values, the affinity, the load gate and `Cargo.lock`.
