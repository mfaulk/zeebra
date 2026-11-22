# grobx capability smoke runs (#1029)

These runs back the capability matrix in
[`docs/research/adaptive-selection-contracts.md`](../../docs/research/adaptive-selection-contracts.md)
§8.3. Each one solves a tiny instance per (field, order, workers, mode) cell through
`tools/external/grobx-driver`, at the M34 pin grobx 0.155.1 `8005a2a1`. The record is about
capability only: it contains no timing or memory figure.

Build the driver to the pin and run the set:

```sh
research/m33-baseline/grobx-pin.sh      # prints the driver's SHA-256; expect fdd6aeec…
python3 research/m34-grobx-capability/smoke.py \
  /buildcache/cargo-target/zeebra-grobx-8005a2a1/release/grobx-driver \
  > research/m34-grobx-capability/smoke.jsonl
```

**Output format.** The first line of `smoke.jsonl` is the driver's `--version` identity. Each
following line is one attempt, with these fields:

- `status`: `ok`, `refused` (a typed driver or engine error) or `stopped`;
- the checker's `certified` verdict;
- a 16-hex-digit prefix of the basis text's SHA-256;
- `route`: the field kernel, plus each run's engine, order and reduction mode, taken from the call
  report.

The reduction mode (`rows`, `tests`, `sketches` or `combinations`) determines the acceptance mode
of a raw attempt (§8.4).

**Committed record.** `smoke.jsonl` came from a private rebuild at `main` `630a33a4`, whose
binary is identical to M33's (§8.2). The result was 22 completed attempts and 11 typed refusals.
All 11 certified attempts returned `certified = true`.
