# #1206: univariate primitives against FLINT and NTL

**Measured at:** `6b150bd7` (`sweep.md`) and `5abda6b3` (`sweep-mulfft.md`), on an unpinned
M4 Pro laptop (macOS, arm64) with Homebrew FLINT 3.6.0 and NTL 11.6.0. The write-up is
[`docs/research/univariate-primitives-comparison.md`](../../docs/research/univariate-primitives-comparison.md).

| File | What |
|---|---|
| `sweep.md` | every primitive except `mulfft`, over all four fields, n = 2⁸ … 2²⁰ |
| `sweep-mulfft.md` | the `mulfft` row alone, from a later build that added it |

Both are the harness's raw output. Only the path of the Zeebra binary has been replaced with a
placeholder.

## Reproduce

```sh
brew install flint ntl
tools/external/provision-univariate-primitives.sh
export CARGO_TARGET_DIR=<private target dir> RUSTC_WRAPPER=""
cargo build --release --example univariate_primitives
MIN_LOG=8 MAX_LOG=20 ROUNDS=3 CAP_S=2 tools/external/univariate-primitives-compare.sh \
  $CARGO_TARGET_DIR/release/examples/univariate_primitives $CARGO_TARGET_DIR/univariate-jobs
```

`PRIMITIVES=mulfft` reproduces `sweep-mulfft.md`.
