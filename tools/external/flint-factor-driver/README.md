# FLINT univariate-factoring driver

A small C driver (#784) that factors one univariate polynomial over a prime field with FLINT and
times the factorization call alone. It is Zeebra's own code, written against FLINT's documented
public API; no FLINT source is copied. FLINT is LGPL-3.0 and is reached only by dynamic linking
from this separate executable — it is never linked into Zeebra.

FLINT 3.6.0 itself is provisioned into `$ZEEBRA_EXT_PREFIX` by `tools/external/provision.sh`
(msolve links it). The system's `libflint.so.22` (pulled in by Singular) has no headers and is not
used: the driver is linked with an RPATH to the prefix.

```sh
tools/external/provision.sh                 # FLINT 3.6.0, if not already present
tools/external/provision-flint-factor.sh    # builds $ZEEBRA_EXT_PREFIX/bin/flint-factor-driver
tools/external/smoke/flint-factor.sh        # two hand-checked factorizations, every algorithm
```

## Interface

```text
flint-factor-driver [--algorithm default|cz|ks|berlekamp] <in.poly> [<out.factors>]
flint-factor-driver --version
```

`<in.poly>` is `modulus <p>`, `degree <n>`, then the `n + 1` decimal coefficients from low to high,
one per line. A modulus that fits a machine word is factored with `nmod_poly_factor` (or the forced
`nmod_poly_factor_with_*` variant); a wider one with `fmpz_mod_poly_factor` (or the forced
`fmpz_mod_poly_factor_*` variant). stdout gets `time_ns <t>`; `<out.factors>` gets one line per
monic factor, `<multiplicity> <c0> ... <cd>`, unsorted.

`examples/modular_composition.rs` writes and reads the same formats: `export dir=<d>` writes the
inputs of its `factor` table, and `factor-file path=<f> out=<o>` factors one with Zeebra's default
route, timing `factorize` alone, and writes the factors sorted bytewise.

## Comparison harness

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-784 RUSTC_WRAPPER=""
cargo build --release --example modular_composition
bin=$CARGO_TARGET_DIR/release/examples/modular_composition
$bin export dir=$CARGO_TARGET_DIR/flint-inputs
tools/benchlock.sh flint-784 taskset -c 8 \
  tools/external/flint-factor-compare.sh $bin $CARGO_TARGET_DIR/flint-inputs 5
```

The harness first requires that Zeebra and all three FLINT arms (`default`, `cz`, `ks`) return the
same multiset of monic factors with multiplicity, and stops otherwise; then it runs the arms once
per repetition with the order rotated and prints the median and minimum. `ZEEBRA_FLINT_INPUTS`
narrows the input list. Results are in `docs/research/modular-composition.md`.
