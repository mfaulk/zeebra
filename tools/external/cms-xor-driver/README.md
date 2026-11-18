# CryptoMiniSat XOR driver

A small C++ driver (#220) that loads a system of XOR constraints into CryptoMiniSat 5.18.0, times
one `solve()`, and optionally measures the affine solution space's dimension. It is Zeebra's own
code against CryptoMiniSat's public `SATSolver` API; no CryptoMiniSat source is copied. CMS is
reached only by dynamic linking from this separate executable and is never linked into Zeebra —
external solvers here are oracles, not components
([`docs/research/sat-and-algebra.md`](../../../docs/research/sat-and-algebra.md) §7).

```sh
export ZEEBRA_EXT_PREFIX=/buildcache/...    # anywhere off $HOME and off tmpfs
tools/external/provision-sat.sh             # kissat 4.0.4, CMS 5.18.0 (+ GMP), and this driver
cargo run --release --example sat_algebra -- replay 3
```

## Interface

```text
cms-xor-driver [--no-gauss] [--dimension] [--max-time <s>] <in.xor>
cms-xor-driver --version
```

`<in.xor>` is `p xor <variables> <rows>`, then one row per line, `<rhs> <v> <v> ...`, variables
0-based; the row asserts that the XOR of its variables equals `rhs`. stdout gets `status
sat|unsat|unknown`, `solve_ns`, `variables` and `rows`.

- Default: on-the-fly Gaussian elimination on, with `autodisablegauss` off so CMS cannot quietly
  drop the module the measurement is about. `--no-gauss` sets the matrix count to zero, leaving
  plain CDCL over CMS's own CNF cutting of each XOR.
- `--dimension` adds `dimension` and `rank`, computed on a **second, fresh** solver so the timed
  run carries nothing from it. Each variable in turn is asked whether the value opposite to a
  fixed model is still feasible under the values already fixed; it is free exactly when it is, so
  the count of free variables is the dimension of the affine solution space and
  `rank = variables - dimension`. This uses CMS only as a satisfiability oracle, which is what makes
  it an independent check of Zeebra's rank rather than a second reading of the same elimination.
  Bounded variable elimination and addition are off on that solver so every variable stays
  assumable.

Exit status is 0 on a decided run, 2 on a usage or parse error, 3 on a timeout.
