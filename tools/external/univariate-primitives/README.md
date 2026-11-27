# Per-primitive univariate drivers: FLINT and NTL

Two small drivers (#1206) that run one univariate primitive over a prime field and time that call
alone: `flint_primitives.c` against FLINT, `ntl_primitives.cpp` against NTL. They are Zeebra's own
code, written against each library's documented public API, and no library source is copied.
FLINT (LGPL-3.0) and NTL (LGPL-2.1+) are reached only by dynamic linking from these separate
executables. Neither is ever linked into Zeebra.

```sh
tools/external/provision-univariate-primitives.sh   # builds $ZEEBRA_EXT_PREFIX/bin/{flint,ntl}-primitives-driver
```

FLINT comes from `$ZEEBRA_EXT_PREFIX` when `tools/external/provision.sh` has installed it there
(FLINT 3.6.0 on the bench host), and otherwise from Homebrew (`brew install flint ntl` on macOS,
which also gives FLINT 3.6.0). NTL comes from `$NTL_PREFIX`, then Homebrew, then `/usr`.
`NTL_PREFIX=none` builds the FLINT driver only.

## Interface

```text
<driver> <job> <reps> [<out>]
<driver> --version
```

A job is `modulus <p>`, `primitive <name>`, then one block per operand: `vec <len>` followed by
`len` decimal residues, one per line. stdout gets `time_ns <median>` and `min_ns <min>` over
`<reps>` calls. `<out>` gets the result of the last call, one line per value. A polynomial is
written as its coefficients from low to high, separated by spaces, and the zero polynomial is an
empty line. A scalar is written as itself. Roots are written one per line in any order, and the
harness sorts them. A primitive the library has no entry point for makes the driver print
`unsupported` and exit with status 3.

| primitive | operands (n = 2^k) | output | FLINT, word / wide modulus | NTL |
|---|---|---|---|---|
| `mul` | `a`, `b` of degree n | `a·b` | `nmod_poly_mul` / `fmpz_mod_poly_mul` | `mul` |
| `mulfft` | as `mul` | as `mul` | as `mul` | as `mul` |
| `divrem` | `a` of degree 2n, `b` of degree n | `q`, `r` | `*_divrem` | `DivRem` |
| `gcd` | `a` of degree n, `b` of degree n−1 | monic gcd | `*_gcd` | `GCD` |
| `xgcd` | as `gcd` | `g`, `s`, `t` with `g = s·a + t·b` | `*_xgcd` | `XGCD` |
| `powmod` | monic `f` of degree n | `x^p mod f` | `*_powmod_x_fmpz_preinv`, with the inverse of `rev(f)` computed inside the timer | `PowerXMod` |
| `roots` | monic `f` of degree n | distinct roots in F_p | `*_roots` (no multiplicity) | `gcd(x^p − x, f)`, then `FindRoots` |
| `multieval` | `f` of degree n−1, n distinct points | values | `nmod_poly_evaluate_nmod_vec_fast` / `fmpz_mod_poly_evaluate_fmpz_vec_fast` | `eval` (vector) |
| `interpolate` | n distinct points, n values | the degree < n interpolant | `nmod_poly_interpolate_nmod_vec_fast`; **none** for `fmpz_mod_poly` | `interpolate` |
| `compose` | `f`, `g` of degree n−1, monic `h` of degree n | `f(g) mod h` | `*_compose_mod` | `CompMod` |
| `resultant` | as `gcd` | `Res(a, b)` | `*_resultant` | `resultant` |

A word-size modulus goes to `nmod_poly` in FLINT. In NTL it goes to `zz_pX` when it is below
`NTL_SP_BOUND`, which on 64-bit hosts covers KoalaBear but not the 64-bit primes. Every other
modulus goes to `fmpz_mod_poly` in FLINT and `ZZ_pX` in NTL.

On Zeebra's side, `examples/univariate_primitives.rs` writes the jobs (`export`) and runs them
with Zeebra's default public entry points (`run`). `mul` is the `&a * &b` operator that the
univariate layer is built on. That operator cannot reach the transform, because its signature
carries neither `KnownOrder` nor a random source (`docs/research/fast-univariate.md` §4.1).
`mulfft` is `zeebra::multiply`, which can reach it. The other entry points are `div_with_remainder`, `gcd`, `xgcd`,
`pow_mod_limbs` (the default route), `roots`, `multipoint_evaluate`, `lagrange_interpolate`,
`compose_mod` and `resultant`.

## Comparison harness

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-1206 RUSTC_WRAPPER=""
cargo build --release --example univariate_primitives
tools/benchlock.sh univariate-1206 taskset -c 8 \
  tools/external/univariate-primitives-compare.sh \
  $CARGO_TARGET_DIR/release/examples/univariate_primitives $CARGO_TARGET_DIR/univariate-jobs
```

For each field, primitive and size, the harness exports one job and runs every arm on it once. It
stops if any arm's output differs from Zeebra's (after sorting, for `roots`). It then runs `ROUNDS`
rounds with the arm order rotated. Each process makes between 1 and 7 calls, enough for about
0.3 s. Each arm's figure is the median of its per-process medians. A (field, primitive) pair stops
growing once Zeebra or FLINT takes more than `CAP_S` seconds a call, and NTL is dropped from a row
once it does. `FIELDS`, `PRIMITIVES`, `MIN_LOG`, `MAX_LOG`, `ROUNDS`, `CAP_S`, `FLINT_DRIVER` and
`NTL_DRIVER` narrow or redirect the sweep. Jobs are deleted after use, because they reach hundreds
of megabytes at 2^20 over BN254. Results are in `docs/research/univariate-primitives-comparison.md`.
