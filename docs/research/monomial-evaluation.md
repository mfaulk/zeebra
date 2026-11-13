# Fixed small powers in monomial evaluation (#632)

**Measured at:** `467a20f8` before, and that base plus the retained
[`implementation.patch`](../../research/monomial-eval/implementation.patch) after.
The benchmark source is unchanged on both sides. Compiler, lockfile, patch and executable
identities are in [`environment.json`](../../research/monomial-eval/environment.json).

## Decision and scope

Use explicit addition chains for exponents 0 through 5 inside `Monomial::eval`. Larger `u32`
exponents retain `FiniteField::pow`; its implementation and the substitution path are unchanged.
The chains use exactly the same number of multiplications as the existing downward walk:
zero for exponents 0 and 1, one for 2, two for 3 and 4, and three for 5. They preserve `0^0 = 1`.
This is a call-site code-shape change, not a new exponentiation algorithm or a solver speedup.

The baseline BN254 evaluation loop calls general `pow` four times. A plain `#[inline]` on
`Monomial::eval` produced identical normalized disassembly of that loop and was rejected.
The fixed-chain implementation exposes the small powers directly; the general calls remain
reachable only through the larger-exponent branches. The retained
[before](../../research/monomial-eval/before-bn254-eval.asm) and
[after](../../research/monomial-eval/after-bn254-eval.asm) disassembly shows the actual benchmark
loops, rather than a separately compiled wrapper.

An exploratory local small-chain arm ran faster than the final production implementation.
Its [patch](../../research/monomial-eval/prototype.patch) and
[log](../../research/monomial-eval/chains.log) are retained, but that ratio is not the adoption
result. The final comparison below measures the actual public method in two executables.

## Production comparison

AMD Ryzen Threadripper PRO 5995WX, Rust 1.99.1 / LLVM 23.1.1, `x86-64-v3`, fat LTO,
one codegen unit, benchmark profile. Four fresh-process passes in **before, after, after, before**
order, serialized through `tools/benchlock.sh`, affinity 0–7, 30 samples per cell, one-second
warmup and one-second measurement. Each table entry is the median of the two per-pass mean
iteration times; brackets give the range of those two means. The BN254 monomial is
`x0^3 x2^5 x3` at the existing seeded four-variable point.

| Production site | Before median [range] | After median [range] | Before / after |
|---|---:|---:|---:|
| BN254 `Monomial::eval` | 235.38 ns [234.83–235.94] | 186.15 ns [186.03–186.27] | **1.264×** |
| Mersenne-31 `Monomial::eval` | 12.35 ns [11.64–13.05] | 11.46 ns [11.36–11.56] | 1.077× |
| 64-bit `Monomial::eval` | 14.04 ns [13.70–14.38] | 13.33 ns [13.32–13.35] | 1.053× |
| BN254 substitution control | 4.585 µs [4.497–4.673] | 4.496 µs [4.490–4.502] | 1.020× |
| Mersenne-31 `PowerPermutation::invert` control | 5.490 µs [5.345–5.634] | 5.356 µs [5.335–5.377] | 1.025× |
| 64-bit `PowerPermutation::invert` control | 12.244 µs [12.112–12.376] | 12.099 µs [11.943–12.255] | 1.012× |

The BN254 improvement is clear in both passes. The smaller-field movements are modest, and
control ranges overlap; no general gain is claimed for substitution or inverse power permutations. There were
no failed final passes. One-minute load was 2.65–3.45 at pass boundaries. Unrelated builds
continued; this worktree's supporting-binary compilation was moved to CPUs 16–23 during the
final comparison. This was not an idle-machine run. No peak-RSS or end-to-end claim is made.
All pass logs, statistical estimates, load readings, commands and executable hashes are retained
under [`research/monomial-eval/`](../../research/monomial-eval/), including the rejected hint.

Build each revision in its own worktree and private build directory before timing. The same
selection used for each final executable is:

```sh
tools/benchlock.sh monomial-eval \
  timeout --signal=INT --kill-after=10s 180s taskset --cpu-list 0-7 \
  /path/to/pow_strategy --bench \
  'small_exponent/.*/eval/production/4|small_exponent/p254_bn254/substitute/production/64|power_permutation/.*/invert/production' \
  --sample-size 30 --measurement-time 1 --warm-up-time 1 --noplot
```

Set `CRITERION_HOME` to a private output directory. The executable is produced by
`cargo rustc --profile bench --bench pow_strategy`; Cargo prints its benchmark target under the
chosen `CARGO_TARGET_DIR`. Run the four-pass order above rather than comparing independently
collected historical numbers.

## Correctness and maintenance

The performance red condition was the existing production benchmark's BN254 gap, reproduced
before changing the arithmetic call site. Correctness tests were added before the fixed-chain
implementation; because results are unchanged, these tests preserve the existing algebraic
contract rather than assert an intentionally different answer. Timing thresholds are not unit
test assertions.

The focused eight-test monomial suite and 384 field/multivariate tests passed with
`--no-default-features`, including zero, one and seeded random values over 31-bit, 64-bit,
BN254, binary-extension and odd-characteristic extension fields, empty monomials and `u32::MAX`
exponents. Clippy passed with warnings denied. Commands:

```sh
cargo test --lib --no-default-features poly::multivariate::monomial::tests
cargo nextest run --lib --no-default-features --profile ci \
  -E 'test(poly::multivariate) + test(fields::finite_field)'
cargo clippy --lib --tests --no-default-features -- -D warnings
```

Existing CI runs the new unit tests in debug and release and already smoke-tests benchmarks;
no workflow changes are needed. The general field exponentiation routine and public API are
unchanged. Addition chains at other call sites, other compiler/ISA combinations, large-exponent
performance and full-solver impact remain unmeasured.
