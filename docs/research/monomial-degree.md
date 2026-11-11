# Cached monomial degrees: the stage gate rejects adoption

**Measured at:** baseline library `a1466a6e`; cached-degree prototype `018ba170`.
Both use the `monomial_degree_profile` harness committed at `018ba170`. The exact library
and layout-test delta is retained in
[`cached-degree.patch`](../../research/monomial-degree/cached-degree.patch), so reproducing the
experiment does not depend on retaining the prototype on a branch.

Issue [#317](https://github.com/mfaulk/zeebra/issues/317), M27-A. This completes the follow-up to
the [comparison microbenchmark gate](interreduction-cost.md#3f3-the-verdict): implement the cache,
test its contracts, price the actual stages and decide whether to adopt it.

## Decision

**Reject a cached degree in the public monomial representation.** The largest measured total-time
ratio is 1.044x, below the repository's 20% threshold; grevlex is effectively unchanged. There is no
measured symbolic-stage improvement on either lex fixture. The comparison-level advantage established
by the earlier gate did not become a substantial F4 improvement. Production `Monomial<N>` remains
the exponent array, with its existing serialization, hashing and overflow behavior.

**Defer a packed production representation.** A separate order-specific key prototype is faster in
the comparison loop, but that is another microbenchmark, not evidence of a stage or full-solve win.
It materializes additional keys while retaining full monomials, rather than implementing packed
polynomial arithmetic or replacing F4 storage. A new production representation, promotion/retry
policy and serialized format are not justified by these measurements. The runnable prototype stays
available for a future experiment on actual F4 column sorting or normal-form merges.

## Method and exactness

Measured 2026-11-11 on AMD Ryzen Threadripper PRO 5995WX, Rust 1.99.1,
`ZEEBRA_MACHINE=threadripper-5995wx`, `ZEEBRA_AFFINITY=8`, one worker. Both builds use
`x86-64-v3`, fat LTO and one codegen unit, with `RUSTFLAGS` unset and `RUSTC_WRAPPER=""`.
Builds and tests finished before measurements. The retained
[`benchlock.log`](../../research/monomial-degree/benchlock.log) records `end=exited` for both
experiments; the one-minute load average was 5.84 at the A/B start and 5.45 at the packing end.
Those averages include preceding builds; they are not a claim that ambient desktop activity vanished.

The stage harness uses `GF(2147483647)` and the **historical `f4_profile recommended` configuration**:
`F4Options::baseline()` plus structured elimination, all pair criteria and the adaptive backend.
In particular, batches remain in echelon form and final interreduction uses division. This is the
configuration #317 names, **not the current default** with reduced batches and matrix interreduction.
No external-engine ratio or competitive-board row is inferred from this experiment.

Each fixture has 31 fresh-process repetitions per arm, alternating before/after and after/before.
The [runner](../../research/monomial-degree/run.py) compares the **full basis bytes** on every
invocation before retaining its row. All 248 runs agree exactly, including between repetitions.
The basis output contains ordered exponent/coefficient text, not the cached field or a derived
`Debug` representation. The retained [samples](../../research/monomial-degree/results/samples.csv)
include a SHA-256 per basis and all individual stage/RSS readings;
[metadata](../../research/monomial-degree/results/metadata.json) pins both binaries and records
successful completion. Stage times and Linux process peak RSS are sampled before basis printing.

The cache prototype preserves the legacy exponent-only serde representation by recomputing degree
on deserialization. Its private `u64` cache preserves degrees above `u32::MAX`; constructors,
arbitrary generation, products, quotients and lcms maintain it. Hashing uses only exponents and
derived ordering remains lexicographic. Regression tests ran on the baseline before implementation
and on the prototype afterwards. This is an optimization experiment with unchanged public behavior,
so those compatibility tests are intentionally green on both representations; there is no invented
failing behavioral requirement. The existing layout assertion turned red at 32 → 40 bytes and was
updated for the prototype; it is unchanged in the final tree.

## Measured stages

All figures below are medians. Ratios are baseline/cache; values above one favor the cache.
Differences below the stated threshold are not claimed as improvements.

| fixture | total, before → cache | ratio | symbolic, before → cache | final interreduction, before → cache |
|---|---:|---:|---:|---:|
| Katsura-5 lex | 0.831 → 0.858 ms | 0.969x | 0.316 → 0.355 ms | 0.091 → 0.087 ms |
| Katsura-6 lex | 9.313 → 9.575 ms | 0.973x | 5.515 → 5.708 ms | 0.579 → 0.591 ms |
| Katsura-7 grlex | 31.843 → 30.505 ms | 1.044x | 2.936 → 3.122 ms | 22.168 → 20.727 ms |
| Katsura-7 grevlex | 19.671 → 19.586 ms | 1.004x | 2.740 → 3.023 ms | 11.214 → 10.953 ms |

| fixture | construction, before → cache | elimination, before → cache | process peak RSS, before → cache |
|---|---:|---:|---:|
| Katsura-5 lex | 0.059 → 0.062 ms | 0.088 → 0.090 ms | 3,248,128 → 3,215,360 bytes |
| Katsura-6 lex | 0.659 → 0.622 ms | 0.883 → 0.876 ms | 4,427,776 → 4,685,824 bytes |
| Katsura-7 grlex | 0.588 → 0.540 ms | 5.061 → 5.036 ms | 4,489,216 → 4,608,000 bytes |
| Katsura-7 grevlex | 0.669 → 0.602 ms | 4.224 → 4.249 ms | 4,218,880 → 4,599,808 bytes |

These short, small-memory fixtures cannot establish large-instance memory scaling. Layout growth
is nevertheless exact: at N = 5/7/8/10, a cached `u64` grows a monomial from 20/28/32/40 to
32/40/40/48 bytes on this target, including alignment. The measured stage benefit does not fund
that unconditional growth. No larger or current-default speedup is claimed or required to reject
this candidate under the issue's stated gate.

## Packed-key experiment

`monomial_packing` encodes at most seven eight-bit exponents and a total degree at most 255 into
an order-specific `u64`. Graded reverse lexicographic keys put degree in the top byte and reversed,
complemented exponents below it. Unsigned comparison then agrees with the full comparator.
Unsupported arities, degrees, exponents or weighted orders return no key; the comparison wrapper
falls back to the full representation. Tests cover ties, equal operands, the degree-255 boundary,
degree/exponent overflow, wide arities and both directions of a mixed packed/unpacked comparison.
No packed arithmetic can silently wrap because this experiment does not perform it.

The input is 2,048 seeded monomials with exponents in 0..=7, compared against a fixed offset.
Each lap makes 2,048,000 comparisons; nine repetitions rotate arm order, reporting medians.
The production arm here is the **cached-degree prototype**, so packing is compared against step 2.
Key construction is outside both comparison timers and reported separately. Packed lookup also has
a smaller working set and avoids order dispatch; the ratio does not isolate those effects.

| arity | order | cached comparator | packed-key lookup | ratio |
|---|---|---:|---:|---:|
| 5 | lex | 6.887 ms | 3.211 ms | 2.145x |
| 5 | grlex | 6.096 ms | 2.822 ms | 2.160x |
| 5 | grevlex | 6.861 ms | 2.827 ms | 2.427x |
| 7 | lex | 5.999 ms | 2.823 ms | 2.126x |
| 7 | grlex | 6.385 ms | 2.818 ms | 2.266x |
| 7 | grevlex | 7.714 ms | 2.817 ms | 2.738x |

N = 8 refuses packing in every order. Construction of all 2,048 keys took 0.005–0.015 ms in
these runs. The [raw output](../../research/monomial-degree/packing.txt) retains those readings.
This answers the cheap comparison question only; it does not measure the whole F4 packing route
or authorize a representation change. Re-running this example on the final tree compares packed
keys against the original summed-degree comparator; use the retained patch to reproduce this table.

## Reproduce

From this repository, create two checkouts at the named baseline and copy in the same harness:

```sh
git worktree add --detach ../zeebra-degree-before a1466a6e
git worktree add --detach ../zeebra-degree-cache a1466a6e
for arm in before cache; do
  cp examples/monomial_degree_profile.rs ../zeebra-degree-$arm/examples/
done
cp examples/monomial_packing.rs ../zeebra-degree-cache/examples/
git -C ../zeebra-degree-cache apply --unidiff-zero "$PWD/research/monomial-degree/cached-degree.patch"
for arm in before cache; do
  target=/buildcache/cargo-target/zeebra-degree-$arm
  mkdir -p "$target/tmp"
  (cd ../zeebra-degree-$arm && env -u RUSTFLAGS RUSTC_WRAPPER="" \
    CARGO_TARGET_DIR="$target" TMPDIR="$target/tmp" \
    cargo build --release --example monomial_degree_profile)
done
(cd ../zeebra-degree-cache && env -u RUSTFLAGS RUSTC_WRAPPER="" \
  CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-degree-cache \
  TMPDIR=/buildcache/cargo-target/zeebra-degree-cache/tmp \
  cargo build --release --example monomial_packing)

# Finish builds/tests before taking these measurements. Use your machine identity and CPU.
export ZEEBRA_MACHINE="$(hostname)" ZEEBRA_AFFINITY=8
tools/benchlock.sh degree-replay timeout --signal=INT --kill-after=10s 180 \
  python3 research/monomial-degree/run.py \
  /buildcache/cargo-target/zeebra-degree-before/release/examples/monomial_degree_profile \
  /buildcache/cargo-target/zeebra-degree-cache/release/examples/monomial_degree_profile \
  /buildcache/cargo-target/zeebra-degree-replay
tools/benchlock.sh packing-replay timeout --signal=INT --kill-after=10s 120 \
  taskset -c "$ZEEBRA_AFFINITY" \
  /buildcache/cargo-target/zeebra-degree-cache/release/examples/monomial_packing
```

The final tree adds no dependency or production API. Existing nextest jobs discover the compatibility
tests and the registered packing example tests, so no new CI workflow is needed. README commands,
the retained patch and the runner were checked against the actual paths and measured invocations.
The remaining uncertainty is whether precomputed packed keys help a real F4 hot path after their
construction, retained capacity and fallback costs are included; this experiment makes no such claim.
