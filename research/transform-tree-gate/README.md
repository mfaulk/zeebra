# Transform-tree estimate gate (#606)

This is deterministic source analysis, **not a benchmark**. The model follows
`SubproductTree::build` and `combine` at `778e1dc9`. Its field widths, radix-two
limits and dispatch thresholds are read from that revision. The research note
in [fast-univariate §4.3.4](../../docs/research/fast-univariate.md#434-transform-tree-estimate-gate-606)
distinguishes historical measurements, exact geometry, sensitivity estimates
and the unresolved public-trait dispatch design.

Run from the repository root:

```sh
python3 -m unittest discover -s research/transform-tree-gate -p 'test_*.py'
mkdir -p /buildcache/cargo-target/zeebra-606/tmp
python3 research/transform-tree-gate/estimate.py > /buildcache/cargo-target/zeebra-606/tmp/table.md
diff -u research/transform-tree-gate/table.md /buildcache/cargo-target/zeebra-606/tmp/table.md
bash tools/check-measurement-provenance.sh docs/research/fast-univariate.md
```

No Rust build, benchmark lock, external dependency or large allocation is
needed. The million-leaf case coalesces identical subtree spans. Tests compare
it to literal left-to-right tree construction on irregular small sizes and
check power-of-two padding, odd carries, threshold/root boundaries and the
extra logarithm in the asymptotic estimate. Tests failed on the missing module
before implementation. The existing `agent-scripts` CI job runs these checks
and regenerates the table.

`table.md` counts dense **potential** build/combine products under the existing
multiplication thresholds. Actual interpolation data can cancel leading
coefficients; it can only reduce their degrees. A carried odd node has no
product. A parent spanning `a+b` points has build degrees `a,b` and combine
product degrees at most `a-1,b` (and `a,b-1`). Domains must accommodate degree
plus one. The byte column prices a single coefficient array at the largest
hypothetical build domain, including unsupported fields for comparison; it is
neither total scratch nor peak RSS. Root discovery, simultaneous arrays, tree
storage and Newton/remainder products are not included. Eligible counts do
not measure coefficient work or time; high levels have few calls but large
products. Threshold eligibility is not a new measured crossover.

The second table reports `n^(e-1)/log2(n)^2`, then divides it by explicit
hypothetical transform/Karatsuba constant ratios. Its values are model ratios,
not predicted or measured speedups. There is no fitted transform-tree constant.
No absolute runtime extrapolation or production arithmetic change is made.
The generic `FiniteField` route remains necessary. The bounded experiment this
gate called for is [fast-univariate §4.3.5](../../docs/research/fast-univariate.md#435-the-transform-tree-measured-606)
(`examples/transform_tree_ab.rs`): it measured the transform tree 1.36x–2.94x
faster at 13,123 points, so the sensitivity rows above with `C_N/C_K >= 2` did
not occur. Production dispatch still awaits the capability design.
