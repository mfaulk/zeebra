# Monomial order width in F4 column sorting

**Measured at:** base `690b894b`, with the
[`monomial_order_width` example](../../examples/monomial_order_width.rs)
(blob `987fd8674bd7`).

[#306](https://github.com/mfaulk/zeebra/issues/306) added a weighted variant to
`MonomialOrder`, taking the enum from one byte to two machine words.
[#626](https://github.com/mfaulk/zeebra/issues/626) asks how that affected the three built-in orders.
The comparison still takes the order by reference. The benchmark measures the change in
representation and dispatch together.

## Method

The example runs three arms in one binary. Production calls `MonomialOrder::cmp`. Wide models its
four-variant representation and narrow models the earlier three-variant representation. Wide and
narrow share the same built-in comparison code, and the wide arm calls the production weighted
comparator for its fourth variant. Wide divided by production measures how closely the model tracks
the current comparator. Wide divided by narrow estimates the effect of the representation and
dispatch change within the model.

The inputs come from Cyclic and Katsura traces over the field of order 2,147,483,647. The sort
replays the descending unstable sort of the monomial-and-handle vectors built from
`F4Options::recommended()` batches. Each timed lap sorts 20 copies of the snapshot set prepared
outside the clock. The dispatch loop runs 20 million comparisons on pairs drawn from the same
traces' distinct monomials. It forces a discriminant reload per comparison, with the input indexing
and checksum calculation in the timed loop.

Each process rotates arm order over nine repetitions and reports each arm's minimum. The program
asserts identical dispatch checksums and sorted columns. The example test also pins a checksum for
each built-in order on a fixed corpus and checks the enum sizes.

The [benchmarking guide](../guide/benchmarking.md#monomial-order-width) gives the commands.

## Results

Three processes ran on 2026-11-10 on an AMD Ryzen Threadripper PRO 5995WX, pinned to logical
CPU 2 under `tools/benchlock.sh`. The build used rustc 1.99.1 (`58cf8f9c3`), x86-64-v3, and
the repository's release profile with fat LTO. The one-minute load at the start of each process
was 5.60–5.86, with four or five runnable tasks. The fifteen-minute average was 340–346.

Ratio ranges are the minimum and maximum across processes. The production time is the median of
the three per-process minima, divided by 20 to give one pass over all batches in that trace.

| System | Order | Batches | Columns | Production sort | Sort wide / production | Sort wide / narrow | Dispatch wide / production | Dispatch wide / narrow |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| Cyclic-5 | lex | 24 | 1,159 | 16.1 µs | 0.992–1.033× | 1.068–1.117× | 0.973–1.002× | 1.016–1.073× |
| Katsura-5 | lex | 20 | 571 | 6.4 µs | 1.010–1.045× | 1.142–1.151× | 0.956–0.999× | 1.075–1.077× |
| Katsura-6 | lex | 65 | 4,129 | 91.8 µs | 0.983–1.013× | 1.021–1.042× | 0.990–1.025× | 1.007–1.052× |
| Katsura-6 | grevlex | 6 | 650 | 16.9 µs | 0.982–0.995× | 1.079–1.093× | 0.992–1.058× | 1.056–1.087× |
| Katsura-7 | grlex | 7 | 1,709 | 63.9 µs | 0.988–0.999× | 1.060–1.154× | 0.984–1.004× | 1.026–1.035× |

The wide arm took 2.1–15.4% longer than the narrow arm for the replayed sorts. All 15 paired
observations had the same direction. The wide arm tracked the production sort to within 4.5%.
The largest observed wide-minus-narrow difference was 9.2 µs for one pass over Katsura-7's seven
batches. The forced-dispatch loop showed a 0.7–8.7% difference, with the weakest rows on the scale
of the wide-versus-production control. The sort results give a measurable cost on these inputs.
The benchmark covers one call site and one compiler/machine combination. It leaves the effect on
end-to-end F4 time and other by-value uses of the enum unmeasured.

The [earlier stable/unstable comparison](msolve-implementation.md#settled-583-the-sort-wants-to-be-unstable-and-the-handout-order-is-not-worth-carrying)
used a pre-#306 checkout and different column vectors. The production times above establish a
current unstable-sort baseline for these traces.
