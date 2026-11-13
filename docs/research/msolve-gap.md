# The msolve gap on `mq-random-10`, decomposed by work counts (#737)

**Measured at:** `99a81844`, which is `main` at `e22b9b58` plus `examples/msolve_gap.rs`, with no
library change. The branch was then rebased onto `55fef8d9` (#736), which changes no file under
`src/`. The harness commit became `47161ee1`, with identical content. msolve 0.11.0 as provisioned by `tools/external/provision.sh`, and a counting copy of the
same release built by `tools/external/msolve-count.py`. Machine: AMD Threadripper PRO 5995WX,
`taskset -c 4`, one worker, under `tools/benchlock.sh` (owner `zb-737`), start load 1.22.
Retained evidence: [`research/msolve-gap/`](../../research/msolve-gap/).

`docs/research/groebner-jl-gap.md` decomposed the Groebner.jl gap. It found that Groebner.jl did
not do less work, and that interreduction and a per-operation constant explained the gap. No study
did the same for msolve. `docs/research/mq10-current-profile.md:172-174` records that the other
engines' work counts were unmeasured. This document measures them for msolve and splits the gap
into **work done** and **cost per unit of work**.

## 0. The answer

| GF(32003), medians of 5 interleaved runs | Zeebra | msolve | ratio |
|---|---:|---:|---:|
| process wall | 2.91 s | 0.21 s | **13.9x** |
| F4 call / msolve `overall(elapsed)` | 2 905.3 ms | 200 ms | 14.5x |
| elimination / msolve `linear algebra` | 2 767.1 ms | 140 ms | **19.8x** |
| batch coefficient products | 1 164 888 894 | 281 213 325 | **4.14x** |
| elimination time per product | 2.38 ns | 0.50 ns | **4.77x** |
| peak RSS | 134.5 MiB | 11.1 MiB | 12.1x |

At GF(2^31−1) the same rows read 13.7x wall, 20.1x elimination, **4.14x** products and **4.86x**
per product (§3).

The elimination gap is about **4x in work times about 5x in cost per unit of work**. Almost all of
the extra work is one mechanism. Zeebra spends **579.7 M products on back-substitution**. msolve
spends **0.64 M**, about 900x less, because it never reduces the reducer rows' tails (§2). In
forward reduction, Zeebra does 2.09x msolve's products.

The 13.9x wall ratio here is not the board's 18.6x (`interreduction-cost.md:1452-1455`). They are
different machines and sessions, and no ratio spans them.

## 1. How each side was counted

**Zeebra.** `examples/msolve_gap.rs` runs `F4Options::default()` with stage clocks on the
digest-pinned instance (`16422daf…` at GF(32003)). A `BatchObserver` records each batch's shape
before elimination. Zeebra's coefficient-product counts come from #713's frozen counter campaign
(`docs/research/grobx-trajectory.md` §"Comparable coefficient work", source `ff65d2b4`). They were
not re-counted here. They do still apply, because the application counts that campaign split into
forward and backward sum to `F4Statistics::row_operations` at this commit **exactly**: 9 943 484
at GF(32003) and 9 943 743 at GF(2^31−1).

**msolve.** `tools/external/msolve-count.py` copies the provisioned 0.11.0 source and adds two
counters at every site where the exact sparse kernel (`laopt 2`, msolve's default) applies a pivot
row to a dense row. One counter is incremented per application; the other adds the pivot row's
length. Counts are split by phase:

- **forward:** lower (pair) rows against the known and newly found pivots
- **new-pivot interreduction:** new pivots reduced against each other, right to left
- **final:** the last basis reduction

The counting copy writes a byte-identical basis to stock msolve. Timings in §0 and §3 come from
**stock** msolve, never from the counting copy.

**The counting conventions agree.** Both engines' final basis reductions count **281
applications and 93 441 products**, the same as Zeebra's separately listed final pass in #713, to
the unit. Both sides charge a pivot row's leading entry as a product. The batch totals below
exclude the final pass on both sides.

## 2. The work, side by side

| phase | Zeebra apps | msolve apps | ratio | Zeebra products | msolve products | ratio |
|---|---:|---:|---:|---:|---:|---:|
| forward | 7 885 325 | 5 344 937 | 1.48x | 585 166 982 | 280 568 561 | **2.09x** |
| backward | 2 058 159 | 2 089 | 985x | 579 721 912 | 644 764 | **899x** |
| final pass (excluded) | 281 | 281 | 1.00 | 93 441 | 93 441 | 1.00 |
| **batch total** | 9 943 484 | 5 347 026 | 1.86x | 1 164 888 894 | 281 213 325 | **4.14x** |

GF(2^31−1) differs only in the last digits on both sides: msolve 5 345 076 / 280 577 385 forward
and 2 089 / 644 800 new-pivot; Zeebra as in #713.

**Backward work is the mechanism, and msolve shows how little is needed.** In msolve's
`exact_sparse_reduced_echelon_form_ff_16` (pinned 0.11.0 source, read as a reference, GPL), the
known pivots (the reducer rows) are **read-only**. After forward reduction, only the **new**
pivots are interreduced, and they only have entries in the non-pivot columns. That is 2 089
applications across the whole run. Zeebra back-substitutes 2 058 159 times. #713 records that
1 089 354 of those target **inherited reducer rows**, and that an average backward application
touches 282 coefficients against 74 forward. msolve's complete reduced basis matches Zeebra's, so
none of the back-substitution into reducer rows is needed for the output.

**Forward work is 2.09x, from three smaller factors.**
- 1.48x more applications.
- 1.41x longer pivot rows per application: 74.2 against 52.5 products.
- Matrices 1.20x the rows and 1.19x the columns (table below), with 1.09x the as-built nonzeros.

Back-substituted reducer tails are denser than the stored basis multiples msolve applies. That is
a plausible cause of the 1.41x but is **not measured here**. The 1.19x extra columns is a separate
symbolic-preprocessing difference (#742).

The matrix shapes per round, GF(32003). Here "m" is msolve's `-v 2` log. Its nonzeros are density
× rows × columns from a two-decimal percentage, so they are approximate.

| round | degree | pairs Z / m | rows Z / m | cols Z / m | nonzeros Z / m≈ |
|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 5 / 5 | 17 / 14 | 40 / 40 | 135 / 101 |
| 2 | 3 | 14 / 14 | 98 / 82 | 196 / 178 | 1,194 / 971 |
| 3 | 4 | 72 / 72 | 503 / 459 | 658 / 622 | 12,683 / 11,477 |
| 4 | 5 | 229 / 229 | 1,611 / 1,404 | 1,695 / 1,538 | 91,219 / 79,464 |
| 5 | 6 | 442 / 442 | 4,290 / 3,430 | 4,169 / 3,404 | 288,054 / 248,693 |
| 6 | 6 | 169 / 169 | 6,057 / 4,954 | 6,292 / 5,199 | 270,044 / 257,558 |
| 7 | 6 | 57 / 57 | 5,710 / 4,877 | 6,027 / 5,195 | 239,132 / 233,091 |
| 8 | 7 | 734 / 733 | 12,554 / 9,977 | 12,020 / 9,607 | 783,727 / 680,528 |
| 9 | 7 | 48 / 48 | 10,435 / 8,889 | 10,738 / 9,195 | 431,626 / 408,672 |
| 10 | 8 | 7 / 11 | 11,504 / 9,883 | 11,851 / 10,226 | 504,689 / 485,105 |
| **sum** | | 1,777 / 1,780 | 52,779 / 43,969 | 53,686 / 45,204 | 2,622,503 / 2,405,660 |

The two engines take the same trajectory: ten rounds, the same degree sequence, the same pairs to
within four, and 247 basis elements. As with Groebner.jl, the gap is not a different algorithm
doing less mathematics.

## 3. Time per unit of work

| | GF(32003) Z | GF(32003) m | GF(2^31−1) Z | GF(2^31−1) m |
|---|---:|---:|---:|---:|
| elimination / `linear algebra`, median | 2 767.1 ms | 140 ms | 3 016.6 ms | 150 ms |
| spread over 5 runs | 2 754.6–2 822.9 | 130–140 | 3 011.6–3 197.3 | 150–160 |
| batch products | 1 164 888 894 | 281 213 325 | 1 164 946 283 | 281 222 185 |
| ns per product | 2.38 | 0.50 | 2.59 | 0.53 |
| **per-product ratio** | | **4.77x** | | **4.86x** |

msolve prints times at 10 ms resolution, so its `linear algebra` figure carries up to ±4%. Both
per-product ratios have that uncertainty. Each engine's time is charged to its own counted
products. Backward products in Zeebra touch longer rows and a different loop, so a per-product
average is a blend, not a kernel constant.

msolve's kernel (`reduce_dense_row_by_known_pivots_sparse_ff_16`, read as a reference) differs from
Zeebra's in mechanism, not in algorithm:

- **The target is a dense `i64` array.** Each pivot's entries are scattered into it with a
  multiply-add, and the result is reduced mod p only when its column is visited. Zeebra's
  `SparseRow::subtract_scaled` merges two sparse rows into a new buffer and copies the result back.
  That merge is 53–57% of cycles (`mq10-current-profile.md:142-143`).
- **Entries are narrow.** Coefficients are 16 bits at GF(32003) and 32 bits at GF(2^31−1), with
  32-bit column indices. Zeebra uses 16 bytes per live entry (`mq10-current-profile.md:81-97`).
- **The inner loop is AVX2**, multiplying 16-bit coefficients on this build.

The table does not apportion the 4.8x among these three. The ranking in §4 is the decision this
measurement supports, not a measured share.

## 4. Ranking for #268, #269, #270 and #715

1. **#269, back-substitution first.** Back-substitution is 49.8% of Zeebra's batch products and
   0.23% of msolve's. msolve's correct, identical output shows that reducer rows need no reduced
   tails. Forward products alone are 585 M, which is 2.09x msolve. That is the work-side bound: a
   count of products, not a time prediction. No stage share here is offered as a speedup.
2. **#269 / #270, the forward kernel.** The obvious candidate for the per-product 4.8x is a dense
   `i64` accumulator with deferred modular reduction against read-only reducers, which is msolve's
   design. #269 owns the scan and loop. #270 owns deferred reduction per field width.
3. **#268, entry width.** 16 bytes against 4+2 or 4+4 bytes. This matters for the 12x peak-RSS
   ratio and for bandwidth, once the kernel stops copying merged rows.
4. **#715, multirow reuse.** msolve does not use multirow bands, so this measurement says nothing
   for or against it. It ranks last on this evidence.

**For parallel F4 (#728, #730).** msolve runs the forward phase under OpenMP with dynamic row
scheduling and CAS pivot publication. It runs new-pivot interreduction serially, which it can
afford at 0.23% of products. Zeebra's backward phase is about half its products. Parallelizing the
forward phase alone therefore bounds the product share at about 2x until #269 removes the
back-substitution, so #269 should land before #728's prototype is judged.

**Not owned by any existing issue:** symbolic preprocessing builds 1.20x msolve's rows and 1.19x
its columns on the same pairs. Filed as #742.

## 5. Reproducing

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-737 RUSTC_WRAPPER=""
cargo build --release --example msolve_gap
B=$CARGO_TARGET_DIR/release/examples/msolve_gap
$B --characteristic 32003 --write-input mq10-32003.ms     # msolve's input, same digest
taskset -c 4 $B --characteristic 32003                    # per-batch shapes, totals, stage clocks
taskset -c 4 msolve -f mq10-32003.ms -o out -v 2 -t 1 -g 2

python3 -I tools/external/msolve-count.py \
  ~/.local/opt/zeebra-ext/src/msolve-0.11.0 /buildcache/cargo-target/zeebra-737/msolve-count
LD_LIBRARY_PATH=/buildcache/cargo-target/zeebra-737/msolve-count/src/neogb/.libs \
  /buildcache/cargo-target/zeebra-737/msolve-count/.libs/msolve \
  -f mq10-32003.ms -o out -t 1 -g 2 2>&1 | grep ZB_COUNT
```

Use `2147483647` for the second field. The timed cohort interleaved Zeebra and stock msolve for
five rounds per field under `tools/benchlock.sh`. Its raw output is
`research/msolve-gap/cohort.txt`.
