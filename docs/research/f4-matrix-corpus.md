# The F4 matrix corpus: real Macaulay matrices, pinned, and whether they predict

**Measured at:** `680692f2`, on base `0882def9` — recorded at the time rather than recovered (#335).
The branch was then rebased onto `ced9cb51`, which brings in #583's `sort_unstable_by` on the
Macaulay columns (+108/-4 in `macaulay.rs`) and #490's live-entry budget. **Every pinned digest in
[§2](#2-the-corpus) was re-derived after the rebase and is unchanged**, which is what licenses
quoting the pre-rebase timings: a monomial order is strict on distinct monomials and the columns are
distinct, so the unstable sort has no tie to break and produces the identical permutation — and the
corpus is what establishes that rather than the argument. Every other commit on this branch changes
prose and doc comments only. One machine, one `release`
build (`lto = "fat"`, `codegen-units = 1`), `RUSTFLAGS` unset, `RUSTC_WRAPPER` empty, a private
`CARGO_TARGET_DIR`, `taskset -c 0-15`, arms interleaved within one process, three repetitions,
medians. Load was gated **inside** `tools/benchlock.sh` and read again at the end;
[§5.3](#53-the-conditions-and-what-they-do-and-do-not-permit) gives both readings and says what they
permit — which is the ranking and not the magnitudes.

The counters in [§2](#2-the-corpus) and the costs in [§4](#4-what-it-costs) are not timings and do
not depend on any of that; shapes, nonzero counts, digests, fill-in ratios and ranks are exact and
reproduce from `cargo run --release --example f4_matrix_corpus -- pin` at any commit where the
corpus has not moved, which is what `test_every_entry_is_pinned_and_in_its_regime` asserts.

This is #262. It delivers a fixed set of the Macaulay matrices F4 really builds, so that an
elimination or construction kernel can be iterated on in milliseconds instead of through
seconds-long whole runs, and so that a change's effect on the kernel is not confounded with its
effect on matrix *shape*.

---

## 0. The issue's motivating figure was superseded; its conclusion survives on other evidence

#262 opens with "Elimination is 65%–88% of an F4 run
(`docs/MILESTONE-F4-OPTIMIZATION.md` §6.2), so it is where the epic's optimization effort will go."
**Both the number and the citation are superseded, and they were already superseded inside the file
the issue cites.**

- §6.2 (`docs/MILESTONE-F4-OPTIMIZATION.md:402`) measured the configuration that is now
  `F4Options::baseline()` — every optimization off — and not the default. §8.7 records that the
  default moved at the end of M16.
- §8.5 of the same file (`:1821`) says: *"At M16-0, elimination was 65–88% of every instance above a
  millisecond. It is now 17% of katsura-7 grlex and 7% of katsura-6 lex."* §9.1 repeats it as
  7–17%. The bottleneck moved to interreduction and matrix construction, and #330, #471, #477,
  #536, #554, #555, #575 and #582 all landed on those.

So on the small katsura/cyclic systems, elimination is **not** the stage the issue describes.

**But the conclusion holds on the instance the competitive board is keyed to, and more strongly than
the issue claims.** `docs/research/interreduction-cost.md` §3c and §3g.3, at `489ccbd6`, on
`mq-random-10` grevlex at digest `72d0ad315fc25409` under the arm that #575 made the default:
elimination is **4 531 ms of 4 851 ms, about 93%**, with interreduction at 0.34% and §3g.3's own
note that *"nothing is left inside the stage to take"* there. The two readings are not in conflict —
they are different instance families. Elimination is a small share of a six-variable katsura and
almost all of a ten-variable MQ system, and the MQ family is what M25 onward is measured on.

**What that means for this corpus.** It must not be a katsura-only corpus, because katsura is the
family where the stage it serves is small; and it must record which option preset each matrix came
from, because §6.2's shares and §8.5's shares differ by *preset* and not only by date. Both are
done below. The corpus is still worth having, and #269 (H13) — titled "the 65-88% stage" — should be
retitled; [§6](#6-what-this-leaves) files that.

---

## 1. What the corpus is, and what it is not

A **generator plus pinned digests**. No matrix bytes are committed, which is what #262 asked for and
is also forced: `serde` is derived on this crate's scalars and polynomials but on none of its matrix
types, `bincode` is a dev-dependency, `serde_json` is not a dependency at all, and a committed
binary corpus of the sizes involved would be tens of megabytes. The repository cost of this change
is source only — see [§4](#4-what-it-costs).

Each entry names an instance, a monomial order, an option preset, and which batch to take. Running
it produces a `MacaulayMatrix`, and the entry pins that matrix's batch index, dimensions, reducer
row count, nonzero count, and a 16-hex-digit sha256 over a canonical encoding of its labels and
entries.

### 1.1 The matrices are captured, not reconstructed

This is the whole point and it is where the recent failures in this repository were.

`BatchObserver` already had one hook, `batch`, which fires before symbolic preprocessing with the
basis and the selected pairs. That is enough to *rebuild* a matrix, and `benches/f4_stages.rs`,
`examples/f4_blocks.rs`, `examples/elimination_density.rs` and three others do exactly that. But
rebuilding takes the options, the reducer-selection policy and the cross-batch reducer cache as
arguments, so **a harness that passes different ones gets a different matrix and no error at all**.
`benches/f4_stages.rs:120` passes `ReducerSelection::FirstApplicable` and `ReducerCache::disabled()`
written out literally, under `F4Options::baseline()`.

So #262 adds a second hook, `BatchObserver::matrix`, called in `reduce_batch_observed_in` after
construction and **before** elimination, which is in place. What it hands over is the object F4 is
about to eliminate. It is defaulted to an empty body, so the three existing observers outside this
module are unaffected and the ordinary path pays nothing for it.

The rebuild route is then **asserted** against the captured one rather than trusted:

- `test_rebuilding_from_the_inputs_reproduces_the_captured_matrix` — rebuilding a captured batch
  from its own inputs under its own preset gives back the captured matrix, by full `PartialEq` and
  by digest, under both presets.
- `test_a_rebuild_under_a_different_reducer_policy_is_a_different_matrix` — the teeth. Rebuilding
  the same batch with `ReducerSelection::LargestLeadingMonomial` produces a different digest, so
  the agreement above is a property of the configuration and not an identity.
- `test_the_largest_captured_matrix_is_the_largest_the_run_reports` — the capture's row count equals
  `F4Statistics::max_matrix_rows`, which the main loop accumulates from the per-batch statistics.
  Two independent readings of the same matrix; a hook that fired after elimination, or a selector
  that took the wrong batch, disagrees here.
- `test_the_digest_reads_the_entries_and_not_only_the_shape` — eliminating a matrix leaves its
  dimensions and labels alone and changes its contents, and the digest notices.

There is exactly one matrix construction site in the crate now. `build_batch_matrix` is factored out
of `reduce_batch_in`, which calls it, so the function a harness builds through and the function F4
builds through are the same function rather than two that agree today.

**Why this much machinery for a benchmark corpus.** Three measurements in the last period of this
repository were measurements of the wrong artifact: #517 timed a parameterized template rather than
the tile under study and the array-indexed accumulator cost ~20% on its own; #317's first gate read
3.32x on a monomial order that never touches the quantity under test, because the arms were
different call sites; #412 published a 3.21x "width penalty" that was a ratio between two different
polynomial pairs, one of them degree 1. Every one would have been caught by asserting the artifact,
and none was caught by looking at the number.

### 1.2 Which preset built a matrix is part of its identity

`F4Options::baseline()` and `F4Options::default()` do not build the same matrices.
`PairCriteria::ALL` discards pairs that `PRODUCT_ONLY` sends to a matrix — §8.5 records this as
replacing 59 large matrices with 107 small ones on katsura-6 lex — and `reduce_batch_rows` changes
what later batches are selected from. So the two presets differ in matrix count, shape and density,
not only in how fast the same matrix is eliminated.

`test_the_two_presets_do_not_build_the_same_matrix` asserts the difference on katsura-5 grevlex, so
the claim is checked rather than asserted. Every pre-existing stage harness in this repository runs
on `baseline()`, which means every existing per-stage figure describes matrices the shipping default
never builds. The corpus carries entries under both presets and `MatrixSpec::options` names which.

### 1.3 The regimes are checked, not labelled

Each entry declares one of three scaffolding regimes — `scaffolded` at or above 80% reducer rows,
`mixed` from 40% to 80%, `pair-heavy` below 40%. `test_every_entry_is_pinned_and_in_its_regime`
asserts the captured matrix's own reducer share falls in the declared band. A regime that was merely
written down would drift the first time a reducer policy moved, and a coverage claim that is not
checked is a coverage claim that is not true.

---

## 2. The corpus

The default set has seventeen matrices. Six field types across five distinct field orders, three scaffolding regimes,
both option presets, and shapes from 61x72 to 12554x12020. Every column but the last two is a
**counter** rather than a timing, so none of it depends on the machine or the profile; `fill-in` is
the live entry count at elimination's high-water and at its end, over the count as built, under the
backend the entry's own preset selects.

| label | field | bits | preset | batch | shape | red% | nz | density | fill-in peak / final | rank | regime | digest |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `katsura-7/grevlex/m31/default` | `Mersenne31` | 31 | default | 4 of 7 | 361x369 | 72.9 | 10 546 | 0.0792 | 1.65x / 1.58x | 306 | mixed | `01c80075ca42a4c2` |
| `katsura-7/grevlex/m31/baseline` | `Mersenne31` | 31 | baseline | 8 of 10 | 6810x6862 | 99.7 | 112 200 | 0.0024 | 6.28x / 6.28x | 6 799 | scaffolded | `746a1103c3b7c6fe` |
| `katsura-6/lex/m31/baseline` | `Mersenne31` | 31 | baseline | 21 of 59 | 1954x945 | 42.4 | 64 756 | 0.0351 | 1.48x / 1.48x | 914 | mixed | `3f5824bd5619b32d` |
| `cyclic-6/grevlex/m31/default` | `Mersenne31` | 31 | default | 7 of 18 | 159x175 | 35.8 | 6 529 | 0.2346 | 1.01x / 0.55x | 112 | pair-heavy | `b059ff3c5e16302b` |
| `cyclic-6/lex/m31/default` | `Mersenne31` | 31 | default | 56 of 58 | 1026x1048 | 99.2 | 29 696 | 0.0276 | 1.42x / 0.78x | 1 022 | scaffolded | `b46c8477b7533630` |
| `katsura-7/grevlex/p64/default` | `Zp18446744073709551557` | 64 | default | 4 of 7 | 361x369 | 72.9 | 10 546 | 0.0792 | 1.65x / 1.58x | 306 | mixed | `ee5963facafddbde` |
| `cyclic-6/grevlex/p64/default` | `Zp18446744073709551557` | 64 | default | 7 of 18 | 159x175 | 35.8 | 6 529 | 0.2346 | 1.01x / 0.55x | 112 | pair-heavy | `b851c4a0cbbbf7bd` |
| `katsura-6/lex/p64/baseline` | `Zp18446744073709551557` | 64 | baseline | 21 of 59 | 1954x945 | 42.4 | 64 756 | 0.0351 | 1.48x / 1.48x | 914 | mixed | `43b5952f8a8b1bde` |
| `katsura-6/grevlex/bn254/default` | `Bn254Fr` | 254 | default | 3 of 6 | 144x152 | 68.1 | 2 461 | 0.1124 | 1.48x / 1.39x | 121 | mixed | `7531e274c605e4dc` |
| `cyclic-5/grevlex/bn254/baseline` | `Bn254Fr` | 254 | baseline | 18 of 22 | 635x379 | 49.9 | 8 372 | 0.0348 | 1.51x / 1.49x | 365 | mixed | `3e2099571be467d7` |
| `mq-random-6/grevlex/p31x64/default` | `Zp2147483647` | 31 | default | 5 of 9 | 757x756 | 87.1 | 16 074 | 0.0281 | 2.56x / 2.39x | 698 | scaffolded | `62e9d2f6c591d1f6` |
| `mq-random-6/grevlex/p31x64/baseline` | `Zp2147483647` | 31 | baseline | 10 of 11 | 3305x3342 | 98.9 | 66 032 | 0.0060 | 6.20x / 6.18x | 3 285 | scaffolded | `13016bd535663e7d` |
| `mq-random-10/grevlex/p31x64/default` | `Zp2147483647` | 31 | default | 7 of 10 | 12554x12020 | 88.3 | 783 737 | 0.0052 | 5.02x / 4.81x | 11 665 | scaffolded | `f9a86d072bdc760f` |
| `cyclic-6/grevlex/gf2/default` | `Zp2` | 1 | default | 6 of 21 | 130x163 | 38.5 | 2 314 | 0.1092 | 1.03x / 0.76x | 94 | pair-heavy | `23a43be1462915fb` |
| `cyclic-7/grevlex/gf2/default` | `Zp2` | 1 | default | 16 of 27 | 1146x795 | 32.5 | 84 450 | 0.0927 | 1.01x / 0.54x | 639 | pair-heavy | `0058c956e245beff` |
| `cyclic-6/grevlex/gf256/default` | `Gf256Mq` | 8 | default | 6 of 21 | 130x163 | 38.5 | 2 314 | 0.1092 | 1.03x / 0.76x | 94 | pair-heavy | `688436ee205fd305` |
| `cyclic-5/lex/gf256/default` | `Gf256Mq` | 8 | default | 14 of 21 | 61x72 | 90.2 | 438 | 0.0997 | 1.02x / 0.80x | 58 | scaffolded | `5d08ac9dd7acb1ce` |

`bits` is the bit length of the field's **order**, which is why `Mersenne31` and `Zp2147483647` both
read 31: they are the same field in a 32-bit and a 64-bit representation. That pair is in the corpus
deliberately — same arithmetic, different entry size, which is exactly the axis a per-width kernel is
specialized along — and the Rust type name is what tells them apart.

Four things in this table were not expected and are worth reading off it.

**The shipping default builds matrices 18.8x shorter than `baseline` does.** katsura-7 grevlex is
6810x6862 under `baseline` and 361x369 under the default, on the same instance and the same order.
Every pre-existing per-stage harness in this repository runs on `baseline()`, so every existing
elimination figure describes a matrix with 19x the rows and 2.6x the fill-in of the one the default
actually eliminates. `mq-random-6` says the same thing less extremely: 3305x3342 against 757x756,
and 6.20x fill-in against 2.56x. This is the gap `MatrixSpec::options` exists to make visible, and
it is the reason a corpus that did not record its preset would be a corpus of matrices from an
unspecified configuration.

**Fill-in is not universal — five entries end up *sparser* than they began.** Every cyclic entry
under a graded order finishes between 0.54x and 0.80x of its initial nonzero count, and peaks at
1.01x–1.03x: the elimination barely allocates and then deletes. The katsura and MQ entries fill in
by 1.48x to 6.28x. So "fill-in" is a property of the family and the order and not of F4, and a
kernel tuned only on a filling matrix is tuned on half the corpus.

**The dense backend cannot run the whole corpus.** `Backend::Dense` on `mq-random-10` reaches
**75 449 540** live entries against the 20 000 000 `F4Options::default()` admits — and its cell
buffer alone would be 12 554 x 12 020 x 16 bytes, about 2.4 GB, which `max_live_bytes` does not
charge for at all. `benches/f4_matrix_corpus.rs` probes each backend once before measuring it and
reports the refusal rather than panicking, because a suite whose coverage silently depends on which
matrices happen to fit is a suite that cannot be compared with itself.

**GF(2) and GF(2^8) build the *same matrix* on cyclic-6.** `cyclic-6/grevlex/gf2/default` and
`cyclic-6/grevlex/gf256/default` are 130x163 with 2 314 entries in both, and they are equal
entry for entry: cyclic's coefficients are `±1`, and the one and the minus one of GF(2) and of
GF(2^8) render identically. The first cut of this corpus digested them to the same sixteen hex
digits, which would have made two entries on the per-field-width axis interchangeable — on the one
axis the corpus exists to separate. The digest now carries the field's type name, and
`test_two_fields_with_identical_entries_digest_differently` is the regression test.

### 2.1 The opt-in large set (#640)

| label | batch | rows | columns | reducer rows | nonzeros | digest |
|---|---|---|---|---|---|---|
| `mq-random-14/grevlex/p31x64/default-64m` | 6 | 75 091 | 76 194 | 67 411 | 24 843 682 | `b6b0c2aa13296fec` |

`large_corpus()` and `walk_large_corpus()` use the same spec/dispatch generator and fingerprint
check as the default set. They are separate entry points: neither `walk_corpus`, the normal
benchmark nor CI smoke includes the large entry. `list-large` prints its metadata and budgets,
`pin-large` derives the fingerprint, and `check-large` refuses a drifted capture. `check-all`
verifies both sets in one process for a whole-corpus capture-cost measurement.

The selected artifact is the matrix built by MQ14 batch 6 (zero-based), not a final
interreduction matrix. `BatchSelector::Prefix(6)` executes earlier batches, clones the selected
matrix and its basis/pairs, then requests an observer stop before elimination. F4 itself returns
`StoppedByObserver`; only the capture wrapper converts that intentional stop into an artifact.
`CapturedMatrix::completed` is false and `batches` is 7, the observed prefix length. Errors before
the selected matrix remain errors. This avoids both a discovery run over the whole system and
all work after the target, while retaining enough inputs to verify a fresh rebuild.

The entry uses shipping strategies with an explicit 64 000 000-entry / 1 024 000 000-byte
allowance. The shipping 32 000 000-entry cap stops an earlier elimination at 32 001 899 live
entries, before the selected matrix can be captured. `OptionsPreset::RaisedDefault` records both
caps; ordinary defaults remain 32 000 000 entries / 512 000 000 bytes. A successful capture does not imply elimination fits that cap.
`ZEEBRA_F4_LARGE_CORPUS=1 cargo bench --bench f4_matrix_corpus` selects only the large set,
skips dense elimination and uses one setup clone per iteration. Backend budget refusals are
reported rather than timed. Use a timeout, process RSS guard and benchmark lock for explicit runs.

---

## 3. GBLA's published matrices: the catalogue survives, the data does not

#262 asks whether GBLA's collection of real F4 matrices is still retrievable and whether its format
is worth reading. Checked on 2026-11-09:

| thing | URL | result |
|---|---|---|
| project page | `https://hpac.imag.fr/gbla/` | **200** |
| matrix database page | `https://hpac.imag.fr/gbla/db.html` | **200**, 4 246 bytes |
| every matrix file | e.g. `https://hpac.imag.fr/gbla/F4/kat12/mat1.gbm.gz` | **404**, all nine |
| source tarball | `https://hpac.imag.fr/gbla/data/src/gbla-0.2.tar.gz` | **200**, 283 542 bytes, sha256 `2c7bbf6f8383ea1299672d7831da891b2bb009c00cc15f48c11247425291993c` |
| GitHub mirror | `https://github.com/ederc/gbla` | **504** from here |

So the *catalogue* is intact and the *data* is gone. What the catalogue still says, which is worth
recording because it is the only surviving measurement of what a published F4 matrix looks like:

| algo | problem | rows | cols | nnz | density | mod |
|---|---|---|---|---|---|---|
| F4 | kat12 | 716 | 1 218 | 68 130 | 7.81% | 65521 |
| F4 | kat12 | 21 910 | 23 120 | 26 070 000 | 5.15% | 65521 |
| F4 | kat13 | 7 757 | 9 161 | 3 823 000 | 5.38% | 65521 |
| F5 | kat14 | 69 660 | 84 570 | 118 100 000 | 2.00% | 65521 |
| F5 | kat15 | 86 490 | 102 700 | 184 200 000 | 2.07% | 65521 |

Two observations.

**The gap remains size, although #640 narrows it.** GBLA's F4 and F5 matrices are 2.0%–7.8%
dense as built. Its largest is 86 490 x 102 700 with 184 million entries. The default set tops out
at 783 737 entries; the opt-in MQ14 capture adds 24 843 682 entries, about 7.4 times smaller than
that GBLA maximum. This reaches the 10^7-entry regime but still leaves 10^8 untested. The kernel
rankings in §5 were measured on the original seventeen matrices; extending the corpus does not
extend those measurements to the large entry.

**The format is readable and not worth reading.** The `.gbm` reader is `draft/io.h`'s
`readFileSplit`: a little-endian stream of a version word XOR'd with `1 << 31`, then `m`, `n`, `mod`,
`nnz`, a per-row start array, a row-to-polynomial correspondence map, a column-id buffer, and a pool
of distinct coefficient polynomials that rows index into. The widths are compile-time typedefs
(`dimen_t`, `elemt_s`, `elemt_m`) rather than fields, so the file is only self-describing to the
extent the version word distinguishes them, and `tools/dump_matrix` exists precisely because the
format needs a converter to be read by anything else. It would be implementable. But the one reason
to implement it — comparing Zeebra's kernel against published GBLA results on the published matrices
— is gone with the matrices, and a reader for a format with no retrievable data would be dead code
with a test fixture that has to be invented. **Not implemented, and the decision is recorded here so
it does not have to be re-derived.**

---

## 4. What it costs

Source only. No binary data is added to the repository.

The module, example and benchmark store generators and pinned fingerprints, with no serialized
matrix format. The MQ14 entry alone holds 24 843 682 `(usize, Zp2147483647)` entries, so its
coefficient payload allowance must account for 16 bytes per entry on this 64-bit target, before
row vectors, column monomials, captured inputs and other process allocations. The live-entry cap
is not an RSS cap.

### 4.1 Historical small-set measurements

The original seventeen-entry capture took **17.6 s** in a `ci-release` build, and
`test_every_entry_is_pinned_and_in_its_regime` — which captures all seventeen *and* rebuilds each
one from its own inputs — took **15.3 s**. `cargo bench --bench f4_matrix_corpus -- --test`, which
is what CI's benchmark smoke job runs on every pull request, took about **80 s** of run time on top
of its build; most of that is `mq-random-10`, which is also the entry the corpus most needs.

Capturing a complete entry costs one F4 run, or two when the entry selects the largest
batch: `BatchSelector::Largest` is resolved in a first pass that records row counts and nothing
else, so the second pass can clone one basis instead of all of them. That is the only reason the
selector is two runs and not one, and it is what keeps capturing a late batch of a long run cheaper
than the run itself.

---

## 5. The predictiveness check

#262's acceptance requires this, and requires it recorded **including if it fails**: a corpus that
does not predict end-to-end behaviour would be optimized at the expense of the thing that matters,
which is an explicit non-goal of the milestone.

### 5.1 What is being compared, and why these two arms

Two **elimination kernels**, not two algorithms: `Backend::Sparse` is the sparse pivot loop and
`Backend::Adaptive` is a dense row accumulator over sparse pivots. Same pivot rule, same row
operation count, different inner loop. `Backend::Dense` is deliberately not an arm — it cannot run
the whole corpus ([§2](#2-the-corpus)), and an arm that is absent on the largest entry would make
the ranking depend on which matrices happened to fit.

For each entry, two rankings are taken in one process:

- **micro** — `eliminate_to` on the captured matrix under each backend, under the plan, row form and
  entry allowance the entry's own preset selects. Nothing else moves.
- **run** — `f4_with_options` on the whole instance, under the same preset with only `elimination`
  changed.

Three repetitions, **arms interleaved within each repetition**, medians reported. The quantity the
check is about is the *sign* of each ratio, not its magnitude: the two rankings either pick the same
backend or they do not. That is deliberately robust to a noisy machine, and it had to be —
[§5.3](#53-the-conditions-and-what-they-do-and-do-not-permit).

Before any timing is taken, the example asserts that rebuilding the entry from its own inputs
reproduces the captured matrix. A figure published from this mode therefore cannot be a figure about
a matrix the live path does not build.

### 5.2 The result

`micro ratio` and `run ratio` are both sparse over adaptive, so **above 1.00x means the adaptive
accumulator won**. `agree` is whether the two rankings picked the same backend.

| label | shape | nz | micro sparse | micro adaptive | micro ratio | run sparse | run adaptive | run ratio | agree |
|---|---|---|---|---|---|---|---|---|---|
| `katsura-7/grevlex/m31/default` | 361x369 | 10 546 | 3.890 ms | 1.773 ms | **2.19x** | 12.755 ms | 8.106 ms | **1.57x** | yes |
| `katsura-7/grevlex/m31/baseline` | 6810x6862 | 112 200 | 64.652 ms | 13.036 ms | **4.96x** | 701.495 ms | 310.171 ms | **2.26x** | yes |
| `katsura-6/lex/m31/baseline` | 1954x945 | 64 756 | 34.876 ms | 15.612 ms | **2.23x** | 364.329 ms | 215.806 ms | **1.69x** | yes |
| `cyclic-6/grevlex/m31/default` | 159x175 | 6 529 | 1.012 ms | 0.712 ms | **1.42x** | 7.623 ms | 6.333 ms | **1.20x** | yes |
| `cyclic-6/lex/m31/default` | 1026x1048 | 29 696 | 4.243 ms | 3.575 ms | **1.19x** | 95.305 ms | 85.537 ms | **1.11x** | yes |
| `katsura-7/grevlex/p64/default` | 361x369 | 10 546 | 3.929 ms | 1.970 ms | **1.99x** | 13.087 ms | 8.426 ms | **1.55x** | yes |
| `cyclic-6/grevlex/p64/default` | 159x175 | 6 529 | 1.107 ms | 0.779 ms | **1.42x** | 8.040 ms | 6.702 ms | **1.20x** | yes |
| `katsura-6/lex/p64/baseline` | 1954x945 | 64 756 | 38.304 ms | 18.253 ms | **2.10x** | 402.433 ms | 253.736 ms | **1.59x** | yes |
| `katsura-6/grevlex/bn254/default` | 144x152 | 2 461 | 2.223 ms | 1.880 ms | **1.18x** | 6.517 ms | 5.696 ms | **1.14x** | yes |
| `cyclic-5/grevlex/bn254/baseline` | 635x379 | 8 372 | 24.116 ms | 19.905 ms | **1.21x** | 101.981 ms | 85.366 ms | **1.19x** | yes |
| `mq-random-6/grevlex/p31x64/default` | 757x756 | 16 074 | 11.520 ms | 4.163 ms | **2.77x** | 25.879 ms | 14.736 ms | **1.76x** | yes |
| `mq-random-6/grevlex/p31x64/baseline` | 3305x3342 | 66 032 | 70.876 ms | 12.589 ms | **5.63x** | 373.017 ms | 170.895 ms | **2.18x** | yes |
| `mq-random-10/grevlex/p31x64/default` | 12554x12020 | 783 737 | 26 944.371 ms | 3 168.882 ms | **8.50x** | 34 015.100 ms | 5 393.497 ms | **6.31x** | yes |
| `cyclic-6/grevlex/gf2/default` | 130x163 | 2 314 | 0.310 ms | 0.195 ms | **1.59x** | 2.356 ms | 2.057 ms | **1.15x** | yes |
| `cyclic-7/grevlex/gf2/default` | 1146x795 | 84 450 | 62.670 ms | 28.650 ms | **2.19x** | 488.381 ms | 266.199 ms | **1.83x** | yes |
| `cyclic-6/grevlex/gf256/default` | 130x163 | 2 314 | 0.489 ms | 0.345 ms | **1.42x** | 2.934 ms | 2.540 ms | **1.16x** | yes |
| `cyclic-5/lex/gf256/default` | 61x72 | 438 | 0.041 ms | 0.033 ms | **1.26x** | 0.816 ms | 0.776 ms | **1.05x** | yes |

**It predicts. 17 of 17 rankings agree, and the agreement is stronger than the criterion asked
for.**

The criterion was that both rankings pick the same backend. They do, on every entry. But the
magnitudes line up too, and in a way that is worth stating because it is the direction a
microbenchmark ought to err in:

- **Rank correlation between the two ratio columns is Spearman rho = 0.930**, with 13 discordant
  pairs of 136. A corpus that merely picked the same winner would have rho near zero and still have
  passed.
- **The micro ratio is above the run ratio on every single entry**, by 1.02x to 2.58x. That is not a
  coincidence and it is not noise: the whole run contains symbolic preprocessing, construction,
  candidate extraction, pair bookkeeping and interreduction, none of which the backend touches, so
  Amdahl's law caps the end-to-end effect below the kernel's own. **The corpus therefore
  over-states a kernel win and never under-states one**, which is the safe direction: a change this
  corpus says is worthless is worthless end to end, and a change it says is worth 5x may be worth
  2x.
- **The ordering of the entries by how much the kernel matters is itself informative.**
  `mq-random-10` is 8.50x in the kernel and 6.31x end to end — the two are nearly equal, because on
  that instance the kernel *is* the run. `cyclic-5/lex/gf256` is 1.26x and 1.05x, because at 438
  entries there is almost nothing for a kernel to do. That spread is the corpus doing its job: the
  same change ranks the same way everywhere and matters a hundredfold more in one place than
  another, and a single-instance A/B could not have shown either.

One figure from this table is a direct confirmation of §0's correction. `mq-random-10`'s single
largest batch takes **3 168.882 ms of the 5 393.497 ms** whole run under the adaptive backend — one
batch's elimination is **58.8%** of the entire computation. `interreduction-cost.md` §3g.3's ~93% for
the whole stage is therefore not surprising, and §6.2's 65-88% framing is stale in the direction of
*understating* the share on this family, not overstating it.

#### What would have falsified it

A `**NO**` in the last column: an entry where the corpus prefers one backend and the whole run
prefers the other. The rows that could plausibly have produced one are the five with run ratios
under 1.20x — `cyclic-5/lex/gf256` at 1.05x, `cyclic-6/lex/m31` at 1.11x, the BN254 pair at 1.14x
and 1.19x, and the GF(2)/GF(2^8) cyclic-6 pair at 1.15x and 1.16x — where the end-to-end effect is
small enough that the sign could flip on a noisy machine. None did, and all five are *small matrices
on which the corpus also reported a small effect*, so the two measurements agree about there being
little to see rather than disagreeing about what is there.

The check is **not** a general claim that any microbenchmark over this corpus predicts end-to-end
cost. It is a claim about one real kernel A/B over seventeen matrices. A change that altered matrix
*shape* — a pair criterion, a reducer policy, a selection strategy — is outside what a fixed set of
matrices can see at all, and is the thing `examples/f4_profile.rs` and `benches/grobner.rs` are for.

### 5.3 The conditions, and what they do and do not permit

The run was taken inside `tools/benchlock.sh`, so nothing else measured against it, and `taskset -c
0-15`-pinned so the two arms shared one core set.

**The box was busy, and the one-minute load average is not the quantity that says how busy.** At the
start of the run it read **2 090.41** with **16 of 9 892** threads runnable, `procs_blocked` 0, and
four processes in `D` state. A 64-core machine with 16 runnable threads is a quarter loaded; a
one-minute average of 2 090 on that machine is counting tasks in uninterruptible wait on a tmpfs
that is 75% full of other agents' build output, not tasks waiting for a core. The gate inside the
lock therefore reads `procs_running` and `procs_blocked` and requires six consecutive clear samples,
and records the average beside them rather than gating on it. Both readings:

```text
START  2026-11-09T06:29:28Z  running=16 blocked=0 dstate=2 loadavg1=2090.41 runnable_total=16/9892
END    2026-11-09T06:33:26Z  running=5  blocked=0 dstate=4 loadavg1=2049.59 runnable_total=5/9496
```

What that permits and what it does not:

- **Permitted: the ranking.** Both arms of every pair ran in the same process, interleaved, on the
  same pinned cores, within seconds of each other. A machine-wide slowdown moves both arms of a
  ratio together and cannot change its sign unless the ratio is already within noise — which is
  reported per row rather than averaged away.
- **Not permitted: the magnitudes as absolute cost.** No figure in
  [§5.2](#52-the-result) should be quoted as "elimination takes X ms"; the figures in
  `docs/MILESTONE-F4-OPTIMIZATION.md` §8.5 and `docs/research/interreduction-cost.md` §3c were taken
  on a quiet machine and these were not.
- **Not permitted: a ratio close to 1.00x read as a direction.** Those rows are reported as what they
  are.

---

## 6. What this leaves

**The opt-in large entry reaches 10^7, while 10^8 remains uncovered.** #640 adds a live
MQ14 batch through prefix capture, without completing the system or eliminating the selected
matrix. The ordinary CI corpus remains at seventeen entries. Large captures are verified
explicitly; the historical predictiveness experiment has not been repeated at that scale.

**#269 (H13) is named for a stage share that moved.** Its title is "F4 elimination kernels — the
65-88% stage". That number is §6.2's, under what is now `baseline()`. On the default it is 7–17% of
the katsura and cyclic rungs and ~93% of `mq-random-10`. The issue is still worth doing and the
title is now misleading about *where*. **Filed as #639, Priority Medium.**

**The GF(2) entries measure one bit per 32, not a bitsliced kernel.** `Zp2` is
`PrimeFieldElement32<2>`, so a GF(2) matrix entry here is a `(usize, u32)` pair — the decision and
its cost are recorded in `docs/research/boolean-solving.md` §8. Those entries are therefore a
*correctness* and *shape* sample for characteristic two and not a measurement of what GF(2)
elimination could cost; a packed representation would be a different kernel on the same matrices,
which is exactly the comparison this corpus makes cheap, and is H14's question rather than this
issue's.

**There is no file format, and that is a decision rather than an omission.** #262's deliverables ask
for "a dump/load path for F4 matrices behind the observer hook, with a documented format"; its
research questions and acceptance criteria ask for the opposite ("prefer a generator plus pinned
parameters over committed binary matrices", "no large binaries added to the repository"). The
generated route is what landed, for the reasons in [§1](#1-what-the-corpus-is-and-what-it-is-not)
and because the one external comparand a format existed to read is gone
([§3](#3-gblas-published-matrices-the-catalogue-survives-the-data-does-not)). **Filed as #646,
Priority Low**, which also records when it should be reopened — an external comparand reappearing,
an entry too expensive to regenerate, or wanting to hand a matrix to a tool outside this crate, for
which GBLA's own SMS export is the smaller first step.

**No Fukuoka MQ instance.** Types II and V are the published GF(2^8) MQ systems and the natural
wide-characteristic-two entries, but they come from `research/instances/`, which
`tools/fetch-mq-challenge.sh` (moved out in #668) downloads and `.gitignore` excludes — so an entry built on them could
not be captured on a machine that had not fetched them, and `walk_corpus` would fail rather than
skip. The GF(2^8) coverage here is cyclic instead.

**The matrix is captured; the *stage* around it is not.** `BatchObserver::matrix` hands over the
matrix, so an elimination or construction kernel can be measured in isolation. Symbolic
preprocessing cannot: its input is the basis and the pairs, which `trace_batches` already gives, and
its output is the thing the matrix is built from. `benches/f4_stages.rs` covers that stage and this
corpus does not replace it.
