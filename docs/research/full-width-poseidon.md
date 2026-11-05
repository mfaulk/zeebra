# The official state width: what a `t = 16` CICO system does to F4, and where it stops

Reference for M23-B (#138), which consumes #78 and #81.

Every figure comes from

```sh
ZEEBRA_WALL_SECONDS=120 ZEEBRA_CORES=0-7 tools/scoreboard.sh ladder --write
```

on one machine, pinned to cores 0–7, release build, `-C target-cpu=x86-64-v3`. The budget is stated
in every record: 200,000 columns, **20,000,000 live entries** — the bound that actually binds — a
10,000-batch cap, and a 120-second wall clock as a backstop. The entry cap is the binding one on
purpose: an entry count is reproducible on any machine, where a wall-clock stop is a fact about
this one.

## 1. What these rows are

Nine instances, frozen in M23-0 before any of them was run: the official field (KoalaBear),
`alpha = 3`, the official state width `t = 16`, `k = 2`, the official input constants
`C_1 = 0xc09de4, C_2 = 0xee6282` and the official exact objective. Only the round counts are
reduced — `R_F ∈ {2, 4, 6}` against `R_P ∈ {0, 2, 4}`, which brackets the official `R_F = 6` from
below in both parameters.

| | |
|---|---|
| variables | `14 + 16·R_F + R_P`, from 46 to 114 |
| equations | `16·R_F + R_P + 2`, from 34 to 102 |
| `N − E` | **12**, on every row, whatever the rounds |

That last line is the one to keep in view. M22-E measured that the underdetermined direction, not
the state width, is what took the small `t = 3` instance from degree 5 to degree 11; at `t = 16`
with `k = 2` the surplus is twelve coordinates on every row and does not shrink along the ladder.
So each row is also run as a **slice** with all but two free inputs fixed at values drawn from a
precommitted seed, which leaves two unknowns against the two output constraints.

A slice is not a weaker version of the problem in the direction that matters: a witness on a slice
is a witness for the original system, since a slice is `I + ⟨x_i − a_i⟩` and its points are points
of `I`. The asymmetry is that an **empty** slice establishes nothing — which is why the scoreboard
has `RunOutcome::SliceEstablishedNothing` rather than reporting one as "no base-field point".

**No full-round claim is made anywhere here.** The official instances are `R_F = 6` with
`R_P ∈ {6, 8, 10}`, and all three were solved externally in 2026 by other people's attacks; these
rows are strictly below them in both round parameters.

## 2. The ladder

| instance | formulation | vars | eqs | deg | last deg done | max rows | max cols | peak entries | peak MB | s | outcome |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| `R_F=2 R_P=0` | as generated | 46 | 34 | 6 | 5 | 4 708 | 36 284 | 6 745 570 | 108.2 | 25.7 | **max_live_nonzeros** |
| `R_F=2 R_P=0` | slice | 46 | 46 | 4 | 4 | 20 866 | 17 424 | 6 414 960 | 102.8 | 30.3 | **basis complete** |
| `R_F=2 R_P=2` | as generated | 48 | 36 | 6 | 5 | 5 780 | 50 148 | 12 168 105 | 195.1 | 46.6 | max_matrix_columns |
| `R_F=2 R_P=2` | slice | 48 | 48 | 4 | 3 | 37 629 | 40 182 | 13 286 070 | 212.9 | 55.0 | max_live_nonzeros |
| `R_F=2 R_P=4` | as generated | 50 | 38 | 6 | 5 | 7 070 | 70 244 | 19 457 729 | 311.9 | 72.9 | max_matrix_columns |
| `R_F=2 R_P=4` | slice | 50 | 50 | 5 | 4 | 7 962 | 8 642 | 1 548 797 | 24.8 | 9.7 | max_live_nonzeros |
| `R_F=4 R_P=0` | as generated | 78 | 66 | 6 | 5 | 9 638 | 81 800 | 15 349 354 | 246.2 | 71.8 | max_matrix_columns |
| `R_F=4 R_P=0` | slice | 78 | 78 | 4 | 3 | 5 696 | 12 861 | 1 372 425 | 22.0 | 19.3 | max_live_nonzeros |
| `R_F=4 R_P=2` | as generated | 80 | 68 | 5 | 4 | 1 168 | 21 098 | 1 492 356 | 24.0 | 14.6 | max_live_nonzeros |
| `R_F=4 R_P=2` | slice | 80 | 80 | 4 | 3 | 6 205 | 15 363 | 1 480 281 | 23.7 | 21.1 | max_live_nonzeros |
| `R_F=4 R_P=4` | as generated | 82 | 70 | 5 | 4 | 1 248 | 24 441 | 1 852 108 | 29.8 | 18.2 | max_live_nonzeros |
| `R_F=4 R_P=4` | slice | 82 | 82 | 4 | 3 | 6 710 | 18 706 | 1 635 266 | 26.2 | 25.9 | max_live_nonzeros |
| `R_F=6 R_P=0` | as generated | 110 | 98 | 5 | 4 | 1 628 | 28 794 | 1 898 794 | 30.6 | 20.6 | max_live_nonzeros |
| `R_F=6 R_P=0` | slice | 110 | 110 | 4 | 3 | 5 696 | 23 059 | 1 549 495 | 25.0 | 26.0 | max_live_nonzeros |
| `R_F=6 R_P=2` | as generated | 112 | 100 | 5 | 4 | 1 710 | 31 296 | 2 167 596 | 34.9 | 24.7 | max_live_nonzeros |
| `R_F=6 R_P=2` | slice | 112 | 112 | 4 | 3 | 5 696 | 25 561 | 1 818 297 | 29.3 | 27.6 | max_live_nonzeros |
| `R_F=6 R_P=4` | as generated | 114 | 102 | 5 | 4 | 1 790 | 34 639 | 2 527 348 | 40.7 | 31.7 | max_live_nonzeros |
| `R_F=6 R_P=4` | slice | 114 | 114 | 4 | 3 | 5 696 | 28 904 | 2 178 049 | 35.1 | 29.0 | max_live_nonzeros |

**How to read the two matrix columns and the entry count.** They are the largest matrix F4
*completed*. The batch that crossed a bound is not recorded, because the check fires during its
construction and the statistics are written per completed batch — so the crossing figure lives in
the record's `limit.detail` instead, and it is always just over the bound: 20,000,210 to
20,000,793 entries on the rows that died on entries. A reader comparing "peak entries" against
"the limit of 20,000,000" and finding the first smaller is seeing that, not an inconsistency.

The wall clock never bound: the slowest row is 72.9 s against a 120-second backstop, so **every
stop in this table is a reproducible resource bound** rather than a fact about this machine.

## 3. What it says

### 3.1 One of eighteen completes, and it is the smallest slice

`R_F = 2, R_P = 0` with twelve of fourteen free inputs fixed — 46 variables, 46 equations —
produces a **complete grevlex Gröbner basis in 30.3 s** at degree 4, from 5 815 reduced pairs and
545 appended elements, with a largest matrix of 20 866 × 17 424 and a 102.8 MB peak. That is the
first completed basis for a system at the official state width in this project.

It is not a witness, and §4 is about what happens next. It is also the *easiest* row by a wide
margin: no other slice completes, and no unspecialized row does.

### 3.2 The binding resource changes at this width — entries, not columns

On the small instances M21 and M22 measured, the bound that bound was always the **column** budget:
the `t = 3` nine-variable instance crossed 60 000 columns at degree 11. Here, fourteen of eighteen
rows cross the **live-entry** cap instead, at degree 4 or 5, and the four that do cross on columns
do so at degree 6 with 50 000–82 000 columns already completed.

So the full-width obstacle is not "the monomial support grows past what fits" but "the matrices
densify before the degree gets anywhere". A strategy aimed at the column count — a better
monomial order, a narrower support — is aimed at the bound that no longer binds first.

### 3.3 The degree reached *falls* as the instance widens

| `R_F` | highest selection degree, as generated |
|---|---|
| 2 | 6 |
| 4 | 5 (6 at `R_P = 0`) |
| 6 | 5 |

and every slice at `R_F ≥ 4` stops at degree 4. A wider system reaches a *lower* degree before it
exhausts the budget, because each degree's matrices are bigger. This is the concrete reason the
scoreboard refuses to rank unfinished runs against each other: on this ladder a higher degree
reached is evidence of a *smaller* problem, not of more progress.

### 3.4 Specialization is not one mechanism

M22-E measured that pinning one free input on the `t = 3` instance took the computation from degree
11 to degree 5 and from 155 MB to 0.2 MB — a decisive win. At full width:

| row | as generated | slice | what the slice changed |
|---|---|---|---|
| `R_F=2 R_P=0` | stops, degree 6 | **completes**, degree 4 | decisive |
| `R_F=2 R_P=4` | stops at 72.9 s, 311.9 MB | stops at 9.7 s, 24.8 MB | 7.5x cheaper, same verdict |
| `R_F=4 R_P=2` | stops at 14.6 s | stops at 21.1 s | **worse** |
| `R_F=6 R_P=4` | stops at 31.7 s | stops at 29.0 s | no change |

Fixing twelve coordinates removes twelve variables' worth of freedom and adds twelve equations, and
on the wide rows that trade is close to neutral: both sides die on entries at degree 4 within 20%
of each other, which is inside the band this project declines to read. "Specialize to make it
feasible" is a statement about a particular system, and at `R_F ≥ 4` and `t = 16` it is not true.

### 3.5 A verified witness at the official state width

The row that completes carries on through the conversion and the search, and three of eight
precommitted slices produce a point that the **permutation** accepts.

| seed | outcome | F4 | conversion | univariate | verify | `D` |
|---|---|---:|---:|---:|---:|---:|
| 0 | empty slice | 30 767 | 129.9 | 17.4 | — | 81 |
| 1 | **verified witness** | 30 581 | 114.7 | 21.0 | 0.004 | 81 |
| 2 | **verified witness** | 29 913 | 121.9 | 21.0 | 0.004 | 81 |
| 3 | empty slice | 30 015 | 121.0 | 16.1 | — | 81 |
| 4 | empty slice | 30 109 | 115.0 | 16.7 | — | 81 |
| 5 | empty slice | 30 388 | 124.0 | 17.7 | — | 81 |
| 6 | **verified witness** | 29 965 | 121.9 | 21.3 | 0.004 | 81 |
| 7 | empty slice | 29 857 | 122.7 | 17.1 | — | 81 |

ms. The witness is a 14-word input whose first two words are the challenge's own
`0xc09de4, 0xee6282` and for which `permutation_plus_linear` returns zero in the first two output
words, exactly, over KoalaBear at `t = 16`. It is checked by running the permutation, not by
re-evaluating the system, so no bug in the generator, the specialization or the solver can make it
pass.

**What it is.** The first verified CICO witness this project has produced at the **official state
width, with the official constants and the exact objective**. `R_F = 2, R_P = 0` against the
official `R_F = 6, R_P ∈ {6, 8, 10}`, so the registry records it as a witness for a faithful
reduction and names what it reduced from. It is not evidence about any official target.

**What the campaign costs.** 3 witnesses in 8 slices, 243.5 s in total: **81.2 s of expected work
per witness, including the slices that found nothing**, with a 95% Wilson interval on the success
rate of 13.7% to 69.4%. Quoting the 30.6 s of the successful slice as "the cost of a solution"
would be wrong by 2.7x, and the interval is what eight trials actually support.

**Where the cost is.** F4 is 99.5% of every run; the conversion is 0.12 s and the univariate search
0.02 s at `D = 81`. That answers the stage question for this instance unambiguously, and it is the
opposite of what M20 measured over a 254-bit field, where root-finding dominated. The quotient
dimension is also exactly the Bézout prediction — the two output constraints have degree `3^2 = 9`
in the two surviving unknowns, and `9 × 9 = 81` — which is a check on the formulation rather than a
coincidence, and it is the number that will decide how far this route can go: `D = 9^rounds`.

### 3.6 What none of this says

The official targets are `R_F = 6` with `R_P ∈ {6, 8, 10}` — 116 to 120 variables, and all three
publicly solved in 2026 by attacks that are not this one. The furthest row here is 114 variables and
it stops at degree 4 having built nothing larger than a 28 904-column matrix. **No row in this
table is evidence about an official target**, and the registry records every one of them as a
faithful reduction naming what it reduced from, so a row cannot be quoted without it.

## 4. Four formulations of one problem (M23-C)

The row that completes is also the only one on which formulations can be *compared* rather than
guessed at: all four presentations below finish, all four recover a verified witness, and all four
report `D = 81`. Same ideal, four ways of writing it; the quotient dimension is an invariant, so
four agreeing values of `D` plus four witnesses that pass the permutation check is the evidence
that nothing here changed the problem.

`poseidon31-cico-t16-rf2-rp0`, slice at seed 1, 46 variables before projection:

| formulation | vars | eqs | max rows | max cols | peak entries | peak MB | generation | F4 | total |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| **as generated** | 46 | 46 | 20 866 | 17 424 | 6 414 960 | 102.8 | 0.06 | **29.9** | **30.1** |
| last-round-first | 46 | 46 | 48 916 | 43 866 | 15 876 487 | 254.4 | 0.06 | 71.5 | 71.7 |
| free-inputs-last | 46 | 46 | 25 264 | 21 057 | 10 082 642 | 161.5 | 0.06 | 49.4 | 49.6 |
| affine-projected | **32** | 32 | 19 278 | 15 836 | 5 966 838 | **95.6** | 19.95 | 25.7 | 45.7 |

seconds. Every row is degree 4 and `D = 81`.

### 4.1 M22-E's winning variable order is 2.4x *worse* here

`last-round-first` was 1.67x and 1.61x **faster** than the generated layout on the `t = 2`
surrogates, with up to 2.1x less peak memory, and it was the only layout that won on both. At
`t = 16` it is **0.42x** — 71.5 s against 29.9 s — with 2.5x the peak memory and 2.5x the matrix
rows. `free-inputs-last`, the layout that lost at `t = 2`, is also worse here but less so.

That reversal is the most useful thing in this document. The mechanism M22-E identified still
holds — reversing the round blocks puts the variables the output constraint touches first, so the
elimination works inwards from the constrained end — but at `t = 16` the first round introduces
sixteen variables rather than two, and starting from the constrained end no longer front-loads a
*small* block. An ordering tuned on a two-word state is not evidence about a sixteen-word state,
and here it is actively misleading.

### 4.2 Affine projection makes F4 cheaper and the run slower

Eliminating all fourteen affine generators — the twelve pinning equations and the two output
constraints — and projecting out of the ring gives a 32-variable system whose F4 is **1.16x faster**
and 7% smaller at the peak. Then the sweep that produces it costs **19.95 s**, against the 4.2 s it
saves, so the run as a whole is 1.5x slower.

Both halves of that are worth having. The projected system is the smallest and cheapest of the four
to *solve*, which is what a reformulation is supposed to deliver; and `eliminate_affine` is a
quadratic-ish substitution sweep over 46 variables and 46 generators whose cost nobody had measured
before, because at `t = 2` it was microseconds. The next move is a cheaper sweep, not a different
transformation — and that is a concrete, measured target rather than a guess.

### 4.3 What the comparison is allowed to say

All four runs are of the same registered problem, so `Comparison::of` compares them; all four
produced a verified witness, so the runtimes are costs of the same thing and the comparison carries
no caveat. Every ratio above is outside the ±20% band this project declines to read — the smallest
is 1.5x — so each is a reading rather than noise. One instance at one width is still one instance:
what is established is that the `t = 2` ordering result does not transfer, not that any particular
layout is best at `t = 16`.

## 5. Reproducing

```sh
tools/scoreboard.sh row poseidon31-cico-t16-rf2-rp0            # one row
tools/scoreboard.sh row poseidon31-cico-t16-rf2-rp0 --slice 0  # its slice
ZEEBRA_WALL_SECONDS=120 tools/scoreboard.sh ladder --write     # all eighteen
ZEEBRA_WALL_SECONDS=180 tools/scoreboard.sh campaign poseidon31-cico-t16-rf2-rp0 --seeds 8 --write
ZEEBRA_WALL_SECONDS=300 tools/scoreboard.sh formulations poseidon31-cico-t16-rf2-rp0 --slice 1 --write
```

Each row runs in its own process. F4 has no cooperative time check, so the only way to stop one
that outlasts its supervisor is to leave its thread behind and exit — acceptable once per process
and not nine times in one. `research/scoreboard/runs/` holds a record per row with the stage
split, and `research/scoreboard/SCOREBOARD.md` is rendered from the accumulated history.
