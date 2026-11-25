# M4GB/M5GB reference comparison on dense overdetermined MQ (#1030)

**Status:** decided, **reject** (§8). On the held-out cells (m/n = 1.8, GF(31) and GF(65521),
bench host, pinned), M4GB is 16.0× and 5.8× faster than Zeebra's best qualified configuration,
well past the 1.5× gate. But pinned grobx is faster than M4GB on every cell, at 0.59× and 0.19×
M4GB's wall. The hypothesis needs M4GB to beat both, so it is disproved. Every M4GB and grobx
basis agrees with Zeebra's coefficient for coefficient. The macOS development figures (§5) stand
as development only. M5GB's only public code was run locally under an owner exception and cannot
run this cohort at all: it is a GF(2) implementation (§3.2).

**Measured at:** `52268421` (planted rows, tag `measured/1030-m4gb-dev-planted`) and `4d1ec9b7`
(unplanted rows, tag `measured/1030-m4gb-dev-unplanted`),
`examples/m4gb_comparison.rs` in release, macOS arm64 (14 cores), unpinned, no RSS figure, one
worker, 2026-11-24. **§8 (the decision):** `41a36e93` (tag `measured/1030-m4gb-held-out`), AMD
Threadripper PRO 5995WX, Linux x86_64, rustc 1.99.1, CCDs 1–2 reserved, each child on CPU 8, with
peak RSS. Evidence: [`research/1030-m4gb-reference/`](../../research/1030-m4gb-reference/README.md).

Parent: #1028 (candidate A). Census this reconciles with: #1031. Gated prototype: #1032.
Pre-declared cohort and rule: [#1030 comment](https://github.com/mfaulk/zeebra/issues/1030#issuecomment-7145421369).

## 1. Contract

Both engines compute the complete reduced Gröbner basis in grevlex over a prime field, from the same
input text in the same variable order. M4GB's basis is verified against Zeebra's, monic and
coefficient for coefficient (`src/grobner/external/m4gb.rs`). Verification is timed separately and
is not in M4GB's figure. Zeebra's figure includes its final interreduction. M4GB's figure includes
writing its basis, because the basis is its output.

## 2. Four mechanisms, kept distinct

1. **Caching a row as constructed.** This is Zeebra's `ReducerCache` (`src/grobner/f4/symbolic.rs`).
   It caches shifted terms, not reduced rows.
2. **F4 `Simplify` (Faugère 1999).** It replaces a reducer `t·f` with a multiple of a row already
   reduced in an earlier matrix. #809 deferred it, and #1031 measured that a never-evicting store of
   tail-reduced multiples avoids at most 2.4% of Zeebra's elimination products on these rows.
3. **M4GB's reduction organization.** M4GB keeps only tail-reduced polynomials: every term except
   the leading one is irreducible. It stores tail-reduced multiples of basis elements and reduces
   over dense coefficient vectors indexed by the irreducible monomials. Critical pairs are taken in
   batches of at most 512 (`MAXSELECTION` at the pin). The paper's claim is that this processes fewer
   pairs than F4 and flattens the degree-of-regularity staircase, not that it reuses F4's rows.
4. **M5GB's signature-aware reductors** (Hauke et al., arXiv:2208.00844). M4GB's tail-reduced store
   under F5-style signature criteria, which target the zero rows #809 named as the dominant cost.

## 3. The references

### 3.1 M4GB

- **Source and licence.** `cr-marcstevens/m4gb` at `01860a52dacb111d6e1533bc7547b2dc8f034073`. It
  is GPL-3.0-or-later (`COPYRIGHT.txt`, `src/config.hpp:9-12`, `LICENSE.txt` verbatim). It runs as
  a subprocess only; see the table in
  [`external-provenance-policy.md`](external-provenance-policy.md).
- **Build.** `tools/external/provision-m4gb.sh "<n…>" "<p…>"`. Upstream uses autotools, and neither
  host has them. Its only generated header, `lib/config.h`, defines nothing the sources read, so the
  provisioner compiles `src/m4gb.cpp` directly at `-O3`, with `-march=x86-64-v3` on x86_64 (never
  upstream's `-march=native`). Each binary carries a `.build` sidecar naming the revision,
  compiler and flags, and the adapter refuses any other revision.
- **Shape.** `MAXVARS` and `FIELDSIZE` are compile-time constants, so there is one binary per
  `(n, p)`.
- **Capability.** Grevlex only. The prime field keeps log tables of `2p` entries, so the adapter
  admits odd primes up to 65,521. **GF(2³¹−1) and every 64-bit prime are out of reach.** GF(2) is
  refused because upstream adds the field equations, which changes the ideal.
- **Threads.** The default is every hardware thread. The adapter always passes `--nrthreads`.
  Upstream marks its threading "NOT FULLY IMPLEMENTED".
- **Unit ideal.** M4GB detects `I = (1)` by throwing `contradiction: I=(1)` and exiting 1. The
  adapter reads that as the basis `{1}` and verifies it. On two small hand-made unit ideals in two
  and three variables, the pinned revision instead stopped making progress at `lcmdegree=3` and never
  exited. The log stopped growing, so this is a livelock, not slow progress. None of the dense
  unplanted rows did this (§5.2). A wall stop on an inconsistent row should still be read as this
  defect.
- **First exec.** On macOS the first exec of a new binary costs about 0.12 s, against 0.00 s on
  later execs. `m4gb-cohort.py` execs each binary once before measuring.

### 3.2 M5GB

The only public implementation found is `manschga/M5GB` at `2d063f74`. It has **no licence grant**:
no licence file, and no header in any of its 12 files. It is also a standalone program, not the
Mathic-based proof of concept the paper describes.

**Owner exception (2026-11-25).** The owner allowed it to be built and run locally, with nothing
vendored or committed. It was fetched to a scratch directory, read in full, and driven by a
throwaway `main` that builds the input polynomials directly (upstream `main` hardcodes n = 20,
p = 2 and an input file that is not in the repository, and its parser reads one character per
coefficient). Each run was checked against a planted dense quadratic system with m = 2n, whose
reduced basis is {x_i − a_i}.

| Build | GF(2) | GF(31) |
|---|---|---|
| upstream, unmodified | correct basis (n = 6 and n = 12) | segmentation fault (n = 6 and n = 8) |
| field equations removed (local patch) | segmentation fault | terminates with a wrong basis: at n = 8, 21 polynomials of degree 2–3, none vanishing at the planted point |

The reasons are structural, so neither is a driver defect:

- **Field equations are built in.** `Initialize` always appends x_i^p − x_i, and the rest of the
  code assumes they are the first n generators. Monomials are indexed through a dense table of every
  term up to a fixed degree, so x^31 at n = 16 needs about 1.5 × 10¹² entries. The GF(31) crash is that.
- **Arithmetic is written for p = 2.** The source says so (`case p=2 should work`, `need to check
  for monomials with p != 2`). Coefficients are 32-bit `int` multiplied as `(a*b) % p`, which
  overflows for p > 46 341, so GF(65521) could not be correct either. Inverses are found by linear
  search over F_p.

So this code is a Boolean-ring (Fukuoka Type IV style) solver, and the #1030 cohort (GF(31),
GF(65521)) is outside what it can compute. **M5GB is not an arm of this comparison**, and that
needs no further licence decision. What would change it is the paper's Mathic-based code, which
is not public. No timing is reported, because no run was on a cohort cell.

## 4. Cohort

Rows come from `corpus::dense_mq_shaped`: #945's dense family, generalized to any `m` and a
per-monomial keep rate. At `m = 2n` and full density it is #945's row exactly, digests pinned.
Rows that differ only in `m` share their first generators.

- **Development (this note):**
  - fields GF(31) and GF(32003);
  - `m/n` ∈ {1.5, 2, 3};
  - density 1000 and 500 per mille;
  - seeds 1 and 2;
  - n ∈ {12, 14, 16}, except n = 16 at `m/n` = 1.5;
  - three repetitions, engine order alternating.
- **n = 16 at `m/n` = 1.5 is absent** because Zeebra needs 41.1 M live entries there, over its
  32 M default budget, so M4GB's basis could not be verified.
- **Held out until the decision:** `m/n` = 1.8 and GF(65521). M4GB covers only 16-bit primes, so
  holding out a field *width* would leave one development field. `m4gb-cohort.py` refuses both.

## 5. Development results

### 5.1 Planted

**Correctness.** Each cell's value is the median process wall over three repetitions. The table
gives the median over that shape's four cells (2 seeds × 2 densities), with the range. All 192 M4GB
runs verified. Zeebra is the shipping `F4Options::default()` at one worker, timed in-process. M4GB
is timed as a process, including startup and file I/O, which favours Zeebra.

| p | n | m (m/n) | Zeebra s | M4GB s | M4GB speedup (range) | faster arm ≥ 0.3 s |
|---|---|---|---|---|---|---|
| 31 | 12 | 18 (1.5) | 0.833 | 0.087 | 9.6x (8.5–9.7) | no |
| 31 | 12 | 24 (2.0) | 0.096 | 0.025 | 3.8x (2.7–3.8) | no |
| 31 | 12 | 36 (3.0) | 0.008 | 0.013 | 0.6x (0.3–0.7) | no |
| 31 | 14 | 21 (1.5) | 9.968 | 0.392 | 25.3x (24.8–26.3) | **yes** |
| 31 | 14 | 28 (2.0) | 0.501 | 0.068 | 7.3x (6.3–8.9) | no |
| 31 | 14 | 42 (3.0) | 0.036 | 0.024 | 1.5x (1.4–1.7) | no |
| 31 | 16 | 32 (2.0) | 14.637 | 0.506 | 28.7x (28.2–29.1) | **yes** |
| 31 | 16 | 48 (3.0) | 0.867 | 0.060 | 14.5x (13.9–17.5) | no |
| 32003 | 12 | 18 (1.5) | 0.903 | 0.212 | 4.3x (4.0–4.3) | no |
| 32003 | 12 | 24 (2.0) | 0.103 | 0.049 | 2.1x (1.7–2.1) | no |
| 32003 | 12 | 36 (3.0) | 0.009 | 0.025 | 0.3x (0.3–0.4) | no |
| 32003 | 14 | 21 (1.5) | 10.709 | 1.035 | 10.3x (9.8–10.6) | **yes** |
| 32003 | 14 | 28 (2.0) | 0.521 | 0.153 | 3.4x (3.3–3.8) | no |
| 32003 | 14 | 42 (3.0) | 0.036 | 0.030 | 1.2x (1.0–1.5) | no |
| 32003 | 16 | 32 (2.0) | 15.437 | 1.302 | 11.9x (11.7–12.0) | **yes** |
| 32003 | 16 | 48 (3.0) | 0.918 | 0.098 | 9.3x (9.3–9.5) | no |

What the table shows:

- **Above the floor, M4GB is 10–29× faster** on all four shapes, at both fields, at both densities.
  The margin is about 2.4× larger at GF(31) than at GF(32003), and the difference is M4GB's: its
  time rises about 2.6× from GF(31) to GF(32003) while Zeebra's barely moves. One candidate cause,
  not isolated here, is that upstream uses table arithmetic at small fields (multiply tables for
  `p ≤ 256`, add-multiply tables for `p ≤ 64`).
- **The margin grows with n and shrinks as `m/n` grows.** At `m/n` = 3, rows are 8–36 ms for
  Zeebra and M4GB's startup floor decides them. That is why the 0.3–0.6× entries at n = 12 are not
  a loss of the algorithm. At n = 16 and `m/n` = 3, M4GB is still 9–15× ahead, below the floor.
- **Density 500 behaves like density 1000.** At half density these quadratics are still dense in
  the sense that matters.

### 5.2 Unplanted

There is one repetition per cell, at n = 12, seed 1, full density, with a 20 s cap. Every unplanted
row is the unit ideal.

| p | m (m/n) | Zeebra s | M4GB s | M4GB speedup | M4GB status |
|---|---|---|---|---|---|
| 31 | 18 (1.5) | 0.805 | 0.087 | 9.2x | verified `{1}` |
| 31 | 24 (2.0) | 0.095 | 0.025 | 3.8x | verified `{1}` |
| 31 | 36 (3.0) | 0.008 | 0.013 | 0.6x | verified `{1}` |
| 32003 | 18 (1.5) | 0.871 | 0.200 | 4.4x | verified `{1}` |
| 32003 | 24 (2.0) | 0.100 | 0.050 | 2.0x | verified `{1}` |
| 32003 | 36 (3.0) | 0.008 | 0.024 | 0.3x | verified `{1}` |

All six rows were reported as `contradiction: I=(1)` and verified. No row stopped at the cap. The
margins match the planted rows of the same shape, all below the floor, so the unplanted cohort needs
n ≥ 14 on the bench host like the planted one.

## 6. Reconciliation with #809 and #1031

**#809's defer stands for `Simplify` inside conventional F4.** Nothing here measures that mechanism.
#1031 measured on Zeebra's own computation that a store of tail-reduced multiples saves at most 2.4%
of elimination products on dense overdetermined rows, and at most 1.4% once storing is charged. So
**the 10–29× above is not a reuse saving inside Zeebra's F4.** It has to come from what differs:

- M4GB's organization (mechanism 3): fewer pairs processed, and dense vectors over irreducible
  monomials, against F4's sparse Macaulay rows;
- Zeebra's own dense small-prime cost (#945). PR #1095's opt-in lane kernel gives about 3×
  complete-task on GF(31), but on the signature engine only.

Which share is which is the open question. A 3× from #945 would leave about 10× at GF(31) and 4× at
GF(32003) on these shapes, and both are still above the 1.5× gate. A route recommendation for #1032
waits until the gap is attributed. That needs the comparison against Zeebra's best qualified
configuration, and M4GB's per-iteration counters: basis size, pairs, and matrix rows and columns,
which its log prints at `--loglevel 3`.

## 7. What is open

1. **The pinned re-run of the development cells.** It was not done: the held-out run took 3.1 h of
   reserved CCDs at 3 repetitions, and another gate was waiting for them. The decision does not
   depend on it.
2. **#945's lane** (`SigF4Options::small_prime_lane`) as a Zeebra arm. It is reachable only through
   `sig_f4`, not through `F4Options` or the external-contract adapter. It cannot change the
   decision: the decision fails against grobx, not against Zeebra. Against Zeebra the margins are
   5.8× and 16×. A 3× lane would leave 1.9× and 5.3×, still past the gate.
3. Counters from M4GB's log (`--loglevel 3`), for the attribution in §6.

M5GB: run under an owner exception and found unable to compute over GF(31) or GF(65521) (§3.2).
The paper's Mathic-based code is the only route to an M5GB arm.

## 8. Deciding run (bench host)

The arms, placement and decision procedure were posted on #1030 before any held-out cell was read
([comment](https://github.com/mfaulk/zeebra/issues/1030#issuecomment-7150169799)). The cut from 5
repetitions to 3 was posted before the medians were read
([comment](https://github.com/mfaulk/zeebra/issues/1030#issuecomment-7150986750)). That comment
also discloses a smoke row at m/n = 1.8 on seed 9, outside the cohort.

- **Arms.** `zeebra` is `F4Options::default()`. `zeebra-adaptive` is `GradedEngine::Adaptive`,
  `f4_signature`'s pre-solve dispatch. `m4gb` is `01860a52`, built `-march=x86-64-v3`.
  `grobx` is the pinned driver `8005a2a1` in raw mode, built x86-64-v3 with fat LTO. Every M4GB
  and grobx basis is re-solved by Zeebra outside the timed region and compared coefficient for
  coefficient.
- **"Zeebra" is the faster Zeebra arm per cell.** That was `zeebra-adaptive` in all 32 cells,
  2.2–3.5× faster than the shipping default at n = 16.
- **Cells.** m/n = 1.8, n ∈ {14, 16}, GF(31) and GF(65521), densities 1000 and 500, seeds 1 and 2,
  planted and unplanted. Three repetitions, with engines rotated one place per repetition, each
  child `taskset` to CPU 8 on reserved CCDs 1–2.
- **The floor removes n = 14.** grobx takes 0.08–0.10 s there, under the 0.3 s floor on the faster
  arm. The decision therefore rests on the 4 n = 16 cells per field.
- **Every row answered and verified.** No M4GB row stopped at the cap, unplanted included.

Medians over the counted (n = 16) planted cells, with every cell's value in the range:

| field | best Zeebra s | M4GB s | grobx s | M4GB vs best Zeebra | M4GB vs grobx | peak RSS MiB: Zeebra adaptive / M4GB / grobx |
|---|---|---|---|---|---|---|
| GF(31) | 18.4–18.9 | 1.16–1.18 | 0.68–0.69 | **16.0×** (15.7–16.2) | **0.59×** (0.58–0.59) | 148–159 / 16–17 / 32–42 |
| GF(65521) | 20.8–20.9 | 3.59–3.68 | 0.67 | **5.8×** (5.7–5.8) | **0.19×** (0.18–0.19) | 152–164 / 23 / 33–42 |

Unplanted, reported and not decided: M4GB is 11.0× and 4.1× faster than the best Zeebra arm, and
grobx is again faster than M4GB (0.48× and 0.16× of M4GB's wall). The full table is in
[`bench-host/tables.md`](../../research/1030-m4gb-reference/bench-host/tables.md).

**Decision: reject.** The pre-declared rule needs M4GB to be at least 1.5× faster than both
comparators on both held-out fields. Against Zeebra it is, by 5.8–16×. Against grobx it is slower
on every cell, by 1.7× at GF(31) and 5.3× at GF(65521). The gap to grobx also *widens* with the
field width, as the Mac development cells suggested between GF(31) and GF(32003). This is
consistent with M4GB's log-table field arithmetic.

**For #1032:** **none** as a separate M4GB backend. The reference that Zeebra trails on this family
is grobx, which M33-G1 already attributes (symbolic preprocessing, bookkeeping and interreduction,
`docs/research/m33-grobx-attribution.md`). M4GB's 5.8–16× over Zeebra is real and is not a reuse
saving (§6, #1031). It is evidence for that attribution, not for M4GB's organization: grobx is an
F4 and beats M4GB without it.
