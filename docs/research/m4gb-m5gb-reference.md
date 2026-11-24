# M4GB/M5GB reference comparison on dense overdetermined MQ (#1030)

**Status:** in progress, no decision. M4GB is provisioned at a pinned commit and runs behind a
verified adapter. On the development cohort, every M4GB basis agrees with Zeebra's coefficient for
coefficient, and M4GB is 10–29× faster than Zeebra's shipping F4 on every cell above the 0.3 s floor
(§5). These figures come from an unpinned macOS session and do not decide anything. The deciding run
needs the bench host, a grobx arm and Zeebra's best qualified configuration (§7). M5GB has no
licence grant and was not run (§3.2).

**Measured at:** `52268421` (planted rows, tag `measured/1030-m4gb-dev-planted`) and `4d1ec9b7`
(unplanted rows, tag `measured/1030-m4gb-dev-unplanted`),
`examples/m4gb_comparison.rs` in release, macOS arm64 (14 cores), unpinned, no RSS figure, one
worker, 2026-11-24. Evidence: [`research/1030-m4gb-reference/`](../../research/1030-m4gb-reference/README.md).

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
no licence file, and no header in any of its 12 files. Under the policy that is the no-grant class,
so it was not built or run. It is also a standalone program, not the Mathic-based proof of concept
the paper describes. Running it, or obtaining the paper's code, is an owner decision.

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

On the bench host, at a frozen tag:

1. The pinned, interleaved run of the development cells at n ≥ 14, with process wall and RSS for
   both arms. Ratios must be recomputed there; the Mac figures are not transferable.
2. **A grobx arm.** The hypothesis is "faster than both". `tools/external/grobx-driver` is built for
   x86-64-v3 and does not run on this Mac.
3. **Zeebra's best qualified configuration** as its arm, not only `F4Options::default()`: the
   signature engine, and the #945 lane if PR #1095 merges.
4. Then the held-out run: `m/n` = 1.8 and GF(65521), under the rule posted on #1030.
5. Counters from M4GB's log, for the attribution in §6.

For the owner: M5GB has no licence grant (§3.2).
