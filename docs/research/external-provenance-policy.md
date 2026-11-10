# External provenance and licensing: what may be read, what may be reused, and how to cite it

Policy for #274, gating code-level reuse in #264–#273. Zeebra is MIT (`Cargo.toml:10`,
`LICENSE-MIT`), and the governing fact about epic #256 is that **almost every competing Gröbner
engine is GPL or LGPL**, so for most of the survey the only lawful product of a source reading is
understanding, not code.

Every licence below was verified from **that project's own licence file or source headers at a
pinned commit**, read in full rather than classified. Access date **2026-11-06** throughout; the
pinned SHA is in the table. Eighteen of the twenty-one entries' API-reported values were wrong,
imprecise, or absent, including two the reconnaissance in #274 itself got wrong.

**This is an engineering policy, not legal advice.** The author is not a lawyer. Where a licence
text is quoted it is quoted so that a human can read the same words; where the answer is genuinely
unclear it is marked **UNCLEAR** and listed in §12 rather than resolved by assertion. Nothing here
authorizes reuse: it authorizes *reading*, and it says what to do instead of reusing. Any case where
reuse is actually contemplated goes to human legal review first — §12 names the four.

---

## 1. Why the API field is not evidence

`gh api repos/OWNER/REPO --jq .license.spdx_id` returns the output of a *classifier*
(licensee/`licensed`), which matches a root licence file against known texts by similarity. Three
failure modes showed up here, all of them material:

1. **It reports one licence where a project grants a choice of two.** `arkworks-rs/algebra` came
   back `Apache-2.0`; its root `Cargo.toml:34` says `license = "MIT OR Apache-2.0"`. Same for
   Sagebrush. In both cases the *more permissive* option was the one the classifier dropped, so the
   error was conservative — but the opposite error is equally available, and zeebra already carries
   `ark-ff` as a dev-dependency (`Cargo.toml:52`), so its correct SPDX is zeebra's own compliance
   question and not only a survey detail.
2. **It cannot see "or later".** Nine entries were reported as a bare version where the grant is
   version-or-later. `GPL-2.0` and `GPL-2.0-or-later` are different licences with different
   compatibility behaviour; the distinction lives in the *grant sentence*, which is in the source
   headers or the README, not in the verbatim GPL text the classifier matched.
3. **`NOASSERTION` means "could not classify", not "unlicensed".** All four `NOASSERTION` cases
   turned out to have unambiguous grants. Three of them are `NOASSERTION` for the trivial reason
   that a sentence was prepended to the GPL text, which defeats the similarity match — BRiAl's
   `LICENSE:1-2` is two lines long and settles the question outright.

The method that works: find the licence file (root first, then subdirectories, then source
headers), read the *grant sentence*, then cross-check it against a second place in the same
repository. Where the two disagree, record both — §3 has three instances where they do.

---

## 2. The verified table

`SHA` is the default-branch tip read on 2026-11-06. `verified from` is where the grant sentence
actually is, which is only sometimes a root licence file.

| library | repo | SHA | licence, verified | verified from | class |
|---|---|---|---|---|---|
| Sagebrush | `sagemathinc/sagebrush` | `b960770f` | **MIT OR Apache-2.0**, at the licensee's option | `NOTICE.md:1-13`; `LICENSE-MIT`; `LICENSE-APACHE`; `engine/mpoly/Cargo.toml:5` | **reuse permitted** |
| Arkworks `algebra` | `arkworks-rs/algebra` | `722284bc` | **MIT OR Apache-2.0** | `Cargo.toml:34`; `README.md:76-83` | **reuse permitted** |
| msolve | `algebraic-solving/msolve` | `b364edcb` | **GPL-2.0-or-later** | `src/neogb/la_ff_32.c:1-14`; `COPYING` (GPL-2 verbatim) | algorithmic reference only |
| Groebner.jl | `sumiya11/Groebner.jl` | `751c90b0` | **GPL-2.0** (header says "GNU GPL v2", no "or later"); **adapted from msolve** | `src/Groebner.jl:1`, `:8-15`; `LICENSE` (GPL-2 verbatim) | algorithmic reference only |
| `gb` | `ederc/gb` | `002c79c0` | **GPL-2.0-or-later** | `src/f4.c:4-6`; `COPYING` (GPL-2 verbatim) | algorithmic reference only |
| GBLA | `ederc/gbla` | `2f8ebcf5` | **LGPL-2.1-or-later** | `src/elimination.c:3-7`; `COPYING` (LGPL-2.1 verbatim) | linking only |
| OpenF4 | `nauotit/openf4` | `7155c6ec` | **GPL-3.0-or-later** | `openf4/include/ideal.h:6-8`; `COPYING` (GPL-3 verbatim) | algorithmic reference only |
| CoCoALib | `cocoa-official/CoCoALib` | `fba1ece3` | **GPL-3.0-or-later** for `src/` and `include/`; GNU FDL for `doc/`; `examples/` **UNCLEAR** (§3.4) | `README.md:29-36`; `COPYRIGHT-full-text` (GPL-3 verbatim); `examples/ex-00-intro.C:1-3` | algorithmic reference only (`examples/`: see §12) |
| M4RI | `malb/m4ri` | `397a70fc` | **GPL-2.0-or-later** ("version 2 or higher") | `m4ri/brilliantrussian.c:8-9`; `COPYING` (GPL-2 verbatim) | algorithmic reference only |
| M4RIE | `malb/m4rie` | `78e88d13` | **GPL-2.0-or-later** ("version 2 or higher") | `src/ple.c:7-8`; `COPYING` (GPL-2 verbatim) | algorithmic reference only |
| Singular | `Singular/Singular` | `3f188e4e` | **GPL-2.0 *or* GPL-3.0, licensee's choice** — not "or later", and **no linking exception** (§3.1) | `COPYING:11-13`; `libpolys/COPYING`; `factory/COPYING:20-28`; `omalloc/COPYING:14-22`; `GPL2`; `GPL3` | algorithmic reference only |
| BRiAl | `BRiAl/BRiAl` | `df5b4fd3` | **GPL-2.0-or-later** | `LICENSE:1-2` | algorithmic reference only |
| Macaulay2 | `Macaulay2/M2` | `a5ff8d7e` | **GPL-2.0-or-later** (source); binaries GPL-3.0 by LGPL-3 linking | `README.md:40-54`; `M2/Macaulay2/COPYING-GPL-2`, `COPYING-GPL-3` | algorithmic reference only |
| Giac | `geogebra/giac` | `19a710ae` | **GPL-3.0-or-later**, per-file; **no root licence file** | `src/giac/headers/cocoa.h:4-8` (135 files carry the grant) | algorithmic reference only |
| Sage | `sagemath/sage` | `36e49d91` | **GPL-3.0-only** for the distribution ("no other versions!"); **GPL-2.0-or-later** for original library code | `COPYING.txt:8-9`, `:17-21` | algorithmic reference only |
| Oscar.jl | `oscar-system/Oscar.jl` | `27be7deb` | **GPL-3.0-or-later** | `LICENSE.md:1`, `:10-13` | algorithmic reference only |
| MathicGB | `broune/mathicgb` | `c72c945b` | **GPL-2.0-or-later asserted in 118 source headers**; the `LICENSE.txt` they point at **does not exist** (§3.2) | `src/mathicgb/F4MatrixBuilder.cpp:1-2` | algorithmic reference only, with the §3.2 caveat |
| FLINT | `flintlib/flint` | `f5c2181a` | **LGPL-3.0-or-later** | `README.md:71-72`; `COPYING.LESSER` (LGPL-3 verbatim) | linking only |
| FFLAS-FFPACK | `linbox-team/fflas-ffpack` | `06aec3f8` | **LGPL-2.1-or-later** | `README.md:16`; `fflas-ffpack/ffpack/ffpack_ludivine.inl:10-12` | linking only |
| LinBox | `linbox-team/linbox` | `60d7d0bc` | **LGPL-2.1-or-later** | `linbox/algorithms/wiedemann.h:42-45` (`README.md` has **no** licence section) | linking only |
| Fukuoka MQ Challenge data | — (not a repository) | — | **"All Rights Reserved", no stated licence** | `README.md:122-124`, and `tools/fetch-mq-challenge.sh` (moved out in #668) exists so the files are fetched and never redistributed | **no grant** |

The fourth class is not empty, and its occupant is already handled correctly: the MQ Challenge
instances are fetched at the user's request by `tools/fetch-mq-challenge.sh` (moved out in #668) and the test that uses
them is `#[ignore]`d, so the repository distributes nothing it has no grant for. That is the
template for any future no-grant input.

### 2.1 "Linking only" is permitted by licence and excluded by convention

Four entries are LGPL, and the LGPL does permit a separately-licensed work to link a shared library.
Zeebra nevertheless links none of them and should not start: `Cargo.toml:36-44` has seven pure-Rust
dependencies and no `-sys` crate, `ark-ff` is a dev-dependency and a test oracle only
(`Cargo.toml:46-52`), and the repository's standing preference is to implement a primitive and
measure it rather than to take a dependency. So **"linking only" should be read as "not available
here"** unless a separate decision is taken to introduce C linkage, which would bring LGPL §6
relinking obligations, a build-system dependency, and the end of `cargo build` as the whole build.
Nothing in #264–#273 needs it.

---

## 3. What the verification changed

### 3.1 Singular has no linking exception, and is not "GPL-2.0-or-later"

#274's table guessed "GPL-2.0+ with exceptions in practice". Both halves are wrong.

`COPYING:11-13`:

> This program is free software; you can redistribute it and/or modify it under the terms of the
> GNU General Public License as published by the Free Software Foundation (version 2 **or version
> 3** of the License).

That is a choice between two specific versions, not "either version 2 or, at your option, any later
version". `libpolys/COPYING:14-16` repeats it verbatim for the polynomial layer, and
`factory/COPYING:20-22` for Factory. Of Singular's own trees, only `omalloc/COPYING:14-17` is
or-later ("either version 2 of the License, or (at your option) any later version").

The text that looks like an exception is not one. `factory/COPYING:22-28`:

> under the terms of the GNU General Public License as published by the Free Software Foundation (
> version 2 or version 3 of the License ); **with the following additional remarks:**
>
> This package is part of the software SINGULAR. The GPL is valid for this package, other packages
> may have other copyrights.

An "additional remark" that the GPL is valid and that *other* packages may differ is a scoping
note. It grants nothing and waives nothing; it is the opposite of a linking exception.
`omalloc/COPYING:17-22` carries the same remark. A full-text search of the repository at
`3f188e4e` for "exception" returns 15 files: `ppcc/gclib/*` (bundled Boehm GC, which does carry its
own permissive terms), `m4/ax_pthread.m4` (autoconf macro boilerplate), the verbatim `GPL2` and
`GPL3` texts, `doc/general.doc`, `Singular/LIB/surfex/doc/gpl.txt`, and `factory/configure.ac` —
where every hit is `-fno-exceptions` and C++ exception handling, not licensing. **No linking
exception applies to `kernel/`, `libpolys/` or `factory/`.**

Also worth recording, because the epic's Singular study cites file and line throughout: Singular's
engine sources carry **no per-file licence header at all**. `kernel/GBEngine/kstd1.cc:1-3` and
`kernel/GBEngine/khstd.cc:1-3` are a four-line banner and an `ABSTRACT:` line. The root `COPYING` is
the only grant, which is one more reason to pin it by SHA rather than describe it.

Consequence: nothing changes for #256. Singular was already reference-only and remains so, and
`src/grobner/differential/singular.rs` is a subprocess adapter, which is the one shape that is
unaffected by any of this (§7).

### 3.2 MathicGB does have a licence — it is the licence *file* that is missing

#274 recorded "no licence file → nothing; absence of a licence is absence of a grant". The first
clause is right and the conclusion is wrong. `broune/mathicgb` at `c72c945b` has **no file matching
`licen|copying|copyright|gpl|notice|legal` anywhere in the tree** (recursive tree listing, 0 hits),
and `README.md` says nothing about licensing. But every source file states the grant in its header.
`src/mathicgb/F4MatrixBuilder.cpp:1-2`:

> // MathicGB copyright 2012 all rights reserved. MathicGB comes with ABSOLUTELY
> // NO WARRANTY and is licensed as **GPL v2.0 or later** - see LICENSE.txt.

118 files in the repository carry that sentence; `LICENSE.txt` matches 0. So MathicGB is
**GPL-2.0-or-later by the same mechanism Giac is** (per-file headers, no root file), and it moves
from the "no grant" class to "algorithmic reference only" — which is, practically, no change at all,
since both classes forbid reuse in an MIT crate. The caveat is for a redistributor rather than for
us: GPL-2.0 §1 requires a copy of the licence to accompany the code, and the copy the headers point
to is not there, so anyone redistributing MathicGB would have to supply the GPL-2 text themselves.
Zeebra redistributes nothing, so this costs us nothing.

The genuine lesson is the opposite of the one #274 drew: **the absence of a root licence file is
not the absence of a grant, and the presence of one is not the whole grant.** Fifteen of the
twenty-one entries required a source header or a README line to pin the version, and three
(MathicGB, Giac, LinBox) had the grant *only* there.

MathicGB is also the cleanest illustration of §6: its `README.md` names
*Practical Gröbner Basis Computation* (Roune and Stillman, ISSAC 2012, `arXiv:1206.6940`) as the
description of its algorithms. The published paper is available on the same terms to everyone; the
GPL source is not. Read the paper.

### 3.3 Groebner.jl declares itself a derivative of msolve

`src/Groebner.jl:1` is `# This file is a part of Groebner.jl. License is GNU GPL v2.`, and
`:8-15` is a self-declared provenance statement:

> Parts of Groebner were adapted from msolve: https://github.com/algebraic-solving/msolve
> msolve is distributed under GNU GPL v2+ […]
> More precisely, the F4 implementation in Groebner adapts monomial hashtable implementation and
> routines for critical pair handling, symbolic preprocessing, and linear algebra from msolve.

Three things follow. First, the chain is internally consistent: GPL-2.0-or-later code may be
redistributed under GPL-2.0, which is what Groebner.jl's header elects. Second, **#265 and #264 are
reading the same code twice** for the hashtable, pair handling, symbolic preprocessing and linear
algebra; the Julia version is a port, so an agreement between the two notes is not corroboration.
Third, and this is the useful part: Groebner.jl is a worked example of what a licence-compliant
adaptation looks like — a named upstream, a named licence, an enumerated list of what was taken, in
the first fifteen lines of the entry point. Zeebra cannot *do* that for GPL upstreams, because the
result would be GPL. It is exactly what zeebra would have to do for Sagebrush (§8).

### 3.4 CoCoALib's README and its example headers do not say the same thing

`README.md:35-36`:

> Source code files under `examples/` are released into the public domain (licence: Creative
> Commons CC0).

`examples/ex-00-intro.C:1-3`:

> // Copyright (c) 2022  John Abbott,  Anna M. Bigatti
> // This file is part of the CoCoALib suite of examples.
> // You are free to use any part of this example in your own programs.

`examples/CopyInfo.C:1-7` is the same pattern. A retained copyright notice plus a one-sentence
permission is **not** a CC0 dedication: CC0 waives the copyright, the sentence does not, and the
sentence says nothing about redistribution, modification, sublicensing or warranty. The README also
points at a file named `COPYING-GPLv3` for the GPL text, and the file at the root is named
`COPYRIGHT-full-text`, so the README is demonstrably not maintained against the tree.

**UNCLEAR, and in §12.** The practical answer is easy — CoCoALib's examples are not needed by
#267, and reading them is unrestricted — but if anyone ever wants to lift one, it is a legal
question and not an engineering one.

### 3.5 Smaller corrections, recorded because a table that only reports hits is not a verification

- **`gb`'s own headers name the wrong project.** `src/f4.c:4-13` reads "**gbla** is free software
  … along with **gbla**", in a file that is part of `gb`. The grant is unambiguous (GPL, version 2
  or later) but the subject is a copy-paste artefact from GBLA. `gb` also vendors
  `src/gbla-elimination.c` and `src/gbla-matrix.c`, i.e. LGPL-2.1-or-later code redistributed
  under GPL-2.0-or-later, which the LGPL permits.
- **M4RIE's header misnames the licence.** `src/ple.c:7` says "the GNU General Public License
  (**GEL**) version 2 or higher". The intent is not in doubt; the string is wrong.
- **Sage is two licences, not one.** `COPYING.txt:8-9` puts the *distribution* under
  "the General Public License, version 3 (no other versions!)", while `:17-21` puts *original Sage
  library code* under GPL "either version 2 of the License, or (at your option) any later version".
  Which applies depends on what is being read, and `COPYING.txt` then enumerates per-component
  licences for ~200 bundled packages.
- **Macaulay2's source and its binaries differ.** `README.md:40-43` is GPL-2.0-or-later;
  `README.md:53-54` records that "Macaulay2 binaries are licensed under GPL-3.0 due to linking with
  LGPL-3.0 libraries (FLINT, MPFR)". Only the source statement is relevant to a reading.
- **LinBox has no licence section in its README** and no grant sentence outside its source
  headers, which is why its API classification came from `COPYING`/`COPYING.LESSER` alone. The
  grant is in the `========LICENCE========` block of every file, e.g.
  `linbox/algorithms/wiedemann.h:42-45`.
- **Sagebrush ships more than two licences.** The root has `LICENSE-MIT`, `LICENSE-APACHE`,
  `LICENSE-Artistic-2.0.txt`, a 45 KB `NOTICE.md`, and a `LICENSES/` directory with nine further
  texts (0BSD, BSD-2/3-Clause, BSL-1.0, ISC, MPL-2.0, OFL-1.1, Unicode-3.0, Zlib). **None of that
  touches `engine/`.** The Artistic-2.0 file covers one data table
  (`packages/cremona-small/py/_cremona_small.py`, from Cremona's `ecdata`, `NOTICE.md:768-772`), and
  the rest are vendored CPython modules, fonts and npm packages. Every `engine/` crate carries
  `license = "MIT OR Apache-2.0"` in its own manifest — `engine/mpoly/Cargo.toml:5`, which is where
  `f4.rs`, `f4q.rs` and `sigf4.rs` live, and `engine/flint/Cargo.toml:5`, whose own description
  records that "FLINT itself is LGPL-3.0-or-later and is used only as a reference".
  `NOTICE.md:16-19` states it directly: "Nothing in Sagebrush is derived from GPL software: PARI,
  Sage, Magma and FLINT are used only from the outside, as oracles in tests and as benchmarks."

---

## 4. The four classes, and what each permits

**Reuse permitted** — Sagebrush, Arkworks `algebra`. Code may be copied into zeebra, modified, and
distributed under zeebra's MIT, subject to §8's attribution requirements. Reuse is still a design
decision and not a default; the repository's standing preference is to implement rather than depend,
and a copied-in kernel acquires a maintenance obligation that a dependency at least makes explicit.

**Linking only** — GBLA, FLINT, FFLAS-FFPACK, LinBox. Dynamic linkage against an unmodified
library, with LGPL §6's obligations, and **no source copying of any size**. Excluded in practice by
§2.1.

**Algorithmic reference only** — every other engine in the table. Reading is unrestricted. What may
leave the reading is a *statement* — a measurement, a design constraint, an understanding of why a
structure is shaped the way it is — cited to file and line so a reader can check it. What may not
leave the reading is code, in any transcription (§5).

**No grant** — the Fukuoka MQ data, and anything else with no licence and no per-file grant. May be
read and used locally; may not be redistributed, vendored, or committed. Handled by fetch-on-demand
plus an `#[ignore]`d test (`README.md:122-130`).

---

## 5. The derivative-work boundary

The rule in one sentence: **what may cross from a GPL source into zeebra is a fact about the
algorithm; what may not cross is a decision the author of that source made.** A fact is checkable
against the mathematics and reproducible from a published description. A decision — this loop order,
this blocking factor, this struct layout, these five fields in this order, this variable naming —
is expression, and copying expression is copying code whether or not the language changed.

Translation is not laundering. A Rust rewrite of a C function, preserving its structure, is a
textbook derivative work: a translation of a novel is a derivative work of the novel. "I retyped it"
and "I had it retyped" are the same position.

The test to apply, in order:

1. **Is there an independent published description?** If yes, that is the source of record (§6).
   Implement from it, cite it, and do not open the GPL source while writing the implementation.
2. **Could you reconstruct this from your notes a week later without the file open?** If no, your
   notes are a transcription and the implementation will be a derivative.
3. **Would a diff against the original line up?** Same loop nest, same branch order, same
   intermediate variables, same field order — if a reviewer could align them, the answer is yes
   regardless of syntax.
4. **If the file disappeared, would the design survive?** A design justified by a measurement or a
   theorem survives. A design justified by "msolve does it this way" does not; it is a copy with a
   citation attached, and a citation is not a licence.

### 5.1 The hard case: `msolve/src/neogb/la_ff_32.c`

#264 reads msolve's per-bitwidth elimination kernels, and `src/neogb/la_ff_32.c` is the file
`docs/MILESTONE-F4-OPTIMIZATION.md` §6.2 makes most interesting, since elimination is 65%–88% of
every F4 run above a millisecond. The file is GPL-2.0-or-later (`:1-14`). An agent reads it and
writes a Rust kernel with the same loop structure, the same accumulator width, the same
delayed-reduction schedule and the same row-block shape.

**That is a derivative work and it may not be distributed under MIT.** It fails tests 2, 3 and 4
simultaneously. The agent did not infringe by reading; it infringed by producing. And the damage is
not confined to the kernel: a GPL-derived file in an MIT crate makes the crate's licence a
misstatement, which is worse than the file itself, and it is close to impossible to unwind once
other code depends on the kernel's interface.

**What to do instead, concretely.**

- The technique in that file is delayed modular reduction in a wide accumulator over a row block,
  which is Faugère–Lachartre's reduction structure (§6) composed with Montgomery or Barrett
  reduction (§6). All three have primary published descriptions. Implement from those.
- The *parameters* are measurable and need no source at all. How many 32-bit products accumulate in
  a `u64` before reduction is arithmetic: for a prime `p < 2^31`, `(p-1)^2 · k < 2^64` bounds `k`,
  and the bound is a theorem, not msolve's property. Block sizes come from #262's F4 matrix
  microbenchmark corpus and this machine's cache, not from msolve's constants — and
  `docs/research/f4-resource-scaling.md` and the `f4_profile` instrument already exist to measure
  them.
- What #264 should *record* is the shape of the claim and not the code: "msolve specializes the
  32-bit kernel separately from the 16- and 8-bit ones
  (`algebraic-solving/msolve@b364edcb:src/neogb/la_ff_32.c`, with `la_ff_16.c` and `la_ff_8.c`
  beside it), and has an AVX2/AVX512 path (`:24-25`); the question for #269 is whether per-field
  specialization pays *here*, measured against the existing generic kernel." That sentence is a
  finding. It is checkable, it survives the file disappearing, and it carries no code.
- Procedurally: **separate the reading from the writing.** Read, write the note, close the source,
  then implement from §6's references. If an implementation needs the GPL file open, the
  implementation is on the wrong side of the line and the right response is to go back to the paper.

### 5.2 The easy-looking case that is also over the line: M4RI's `brilliantrussian.c`

#272 targets bit-packed GF(2) linear algebra and M4RI's Method of Four Russians. M4RI is
GPL-2.0-or-later (`m4ri/brilliantrussian.c:8-9`). The temptation here is different from §5.1 and
worse, because M4RI's Gray-code table construction is *short* — a few dozen lines — and short code
feels like it cannot be a derivative.

Length is not the test; originality of expression is, and a carefully tuned table-construction loop
is expression. Transcribing forty lines is still transcription.

The right route is unusually clean, because this technique has two independent descriptions and a
published algorithm paper: Arlazarov–Dinic–Kronrod–Faradzhev (1970) for the method, and
Albrecht–Bard–Hart's *Algorithm 898* (ACM TOMS, 2010) for the matrix-multiplication arrangement
M4RI actually implements — published by M4RI's own authors, under ACM's terms rather than the GPL,
and written precisely so that the algorithm can be implemented by others. Implement from
*Algorithm 898*; cite M4RI only for measurements and for what #272 should compare against.

One more thing to carry out of this case: #272's decision gate is a comparison, and a comparison
needs M4RI to *run*, not to be copied. That is an adapter (§7), and an adapter has no licence
problem at all.

### 5.3 The case where reuse is permitted, and still needs a decision: Sagebrush's `sigf4.rs`

#266 reads Sagebrush for implementation cost, and `engine/mpoly/src/sigf4.rs` is the file #223
retracted a claim about. Sagebrush is `MIT OR Apache-2.0`
(`NOTICE.md:1-13`, `engine/mpoly/Cargo.toml:5`), so copying it is *lawful* — which makes this the
one case where the engineering question is live rather than foreclosed.

It is still a decision, and it should be made explicitly:

- **Attribution is mandatory and is not satisfied by a citation in a research note.** §8 has the
  mechanics. MIT requires the copyright notice and the permission notice to travel with the code;
  Apache-2.0 adds more. A `docs/research/` note is documentation, not a licence notice.
- **Taking the file sets zeebra's licence on it.** Under `MIT OR Apache-2.0` the recipient elects,
  so zeebra elects MIT and must carry SageMath, Inc.'s notice. Zeebra's own `LICENSE-MIT` does not
  cover someone else's copyright.
- **The maintenance cost is real.** A copied kernel diverges from upstream silently and has no
  version to bump. The repository's standing preference — implement, then measure the in-crate
  option before offering a dependency — applies with full force, and #223 already declined the
  signature-based direction on three independent legs. #266's remit is the *cost* question, not a
  reopening of the decline.
- So the likely right answer for `sigf4.rs` specifically is **read it, measure the implementation
  cost, and copy nothing** — not because copying is forbidden but because the feature was declined.
  Where a Sagebrush component *is* wanted, §8 is the checklist.

### 5.4 Reading Groebner.jl's hashtable is reading msolve's

#265 reads Groebner.jl's monomial encodings and hashtable. `src/Groebner.jl:8-15` says those
routines were adapted from msolve (§3.3). So the licence position is msolve's, the two readings are
not independent, and an agent who thinks "this is Julia, the C file is the thing I must not copy"
has it backwards: both are GPL and both are reference-only. The only thing Groebner.jl adds here is
a second vantage on the same design — useful for understanding, never for provenance.

---

## 6. Prefer the independent published description

**Where an algorithm has a paper, a textbook or a specification, that is the citation of record.**
Implement from it, cite it in the source comment and in the research note, and treat any
implementation you read as evidence about *engineering*, not as the description of the algorithm.
This is not new policy: `docs/MILESTONE-F4.md:711-712` already states it — "Published algorithm
descriptions are the primary references. Existing implementations are read for architecture and
performance strategy, under their own licenses; no code is copied." This document makes it binding
and names the references.

For the techniques #256 targets:

| technique | reference of record | where it bites |
|---|---|---|
| **F4** | Faugère, *A new efficient algorithm for computing Gröbner bases (F4)*, J. Pure Appl. Algebra 139 (1999) 61–88, doi:10.1016/S0022-4049(99)00005-5 | already the cited basis of `src/grobner/f4`; `docs/MILESTONE-F4.md:702` |
| **F5** | Faugère, *A new efficient algorithm for computing Gröbner bases without reduction to zero (F5)*, ISSAC 2002, 75–83 | #223 (declined); #266, read and cited in `docs/research/signature-based.md` §4.4 |
| **Faugère–Lachartre** | Faugère and Lachartre, *Parallel Gaussian elimination for Gröbner bases computations in finite fields*, PASCO 2010, 89–97 | #269, #264 — the structure §5.1's kernel is an instance of |
| **GBLA** (the FL implementation's own description) | Boyer, Eder, Faugère, Lachartre, Martani, *GBLA: Gröbner Basis Linear Algebra Package*, ISSAC 2016 | #267; prefer this over reading `ederc/gbla` |
| **FGLM** | Faugère, Gianni, Lazard, Mora, *Efficient computation of zero-dimensional Gröbner bases by change of ordering*, J. Symbolic Comput. 16 (1993) 329–344 | `src/grobner/fglm`, README §"Monomial-order conversion (FGLM)" |
| **Sparse-FGLM** | Faugère and Mou, *Sparse FGLM algorithms*, J. Symbolic Comput. 80 (2017) 538–569 (and the ISSAC 2011 predecessor) | #224, #264 |
| **Method of Four Russians** | Arlazarov, Dinic, Kronrod, Faradzhev (1970), Dokl. Akad. Nauk SSSR 194, 487–488; and **Albrecht, Bard, Hart, *Algorithm 898: Efficient multiplication of dense matrices over GF(2)*, ACM TOMS 37(1) (2010)** for the arrangement M4RI implements | #272 — §5.2 |
| **Montgomery reduction** | Montgomery, *Modular multiplication without trial division*, Math. Comp. 44 (1985) 519–521 | #270; `montgomery_256` already exists (`docs/MILESTONE-LARGE-PRIME-FIELDS.md:745`) |
| **Barrett reduction** | Barrett, CRYPTO '86, LNCS 263, 311–323 | #270, #272; already used on the `PCLMULQDQ` path (`docs/research/boolean-solving.md:57`) |
| **Brent–Kung modular composition** | Brent and Kung, *Fast algorithms for manipulating formal power series*, J. ACM 25 (1978) 581–595 | #271; `docs/research/fast-univariate.md:863-864`, `:1115` record that none exists yet |
| **Gebauer–Möller criteria** | Gebauer and Möller, *On an installation of Buchberger's algorithm*, J. Symbolic Comput. 6 (1988) 275–286 | already implemented; `docs/research/signature-based.md` §2, `docs/research/degree-profiles.md:192-193` |
| **msolve, as a system** | Berthomieu, Eder, Safey El Din, *msolve: A Library for Solving Polynomial Systems*, ISSAC 2021, 51–58 | #259, #264 — read this before `src/` |
| **Groebner.jl, as a system** | Demin and Gowda, `arXiv:2304.06935` | #260, #265; already cited at `docs/MILESTONE-F4.md:705-706` |
| **MathicGB, as a system** | Roune and Stillman, *Practical Gröbner Basis Computation*, ISSAC 2012, `arXiv:1206.6940` (named by `broune/mathicgb@c72c945b:README.md`) | #267 — §3.2 |
| **OpenF4's variant** | Joux and Vitse, *A variant of the F4 algorithm*, CT-RSA 2011 | #267 |

Two caveats on this table, because it would be dishonest to present it as uniformly verified. The
entries marked with a `docs/` or in-tree citation are corroborated against something this repository
has already read. The bibliographic details of the rest — page ranges in particular — are recorded
from the standard literature and **have not each been checked against the published article in this
pass**; an issue that relies on one should verify its own citation when it cites it, which is the
normal standard in `docs/research/` anyway (`docs/research/signature-based.md:206-207` is the model:
a citation chain where every link was actually read).

---

## 7. Adapter isolation

#259 and #260 build benchmark adapters for msolve, Groebner.jl and Sagebrush. **They must invoke
external programs as subprocesses and must never link them, vendor them, or acquire them as a Cargo
dependency.** This is the shape that makes a GPL comparand usable at all: running a program is not
distributing it, and a subprocess boundary creates no derivative work in either direction.

The precedent is in the tree and is the template. `src/grobner/differential/singular.rs` drives
Singular by generating a script and spawning the binary: `script()` at `:330` builds the whole
program as a string (`:336-367`), `run()` at `:388` spawns it with `Command::new(&self.binary)` at
`:398`, and the result is parsed from stdout. There is no FFI, no build script, no header, and no
link step. Singular's licence (§3.1) is therefore irrelevant to zeebra's, and the adapter is the
reason the epic can have an external oracle at all.

The requirements, stated so that a later refactor has to argue against them explicitly:

1. **Process boundary, always.** `std::process::Command`, input by generated file or stdin, output
   parsed from stdout/stderr. No `-sys` crate, no `build.rs` that compiles or links a comparand, no
   `#[link]`, no vendored source.
2. **No comparand in `[dependencies]` or `[dev-dependencies]`.** Adapters locate a binary at
   runtime and report absence as unavailability. An adapter must degrade to "not installed", never
   to a build failure — the pattern `OracleError::Unavailable { binary, reason }`
   (`src/grobner/differential/singular.rs:52`) already encodes.
3. **An absent comparand is never a result.** Same discipline as the oracle: "an oracle that did
   not answer is never agreement" (`src/grobner/differential/singular.rs:8`). A missing binary, a
   timeout, or an unparsed output is an error, not a comparison that passed.
4. **No comparand on the default build or test path.** Opt-in, as the live Singular sweep already
   is (`README.md:114-121`).
5. **Do not "optimize" an adapter into a dependency.** Subprocess overhead is a known, measurable
   constant; #257's protocol is where it gets accounted for. Removing the process boundary to save
   it would convert a licensing non-issue into a licensing violation, and is forbidden regardless of
   the speedup. If a future proposal wants linkage, it needs its own issue, a licence analysis, and
   human legal review — not a performance argument.
6. **Comparand inputs and outputs are data, not code.** Generated scripts and parsed results are
   zeebra's. A comparand's *own* example files, corpora or test data are governed by its licence
   and are not to be committed (the MQ Challenge pattern, §4).

---

## 8. Attribution, concretely

Applies only to the two permissive entries. Nothing below makes GPL code reusable.

### 8.1 Reusing Sagebrush code under MIT

`LICENSE-MIT` (Sagebrush, `b960770f`) is the standard text, with
`Copyright (c) 2026 SageMath, Inc.`, and its operative condition is one sentence:

> The above copyright notice and this permission notice shall be included in all copies or
> substantial portions of the Software.

So, for any Sagebrush code copied into zeebra:

1. **Keep SageMath, Inc.'s copyright notice and the MIT permission notice with the code.** In
   practice: a header comment on the file or the module naming the origin, plus the full MIT text
   somewhere a recipient of the crate will find it. Zeebra's own `LICENSE-MIT` is zeebra's
   copyright, not SageMath's, so a second notice is required — `LICENSE-MIT-sagebrush`, or a
   `THIRD-PARTY-NOTICES` file, which is the direction §8.3 recommends.
2. **The notice travels with the crate, not with the repository.** It must be in what `cargo
   package` ships, which means the file is included by `Cargo.toml`'s `include`/`exclude` and
   referenced from the source. Arkworks does exactly this: `Cargo.toml:30-31` lists
   `LICENSE-APACHE` and `LICENSE-MIT` among the packaged files.
3. **Record the provenance in the source, in §9's format.** Repository, SHA, `path:line`, date, and
   what was changed. Groebner.jl's `src/Groebner.jl:8-15` is the model for the wording (§3.3).
4. **A research-note citation is not a notice.** `docs/research/` satisfies §9, not the licence.
   Both are required.

### 8.2 What Apache-2.0 adds

Sagebrush and Arkworks are both `MIT OR Apache-2.0`, so **zeebra may simply elect MIT** and §8.1 is
the whole obligation. Electing MIT is the recommended default: it is what zeebra already is, it
avoids §8.2's extra machinery, and a single-licence crate is simpler to audit. Two things about
Apache-2.0 are worth knowing anyway, because a future permissive upstream may be Apache-only.

**The NOTICE obligation (§4(d)).** If the work carries a `NOTICE` file, a redistributor must
reproduce its attribution notices "in at least one of" the derivative work's `NOTICE` file, the
source distribution, or the displayed documentation. This is strictly more than MIT asks: MIT wants
one notice preserved, Apache-2.0 wants an upstream-curated *file* propagated. Sagebrush's
`NOTICE.md` is 45 KB and recursive — it names a derived-code inventory and points at generated
`THIRD-PARTY-NOTICES.txt` files per distribution (`NOTICE.md`, closing section), with
`scripts/third-party-notices.mjs` checked in CI. That is the realistic shape of the obligation at
scale, and it is a reason to prefer electing MIT.

**§5, the patent grant, which is worth having.** Apache-2.0 §3 grants a patent licence from each
contributor covering their contributions, terminating if the licensee initiates patent litigation
over the work. MIT grants no patent rights expressly. For algebraic-cryptanalysis kernels the risk
is low, but it is a real asymmetry: Apache-2.0's patent grant and §4's notice burden come together,
and if an upstream's patent posture ever mattered, Apache-2.0 would be the better election despite
the paperwork. **UNCLEAR whether MIT's grant extends to patents by implication** — commentary
differs, and this is a lawyer's question, not an engineer's (§12).

**Also §4(b):** modified files must carry prominent notices stating that they changed. Cheap, and
good practice regardless of licence.

### 8.3 The mechanism to build if any of this is ever exercised

Nothing is reused today, so nothing is owed today. When something is:

- a single root `THIRD-PARTY-NOTICES.md`, one section per upstream: project, licence, SHA, what was
  taken, what was changed, and the verbatim licence text;
- the licence texts packaged, via `Cargo.toml`'s `include`;
- zeebra's `Cargo.toml:10` `license = "MIT"` revisited only if an upstream forces it — and if an
  upstream would force it, that is the signal not to take the code;
- a CI check that the notices file covers every third-party-derived file, which is what Sagebrush
  does and is the only way this stays true.

---

## 9. Citation format

**Every claim about an external implementation cites: repository, commit SHA, `path:line`, and
access date.** The SHA is not optional — a default-branch citation decays, and three of the entries
in §2 would have been unverifiable without one, since their grant is in a source header that could
move. The format:

```
owner/repo@<short-sha>:<path>:<line-or-range>   (accessed YYYY-MM-DD)
```

with the SHA stated once per note in a `Source:` line and the `path:line` used inline after that.
`docs/research/singular-engine-notes.md` is the template and already does the first half.

**Worked example, applied to an existing note.** `singular-engine-notes.md:9-10` currently says:

> Source: `github.com/Singular/Singular` at `3f188e4e` (2026-11-05), the `kernel/GBEngine`,
> `libpolys/polys` and `Singular/LIB` trees.

and then at `:108` cites the Hilbert-driven pair deletion as:

> The driving itself is `kernel/GBEngine/khstd.cc:28`, `khCheck`.

Under this policy that becomes:

> `Singular/Singular@3f188e4e:kernel/GBEngine/khstd.cc:28` — `khCheck`, the Hilbert-driven pair
> deletion. Licence: GPL-2.0 **or** GPL-3.0 at the licensee's choice (`:COPYING:11-13`; no linking
> exception, §3.1). Algorithmic reference only. (accessed 2026-11-06)

Three things the expansion adds, each of which earns its space:

1. **The SHA is attached to the line, not only to the note's preamble**, so the citation survives
   being quoted elsewhere — which is exactly what happened: #254's note is cited by #256's epic
   body, where the preamble is absent.
2. **The licence and class are at the point of use**, so an agent reading the citation while writing
   code sees "reference only" without going to look.
3. **The claim was re-verified.** `khstd.cc:28` at `3f188e4e` is the opening line of
   `void khCheck( ideal Q, intvec *w, bigintmat *hilb, int &eledeg, int &count, kStrategy strat)`,
   with the comment at `:24-27` reading "compare the given hilbert series with the current one,
   delete not needed pairs (if possible)". The existing citation is **exact**, which is the point of
   checking rather than assuming.

The preamble line should also gain the class, once per source:

> Source: `Singular/Singular@3f188e4e` (accessed 2026-11-05/06), the `kernel/GBEngine`,
> `libpolys/polys` and `Singular/LIB` trees. **GPL-2.0 or GPL-3.0; algorithmic reference only — no
> code from this source appears in zeebra.** The subprocess adapter
> (`src/grobner/differential/singular.rs`) is unaffected (§7).

No retrofit of existing notes is proposed. `singular-engine-notes.md` is already correct in
substance and the only thing it lacks is the class annotation; a sweep over the back catalogue would
be churn. New notes use the format.

---

## 10. Checklist for #264–#273

Every source study (#264–#267) and every implementation prototype (#268–#273) satisfies all of this
before merge. It is short on purpose.

**Before reading**

- [ ] The licence of each source to be read is in §2's table, or has been verified and added to it,
      from the project's own licence file or source headers at a pinned SHA.
- [ ] The class is known: reuse permitted / linking only / algorithmic reference only / no grant.
- [ ] §6's reference of record for the technique has been identified, and read **first** where one
      exists.

**In the note**

- [ ] A `Source:` line per external project: `owner/repo@<sha>`, access date, licence, class (§9).
- [ ] Every claim about an external implementation carries `path:line` at that SHA.
- [ ] Negative and ambiguous findings kept, not smoothed over — including "we could not determine
      the licence" and "this is the same code as that other project's" (§3.3).
- [ ] Where a reading contradicts a published description, both are recorded.

**Before any code is written**

- [ ] For a reference-only source: the implementation is written from §6's published description,
      with the source closed. If it cannot be, say so in the issue and stop.
- [ ] §5's four tests applied and answered in the pull-request body, not in the author's head.
- [ ] No file in the diff would align line-for-line against a reference-only source.
- [ ] Parameters (block sizes, accumulator widths, thresholds) are justified by a theorem or by a
      measurement on this machine, not by a comparand's constant.

**If code is reused from a permissive source**

- [ ] It is Sagebrush or Arkworks — i.e. in §2's "reuse permitted" class — and nothing else.
- [ ] §8.1's notices are in the tree **and** in what `cargo package` ships.
- [ ] Provenance comment in the source, in §9's format, naming what was taken and what changed.
- [ ] Human review sign-off recorded on the issue. This item is not self-serve.

**If an adapter is involved**

- [ ] Subprocess only; §7's six requirements each hold.
- [ ] Opt-in, off the default build and test path; absence reports as unavailability.
- [ ] No comparand source, corpus or example data committed.

---

## 11. Where this belongs

**Recommendation, not an action.** This document binds contributors generally and not only epic
#256, so `docs/research/` is the wrong home for it on its own. Three observations and a proposal;
the repository's contributor documentation is not restructured here.

1. **There is no `CONTRIBUTING.md`.** The contributor rules live in `CLAUDE.md` — which
   `README.md:3046-3047` already points at for the multi-agent claiming protocol — and in
   `README.md`'s 3 059 lines.
2. **`README.md` does not state zeebra's own licence anywhere.** `license = "MIT"` is in
   `Cargo.toml:10` and the text is in `LICENSE-MIT`; `README.md`'s only licensing sentence is about
   the Fukuoka MQ data at `:122-124`. A reader of the README cannot find out what zeebra is licensed
   as. That is a gap independent of this epic and worth closing on its own.
3. **The policy's two halves have different audiences.** The "what may I reuse" rule binds every
   contributor forever. The verified table is a snapshot that decays and belongs with the research.

Proposed, for a human to accept or decline:

- **Add a short `## License` section to `README.md`** stating MIT, pointing at `LICENSE-MIT`, and
  carrying three sentences of the rule: external implementations are read under their own licences
  and no code is copied; published descriptions are the primary references; benchmark adapters
  invoke external programs and never link them. Then a link here for the table and the detail. This
  is the highest-value change and the smallest.
- **Create `CONTRIBUTING.md`** only if there is other contributor material to put in it. A one-topic
  `CONTRIBUTING.md` is worse than a README section, because it is a second place to look for rules
  that are currently in `CLAUDE.md`.
- **Add the §10 checklist to the pull-request template** if one is introduced, or to `CLAUDE.md`'s
  workflow section, so it is seen at the moment it applies rather than when someone goes looking.
- **Keep this file as the authority** for the table, the per-library verification, and the worked
  examples, with `docs/research/` notes citing it by section.

Note that `docs/MILESTONE-F4.md:711-712` already states the core rule, correctly, in one sentence.
The problem is not that the policy was absent; it is that it was stated once, in a milestone
document, with no table and no boundary test. This file supplies those; a README pointer supplies
the visibility.

---

## 12. What needs a human, and what is still unclear

Flagged rather than resolved. None of these blocks #264–#273, because every one of them concerns
*reuse*, and the policy's answer for everything outside §2's permissive pair is "do not reuse".

1. **CoCoALib's `examples/`.** `README.md:35-36` says CC0; `examples/ex-00-intro.C:1-3` retains
   copyright and grants a one-sentence permission (§3.4). These are not the same grant, and the
   README is stale on an adjacent filename. If anything from `examples/` is ever wanted, this goes
   to legal review first. Current practical answer: not needed, and reading is unrestricted.
2. **Whether MIT's grant reaches patents.** Relevant only if a permissive upstream has a patent
   position; commentary differs and it is not an engineering question (§8.2). It does not arise
   today because nothing is reused.
3. **Any actual reuse from Sagebrush or Arkworks.** Lawful by §2, and still requiring the §8
   mechanism and a human sign-off before merge, because a notice obligation discharged wrongly is
   the same failure as no notice. §10 makes the sign-off a checklist item.
4. **MathicGB's missing `LICENSE.txt`.** Resolved for our purposes — 118 source headers assert
   GPL-2.0-or-later, so the grant exists and the class is reference-only, which forbids reuse anyway
   (§3.2). It would need a human if anyone ever wanted to *redistribute* MathicGB, since the licence
   copy its own headers point at does not exist. Zeebra redistributes nothing.

And three negative findings, kept because they are the kind that gets quietly dropped:

- **No linking exception exists anywhere in Singular** that applies to `kernel/`, `libpolys/` or
  `factory/`. The reconnaissance believed otherwise; §3.1 has the search and the text.
- **The "no grant" class has exactly one occupant**, and it is not an engine — it is the Fukuoka MQ
  data, already handled correctly. MathicGB was the expected occupant and turned out not to be one.
- **Of twenty-one entries, the API's classification was precisely right on two** (Groebner.jl, and
  BRiAl only because `NOASSERTION` was correctly read as "go look"). Verification was not a
  formality; it changed eighteen rows and one of #274's own conclusions.
