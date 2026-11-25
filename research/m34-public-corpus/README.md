# #1006: public application panel

This is M34's public application corpus ([plan §8.2](../../docs/MILESTONE-GENERALIZABLE-SELECTION.md)).
It holds **56 base problems in 23 families**. 39 are exact integer systems from the SymbolicData
collection. 17 come from two application models outside it, built by independently written
generators: the Chandrasekhar H-equation and n-site phosphorylation steady states. Each problem is
admitted at two fields, 2³¹−1 (`p31`) and 2⁶⁴−59 (`p64`), with grevlex and task `T-GB`. That gives
112 `corpus-instance-v1` records under the [lineage contract](../../docs/research/corpus-lineage.md).

This slice is **not a cohort freeze**. The panel is admitted but unsplit; #1005's separate freeze
commit draws the cohorts once #1006 and #1007 are complete. No solver timings are recorded here,
and the Singular reference runs are not measurements.

| File | Role |
|---|---|
| `panel.json` | Hand-curated selection: problem id, upstream entry or generator call, `family_id`, `source_id`, `formulation_id`, parameters and presentation parents |
| `inputs.json` | Exact upstream SymbolicData equations, frozen by `import`, with each upstream file's SHA-256 |
| `catalog.json` | Generated records, one per line. CI rebuilds them from `inputs.json` and the generators in `tools/m34_public_corpus.py`, and compares the bytes |
| `references.json` | Reduced-basis digests for every record: Singular at `p31`, certified grobx at `p64`. The basis text itself is not stored |
| `composition.json` | Per-family counts, scales and frontier rows for the §8.2 composition read, written by `catalog` and checked by `check` |

## Reproduce

```sh
python3 tools/test/m34-public-corpus-test.py
python3 tools/m34_public_corpus.py check
python3 tools/corpus_lineage.py validate research/m34-public-corpus/catalog.json
# Re-import (needs the pinned upstream checkout, not needed in CI):
gh api repos/symbolicdata/data/tarball/a5cdf5366150bffba22a2c91a86a012dd23831af > sd.tgz
tar xzf sd.tgz && python3 tools/m34_public_corpus.py import symbolicdata-data-a5cdf53
python3 tools/m34_public_corpus.py catalog
# References: Singular (build 44105) at p31, certified grobx 0.155.1 at p64
# (tools/external/grobx-driver); about 10 minutes at --jobs 12, untimed:
python3 tools/m34_public_corpus.py references --timeout 120 --grobx-timeout 300 --jobs 12
# Only rows that are missing or whose input digest changed (about 3 minutes for the 34 generated rows):
python3 tools/m34_public_corpus.py references --missing --timeout 120 --grobx-timeout 300 --jobs 12
```

Run these from the repository root with Python 3.9 or newer, standard library only. Extract the
tarball outside the repository.

## Sources and licensing

| Source | Licence, as verified | Decision |
|---|---|---|
| [SymbolicData](https://github.com/symbolicdata/data) `a5cdf536`, `XMLResources/IntPS` | **CC0-1.0**. Asserted for the Data Catalogue at `RDFData/SymbolicData.ttl:13` and `RDFData/Systems.ttl:12`. The repository has no root licence file | **Admitted.** Exact integer equations are imported verbatim; the per-file SHA-256 is in `inputs.json` |
| Chandrasekhar H-equation: S. Chandrasekhar, *Radiative Transfer* (1950); collocation as in C. T. Kelley, [J. Math. Phys. 21 (1980) 1625](https://doi.org/10.1063/1.524647) | Model from the literature. Generator `chandrasekhar_h` written for Zeebra, MIT | **Admitted.** No third-party code. Groebner.jl's `chandra` was the discovery pointer and was not read |
| n-site phosphorylation: L. Wang and E. D. Sontag, [J. Math. Biol. 57 (2008) 29–52](https://doi.org/10.1007/s00285-007-0145-z) | Reaction network from the paper. Generator `multisite_phosphorylation` written for Zeebra, MIT | **Admitted.** No third-party code or model file |
| Groebner.jl benchmark generators (Demin & Gowda, [arXiv:2304.06935](https://arxiv.org/abs/2304.06935), pinned `54c9d643`) | GPL-2.0 ([provenance policy](../../docs/research/external-provenance-policy.md) table) | **Discovery only.** Generator code is not copied. Chandra is admitted from its primary source, above. Henrion, Hexapod and IPP are excluded below |
| [StructuralIdentifiability.jl](https://github.com/SciML/StructuralIdentifiability.jl) and SIAN exports | MIT (GitHub classifier; root file not read) | **Excluded for M34.** The exported system is what would be admitted, and neither package is installed here (`~/.julia` has Groebner.jl only). SIAN's export also substitutes random values, so each export would be a new seeded formulation |
| Macaulay2 `ExampleSystems` | GPL-2.0-or-later (provenance policy table) | **Discovery and cross-check only.** Its models overlap SymbolicData; overlapping models are linked through `source_id`, not double-counted |
| [MathRepo](https://mathrepo.mis.mpg.de/) ligand-binding systems | **No licence stated.** The site shows only "© Copyright 2026, Max Planck Institute for Mathematics in the Sciences" and a Terms of Use link (read 2026-11-25) | **Excluded:** unclear licence, per #1006's stop condition |
| PHCpack demo database | Not reviewed for admission | **Discovery only**, per #1006: its entries are often floating-point |

The CC0 statement covers the catalogue as a whole. The `IntPS` XML files carry no per-file licence,
so the catalogue-level dedication is the grant relied on. The upstream entries record their
contributors and creation dates (`createdBy`, `createdAt`); the original publications are listed in
SymbolicData's `RDFData/Bibliography.ttl`.

## Panel

`n` and `m` are the number of variables and generators. *Dimension* is from Singular at `p31`.
"Frontier" means Singular's `std` did not finish in 120 s; per #1006 such an input is retained with
`reference: none`. At `p64`, `sd-hairer-2` is also a frontier input: certified grobx did not finish
in 300 s. Its `p31` twin has a reference.

| Problem | Upstream entry | `family_id` | n | m | Dimension at p31 |
|---|---|---|---:|---:|---|
| `sd-signaltheory-f633` | `SignalTheory.f633` | `sd/signal-theory` | 10 | 9 | 2 |
| `sd-signaltheory-f744` | `SignalTheory.f744` | `sd/signal-theory` | 12 | 12 | 1 |
| `sd-signaltheory-f855` | `SignalTheory.f855` | `sd/signal-theory` | 14 | 15 | 1 |
| `sd-signaltheory-f966` | `SignalTheory.f966` | `sd/signal-theory` | 16 | 24 | frontier |
| `sd-verschelde-gametwo5` | `Verschelde.gametwo5` | `sd/gametwo-nash` | 5 | 5 | 0, vdim 44 |
| `sd-verschelde-gametwo6` | `Verschelde.gametwo6` | `sd/gametwo-nash` | 6 | 6 | 0, vdim 265 |
| `sd-verschelde-gametwo7` | `Verschelde.gametwo7` | `sd/gametwo-nash` | 7 | 7 | frontier |
| `sd-singular-schwarz-7` … `-11` | `Singular.schwarz_7` … `_11` | `sd/schwarz` | 7–11 | 7–11 | 0, vdim 2ⁿ |
| `sd-robot-fabrice24` | `Robot-Fabrice24` | `sd/robot-kinematics` | 9 | 9 | 0, vdim 40 |
| `sd-robot-romin` | `Robot-Romin` | `sd/robot-kinematics` | 12 | 7 | 5 |
| `sd-robot-rr` | `Robot-RR` | `sd/robot-kinematics` | 15 | 16 | 4 |
| `sd-robot-jcf26` | `Robot-jcf26` | `sd/robot-kinematics` | 34 | 34 | 0, vdim 40 |
| `sd-butcher` | `Butcher` | `sd/runge-kutta-order-conditions` | 8 | 8 | 3 |
| `sd-hairer-1` | `Hairer_1` | `sd/runge-kutta-order-conditions` | 8 | 6 | 2 |
| `sd-hairer-2` | `Hairer_2` | `sd/runge-kutta-order-conditions` | 13 | 11 | 2 |
| `sd-hairer-2-1` | `Hairer_2_1` (parent `sd-hairer-2`) | `sd/runge-kutta-order-conditions` | 13 | 12 | 2 |
| `sd-ellipsoid-2`, `-4`, `-m2` | `Ellipsoid_2`, `_4`, `_-2` | `sd/ellipsoid` | 10 | 4 | 6 |
| `sd-verschelde-virasoro` | `Verschelde.virasoro` | `sd/virasoro` | 8 | 8 | 0, vdim 256 |
| `sd-fourbodyproblem` | `FourBodyProblem` | `sd/four-body` | 6 | 6 | 0, vdim 84 |
| `sd-verschelde-chemkin` | `Verschelde.chemkin` | `sd/chemkin` | 13 | 13 | 0, vdim 40 |
| `sd-caprasse` | `Caprasse` | `sd/classical/caprasse` | 4 | 4 | 0, vdim 56 |
| `sd-cassou` | `Cassou` | `sd/classical/cassou` | 4 | 4 | 0, vdim 16 |
| `sd-trinks`, `sd-trinks-1` | `Trinks`, `Trinks_1` (parent `sd-trinks`) | `sd/classical/trinks` | 6 | 6, 7 | 0, vdim 10 and 2 |
| `sd-fee-1` | `Fee_1` | `sd/classical/fee_1` | 4 | 4 | 0, vdim 26 |
| `sd-rose` | `Rose` | `sd/classical/rose` | 3 | 3 | 0, vdim 136 |
| `sd-schiele` | `Schiele` | `sd/classical/schiele` | 5 | 4 | 1 |
| `sd-czapor-86a` | `Czapor-86a` | `sd/classical/czapor-86a` | 3 | 3 | 0, vdim 8 |
| `sd-weispfenning-94` | `Weispfenning-94` | `sd/classical/weispfenning-94` | 3 | 3 | 0, vdim 54 |
| `sd-raksanyi` | `Raksanyi` | `sd/classical/raksanyi` | 8 | 4 | 4 |
| `sd-bjoerk-8` | `Bjoerk_8` | `sd/classical/bjoerk_8` | 8 | 9 | unit ideal (basis {1}) |
| `sd-heron` | `Heron` | `sd/classical/heron` | 7 | 4 | 3 |
| `sd-fourcircles` | `FourCircles` | `sd/classical/fourcircles` | 2 | 3 | 0, vdim 14 |

**Cross-check.** For every zero-dimensional problem where SymbolicData publishes a degree
(`sd:hasDegree`), Singular's `vdim` at `p31` agrees with it: Caprasse 56, Trinks 10, Trinks_1 2,
Fee_1 26, Rose 136, Czapor-86a 8, Weispfenning-94 54 and FourCircles 14. That is evidence that the
import and the reduction modulo `p31` did not alter these ideals.

**Lineage choices.**
- `formulation_id` is the upstream entry, so a field twin is the same formulation (§8.2).
- `presentation_parent` links an `_1` variant to its base where both are admitted.
- `support_id` is the computed `support-v1` digest; reduction removed no term at either prime.
- Each robot model has its own `source_id` but shares the family, so S2 keeps the family whole.
- The `sd/classical/*` problems are separate models from different authors, so each is its own
  family and source. They cover one scale each and do not satisfy §8.2's two-scale rule.
- The `sd/schwarz` family comes from Singular's example collection. No application model is
  claimed for it.

## Generated application families

Both generators live in `tools/m34_public_corpus.py` and are rebuilt by `check` in CI. The record's
`source` names the paper, and its `transformations` list the parameter specialization before the
prime reduction.

| Problem | `family_id` | n | m | Dimension at p31 |
|---|---|---:|---:|---|
| `gen-chandrasekhar-h-4` … `-11` | `app/chandrasekhar-h` | 4–11 | 4–11 | 0, vdim 2ⁿ (16 … 2048) |
| `gen-phosphorylation-2` … `-7` | `app/multisite-phosphorylation` | 9–24 | 9–24 | 0, vdim 2·sites+1 (5 … 15) |
| `gen-phosphorylation-{2,4,6}-nonzero` (parent: the same `sites` without `-nonzero`) | `app/multisite-phosphorylation` | 10, 16, 22 | 10, 16, 22 | 0, vdim equal to the parent |

- **Chandrasekhar H-equation.** H(μ) = 1 + (c/2)·μ·H(μ)·∫₀¹ H(ν)/(μ+ν) dν, collocated at
  μᵢ = i/n with the n-point right-endpoint rule: 2n·Hᵢ − c·Hᵢ·Σⱼ i/(i+j)·Hⱼ − 2n = 0 for
  i = 1..n, with albedo c = 51/50. Each equation is scaled by the lcm of its denominators, which is
  exact over ℚ. Reduction refuses a prime dividing any of those denominators. They are all
  primes ≤ 2n, for example 2, 3, 5, 7, 11, 13 and 19 at n = 11, and each record's
  `clear-denominators` transformation lists them. The Bézout bound 2ⁿ is attained at both primes.
- **Phosphorylation.** The sequential distributive network Sᵢ + E ⇌ ESᵢ → Sᵢ₊₁ + E and
  Sᵢ₊₁ + F ⇌ FSᵢ₊₁ → Sᵢ + F for i = 0..sites−1, under mass action. The equations are the ODE
  right-hand sides of every complex and of S₀..S_{sites−1}. The dependent rows (S_sites, E, F) are
  replaced by the three conservation laws. The rates at site i are (i+2, 1, i+1) for the kinase and
  (i+1, 2, i+3) for the phosphatase, with totals E = 7, F = 11 and S = 10·sites + 3. The specialization
  is a choice made here, recorded on every record. It is not taken from the paper. `n` in
  `family_parameters` is the variable count, so S3 scales on the same axis as the other families.
  `sites` is kept beside it.

**Inequations and saturation.** #1006 asks for tasks with inequations and saturation. #1004's
contracts (`T-GB`, `T-GB-conv`, `T-PT1`, `T-PTALL`) and the lineage schema's `task` field have
no saturation task, so the panel admits what those contracts can state:

- The three `-nonzero` problems add the Rabinowitsch generator t·E·F·S₀⋯S_sites − 1, encoding
  "every free species is nonzero". Their task is `T-GB` of the **augmented ideal** in
  k[species, t], labelled by a `rabinowitsch-augmentation` transformation. It is not the saturation
  I : (E·F·S₀⋯S_sites)^∞. Here the augmented `vdim` equals the parent's at both primes, so no
  steady state of these specializations has a zero free species.
- Producing the saturation itself needs an elimination order on t and an extraction step. That is
  a new contract, which #1004 would have to write before any arm could be compared on it. It is not
  admitted, and this is recorded as an exclusion rather than approximated by the augmented basis.

## Verification procedure

A successful arm output on a `p31` record is verified by comparing its `reduced-basis-v1` digest
with `references.json`. To compute that digest, make each basis element monic and normalize it the
way `normalized-input-v1` does, then hash `{format, field, variables, order, basis}`. The oracle is
Singular, `option(redSB)`, `std` then `simplify(…, 1)`, run as a subprocess.

On a `p64` record the oracle is certified grobx 0.155.1 (`8005a2a1`, `tools/external/grobx-driver`),
as the [M33 protocol](../../docs/research/adaptive-selection-contracts.md) allows above 2³¹. Its
checker independently verifies every returned basis. The tool parses grobx's basis text and computes the
same `reduced-basis-v1` digest. Making each element monic at its grevlex leading term means the two
oracles' different scalars and orderings cannot change the digest; the `p31` digests were identical
before and after that normalization was added. 36 of 39 `p64` records have a reference, and the three
frontier rows are kept with no reference.

The two fields check each other. On every problem with a reference at both primes, zero-dimensionality
and `vdim` agree between Singular at `p31` and grobx at `p64`. grobx's `vdim` is counted from the
staircase of its leading terms. `m34-public-corpus-test.py` asserts that agreement.

## Exclusions

| Upstream entries | Reason |
|---|---|
| `Cyclic_*`, `Katsura_*`, `Singular.rcyclic_*`, `Singular.ecyclic_*`, `PoSSo.rkat*`, `Verschelde.eco*`, `Verschelde.redeco*`, `Verschelde.noon*`, `Noonburg-89`, `Reimer_5` | Relatives of the existing ladders. Admitting them would need parent links to the retained Zeebra definitions (#1005 audit); they are left to that lineage work |
| `Geometry.*` with parameters, and other entries whose coefficients contain symbols | Parametric ideals over Q(u), not exact prime-field systems. A specialization would be a new formulation with its own contract |
| `Geometry.*` without parameters (135), `Curves.*`, `ZeroDim.*` | Not reviewed yet: generated test sets whose provenance needs per-entry review. Next slice |
| `satlib.*` | Boolean SAT encodings. This is a different task class from T-GB over a large prime |
| `Paris.fronville`, `Paris.safey` | 130–165 kB inputs. Deferred until the matrix budget C is fixed (owner decision 3, #1043) |
| `Amrhein`, `Czapor-86c_2`, `Meintjes`, `Singular.schwarz_6`, `ZeroDim.example_33`, `Cassou_1` | Flagged by the first screen; not reviewed |
| The remaining IntPS entries (`Gerdt-*`, `Wang-*`, `Czapor-*`, `Pfister_*`, `Vermeer*` and others) | Not reviewed yet. Candidates for later slices |
| `ModPS` | Systems that are already modular, at a fixed prime. Not yet reviewed |
| Saturation outputs I : g^∞ | No #1004 contract or schema `task` for them. The augmented-ideal `T-GB` is admitted instead and labelled as such (see *Inequations and saturation*) |
| Groebner.jl's Henrion, Hexapod, IPP | Not admitted. IPP's PHCpack form has decimal coefficients, which are never converted silently. No primary-source definition of Hexapod or Henrion was reconstructed within the #1006/#1007 line cap |
| BioModels steady states (BIOMD103, BIOMD123) | Rate laws must be turned into polynomials and parameters specialized from SBML. That is an export step with its own audit, not done here. `app/multisite-phosphorylation` covers the mass-action steady-state class |
| SIAN / StructuralIdentifiability.jl exports | Toolchain not installed; each export is a seeded random specialization (see sources) |
| MathRepo | No licence stated |

## Composition hand-off to #1007 (§8.2)

`composition.json` is #1006's side of the combined composition table. `catalog` writes it, and
`check` fails when it is stale. For each `family_id` it lists the base problems, the scales (the
distinct values of `n`, the variable count), the `source_id`s, a `multi_scale` flag, and the
reference-frontier rows at each field. "Frontier" here means the oracle did not finish. It is a
proxy: §8.2's frontier is "no arm finishes within C", which #1012 measures.

| | Base problems | Families |
|---|---:|---:|
| Whole panel | 56 | 23 |
| Families with ≥ 2 scales (§8.2's rule) | 37 | 7 |
| Single-scale families: `sd/classical/*` (12), `sd/ellipsoid`, `sd/virasoro`, `sd/four-body`, `sd/chemkin` | 19 | 16 |

The seven multi-scale families are `app/chandrasekhar-h` (8), `app/multisite-phosphorylation` (9),
`sd/schwarz` (5), `sd/signal-theory` (4), `sd/robot-kinematics` (4),
`sd/runge-kutta-order-conditions` (4) and `sd/gametwo-nash` (3). All are public applications except
`sd/schwarz`, which comes from Singular's example collection, so #1006 meets the "≥ 4 public
application families" part by itself.

- **Single-scale families.** They remain admitted and are usable under S1, S2 and S5. They cannot
  meet §8.2's two-scale rule, so #1006 counts only the 37 multi-scale problems toward the pilot.
  Merging them into one family would let them in, but it would turn 16 unrelated models into one
  S2 group that holds a quarter of #1006's problems. That merge is not made here.
- **15% cap.** The largest #1006 family, `app/multisite-phosphorylation`, has 9 problems. That is
  within 15% for any pilot of 60 or more base problems.
- **Frontier and small.** At `p31`, 2 of 56 problems are oracle-frontier: `sd-signaltheory-f966`
  and `sd-verschelde-gametwo7`. The phosphorylation problems are all well under a second in
  Singular. §8.2's ≥ 10% frontier and ≥ 10% small shares are read on arm timings by #1012, not
  here.

## Coverage by #1009's features

These values come from `examples/feature_costs.rs --skip-solve`, run on all 112 records of this
catalog. The counting rules are `coverage()` in
[`research/1009-feature-costs/summarize.py`](../1009-feature-costs/summarize.py). These are feature
*values*, not timings. #1009's cost verdicts stay those of its own campaign, which covered the
78 first-slice records. Counts are records; each problem has two records, and both fields give the
same values.

| Question | First slice (78) | Added here (34) | Panel (112) |
|---|---:|---:|---:|
| variables `n` | 2–34 | 4–24 | 2–34 |
| wide inputs, `n > 16` | 2 | 8 | 10 |
| max degree | 2–12 | 2–10 | 2–12 |
| terms | 12–796 | 24–143 | 12–796 |
| `m > n` / `m = n` / `m < n` | 12 / 44 / 22 | 0 / 34 / 0 | 12 / 78 / 22 |
| every generator homogeneous | 2 | 0 | 2 |
| degree 2, no linear generator | 16 | 16 | 32 |
| affine-linear rank > 0 | 32 | 18 | 50 |
| a scalar substitution | 36 | 18 | 54 |
| binomials > half the generators | 6 | 12 | 18 |
| a leading monomial divisible by another | 50 | 18 | 68 |
| greedy elimination width | 1–24 | 3–22 | 1–24 |
| top-degree density | 3.3·10⁻⁵ – 1 | 1.3·10⁻⁶ – 0.4 | 1.3·10⁻⁶ – 1 |
| incidence splits, unused variable, constant generator, inconsistent linear part, all initial pairs coprime, a cap reached | 0 | 0 | 0 |

- **What the generated families add.** The wide region `n > 16` goes from one problem to five: phosphorylation
  at 5, 6 and 7 sites, the 6-site nonzero presentation, and `sd-robot-jcf26`. There is now a
  controlled-size ladder of dense square quadratics (Chandrasekhar, every Hᵢ coupled to every Hⱼ).
  There is also a ladder whose linear conservation laws and binomial-heavy complex equations grow
  with size (phosphorylation).
- **Still uncovered by public data.** No public problem splits into incidence components. Only
  `sd-raksanyi` is homogeneous, and no problem has all initial pairs coprime. Those are structural
  properties that #1007's controlled families (`zb/coupled-blocks`, `zb/toric`, …) vary on
  purpose. Public applications were not bent to fill them.

`examples/feature_costs.rs` gains instantiations for 18, 21, 22 and 24 variables, so every record
in this catalog can be read. Reproduce, with a private `CARGO_TARGET_DIR`:

```sh
cargo build --release --example feature_costs
for id in $(python3 -c "import json; print(*[r['id'] for r in json.load(open('research/m34-public-corpus/catalog.json'))])"); do
  "$CARGO_TARGET_DIR"/release/examples/feature_costs --catalog research/m34-public-corpus/catalog.json \
    --id "$id" --skip-solve --batches 1 --min-batch-ms 0
done > features.jsonl
```

## Status against #1006

- **Done.**
  - Licensing review of the sources in *Sources and licensing*. Admitted: SymbolicData, the
    Chandrasekhar H-equation and n-site phosphorylation. Excluded with reasons: MathRepo, SIAN and
    StructuralIdentifiability exports, BioModels, Henrion, Hexapod and IPP.
  - 56 base problems in 23 families, 112 records, each with an exact admission path that CI
    rebuilds.
  - References at both fields for every record except five frontier rows: `sd-signaltheory-f966` and `sd-verschelde-gametwo7` at both fields, and `sd-hairer-2` at `p64`.
    Zero-dimensionality and `vdim` agree across fields on every pair.
  - Inequations: three Rabinowitsch presentations under `T-GB`. Saturation is a documented
    exclusion until #1004 writes a contract for it.
  - Feature coverage above. Composition hand-off in `composition.json`.
- **Left to later work, not blocking M34.** The unreviewed SymbolicData entries in *Exclusions*.
  The ladder relatives, which need #1005's parent links. A saturation contract, which is #1004's.
  A SIAN export, if a toolchain is provisioned.
