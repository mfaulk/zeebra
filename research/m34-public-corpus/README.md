# #1006: public application panel, first slice

This is the first admitted slice of M34's public application corpus
([plan §8.2](../../docs/MILESTONE-GENERALIZABLE-SELECTION.md)). It adds **39 base problems in 21
families**, every one an exact integer system from the SymbolicData collection. Each problem is
admitted at two fields, 2³¹−1 (`p31`) and 2⁶⁴−59 (`p64`), with grevlex and task `T-GB`. That gives
78 `corpus-instance-v1` records under the [lineage contract](../../docs/research/corpus-lineage.md).

This slice is **not a cohort freeze**. The panel is admitted but unsplit; #1005's separate freeze
commit draws the cohorts once #1006 and #1007 are complete. No solver timings are recorded here,
and the Singular reference runs are not measurements.

| File | Role |
|---|---|
| `panel.json` | Hand-curated selection: problem id, upstream entry, `family_id`, `source_id`, `formulation_id`, parameters and presentation parents |
| `inputs.json` | Exact upstream equations, frozen by `import`, with each upstream file's SHA-256 |
| `catalog.json` | Generated records, one per line. CI rebuilds them from `inputs.json` and compares the bytes |
| `references.json` | Reduced-basis digests for every record: Singular at `p31`, certified grobx at `p64`. The basis text itself is not stored |

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
```

Run these from the repository root with Python 3.9 or newer, standard library only. Extract the
tarball outside the repository.

## Sources and licensing

| Source | Licence, as verified | Decision |
|---|---|---|
| [SymbolicData](https://github.com/symbolicdata/data) `a5cdf536`, `XMLResources/IntPS` | **CC0-1.0**. Asserted for the Data Catalogue at `RDFData/SymbolicData.ttl:13` and `RDFData/Systems.ttl:12`. The repository has no root licence file | **Admitted.** Exact integer equations are imported verbatim; the per-file SHA-256 is in `inputs.json` |
| Groebner.jl benchmark generators (Demin & Gowda, [arXiv:2304.06935](https://arxiv.org/abs/2304.06935), pinned `54c9d643`) | GPL-2.0 ([provenance policy](../../docs/research/external-provenance-policy.md) table) | **Discovery only.** Generator code is not copied. Its application systems (Chandra, Henrion, Hexapod, IPP, the SIAN models, BIOMD) need an independent primary-source definition each; deferred to the next slice |
| [StructuralIdentifiability.jl](https://github.com/SciML/StructuralIdentifiability.jl) and SIAN exports | MIT (GitHub classifier; root file not yet read) | **Next slice.** This needs the exported polynomial system, not the ODE model name, and the Julia export is not yet run here |
| Macaulay2 `ExampleSystems` | GPL-2.0-or-later (provenance policy table) | **Discovery and cross-check only.** Its models overlap SymbolicData; overlapping models are linked through `source_id`, not double-counted |
| [MathRepo](https://mathrepo.mis.mpg.de/) ligand-binding systems | Not yet reviewed | **Pending** licence review |
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

## Exclusions in this slice

| Upstream entries | Reason |
|---|---|
| `Cyclic_*`, `Katsura_*`, `Singular.rcyclic_*`, `Singular.ecyclic_*`, `PoSSo.rkat*`, `Verschelde.eco*`, `Verschelde.redeco*`, `Verschelde.noon*`, `Noonburg-89`, `Reimer_5` | Relatives of the existing ladders. Admitting them would need parent links to the retained Zeebra definitions (#1005 audit); this slice leaves them to that lineage work |
| `Geometry.*` with parameters, and other entries whose coefficients contain symbols | Parametric ideals over Q(u), not exact prime-field systems. A specialization would be a new formulation with its own contract |
| `Geometry.*` without parameters (135), `Curves.*`, `ZeroDim.*` | Not reviewed yet: generated test sets whose provenance needs per-entry review. Next slice |
| `satlib.*` | Boolean SAT encodings. This is a different task class from T-GB over a large prime |
| `Paris.fronville`, `Paris.safey` | 130–165 kB inputs. Deferred until the matrix budget C is fixed (owner decision 3, #1043) |
| `Amrhein`, `Czapor-86c_2`, `Meintjes`, `Singular.schwarz_6`, `ZeroDim.example_33`, `Cassou_1` | Flagged by the first screen; not reviewed in this slice |
| The remaining IntPS entries (`Gerdt-*`, `Wang-*`, `Czapor-*`, `Pfister_*`, `Vermeer*` and others) | Not reviewed yet. Candidates for later slices |
| `ModPS` | Systems that are already modular, at a fixed prime. Not yet reviewed |

## Status against #1006 and §8.2

- **Done.** Licensing review of six sources. An exact admission path, with a CI-checked rebuild.
  39 base problems in 21 families. Six application families cover ≥ 2 scales or instances:
  signal theory, gametwo, Schwarz, robot kinematics, Runge–Kutta and ellipsoid. Two frontier inputs at both fields, plus `sd-hairer-2` at `p64`.
  References at both fields: Singular at `p31`, certified grobx at `p64`, which agree on dimension
  and `vdim`.
- **Open.**
  - Application sources outside SymbolicData: Groebner.jl's systems by independent definition,
    SIAN/StructuralIdentifiability exports, MathRepo.
  - Inequation and saturation tasks; none are in this slice.
  - Coverage by #1009's features.
  - The composition read across #1006 and #1007 together.
