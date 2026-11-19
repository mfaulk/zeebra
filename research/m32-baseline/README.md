# #939 M32-0: freeze and corpus pin

Plan: [`docs/MILESTONE-ADAPTIVE-F4.md`](../../docs/MILESTONE-ADAPTIVE-F4.md) §7.1, §8.3 (F0), §10.1.
Findings: [`docs/research/m32-baseline.md`](../../docs/research/m32-baseline.md).

**Measured at:** the admission read only — pin build `f26b8d80` (tag `measured/939-pin`): the
baseline `7b25a1ee` plus the held-out inputs in `examples/sig_f4_study.rs`; library identical.
One `tools/bench-reserve.sh` reservation of CCDs 1–2, `bench-reserve run zb-939 8-23`, 2026-11-19 09:15–09:22 EST ([benchlock.log](benchlock.log), `status=0`); children `taskset` from CPU 8, `rss-guard` 8 GiB, 180 s cap. Load 3–6 on the other CPUs (another session's compilers); an admission bound, not a gate. **Host:** Threadripper PRO 5995WX.

This directory holds #939's first two deliverables. The baseline cohort, the symbolic-stage
attribution, the cost model, #934 and #935 follow under the same issue and add their own files here.

## Files

| File | What |
|---|---|
| [pins.py](pins.py) → [pins.json](pins.json) | the freeze commits, every development and held-out row's canonical SHA-256 and generator, and the admission verdicts; reproduced in CI |
| [identities.py](identities.py) → [identities.json](identities.json) | toolchain, build, options, field representations, timed `src/` diffs, executable SHA-256s of all three builds |
| [campaign.py](campaign.py), [run.sh](run.sh) | the `admission` suite on M31's child runner (`research/m31-baseline/campaign.py` `run_one`) |
| [test_pins.py](test_pins.py) | unit tests for the admission rule and the pin reproduction; run in CI |
| `admission.jsonl.gz`, `session.log`, `benchlock.log` | every admission attempt, the session console and its `bench-reserve run` lock record |

## 1. Freeze (F0)

| Role | Commit | Timed tree |
|---|---|---|
| M31 reference | `8715c8ed` (#926, on `main`) | — |
| M32 baseline | `7b25a1ee` (#943, `main` at the freeze) | `src/` = `e59a90a1`'s; vs `8715c8ed`, 8 added lines in two files, all documentation: a 7-line performance caveat in `src/grobner/sigf4/dispatch.rs`'s doc comment and one `#[doc = include_str!(…)]` in `src/lib.rs`. No code line differs (`identities.json`, `timed_diffs`). `Cargo.toml`, `Cargo.lock`, `.cargo/` identical |
| Pin build | `f26b8d80` | the baseline plus `examples/sig_f4_study.rs`'s held-out inputs and instantiations; `src/` identical to the baseline |

Every executable is built from a `git archive` of its commit into a private target directory:
release, fat LTO, `codegen-units = 1` (`Cargo.toml`), `-C target-cpu=x86-64-v3`
(`.cargo/config.toml`), `--features research-sigf4`, `RUSTC_WRAPPER=""`, `CARGO_INCREMENTAL=0`,
rustc 1.99.1 (58cf8f9c3 2026-10-13). Fields: Goldilocks and 2⁶⁴−353 as `PrimeFieldElement64<p>`, GF(32003) as `Zp32003`,
GF(2³¹−1) as `Zp2147483647`; order grevlex throughout.

`wide_corpus` and `zeebra_driver` are byte-identical across the reference and the baseline. The two
executables that link the signature engine differ, consistent with the seven doc-comment lines
added to `sigf4/dispatch.rs`, which shift the source line numbers embedded in its panic locations.

| Build | Executable | SHA-256 |
|---|---|---|
| M31 reference `8715c8ed` | `m29_cost_model` | `04488cbc717b66814ca5e57f952cd77405480c51c812bbd58d91682eab66f5fd` |
| M31 reference `8715c8ed` | `sig_f4_study` | `90f3577954cd88d8ebf12c1f8f5a31bb0d9233b142821959cbb99c21c308f4ee` |
| M31 reference `8715c8ed` | `wide_corpus` | `75ad7d5d36b4f0ba580e6452637ce9da26253fd3aaa1d3c0348f9117060582a9` |
| M31 reference `8715c8ed` | `zeebra_driver` | `e824462a5dc408c78e1b7905b35e6ef81dcf2f0bc4288fa8294eaf612b0fdc46` |
| M32 baseline `7b25a1ee` | `m29_cost_model` | `b9c4ae822221501ee62afa948e9b742b98ac1972dff652643b0b82922dffc358` |
| M32 baseline `7b25a1ee` | `sig_f4_study` | `2048b344ccf3463943d0d7369b4a51244d2abbb0388bef2fe55432ef7408968f` |
| M32 baseline `7b25a1ee` | `wide_corpus` | `75ad7d5d36b4f0ba580e6452637ce9da26253fd3aaa1d3c0348f9117060582a9` |
| M32 baseline `7b25a1ee` | `zeebra_driver` | `e824462a5dc408c78e1b7905b35e6ef81dcf2f0bc4288fa8294eaf612b0fdc46` |
| pin build `f26b8d80` | `sig_f4_study` | `26b25335db554ab8b0d720a0e48a178c460306e779411fbb992ad85bffd471a3` |

## 2. Corpus pin (plan §10.1)

Two canonical forms, each its source's own: catalog rows hash `research/wide-corpus/cases.json`'s
`wide-corpus-v1` text (as M31 pinned them); rows built in code hash the external contract's
`Instance::canonical` text (as the published ladder pins MQ10). `pins.py` re-hashes the catalog and
checks every code pin is present verbatim in its source; `sig_f4_study`'s
`held_out_candidates_reproduce_their_pins` test rebuilds every held-out row from its generator.

### Development set (tuning allowed)

| Row | Field | Vars | Role | Generator | Canonical SHA-256 |
|---|---|---|---|---|---|
| eco-12 | 2⁶⁴−353 | 12 | M31 primary | research/wide-corpus/cases.json (independent benchmark_systems definition) | `e9ef0fecf3906d9283e1ce003c4489d6921fb8718f2956c39c4aaa79e52a93cb` |
| katsura-11 | Goldilocks | 11 | M31 second family | research/wide-corpus/cases.json (independent benchmark_systems definition) | `036f0a35884e82d7bc3e3bc930ee9ccbe38fbddfc81e56fa8bf190a05ae1b955` |
| katsura-11 | 2⁶⁴−353 | 11 | M31 competitive | research/wide-corpus/cases.json (independent benchmark_systems definition) | `c08214c56a6654ab7a376c61df339b2e7cc65a225d027cc3a3fc3bec9876a4a2` |
| mq-random-11 | Goldilocks | 11 | M31 reported | research/wide-corpus/cases.json (dense MQ; StdRng seed 1937768459; all degree <=2 coefficients nonzero; no planting) | `ee76de455c5ea571d6e8286152a4b4380b9d1ea323ee63dc8f889ffa11a92af5` |
| mq-random-10 | GF(32003) | 10 | M31 MQ10 | grobner::external::corpus::random_mq_instance(10, seed 10) (ladder) | `16422dafcdb6487ea541f976f7754112b811c85af2b3537ed10fe4ef9c8f3d7f` |
| mq-random-10 | GF(2³¹−1) | 10 | M31 MQ10 | grobner::external::corpus::random_mq_instance(10, seed 10) (ladder) | `72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2` |
| cyclic-7 | Goldilocks | 7 | M31 unfavourable control | research/wide-corpus/cases.json (independent benchmark_systems definition) | `274e9a533b788e6e440803ad61ee44d2e0c691cec045c8c3bd6607ad8c42cb11` |
| cyclic-7 | 2⁶⁴−353 | 7 | M31 unfavourable control | research/wide-corpus/cases.json (independent benchmark_systems definition) | `1da97cb3fe0eff34f224caaa8f029579d5f7252d910b78a3d5021baec41386bc` |
| katsura-4 | Goldilocks | 4 | M31 small control | research/wide-corpus/cases.json (independent benchmark_systems definition) | `00f08d221047f38741f377f52893d3d561236feecf3bce5f9108d570937f35d3` |
| katsura-4 | 2⁶⁴−353 | 4 | M31 small control | research/wide-corpus/cases.json (independent benchmark_systems definition) | `f2670d770ef9a866db0a407dbd1f05827563a9af3bc4485d51a99bb3eef307b6` |
| noon-7 | Goldilocks | 7 | M31 small control | research/wide-corpus/cases.json (Noonburg 11/10; equations multiplied by 10) | `c146f701505e9d4a0b2ffaec9d0047b85eba1358f885c54196115c14ced7a933` |
| katsura-9 | 2⁶⁴−353 | 9 | M31 held out, demoted | research/wide-corpus/cases.json (independent benchmark_systems definition) | `18eb9c774fc5700cc38e0724dc04af38f34803132a8c20b38f1ad88f5ff749ec` |
| noon-8 | 2⁶⁴−353 | 8 | M31 held out, demoted | research/wide-corpus/cases.json (Noonburg 11/10; equations multiplied by 10) | `403af18521ea58b7846c8cc18d07f9932884a27413953b9c6eac6a23ed090668` |

### Held-out set (never used for tuning; read once by #941, again by #942)

Candidates were fixed by the plan before any read. Where the plan's (name, field) already exists in
the wide catalog, that row is the candidate; katsura-10 at GF(2³¹−1) is the published ladder's
rung (10 variables; its digest was published before M32). The other three are generated from
`grobner::benchmark_systems` or `grobner::external::corpus::random_mq_instance`; the 9-variable MQ
takes the ladder's seed rule, seed = n, so seed 9, which no earlier row uses.

| Row | Field | Vars | Generator | Canonical SHA-256 | F4-16 process wall, ms (3 reps) | Peak RSS | Basis | Verdict |
|---|---|---|---|---|---|---|---|---|
| mq-random-10 | Goldilocks | 10 | research/wide-corpus/cases.json (dense MQ; StdRng seed 1937768458; all degree <=2 coefficients nonzero; no planting) | `f69e955f898956df18bf174d1635f4f2cef7cf3e457e101713e826b3674a7bf3` | 925.1, 930.5, 933.5 | 107 MiB | 426 | **kept** |
| mq-random-12 | 2⁶⁴−353 | 12 | research/wide-corpus/cases.json (dense MQ; StdRng seed 1937768460; all degree <=2 coefficients nonzero; no planting) | `549302dc73ca71fcacde392a0e24dc4c26f469159b880d29a6b01c62c0a300a6` | 103969.1, 104554.0, 105039.1 | 1438 MiB | 1463 | **dropped**: median 104554.0 ms outside 20 ms-60 s |
| mq-random-9 | GF(32003) | 9 | grobner::external::corpus::random_mq_instance(9, seed 9) | `4e4ddcb645c8f6eddb73d21a1532437643f7a2a2a6faf6643886d1c4a5076b21` | 3.1, 3.1, 3.2 | 5 MiB | 1 | **dropped**: median 3.1 ms outside 20 ms-60 s; the system is inconsistent (reduced basis {1}) |
| katsura-10 | GF(2³¹−1) | 10 | grobner::benchmark_systems::katsura::<10> (ladder katsura_instance) | `67d6a96fadd21cc7a295c7100c93d84d2d7be37d9b7927377e57f973ebbbc8b0` | 240.5, 242.4, 250.8 | 42 MiB | 272 | **kept** |
| eco-11 | GF(2³¹−1) | 11 | grobner::benchmark_systems::eco::<11> | `3bdb17005b060d861412758860684229498a54906f610b9854b6bd09d8d11951` | 426.1, 427.4, 432.2 | 60 MiB | 389 | **kept** |
| cyclic-6 | Goldilocks | 6 | grobner::benchmark_systems::cyclic::<6> | `2867c8eb39e07bec37ecb907e5b6971146a479594b0a9fc5ba20b64650a0c918` | 7.5, 7.6, 7.7 | 8 MiB | 45 | **dropped**: median 7.6 ms outside 20 ms-60 s |

**Admission rule** (plan §10.1, fixed before the read): kept iff conventional F4 at 16 workers
completes in 20 ms–60 s under §10.4's budgets (180 s wall, `rss-guard` 8 GiB) and both engines
accept the field; otherwise dropped with the reason and not replaced. Read as the median process
wall of three fresh-process repetitions (`sig_f4_study --engine f4 --workers 16`, CPUs 8–23):
an admission bound, not a gate. Field acceptance is static: both engines are generic over
`FiniteField`, the signature engine's only refusal is a non-graded order, and `sig_f4_study`
instantiates both engines for every row. The signature engine was not run on any held-out row.

**Pinned held-out set: 3 rows**: goldilocks/mq-random-10, m31/katsura-10, m31/eco-11. Dropped, not replaced: wide64/mq-random-12 (conventional F4-16 takes 104.6 s, above 60 s), gf32003/mq-random-9 (3.1 ms, below 20 ms: seed 9 gives an inconsistent system) and goldilocks/cyclic-6 (7.6 ms, below 20 ms). All 18 attempts completed; none hit the wall or the RSS guard. Every record's input digest equals its pin (`pins.py` checks it).

## Reproduce

```sh
B=/buildcache/cargo-target/zeebra-939           # never under $HOME or /tmp
export RUSTC_WRAPPER="" CARGO_INCREMENTAL=0 TMPDIR=$B/tmp
for c in pin:f26b8d80 base:7b25a1ee ref:8715c8ed; do
  git archive -o $B/${c%%:*}.tar ${c#*:}
done
# in each extract: cargo build -j24 --release --locked --features research-sigf4 --example sig_f4_study
#   (base and ref also: --example m29_cost_model --example zeebra_driver --example wide_corpus)
# then copy each into $B/bin/{pin,base,ref}/
setsid -w research/m32-baseline/run.sh OUT admission
gzip -n -c OUT/admission.jsonl > research/m32-baseline/admission.jsonl.gz
python3 research/m32-baseline/pins.py > research/m32-baseline/pins.json
python3 research/m32-baseline/identities.py --bins $B/bin --pin f26b8d80 > research/m32-baseline/identities.json
```
