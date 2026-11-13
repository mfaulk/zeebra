# Isolated randomized-reduction study (#714)

This study reuses the MQ10 corpus, reference bases, passive counters and process-tree watchdog
from [#713](../grobx-trajectory/README.md). It changes no Zeebra solver default or public API.
The experimental driver and its overlay remain in the separate GPL-3.0-only workspace.

Build and run its tests before taking the benchmark lock:

```sh
python3 tools/test/grobx-randomization-test.py
python3 tools/external/grobx-driver/research/randomization/test_policy.py
python3 tools/external/grobx-driver/research/provision.py \
  --source /path/to/pinned/grobx/checkout \
  --target /buildcache/cargo-target/zeebra-714-grobx --randomization --test
```

The source checkout only supplies `git archive` of
`1854835dbc25f24dc9a9ba017024d5030e99da1c`. The provisioner refuses changed anchors and existing
output directories. It retains the exact lockfile, patched-source hashes and recipe hashes.
Ordinary driver builds and ordinary passive-counter provisioning are unchanged.

Experimental JSON requests retain the ordinary driver contract and accept:

| Key | Meaning |
|---|---|
| `research_policy` | `native`, `no-plain`, `no-signature`, or `none`; the latter two disable signature **zero tests**, not the signature engine. |
| `research_signatures` | Boolean, default true; false selects public `Params.signatures=false`. |
| `research_seed` | Unsigned 64-bit solver seed, default zero. Input-generator seed and input digest stay unchanged. |
| `research_validate` | Boolean, default false; enables the native residual guard only in raw, plain-only runs. |
| `research_work` | Existing passive work-counter switch; also enables event observations. |

Bad policy names/types and signature/certified residual-guard requests are refused. The plain
combination threshold, signature test count, arithmetic, band eligibility, pair rules and handover
policy retain their pinned values. Turning off combinations inherently removes their band path;
that interaction is reported, not described as a SIMD-only ablation. Observe actual reports,
including discarded signature rounds and original-input restarts.

The native guard reduces every original matrix row, including reducer rows, by final pivots before
the plain batch returns. It spends the same deadline/budget and records residual-check work and
time separately. Valid pivot formation supplies the reverse rowspace inclusion. This is a native
invariant check, not an independently checked cofactor certificate. It does not certify signature
prefixes; final global span equality cannot validate earlier signature-zero decisions.
`randomization_contract.py` independently tests both span inclusions with explicit combination
witnesses, including omitted/rogue pivots, degenerate rows and incomplete checks.

Freeze and commit sources before timing. Every primary arm receives five fresh-process
repetitions at each prime, reversing order on alternate repetitions. The base arms are stock,
patched/counters-off, patched/counters-on, no-plain, no-signature-tests, neither, plain-only,
plain-only/no-combinations, plain-only/native-residual-guard, and exact-certified. The latter is a
**separate objective** whose cofactors/checker disable several optimizations, not an isolated
randomization or validation control. Seeds 1 and 2 form a separate sensitivity cohort for three
raw policies, with one attempt per seed/policy/prime. Each of the seven changed policies additionally receives an observer-off control in the same
binary. Total: 170 primary plus 12 sensitivity attempts. Sensitivity is not a correctness proof.

```sh
ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=2 \
  tools/benchlock.sh grobx-714 \
  timeout --signal=INT --kill-after=60s 1800s taskset -c 2 \
  python3 tools/external/grobx-randomization-study.py \
    --grobx-stock /path/to/stock/grobx-driver \
    --grobx-research /buildcache/cargo-target/zeebra-714-grobx/build/release/grobx-driver \
    --scratch /buildcache/cargo-target/zeebra-714-run \
    --output /buildcache/cargo-target/zeebra-714-run/cohort.json.gz \
    --repeats 5 --max-load 8
```

CPU/affinity, compiler, source/config/lock/binary identities, every request and every attempt are
retained. The existing guard enforces 60 seconds and 2 GiB for the complete direct driver process,
including its exact checker; this is tighter than the historical nested 185-second parent watchdog.
The whole campaign has a separately declared 1,800-second outer stop. Process wall includes full
answer encoding. Independent coefficient-for-coefficient comparison to complete retained
Singular-verified references occurs afterwards. Native guard/checker work remains inside its own
process wall. Raw stage times and process wall are distinct.

The load gate preserves a partial cohort and refuses the next attempt; failures/stops remain
results, never implied speedups. No automatic retries or repetition extensions are performed.
Instrumentation overhead is estimated by stock/off/on controls and same-binary on/off pairs
for every policy, with structural-path equality. Wall comparisons use observer-off arms; on arms
provide separately labelled coefficient-work counts.
Any integration proposal needs independent exact acceptance, bounded retry/fallback costs and
public Katsura/Cyclic/larger-MQ validation; this campaign alone does not authorize integration.
