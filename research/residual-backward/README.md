# Residual backward feasibility (#730)

The [decision report](../../docs/research/residual-backward.md) rejects a full-RREF scheduler for
the candidate-only F4 caller and defers a new target scheduler until a current integrated elapsed
profile clears the complete-task opportunity gate. No solver is launched by these commands:

```sh
python3 tools/test/residual-backward-model-test.py
python3 research/residual-backward/model.py --check
```

Use `python3 research/residual-backward/model.py` to regenerate `summary.json`. It reuses the
existing #269/#749 complete-answer and trajectory validators and #592 runtime validator. All
source archive SHA256 identities and original build/controller pins are retained in the summary.
Nothing copies historical timers onto production work counts: ceilings use complete F4 and
backward elapsed durations from the same #269 native attempt; production per-batch work is
reconciled separately across five repetitions at each prime. All 1–64-worker speedups and scratch
sizes here are model outputs, not measurements or additional budget permissions.

`reservation(R,Q,C,p)` charges retained original matrix entries `R`, every deferred output's
maximum suffix support `Q`, and `p` dense rows of width `C`. `workspace(C,sizeof(F),p)` is only
dense cells plus one shared 64-bit index and mask; output storage and runtime overhead are extra.
The tests cover these boundaries and reject incomplete dispatch grids and work batches.

Exact per-target skew and source fanout remain unavailable in the retained cohorts. They are
required if current whole-task elapsed opportunity reopens after forward integration, together
with new bounded measurements and independent complete-answer checks. No production parallel
policy, full solve claim or generic field speedup follows from this offline decision.
