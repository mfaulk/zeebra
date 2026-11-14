# Waiting-row scheduler gate (#729)

The [decision report](../../docs/research/waiting-row-scheduler.md) compares retained CAS evidence
with the requirements of an ordered waiting-row scheduler. No solver campaign runs here.
`evidence.json` is an offline extraction of pinned #728 and #747 archives, not a new timing cohort.
It retains archive hashes, source identities and per-cell median/range. Products after a lost claim
are not avoidable elapsed time; worker-duration balance is not utilization.

Run from the repository root:

```sh
python3 -m unittest discover -s research/waiting-row -p 'test_*.py'
python3 research/waiting-row/evidence.py > /tmp/waiting-row-evidence.json
diff -u research/waiting-row/evidence.json /tmp/waiting-row-evidence.json
python3 research/concurrent-pivots/summarize.py
python3 research/selective-backward/combined_summary.py
bash tools/check-measurement-provenance.sh
```

The existing cohort summarizers independently recheck complete answers and exact input/trajectory
contracts. The extraction checks payload hashes through `study_artifacts`, repetition coverage,
accepted attempts, product/worker aggregation and valid same-process timer boundaries. It does
not rerun independent engines or measure queue costs. Its unit tests cover invalid boundaries,
incomplete worker totals, post-loss counter semantics and the conditional complete-task model.
Existing CI runs these checks and compares regenerated evidence. Solver defaults and APIs are
unchanged; no Rust tests or library build are needed for this evidence-only change.
