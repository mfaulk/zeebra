# msolve gap evidence (#737)

Raw output behind [`docs/research/msolve-gap.md`](../../docs/research/msolve-gap.md). Zeebra was
built at `99a81844` (pre-rebase; the same harness is `47161ee1` on this branch). msolve is 0.11.0, run on an AMD Threadripper PRO 5995WX with `taskset -c 4`
and one worker.

| file | what |
|---|---|
| `cohort.txt` | the timed cohort under `tools/benchlock.sh`: five interleaved rounds per field of `examples/msolve_gap.rs` and **stock** msolve `-v 2 -t 1 -g 2` |
| `zeebra-batches-32003.tsv`, `zeebra-batches-2147483647.tsv` | per-batch degree, pairs, basis size, rows, reducer rows, columns and as-built nonzeros, then totals and stage clocks |
| `msolve-counted-32003.log`, `msolve-counted-2147483647.log` | the counting copy built by `tools/external/msolve-count.py`. The `ZB_COUNT` line on each log's last lines holds the phase counts, and the basis is byte-identical to stock msolve's. Not a timing source. |
