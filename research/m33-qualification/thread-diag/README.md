# Thread-state diagnosis of the M33-Q thread-cap rows

This is a diagnosis for owner decision 11 on #965. It is not a timing session: it used no CCD
reservation, ran pinned to CPUs 24–39, and sits outside the five-session budget. It ran on
2026-11-21 with the M33-Q binaries: F0 `31e334bd` (sha256 `fe8fe83c…`) and F2 `db181c51`
(`b14b4680…`), both carrying the harness at `dd57bc4e`.

The question: in the five rows where the harness saw more threads than the cap, does any thread in
state R exceed the cap, or is the excess only threads of a team that has finished or is exiting?

## Method

- `tasktrace.rs` is a standalone tracer: `rustc -O tasktrace.rs`, no dependencies. It launches the
  harness and, from outside the process, sweeps `/proc/<pid>/task/*/stat` every 18–40 µs. The traced
  process therefore has no sampler thread of its own. It logs every change in the number of live
  threads or in the set of running ones, and each thread's first and last sighting.
- `diag.py run` runs every arm of the correctness manifests for the five rows, 20 times each, at
  16 workers, with the harness's own `--sample-threads` sampler off. `diag.py report` produces
  `result.md`.
- A *team* is the set of threads born before any of them is gone. A birth after a team member has
  disappeared starts the next team, so each team starts at its first birth and finishes at its
  last member's last sighting.
- `classify.py` takes each sample with more than 16 worker threads in state R and splits them:
  threads of the newest team started by then, and threads of an earlier team. For the earlier-team
  threads it gives how long they still had before their last sighting (`classify.md`).

The calling thread is excluded from the worker counts. A sweep is not atomic, so a thread can be
seen up to one sweep after it has gone.

```sh
B=/buildcache/cargo-target/zeebra-974
rustc -O -o $B/diag/tasktrace tasktrace.rs
python3 diag.py run --manifests $B --tasktrace $B/diag/tasktrace --out $B/diag/run --reps 20
python3 diag.py report --out $B/diag/run > result.md
python3 classify.py $B/diag/run > classify.md
```

The raw traces, 25 MB, are kept in `/buildcache/cargo-target/zeebra-974/diag/run/` and are not
committed.

## Result

Maximum worker threads in state R at once, over all arms and 20 runs, with a cap of 16:

| Row | F0 | F2 |
|---|---:|---:|
| grevlex/gf32003/katsura-11 | 16 | 16 |
| grevlex/gf32003/noon-7 | 16 | 16 |
| grevlex/wide64/cyclic-7 | 20 (entry) | 17 (entry, f4) |
| grevlex/wide64/noon-8 | 16 | 17 (f4) |
| grlex/wide64/eco-12 | 16 (f4 only; the suite has no F0 entry arm) | 18 (f4) |

- **The newest team never has more than 16 threads running.** In every sample above the cap, the
  excess is threads of an earlier team. That includes F0's 20, which is 16 new threads plus 4–5 old
  ones.
- **Most of those threads disappear soon after.** Earlier-team threads were last seen a median of
  0.26–0.86 ms after the sample, and at most 1.05 ms. That looks like exit lag.
- **The exception is grlex/wide64/eco-12 on F2's shipping F4.** In runs 11 and 16 of 20, one thread
  of a 15-thread team kept running beside the next full 16-thread team for 3 ms and 9 ms (one
  thread lived from 26.6 ms to 46.5 ms; R in 134 of its samples, S in 26). At those moments 17
  workers were computing.
