# Benchmarking and measurement

The benchmark suites, the examples that report algorithmic counters, and the rules this repository
follows before publishing a number.

## Measuring on a busy machine

For the cached monomial degree and packed order-key experiments, see the
[stage gate and reproduction commands](../research/monomial-degree.md). Build
`monomial_degree_profile` for a single-fixture stage/RSS report with the full basis on stdout,
or `monomial_packing` for the comparison-loop experiment. The cache was rejected for production;
the retained patch reproduces the measured cached arm without changing the public representation.

`tools/benchlock.sh` runs one command at a time, machine-wide, and records that it did:

```sh
tools/benchlock.sh <owner-tag> <command> [args...]

tools/benchlock.sh agentD cargo run --release --example univariate_scaling -- koalabear
```

Two concurrent measurements on one box contend for shared cache and memory bandwidth, so a ratio
taken while something else ran is not a measurement of the change. The script takes an exclusive
`flock`, appends `QUEUED` / `START` / `END` lines with the owner tag and a timestamp to
`$HOME/.zeebra/benchlock.log` (override the directory with `ZEEBRA_BENCHLOCK_DIR`; it must be
outside every worktree), and exits with the command's status so a failing measurement fails the
caller. Two records whose `START`..`END` windows overlap were not taken under this protocol —
unless both carry `lock=ccd:` with disjoint CCDs (see *Reserved CCDs* below) — and the log is what
says so — which is what makes figures taken weeks apart, such as the pre- and
post-#161 revisions in [`docs/research/graeffe-root-finding.md`](../research/graeffe-root-finding.md)
§4.4, comparable with each other.

The lock handles contention and nothing else. Also needed, per invocation:

- `CARGO_TARGET_DIR` inside the caller's own worktree and `RUSTC_WRAPPER=""`. The default target directory is keyed by package and profile rather than
  by checkout, so two worktrees overwrite each other's `libzeebra.rlib` and an example links
  against a library built from other source; the symptom is a missing export that is plainly
  present.
- A private scratch directory. Two callers' `tee run1.txt` collide, and a clobbered `tee` is a
  silently wrong figure rather than a crash.
- `timeout --signal=INT --kill-after=60s` on anything long, with a budget-killed run reported as a
  resource-limited result rather than as a measurement. A run left past its budget holds the lock
  against everyone else.
- A memory ceiling enforced by `tools/rss-guard.sh`, not by a hand-rolled `pgrep -f` loop. See
  below.
- **`setsid`, so the run survives its launcher.** See *Why a run ended* below.
- A build whose ISA floor actually survived. `.cargo/config.toml` is not inherited by a harness
  crate built outside this worktree, which is a third route to losing `-C target-cpu=x86-64-v3`
  with no `RUSTFLAGS` mistake to avoid (#352); `tools/benchlock.sh` lists it among the hazards the
  lock does not handle.

### Reserved CCDs: measuring beside builds

The exclusive lock asks the whole 128-thread box to be quiet even for a one-thread subject.
`tools/bench-reserve.sh` (#848) instead fences whole CCDs off with a cgroup cpuset. On the 5995WX
each CCD (8 cores plus their SMT siblings) has its **own** 32 MB L3, so a reserved CCD shares no
cache, no core and no scheduler placement with the builds on the other six. It does not fence DRAM
bandwidth, the Infinity Fabric, the package power budget (the boost clock of #827) or `system.slice`
daemons; *Calibration* below records what that leaves.

One-time root step (prints the commands; it never runs `sudo` itself):

```sh
tools/bench-reserve.sh setup   # a user@.service drop-in delegating `cpuset` to your user manager
```

After that, nothing needs root:

```sh
tools/bench-reserve.sh reserve          # CCDs 1-2: CPUs 8-23 + siblings 72-87, the M29 placement
tools/bench-reserve.sh status           # rc 0 reserved, 1 released, 2 failed read or not enforced
tools/bench-reserve.sh run zb-848 8-23 env RUSTC_WRAPPER="" timeout --signal=INT --kill-after=60s 1200 \
  "$CARGO_TARGET_DIR/release/examples/m29_cost_model" ...
tools/bench-reserve.sh release          # refuses while a reserved run is in flight; --force overrides
```

`reserve` restricts the user manager's `app.slice`, `background.slice` and `session.slice` (where
terminals, editors and every agent's `cargo` run) to the other CCDs, and `status` checks the
kernel's `cpuset.cpus.effective` against the recorded plan rather than trusting the state file.
`run` refuses unless `status` is `reserved` and the CPU list lies inside the reservation, then runs
the command in `zbbench.slice`, pinned with `taskset`, under `benchlock` with
`ZEEBRA_BENCHLOCK_CPUS` set. In that mode `benchlock` takes `benchlock.lock` **shared** plus an
exclusive `benchlock.ccd<N>.lock` per CCD the list touches: two runs on disjoint reserved CCDs
proceed together, a run on a held CCD queues, and an ordinary unscoped `benchlock` run still
excludes all of them. A reservation is `--runtime` and dies with the login session.

**A reservation is a machine-wide act.** It takes the reserved CPUs out of every other session's
cpuset — every agent, every terminal — so their builds lose a quarter of the box and a `taskset`
onto those CPUs fails with `Invalid argument`. That is not hypothetical: the calibration below
broke a concurrent #194 measurement pinned to CPU 10, which saw its cpuset change mid-run with no
explanation. So: reserve for a measurement session and `release` when it ends, never as a standing
state; an unscoped `benchlock` run now warns and records `reserved=<cpus>` on START while one is
up; and when a pin fails with `Invalid argument`, run `tools/bench-reserve.sh status` before
anything else.

Placement is part of a figure. A 16-worker run means 16 physical cores, CPUs 8-23 across CCDs 1-2
with their siblings idle — not one CCD's 16 hardware threads, which would pair every worker with
another on one core and measure something else.

#### Calibration

Measured at `faa015e6` (library source of `527a105e`), 2026-11-16/17; data, scripts and the full
tables are in [`research/bench-reserve/`](../../research/bench-reserve/README.md). Seven fresh
processes per cell, median wall against the reserved-and-idle arm A1:

| subject | builds, reserved | DRAM hogs, reserved | builds, **no fence** | idle again (A2) |
|---|---:|---:|---:|---:|
| MQ10, 1 worker (CPU 8) | 1.093x, spread 6% | 1.100x, 1% | 1.154x, 39% | 0.985x |
| MQ10, 16 workers (8-23) | 1.006x, 16% | 1.020x, 1% | 1.028x, 35% | 0.997x |
| Eco-12 wide, 16 workers | 1.056x, 19% | 1.114x, 4% | 1.095x, 48% | 1.000x |

(spread = (max − min) / median.) And an A/A test — the same binary twice back to back, nine pairs:

| subject | box | median wall ms | A/A ratio [min, max] |
|---|---|---:|---|
| MQ10, 1 worker | idle | 1074.7 | 0.997 [0.993, 1.025] |
| MQ10, 1 worker | builds on the other CCDs | 1197.1 | 0.998 [0.976, 1.007] |
| Eco-12 wide, 16 workers | idle | 3612.4 | 1.001 [0.994, 1.006] |
| Eco-12 wide, 16 workers | builds on the other CCDs | 3779.9 | 0.998 [0.987, 1.008] |

What that sets:

- **The fence is worth having.** Against no fence it cuts the run-to-run spread under builds from
  35–48% to 6–19%, and the median shift by 40–80%.
- **It does not make a reserved CCD a quiet box.** Absolute walls still move 1–11% with what the
  rest of the machine does, and DRAM traffic alone (arm D, load 13) costs as much as a full build
  load: the shared memory system, not cache or cores, is what is left. An **absolute figure for
  publication** — a baseline, a scoreboard row, a figure compared against one taken another day —
  still takes an unscoped `benchlock` on a quiet box.
- **Paired ratios survive.** An A/B with the arms interleaved pair by pair on a reserved CCD
  carries the same noise loaded as idle (worst A/A pair within 2.5% either way), because both arms
  share whatever the box was doing. That is the use reservation is for:
  deciding whether a change is faster while the rest of the machine keeps building. Quote the
  ratio, and label any absolute wall as taken beside builds.
- The ratio result does not call for a frequency cap. Cross-engine tables with serial comparands
  do, and *Fixed clock* below adds an opt-in one (#954). It is not yet qualified: its A/A
  validation is part of #968's calibration.

### Why a run ended

An `END` line names its cause, and **`end=exited` rather than `status=0` is what says a measurement
completed**. The distinction is not decorative. A 1.5-hour Anemoi run was killed at 3 177 s of a
5 400 s budget when the agent harness stopped the background shell that had launched it — taking
`benchlock`, `timeout`, `taskset` and the binary with it, since all four were its descendants — and
the log recorded:

```text
2026-11-06T20:01:47-05:00  END  zb-m25-anemoi  pid=2761621  status=0  elapsed=3177s  ...
```

`status=0`, a plausible `elapsed`, and no resource limit anywhere near being crossed. From the
lock's side the measurement had finished; the only clue otherwise was an output file holding eleven
header lines and no stage table. That consumed 53 minutes of a serialized mutex with three other
agents queued behind it *while reporting success*, and it made every historical `END status=0`
retroactively ambiguous — which matters because the resource policy authorizes bounded runs on the
grounds that a budget stop is observable and attributable, and it is not, if a budget stop and an
unrelated kill read the same (#344).

So the cause is now explicit:

| field | meaning |
|---|---|
| `end=exited` | the command ran and returned on its own; `status=` is its own status |
| `end=budget` | status 124, GNU `timeout`'s convention — a resource-attributed stop |
| `end=signalled-child(NAME)` | the command itself died of a signal; `status=` is 128+n |
| `end=launcher-signal(NAME)` | **the lock itself was signalled.** `status=` is forced to 128+n however the command exited, and `child=` keeps the command's own status visible |
| `launcher=gone` | the run outlived the process that launched it |
| `end=aborted`, `route=trap` | the `END` came from the `EXIT` trap, so the lock never reached its own last line and never observed the command return. Never `end=exited`, and `status=` is 128 rather than 0 |

`end=launcher-signal` is the one that closes the incident, and the override is the point: in that
run the child reported **0**, because an intermediate `bash run.sh` with no `set -e` exited on its
own last command after the binary beneath it had died. No exit status reaching the lock could have
been trusted, so a signal to the lock now outranks whatever the command said.

Two cases leave no `END` at all, both honestly. A signal arriving while a caller is still
**queued** leaves a `QUEUED` line and nothing else, which is right: no `START` means no window was
opened, so nothing later can look like it overlapped. And `kill -9` cannot be trapped, so it leaves
a `START` with no `END` — an unterminated window, unhelpful but not a claim that anything finished,
and the one case no script can prevent. Verified by process-group kill:

```text
kill -TERM  ->  status=143 end=launcher-signal(TERM) child=143
kill -HUP   ->  status=129 end=launcher-signal(HUP)  child=129
kill -USR1  ->  status=138 end=launcher-signal(USR1) child=138
kill -KILL  ->  (no END line)
```

`launcher=gone` is a note and not a failure, deliberately — `setsid` reparents a run to init on
purpose, so overriding the status on it would fail the very discipline being recommended:

```sh
setsid nohup bash run.sh > log 2>&1 < /dev/null &
ps -o pid=,sid= -p "$!"   # a session id that differs from this shell's is the confirmation
```

The lock does **not** call `setsid` itself. A detached run that nobody can cancel is its own
hazard, and that trade is worse than the one it would fix; so the lock records what happened rather
than preventing it.

`tools/test/benchlock-test.sh` covers the classification and reproduces the incident end to end —
benchlock in its own session, a measured command whose wrapper swallows the kill and exits 0, and a
signal to the whole process group — asserting that the resulting `END` is not `status=0`. It runs
in CI's `agent-scripts` job, in a throwaway `ZEEBRA_BENCHLOCK_DIR`, so it never takes the real lock
or appends to the real log.

### Enforcing a memory ceiling

```sh
tools/rss-guard.sh <comm> <id-substring> <ceiling-kb> [--poll <seconds>] [--once] [--wait <seconds>]
                   [--signal <name>] [--kill-pid <pid>] [--dry-run]

tools/rss-guard.sh anemoi_ladder anemoi17-cico-n6-fcico $((16 * 1024 * 1024)) --poll 10
```

`<comm>` is the binary's name as `/proc/<pid>/comm` spells it, truncated to 15 characters by the
kernel and by the script alike; `<id-substring>` is then confirmed against that pid's command line,
so a second concurrent run of the same binary on a different row is not watched. The mark read is
`VmHWM`, the high-water mark, so a peak that has already been released still counts.

**Do not find the process with `pgrep -f`.** A script created and run through a heredoc inside
`bash -c` — how agent sessions launch benchmark runs — has its entire text in the wrapper's
`/proc/<pid>/cmdline`, and `pgrep -f` matches the full command line, so it matches the wrapper on
its own payload. Observed live in #328 while one row was running and the next was still queued:
`pgrep -f` returned two `comm=bash` pids for the queued job and did not return the running binary
at all. The consequences were a monitor reporting queued work as running, and an RSS guard reading
a wrapper's ~4 MB high-water mark — which can never exceed a 16 GiB ceiling, so it silently never
fired and the run proceeded unsupervised while looking supervised.

Hence the exit statuses, which split three ways rather than two:

| status | meaning |
|---|---|
| 0 | watched to completion, the ceiling was never crossed |
| 3 | the ceiling was crossed and the signal was sent |
| 1 | **nothing matched — nothing was guarded.** Not a pass |
| 2 | a read of `/proc` failed |
| 64 | usage error, including a `<comm>` that names a wrapper (`bash`, `timeout`, `taskset`, …) |

Status 1 is the one worth the separate code: "watched and it was fine" and "watched nothing" are
the same output otherwise, and only the first is a guarded run. A guard started before its binary
waits `--wait` seconds (60 by default) for one to appear and then reports `NOT GUARDED` rather than
polling an empty process table forever.

When the launcher and the guard are in the same script, prefer neither form of matching: capture
the pid from `$!` and pass it with `--kill-pid`.

`tools/test/rss-guard-test.sh` covers the pure half against a synthetic `/proc` — including a case
where both wrappers' command lines contain the row id and only the binary is matched — and runs in
CI's `agent-scripts` job.

### Recording the CPU context of a multicore timing

A 16-worker burst holds the 5995WX at its all-core clock (about 3.99 GHz rather than 4.54) for
200–500 ms afterwards, and CCD placement moves serial-stage timings (#827). Both change a wall time
without changing the work. Since M29 (#834), a timing records its context beside the figure and is
**never** corrected for it. Process wall stays authoritative, and a clock-normalized figure is an
inference, not a measurement:

```sh
tools/cpu-context.sh 8-23   # one JSON line: load, each CPU's L3 domain/core/clock, governor, boost, compilers
```

Take a snapshot before and after each child, pin the child with `taskset` to the same list, and
publish the load, the number of L3 domains the list spans and the compiler count with the figure.
Compare a serial stage only between arms run in the same parallel context. The
M29 campaign ([`research/m29-baseline/costmodel.py`](../../research/m29-baseline/costmodel.py)) also
samples `scaling_cur_freq` every 25 ms during each child. `tools/test/cpu-context-test.sh` covers
the script against a synthetic `/sys` and `/proc`.

Fields added for M33 (#968). Fields are only added, never renamed or removed:

| field | meaning |
|---|---|
| `cpus[].min_khz`, `cpus[].max_khz` | `scaling_min_freq` / `scaling_max_freq` per listed CPU |
| `kernel` | `uname -r` (`/proc/sys/kernel/osrelease`) |
| `clock` | `boost`, `fixed@<MHz>` (boost off and one `scaling_max_freq` across the list), or `unknown` |
| `siblings` | SMT siblings of the listed CPUs that are not themselves listed |
| `stat[]` | raw `/proc/stat` jiffies `{cpu, role: bench\|sibling, busy, total}` for the list and its siblings |
| `rest_stat` | `{busy, total, cpus}` summed over every other online CPU |
| `rapl_uj`, `rapl_max_uj` | RAPL package energy and its wrap range; `null` when unreadable (energy is root-only by default) |
| `temp_mc` | `k10temp` Tctl, millidegrees C, or `null` |
| `runner_listeners`, `runner_workers` | counts of `Runner.Listener` / `Runner.Worker` (other repositories' self-hosted CI) |
| `benchlock_open[]` | `{owner, pid}` per `benchlock.log` START with no END whose process is still alive |
| `interval_busy_pct[]` | only with `--interval SECONDS`: busy % per listed CPU and sibling over the window |

`busy` is user + nice + system + irq + softirq + steal, and `total` adds idle and iowait. A busy
fraction is the difference between two snapshots, which is what `tools/bench_contamination.py`
computes.

### Measurement modes and contamination (#968)

Every M33 figure is taken in one of two modes (plan §11.2,
[`docs/MILESTONE-COMPETITIVE-BENCHMARKING.md`](../MILESTONE-COMPETITIVE-BENCHMARKING.md)):

- **dev**: decide whether a change is faster. CCDs 1-2 reserved, children pinned to physical CPUs
  8-23 with their siblings idle. Builds, tests and agents may run on the other CCDs. Quote paired
  Zeebra ÷ Zeebra ratios with an A/A control. A dev-mode absolute wall is never published as a
  competitive result.
- **publication**: Gate D and the competitive scoreboard. Same placement plus an exclusive
  `benchlock`, no compiler or linker process, no active `Runner.Worker`, and load under 4 on the
  non-bench CPUs. The clock is fixed if #954 qualifies, otherwise boost, recorded, and the same for
  every arm.

`tools/bench_contamination.py` holds the rules, so every runner journals the same verdict:

| rule | dev | publication |
|---|---|---|
| any SMT sibling of a bench CPU > 5% busy over the attempt (all of it is foreign) | contaminated | contaminated |
| bench CPUs in aggregate > 5% foreign: (busy − child's own CPU time) / total | contaminated | contaminated |
| bench median clock > 3% off the median of its group (in `bench-job`, one arm of one cell: instance, worker count, arm) | contaminated | contaminated |
| busy-CPU equivalents on the non-bench CPUs ≥ 4 | — | contaminated |
| a compiler/linker, a `Runner.Worker`, or another `benchlock` owner in either snapshot | — | contaminated |
| more than 20% of a session's attempts contaminated | session void, rerun whole | same |

Contaminated attempts are kept, flagged and excluded from verdicts. The thresholds are the plan's
starting values. Calibration may tighten them, and loosening one takes an owner decision on #965.
Bench CPUs are judged in aggregate because `/proc/stat` cannot attribute a CPU's busy time to a
process. Without the child's CPU time, the bench rule is skipped and the verdict notes it.

The runner's interface, per attempt and per session:

```python
import bench_contamination as bc            # tools/ on sys.path
m = bc.attempt_metrics(before, after, own_cpu_s=ru.ru_utime + ru.ru_stime)  # snapshots as dicts; ru from os.wait4
v = bc.attempt_verdict(m, mode="dev", session_median_khz=None, owner="zb-968")
#   -> {"contaminated": bool, "reasons": [str], "notes": [str]}
s = bc.session_verdict([m, ...], mode="dev", groups=[workers, ...], owner="zb-968")
#   -> {"attempts": [verdict...], "contaminated": n, "total": n, "void": bool, "median_khz": {...}}
bc.publication_refusals(snapshot, owner="zb-968")   # [] when publication mode may start
```

The same functions are available from the command line:

```sh
tools/bench_contamination.py attempt before.json after.json --own-cpu-s 9.8 --mode publication
tools/bench_contamination.py session metrics.jsonl --mode dev   # lines {"metrics": ..., "group": 16}; rc 1 void
tools/bench_contamination.py check --mode publication --cpus 8-23 --owner zb-968 --wait 3600 --poll 60
```

`check` exits 0 when the mode may start, 1 when it is refused (the JSON names each reason), and 2
when the snapshot failed. Dev mode always passes `check`: it records the context and refuses
nothing. Publication mode re-polls every `--poll` seconds until `--wait` runs out. Before the
first attempt nothing of ours is running, so `check` uses machine-wide `load1`, which is the
stricter reading.

Calibration is pending: an A/A and a 5% A/B on Eco-12 1 w and MQ10 16 w under idle, build,
memory-bandwidth and fixed-clock conditions, run as `bench-job` jobs (`research/m33-calibration/`). Until it
does, nobody has measured which conditions dev mode tolerates.

### Fixed clock (#954)

A serial process boosts to about 4.5 GHz, while a 16-worker run sits at the all-core clock. So a
Zeebra-16 ÷ comparand-1 ratio carries a frequency term of about 1.14x that has nothing to do with
the algorithm. `tools/bench-clock.sh` is opt-in and root-gated:

```sh
tools/bench-clock.sh status              # rc 0 fixed, 1 not fixed, 2 inconsistent
sudo tools/bench-clock.sh fix 3900       # boost off, min = max = 3900 MHz on CPUs 8-23,72-87
sudo tools/bench-clock.sh restore        # boost and every CPU's own min/max back
```

It runs only when you name a subcommand. `fix` and `restore` refuse without root (rc 77). `fix`
records the prior state in `/run/zeebra-bench-clock` before it writes anything. It rolls back a
write that fails or that the kernel clamps, and it refuses a second `fix` until `restore`. A fixed
clock is shared machine state, like a CCD reservation, so restore it when the session ends. A
reboot also clears it. `cpu-context` records the result as `"clock":"fixed@3900"`. Pick a figure at
or below the 16-worker all-core clock (about 3.99 GHz, #827).

Optional root step, so that a session does not need an interactive `sudo`. It is separate from
the script and fully reversible:

```sh
sudo install -D -o root -g root -m 0755 -t /usr/local/libexec/zeebra tools/cpu-context.sh tools/bench-clock.sh
echo "$USER ALL=(root) NOPASSWD: /usr/local/libexec/zeebra/bench-clock.sh fix *, /usr/local/libexec/zeebra/bench-clock.sh restore" \
  | sudo tee /etc/sudoers.d/zeebra-bench-clock
sudo chmod 0440 /etc/sudoers.d/zeebra-bench-clock && sudo visudo -c
# undo: restore if fixed, then
sudo rm -r /etc/sudoers.d/zeebra-bench-clock /usr/local/libexec/zeebra
```

Install a root-owned copy. A sudoers entry that names the checkout's own file would let anyone who
can edit the checkout run code as root. No boot-time unit is installed: the fix is per session, by
design. Reading RAPL energy as a user needs a similar step (`chmod 0444` on
`/sys/class/powercap/intel-rapl:0/energy_uj`, undone by a reboot). Until someone takes it,
`rapl_uj` stays `null`.
## Submitting a benchmark job

`tools/bench-job` (#967) turns a campaign into a job an agent can submit, leave and read back
later. It is not a service: the job is a directory, the result is its
[`StudyJournal`](../../tools/external/attempt_journal.py), and the runner is an ordinary process
under `bench-reserve run`. The manifest schema is in
[`docs/research/benchmark-schema.md`](../research/benchmark-schema.md) §7.

```sh
tools/bench-job submit manifest.json          # validates, copies binaries, queues; prints the job id
tools/bench-reserve.sh reserve                # the job runs inside a reservation
setsid nohup tools/bench-job run <job-id> > /buildcache/bench-jobs/<job-id>.log 2>&1 < /dev/null &
tools/bench-job status [<job-id>] [--json]     # queued, running, done, cancelled, failed, interrupted
tools/bench-job cancel <job-id>               # stops within 10 s (SIGINT to the child)
tools/bench-job resume <job-id> [--force-uncancel]
tools/bench-job report <job-id> [--json] [--baseline ARM] [--bound 1.05]
tools/bench-job scoreboard <job-id> [--scored ARM] [--references refs.json] [--attempt-digests d.json] \
    [--append research/competitive/results/history.json]
tools/bench-reserve.sh release
```

**Reading a report.** `report` renders Markdown (`--json` gives the same data) from the journal
alone, through `tools/bench_stats.py` (*Statistics and verdicts* below):

- **Provenance:** job id, mode, manifest and journal SHA-256s, each arm's commit, binary SHA-256 and
  build, cpus, reservation (CCD-scoped in dev mode, exclusive in publication mode), clock governor
  the clock rule's grouping (`arm`, or `cell` for a verdict written before #996) and the session's
  median clock per group.
- **Attempts:** counts by status, the contaminated count (#968), session void, and whether the job
  stopped before completing.
- **Wall and RSS, Stages, Scaling:** medians per instance, worker count and arm, over clean `ok`
  attempts only. Stages come from the child's `statistics.*_ns`. Scaling lists each arm's speedup
  over its fewest workers.
- **Ratios:** every arm ÷ the baseline arm (default: the first), paired per repetition, with a
  `regression_verdict` against `--bound`. Fewer than 9 pairs reads `stopped`.
- **Verification:** one basis digest per instance (`consistent`) or several (`DIVERGENT`), and
  every attempt that failed or was contaminated.

Contaminated attempts are listed and counted but never timed.

**Scoreboard.** `scoreboard` turns a publication-mode job into `CompetitiveRecord` rows. Each
instance needs a `competitive` block (`problem`, `problem_digest`, `family`, `task`, `field`,
`order`, `variable_count`), and each arm may name `library` and `library_version` (an arm without
`library` is a Zeebra arm). You get one row per instance, arm and worker count **that arm ran**: the
median of the clean attempts, or `failed` with no time. `--append` adds the rows to
`history.json`; then `cargo run --release --example competitive -- --write` re-renders
`COMPETITIVE.md`. Dev-mode jobs are refused.

- **Pairing.** The board pairs two rows only when `environment.commit` and `policy` are equal. Each
  competitor row therefore carries the commit of the **scored** Zeebra arm, and so does that arm's own
  row, and they share one policy. The scored arm is the job's only Zeebra arm, or the one named with
  `--scored`. Any other Zeebra arm's policy names the arm, so it never pairs by accident. A
  comparand's own version goes in `library_version`.
- **Invariants.** `--references refs.json` maps an instance to an independent reference:
  `{"basis_digest", "invariants", "checked_against"}`. A row is then timed only over the clean
  attempts whose basis digest equals the reference. It carries the reference's invariants and a
  `verification` block. If no attempt matches, the row is `failed`. An attempt's digest is the
  child's `basis_sha256`, or the entry for its id in `--attempt-digests digests.json` when the
  caller extracted the digest from output the child does not summarize (msolve, grobx). Without a
  reference, a row has no invariants: it renders but is never publishable.

**Nightly smoke.** `tools/bench-job-smoke.sh` runs submit → run → report → verify with 2 attempts
on katsura-4 in the nightly `Benchmarks run` job. Timing is ignored and no verdict is read.
GitHub CI has no performance gate. This repository has no self-hosted runner, and timings from
shared runners mean nothing. Performance campaigns stay local.

`run --next` takes the oldest queued job instead of a named one. Exit status: 0 the plan finished
(every attempt has an outcome, failures included), 3 refused (binary or input hash mismatch, or the
journal's aggregate budget), 4 cancelled, 75 already running, 64 a usage or manifest error.

**What submit refuses.** A binary whose SHA-256 differs from the manifest; a binary inside a git
checkout with uncommitted changes, or one at another commit; a build recipe that does not record
`git archive <commit>`; an argv template naming an unknown field. It copies each binary into the job
and re-hashes the copy before **every** attempt, and an attempt whose binary changed is refused with
a `binary-mismatch` stop record rather than run. A job never compiles.

**Comparands and per-solver inputs (#966).** An externally provisioned comparand (msolve's
tarball, a pinned grobx driver) records `build.comparand`, its provenance, in place of the
`git archive` recipe. An instance can carry one file per solver format in `inputs`, named in argv as
`{inputs[ms]}`, and an arm with its own `workers` list runs only at those counts.
`research/m33-baseline/campaign.py manifest` writes both M33-0 baseline jobs this way.

**Where jobs live.** `$ZEEBRA_BENCH_JOBS`, default `/buildcache/bench-jobs`. A root under `$HOME`
or this repository is refused (CLAUDE.md §1). `/buildcache` is root-owned, so the default needs a
one-time `sudo install -d -o "$USER" /buildcache/bench-jobs`.

```text
/buildcache/bench-jobs/
  queue                     "<iso-time> <job-id>" per submit, oldest first
  <job-id>/                 job id = first 12 hex of the canonical manifest's SHA-256
    manifest.json           canonical and immutable
    bin/<arm>/<binary>      the copies that run, mode 0555
    inputs/<instance>/...   copied instance files (`path`, and `inputs/<instance>/<key>/` per named input)
    journal/                StudyJournal: header.json (plan, limits), journal.jsonl, blobs/
    started                 pid and time of the first run; its absence means queued
    run.lock                flock held by the live runner
    current.json            the attempt in flight, with its start time
    cancel                  a cancel request for the live runner
```

**Attempts.** The plan is instances × workers × seeds in turn with the arms rotated one place per
repetition (`tools/bench_campaign.py` `plan`, the rotation M31-M32 used). Attempt *k* of plan index
*i* is `<job-id>:<i>:<k>`. Each runs as `taskset -c <first w CPUs of run.cpus> timeout --signal=INT`
under `rss-guard.sh` when `rss_bytes` is set, with a `cpu-context.sh` snapshot before and after.
The binary itself runs under GNU time (`/usr/bin/time -f %M`, or `$ZEEBRA_BENCH_TIME`), whose
`wait4` of the binary alone is `solver_peak_rss_bytes`, the peak the report and scoreboard use. The
runner's own `wait4` figure stays in `observed_peak_rss_bytes`. It is only a bound: the wrapper tree
is forked from the Python runner, and exec carries the forked image's high-water mark, so it never
reads below the runner's own RSS (about 31 MiB, #990). A journal without the solver figure, or a host
without GNU time, falls back to the tree's: the report marks it `≤` and the scoreboard labels its
basis an upper bound. The exit, raw stdout and stderr are journaled before the verdict (`ok`, `failed`, `timeout`,
`rss-limit` or `cancelled`), so nothing is parsed before it is durable.

**Resume.** An index with a recorded exit is never re-run: a SIGKILLed runner loses only the attempt
in flight, whose exit never became durable, and its child dies with it (`PR_SET_PDEATHSIG`). A
failed try is retried immediately while `run.retries` lasts, and every try is kept. A cancelled try
is re-run on `resume --force-uncancel`, which journals a `resume` record after the `stop` rather
than rewriting it.

**Modes.** `mode` is `dev` or `publication` and is recorded in the manifest and journal header.
A dev job runs under the CCD-scoped lock. A publication job takes the exclusive, machine-wide
lock (`bench-reserve run` with `ZEEBRA_BENCH_RESERVE_EXCLUSIVE=1`). Before its first attempt it
checks `bench_contamination.publication_refusals`, re-checking every 60 s for up to
`run.mode_wait_seconds` (default 0). If the conditions never hold, it journals a `mode-refused`
stop listing the refusals and exits 3.

Every attempt's exit metadata carries `contamination`, which holds `{mode, metrics, verdict}`.
The metrics come from the before/after `cpu-context` snapshots, with the child's `wait4` CPU time
as `own_cpu_s` and the sampled median clock. Snapshots that cannot be read give `verdict: null`
plus an `error`, never a clean verdict. The `complete` stop carries the session verdict:
`{version, grouping, contaminated, total, void, median_khz, flagged}`. That is where the clock
rule is applied, against the median of each arm within a cell (instance, worker count and arm;
`median_khz` is keyed `<instance>@<w>w/<arm>`). Solvers sample different clocks inside one cell:
grobx reads about 2.67 GHz beside Zeebra's 3.99 and groebner-rs's 4.54, while hardware cycle counts
put grobx at 4.09–4.16 GHz (#992). A cell-wide median therefore voided every mixed-solver M33
session on clock alone, with foreign load at 1.7% or less (#996). Version 2 groups per arm; a
verdict without `version` is version 1, grouped per cell (instance and worker count), and `report`
still reads it. The foreign and sibling rules are unchanged. The M33 sessions re-judged under
version 2 are in [`research/m33-clock-rule/`](../../research/m33-clock-rule/README.md).

A `cpu-context` snapshot costs about 0.5 CPU-s, and part of that cost falls inside the window its
`/proc/stat` reads bound. So the runner moves its harness (snapshots and frequency sampler) onto
the CPUs of `run.cpus` that the attempt does not use. When none are free, as at 16 workers on
8-23, it counts the harness's CPU time as the child's own (`harness_cpu_seconds` in the
metadata). That can hide at most that much foreign time.

Worked example: the M32 `walls` cell `wide64/katsura-9` on the dispatch entry point at one worker
(`research/m32-baseline/campaign.py`, arm `en:1`), from a `git archive` build:

```sh
C=31e334bda226d896686c64495867729119e52b0f
S=/buildcache/cargo-target/zeebra-967/src-${C:0:8}; mkdir -p "$S"
git archive -o "$S.tar" "$C"; tar -xf "$S.tar" -C "$S"
(cd "$S" && CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-967/target RUSTC_WRAPPER="" \
  cargo build --release --features research-sigf4 --example sig_f4_study -j24)
B=/buildcache/cargo-target/zeebra-967/target/release/examples/sig_f4_study
cat > /buildcache/cargo-target/zeebra-967/katsura-9.json <<JSON
{"schema": "bench-job-manifest-v1", "mode": "dev",
 "context": {"issue": 967, "agent": "$(scripts/agent/zb-claim.sh id)"},
 "arms": [{"name": "en", "commit": "$C", "binary": "$B", "sha256": "$(sha256sum "$B" | cut -c1-64)",
           "build": {"profile": "release", "flags": ".cargo/config.toml (x86-64-v3, fat LTO, 1 CGU)",
                     "recipe": "git archive $C | tar -x; cargo build --release --features research-sigf4 --example sig_f4_study"},
           "argv": ["--field", "{field}", "--name", "{name}", "--engine", "entry",
                    "--workers", "{workers}", "--wall-s", "180"]}],
 "instances": [{"name": "wide64/katsura-9", "params": {"field": "wide64", "name": "katsura-9"}}],
 "run": {"workers": [1], "cpus": "8-23", "repetitions": 9, "interleave": "rotate", "seeds": [0],
         "retries": 0, "limits": {"wall_seconds": 210, "kill_after_seconds": 60,
                                  "rss_bytes": 8589934592, "live_bytes": null}}}
JSON
tools/bench-job submit /buildcache/cargo-target/zeebra-967/katsura-9.json
```

`tools/test/bench-job-test.sh` covers submit refusals, plan determinism, SIGKILL and resume,
cancel, timeouts, retries and binary tampering with synthetic children and a fake reservation.

## Statistics and verdicts

New M33 campaigns read their ratios and verdicts through [`tools/bench_stats.py`](../../tools/bench_stats.py)
(standard library only) instead of copying an `interval()` into their `summarize.py`. Older
`summarize.py` files stay as published: they are evidence.

```python
import bench_stats as bs                       # sys.path.insert(0, 'tools') first
ci = bs.paired_ratio(bs.paired_ratios(cand_by_rep, base_by_rep), seed=f'{row} cand base')
bs.regression_verdict(ci, 1.05)                # Verdict(outcome, extend, reason)
ci = bs.independent_ratio(zeebra_ms, msolve_ms, seed=f'{row} msolve {w}')
bs.win_verdict(ci, anomaly=bs.msolve_anomaly(msolve_by_workers, w))
```

- **Paired** (Zeebra ÷ Zeebra): median of per-repetition ratios. **Independent** (Zeebra ÷
  competitor): median ÷ median, each side resampled on its own. Both are 95% percentile bootstraps,
  20,000 draws. An `int` seed is used as given and a `str` seed is its CRC-32. The same seed always
  gives the same interval.
- **Precision rule** (`precise`): the half-width, relative to the median, is at most half the
  distance from the threshold to 1.0. `relative=False` is the ratio-unit variant used by
  `research/m32-gate-s`.
- **Verdicts.** `win`: median < 1 and upper < 1. `loss`: lower > 1. `regression` /
  `no-regression`: upper vs the bound. `inconclusive`: the interval spans 1 or is imprecise.
  `stopped`: n < 9. `anomaly`: a win at a worker count where msolve's median exceeds 1.10× its own
  best. `extend=True` asks for the single predeclared extension (n = 9 → 12 more, pooled to 21). Pass
  `extended=True` on the pooled read so the verdict is final. A row under 300 ms (`small=True`)
  never wins.
- **Contamination.** `partition_contaminated` splits attempts on their `contaminated` flag. Report
  both counts. `session_void` applies the more-than-20% rule.

`tools/test/bench-stats-test.py` reprints published cells from `research/m32-qualification/` and
`research/m31-final/` through the module. Its replays must match to the printed digit.

## Which commit a figure came from

A measurement published under `docs/` states the commit it was taken at. The field has always
existed — `Environment::commit` (`grobner::record`), filled from `git rev-parse` — and the
gap was the prose, which recorded the machine, the pinning, the build flags and the lock and never
the commit (#335). The cost was concrete: #318 found a figure on record 1.2x faster than the same
measurement taken later, and "re-measure at the old commit" could not be *set up* from what was
written down.

So every document under `docs/research/` and `docs/MILESTONE-*.md` that contains a timing or memory
figure in a table carries a declaration in its header:

```text
**Measured at:** `93bb1c2`                    the commit the figures were taken at
**Measured at:** publication bound `x`…`y`    retrospective: at or before the commits that published them
**Measured at:** not measured here — <why>    every figure is quoted from a cited source
**Measured at:** unrecorded — <why>           genuinely unrecoverable, and said so
```

```sh
tools/check-measurement-provenance.sh            # all of docs/; rc 1 = a document with no era
tools/check-measurement-provenance.sh docs/research/f4-resource-scaling.md
```

The checker runs in CI's `agent-scripts` job. It exists rather than a convention because the M27
reproducibility checklist already asked for the commit and the documents still did not carry one.

A figure already published without its commit can usually be dated from git, which is where the
existing `publication bound` declarations came from:

```sh
git log -S "37 634.3" --format='%h %ad' --date=short -- docs/research/resultant-elimination.md | tail -1
```

That is an upper bound, not the measured tree, and it is labelled as one — never written into
`Environment::commit`, whose contract is the commit the run actually used. A commit is also not by
itself reproducibility: §6.5's figure does not reproduce at its own commit, because the session and
the ambient load moved it more than any code did, which is why `tools/benchlock.sh` records `load=`.
`docs/research/external-comparison-protocol.md` §10 is the authority on all of this.

## Benchmarks

Criterion benchmarks cover field arithmetic, sparse polynomial operations, dense and sparse linear
algebra, and Gröbner basis computation:

```sh
cargo bench                              # everything
cargo bench --bench grobner              # one suite
cargo bench --bench sparse_linear_algebra
cargo bench --bench f4_stages
cargo bench --bench f4_matrix_corpus     # elimination, one pinned real Macaulay matrix at a time
cargo bench --bench fglm                 # order conversion: stages, pipeline, strategies,
                                         # dependence, the shipped configuration, verification
cargo bench --bench polynomial_solving   # one solution against all of them, both routes
cargo bench --bench sparse_polynomial    # multivariate arithmetic, four arities
cargo bench --bench monomial_order       # MonomialOrder::cmp, three arms, two tie regimes
cargo bench --bench pow_strategy         # FiniteField::pow's body, five arms, six exponent widths
```

`monomial_order` is #317's gate rather than a coverage benchmark, and it has **three** arms where an
A/B would have two. It prices one change — storing a monomial's total degree instead of summing
`[u32; N]` on every graded comparison — and a two-arm first cut reported `lex` at 3.32x, on an order
that never reads the degree. So `production` is `MonomialOrder::cmp` on the real `Monomial<N>`,
`summed` is a bench-local transcription of it, and `stored` is that transcription with the degree in
a field; `summed` against `production` is the fidelity check, and the `lex` rows of `summed` against
`stored` are the control. See `docs/research/interreduction-cost.md` §3f.

`pow_strategy` is #181's gate, and the same shape for the same reason: `production` is
`FiniteField::pow` as shipped and the other four arms are bench-local transcriptions of the bodies
it could have — the recursive one it had, and three loops. It needs that many because the obvious
two-arm A/B gives the wrong answer. Making the default iterative is **1.9x** at the exponent widths
`PowerPermutation::invert` uses and a **9x to 40x regression** at `pow(1)` over a field whose
multiply is expensive, in the same change, because the loop seeds its accumulator with one and so
pays a multiplication the recursion does not. So `pow_limbs` walks the exponent downward below
`NARROW_EXPONENT_BITS` and upward above it, and `production` tracking whichever arm the threshold
selects is the fidelity check. `e8` and `e16` are in no call site and exist only to bracket the
threshold's crossover, which turns out to be field-dependent. Four arms also caught a candidate
that should have won on operation count and did not — `seeded` — which is the reason the arm
exists. See `docs/MILESTONE-LARGE-PRIME-FIELDS.md` §4.1.2.

The `small_exponent/.*/eval/` cells compare actual `Monomial::eval` with those same routes.
Production evaluation uses fixed addition chains through exponent five, retaining `pow` above
that range. The [evaluation study](../research/monomial-evaluation.md) records the before/after
gate and the rejected `#[inline]` hint; a local transcription's timing alone does not price a
production change.

`sparse_polynomial`'s `mul_dense` arm is separate from `mul` because they are different shapes, not
just different sizes. `mul` draws monomials independently, which is sparse in the total-degree sense
at every size; `mul_dense` builds the dense total-degree simplex, which is what the symbolic
resultant build actually produces and what selects the specialised bivariate multiplication route.
An arm of only the first kind cannot catch a wrong dispatch predicate.

`sparse_linear_algebra` has three groups, and the differences between them matter. `sparse_linalg`
times sparse row echelon beside dense *reduced* row echelon, which performs a back-substitution
pass the sparse side never does; it is indicative of nothing about storage and is kept only for
continuity. `matched_echelon` runs the identical algorithm under each `linalg::echelon` backend on
identical matrices, and times densification and sparsification in their own benchmark, so the
comparison measures representation rather than algorithm or conversion. `sparse_rref` times
`linalg::sparse::reduced_row_echelon`, whose back-substitution pass neither of the others covers,
on two shapes that answer different questions: a random square matrix, which at low density fills
in until it is near-dense and leaves the pass nothing to skip, and a banded matrix, which stays
sparse throughout and is where skipping is worth anything.

`f4_stages` times F4's stages separately — symbolic preprocessing, matrix construction,
elimination under each backend, representation conversion, and a whole batch — replaying the
batches a real computation produced rather than synthetic ones. `grobner` says whether something
got faster; `f4_stages` says whether a change removed cost or moved it from one stage to another.

`f4_matrix_corpus` is the per-matrix complement to it. `f4_stages` sums elimination over every batch
of four instances over one field under `F4Options::baseline()`, which is the right unit for "did the
stage get faster" and the wrong one for "which kernel is faster on which matrix": the shapes are
summed over, the field is fixed, and `baseline()` builds matrices the shipping default never builds.
This benchmark times **one named matrix at a time**, across six field types spanning five field
widths and three scaffolding regimes under both presets, with Criterion's throughput set from the matrix's nonzero count. Each
matrix is captured out of a live run through the `BatchObserver::matrix` hook — it is the object F4
handed to elimination, not a reconstruction — and is pinned by digest, so a benchmark here cannot
report a figure about a matrix that moved. See
[`docs/research/f4-matrix-corpus.md`](../research/f4-matrix-corpus.md).

Large matrices are explicit opt-in: `f4_matrix_corpus -- list-large` prints their pinned
metadata and budgets, `check-large` verifies their captures, and `check-all` verifies both sets. `BatchSelector::Prefix(k)`
runs through construction of batch `k`, then stops before its elimination; it does not compute a
complete basis. `CapturedMatrix::completed` distinguishes this from a full capture. Earlier
resource errors still fail the capture. To benchmark only the large set, use
`ZEEBRA_F4_LARGE_CORPUS=1 cargo bench --bench f4_matrix_corpus`. This skips the dense backend and
holds at most one setup clone per iteration; sparse/adaptive arms that exceed the entry allowance
are reported as refusals. Capture success does not promise that elimination fits the same budget. The ordinary `walk_corpus` and CI benchmark smoke exclude
these entries. Use the benchmark lock, a process memory guard and a timeout when capturing them.

Wall-clock time alone does not say *why* a Gröbner computation got faster. For the algorithmic
counters — pairs considered, pairs eliminated by Buchberger's first criterion, reductions, zero
reductions, basis size:

```sh
cargo run --release --example grobner_statistics   # Buchberger
cargo run --release --example f4_statistics        # F4, beside Buchberger
cargo run --release --example f4_profile           # F4, cost attributed per stage
cargo run --release --example f4_profile -- list   # the configurations available
cargo run --release --example f4_profile -- shipped  # the same, under F4Options::recommended() (#614)
cargo run --release --example f4_memory            # F4, memory attributed per structure
cargo run --release --example interreduce_working_set -- katsura-11 --arm unbounded
cargo run --release --example f4_degrees           # F4, work and useful work per degree
cargo run --release --example f4_schedule          # critical-pair order, and batch size, apart
cargo run --release --example f4_schedule -- list  # the instances available
cargo run --release --example hilbert_study         # the semiregular model against the measurement
cargo run --release --example hilbert_driven        # a predicted cap against a cap chosen without one
cargo run --release --example hilbert_driven -- list
cargo run --release --example m22_ablation          # every M22 strategy, one table per instance
cargo run --release --example m22_ablation -- list
cargo run --release --example f4_blocks            # F4, row arrangements of the Macaulay matrix
cargo run --release --example f4_matrix_corpus -- list     # the pinned matrix corpus
cargo run --release --example f4_matrix_corpus -- check    # capture it and verify every digest
cargo run --release --example f4_matrix_corpus -- pin      # re-derive the pinned table
cargo run --release --example f4_matrix_corpus -- predict  # does the corpus rank kernels as a run
cargo run --release --example f4_selection         # reducer selection and the reducer cache
cargo run --release --example elimination_density  # how dense an F4 matrix really is
cargo run --release --example block_density        # dense 64x64 tiles in the corpus, and in D - C A^-1 B
tools/benchlock.sh zb-803 taskset -c 8 target/release/examples/block_density split mq-random-10  # timed phase split
cargo run --release --example accumulator_span     # whether a vectorizable inner loop is available
cargo run --release --example accumulator_span -- list
cargo run --release --example boolean_density      # what a GF(2) entry costs, at two field widths
cargo run --release --example boolean_density -- 6 8
cargo run --release --example gf2_packed_elimination -- f4 5      # bit-packed GF(2) vs generic, F4 matrices
cargo run --release --example gf2_packed_elimination -- square 5  # Four Russians crossover
cargo run --release --example gf2_f4_dispatch -- batches 5        # packed vs generic F4 batches
cargo run --release --example gf2_f4_dispatch -- sweep 5          # same, MQ n=12..16 x density grid
cargo run --release --example gf2_f4_dispatch -- solve 7          # packed vs generic F4 solves
cargo run --release --example sat_algebra -- clauses             # ANF->CNF clause blow-up (#220)
cargo run --release --example sat_algebra -- replay 3            # GF(2) F4 matrices vs CryptoMiniSat Gauss
cargo run --release --example sat_algebra -- preprocess 3        # kissat with and without affine elimination
cargo run --release --example pair_criteria        # what each pair criterion discards, F4
cargo run --release --example pair_criteria -- buchberger
cargo run --release --example certification_criteria  # what they discard from a certification pass
cargo run --release --example certification_criteria -- list
cargo run --release --example f4_ablation          # every configuration, one table
cargo run --release --example f4_milestone         # both engines, at matched and default criteria
cargo run --release --example fglm_baseline        # which systems are zero-dimensional, and what
                                                   # a lex basis costs against a grevlex one
cargo run --release --example fglm_baseline -- cyclic-6   # one system per process
cargo run --release --example fglm_operators      # how sparse the multiplication operators are
cargo run --release --example fglm_conversion      # the FGLM pipeline against direct lex F4
cargo run --release --example fglm_profile         # where a conversion's time and memory go
cargo run --release --example fglm_profile -- katsura-7   # one system per process
cargo run --release --example fglm_border          # what deduplicating the border is worth
cargo run --release --example fglm_parallel -- per-batch   # is the border reduction worth
cargo run --release --example fglm_parallel -- sweep       # parallelizing? one table each
cargo run --release --example fglm_storage         # operator representations, stored and applied
cargo run --release --example wiedemann_conversion # certified scalar route versus classical
cargo run --release --example sparse_matvec_throughput -- --quick # matvec per field, width, threads
cargo run --release --example fglm_shape           # shape position, and what that route would save
cargo run --release --example fglm_ablation        # every strategy combination, one table
cargo run --release --example fglm_ablation -- list
cargo run --release --example solve_one            # systems in, verified solutions out, both routes
cargo run --release --example solve_baseline       # both routes with resources and outcome class
cargo run --release --example solve_auto           # four policies against an offline best-of-two
cargo run --release --example strategy_selection   # #273: every route per instance, time and memory winners
cargo run --release --example specialize_slices    # seeded slices of an underdetermined system
cargo run --release --example field_width          # what a 4-byte field element is worth, per
cargo run --release --example field_width -- axpy  # arm: the kernel, a dense echelon, F4
cargo run --release --example field_reduction      # #270: every reduction per field width, one
cargo run --release --example field_reduction -- 64  #   build, oracle-checked first (32, 64, 256)
cargo run --release --example univariate_scaling   # univariate cost and memory against degree
cargo run --release --example univariate_scaling -- list
cargo run --release --example ntt_access           # #591: is the NTT access-bound or
                                                   #   arithmetic-bound? Needs a quiet box
cargo run --release --example ntt_access -- goldilocks budget=30
cargo run --release --example ntt_access -- list
cargo run --release --example univariate_scaling -- points=250,500,1000,2000   # lagrange only, exact counts
cargo run --release --example karatsuba_crossover  # Karatsuba against schoolbook, per field width
cargo run --release --example karatsuba_crossover -- bn254
cargo run --release --example division_crossover   # Newton inversion against long division, per field width
cargo run --release --example division_crossover -- bn254
cargo run --release --example division_crossover -- all max_log=13
cargo run --release --example subproduct_crossover  # the subproduct tree against the quadratic forms
cargo run --release --example subproduct_crossover -- bn254
cargo run --release --example transform_tree_ab -- all   # #606: transform-kernel subproduct tree vs its Karatsuba control
cargo run --release --example transform_tree_ab -- koalabear sizes=13123,16384 thresholds=256,1024 reps=5
cargo run --release --example multiplication_dispatch  # schoolbook vs Karatsuba vs transform, and the crossings
cargo run --release --example multiplication_dispatch -- koalabear max_log=17
cargo run --release --example multivariate_mul     # multivariate multiply: time and live heap per route
cargo run --release --example multivariate_mul -- chunk         # block size sensitivity
cargo run --release --example multivariate_mul -- max_degree=90 # stop short of the six-round size
cargo run --release --example graeffe_root         # Graeffe root finding, stage by stage, against `roots`
cargo run --release --example graeffe_root -- deflate   # all roots by deflation, #351
cargo run --release --example graeffe_root -- list
cargo run --release --example graeffe_root -- goldilocks degrees=256,1024,4096   # where the method does not pay
cargo run --release --example batch_inversion      # batch inversion: routine, integration,
cargo run --release --example batch_inversion -- f4   # and the F4 headroom left alone
cargo run --release --example competitive          # render research/competitive/ from its history
cargo run --release --example competitive -- --write   # and update COMPETITIVE.md in place
cargo run --release --example competitive_sweep -- --list   # corpus x engines x tasks, exploratory
cargo run --release --example zeebra_driver -- REQUEST.json   # one fresh-process Zeebra solve from a
                                                   #   comparand request (#820); F4 capped at `workers`
. tools/external/env.sh                            # REQUIRED FIRST, or the sweep sees one engine
tools/benchlock.sh runner cargo run --release --example competitive_sweep -- \
    --row katsura-6 --task reduced-grobner-basis --measure --write   # one measured row
tools/benchlock.sh runner cargo run --release --example competitive_sweep -- \
    --characteristic 32003 --row katsura-6 --task reduced-grobner-basis --measure --write
                                                   # the same rung at the corpus's other identity;
                                                   #   only a PUBLISHED characteristic is accepted
tools/benchlock.sh runner cargo run --release --example competitive_sweep -- \
    --row mq-random-10 --task reduced-grobner-basis \
    --interreduction matrix --measure --write      # a row under a non-default F4 route; the route
                                                   #   lands in the row's library_version, because
                                                   #   the commit does not determine it (#507)
cargo run --release --example interreduction_routes            # both interreduction routes per
                                                   #   ladder rung, interleaved in one process,
                                                   #   with the matrix route's own verdict
cargo run --release --example interreduction_routes -- --orders --wall 60 katsura-6
                                                   # the same rung under grevlex, grlex and lex —
                                                   #   where the two routes disagree (#507 §3e.2)
cargo run --release --example interreduction_repeats           # the division route's repeat rate:
                                                   #   reduction steps whose work an earlier
                                                   #   element's reduction already did (#569).
                                                   #   Counts, not durations — load-independent
cargo run --release --example interreduction_repeats -- katsura-6 --order lex
                                                   # the same on the one path the division route
                                                   #   still ships on under the default
cargo run --release --example heap_division     # DivisionRoute::Heap against the merge route,
                                                   #   interleaved, on FGLM border reduction, lex
                                                   #   interreduction and mq-random-10 (#562 §3j)
tools/benchlock.sh agentD cargo bench              # anything measured, under the exclusive lock
cargo run --release --example determinant_sweep    # the Sylvester determinant cost law,
                                                   #   five matrix orders, fitted with residuals
cargo run --release --example determinant_sweep -- --cost-only   # what the sweep would cost
cargo run --release --example determinant_sweep -- --kernel euclidean   # the O(n^2) kernel
cargo run --release --example determinant_width    # the width sweep 1..32 and the kernel split,
                                                   #   every arm in one process (#412)
cargo run --release --example determinant_width -- --count-allocations   # calls per determinant
cargo run --release --example determinant_width -- --compare-kernels --order 162 --width 32
                                                   # dense and Euclidean, same samples and width
cargo run --release --example f4_profile -- mq     # the competitive MQ instance, per stage
cargo run --release --example f4_profile -- mq-instance   # that instance as canonical text
cargo run --release --example f4_profile -- divmask       # #331: the divisor-mask counters
cargo run --release --example f4_profile -- symbolic-split  # #585: what share of symbolic
                                                   #   preprocessing the divisor search is
cargo run --release --example f4_profile -- mq-rows      # #477: reduced row echelon per batch
cargo run --release --example f4_profile -- scatter       # #582: the row scatter, split four ways
cargo run --release --example f4_profile -- handles       # #621: handles against the hash read
cargo run --release --example column_sort_routes   # #583: the column sort, stable against unstable
timeout 900 cargo run --release --example buchberger_reach -- katsura-6 lex all
```

`solve_baseline` is M21-0's baseline: both routes on every corpus system, reporting what each
*cost* and which of the mathematically distinct outcomes it reached — a verified point, no
base-field point, an inconsistent ideal, a positive-dimensional ideal, or a crossed budget. It
takes about 30 seconds, nearly all of it katsura-7's direct-lex attempt failing. See
[`docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md`](../MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md)
§4 for the table and what it decided.

`f4_statistics` prints matrix dimensions, how many reductions each matrix absorbed, how much of
each matrix was reduction scaffolding, and how much elimination filled it in. It asserts that the
two engines agree wherever both can run. It pins itself to `F4Options::baseline()`, because its
columns are the ones `docs/MILESTONE-F4.md` §7.1 records and comparing against them needs that
configuration.

`f4_profile` prints where the time went: symbolic preprocessing, construction, elimination,
candidate extraction, and the final interreduction, with the remainder shown as `other` so an
unattributed cost cannot hide. It takes the name of a configuration — `baseline` by default,
`recommended` for what `F4Options::default()` is — so the effect of one optimization can be read
off against another's. The timing comes from
`F4Options::measure_stages`, which reads a clock four times per batch and is off by default. Three
modes take no configuration: `mq` is the digest-pinned `mq-random-10` stage split (#349),
`mq-instance` prints that instance's canonical text — field, order, variables and generators, the
bytes the identity digest is taken over — so an external engine's own counters can be taken on the
same ideal and compared against these columns, and `construction` splits the construction stage
four ways (#330): the distinct-monomial set, the column sort, the monomial-to-column map, and the
row scatter, then measures the current route against the one it replaced in one process on one
build. `docs/research/groebner-jl-gap.md` is what the `mq-instance` comparison produced;
`docs/research/msolve-implementation.md` §4.1 is what the `construction` split settled.

`scatter` goes one level further in (#582), because the `construction` split left the scatter at
89% of the stage and no counter had ever been inside it. Two of its four parts are clocked —
`scatter_rows`, the per-row loop, and `scatter_assemble`, `SparseMatrix::new` plus the
row-provenance copy. The other two, the multiplier shift and the per-term column lookup, are per
*term*, where `Instant::now()` costs more than the work it would time; they come from
`ScatterPrefix`, a **nested ablation** whose arms are prefixes of the real loop and whose adjacent
differences are one step's cost. The full arm is that loop verbatim, so the table prints it
beside the clocked `scatter_rows` as a control: if those two disagree, nothing beside them means
anything. Each arm carries a checksum that an emptied arm cannot produce
(`test_the_scatter_ablation_arms_do_the_scatters_work` pins each one to a quantity derived from the
built matrix), the arm order rotates per repetition, and each arm is min-reduced over its own runs.

Since #621 the loop those arms describe is **not** the shipping one, so the mode clocks
`MacaulayMatrix::build_hashed_scatter_for_benchmark` rather than `build_measured` and keeps
reporting what #582 reported. `handles` is the A/B between the two. Symbolic preprocessing interns
every shifted row monomial to deduplicate its own work queue, so it now assigns each a handle — an
index into a first-appearance arena — and `Preprocessed` carries the handle of every row term in one
flat vector. Construction inverts the column sort's permutation into an array keyed by handle, and
the scatter reads a column by indexed load: no monomial is formed and no hash is probed. Both arms
read the same `Preprocessed`, built once per batch outside the timing, and every pair of matrices is
asserted equal. The table's `entries/col` column is the ratio #621's kill criterion rested on,
because the per-entry lookup can be removed at most once per entry.

`column_sort_routes` is the smallest of these questions and the last of #583's: whether
construction's column sort should be stable. It replays a `recommended` trace, snapshots the column
vector each batch hands the sort — `preprocessed.monomials`, which is what construction itself
collects — and sorts the same snapshot both ways, interleaved with the arm order
rotated and each arm min-reduced. The arms assert **equal output** as well as timing it, because
stability can only matter where the comparator reports a tie and a figure for two different column
orders would mean nothing. `sort_unstable_by` wins on every instance tried, so it is what
`build_measured` now calls; `docs/research/msolve-implementation.md` §4.1 has the table and what it
decided about the rest of #583.

A third configuration-free mode answers a question rather than reporting a cost. `f4_profile --
divmask` is #331's counter-only experiment: `F4Options::measure_divmask` builds a 32-bit divisor
mask with thresholds calibrated from the input's own exponent range and replays every divisibility
test in symbolic preprocessing against it **after** the real answer is known, so nothing a mask
could get wrong can reach the basis — asserted element for element by
`test_the_probe_does_not_change_the_divisor_selected`. It reports the tests performed, how many
answered negative, and how many of those a mask would have settled without an exponent comparison,
which is 94%–97% on every instance tried. The run pays a second walk of the basis per divisor
lookup, so **its durations are not quotable**; the counters are exact and machine-independent,
which is the trade `count_interreduction` already makes. See
`docs/research/msolve-implementation.md` §4 H2 for the result and what it does and does not bound.

`f4_profile -- symbolic-split` is the other half of that question, and the half that settled it.
`divmask` counts the tests a mask would answer; `symbolic-split` prices them, by multiplying
`divisor_scan_steps` — exact, and free, because the shipped scan increments it once per
divisibility test — by a per-step cost taken from timing `MonicBasis::find_divisor_with` over a
real basis and dividing by the steps that same scan reports. It prints a **range**, because a
negative answer exits early and a positive one compares every variable, and it labels its own
output a projection rather than a measurement. The answer is a null result: the divisor search is
2.5%–4.7% of `symbolic` on three of four instances and 24%–30% on the fourth, which bounds even a
*free* mask at under 6% of one run and under 1% of the other three. §4 H2 has the table and why
#585's stage 2 was closed rather than built.

`f4_memory` is the same question for bytes rather than for time, and it exists because the answer
turned out not to be the matrix. It runs a tracking `#[global_allocator]` beside the solver's own
counters, measures each batch's symbolic preprocessing and matrix construction on the batches F4
really selected — including the batch that is **refused**, which no `F4Statistics` field describes —
and prints each named structure's share against the measured peak, on katsura-6, katsura-7 and
cyclic-6. After symbolic preprocessing succeeds, a construction refusal also prints the exact
row, column and entry demand, the entry allowance and its excess. These are construction counts;
they do not predict elimination fill-in or the process's peak RSS.

`interreduce_working_set` is that question for the *final interreduction*, which `f4_memory`'s
per-batch probe does not reach. It runs **one rung and one arm per process**, because peak resident
size is a per-process reading: `--arm unbounded` lifts the live-entry allowance so the matrix pass
runs to completion and reports its elimination's own high-water mark, `--arm default` is the shipped
allowance where that pass refuses and falls back, and `--arm division` is the comparand the memory
ratio is against. It is the instrument [#536](https://github.com/mfaulk/zeebra/issues/536) was
settled with; `docs/research/f4-resource-scaling.md` §12 has the table it produced. `--arm tails`
is `unbounded` with `F4Options::tail_only_interreduction` (#808), and `--echelon-batches` turns
`reduce_batch_rows` off, the regime #536 was measured in. Each row prints a `basis digest`, so arms
run in separate processes can be checked for agreement; `docs/research/interreduction-cost.md` §3k
has that A/B.

`interreduction_repeats` asks a third question about the same stage, and it is a **count** rather
than a measurement: how much of the division route's work is work an earlier basis element's
reduction already did. It replays the basis entering the stage — the last traced batch's basis plus
that batch's candidates — and reports, per reduction step, whether the
`(quotient monomial, reducer leading monomial)` pair recurred and whether the reducer's tail was
unchanged, which is the only case a cache could have served. Two input arms per rung, with
`reduce_batch_rows` the only difference, because the input decides the stage. Because the output is
operation counts and not durations it is **exact, deterministic and load-independent**, so it needs
no interleaving and no quiet machine — it runs under `tools/benchlock.sh` out of politeness rather
than for validity. It settled [#569](https://github.com/mfaulk/zeebra/issues/569), the last
unadjudicated candidate mechanism from #436: the repeat rate is **98.57%** and the verdict is still
not to build the cache, for the reasons in `docs/research/interreduction-cost.md` §3i.

`f4_degrees` is M22-0's baseline: one table per system giving, for each lcm degree, the pairs
selected and discarded, the split of matrix rows into reducer scaffolding and pair halves, **the
rank the pair rows added on top of the reducer block**, the pair rows that added nothing, the
largest matrix, the elements extracted, and how many of those came out below the degree that found
them. It covers katsura-5 for calibration, then katsura-6, cyclic-5, cyclic-6 and a planted
eight-variable system.

`m22_ablation` is M22-I's: the whole M22 strategy matrix on one table per instance, over the
corpus of §11.2 — katsura-5/6/7, cyclic-5/6, a planted system, a nonradical ideal, a
positive-dimensional one. Every row's basis is **asserted** equal to the baseline's and certified, since a differing
basis is a defect and a column reporting one would bury it. `total ms` is solve plus certification,
which is the only figure a default decision may use. Variable order is held fixed at the generated
layout throughout — M22-E measured it at 1.6x–1.7x, which would otherwise be attributed to whichever
F4 strategy varied alongside it. There is no mutant row, because M22-D added no mutant mode; `D = A`
is printed to make the gap explicit. See
[`docs/MILESTONE-DEGREE-AWARE-F4.md`](../MILESTONE-DEGREE-AWARE-F4.md).

`hilbert_study` is M22-B's measurement: the exact Hilbert function of each computed basis's
leading-term ideal against the semiregular prediction, degree by degree, with the first
disagreement and its sign reported. It covers textbook regular sequences, random homogeneous
quadratics, deliberate counterexamples, the Fukuoka type III top forms *and* the published
inhomogeneous instances, and reduced-round Poseidon. See
[`docs/research/hilbert-functions.md`](../research/hilbert-functions.md) for the tables.

`f4_schedule` is M22-A's measurement: every compiled critical-pair order on one table per
instance, with the computed basis asserted equal to the baseline's on every row. Ordering and batch
sizing get a table each, deliberately — a sort and a cap varied together cannot be attributed —
plus a cross product on one instance to check whether the two interact. `-- list` names the
instances and `-- <name>` runs one per process.

`f4_blocks` replays the batches a computation really built and eliminates each one four ways —
rows as preprocessing produced them, reducer rows first, reducer rows taken as established pivots,
and the same with the reducer block interreduced — reporting row operations, peak live nonzeros,
final nonzeros, and time on the identical matrices. Holding the matrix fixed is the point: a
change of row arrangement changes which candidates come out, hence every later batch, so the
whole-computation effect and the per-elimination effect are different measurements.

`elimination_density` reports the density a representation policy would have to read: the
distribution of row densities as built and at each row's own peak during its reduction, the density
of the densest 64x64 blocks, and the three backends' elimination times with representation
conversion in its own column. A global density of a fraction of a percent says nothing about
either. A last table divides each backend's time by the `row_operations` it reported, which is the
per-operation cost a change inside a row operation has to move, and states the pivot index's
storage at the instance's widest matrix. `-- list` names the instances; the largest are excluded by
default, because a dense representation of katsura-7 grevlex is 374 MB for a matrix holding 112k
entries.

`block_density` asks the GPU-tile question of the pinned matrix corpus rather than of a fixed
instance list (#225; `docs/research/gpu-f4.md`). For each entry it tiles two matrices into 64x64
cells: the matrix as built in the structured `[A B; C D]` arrangement, and the pair-row residual
`D' = D - C A^-1 B` on the columns no reducer leads — the block a Faugère–Lachartre split would hand
a dense kernel — before and after that residual's own echelon. It reports the fullest tile and the
share of nonzeros lying in tiles at least half full. Nothing is timed, so every figure is exact and
needs no benchmark lock; `-- large` walks the explicit large captures instead.

`block_density -- split <label substring>` (and `split-large`) is its one timed mode (#803;
`docs/research/residual-split.md`), so run it under the benchmark lock on a pinned core. Per entry
it interleaves six arms: the production batch (echelon, then the candidate-only backward pass), the
full-RREF route, the forward pass alone, the reference sweep producing `D'`, the echelon of `D'`,
and the Faugère–Lachartre order (sweep, then reduce `D'` only), and it asserts that the last arm's
candidate rows equal production's coefficient for coefficient. With `--features research-work` it
also prices the sweep at the forward pass's own ns per coefficient product; take times from a stock
build, since those hooks sit in the hot loop. An entry whose elimination crosses its own capture
budget is reported as refused and then timed unbounded.

`block_density -- residual-work <label substring>` (and `residual-work-large`; #86, needs
`--features research-work`) is untimed. It counts the shipped backend's coefficient products and
dense-row cell traffic on the echelon and back-substitution of `D'` alone, beside the sweep's exact
count and the dense model's, so it needs no benchmark lock.

`gpu_kernel_census` is #86's instrument (`docs/research/gpu-kernel-classification.md`). Its
`ceilings` mode times the shipped elimination step `acc[c] -= v * factor` per field, with the pivot
entries resident in L2, L3 and DRAM, against a contiguous L1 loop and one core's streaming read.
That separates arithmetic-, index- and bandwidth-bound fields. `f4 --system S --field F --workers W`
runs one public system (Katsura, Cyclic, seeded MQ) over GF(2^31-1), Goldilocks, BN254 Fr or
`Gf256Mq` with stage clocks. Add `--work` (with `--features research-work`) for the entry census
that gives logical bytes per product. `research/gpu-kernels/run.sh` drives both, timing under the
benchmark lock, and `research/gpu-kernels/analyze.py` prints the tables.

```bash
cargo run --release --example gpu_kernel_census -- ceilings --reps 5
cargo run --release --features research-work --example gpu_kernel_census -- \
  f4 --system katsura-9 --field bn254 --workers 1 --work
```

`accumulator_span` answers whether the shipped elimination backend has a loop a SIMD kernel could
go in. `Backend::Adaptive`'s inner operation walks the *pivot's* sparse entries and indexes a dense
buffer, which is a gather and a scatter; the only contiguous alternative updates the pivot's whole
span `[leading_column, trailing_column]`, and `span / support` is the extra cell updates that would
cost. The harness reports that multiplier weighted by row operations, the share of row operations
whose span is too short to fill a vector, the occupancy of the pivot within its span by decile, and
an accounting of all three of the accumulator's loops so the two that are *already* contiguous can
be sized. Everything is reported for **both reduction strategies**, which matters more than it
sounds: the two do not see the same matrices, and the multiplier is 4.04x under the baseline
against **9.81x** under the one `F4Options::default()` runs. It is a property of the matrices rather
than a timing, so it reproduces exactly and needs no exclusive lock — and it is self-checking: for
every matrix it also runs the real backend, split form included, and asserts its replay applied the
same pivots, by `row_operations` and `pivot_inversions`. The answer, measured, is **no** — see
[`docs/MILESTONE-SIMD-PARALLELISM.md`](../MILESTONE-SIMD-PARALLELISM.md) §10.

`boolean_density` answers what a `GF(2)` coefficient costs to store, which is #218's last open
question. A sparse entry is `(usize, F)` and the index's alignment pads it to **16 bytes at any
field width**, so over `GF(2)` it is 16 bytes carrying one bit — a factor of 128, and a
representation cost rather than an arithmetic one. The harness eliminates the *same* structural
system at two field widths — random quadratics with `x_i^2 - x_i` adjoined, which over `GF(2)` are
the field equations and are asserted to be — and reports entries, peak live entries, row operations
and per-backend times for each. The counts are exact and reproduce bit-for-bit; the measured
surprise is that `GF(2)` needs about **half** the entries and half the row operations of the wide
field on the same system, because `a + a = 0` makes cancellation far more frequent. So `GF(2)` is
already cheaper in memory — by entry count, not entry size. It also runs all three elimination
backends over characteristic-two matrices and asserts they agree, which
[`docs/research/boolean-solving.md`](../research/boolean-solving.md) §15 explains had never been
checked.

`gf2_packed_elimination` is #272's instrument: it collects every matrix F4 eliminates for
characteristic-two systems and times the generic sparse `reduced_row_echelon` over `Zp2` against
`linalg::gf2`'s bit-packed Gauss-Jordan and Four Russians kernels, asserting every packed RREF equal
to the generic one, and projects the end-to-end effect from F4's measured elimination stage.
`square` sweeps dense square matrices for the Four Russians crossover. Results and the decision are in
[`docs/research/characteristic-two-linear-algebra.md`](../research/characteristic-two-linear-algebra.md).

`gf2_f4_dispatch` is #777's instrument for the packed route wired into F4: `batches` replays
every batch of the #272 families under `Gf2Elimination::Generic` and `Packed` and prints each
batch's shape, density and both elimination-stage times (what `Auto`'s thresholds were read from);
`sweep` does the same over random MQ at n = 12..16, square and overdetermined, at five
quadratic-monomial densities on a held-out seed (#794); `solve` times whole solves under `Generic`, `Auto` and `Packed`. Candidates and bases are asserted
equal to the generic route's in every repetition. Results are in
[`docs/research/characteristic-two-linear-algebra.md`](../research/characteristic-two-linear-algebra.md) §7.

`sat_algebra` is #220's instrument for the SAT decision record. `clauses` counts the CNF an
ANF→CNF conversion emits (Tseitin ANDs, XORs cut at 3–6) for planted random MQ systems and for the
Macaulay rows a real `GF(2)` F4 run builds. `replay` eliminates every one of those matrices with
`Dense`, `Sparse`, `Adaptive` and the bit-packed kernel, exports each as XOR constraints, and has
CryptoMiniSat solve them; rank and solution-space dimension are asserted equal to CMS's before any
time is printed. `preprocess` times kissat on a planted system with an affine layer, alone and after
`transform::eliminate_affine`, and checks every model against the original equations. The solvers
are external oracles from `tools/external/provision-sat.sh`, found through `$ZEEBRA_EXT_PREFIX`;
without them the solver columns print `not run`. `ZEEBRA_SAT_SKIP_F4=1` drops the F4 columns from
`preprocess`. Results and the decision are in
[`docs/research/sat-and-algebra.md`](../research/sat-and-algebra.md).

`f4_selection` compares every reducer-selection policy and the cache against one common baseline,
on one line each: the closure size, the largest matrix, the peak live entries, the row operations,
the share of reducer multiples that had been needed before, and the stage times. The policies come
from `ReducerSelection::ALL`, so one added to the enum is measured without the program being
edited, and every row's basis is asserted equal to the first row's.
`f4_profile`'s configurations bundle several options together, so neither effect can be attributed
from it alone.

`f4_ablation` runs twelve configurations over the corpus and asserts every one returns the
baseline's basis, which is what establishes that the optimizations compose rather than conflict.
`f4_milestone` is the headline comparison: both engines on identical inputs in one process, with
the bases asserted equal wherever both can run. It reports **two** ratios, because the pair
criteria are shared machinery and the two functions' defaults do not match — see "Choosing a
strategy" below. `buchberger_reach` runs the classical engine on one hard instance per invocation
so an external timeout can bound it, which is how a dash in that table is shown to mean "does not
finish" rather than "was not tried".

`fglm_baseline` classifies each benchmark system as unit, zero-dimensional, or
positive-dimensional from the leading monomials of its grevlex basis, reports the dimension `D` of
`R/I` as a vector space, and times a lex basis against a grevlex one under both engines. It is the
baseline for the order-conversion work; **cyclic-4 is positive-dimensional**, so FGLM does not
apply to it, and that is measured rather than assumed.

`fglm_profile` attributes a conversion's cost. One table is the shape of the border — how many of
the `N * D` operator columns leave the standard monomials, and how many *distinct* monomials those
are, whose gap bounds what deduplicating them could remove. The other is the stage breakdown
(standard-monomial enumeration, border classification, scalar normal forms, a batch's symbolic
closure, coordinate assembly, the lex walk) beside what the representations hold. Scalar reduction
and batched reduction are the same stage under two strategies, so one column is zero whenever the
other is not and the reported share is of their sum. It profiles the shipped strategies, or M17's
with `-- baseline`. It sets `FglmOptions::measure_stages`, which is off by
default because the operator loop runs `N * D` times and a clock read inside it is not free. The
byte figures are estimates of this crate's own representations;
`zeebra::util::peak_resident_bytes` is the separate, process-wide measurement, and the two are not
interchangeable.

`fglm_border` prices the three `OperatorConstruction` strategies against each other on the same
prepared source basis, having first asserted that they build identical operators, and varies the
batch size — which is the trade that decides the recommended default rather than being left to a
guess. It also answers,
with its own measurement rather than by inference, whether the one-term polynomial built per border
reduction is worth avoiding: 0.07% to 0.38% of the reduction it precedes on the families where
reduction dominates, so no. `cargo bench --bench fglm -- fglm_operator_construction` is the same
comparison under Criterion.

`fglm_parallel` is why one border batch's target loop is **not** parallelized, measured rather than
argued, and it is the entry point for anyone who wants to re-open that. Its target loop is the one
loop in the project whose iterations are genuinely independent — the reducer pivots are fixed before
any border monomial is touched — and that is not enough. Four tables, selected by name because they
want different machine conditions: `per-batch` splits a batch's clock between the symbolic closure
and the target loop (two single-threaded tables, one pinned core); `floor` prices one
`std::thread::scope` dispatch on this machine; `carry` prices the `dirty_from` carry a split gives
up, sequentially, so it is separated from the dispatch cost; and `sweep` runs the reduction on up to
128 scoped threads with every row's remainders asserted bit-identical to the one-worker row's. At
the recommended batch of 64 a batch's target loop is 8 to 210 µs against 21 µs per worker, so one
worker is the fastest row on every system in the corpus. §6.8 of
[`docs/MILESTONE-FGLM-SCALABILITY.md`](../MILESTONE-FGLM-SCALABILITY.md) has the figures and the
decision; `BorderReduction::Grouped` is the decomposition without the threads, kept because the
carry's cost is a measurement.

That refutation is about splitting *one batch's* target loop. Sharing *whole batches* across
threads is a different decomposition: each worker builds a closure and reduces it, so there is no
carry to give up and one dispatch covers a batch's closure as well as its reduction. #826 ships it as
`BorderBatch::workers`. `fglm_operator_probe` is its A/B. It builds one source basis per system,
times `QuotientAlgebra` construction at each worker count given (fastest of `REPS`, default 7), and
asserts that every count's operators equal the first count's:

```bash
cargo run --release --features external-runners --example fglm_operator_probe -- 1 16
```

`wiedemann_conversion` alternates classical and adaptive conversion on identical prepared bases,
asserts exact basis equality, and prints the chosen route, projection attempts, fallback reason,
operator-construction time, dependence time and output digest. Its process peak spans all repeats;
use separate `--route classical` and `--route adaptive` processes for per-route memory.
`--msolve PATH` checks the eliminant through the existing bounded adapter. See the
[conversion guide](grobner-bases.md#certified-scalar-wiedemann) for input format and limits.

`sparse_matvec_throughput` times dependent Krylov steps of the real `wiedemann_conversion` operators
and of density-matched and cache-level synthetic matrices, per field (GF(2), GF(2^8), BabyBear,
Goldilocks, BN254), storage format, block width and thread count, with an L1 multiply-add rate and a
streaming-read bandwidth measured beside every repetition. Run the full sweep under
`tools/benchlock.sh` and `taskset -c 0-63`; `--quick` is a seconds-long smoke test. Results and the
#731 conclusion are in [`docs/research/sparse-matvec-throughput.md`](../research/sparse-matvec-throughput.md).

`block_krylov_study` splits a forced scalar Wiedemann conversion into operator construction,
sequence, reconstruction and certificate (`--mode stages`, one route per process for attributable
RSS). It also times serial, batched, threaded and block-shaped Krylov sequences at widths 2/4/8 on
the real operator (`--mode sequence`). Families: `cyclic`, `dense`, `powers` (non-shape) and
`nonradical`. Fields: `zp65537`, `babybear`, `goldilocks`. Campaign scripts, raw output and the
#731 reject/defer decision are in
[`docs/research/block-krylov-conversion.md`](../research/block-krylov-conversion.md).

`fglm_shape` is M18-4's dense research spike, measured. `grobner::fglm::shape` detects **shape
position** — whether a single variable's powers `1, t, ..., t^{D-1}` are a basis of `R/I` — and
where the last variable qualifies it produces the lex basis `p(t), x_0 - h_0(t), ...` from that
variable's Krylov sequence, with no monomial walk and without retaining the accepted quotient
vectors. The whole katsura family qualifies and nothing else in the corpus does; 76 of 120
zero-dimensional differential fixtures do, and the route is checked against Singular on every one.

Detection is **algebraic, not a count of solutions**: `<x - 1, (y - 1)^2>` has one point, dimension
two, and is in shape position, while `<x^2, y^2>` has one point, dimension four, and is not. The
output is verified before it is returned — every polynomial's class in `R/I` must be zero, which
with the leading monomials proves it is the reduced lex basis — so nothing probabilistic is
exposed. It is public and tested but not a `FglmOptions` strategy; `docs/MILESTONE-FGLM-SCALABILITY.md`
§8.5 is the **no-go** on a full sparse-FGLM milestone and the measurements behind it.
[`docs/research/wiedemann-krylov.md`](../research/wiedemann-krylov.md) is the decision record for
Wiedemann and Krylov methods in both places this crate eliminates — **won't-do** for F4's
echelonization, and a deferral for order conversion that M25's competitive baseline has since
reopened as staged work. Read it before proposing either.
[`docs/research/order-conversion.md`](../research/order-conversion.md) is the survey of what else
there is: eight alternatives to the classical conversion, each with a verdict and the measured figure
that settles it, and the reaffirmed-but-narrowed §8.5 no-go. Its §4 records shape position measured on a cipher-derived family — machine-independent,
because a minimal-polynomial degree is not a timing.

`grobner::shape_position_hypotheses` is the cheap syntactic half of the same question, from Campa and
Roy's Theorem 8 (eprint 2025/814): zero-dimensionality, a pure-power leader for every variable, and a
finite `deg_≺`-top-form quotient, each decided from the basis for the price of a Hilbert series
rather than a quotient algebra. It is **not** called a certificate of shape position, because those
hypotheses do not imply it — `test_the_published_hypotheses_are_not_sufficient` exhibits an ideal
that discharges every one of them and is not in shape position. The full reading, including the
hypothesis Theorem 8's proof invokes and its statement omits, is in `docs/research/anemoi.md`
§10.5, which moved out with the cryptanalysis research in #668 and is preserved at commit
`9532a9a2`. The missing condition is exactly
`shape_report`'s `minimal_polynomial_degree == dimension`, so the two together are what settles a
family and the module's docs say which half is a deduction and which a computation.

`fglm_storage` reports the operator representations three ways: bytes under each strategy, which are
exact; operator *application*, on a unit input and a dense one, because the sparse path skips a zero
input coordinate and the dense path does not; and the whole conversion, where the difference turns
out to be under 1%. `cargo bench --bench fglm -- fglm_operator_application` is the application half
under Criterion.

`fglm_ablation` runs every construction × storage combination on one source basis per system, with
the lex basis and the operators' nonzero count asserted equal to the baseline's on every row, and
reports time and memory side by side. **It is where the defaults came from.** The shipped
configuration is at least as fast as M17's on every system in the corpus — 14.0x on katsura-7, 1.17x
on planted-10 — and never stores more. Two changes cannot be ablated and the example says so: the
compact sparse column and the span's two triangular blocks are not strategies, so they are in every
row including the baseline. `cargo bench --bench fglm -- fglm_recommended` is the same comparison
under Criterion, and `fglm_profile` shows what that left behind: border reduction was 95% of
katsura-7's conversion and is 52%, while planted-10's lex walk is the majority of its own —
M18 did not touch it, and two follow-ups did: offsetting each echelon row's coordinates by its
pivot, and reducing into registers the span owns rather than allocating a residue per candidate.
Together, on one pinned and interleaved protocol, they take planted-10's lex walk from 23.2 ms to
11.1 ms — 2.09x — and the conversion's dense blocks from 20,484 kB to 16,392 kB, which is a fifth
of them and not a quarter.

Recorded baselines, before/after measurements, and the reasoning behind each optimization are in
[`docs/MILESTONE-ALGEBRA-FOUNDATION.md`](../MILESTONE-ALGEBRA-FOUNDATION.md),
[`docs/MILESTONE-F4.md`](../MILESTONE-F4.md),
[`docs/MILESTONE-F4-OPTIMIZATION.md`](../MILESTONE-F4-OPTIMIZATION.md),
[`docs/MILESTONE-FGLM-SOLVING.md`](../MILESTONE-FGLM-SOLVING.md),
[`docs/MILESTONE-FGLM-SCALABILITY.md`](../MILESTONE-FGLM-SCALABILITY.md),
[`docs/MILESTONE-SIMD-PARALLELISM.md`](../MILESTONE-SIMD-PARALLELISM.md),
[`docs/MILESTONE-LARGE-PRIME-FIELDS.md`](../MILESTONE-LARGE-PRIME-FIELDS.md),
[`docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md`](../MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md),
[`docs/MILESTONE-DEGREE-AWARE-F4.md`](../MILESTONE-DEGREE-AWARE-F4.md),
and
[`docs/MILESTONE-COMPETITIVE-ALGEBRA.md`](../MILESTONE-COMPETITIVE-ALGEBRA.md).
[`docs/MILESTONE-ALGORITHMIC-ELIMINATION.md`](../MILESTONE-ALGORITHMIC-ELIMINATION.md) is the
current plan rather than a record of measurements taken, and
[`docs/MILESTONE-COMPETITIVE-MQ-SOLVING.md`](../MILESTONE-COMPETITIVE-MQ-SOLVING.md) is the next
one. That plan opens by recording that the one before it is unfinished, because its own scope
depends on measurements M26 has not yet reported.

M25 calibrated Zeebra against external solvers on identical problems; where a published conversion wall was checked it **did not reproduce**: 46 s here against 6.13 h reported, and a within-run conversion/basis ratio of 1.71 against 2 367.

That milestone's §10.1 is worth reading on its own. It scores the plan's own predictions and finds
that every one about a stage already measured held, while three of four about quantities nobody had
measured were wrong by more than an order of magnitude — one by 838x.

### Sylvester kernel comparison

`determinant_width --compare-kernels` times dense and Euclidean kernels in alternating order,
asserts identical sample vectors on every draw, and prints each draw plus the ratio of the two
medians. `--width` is repeatable; `--samples` is rounded up to a multiple of each width so every
requested worker receives work. Both kernels use the same fixed-seed pair and consecutive sample
points. `--pair synthetic` (default) has degree one in the surviving variable; `--pair triangular`
includes quadratic specialization work. Neither is a registered cryptanalytic instance.

Build before taking the benchmark lock, then pin to 32 physical cores (verify the topology on
your machine). On the development workstation:

```sh
cargo build --release --example determinant_width
ZEEBRA_MACHINE=5995wx ZEEBRA_AFFINITY=0-31 \
  tools/benchlock.sh sylvester-297 timeout 600 taskset --cpu-list 0-31 \
  target/release/examples/determinant_width --compare-kernels \
  --order 1458 --width 32 --samples 128 --repeats 3
```

If you set `CARGO_TARGET_DIR`, replace `target/release` with that directory's `release` path.
Use `--order 162 --samples 32 --repeats 1` for a quick check. `--compare-kernels` cannot be combined
with `--kernel` or `--count-allocations`; order must be positive and even. Initial load above eight
refuses the run. Retain all draws and examine their spread and the benchmark-lock load log before
publishing; a short Euclidean batch can be dominated by thread creation. The ratio includes sample
specialization and thread creation but excludes coefficient extraction, interpolation, root finding
and verification. It is a kernel-stage comparison and cannot be quoted as a solver speedup.

### Monomial order width

Build before acquiring the benchmark lock. Choose a CPU in the current affinity mask and check
the machine load and runnable count while holding the lock.

```sh
env -u RUSTFLAGS RUSTC_WRAPPER="" CARGO_TARGET_DIR=target-width \
  cargo build --release --example monomial_order_width
tools/benchlock.sh monomial-order-width bash -c \
  'cat /proc/loadavg && taskset --cpu-list 2 target-width/release/examples/monomial_order_width'
```

The harness compares production with four-variant and three-variant versions of the same built-in
comparators. It times forced per-comparison dispatch and replays the unstable sort over recommended
F4 column snapshots. It checks the dispatch checksums and sorted columns across arms.
Run `cargo test --example monomial_order_width` for the fixed checksum and layout check that also
runs in CI. See the [measurement and scope](../research/monomial-order-width.md).

### Classification before direct lex

Build `cargo build --release --example classify_before_lex`. The runner accepts one of
`planted-8`, `katsura-5`, `katsura-6-minus-one`, or `cyclic-4-gf2`, followed by `direct` or
`classify`. Each invocation emits one JSON record with the environment, outcome, plan, batch
counts, elapsed time, and process peak RSS. Run one invocation per process under the benchmark
lock so the high-water mark belongs to that row. Both policies use the same 1000-row/1000-column
F4 limits, RNG seed 417, and other default budgets. See
[the measurement protocol](../research/classify-before-lex.md) for pinned commands and results.

### Multirow pivot reuse (#715)

`mq10_profile --multirow=single|band4|lanes4`, built with `--features research-multirow`, runs the
shipped F4 route with the forward pass in the production single-row loop, four-row bands with
separate scalar lanes, or four interleaved lanes, and reports the band census (pivot reads against
applications, sharing width, partial bands, scratch). `tools/external/multirow-study.py` runs the
three arms plus a feature-absent control under the benchmark lock and verifies every basis against
the retained references. The [report](../research/multirow-reuse.md) rejects integration and defers
an explicit SIMD kernel. Checks:

```sh
cargo test --features research-multirow --lib linalg::dense::band
python3 tools/test/multirow-study-test.py
python3 research/multirow-reuse/summarize.py
```

### Persistent worker dispatch and border reduction

The [worker-pool study](../../research/worker-pool/README.md) compares scoped threads, a bounded
parked pool and a Rayon dev-only runtime. Build `worker_pool_study` with `--features research-work`;
this is a measurement entry point, not a parallel conversion strategy. Its reproduction commands
use a private `/buildcache` target, the benchmark lock, topology-aware CPU masks, five fresh-process
repetitions and bounded child processes. The [report](../research/worker-pool.md) retains the full
worker sweep and negative/default-batch controls. No old single-thread timing is a scaling baseline.

The focused correctness checks are:

```sh
cargo test --features research-work --example worker_pool_study
cargo test --features research-work --lib dispatch_tests
python3 tools/test/worker-pool-study-test.py
python3 research/worker-pool/summarize.py
```

The summarizer validates retained evidence without running measurements. It refuses incomplete
campaigns, missing/duplicate cells, identity mismatches and failed attempts.
