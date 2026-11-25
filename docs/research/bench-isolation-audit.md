# Bench isolation audit: what a CCD reservation fences (#1104)

**Measured at:** `a63c5568` (main; `tools/bench-reserve.sh`, `tools/bench_campaign.py` and
`tools/bench-job` as there), with `tools/bench-isolation-audit.sh` as added beside this document (#1104; zombie handling came after the window-1 snapshots, §2); 2026-11-25,
Threadripper PRO 5995WX, kernel 7.3.3-200.fc44, two reservation windows (12:11–12:31 and
12:32:15–12:32:19 EST) announced in `benchlock.log` as `#1104-isolation-audit-window1`.
Raw data and scripts: [`research/bench-isolation-audit/`](../../research/bench-isolation-audit/).
**Parent:** #1103. **Feeds:** #1105 (§8), #1106/#1107 (§6), #1108/#1109 (§5, §6, §9).

## Summary

| Hypothesis | Verdict | Evidence |
|---|---|---|
| **H-A1**: with CCDs 1–2 reserved, no user-manager task outside `zbbench.slice` can run on `8-23,72-87` | **Falsified**, in 3 of 3 snapshots | Four live escape groups (§2): `systemd --user` (`user@.service/init.scope`), `uresourced.service`, rootless podman's `catatonit` (`user@.service/user.slice`), and the GDM login `session-*.scope`. Plus one unprivileged route anyone can take: `systemd-run --user --slice=<new>` gets all 128 CPUs (§3). |
| **H-A2**: over 20 min with a build loop on the rest, every task on the reserved CPUs is a kernel thread or `system`/`machine` task | **Falsified by 8 ticks**; held for every fenced slice | 1,020 s, 752 snapshots, 7 clean `cargo build -j48 --tests` builds: the 32 CPUs were 0.033% busy (1,088 ticks, 66% IRQ). The only user-side time was `systemd --user` in its unfenced `init.scope`: 3 ticks on siblings, 5 on cores. Fenced slices: 0. |
| **H-A3**: harness CPU time on bench CPUs < 1% of a 0.24 s 16-worker attempt when a spare CPU exists | **Held with a spare; falsified (6.0%) without one** — the shape every retained manifest uses for 16 workers | With a spare: `bench_foreign` median 0, p90 ≤ 0.35% over 4,552 attempts. Without: 0.236 CPU-s inside the timed window, 89% of it `tools/rss-guard.sh` (§5). |

Not a stop condition (#1104 *Budget*): every check here ran unprivileged, and every escape but
the GDM login scope can be closed unprivileged (§9). The fence that *is* there is tight: tasks
in the fenced slices did not run on a reserved CPU once in the window.

What changes for the track:

1. `bench-reserve.sh reserve` should fence every user-manager slice, not a fixed list of three, and
   `status` should fail on escapes — filed as a follow-up (§9).
2. The harness must leave the reservation (#1108): out-of-window snapshots cost 0.59 CPU-s each on
   the attempt's CCD, and in-window `rss-guard` 0.2 CPU-s, at every worker count (§5).
3. One CCD suffices for w ≤ 8, returning 8 cores to development (§6).
4. A reservation has no owner: one outlived this audit's window because another agent's run queued
   on it (§4).

## 1. Machine state (read-only, 2026-11-25)

From `inventory-unreserved-initial.json` and `window1/inventory-unreserved.json`.

| Item | Value | Note |
|---|---|---|
| `system.slice`, `machine.slice`, `init.scope`, `user.slice` `cpuset.cpus.effective` | `0-127` | unfenced, as #1104 found |
| User-manager slices | `app`, `background`, `session`, `zbbench`, **and `user.slice`** | `user@1000.service/user.slice` holds rootless podman (`podman-pause-*.scope`) and is not in `reserve`'s list |
| Self-hosted GitHub runners (`github-runner-*`) | **user** services in `app.slice` | Not `system.slice` as #1104 assumed: `reserve` already fences them and their jobs. Their docker jobs are a different matter (`docker.service`, system) |
| `docker`/`containerd` | `system.slice`, no container running at audit time | a running rootful container would be `system.slice/docker-*.scope`, unfenced |
| `/sys/devices/virtual/workqueue/cpumask` | all 128 CPUs | unbound kworkers may run on the bench |
| Kernel cmdline | no `isolcpus`, `nohz_full`, `irqaffinity`, `rcu_nocbs` | |
| IRQs | 199; 45 have an effective CPU in `8-23,72-87`: 33 NVMe queues (managed, one per CPU), 5 AHCI, 4 NIC, 3 PCIe | `irqbalance.service` is running with a default config |
| `perf_event_paranoid` | 2 | `cycles`/`task-clock` per process yes, uncore no |

## 2. Where agents and their processes land (item 2)

Every launch path tried, with its cgroup class under a reservation:

| Launch path | cgroup | Fenced by `reserve`? |
|---|---|---|
| GNOME Terminal shell, Claude Code, `cargo`/`rustc` under it | `app.slice/app-org.gnome.Terminal.slice/vte-spawn-*.scope` | yes |
| tmux / editors / browsers started from the desktop | `app.slice/app-*.scope` | yes |
| `systemd-run --user` (service or `--scope`), default slice | `app.slice/run-*.{service,scope}` | yes |
| `systemd-run --user --scope -p AllowedCPUs=8` while reserved | `app.slice/run-*.scope`, effective = rest | yes (the request is ignored; §3) |
| **`systemd-run --user --slice=<anything new>`** | `user@.service/<new>.slice` | **no — `Cpus_allowed_list: 0-127`** |
| Self-hosted runners and their job processes | `app.slice/github-runner-*.service` | yes |
| GNOME session services | `session.slice/*` | yes |
| Rootless podman containers | `user@.service/user.slice/podman-pause-*.scope` (`catatonit`) and siblings | **no** |
| `systemd --user` itself, `(sd-pam)` | `user@.service/init.scope` | **no** |
| `uresourced` (user instance) | `user@.service/uresourced.service` | **no** |
| GDM login session (`gdm-session-worker`, `gnome-session-init-worker`) | `user-1000.slice/session-3.scope` | **no** (owned by the system manager) |
| ssh / tty logins | `user-1000.slice/session-*.scope` | **no** — no `sshd` runs here today, so none were present |
| cron | `crond.service` (system); jobs would get a `session-*.scope` through `pam_systemd` | **no** — no user crontab exists today |
| Rootful docker / containerd | `system.slice` | **no** (root; Appendix A.1) |
| `bench-reserve.sh run` | `zbbench.slice/run-*.scope`, `Cpus_allowed_list: 8-23,72-87` | the bench itself (verified in `window1/hold.txt`) |

The four escape groups seen in all three snapshots (`window1/inventory-reserved-{1,2,3}.json`) are
daemons that were idle in the window. They are a correctness hole rather than an observed
interference: H-A2's sample charged them 8 ticks in 17 minutes. The snapshots also list a fifth group, a sandboxed desktop app's scope in `app.slice`, with one task at `0-127`. It is a
**zombie**: the kernel's cpuset update skips zombies, so its mask is stale, and it can never run.
The script now counts zombies apart and never as meeting (`zombies` per group); the snapshots
predate that and still list it.

## 3. Reservation transitions (item 3)

`window1/transition-*.txt`, `window1/transition-taskset.txt`, `window2/transition-*.txt`.
Subjects started in `app.slice` before `reserve 1,2`:

| Subject (mask before) | While reserved | After `release` |
|---|---|---|
| `taskset -c 0-127` (wider) | `0-7,24-71,88-127` (cpuset ∩ request) | `0-127` |
| `taskset -c 8` (disjoint from the new cpuset) | `0-7,24-71,88-127` (falls back to the whole cpuset) | `8` |
| `taskset -c 0,8` (straddling) | **`0`** — the intersection, one CPU | `0,8` |
| a 1-thread spinner pinned to 8 | moved to CPU 39 within the first snapshot; ran on the rest all window | — |
| scope with `AllowedCPUs=8` | systemd `cpuset.cpus=8`, kernel `cpuset.cpus.effective=0-7,24-71,88-127` | `8` |
| mask set to `0-127` *during* the reservation | `0-7,24-71,88-127` | `0-127` |

The kernel keeps each task's *requested* mask and re-applies it on release, including a request
made while reserved. `release` does not lose state.

Probes made while reserved:

| Call | Result |
|---|---|
| `taskset -c 8 true` (new process) | `Invalid argument`, rc 1 — #194's symptom |
| `taskset -cp 8 <pid>` | `Invalid argument`, rc 1 |
| `taskset -cp 0-127 <pid>` | rc 0, mask silently becomes the rest |
| `taskset -cp 0,8 <pid>` | **rc 0, mask silently becomes `0`** |
| `systemd-run --user --scope -p AllowedCPUs=8 …` | rc 0, runs on the rest |
| `systemd-run --user --scope --slice=zb1104-escape.slice …` | rc 0, **`Cpus_allowed_list: 0-127`** |

Three places disagree, as #1104 suspected: `taskset` reports success while narrowing a straddling
request to whatever survives, so a 2-CPU job quietly becomes a 1-CPU job for the window. systemd's
`AllowedCPUs` (and `cpuset.cpus`) on a child shows what was asked for, while
`cpuset.cpus.effective` shows what the kernel enforces. Only `effective` and the task's
`Cpus_allowed_list` are evidence; `bench-reserve.sh status` already reads `effective`.

## 4. A reservation outlives its session

Window 1's hold ended at 12:29:43. Another agent's `#1141` probe had queued on the CCD lock at
12:21:35 (`benchlock.log`) and started inside this reservation the same second. `release` then
correctly refused (`1 process(es) still running in zbbench.slice`). Releasing with `--force` would
have unfenced the builds around a measurement in flight. The reservation was released at 12:31:47,
once #1141's run ended.

Nothing records who a reservation belongs to or who should release it, and nothing stops a
queued run from starting inside a reservation its owner meant to release. #1109 owns reservation
lifetimes; this is input for it.

## 5. Harness cost on the bench CPUs (item 5)

### From 7,012 retained attempts (39 jobs, every manifest `run.cpus=8-23`)

`research/bench-isolation-audit/journal-harness/` (`summarize.py`, `summary.txt`):

| Workers | Spare CPU? | n | Median harness CPU-s / attempt | Median attempt CPU-s | `bench_foreign` median / p90 |
|---:|---|---:|---:|---:|---|
| 1 | yes (15) | 3,288 | 1.089 | 0.007 | 0 / 0.35% |
| 4 | yes (12) | 634 | 1.150 | 0.010 | 0 / 0.16% |
| 8 | yes (8) | 630 | 1.253 | 0.017 | 0.004% / 0.12% |
| 16 | **no** | 2,460 | 1.547 | 0.015 | 0 / 0 — by construction (harness time counted as own) |

The harness spends 1.1–1.5 CPU-s per attempt at every worker count, mostly in two
`cpu-context.sh` snapshots. With a spare CPU they run on it, which is on the attempt's own CCD and
L3 for w ≤ 8. With no spare, as for every 16-worker cell, they run on the attempt's CPUs, and
`bench_foreign` cannot see them because `own_cpu_s` absorbs them.

### Inside the timed window, no spare (16 workers on `8-23`)

`research/bench-isolation-audit/harness-cost/` (`hcost.py`, `result-8-23.{json,log}`): `run_child`
with the snapshots stubbed out and the harness pinned to the child's CPUs, 15 repetitions per cell, a
16-thread spinner as the child. *Capacity* is 16 × wall.

| Child wall | Everything (`perf` + `rss-guard` + sampler) | Without `perf` | Sampler only |
|---:|---:|---:|---:|
| 0.24 s | 0.236 CPU-s = **6.0%** of capacity | 0.209 (5.3%) | 0.004 (0.11%) |
| 1 s | 0.234 (1.45%) | 0.203 (1.26%) | 0.013 (0.08%) |
| 5 s | 0.652 (0.81%) | 0.628 (0.78%) | 0.056 (0.07%) |

The terms are `rss-guard.sh` at about 0.2 CPU-s to start plus 0.1 CPU-s per 1 s poll (bash scanning
1,600 `/proc` entries), `perf stat -p` attach at about 0.03 CPU-s (its `CycleCounter` polls `/proc`
every 5 ms until the solver appears), and the 25 ms frequency sampler at about 0.011 CPU-s/s. One
`cpu-context.sh` snapshot costs 0.585 CPU-s in 0.50 s wall (5 repetitions).

**Recommendation for #1105/#1108:** run the harness on a CPU outside the reservation, not on a
spare core of the reserved CCD. A same-CCD spare keeps harness time out of the attempt's CPUs, but
not out of its L3, and a 0.5 s `/proc` scan right before the timed region is the worst case for
that. Concretely: keep only the child in `zbbench.slice`, and run the `bench-job` runner, snapshots,
`perf` and the guard in `app.slice` on the rest CPUs. Snapshots read `/proc/stat` for the bench
CPUs from anywhere, and `perf stat -p` counts the target wherever `perf` runs. Independently,
`rss-guard` should be given the child's pid, which `run_child` already has, instead of scanning
`/proc`. That removes most of the 0.2 CPU-s even when the harness stays put.

## 6. CCD policy (item 6)

`tools/bench-isolation-audit.sh policy 1 2 4 8 9 12 16 17` → `research/bench-isolation-audit/policy.txt`,
computed from `cache/index3/id` of the placement CPUs and `br_plan` of the resulting CCDs:

| Workers | Placement | Reserved CCDs | Reserved CPUs | Idle siblings | Development CPUs | Development cores |
|---:|---|---|---|---|---|---:|
| 1 | 8 | 1 | 8-15,72-79 | 72 | 0-7,16-71,80-127 | 56 |
| 2 | 8-9 | 1 | 8-15,72-79 | 72-73 | 0-7,16-71,80-127 | 56 |
| 4 | 8-11 | 1 | 8-15,72-79 | 72-75 | 0-7,16-71,80-127 | 56 |
| 8 | 8-15 | 1 | 8-15,72-79 | 72-79 | 0-7,16-71,80-127 | 56 |
| 9 | 8-16 | 1,2 | 8-23,72-87 | 72-80 | 0-7,24-71,88-127 | 48 |
| 12 | 8-19 | 1,2 | 8-23,72-87 | 72-83 | 0-7,24-71,88-127 | 48 |
| 16 | 8-23 | 1,2 | 8-23,72-87 | 72-87 | 0-7,24-71,88-127 | 48 |
| 17 | 8-24 | 1,2,3 | 8-31,72-95 | 72-88 | 0-7,32-71,96-127 | 40 |

The M29 placement `8..8+w-1` is the same under each row; only the fence around it changes. A 1-CCD
reservation returns CCD 2's 8 cores to development for every w ≤ 8 session, which is most attempts
(4,552 of 7,012 retained attempts are w ≤ 8).

**Deriving it from a manifest without changing old manifests (for #1108/#1109).** Today a manifest
says `run.cpus` (always `8-23`) and `run.workers`, and the reservation is whatever the operator took.
Proposal:

- The CCDs are the L3 ids of `run.cpus[0 .. max(run.workers) − 1]` — the CPUs the widest attempt
  occupies — exactly what `policy` computes. For every retained manifest, that is CCDs 1–2 when 16
  is among the workers and CCD 1 otherwise.
- `bench-job` checks that the live reservation covers those CCDs, as `bench-reserve run` checks the
  cpulist today, and records the derived CCDs in the journal header.
- `run.cpus` keeps its meaning (the CPUs attempts may be placed on). What it loses is its second job,
  supplying `harness_cpus`: with the harness moved off the reservation (§5), the spare set stops
  mattering. An old manifest therefore derives the same placement and a reservation no larger than
  today's. Only the harness moves, which is the change §5 asks for anyway.
- A manifest may state `run.reserve_ccds` explicitly to override, for example to reserve a
  neighbouring CCD as a thermal or power buffer. Absent means derived.

## 7. Privileged options

Appendix A. None was applied.

## 8. What a CCD fence does not isolate

A reservation fences CPU time and L3 for the processes in the fenced slices. Everything below is
shared with the rest of the machine whatever the fence does. *Telemetry* names what can see the
channel from an unprivileged attempt record. This is the input to #1105, whose `telemetry: 1` fields
are named where they exist already (#1117).

| Channel | Why the fence does not cover it | Telemetry that can see it | Privilege |
|---|---|---|---|
| DRAM bandwidth, memory controllers | NPS1: one NUMA node, every CCD interleaves over all channels | resctrl MBM (`mbm_bytes_per_s`) when resctrl is mounted; `perf` `amd_df`/`amd_umc` uncore otherwise | resctrl mount (root, once) or `perf_event_paranoid` ≤ 0 (today 2). **None available today** |
| Infinity Fabric, IO die | every L3 miss and device DMA crosses it | `amd_df` uncore events | paranoid ≤ 0. **None available today** |
| Package power, boost budget | one package limit; current drawn elsewhere lowers the bench cores' boost | effective clock from `perf stat` (`effective_khz`, #999), sampled `scaling_cur_freq` (`median_khz`); RAPL `package_w` | perf: none. RAPL: root-only today (`rapl_uj` null); owner `chmod 0444` documented |
| Temperature | shared package and heatsink; throttling is package-wide | `k10temp` Tctl (`temp_mc`) | none |
| `system.slice` daemons, rootful docker | `reserve` restricts only the user manager | `bench_foreign`, `sibling_busy`; `bench_running` names a task at snapshot time; this script's `sample` attributes it | none |
| Unfenced user cgroups (§2) | not in `reserve`'s fixed list | as above; `inventory` lists them under `escapes` | none |
| Kernel threads, unbound workqueues | per-CPU kthreads run where their CPU's work is; unbound kworkers follow the global workqueue mask (all CPUs) | `bench_foreign`; `sample`'s `kernel` class (152 of 207 attributed ticks in H-A2) | none to see; root to move (A.2) |
| IRQs, softirqs | 45 IRQs aim at CCDs 1–2; 33 are managed NVMe queues | `/proc/stat` irq+softirq per bench CPU (inside `bench_busy`; split out as `sample`'s `cpu_ticks.irq`: 66% of H-A2's busy time); `/proc/interrupts` deltas | none to see; root to move (A.3, A.4) |
| Page cache, disk I/O | one page cache; reclaim and writeback run as whoever triggers them | PSI `io`/`memory` (`psi`), `vmstat` scan/steal/swap, rusage `majflt`/`inblock` | none |
| Allocator, compaction, THP | `kcompactd`, `khugepaged`, zone locks are global | `vmstat`, PSI `memory` | none |
| Kernel locks (mmap, cgroup, scheduler) | global or per node | **none available** (lock stats or eBPF; out of scope per #1105) | — |
| TLB shootdowns | kernel-wide flushes IPI every CPU | `/proc/interrupts` `TLB` row per CPU | none |

## 9. Follow-ups

- **Fence every user-manager slice, and fail `status` on escapes** (`bench-reserve.sh`; not done
  here, per #1104's non-goals). `reserve` could set `AllowedCPUs` on every top-level slice of the
  user manager except `zbbench.slice` (including `user.slice` and any created later), and `status`
  could run `bench-isolation-audit.sh inventory` and return 2 on a live escape. Neither needs root.
  `init.scope` (the user manager itself) and `session-*.scope` cannot be fenced from the user
  manager; the first is near idle, and the second needs Appendix A.1's sudo rule or a polkit grant.
- **Harness off the reservation, and `rss-guard` by pid** (§5). This belongs to #1108.
- **Reservation ownership** (§4). This belongs to #1109.

## 10. Method notes and limits

- `inventory` reads each task's `Cpus_allowed_list` rather than each cgroup's cpuset. It is what the
  scheduler enforces, and it catches a task that kept a stale mask. It ran in 1.4 s wall
  (0.67 + 0.93 CPU-s) over about 1,600 processes and 7,000 tasks.
- `sample` at 1 s cannot see a task born and dead between snapshots, and IRQ time has no task. Its
  `coverage` (attributed ÷ busy) was 0.19 in H-A2, with 66% of busy being IRQ and most of the
  rest system time charged to no thread. The H-A2 verdict rests on two facts: tasks in fenced
  slices could not have run there (their masks, §3), and nothing user-side was charged except
  `systemd --user`.
- One window, one day, one machine state. #985's sibling spikes of 6–100% during `cargo clean` did
  not recur in 7 clean builds. The reserved CPUs stayed under 0.04% busy throughout. The likely
  differences are a quieter machine and an XFS rather than btrfs target directory (`/buildcache`),
  but neither was tested.

## Appendix A. Privileged options (documented, none applied)

Each needs root. Applying one is an owner decision recorded on #1103. `REST` below is the
reservation's rest cpulist (`0-7,24-71,88-127` for CCDs 1–2) and `BENCH` its bench cpulist
(`8-23,72-87`).

### A.1 Fence `system.slice`, `machine.slice` and `init.scope` for the reservation's lifetime

Covers every system service (docker, containerd and their containers, `crond`, `tuned`,
`irqbalance`, journald), rootful containers and VMs, and PID 1.

```bash
sudo systemctl set-property --runtime system.slice  AllowedCPUs="$REST"
sudo systemctl set-property --runtime machine.slice AllowedCPUs="$REST"
sudo systemctl set-property --runtime init.scope    AllowedCPUs="$REST"
# rollback (a reboot also clears it: --runtime writes under /run)
sudo systemctl set-property --runtime system.slice  AllowedCPUs=
sudo systemctl set-property --runtime machine.slice AllowedCPUs=
sudo systemctl set-property --runtime init.scope    AllowedCPUs=
```

The same pattern with `user-1000.slice` fences login sessions (`session-*.scope`). Making it part of
`reserve` without a password needs a sudoers rule for exactly these commands. **Security:** anyone
who can run as the user could then confine system services to any cpulist. That is a local denial
of service, not an escalation, and the rule should pin the argument to `REST` and the empty string.
**Blast radius:** system services, including docker containers that other repositories' CI jobs
start, have 112 CPUs instead of 128 for the window. The runners themselves are user services and
are already fenced.

### A.2 Unbound workqueues

```bash
cat /sys/devices/virtual/workqueue/cpumask        # ffffffff,ffffffff,ffffffff,ffffffff today
echo "<hex mask of REST>" | sudo tee /sys/devices/virtual/workqueue/cpumask
echo ffffffff,ffffffff,ffffffff,ffffffff | sudo tee /sys/devices/virtual/workqueue/cpumask   # rollback
```

This moves only *unbound* work (`kworker/u*`: btrfs endio and flush, writeback, `events_unbound`).
That kind of work ran at least 76 of the 152 kernel ticks H-A2 charged to the reserved CPUs, and it is the
likely source of #985's `cargo clean` spikes. Per-CPU kworkers stay with their CPU by design, and
workqueues with `WQ_SYSFS` have their own mask under `/sys/devices/virtual/workqueue/<name>/`.
**Security:** nothing beyond root. **Blast radius:** unbound kernel work has 16 fewer cores during
the window; no other repository is affected.

### A.3 IRQ affinity

```bash
for d in /proc/irq/[0-9]*; do echo "$REST" | sudo tee "$d/smp_affinity_list" >/dev/null 2>&1; done
```

Two limits make this weaker than it looks. First, `irqbalance.service` runs here and would rewrite
the masks. Tell it instead with `IRQBALANCE_BANNED_CPULIST=$BENCH` in `/etc/sysconfig/irqbalance`,
then `sudo systemctl restart irqbalance`. Roll back by removing the line and restarting. Second, 33
of the 45 IRQs on `BENCH` are NVMe queues, which are managed IRQs: the kernel pins one queue per CPU
and refuses `smp_affinity` writes to them. Only `isolcpus=managed_irq,…` (A.4) moves those, and a
queue fires only on a CPU that submitted I/O to it. **Blast radius:** network, SATA and PCIe
interrupts move to other CPUs; nothing else changes.

### A.4 `isolcpus` / `nohz_full` / `rcu_nocbs` (boot time): expected to be rejected

```
# /etc/default/grub, GRUB_CMDLINE_LINUX +=
#   isolcpus=managed_irq,domain,8-23,72-87 nohz_full=8-23,72-87 rcu_nocbs=8-23,72-87
sudo grub2-mkconfig -o /boot/grub2/grub.cfg && sudo reboot
# rollback: remove the parameters, regenerate, reboot
```

This is the only option that moves managed IRQs, the scheduler tick and RCU callbacks off the bench
CPUs. It is also permanent until the next reboot. The scheduler stops balancing onto those CPUs, so
every build, agent and CI job loses 32 CPUs all the time, not only while a benchmark runs. That is
the opposite of #1103's goal. Rejected for that reason; listed so the trade-off is on record.
**Security:** nothing beyond root and a reboot.
