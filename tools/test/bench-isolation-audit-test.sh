#!/usr/bin/env bash
# Unit tests for tools/bench-isolation-audit.sh, over a synthetic /proc, /sys and cgroup tree.
#
# What matters is the classification: a task in an unfenced cgroup reported as fenced, or a
# CPU-time sample attributed to the wrong class, would certify a reservation that does not hold.
set -uo pipefail

SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/bench-isolation-audit.sh"
# shellcheck source=../bench-isolation-audit.sh
. "$SCRIPT"

pass=0 fail=0

check() { # <label> <expected> <actual>
  if [ "$2" = "$3" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL  %s\n  expected: %q\n  actual:   %q\n' "$1" "$2" "$3" >&2
  fi
}

check_rc() { # <label> <expected-rc> <actual-rc>
  if [ "$2" -eq "$3" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL  %s\n  expected rc: %s\n  actual rc:   %s\n' "$1" "$2" "$3" >&2
  fi
}

ROOT="$(mktemp -d)"
trap 'rm -rf "$ROOT"' EXIT
SYS="$ROOT/sys" PROC="$ROOT/proc" CG="$ROOT/cgroup" WQ="$ROOT/workqueue"
UM="$CG/user.slice/user-1000.slice/user@1000.service"
export ZEEBRA_CPU_CONTEXT_SYS="$SYS" ZEEBRA_CPU_CONTEXT_PROC="$PROC" ZEEBRA_CPU_CONTEXT_CGROUP="$CG" \
  ZEEBRA_ISOLATION_AUDIT_WORKQUEUE="$WQ" ZEEBRA_BENCH_RESERVE_SYS="$SYS" \
  ZEEBRA_BENCH_RESERVE_CGROUP="$UM" ZEEBRA_BENCH_RESERVE_STATE="$ROOT/reserve-state"

# Three CCDs of two cores each, SMT siblings offset by 6: CCD n = cores 2n,2n+1 and 2n+6,2n+7.
mkdir -p "$SYS" && printf '0-11\n' >"$SYS/online"
printf '\n' >"$SYS/isolated"
for c in $(seq 0 11); do
  mkdir -p "$SYS/cpu$c/cache/index3" "$SYS/cpu$c/topology"
  echo $(((c % 6) / 2)) >"$SYS/cpu$c/cache/index3/id"
  echo $((c % 6)) >"$SYS/cpu$c/topology/core_id"
  printf '%s,%s\n' $((c % 6)) $((c % 6 + 6)) >"$SYS/cpu$c/topology/thread_siblings_list"
done
mkdir -p "$WQ" && printf 'fff\n' >"$WQ/cpumask"

# A live reservation of CCD 1: bench 2-3,8-9, rest 0-1,4-7,10-11.
mkdir -p "$UM/app.slice" "$UM/zbbench.slice"
printf 'cpuset cpu io memory pids\n' >"$UM/cgroup.controllers"
printf '0-1,4-7,10-11\n' >"$UM/app.slice/cpuset.cpus.effective"
printf '2-3,8-9\n' >"$UM/zbbench.slice/cpuset.cpus.effective"
printf 'ccds=1\nbench=2-3,8-9\nrest=0-1,4-7,10-11\nat=2026-11-25T12:00:00-05:00\n' >"$ROOT/reserve-state"
for s in system.slice machine.slice init.scope user.slice; do
  mkdir -p "$CG/$s" && printf '0-11\n' >"$CG/$s/cpuset.cpus.effective"
done

mkdir -p "$PROC/sys/kernel" "$PROC/irq/0" "$PROC/irq/24/nvme0q3" "$PROC/irq/25/eth0-rx" "$PROC/irq/26"
printf '7.3.3-test\n' >"$PROC/sys/kernel/osrelease"
printf 'BOOT_IMAGE=/vmlinuz ro quiet\n' >"$PROC/cmdline"
printf '0\n' >"$PROC/irq/0/effective_affinity_list"
printf '8\n' >"$PROC/irq/24/effective_affinity_list"
printf '4\n' >"$PROC/irq/25/effective_affinity_list"

# fake_task <pid> <tid> <ppid> <name> <cpus_allowed> <cgroup|-> [state] [ticks] [cpu]
fake_task() {
  local d="$PROC/$1/task/$2"
  mkdir -p "$d"
  printf 'Name:\t%s\nState:\t%s\nTgid:\t%s\nPid:\t%s\nPPid:\t%s\nCpus_allowed_list:\t%s\n' \
    "$4" "${7:-S}" "$1" "$2" "$3" "$5" >"$d/status"
  # Fields 3.. of /proc/<pid>/stat: state ppid ... utime(14) stime(15) ... processor(39).
  local f=() _
  for _ in $(seq 3 52); do f+=(0); done
  f[0]="${7:-S}" f[1]="$3" f[11]="${8:-0}" f[12]=0 f[36]="${9:-0}"
  printf '%s (%s) %s\n' "$2" "$4" "${f[*]}" >"$d/stat"
  [ "$6" = - ] || printf '0::%s\n' "$6" >"$PROC/$1/cgroup"
}
USER_TERM=/user.slice/user-1000.slice/user@1000.service/app.slice/app-org.gnome.Terminal.slice/vte-spawn-391a851f-72e0-49da-83cb-0fc7065dc7b7.scope
fake_task 1 1 0 systemd 0-11 /init.scope
fake_task 2 2 0 kthreadd 0-11 /
fake_task 10 10 2 ksoftirqd/2 2 /
fake_task 11 11 2 kworker/u24:0 0-11 /
fake_task 12 12 2 kworker/0:1 0 /
fake_task 200 200 1 Runner.Worker 0-11 /system.slice/github-runner-foo.service
fake_task 202 202 1 postgres 0-11 /system.slice/docker-0123456789abcdef0123.scope
fake_task 300 300 1 claude 0-1,4-7,10-11 "$USER_TERM"
fake_task 300 301 1 tokio-rt 0-1,4-7,10-11 "$USER_TERM"
fake_task 310 310 300 rustc 0-11 /user.slice/user-1000.slice/user@1000.service/app.slice/run-p310-i311.scope
fake_task 400 400 1 bash 0-11 /user.slice/user-1000.slice/session-3.scope
fake_task 401 401 1 systemd 0-11 /user.slice/user-1000.slice/user@1000.service/init.scope
fake_task 500 500 1 zeebra 2-3 /user.slice/user-1000.slice/user@1000.service/zbbench.slice/run-p500-i501.scope
fake_task 600 600 1 ghost 0-11 -
# A zombie keeps the affinity it died with (the cpuset update skips it) but can never run again.
fake_task 320 320 300 zypak-sandbox 0-11 /user.slice/user-1000.slice/user@1000.service/app.slice/app-flatpak-x.scope Z

# --- iso_classify ------------------------------------------------------------

# The user manager's fenced slices are grouped by their first child, with ids blanked.
check "classify: terminal scope" "user-fenced	app.slice/app-org.gnome.Terminal.slice" "$(iso_classify "$USER_TERM" 300 1)"
check "classify: transient run scope" "user-fenced	app.slice/run-p*-i*.scope" \
  "$(iso_classify /user.slice/user-1000.slice/user@1000.service/app.slice/run-p310-i311.scope 310 300)"
# zbbench.slice is the bench itself, not an escape.
check "classify: bench slice" "bench	zbbench.slice/run-p*-i*.scope" \
  "$(iso_classify /user.slice/user-1000.slice/user@1000.service/zbbench.slice/run-p5-i6.scope 5 1)"
# An ssh or tty login lives outside user@.service and so outside every fenced slice.
check "classify: login session escapes" "login-session	session-*.scope" \
  "$(iso_classify /user.slice/user-1000.slice/session-3.scope 400 1)"
# The user manager itself is under user@.service but in none of the fenced slices.
check "classify: user manager init.scope" "user-manager-other	init.scope" \
  "$(iso_classify /user.slice/user-1000.slice/user@1000.service/init.scope 401 1)"
# System services group by unit, with container ids blanked so one docker group remains.
check "classify: system unit" "system	github-runner-foo.service" "$(iso_classify /system.slice/github-runner-foo.service 200 1)"
check "classify: docker scope" "system	docker-*.scope" \
  "$(iso_classify /system.slice/docker-0123456789abcdef0123.scope 202 1)"
check "classify: machine slice" "machine	libpod-*.scope" "$(iso_classify /machine.slice/libpod-abcdef0123456789.scope 9 1)"
# Children of kthreadd are kernel threads whatever their cgroup.
check "classify: kernel thread" "kernel	kworker/*:*" "$(iso_classify / 12 2 kworker/0:1)"
check "classify: init" "init	init.scope" "$(iso_classify /init.scope 1 0)"
# A process whose cgroup could not be read is unknown, never assumed fenced.
check "classify: unreadable cgroup" "unknown	?" "$(iso_classify '' 600 1)"

# --- iso_hexmask_to_list -----------------------------------------------------

check "hexmask: low bits" "0-11" "$(iso_hexmask_to_list fff)"
check "hexmask: comma groups" "0-3,32,64-95" "$(iso_hexmask_to_list ffffffff,00000001,0000000f)"
check "hexmask: zero is empty" "" "$(iso_hexmask_to_list 0)"

# --- iso_inventory -----------------------------------------------------------

inv="$(iso_inventory 2-3,8-9)"
check "inventory: is JSON" 0 "$(jq -e . >/dev/null <<<"$inv"; echo $?)"
check "inventory: audited cpus" "2-3,8-9" "$(jq -r .cpus <<<"$inv")"
check "inventory: reservation read" "reserved 1" "$(jq -r '"\(.reservation.status) \(.reservation.ccds)"' <<<"$inv")"
# Both threads of the fenced terminal are counted, and neither meets the bench CPUs.
check "inventory: fenced group" "1 2 0" \
  "$(jq -r '.groups[] | select(.group=="app.slice/app-org.gnome.Terminal.slice") | "\(.procs) \(.tasks) \(.tasks_meeting)"' <<<"$inv")"
# A per-CPU kthread on a bench CPU is bound; a wide kworker is unbound; one on CPU 0 does not meet.
check "inventory: kernel bound meets" "1" "$(jq -r '.classes["kernel-bound"].tasks_meeting' <<<"$inv")"
check "inventory: kernel unbound meets" "2" "$(jq -r '.classes["kernel-unbound"].tasks_meeting' <<<"$inv")"
check "inventory: kernel bound total" "2" "$(jq -r '.classes["kernel-bound"].tasks' <<<"$inv")"
# Escapes are user-owned tasks outside zbbench.slice whose affinity admits a bench CPU.
check "inventory: escapes" "login-session:session-*.scope user-fenced:app.slice/run-p*-i*.scope user-manager-other:init.scope" \
  "$(jq -r '[.escapes[] | "\(.class):\(.group)"] | sort | join(" ")' <<<"$inv")"
check "inventory: escape names its process" "rustc" \
  "$(jq -r '.escapes[] | select(.class=="user-fenced") | .comms_meeting | keys | join(",")' <<<"$inv")"
check "inventory: a zombie is not an escape" "1 0 1" \
  "$(jq -r '.groups[] | select(.group=="app.slice/app-flatpak-x.scope") | "\(.tasks) \(.tasks_meeting) \(.zombies)"' <<<"$inv")"
check "inventory: bench is not an escape" "1" "$(jq -r '.classes.bench.tasks_meeting' <<<"$inv")"
check "inventory: unknown cgroup counted" "1" "$(jq -r '.classes.unknown.procs' <<<"$inv")"
check "inventory: system cpuset" "0-11" "$(jq -r '.cpusets["system.slice"]' <<<"$inv")"
check "inventory: user slice cpuset" "0-1,4-7,10-11" "$(jq -r '.cpusets["user@1000.service/app.slice"]' <<<"$inv")"
check "inventory: workqueue meets" "0-11 true" "$(jq -r '"\(.isolation.workqueue_cpumask) \(.isolation.workqueue_meets)"' <<<"$inv")"
check "inventory: no isolcpus" "null" "$(jq -r '.isolation.cmdline.isolcpus' <<<"$inv")"
# IRQ 24 is steered to bench CPU 8; IRQ 26 has no readable affinity.
check "inventory: irqs" "4 1 1 24:nvme0q3" \
  "$(jq -r '.irqs | "\(.total) \(.meeting) \(.unreadable) \(.list | map("\(.irq):\(.actions)") | join(","))"' <<<"$inv")"
# Without an argument the live reservation's bench CPUs are audited.
check "inventory: default cpus" "2-3,8-9" "$(iso_inventory | jq -r .cpus)"
rm "$ROOT/reserve-state"
iso_inventory >/dev/null 2>&1
check_rc "inventory: no reservation and no cpulist is rc 64" 64 $?
iso_inventory 'x-' >/dev/null 2>&1
check_rc "inventory: malformed cpulist is rc 64" 64 $?

# --- iso_task_lines + iso_sample_aggregate -----------------------------------

# Two snapshots: the bench child and a bound kthread gain ticks on bench CPUs; the escaped rustc
# gains ticks on CPU 9; the fenced claude gains ticks on CPU 4, which is not audited.
snap() { # <tick multiplier>
  local m="$1"
  fake_task 10 10 2 ksoftirqd/2 2 / S $((3 * m)) 2
  fake_task 310 310 300 rustc 0-11 /user.slice/user-1000.slice/user@1000.service/app.slice/run-p310-i311.scope R $((5 * m)) 9
  fake_task 500 500 1 zeebra 2-3 /user.slice/user-1000.slice/user@1000.service/zbbench.slice/run-p500-i501.scope R $((40 * m)) 3
  fake_task 300 300 1 claude 0-1,4-7,10-11 "$USER_TERM" R $((7 * m)) 4
  {
    for c in $(seq 0 11); do printf 'cpu%s %s 0 %s 1000 0 %s 0 0 0 0\n' "$c" $((10 * m)) $((2 * m)) "$m"; done
  } >"$PROC/stat"
}
# A task born after the first snapshot is charged all of its ticks: they all fell in the window.
stream="$(snap 1; printf '@ 100\n'; iso_task_lines; snap 2
  fake_task 700 700 1 cron-job 0-11 /system.slice/crond.service R 4 8
  printf '@ 101\n'; iso_task_lines)"
agg="$(iso_sample_aggregate 2-3,8-9 <<<"$stream")"
check "sample: is JSON" 0 "$(jq -e . >/dev/null <<<"$agg"; echo $?)"
check "sample: snapshots" "2" "$(jq -r .snapshots <<<"$agg")"
check "sample: attributed by class" "bench=40 kernel=3 system=4 user-fenced=5" \
  "$(jq -r '.attributed_ticks | to_entries | map("\(.key)=\(.value)") | sort | join(" ")' <<<"$agg")"
# Per-CPU busy over the window: 4 audited CPUs x (10 user + 2 system + 1 irq) ticks.
check "sample: busy breakdown" "40 8 4 52" \
  "$(jq -r '.cpu_ticks | "\(.user) \(.system) \(.irq) \(.busy)"' <<<"$agg")"
# A user task seen running on an audited CPU is a falsifier of H-A2 and is named.
check "sample: user tasks seen running" "rustc" \
  "$(jq -r '[.seen_running[] | select(.class=="user-fenced") | .comm] | join(",")' <<<"$agg")"
# Attribution is also kept per CPU, so bench cores and their siblings can be judged apart.
check "sample: per-CPU attribution" "2:kernel=3 3:bench=40 8:system=4 9:user-fenced=5" \
  "$(jq -r '.by_cpu | to_entries | map("\(.key):" + (.value | to_entries | map("\(.key)=\(.value)") | join(","))) | sort | join(" ")' <<<"$agg")"
# Coverage is attributed over busy ticks, so a reader can see how much went unnamed.
check "sample: coverage" "52 1" "$(jq -r '"\(.attributed_total) \(.coverage)"' <<<"$agg")"
check "sample: top group" "bench zeebra 40" \
  "$(jq -r '.top[0] | "\(.class) \(.comm) \(.ticks)"' <<<"$agg")"

# --- iso_policy --------------------------------------------------------------

# With placement base 2, one worker sits on CCD 1 and three straddle into CCD 2.
check "policy: one worker, one CCD" \
  "workers=1 ccds=1 placement=2 bench=2-3,8-9 idle_siblings=8 dev_cpus=0-1,4-7,10-11 dev_cores=4" \
  "$(iso_policy 1 2)"
check "policy: three workers, two CCDs" \
  "workers=3 ccds=1,2 placement=2-4 bench=2-5,8-11 idle_siblings=8-10 dev_cpus=0-1,6-7 dev_cores=2" \
  "$(iso_policy 3 2)"
iso_policy 0 2 >/dev/null 2>&1
check_rc "policy: zero workers is rc 64" 64 $?
iso_policy 5 2 >/dev/null 2>&1
check_rc "policy: a placement needing every CCD is rc 64" 64 $?

printf 'bench-isolation-audit: %d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
