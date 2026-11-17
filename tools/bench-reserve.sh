#!/usr/bin/env bash
#
# Fence whole CCDs off for benchmarks, so measurements can run beside builds (#848).
#
#   tools/bench-reserve.sh setup                       print the one-time root step
#   tools/bench-reserve.sh reserve [CCDS]              default CCDS=1,2 (CPUs 8-23 + siblings)
#   tools/bench-reserve.sh status                      rc 0 reserved, 1 released, 2 failed/inconsistent
#   tools/bench-reserve.sh run <owner> <cpulist> <command> [args...]
#   tools/bench-reserve.sh release [--force]
#
# The 5995WX's L3 is per CCD (8 x 32 MB), so a reserved CCD shares no cache with the rest of the
# box. `reserve` restricts the user manager's app/background/session slices to the other CCDs;
# `run` launches the command in `zbbench.slice` pinned to <cpulist>, under a CCD-scoped
# `tools/benchlock.sh` (ZEEBRA_BENCHLOCK_CPUS), so runs on disjoint reserved CCDs may overlap while
# an unscoped benchlock run still excludes them all.
#
# What a reservation does NOT fence: DRAM bandwidth and the Infinity Fabric, the package power
# budget (boost clock, #827), and system.slice daemons, which this unprivileged script cannot move.
# Which subjects survive that is a calibration result — see docs/guide/benchmarking.md — not an
# assumption. Reserve the CCDs a measurement's placement is defined on: M29 pins w workers to
# CPUs 8..8+w-1, which is why the default is CCDs 1-2.
#
# A reservation is shared state: it takes the CPUs out of every other session's cpuset, so their
# `taskset` onto them fails with "Invalid argument" (#194 hit this during the calibration). Reserve
# for a measurement session and release when it ends. Everything is --runtime: a reboot or logout
# also releases it, along with the state file in $XDG_RUNTIME_DIR.
#
# Test seams (tools/test/bench-reserve-test.sh): ZEEBRA_BENCH_RESERVE_SYS relocates
# /sys/devices/system/cpu, ZEEBRA_BENCH_RESERVE_CGROUP the user manager's cgroup, and
# ZEEBRA_BENCH_RESERVE_STATE the state file.

set -uo pipefail

# shellcheck source=cpu-context.sh
. "$(dirname "${BASH_SOURCE[0]}")/cpu-context.sh"

BR_FENCED_SLICES="app.slice background.slice session.slice"
BR_BENCH_SLICE="zbbench.slice"

br_sys() { printf '%s' "${ZEEBRA_BENCH_RESERVE_SYS:-/sys/devices/system/cpu}"; }
br_cgroup() {
  local uid
  uid="$(id -u)"
  printf '%s' "${ZEEBRA_BENCH_RESERVE_CGROUP:-/sys/fs/cgroup/user.slice/user-$uid.slice/user@$uid.service}"
}
br_state() { printf '%s' "${ZEEBRA_BENCH_RESERVE_STATE:-${XDG_RUNTIME_DIR:-/run/user/$(id -u)}/zeebra-bench-reserve}"; }

# ---------------------------------------------------------------------------------------------
# The pure half.
# ---------------------------------------------------------------------------------------------

br_compress() { # <id>...  ->  canonical cpulist
  local out="" lo="" prev="" c
  for c in $(printf '%s\n' "$@" | sort -nu); do
    if [ -n "$prev" ] && [ "$c" -eq $((prev + 1)) ]; then
      prev="$c"
      continue
    fi
    [ -z "$lo" ] || out+="${out:+,}$([ "$lo" = "$prev" ] && echo "$lo" || echo "$lo-$prev")"
    lo="$c" prev="$c"
  done
  [ -z "$lo" ] || out+="${out:+,}$([ "$lo" = "$prev" ] && echo "$lo" || echo "$lo-$prev")"
  printf '%s' "$out"
}

br_same_set() { # <cpulist> <cpulist>  ->  rc 0 when equal as sets
  local a b
  a="$(ctx_expand_cpulist "$1")" || return 1
  b="$(ctx_expand_cpulist "$2")" || return 1
  # shellcheck disable=SC2086  # deliberate splitting into ids
  [ "$(br_compress $a)" = "$(br_compress $b)" ]
}

# Which CPUs a reservation of CCDS fences, as `bench=` and `rest=` lines. A CCD's SMT siblings
# share its L3 and so come with it. rc 64 for a CCD that does not exist or a plan leaving no rest,
# rc 2 when the topology cannot be read.
br_plan() { # <ccds, comma or space separated>
  local online cpus c id want bench=() rest=() wanted=" ${1//,/ } "
  online="$(ctx_read "$(br_sys)/online")" || return 2
  cpus="$(ctx_expand_cpulist "$online")" || return 2
  for want in $wanted; do
    case "$want" in *[!0-9]*) return 64 ;; esac
  done
  local seen=" "
  for c in $cpus; do
    id="$(ctx_read "$(br_sys)/cpu$c/cache/index3/id")" || return 2
    case "$id" in *[!0-9]*) return 2 ;; esac
    seen+="$id "
    if [[ "$wanted" == *" $id "* ]]; then bench+=("$c"); else rest+=("$c"); fi
  done
  for want in $wanted; do
    [[ "$seen" == *" $want "* ]] || { printf 'bench-reserve: no CCD %s\n' "$want" >&2; return 64; }
  done
  [ "${#rest[@]}" -gt 0 ] || { printf 'bench-reserve: that leaves no CPUs for anything else\n' >&2; return 64; }
  printf 'bench=%s\nrest=%s\n' "$(br_compress "${bench[@]}")" "$(br_compress "${rest[@]}")"
}

br_subset() { # <inner-cpulist> <outer-cpulist>  ->  rc 0 inside, 1 not, 64 malformed
  local inner outer c
  inner="$(ctx_expand_cpulist "$1")" || return 64
  outer=" $(ctx_expand_cpulist "$2") " || return 64
  for c in $inner; do [[ "$outer" == *" $c "* ]] || return 1; done
}

# Whether the recorded reservation is what the kernel is actually enforcing. Only `reserved` lets
# `run` proceed: a state file over an unfenced cgroup is the case that would publish contaminated
# figures as clean ones.
br_classify() { # <state-rest-or-empty> <app.slice-effective> <online>
  if [ -n "$1" ]; then
    if br_same_set "$1" "$2"; then echo reserved; else echo inconsistent; fi
  elif br_same_set "$2" "$3"; then
    echo released
  else
    echo inconsistent
  fi
}

br_delegated() { # <cgroup.controllers>  ->  rc 0 cpuset delegated, 1 not, 2 unreadable
  local line
  line="$(ctx_read "$1")" || return 2
  [[ " $line " == *" cpuset "* ]]
}

br_setup_text() {
  cat <<'SETUP'
One-time root step: delegate the cpuset controller to your user manager, so reservations and
pinned runs need no sudo afterwards.

  sudo mkdir -p /etc/systemd/system/user@.service.d
  printf '[Service]\nDelegate=cpu cpuset io memory pids\n' \
    | sudo tee /etc/systemd/system/user@.service.d/zeebra-cpuset.conf
  sudo systemctl daemon-reload
  systemctl --user daemon-reexec

If `cpuset` is still missing from the user manager's cgroup.controllers afterwards, log out and
back in. Undo by removing the drop-in and repeating the last two commands.
SETUP
}

# ---------------------------------------------------------------------------------------------
# The imperative half.
# ---------------------------------------------------------------------------------------------

br_state_get() { # <key>  ->  value from the state file; rc 1 when there is no state file
  local f
  f="$(br_state)"
  [ -e "$f" ] || return 1
  sed -n "s/^$1=//p" "$f"
}

br_status() { # [--quiet]
  local quiet="${1:-}" cg rest bench eff online verdict
  cg="$(br_cgroup)"
  online="$(ctx_read "$(br_sys)/online")" || { echo "bench-reserve: cannot read online CPUs" >&2; return 2; }
  rest="$(br_state_get rest)" || rest=""
  bench="$(br_state_get bench)" || bench=""
  # Before cpuset is enabled for app.slice the file is absent, which means unrestricted.
  eff="$(ctx_read "$cg/app.slice/cpuset.cpus.effective")" || eff="$online"
  verdict="$(br_classify "$rest" "$eff" "$online")"
  if [ "$quiet" != --quiet ]; then
    printf 'status=%s ccds=%s bench=%s rest=%s app.slice=%s\n' \
      "$verdict" "$(br_state_get ccds 2>/dev/null || true)" "${bench:--}" "${rest:--}" "$eff"
  fi
  case "$verdict" in
    reserved) return 0 ;;
    released) return 1 ;;
    *) return 2 ;;
  esac
}

br_reserve() { # [ccds]
  local ccds="${1:-1,2}" cg plan bench rest s rc=0
  cg="$(br_cgroup)"
  br_delegated "$cg/cgroup.controllers" || rc=$?
  if [ "$rc" -ne 0 ]; then
    printf 'bench-reserve: cpuset is not delegated to the user manager (%s)\n\n' "$cg" >&2
    br_setup_text >&2
    return 2
  fi
  plan="$(br_plan "$ccds")" || return $?
  bench="$(sed -n 's/^bench=//p' <<<"$plan")"
  rest="$(sed -n 's/^rest=//p' <<<"$plan")"
  local current
  if current="$(br_state_get bench)" && [ "$current" != "$bench" ]; then
    printf 'bench-reserve: already reserved %s; release first\n' "$current" >&2
    return 1
  fi
  systemctl --user set-property --runtime "$BR_BENCH_SLICE" AllowedCPUs="$bench" || return 2
  for s in $BR_FENCED_SLICES; do
    systemctl --user set-property --runtime "$s" AllowedCPUs="$rest" || return 2
  done
  printf 'ccds=%s\nbench=%s\nrest=%s\nat=%s\n' "${ccds// /,}" "$bench" "$rest" \
    "$(date --iso-8601=seconds)" >"$(br_state)" || return 2
  br_status
}

br_release() { # [--force]
  local cg procs s
  cg="$(br_cgroup)"
  procs="$(cat "$cg/$BR_BENCH_SLICE"/*/cgroup.procs 2>/dev/null | wc -l)"
  if [ "$procs" -gt 0 ] && [ "${1:-}" != --force ]; then
    printf 'bench-reserve: %s process(es) still running in %s; wait, or --force\n' "$procs" "$BR_BENCH_SLICE" >&2
    return 1
  fi
  for s in $BR_FENCED_SLICES; do
    systemctl --user set-property --runtime "$s" AllowedCPUs= || return 2
  done
  rm -f "$(br_state)"
  br_status
  [ $? -eq 1 ]
}

br_run() { # <owner> <cpulist> <command> [args...]
  local owner="$1" cpus="$2" bench rc=0
  shift 2
  br_status --quiet || rc=$?
  if [ "$rc" -ne 0 ]; then
    printf 'bench-reserve: no verified reservation (status rc %s); see `%s status`\n' "$rc" "$0" >&2
    return 2
  fi
  bench="$(br_state_get bench)"
  br_subset "$cpus" "$bench" || rc=$?
  if [ "$rc" -ne 0 ]; then
    printf 'bench-reserve: %s is not inside the reservation %s\n' "$cpus" "$bench" >&2
    return 64
  fi
  ZEEBRA_BENCHLOCK_CPUS="$cpus" exec bash "$(dirname "${BASH_SOURCE[0]}")/benchlock.sh" "$owner" \
    systemd-run --user --scope --quiet --collect --slice="$BR_BENCH_SLICE" -p AllowedCPUs="$cpus" -- \
    taskset --cpu-list "$cpus" "$@"
}

br_usage() {
  sed -n '3,8p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//' >&2
}

br_main() {
  local cmd="${1:-}"
  [ "$#" -gt 0 ] && shift
  case "$cmd" in
    setup) br_setup_text ;;
    reserve) br_reserve "$@" ;;
    release) br_release "$@" ;;
    status) br_status "$@" ;;
    run)
      [ "$#" -ge 3 ] || { br_usage; return 64; }
      br_run "$@"
      ;;
    *) br_usage; return 64 ;;
  esac
}

if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  br_main "$@"
  exit $?
fi
