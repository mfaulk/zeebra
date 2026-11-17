#!/usr/bin/env bash
#
# Snapshot the CPU context a measurement ran in, as one JSON line (#834, policy from #827).
#
#   tools/cpu-context.sh CPULIST          e.g. tools/cpu-context.sh 8-23
#
# #827 found that a 16-worker burst holds the 5995WX at its all-core clock (~3.99 GHz rather than
# ~4.54) for 200–500 ms afterwards, and that cross-CCD placement moves serial-stage timings. Both
# change a wall time without changing the work, so the M29 protocol records them beside every
# timing — and never corrects for them: process wall stays authoritative, and a clock-normalized
# figure is an inference, not a measurement. Take a snapshot before and after each child.
#
# Recorded: the 1/5/15-minute load, each listed CPU's L3 domain (the CCD on Zen 3), core id and
# current scaling frequency, the number of distinct L3 domains the list spans, the governor and
# boost state, and how many compiler/linker processes were running (`cargo` and `rustc` from other
# worktrees are what `benchlock` cannot exclude).
#
#   ZEEBRA_CPU_CONTEXT_SYS    relocates /sys/devices/system/cpu (tests supply a synthetic tree)
#   ZEEBRA_CPU_CONTEXT_PROC   relocates /proc
#
# Exit status: 0 snapshot printed; 2 the load or a listed CPU's topology could not be read — a
# context with holes is not a context; 64 usage. An unreadable frequency is `null`, not a failure:
# some drivers do not expose one, and #827's rule is "where available".

set -uo pipefail

ctx_sys() { printf '%s' "${ZEEBRA_CPU_CONTEXT_SYS:-/sys/devices/system/cpu}"; }
ctx_proc() { printf '%s' "${ZEEBRA_CPU_CONTEXT_PROC:-/proc}"; }

# Process names counted as compiler activity. /proc/<pid>/comm is truncated to 15 characters.
CTX_COMPILERS="cargo rustc rustdoc cc1 cc1plus ld ld.lld ld.mold mold rust-lld lld clang gcc"

ctx_expand_cpulist() { # <list>  ->  space-separated CPU ids; rc 64 on a malformed list
  local list="$1" part lo hi out=()
  [ -n "$list" ] || return 64
  local IFS=,
  for part in $list; do
    if [[ "$part" =~ ^([0-9]+)-([0-9]+)$ ]]; then
      lo="${BASH_REMATCH[1]}" hi="${BASH_REMATCH[2]}"
      [ "$lo" -le "$hi" ] || return 64
      while [ "$lo" -le "$hi" ]; do out+=("$lo"); lo=$((lo + 1)); done
    elif [[ "$part" =~ ^[0-9]+$ ]]; then
      out+=("$part")
    else
      return 64
    fi
  done
  printf '%s' "${out[*]}" | tr ',' ' '
}

ctx_read() { # <path>  ->  first line, rc 2 when unreadable or empty
  local line=""
  { IFS= read -r line <"$1"; } 2>/dev/null || [ -n "${line:-}" ] || return 2
  [ -n "$line" ] || return 2
  printf '%s' "$line"
}

ctx_l3() { ctx_read "$(ctx_sys)/cpu$1/cache/index3/shared_cpu_list"; }
ctx_core() { ctx_read "$(ctx_sys)/cpu$1/topology/core_id"; }
ctx_khz() { ctx_read "$(ctx_sys)/cpu$1/cpufreq/scaling_cur_freq"; }

ctx_compiler_count() { # -> number of running compiler/linker processes
  local comm count=0 name
  for comm in "$(ctx_proc)"/[0-9]*/comm; do
    name="$(ctx_read "$comm")" || continue
    case " $CTX_COMPILERS " in *" $name "*) count=$((count + 1)) ;; esac
  done
  printf '%s' "$count"
}

ctx_json_string() { printf '"%s"' "${1//\"/\\\"}"; }

ctx_snapshot() { # <cpulist>
  local cpus cpu l3 core khz load l1 l5 l15 rest entries=() domains=() governor boost
  cpus="$(ctx_expand_cpulist "$1")" || return 64
  load="$(ctx_read "$(ctx_proc)/loadavg")" || return 2
  read -r l1 l5 l15 rest <<<"$load"
  for cpu in $cpus; do
    l3="$(ctx_l3 "$cpu")" || return 2
    core="$(ctx_core "$cpu")" || return 2
    khz="$(ctx_khz "$cpu")" || khz=null
    entries+=("{\"cpu\":$cpu,\"l3\":$(ctx_json_string "$l3"),\"core\":$core,\"khz\":$khz}")
    case " ${domains[*]-} " in *" $l3 "*) ;; *) domains+=("$l3") ;; esac
  done
  governor="$(ctx_read "$(ctx_sys)/cpu${cpus%% *}/cpufreq/scaling_governor")" || governor=""
  boost="$(ctx_read "$(ctx_sys)/cpufreq/boost")" || boost=""
  local IFS=,
  printf '{"at":%s,"load1":%s,"load5":%s,"load15":%s,"cpulist":%s,"l3_domains":%s,' \
    "$(ctx_json_string "$(date -u +%Y-%m-%dT%H:%M:%S.%3NZ)")" "$l1" "$l5" "$l15" \
    "$(ctx_json_string "$1")" "${#domains[@]}"
  printf '"governor":%s,"boost":%s,"compilers":%s,"cpus":[%s]}\n' \
    "$(ctx_json_string "$governor")" "$(ctx_json_string "$boost")" "$(ctx_compiler_count)" \
    "${entries[*]}"
}

ctx_main() {
  if [ $# -ne 1 ]; then
    echo "usage: tools/cpu-context.sh CPULIST" >&2
    return 64
  fi
  ctx_snapshot "$1"
}

if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  ctx_main "$@"
fi
