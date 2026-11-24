#!/usr/bin/env bash
#
# Snapshot the CPU context a measurement ran in, as one JSON line (#834, policy from #827; #968).
#
#   tools/cpu-context.sh CPULIST                       e.g. tools/cpu-context.sh 8-23
#   tools/cpu-context.sh --interval SECONDS CPULIST    adds busy % per CPU over the window
#
# #827 found that a 16-worker burst holds the 5995WX at its all-core clock (~3.99 GHz rather than
# ~4.54) for 200–500 ms afterwards, and that cross-CCD placement moves serial-stage timings. Both
# change a wall time without changing the work, so the M29 protocol records them beside every
# timing — and never corrects for them: process wall stays authoritative, and a clock-normalized
# figure is an inference, not a measurement. Take a snapshot before and after each child.
#
# Fields are only ever added, never renamed or removed. `stat` carries raw /proc/stat jiffies for
# the listed CPUs and their SMT siblings and `rest_stat` their sum over every other online CPU, so
# a before/after pair gives busy fractions over the attempt (tools/bench_contamination.py). The
# field list is in docs/guide/benchmarking.md, *Recording the CPU context of a multicore timing*.
#
#   ZEEBRA_CPU_CONTEXT_SYS    relocates /sys/devices/system/cpu (tests supply a synthetic tree)
#   ZEEBRA_CPU_CONTEXT_PROC   relocates /proc
#   ZEEBRA_CPU_CONTEXT_CLASS  relocates /sys/class (powercap, hwmon)
#   ZEEBRA_CPU_CONTEXT_CGROUP   relocates /sys/fs/cgroup (zbbench.slice pressure)
#   ZEEBRA_CPU_CONTEXT_RESCTRL  relocates /sys/fs/resctrl (MBM bandwidth counters)
#   ZEEBRA_BENCHLOCK_DIR      where benchlock.log lives, as for tools/benchlock.sh
#
# Exit status: 0 snapshot printed; 2 the load or a listed CPU's topology could not be read — a
# context with holes is not a context; 64 usage. An unreadable frequency, RAPL counter or
# temperature is `null`, not a failure: some drivers do not expose one, RAPL energy is root-only by
# default, and #827's rule is "where available".

set -uo pipefail

ctx_sys() { printf '%s' "${ZEEBRA_CPU_CONTEXT_SYS:-/sys/devices/system/cpu}"; }
ctx_proc() { printf '%s' "${ZEEBRA_CPU_CONTEXT_PROC:-/proc}"; }
ctx_class() { printf '%s' "${ZEEBRA_CPU_CONTEXT_CLASS:-/sys/class}"; }

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
ctx_num_or_null() { # <path>  ->  the integer in it, or null
  local v
  v="$(ctx_read "$1")" && [[ "$v" =~ ^[0-9]+$ ]] && printf '%s' "$v" || printf null
}

ctx_count_comm() { # <name>...  ->  number of running processes whose comm is one of the names
  # One `cat` rather than a read per process: there are thousands, and a process exiting
  # mid-scan only drops out of the count.
  cat "$(ctx_proc)"/[0-9]*/comm 2>/dev/null |
    awk -v want=" $* " 'index(want, " " $0 " ") { n++ } END { printf "%d", n }'
}

# shellcheck disable=SC2086  # deliberate splitting of the name list
ctx_compiler_count() { ctx_count_comm $CTX_COMPILERS; }

ctx_json_string() { printf '"%s"' "${1//\"/\\\"}"; }

ctx_siblings() { # <cpu>...  ->  SMT siblings of the CPUs that are not themselves listed
  local cpu sib list out=() listed=" $* "
  for cpu in "$@"; do
    list="$(ctx_read "$(ctx_sys)/cpu$cpu/topology/thread_siblings_list")" || continue
    for sib in $(ctx_expand_cpulist "$list"); do
      case "$listed ${out[*]-} " in *" $sib "*) ;; *) out+=("$sib") ;; esac
    done
  done
  printf '%s' "${out[*]-}"
}

# busy = user + nice + system + irq + softirq + steal; total = busy + idle + iowait. Guest time is
# already inside user. `%.0f` rather than `%d`: mawk's %d wraps at 2^31 jiffies.
ctx_stat_tokens() { # <cpu>...  ->  "cpu:busy:total" per listed CPU, in /proc/stat order
  awk -v want=" $* " '$1 ~ /^cpu[0-9]+$/ { c = substr($1, 4)
    if (index(want, " " c " ")) { b = $2 + $3 + $4 + $7 + $8 + $9
      printf "%s%s:%.0f:%.0f", sep, c, b, b + $5 + $6; sep = " " } }' "$(ctx_proc)/stat"
}

ctx_stat_sum() { # <cpu>...  ->  "busy:total:ncpus" summed over the listed CPUs
  ctx_stat_tokens "$@" | awk '{ for (i = 1; i <= NF; i++) { split($i, f, ":"); b += f[2]; t += f[3] }
    printf "%.0f:%.0f:%d", b, t, NF }'
}

ctx_busy_pct() { # <tokens-before> <tokens-after>  ->  JSON array of {cpu, pct}
  awk -v a="$1" -v b="$2" 'BEGIN { n = split(a, x, " ")
    for (i = 1; i <= n; i++) { split(x[i], f, ":"); B[f[1]] = f[2]; T[f[1]] = f[3] }
    m = split(b, y, " ")
    for (i = 1; i <= m; i++) { split(y[i], g, ":"); if (!(g[1] in T)) continue
      dt = g[3] - T[g[1]]; pct = dt > 0 ? 100 * (g[2] - B[g[1]]) / dt : 0
      out = out sep sprintf("{\"cpu\":%s,\"pct\":%.1f}", g[1], pct); sep = "," }
    printf "[%s]", out }'
}

ctx_clock_mode() { # <boost> <max_khz>...  ->  boost | fixed@<MHz> | unknown
  local boost="$1" k first=""
  shift
  [ "$boost" = 1 ] && { printf boost; return; }
  for k in "$@"; do
    [[ "$k" =~ ^[0-9]+$ ]] || { printf unknown; return; }
    [ -z "$first" ] && first="$k"
    [ "$k" = "$first" ] || { printf unknown; return; }
  done
  if [ "$boost" = 0 ] && [ -n "$first" ]; then printf 'fixed@%s' "$((first / 1000))"; else printf unknown; fi
}

ctx_temp_mc() { # -> k10temp Tctl in millidegrees C, or null
  local h
  for h in "$(ctx_class)"/hwmon/hwmon*; do
    [ "$(ctx_read "$h/name")" = k10temp ] && { ctx_num_or_null "$h/temp1_input"; return; }
  done
  printf null
}

# benchlock owners holding the lock now: a START with no later END, from a process still alive.
ctx_benchlock_open() { # -> JSON array of {owner, pid}
  local log owner pid out=()
  log="${ZEEBRA_BENCHLOCK_DIR:-$HOME/.zeebra}/benchlock.log"
  [ -r "$log" ] || { printf '[]'; return; }
  while read -r owner pid; do
    [ -d "$(ctx_proc)/$pid" ] && out+=("{\"owner\":$(ctx_json_string "$owner"),\"pid\":$pid}")
  done < <(awk '$2 == "START" || $2 == "END" { p = $4; sub(/^pid=/, "", p); st[p] = $2; ow[p] = $3 }
    END { for (p in st) if (st[p] == "START") print ow[p], p }' "$log" | sort -k2n)
  local IFS=,
  printf '[%s]' "${out[*]-}"
}

# --- Interference telemetry (#1105). Metrics, not rules: no verdict reads these yet. Each is a
# value, null, or {"unavailable": "<reason>"}, so a missing source is never read as zero.
CTX_TELEMETRY=1

ctx_unavailable() { printf '{"unavailable":"%s"}' "$1"; }

ctx_list_meets() { # <cpulist> <cpu>...  ->  rc 0 when any of the CPUs is in the list
  local list="$1"
  shift
  awk -v l="$list" -v want="$*" 'BEGIN { n = split(l, p, ","); m = split(want, w, " ")
    for (i = 1; i <= n; i++) { k = split(p[i], r, "-"); lo = r[1] + 0; hi = (k > 1 ? r[2] : r[1]) + 0
      for (j = 1; j <= m; j++) if (w[j] + 0 >= lo && w[j] + 0 <= hi) exit 0 }
    exit 1 }'
}

# A process counts as on the bench when its affinity (`Cpus_allowed_list`, which already reflects
# its cpuset) admits a bench CPU or sibling. One whose status cannot be read counts as on the bench:
# it may run anywhere, and the conservative reading is the one that cannot hide interference.
ctx_placed_count() { # <cpu>... -- <name>...  ->  "<on bench> <elsewhere>"
  local cpus=() f allowed on=0 off=0
  while [ $# -gt 0 ] && [ "$1" != -- ]; do cpus+=("$1"); shift; done
  shift
  [ $# -gt 0 ] || { printf '0 0'; return; }
  for f in $(grep -l -x -F -f <(printf '%s\n' "$@") "$(ctx_proc)"/[0-9]*/comm 2>/dev/null); do
    allowed="$(awk '$1 == "Cpus_allowed_list:" { print $2 }' "${f%/comm}/status" 2>/dev/null)"
    if [ -z "$allowed" ] || ctx_list_meets "$allowed" "${cpus[@]}"; then on=$((on + 1)); else off=$((off + 1)); fi
  done
  printf '%d %d' "$on" "$off"
}

ctx_psi_file() { # <path> <label>  ->  {some_us, full_us} totals, or unavailable
  [ -r "$1" ] || { ctx_unavailable "no $2"; return; }
  awk '$1 == "some" || $1 == "full" { for (i = 2; i <= NF; i++) if ($i ~ /^total=/) v[$1] = substr($i, 7) }
    END { printf "{\"some_us\":%s,\"full_us\":%s}", ("some" in v) ? v["some"] : "null",
          ("full" in v) ? v["full"] : "null" }' "$1"
}

ctx_psi() { # <dir> <label prefix> <file suffix>  ->  {cpu, memory, io}
  printf '{"cpu":%s,"memory":%s,"io":%s}' "$(ctx_psi_file "$1/cpu$3" "$2cpu$3")" \
    "$(ctx_psi_file "$1/memory$3" "$2memory$3")" "$(ctx_psi_file "$1/io$3" "$2io$3")"
}

ctx_psi_slice() { # -> pressure of the cgroup tools/bench-reserve.sh runs measurements in
  local d="${ZEEBRA_CPU_CONTEXT_CGROUP:-/sys/fs/cgroup}/zbbench.slice"
  [ -d "$d" ] || { ctx_unavailable "no zbbench.slice"; return; }
  ctx_psi "$d" zbbench.slice/ .pressure
}

ctx_vmstat() { # -> swap, reclaim scan/steal (summed over sources) and major faults, machine-wide
  local f
  f="$(ctx_proc)/vmstat"
  [ -r "$f" ] || { ctx_unavailable "no vmstat"; return; }
  awk 'function v(k) { return (k in s) ? sprintf("%.0f", s[k]) : "null" }
    $1 == "pswpin" || $1 == "pswpout" || $1 == "pgmajfault" { s[$1] = $2 }
    $1 ~ /^pgscan_/ { s["pgscan"] += $2 } $1 ~ /^pgsteal_/ { s["pgsteal"] += $2 }
    END { printf "{\"pswpin\":%s,\"pswpout\":%s,\"pgscan\":%s,\"pgsteal\":%s,\"pgmajfault\":%s}",
          v("pswpin"), v("pswpout"), v("pgscan"), v("pgsteal"), v("pgmajfault") }' "$f"
}

ctx_mbm() { # -> resctrl MBM total bytes over every L3 domain (default group: the whole machine)
  local d f v sum=0 n=0
  d="${ZEEBRA_CPU_CONTEXT_RESCTRL:-/sys/fs/resctrl}/mon_data"
  [ -d "$d" ] || { ctx_unavailable "resctrl not mounted"; return; }
  for f in "$d"/mon_L3_*/mbm_total_bytes; do
    [ -e "$f" ] || continue
    v="$(ctx_read "$f")" && [[ "$v" =~ ^[0-9]+$ ]] || { ctx_unavailable "mbm_total_bytes unreadable"; return; }
    sum=$((sum + v)) n=$((n + 1))
  done
  [ "$n" -gt 0 ] || { ctx_unavailable "no mbm_total_bytes"; return; }
  printf '%s' "$sum"
}

ctx_ccd_stat() { # -> JSON array of {l3, busy, total, cpus} per L3 domain over every online CPU
  local online
  online="$(ctx_read "$(ctx_sys)/online")" || { printf null; return; }
  awk -v sys="$(ctx_sys)" -v want=" $(ctx_expand_cpulist "$online") " '
    $1 ~ /^cpu[0-9]+$/ { c = substr($1, 4); if (!index(want, " " c " ")) next
      l3 = "unknown"; f = sys "/cpu" c "/cache/index3/shared_cpu_list"; line = ""
      if ((getline line < f) > 0 && line != "") l3 = line
      close(f)
      if (!(l3 in N)) order[++k] = l3
      B[l3] += $2 + $3 + $4 + $7 + $8 + $9; T[l3] += $2 + $3 + $4 + $5 + $6 + $7 + $8 + $9; N[l3]++ }
    END { for (i = 2; i <= k; i++) { x = order[i]
        for (j = i - 1; j > 0 && order[j] > x; j--) order[j + 1] = order[j]
        order[j + 1] = x }
      for (i = 1; i <= k; i++) out = out (i > 1 ? "," : "") \
        sprintf("{\"l3\":\"%s\",\"busy\":%.0f,\"total\":%.0f,\"cpus\":%d}", order[i], B[order[i]], T[order[i]], N[order[i]])
      printf "[%s]", out }' "$(ctx_proc)/stat"
}

# Runnable tasks whose last CPU (field 39 of /proc/<pid>/stat) is a bench CPU or sibling, other than
# this script and its children. A snapshot names them; it does not see what ran between snapshots.
ctx_bench_running() { # <cpu>...  ->  JSON array of {pid, comm, cpu}, at most 16
  cat "$(ctx_proc)"/[0-9]*/stat 2>/dev/null | awk -v want=" $* " -v self="$$" '{
    o = index($0, "("); r = 0
    for (i = length($0); i > o; i--) if (substr($0, i, 1) == ")") { r = i; break }
    if (!o || !r) next
    pid = substr($0, 1, o - 2); comm = substr($0, o + 1, r - o - 1)
    n = split(substr($0, r + 2), f, " ")
    # Our children (cat, awk) by parent pid, unless we are init and every orphan is "ours".
    if (n < 37 || f[1] != "R" || pid == self || (self > 1 && f[2] == self) || !index(want, " " f[37] " ")) next
    if (++k > 16) next
    gsub(/\\/, "\\\\", comm); gsub(/"/, "\\\"", comm)
    out = out sep sprintf("{\"pid\":%s,\"comm\":\"%s\",\"cpu\":%s}", pid, comm, f[37]); sep = "," }
    END { printf "[%s]", out }'
}

ctx_telemetry_json() { # <bench cpus> <sibling cpus>  ->  the #1105 fields, comma-led
  local placed workers
  # shellcheck disable=SC2086  # deliberate splitting of the CPU and name lists
  placed="$(ctx_placed_count $1 $2 -- $CTX_COMPILERS)"
  # shellcheck disable=SC2086
  workers="$(ctx_placed_count $1 $2 -- Runner.Worker)"
  printf ',"telemetry":%s,"compilers_on_bench":%s,"compilers_elsewhere":%s,"runner_workers_on_bench":%s' \
    "$CTX_TELEMETRY" "${placed% *}" "${placed#* }" "${workers% *}"
  printf ',"psi":%s,"psi_bench_slice":%s,"vmstat":%s,"mbm_bytes":%s,"ccd_stat":%s' \
    "$(ctx_psi "$(ctx_proc)/pressure" pressure/ '')" "$(ctx_psi_slice)" "$(ctx_vmstat)" "$(ctx_mbm)" \
    "$(ctx_ccd_stat)"
  # shellcheck disable=SC2086
  printf ',"bench_running":%s' "$(ctx_bench_running $1 $2)"
}

ctx_stat_json() { # <bench cpus> <sibling cpus>  ->  JSON array of {cpu, role, busy, total}
  local tok c b t role out=()
  for tok in $(ctx_stat_tokens $1 $2); do
    IFS=: read -r c b t <<<"$tok"
    role=bench; case " $2 " in *" $c "*) role=sibling ;; esac
    out+=("{\"cpu\":$c,\"role\":\"$role\",\"busy\":$b,\"total\":$t}")
  done
  local IFS=,
  printf '[%s]' "${out[*]-}"
}

ctx_rest_json() { # <bench cpus> <sibling cpus>  ->  {busy,total,cpus} over the other online CPUs
  local online c rest=() b t n
  online="$(ctx_read "$(ctx_sys)/online")" || { printf null; return; }
  for c in $(ctx_expand_cpulist "$online"); do
    case " $1 $2 " in *" $c "*) ;; *) rest+=("$c") ;; esac
  done
  [ "${#rest[@]}" -gt 0 ] || { printf null; return; }
  IFS=: read -r b t n <<<"$(ctx_stat_sum "${rest[@]}")"
  printf '{"busy":%s,"total":%s,"cpus":%s}' "${b:-0}" "${t:-0}" "${n:-0}"
}

ctx_snapshot() { # <cpulist> [stat tokens from the start of an interval]
  local cpus cpu l3 core khz load l1 l5 l15 rest entries=() domains=() governor boost maxes=()
  local sibs min max kernel rapl
  rapl="$(ctx_class)/powercap/intel-rapl:0"
  cpus="$(ctx_expand_cpulist "$1")" || return 64
  load="$(ctx_read "$(ctx_proc)/loadavg")" || return 2
  read -r l1 l5 l15 rest <<<"$load"
  for cpu in $cpus; do
    l3="$(ctx_l3 "$cpu")" || return 2
    core="$(ctx_core "$cpu")" || return 2
    khz="$(ctx_khz "$cpu")" || khz=null
    min="$(ctx_num_or_null "$(ctx_sys)/cpu$cpu/cpufreq/scaling_min_freq")"
    max="$(ctx_num_or_null "$(ctx_sys)/cpu$cpu/cpufreq/scaling_max_freq")"
    maxes+=("$max")
    entries+=("{\"cpu\":$cpu,\"l3\":$(ctx_json_string "$l3"),\"core\":$core,\"khz\":$khz,\"min_khz\":$min,\"max_khz\":$max}")
    case " ${domains[*]-} " in *" $l3 "*) ;; *) domains+=("$l3") ;; esac
  done
  # shellcheck disable=SC2086  # deliberate splitting into ids
  sibs="$(ctx_siblings $cpus)"
  governor="$(ctx_read "$(ctx_sys)/cpu${cpus%% *}/cpufreq/scaling_governor")" || governor=""
  boost="$(ctx_read "$(ctx_sys)/cpufreq/boost")" || boost=""
  kernel="$(ctx_read "$(ctx_proc)/sys/kernel/osrelease")" || kernel=""
  local IFS=,
  printf '{"at":%s,"load1":%s,"load5":%s,"load15":%s,"cpulist":%s,"l3_domains":%s,' \
    "$(ctx_json_string "$(date -u +%Y-%m-%dT%H:%M:%S.%3NZ)")" "$l1" "$l5" "$l15" \
    "$(ctx_json_string "$1")" "${#domains[@]}"
  printf '"governor":%s,"boost":%s,"compilers":%s,"cpus":[%s],' \
    "$(ctx_json_string "$governor")" "$(ctx_json_string "$boost")" "$(ctx_compiler_count)" \
    "${entries[*]}"
  IFS=$' \t\n'
  printf '"kernel":%s,"clock":"%s","siblings":%s,"stat":%s,"rest_stat":%s,' \
    "$(ctx_json_string "$kernel")" "$(ctx_clock_mode "$boost" "${maxes[@]}")" \
    "$(ctx_json_string "$(ctx_compress_ids $sibs)")" "$(ctx_stat_json "$cpus" "$sibs")" \
    "$(ctx_rest_json "$cpus" "$sibs")"
  printf '"rapl_uj":%s,"rapl_max_uj":%s,"temp_mc":%s,"runner_listeners":%s,"runner_workers":%s,' \
    "$(ctx_num_or_null "$rapl/energy_uj")" "$(ctx_num_or_null "$rapl/max_energy_range_uj")" \
    "$(ctx_temp_mc)" "$(ctx_count_comm Runner.Listener)" "$(ctx_count_comm Runner.Worker)"
  printf '"benchlock_open":%s' "$(ctx_benchlock_open)"
  ctx_telemetry_json "$cpus" "$sibs"
  # shellcheck disable=SC2086
  [ -z "${2:-}" ] || printf ',"interval_busy_pct":%s' "$(ctx_busy_pct "$2" "$(ctx_stat_tokens $cpus $sibs)")"
  printf '}\n'
}

ctx_compress_ids() { # <id>...  ->  canonical cpulist ("" for none)
  local res="" lo="" prev="" c
  for c in $(printf '%s\n' "$@" | sort -nu); do
    if [ -n "$prev" ] && [ "$c" -eq $((prev + 1)) ]; then prev="$c"; continue; fi
    [ -z "$lo" ] || res+="${res:+,}$([ "$lo" = "$prev" ] && echo "$lo" || echo "$lo-$prev")"
    lo="$c" prev="$c"
  done
  [ -z "$lo" ] || res+="${res:+,}$([ "$lo" = "$prev" ] && echo "$lo" || echo "$lo-$prev")"
  printf '%s' "$res"
}

ctx_main() {
  if [ $# -eq 3 ] && [ "$1" = --interval ] && [[ "$2" =~ ^[0-9]+(\.[0-9]+)?$ ]]; then
    local cpus before
    cpus="$(ctx_expand_cpulist "$3")" || return 64
    # shellcheck disable=SC2086
    before="$(ctx_stat_tokens $cpus "$(ctx_siblings $cpus)")"
    sleep "$2"
    ctx_snapshot "$3" "$before"
    return
  fi
  if [ $# -ne 1 ]; then
    echo "usage: tools/cpu-context.sh [--interval SECONDS] CPULIST" >&2
    return 64
  fi
  ctx_snapshot "$1"
}

if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  ctx_main "$@"
fi
