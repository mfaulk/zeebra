#!/usr/bin/env bash
#
# Read-only audit of what a CCD reservation actually fences (#1104).
#
#   tools/bench-isolation-audit.sh inventory [CPULIST]                 one JSON document
#   tools/bench-isolation-audit.sh sample CPULIST SECONDS [INTERVAL]   one JSON document
#   tools/bench-isolation-audit.sh policy WORKERS... [--base N]        one line per worker count
#
# `inventory` groups every task by cgroup class and says which ones' effective affinity
# (Cpus_allowed_list) admits a CPU in CPULIST, which defaults to the live reservation's bench CPUs.
# An `escape` is a user-owned task outside zbbench.slice that could run there; zombies keep a stale
# mask and are counted but never meet. `sample` charges the CPU time a task accrues between
# snapshots to the CPU it was last seen on, and a task born mid-window all of its time. Approximate:
# a task that migrated is charged to where it ended up, one born and dead between snapshots is never
# seen, and IRQ/softirq time has no task — `coverage` says how much of the busy time was named.
# `policy` derives the CCDs a w-worker M29 placement (CPUs base..base+w-1, base 8) needs, from the
# topology and tools/bench-reserve.sh's own plan (#1104 §6).
#
# Needs no root and changes nothing. cgroup v2 only. Test seams, as in tools/cpu-context.sh:
# ZEEBRA_CPU_CONTEXT_{SYS,PROC,CGROUP}, ZEEBRA_ISOLATION_AUDIT_WORKQUEUE for
# /sys/devices/virtual/workqueue, and tools/bench-reserve.sh's ZEEBRA_BENCH_RESERVE_* for the
# reservation state.

set -uo pipefail

# shellcheck source=bench-reserve.sh
. "$(dirname "${BASH_SOURCE[0]}")/bench-reserve.sh"

iso_cgroot() { printf '%s' "${ZEEBRA_CPU_CONTEXT_CGROUP:-/sys/fs/cgroup}"; }
iso_wq() { printf '%s' "${ZEEBRA_ISOLATION_AUDIT_WORKQUEUE:-/sys/devices/virtual/workqueue}"; }

# Shared awk: cgroup path classification, id blanking, and cpulist membership. Kernel threads are
# kthreadd (pid 2) and its children, whatever cgroup they report.
ISO_AWK_LIB='
# Blank ids token by token: an all-hex token holding a digit (uuids, container ids) or any digit run.
function iso_tok(t) { if (t ~ /^[0-9a-f]+$/ && t ~ /[0-9]/) return "*"; gsub(/[0-9]+/, "*", t); return t }
function iso_norm(s,    out, tok, i, n, ch) {
  if (s in NORMC) return NORMC[s]
  out = ""; tok = ""; n = length(s)
  for (i = 1; i <= n; i++) {
    ch = substr(s, i, 1)
    if (index("-._:/@ ", ch)) { out = out iso_tok(tok) ch; tok = "" } else tok = tok ch
  }
  out = out iso_tok(tok)
  while (gsub(/\*-\*/, "*", out)) ;
  return NORMC[s] = out
}
function iso_classify(path, pid, ppid, comm,    c, n, s) {
  if (pid == 2 || ppid == 2) return "kernel\t" iso_norm(comm)
  if (path == "") return "unknown\t?"
  if (path == "/") return "root\t/"
  n = split(path, c, "/")
  if (c[2] == "init.scope") return "init\tinit.scope"
  if (c[2] == "system.slice") return "system\t" (n >= 3 ? iso_norm(c[3]) : "-")
  if (c[2] == "machine.slice") return "machine\t" (n >= 3 ? iso_norm(c[3]) : "-")
  if (c[2] == "user.slice") {
    if (n >= 4 && c[4] ~ /^user@[0-9]+\.service$/) {
      s = (n >= 5 ? c[5] : "-")
      if (s == "zbbench.slice") return "bench\t" iso_norm(s (n >= 6 ? "/" c[6] : ""))
      if (s == "app.slice" || s == "background.slice" || s == "session.slice")
        return "user-fenced\t" iso_norm(s (n >= 6 ? "/" c[6] : ""))
      return "user-manager-other\t" iso_norm(s)
    }
    if (n >= 4 && c[4] ~ /^session-.*\.scope$/) return "login-session\t" iso_norm(c[4])
    return "user-other\t" iso_norm(n >= 4 ? c[3] "/" c[4] : c[3])
  }
  return "other\t" iso_norm(c[2])
}
function iso_want(list,    p, n, i) { n = split(list, p, " "); for (i = 1; i <= n; i++) WANT[p[i]] = 1 }
function iso_meets(list,    p, n, i, r, k, lo, hi, j) {
  n = split(list, p, ",")
  for (i = 1; i <= n; i++) {
    k = split(p[i], r, "-"); lo = r[1] + 0; hi = (k > 1 ? r[2] : r[1]) + 0
    for (j = lo; j <= hi; j++) if (j in WANT) return 1
  }
  return 0
}
function iso_ncpus(list,    p, n, i, r, k, t) {
  n = split(list, p, ","); t = 0
  for (i = 1; i <= n; i++) { k = split(p[i], r, "-"); t += (k > 1 ? r[2] - r[1] + 1 : 1) }
  return t
}
function iso_json(s) { gsub(/\\/, "\\\\", s); gsub(/"/, "\\\"", s); gsub(/\t/, " ", s); return "\"" s "\"" }
# The top `k` keys of counts[] whose key starts with prefix, as a JSON object of name -> count.
function iso_top(counts, prefix, k,    out, sep, used, i, key, best, bk, name) {
  out = ""; sep = ""
  for (i = 0; i < k; i++) {
    best = -1; bk = ""
    for (key in counts) if (index(key, prefix) == 1 && !(key in used) && counts[key] > best) { best = counts[key]; bk = key }
    if (best < 0) break
    used[bk] = 1; name = substr(bk, length(prefix) + 1)
    out = out sep iso_json(name) ":" best; sep = ","
  }
  return "{" out "}"
}
'

iso_classify() { # <cgroup path or ""> <pid> <ppid> [comm]  ->  "class<TAB>group"
  awk -v path="$1" -v pid="$2" -v ppid="$3" -v comm="${4:-}" "$ISO_AWK_LIB"'
    BEGIN { print iso_classify(path, pid, ppid, comm) }'
}

iso_hexmask_to_list() { # <hex mask, comma-grouped, most significant group first>  ->  cpulist
  local mask="${1//,/}" ids=() i nib bit n
  n=${#mask}
  for ((i = 0; i < n; i++)); do
    nib=$((16#${mask:n-1-i:1}))
    for bit in 0 1 2 3; do
      (((nib >> bit) & 1)) && ids+=($((i * 4 + bit)))
    done
  done
  [ "${#ids[@]}" -gt 0 ] && ctx_compress_ids "${ids[@]}"
  return 0
}

iso_cmdline_param() { # <cmdline> <name>  ->  JSON string value, or null when absent
  local w
  for w in $1; do
    case "$w" in "$2"=*) ctx_json_string "${w#*=}"; return ;; "$2") printf '""'; return ;; esac
  done
  printf null
}

# One awk pass over every task's status and every process's cgroup. grep -H rather than awk over
# the files: a process that exits mid-scan is a vanished file, which grep skips and mawk dies on.
iso_groups_json() { # <expanded cpu ids>  ->  "classes": {...}, "groups": [...], "escapes": [...]
  local p
  p="$(ctx_proc)"
  {
    grep -H '^0::' "$p"/[0-9]*/cgroup 2>/dev/null | sed 's/^/C\t/'
    grep -H -E '^(Name|State|PPid|Cpus_allowed_list):' "$p"/[0-9]*/task/[0-9]*/status 2>/dev/null | sed 's/^/S\t/'
  } | awk -v want="$1" "$ISO_AWK_LIB"'
    BEGIN { FS = "\t"; iso_want(want) }
    function fid(file, back,    q, n) { n = split(file, q, "/"); return q[n - back] }
    $1 == "C" { line = substr($0, 3); i = index(line, ":"); pid = fid(substr(line, 1, i - 1), 1)
      cg[pid] = substr(line, i + 4); next }
    $1 == "S" { line = substr($0, 3); i = index(line, ":"); file = substr(line, 1, i - 1); kv = substr(line, i + 1)
      tid = fid(file, 1); pid = fid(file, 3); tg[tid] = pid
      j = index(kv, ":"); key = substr(kv, 1, j - 1); val = substr(kv, j + 1); sub(/^[ \t]+/, "", val)
      if (key == "Name") name[tid] = val; else if (key == "PPid") pp[tid] = val; else if (key == "State") stt[tid] = substr(val, 1, 1); else aff[tid] = val }
    END {
      for (tid in tg) {
        pid = tg[tid]; ppid = (pid in pp ? pp[pid] : pp[tid])
        pname = (pid in name ? name[pid] : name[tid])
        split(iso_classify((pid in cg ? cg[pid] : ""), pid, ppid, pname), cl, "\t")
        c = cl[1]; g = cl[2]
        if (c == "kernel") c = (iso_ncpus(aff[tid]) == 1 ? "kernel-bound" : "kernel-unbound")
        # A zombie keeps the affinity it died with, since cpuset updates skip it, and never runs again.
        m = (stt[tid] == "Z" ? 0 : aff[tid] == "" ? 1 : iso_meets(aff[tid]))
        k = c SUBSEP g; G[k] = 1
        if (stt[tid] == "Z") zb[k]++
        tasks[k]++; ctasks[c]++
        if (m) { tm[k]++; ctm[c]++; pm[k SUBSEP pid] = 1 }
        affs[k SUBSEP aff[tid]]++
        if (!((k SUBSEP pid) in seenp)) { seenp[k SUBSEP pid] = 1; procs[k]++; cprocs[c]++; comms[k SUBSEP pname]++ }
      }
      for (kp in pm) { split(kp, q, SUBSEP); k = q[1] SUBSEP q[2]; pmk[k]++; cpm[q[1]]++
        pid = q[3]; cm[k SUBSEP (pid in name ? name[pid] : "?")]++ }
      printf "\"classes\":{"; sep = ""
      for (c in ctasks) { printf "%s%s:{\"procs\":%d,\"tasks\":%d,\"procs_meeting\":%d,\"tasks_meeting\":%d}", sep, iso_json(c), cprocs[c], ctasks[c], cpm[c], ctm[c]; sep = "," }
      printf "},\"groups\":["; sep = ""; esep = ""; esc = ""
      for (k in G) { split(k, q, SUBSEP)
        obj = sprintf("{\"class\":%s,\"group\":%s,\"procs\":%d,\"tasks\":%d,\"procs_meeting\":%d,\"tasks_meeting\":%d,\"zombies\":%d,\"comms\":%s,\"comms_meeting\":%s,\"affinity\":%s}",
          iso_json(q[1]), iso_json(q[2]), procs[k], tasks[k], pmk[k], tm[k], zb[k], iso_top(comms, k SUBSEP, 6), iso_top(cm, k SUBSEP, 6), iso_top(affs, k SUBSEP, 3))
        printf "%s%s", sep, obj; sep = ","
        if (tm[k] > 0 && q[1] ~ /^(user-fenced|user-manager-other|login-session|user-other)$/) { esc = esc esep obj; esep = "," } }
      printf "],\"escapes\":[%s]", esc
    }'
}

iso_irqs_json() { # <expanded cpu ids>  ->  {"total","meeting","unreadable","list":[...]}
  local want=" $1 " d irq eff total=0 meeting=0 unreadable=0 list="" sep="" a actions
  for d in "$(ctx_proc)"/irq/[0-9]*; do
    [ -d "$d" ] || continue
    irq="${d##*/}"
    total=$((total + 1))
    eff="$(ctx_read "$d/effective_affinity_list")" || { unreadable=$((unreadable + 1)); continue; }
    local c hit=0
    for c in $(ctx_expand_cpulist "$eff" 2>/dev/null); do [[ "$want" == *" $c "* ]] && { hit=1; break; }; done
    [ "$hit" = 1 ] || continue
    meeting=$((meeting + 1))
    [ "$meeting" -le 64 ] || continue
    actions=""
    for a in "$d"/*/; do [ -d "$a" ] && { a="${a%/}"; actions+="${actions:+,}${a##*/}"; }; done
    list+="$sep{\"irq\":$irq,\"effective\":$(ctx_json_string "$eff"),\"actions\":$(ctx_json_string "$actions")}"
    sep=,
  done
  printf '{"total":%d,"meeting":%d,"unreadable":%d,"list":[%s]}' "$total" "$meeting" "$unreadable" "$list"
}

iso_cpusets_json() { # -> {"<cgroup>": "<cpuset.cpus.effective>"} for the top-level and user-manager slices
  local root f rel out="" sep=""
  root="$(iso_cgroot)"
  for f in "$root"/{system.slice,machine.slice,init.scope,user.slice}/cpuset.cpus.effective \
    "$root"/user.slice/user-*.slice/user@*.service/*.slice/cpuset.cpus.effective; do
    [ -e "$f" ] || continue
    rel="${f#"$root"/}" rel="${rel%/cpuset.cpus.effective}"
    case "$rel" in user.slice/user-*.slice/*) rel="${rel#user.slice/*/}" ;; esac
    out+="$sep$(ctx_json_string "$rel"):$(ctx_json_string "$(ctx_read "$f" || true)")"
    sep=,
  done
  printf '{%s}' "$out"
}

iso_inventory() { # [cpulist]
  local cpus="${1:-}" ids
  if [ -z "$cpus" ]; then
    cpus="$(br_state_get bench 2>/dev/null)" || cpus=""
    [ -n "$cpus" ] || { echo "bench-isolation-audit: no reservation; give a cpulist" >&2; return 64; }
  fi
  ids="$(ctx_expand_cpulist "$cpus")" || { echo "bench-isolation-audit: malformed cpulist $cpus" >&2; return 64; }
  local status cmdline wq wqlist wq_meets=false c
  status="$(br_status 2>/dev/null)"
  cmdline="$(ctx_read "$(ctx_proc)/cmdline" || true)"
  wq="$(ctx_read "$(iso_wq)/cpumask")" && wqlist="$(iso_hexmask_to_list "$wq")" || wqlist=""
  for c in $(ctx_expand_cpulist "$wqlist" 2>/dev/null); do [[ " $ids " == *" $c "* ]] && wq_meets=true; done
  printf '{"tool":"bench-isolation-audit","version":1,"at":"%s","kernel":%s,"cpus":%s,' \
    "$(date --iso-8601=seconds)" "$(ctx_json_string "$(ctx_read "$(ctx_proc)/sys/kernel/osrelease" || true)")" \
    "$(ctx_json_string "$cpus")"
  printf '"reservation":{"status":%s,"ccds":%s,"bench":%s,"rest":%s},' \
    "$(ctx_json_string "$(sed -n 's/^status=\([^ ]*\).*/\1/p' <<<"$status")")" \
    "$(ctx_json_string "$(br_state_get ccds 2>/dev/null || true)")" \
    "$(ctx_json_string "$(br_state_get bench 2>/dev/null || true)")" \
    "$(ctx_json_string "$(br_state_get rest 2>/dev/null || true)")"
  printf '"cpusets":%s,' "$(iso_cpusets_json)"
  printf '"isolation":{"isolated":%s,"nohz_full":%s,"workqueue_cpumask":%s,"workqueue_meets":%s,"cmdline":{"isolcpus":%s,"nohz_full":%s,"irqaffinity":%s,"rcu_nocbs":%s}},' \
    "$(ctx_json_string "$(ctx_read "$(ctx_sys)/isolated" || true)")" \
    "$(ctx_json_string "$(ctx_read "$(ctx_sys)/nohz_full" || true)")" \
    "$(ctx_json_string "$wqlist")" "$wq_meets" \
    "$(iso_cmdline_param "$cmdline" isolcpus)" "$(iso_cmdline_param "$cmdline" nohz_full)" \
    "$(iso_cmdline_param "$cmdline" irqaffinity)" "$(iso_cmdline_param "$cmdline" rcu_nocbs)"
  printf '"irqs":%s,' "$(iso_irqs_json "$ids")"
  iso_groups_json "$ids"
  printf '}\n'
}

# One snapshot for iso_sample_aggregate: "@" lines are written by the caller; this emits per-CPU
# /proc/stat ("P"), process cgroups ("C") and per-task stat ("T") lines.
iso_task_lines() {
  local p
  p="$(ctx_proc)"
  awk '$1 ~ /^cpu[0-9]+$/ { print "P\t" $0 }' "$p/stat"
  grep -H '^0::' "$p"/[0-9]*/cgroup 2>/dev/null | sed 's/^/C\t/'
  grep -H '' "$p"/[0-9]*/task/[0-9]*/stat 2>/dev/null | sed 's/^/T\t/'
}

iso_sample_aggregate() { # <cpulist>  <stream on stdin>  ->  JSON
  local ids
  ids="$(ctx_expand_cpulist "$1")" || return 64
  awk -v want="$ids" -v cpus="$1" "$ISO_AWK_LIB"'
    BEGIN { FS = "\t"; iso_want(want) }
    function fid(file, back,    q, n) { n = split(file, q, "/"); return q[n - back] }
    $1 == "@" || /^@ / { snaps++; split($0, w, " "); t = w[2]; if (snaps == 1) t0 = t; t1 = t
      delete cg; first = (snaps == 1); next }
    $1 == "P" { split($2, f, " "); c = substr(f[1], 4); if (!(c in WANT)) next
      u = f[2] + f[3]; s = f[4]; iq = f[7] + f[8]; st = f[9]
      if (first) { u0 += u; s0 += s; q0 += iq; st0 += st } else { lastu[c] = u; lasts[c] = s; lastq[c] = iq; lastst[c] = st }
      next }
    $1 == "C" { line = substr($0, 3); i = index(line, ":"); cg[fid(substr(line, 1, i - 1), 1)] = substr(line, i + 4); next }
    $1 == "T" { line = substr($0, 3); i = index(line, ":"); file = substr(line, 1, i - 1); rest = substr(line, i + 1)
      tid = fid(file, 1); pid = fid(file, 3)
      o = index(rest, "("); r = 0
      for (j = length(rest); j > o; j--) if (substr(rest, j, 1) == ")") { r = j; break }
      if (!o || !r) next
      comm = substr(rest, o + 1, r - o - 1); n = split(substr(rest, r + 2), f, " ")
      if (n < 37) next
      ticks = f[12] + f[13]; cpu = f[37]
      if (tid == pid) pp[pid] = f[2]
      if ((cpu in WANT) && snaps >= 2) {
        d = (tid in prev ? ticks - prev[tid] : ticks)
        if (d > 0 || f[1] == "R") {
          split(iso_classify((pid in cg ? cg[pid] : ""), pid, (pid in pp ? pp[pid] : f[2]), comm), cl, "\t")
          if (d > 0) { att[cl[1]] += d; bycpu[cpu SUBSEP cl[1]] += d; key = cl[1] SUBSEP cl[2] SUBSEP iso_norm(comm); top[key] += d }
          if (f[1] == "R" && cl[1] != "bench") { sk = cl[1] SUBSEP iso_norm(comm); seen[sk]++ }
        }
      }
      prev[tid] = ticks; next }
    END {
      for (c in lastu) { u1 += lastu[c]; s1 += lasts[c]; q1 += lastq[c]; st1 += lastst[c] }
      du = u1 - u0; ds = s1 - s0; dq = q1 - q0; dst = st1 - st0
      printf "{\"tool\":\"bench-isolation-audit\",\"mode\":\"sample\",\"version\":1,\"cpus\":%s,\"snapshots\":%d,\"window_s\":%s,", iso_json(cpus), snaps, (snaps ? t1 - t0 : 0)
      printf "\"cpu_ticks\":{\"user\":%d,\"system\":%d,\"irq\":%d,\"steal\":%d,\"busy\":%d},", du, ds, dq, dst, du + ds + dq + dst
      for (c in att) tot += att[c]
      printf "\"attributed_total\":%d,\"coverage\":%s,", tot, (du + ds + dq + dst > 0 ? sprintf("%.4g", tot / (du + ds + dq + dst)) : "null")
      printf "\"attributed_ticks\":{"; sep = ""
      for (c in att) { printf "%s%s:%d", sep, iso_json(c), att[c]; sep = "," }
      printf "},\"by_cpu\":{"; sep = ""
      for (k in bycpu) { split(k, q, SUBSEP); cpul[q[1]] = cpul[q[1]] (q[1] in cpus_seen ? "," : "") iso_json(q[2]) ":" bycpu[k]; cpus_seen[q[1]] = 1 }
      for (c in cpul) { printf "%s\"%s\":{%s}", sep, c, cpul[c]; sep = "," }
      printf "},\"top\":["; sep = ""
      for (i = 0; i < 40; i++) { best = 0; bk = ""
        for (k in top) if (!(k in used) && top[k] > best) { best = top[k]; bk = k }
        if (bk == "") break
        used[bk] = 1; split(bk, q, SUBSEP)
        printf "%s{\"class\":%s,\"group\":%s,\"comm\":%s,\"ticks\":%d}", sep, iso_json(q[1]), iso_json(q[2]), iso_json(q[3]), best; sep = "," }
      printf "],\"seen_running\":["; sep = ""
      for (k in seen) { split(k, q, SUBSEP); printf "%s{\"class\":%s,\"comm\":%s,\"snapshots\":%d}", sep, iso_json(q[1]), iso_json(q[2]), seen[k]; sep = "," }
      printf "]}\n"
    }'
}

iso_sample() { # <cpulist> <seconds> [interval]
  local cpus="$1" secs="$2" ival="${3:-1}" end now
  ctx_expand_cpulist "$cpus" >/dev/null || { echo "bench-isolation-audit: malformed cpulist $cpus" >&2; return 64; }
  [[ "$secs" =~ ^[0-9]+$ ]] || return 64
  end=$(($(date +%s) + secs))
  {
    while :; do
      now="$(date +%s.%N)"
      printf '@ %s\n' "$now"
      iso_task_lines
      [ "${now%.*}" -lt "$end" ] || break
      sleep "$ival"
    done
  } | iso_sample_aggregate "$cpus"
}

iso_policy() { # <workers> [base]  ->  workers= ccds= placement= bench= idle_siblings= dev_cpus= dev_cores=
  local w="$1" base="${2:-8}" c id ccds=() plan bench rest placement sibs cores
  [[ "$w" =~ ^[0-9]+$ ]] && [ "$w" -ge 1 ] || { echo "bench-isolation-audit: workers must be >= 1" >&2; return 64; }
  for ((c = base; c < base + w; c++)); do
    id="$(ctx_read "$(ctx_sys)/cpu$c/cache/index3/id")" || return 2
    [[ " ${ccds[*]-} " == *" $id "* ]] || ccds+=("$id")
  done
  local list
  list="$(printf '%s\n' "${ccds[@]}" | sort -n | paste -sd,)"
  plan="$(br_plan "$list" 2>/dev/null)" || return $?
  bench="$(sed -n 's/^bench=//p' <<<"$plan")"
  rest="$(sed -n 's/^rest=//p' <<<"$plan")"
  # shellcheck disable=SC2046  # deliberate splitting into ids
  placement="$(ctx_compress_ids $(seq "$base" $((base + w - 1))))"
  # shellcheck disable=SC2046
  sibs="$(ctx_compress_ids $(ctx_siblings $(seq "$base" $((base + w - 1)))))"
  cores="$(for c in $(ctx_expand_cpulist "$rest"); do ctx_core "$c"; echo; done | sort -u | grep -c .)"
  printf 'workers=%s ccds=%s placement=%s bench=%s idle_siblings=%s dev_cpus=%s dev_cores=%s\n' \
    "$w" "$list" "$placement" "$bench" "$sibs" "$rest" "$cores"
}

iso_usage() { sed -n '5,7p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//' >&2; }

iso_main() {
  local cmd="${1:-}"
  [ "$#" -gt 0 ] && shift
  case "$cmd" in
    inventory) iso_inventory "$@" ;;
    sample)
      [ "$#" -ge 2 ] || { iso_usage; return 64; }
      iso_sample "$@"
      ;;
    policy)
      local base=8 ws=() w rc=0
      while [ "$#" -gt 0 ]; do
        case "$1" in --base) base="$2"; shift 2 ;; *) ws+=("$1"); shift ;; esac
      done
      [ "${#ws[@]}" -gt 0 ] || { iso_usage; return 64; }
      for w in "${ws[@]}"; do iso_policy "$w" "$base" || rc=$?; done
      return "$rc"
      ;;
    *) iso_usage; return 64 ;;
  esac
}

if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  iso_main "$@"
  exit $?
fi
