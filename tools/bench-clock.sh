#!/usr/bin/env bash
#
# Opt-in fixed clock for measurement sessions (#954).
#
#   tools/bench-clock.sh status [CPULIST]          rc 0 fixed, 1 not fixed, 2 inconsistent/failed
#   sudo tools/bench-clock.sh fix <MHz> [CPULIST]  default CPULIST 8-23,72-87 (CCDs 1-2 + siblings)
#   sudo tools/bench-clock.sh restore
#   tools/bench-clock.sh setup                     print the optional sudoers step; runs nothing
#
# A serial process boosts to ~4.5 GHz while a 16-worker run sits at the all-core clock (#827), so a
# Zeebra-16 / comparand-1 ratio carries a ~1.14x frequency term that is not algorithmic. `fix`
# disables boost and pins scaling_min_freq = scaling_max_freq = <MHz> on the listed CPUs; pick a
# figure at or below the 16-worker all-core clock so serial and parallel arms run at one speed.
#
# Nothing here runs unless a subcommand is named, and `fix`/`restore` refuse without root (rc 77):
# no privileged change is made silently. A fixed clock is shared machine state, like a CCD
# reservation, so `fix` records the previous state in /run (world-readable, gone on reboot, as is
# the fix itself) and `restore` puts every value back. A write that fails part-way is rolled back.
# tools/cpu-context.sh records the result as `"clock":"fixed@<MHz>"` or `"boost"`.
#
# Test seams (tools/test/bench-clock-test.sh): ZEEBRA_BENCH_CLOCK_SYS relocates
# /sys/devices/system/cpu, and stands in for root since it writes nothing real;
# ZEEBRA_BENCH_CLOCK_STATE relocates the state file.

set -uo pipefail

# shellcheck source=cpu-context.sh
. "$(dirname "${BASH_SOURCE[0]}")/cpu-context.sh"

BC_DEFAULT_CPUS="8-23,72-87"

bc_sys() { printf '%s' "${ZEEBRA_BENCH_CLOCK_SYS:-/sys/devices/system/cpu}"; }
bc_state() { printf '%s' "${ZEEBRA_BENCH_CLOCK_STATE:-/run/zeebra-bench-clock}"; }
bc_freq() { printf '%s' "$(bc_sys)/cpu$1/cpufreq/$2"; }

bc_root_gate() {
  [ "$(id -u)" -eq 0 ] || [ -n "${ZEEBRA_BENCH_CLOCK_SYS:-}" ] && return 0
  printf 'bench-clock: %s needs root; run it as: sudo %s %s\n' "$1" "$0" "$*" >&2
  return 77
}

bc_get() { # <key>  ->  value from the state file; rc 1 when there is none
  [ -e "$(bc_state)" ] || return 1
  sed -n "s/^$1=//p" "$(bc_state)"
}

bc_write() { # <path> <value>; skipped when already equal, rc 2 on failure
  [ "$(ctx_read "$1" 2>/dev/null)" = "$2" ] && return 0
  { printf '%s\n' "$2" >"$1"; } 2>/dev/null || { printf 'bench-clock: cannot write %s\n' "$1" >&2; return 2; }
}

bc_status() { # [cpulist]
  local cpus mhz boost c min max verdict=fixed rc=0
  cpus="$(bc_get cpus)" || cpus="${1:-$BC_DEFAULT_CPUS}"
  mhz="$(bc_get mhz)" || mhz=""
  boost="$(ctx_read "$(bc_sys)/cpufreq/boost")" || boost=""
  local ids
  ids="$(ctx_expand_cpulist "$cpus")" || return 64
  for c in $ids; do
    min="$(ctx_read "$(bc_freq "$c" scaling_min_freq)")" || { echo "bench-clock: cannot read cpu$c" >&2; return 2; }
    max="$(ctx_read "$(bc_freq "$c" scaling_max_freq)")" || return 2
    [ -n "$mhz" ] && { [ "$min" = "${mhz}000" ] && [ "$max" = "${mhz}000" ] || verdict=inconsistent; }
  done
  if [ -z "$mhz" ]; then
    verdict="$([ "$boost" = 1 ] && echo boost || echo unknown)" rc=1
  elif [ "$boost" != 0 ] || [ "$verdict" = inconsistent ]; then
    verdict=inconsistent rc=2
  else
    verdict="fixed@$mhz"
  fi
  printf 'clock=%s boost=%s cpus=%s recorded=%s\n' "$verdict" "${boost:--}" "$cpus" "${mhz:--}"
  return "$rc"
}

bc_restore() {
  bc_root_gate restore || return $?
  local f c saved rc=0
  f="$(bc_state)"
  [ -e "$f" ] || { echo "bench-clock: nothing to restore" >&2; return 1; }
  # Boost first: on amd-pstate toggling it resets the policy limits that the next lines restore.
  bc_write "$(bc_sys)/cpufreq/boost" "$(bc_get boost)" || rc=2
  for c in $(ctx_expand_cpulist "$(bc_get cpus)"); do
    saved="$(bc_get "cpu$c")"
    bc_write "$(bc_freq "$c" scaling_max_freq)" "${saved#*:}" || rc=2
    bc_write "$(bc_freq "$c" scaling_min_freq)" "${saved%%:*}" || rc=2
  done
  [ "$rc" -eq 0 ] && rm -f "$f"
  [ "$rc" -eq 0 ] || echo "bench-clock: restore incomplete; state kept in $f, rerun restore" >&2
  return "$rc"
}

bc_fix() { # <MHz> [cpulist]
  bc_root_gate fix "$@" || return $?
  local mhz="${1:-}" cpus="${2:-$BC_DEFAULT_CPUS}" ids c lo hi khz boost
  [[ "$mhz" =~ ^[0-9]+$ ]] || { echo "bench-clock: <MHz> must be an integer" >&2; return 64; }
  khz=$((mhz * 1000))
  ids="$(ctx_expand_cpulist "$cpus")" || return 64
  if [ -e "$(bc_state)" ]; then
    echo "bench-clock: already fixed ($(bc_status)); restore first" >&2
    return 1
  fi
  boost="$(ctx_read "$(bc_sys)/cpufreq/boost")" || { echo "bench-clock: cannot read boost" >&2; return 2; }
  local state
  state="mhz=$mhz"$'\n'"cpus=$cpus"$'\n'"boost=$boost"$'\n'"at=$(date --iso-8601=seconds)"
  for c in $ids; do
    lo="$(ctx_read "$(bc_freq "$c" cpuinfo_min_freq)")" || return 2
    hi="$(ctx_read "$(bc_freq "$c" cpuinfo_max_freq)")" || return 2
    if [ "$khz" -lt "$lo" ] || [ "$khz" -gt "$hi" ]; then
      printf 'bench-clock: %s MHz is outside cpu%s range %s-%s kHz\n' "$mhz" "$c" "$lo" "$hi" >&2
      return 64
    fi
    state+=$'\n'"cpu$c=$(ctx_read "$(bc_freq "$c" scaling_min_freq)"):$(ctx_read "$(bc_freq "$c" scaling_max_freq)")"
  done
  printf '%s\n' "$state" >"$(bc_state)" || return 2
  trap 'bc_restore; exit 130' INT TERM
  local ok=1
  bc_write "$(bc_sys)/cpufreq/boost" 0 || ok=0
  for c in $ids; do
    [ "$ok" = 1 ] || break
    lo="$(ctx_read "$(bc_freq "$c" cpuinfo_min_freq)")"
    # min down first so the max can go below the old min; then min up to meet it.
    bc_write "$(bc_freq "$c" scaling_min_freq)" "$lo" &&
      bc_write "$(bc_freq "$c" scaling_max_freq)" "$khz" &&
      bc_write "$(bc_freq "$c" scaling_min_freq)" "$khz" || ok=0
  done
  trap - INT TERM
  if [ "$ok" = 1 ] && bc_status >/dev/null; then
    bc_status
    return 0
  fi
  echo "bench-clock: fix did not take (the kernel may clamp or round); rolling back" >&2
  bc_restore >/dev/null
  return 2
}

bc_setup_text() {
  cat <<'SETUP'
Optional root step, so a session can fix and restore the clock without an interactive sudo.
Install a root-owned copy: a sudoers entry on the repository's own file would let anyone who can
edit the checkout run arbitrary code as root.

  sudo install -o root -g root -m 0755 tools/cpu-context.sh tools/bench-clock.sh /usr/local/libexec/zeebra/
  echo "$USER ALL=(root) NOPASSWD: /usr/local/libexec/zeebra/bench-clock.sh fix *, /usr/local/libexec/zeebra/bench-clock.sh restore" \
    | sudo tee /etc/sudoers.d/zeebra-bench-clock
  sudo chmod 0440 /etc/sudoers.d/zeebra-bench-clock && sudo visudo -c

Undo: sudo /usr/local/libexec/zeebra/bench-clock.sh restore (if fixed), then
  sudo rm -r /etc/sudoers.d/zeebra-bench-clock /usr/local/libexec/zeebra
A fix does not survive a reboot; nothing here installs a boot-time unit.
SETUP
}

bc_main() {
  local cmd="${1:-}"
  [ "$#" -gt 0 ] && shift
  case "$cmd" in
    status) bc_status "$@" ;;
    fix) [ "$#" -ge 1 ] || { sed -n '5,9p' "${BASH_SOURCE[0]}" >&2; return 64; }; bc_fix "$@" ;;
    restore) bc_restore ;;
    setup) bc_setup_text ;;
    *) sed -n '5,9p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//' >&2; return 64 ;;
  esac
}

if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  bc_main "$@"
  exit $?
fi
