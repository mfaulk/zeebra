"""Child runner and plan rotation shared by `tools/bench-job` and the M29-M32 campaign controllers.

Moved out of `research/m29-baseline/costmodel.py` and `research/m31-baseline/campaign.py` (#967);
both keep re-exporting these names so their campaigns replay unchanged. A child is reaped with
`wait4` so its CPU time and peak RSS come from the kernel, and it carries `PR_SET_PDEATHSIG` so a
killed controller does not leave a measurement running on reserved CPUs behind it.
"""
import ctypes
import json
import os
import signal
import subprocess
import tempfile
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIRST_CPU = 8
_PR_SET_PDEATHSIG = 1


def cpulist(workers, first=FIRST_CPU):
    return f'{first}' if workers == 1 else f'{first}-{first + workers - 1}'


def snapshot(cpus):
    # ZEEBRA_CPU_CONTEXT is a test seam: tools/test/bench-job-test.py stubs the 1-2 s context read.
    script = os.environ.get('ZEEBRA_CPU_CONTEXT', str(ROOT / 'tools/cpu-context.sh'))
    r = subprocess.run(['bash', script, cpus], capture_output=True, text=True)
    return json.loads(r.stdout) if r.returncode == 0 else dict(error=r.returncode, stderr=r.stderr)


class Sampler(threading.Thread):
    def __init__(self, cpus):
        super().__init__(daemon=True)
        ids = []
        for part in cpus.split(','):
            first, _, last = part.partition('-')
            ids += range(int(first), int(last or first) + 1)
        self.paths = [Path(f'/sys/devices/system/cpu/cpu{c}/cpufreq/scaling_cur_freq') for c in ids]
        self.samples, self.stop = [], threading.Event()

    def run(self):
        while not self.stop.wait(0.025):
            try:
                self.samples.append(sum(int(p.read_text()) for p in self.paths) / len(self.paths))
            except OSError:
                return


def summarize_freq(samples):
    if not samples:
        return None
    s = sorted(samples)
    return dict(n=len(s), mean_khz=round(sum(s) / len(s)), min_khz=round(s[0]),
                median_khz=round(s[len(s) // 2]), max_khz=round(s[-1]))


def plan(rows, reps):
    """(rep, row, arm) in run order: rows in turn, arms rotated one place per repetition, so each
    arm's repetition r sits beside every other arm's repetition r (the pairing the ratios use)."""
    order = []
    for rep in range(reps):
        for row, arms in rows:
            shift = rep % len(arms)
            order += [(rep, row, arm) for arm in arms[shift:] + arms[:shift]]
    return order


def _die_with_parent():
    # A controller can inherit SIGINT ignored (a background job) or blocked (GitHub's runner), and so
    # would the binary; then neither `timeout --signal=INT` nor a cancel could stop it short of
    # `--kill-after`.
    signal.signal(signal.SIGINT, signal.SIG_DFL)
    signal.pthread_sigmask(signal.SIG_UNBLOCK, {signal.SIGINT, signal.SIGTERM})
    ctypes.CDLL(None, use_errno=True).prctl(_PR_SET_PDEATHSIG, signal.SIGTERM)


# The peak RSS `wait4` reports for the child is the whole tree's maximum, and on Linux that tree
# starts as a fork of this Python process: exec records the forked image's high-water mark
# (`setmax_mm_hiwater_rss`), so every figure is at least the controller's own RSS (about 31 MiB
# under bench-job, #990). The measured binary is therefore launched under GNU time, a small C
# process whose `wait4` of the binary alone is exact; `rss_reporter` names it.
GNU_TIME = '/usr/bin/time'


def gnu_time(path=None):
    """`path` (default `$ZEEBRA_BENCH_TIME`, else /usr/bin/time) if it is GNU time, else None."""
    path = path or os.environ.get('ZEEBRA_BENCH_TIME', GNU_TIME)
    try:
        with tempfile.NamedTemporaryFile('r') as f:
            ok = subprocess.run([path, '-f', '%M', '-o', f.name, 'true'], stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL, timeout=10).returncode == 0
            return path if ok and parse_time_report(f.read())[0] is not None else None
    except (OSError, subprocess.SubprocessError):
        return None


def parse_time_report(text):
    """(peak_rss_kb | None, signal | None) from a `-f %M` report. GNU time writes `Command terminated
    by signal N` (or `exited with non-zero status`) on its own line before the figure."""
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    kb = int(lines[-1]) if lines and lines[-1].isdigit() else None
    sig = next((int(line.rsplit(' ', 1)[1]) for line in lines
                if line.startswith('Command terminated by signal ') and line.rsplit(' ', 1)[1].isdigit()), None)
    return kb, sig


# The attempt's effective clock from hardware counters (#999). Sampled `scaling_cur_freq` does not
# track it: attempts sampled at 1.43 GHz ran at 4.09-4.16 GHz by cycle count (#992). perf is not
# wrapped around the child, because its ~21 ms startup would land inside `process_wall_ns`, and it
# would stand between `timeout` and the solver. It attaches (`perf stat -p`) to the solver pid from
# outside the measured tree instead, so the wall, the rss-guard's target and the timeout's signal path
# are exactly what they are without it. The cost is the solver's first ~25 ms, which are not
# counted, and an attempt shorter than that gets no count and falls back to the sampled clock.
PERF = '/usr/bin/perf'
PERF_PARANOID = Path('/proc/sys/kernel/perf_event_paranoid')
PERF_EVENTS = 'cycles,task-clock'
CLOCK_PERF, CLOCK_SAMPLED, CLOCK_SNAPSHOT = 'perf-cycles', 'sampled', 'snapshot'
RUNNER_WRAPPERS = frozenset({'taskset', 'timeout', 'time'})


def perf_permitted(paranoid_text):
    """True if a `perf_event_paranoid` value lets an unprivileged user count its own processes."""
    try:
        return int(paranoid_text.strip()) <= 2
    except ValueError:
        return False


def parse_perf_stat(text):
    """`{cycles, task_clock_ms, cycles_event}` from a `perf stat -x,` report, None where absent or
    `<not counted>`. Hybrid PMUs (`cpu_core/cycles/`, `cpu_atom/cycles/`) are summed. At paranoid 2
    the events are user-only (`cycles:u`), so kernel time is in task-clock but not in the cycles."""
    cycles, ms, event = None, None, None
    for line in text.splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        fields = line.split(',')
        if len(fields) < 3:
            continue
        value, unit, name = fields[0], fields[1], fields[2]
        base = name.split('/')[1] if name.count('/') >= 2 else name.split(':')[0]
        if base not in ('cycles', 'task-clock'):
            continue
        try:
            number = float(value)
        except ValueError:
            number = None
        if base == 'cycles':
            event = event or name
            if number is not None:
                cycles = (cycles or 0) + int(number)
        elif number is not None and unit == 'msec':
            ms = (ms or 0.0) + number
    return dict(cycles=cycles, task_clock_ms=ms, cycles_event=event)


def effective_khz(cycles, task_clock_ms):
    """Cycles per millisecond of CPU time, which is kHz; None without both counts."""
    if not cycles or not task_clock_ms or task_clock_ms <= 0:
        return None
    return round(cycles / task_clock_ms)


def perf_stat(path=None, paranoid=PERF_PARANOID):
    """`path` (default `$ZEEBRA_BENCH_PERF`, else /usr/bin/perf) if it can count this user's processes
    here, else None. An empty `$ZEEBRA_BENCH_PERF` turns cycle counting off."""
    path = os.environ.get('ZEEBRA_BENCH_PERF', PERF) if path is None else path
    if not path:
        return None
    try:
        if not perf_permitted(Path(paranoid).read_text()):
            return None
        with tempfile.NamedTemporaryFile('r') as f:
            subprocess.run([path, 'stat', '-e', PERF_EVENTS, '-x,', '-o', f.name, '--', 'true'],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=30)
            return path if parse_perf_stat(f.read())['cycles'] is not None else None
    except (OSError, subprocess.SubprocessError):
        return None


def attempt_clock(result):
    """`(khz | None, source)` for the clock rule: the cycle-count clock where perf produced one, else
    the sampled `scaling_cur_freq` median, else None (`attempt_metrics` then reads the snapshots)."""
    perf, freq = result.get('perf'), result.get('freq')
    if perf and perf.get('effective_khz'):
        return perf['effective_khz'], CLOCK_PERF
    if freq:
        return freq['median_khz'], CLOCK_SAMPLED
    return None, CLOCK_SNAPSHOT


def solver_pid(procs, root, wrappers):
    """The first descendant of `root`, breadth first, whose comm is not a wrapper's: the measured binary.
    `procs` maps pid -> (ppid, comm). A forked child keeps its parent's comm until it execs, so a
    wrapper-named descendant is either a wrapper or a solver not started yet; both are passed over."""
    children = {}
    for pid, (ppid, _) in procs.items():
        children.setdefault(ppid, []).append(pid)
    queue = sorted(children.get(root, []))
    while queue:
        pid = queue.pop(0)
        if procs[pid][1] not in wrappers:
            return pid
        queue += sorted(children.get(pid, []))
    return None


def read_procs(after_pid):
    """pid -> (ppid, comm) for the processes numbered above `after_pid`. Pids are allocated upward, so
    the runner's descendants are among them unless the pid space wrapped; then nothing is found and
    the attempt falls back to the sampled clock. Reading only these keeps a poll near 3 ms, where a
    full /proc scan costs about 30 ms on this box."""
    out = {}
    for name in os.listdir('/proc'):
        if not name.isdigit() or int(name) <= after_pid:
            continue
        try:
            with open(f'/proc/{name}/stat', 'rb') as f:
                stat = f.read()
        except OSError:
            continue
        close = stat.rfind(b')')
        fields = stat[close + 2:].split()
        if close < 0 or len(fields) < 2:
            continue
        out[int(name)] = (int(fields[1]), stat[stat.find(b'(') + 1:close].decode(errors='replace'))
    return out


class CycleCounter(threading.Thread):
    """Finds the solver under `root` and attaches `perf stat -p` to it; `finish` stops perf and parses."""

    def __init__(self, perf, root, wrappers, report_path, poll_s=0.005):
        super().__init__(daemon=True)
        self.perf, self.root, self.wrappers, self.report_path, self.poll_s = perf, root, wrappers, report_path, poll_s
        self.pid, self.rc, self.stop = None, None, threading.Event()

    def run(self):
        while not self.stop.wait(self.poll_s):
            pid = solver_pid(read_procs(self.root), self.root, self.wrappers)
            if pid is not None:
                break
        else:
            return
        self.pid = pid
        proc = subprocess.Popen([self.perf, 'stat', '-e', PERF_EVENTS, '-x,', '-o', self.report_path, '-p', str(pid)],
                                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, preexec_fn=_die_with_parent)
        # This thread outlives perf: PR_SET_PDEATHSIG fires when the *thread* that forked it exits.
        self.stop.wait()
        if proc.poll() is None:
            proc.send_signal(signal.SIGINT)  # `-p` counts until interrupted, then writes the report
        try:
            self.rc = proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()
            self.rc = 'hung'

    def finish(self):
        self.stop.set()
        self.join()
        rc = self.rc
        try:
            counts = parse_perf_stat(Path(self.report_path).read_text())
        except OSError:
            counts = parse_perf_stat('')
        return dict(pid=self.pid, rc=rc, events=PERF_EVENTS, **counts,
                    effective_khz=effective_khz(counts['cycles'], counts['task_clock_ms']))


def run_child(argv, cpus, timeout_s, kill_after_s=60, guard=None, should_stop=None, stop_grace_s=10,
              scratch_dir=None, rss_reporter=None, perf=None):
    """One child under `taskset -c cpus timeout --signal=INT`, with `cpu-context` before and after.

    With `rss_reporter` (a GNU time path, see `gnu_time`) the binary runs under it, and
    `solver_peak_rss_bytes` is the binary's own peak; otherwise it is None and only the tree-wide
    `peak_rss_bytes` exists. GNU time turns a signalled binary into exit 128+N; that is mapped back
    to -N, so `returncode` reads as it does without the reporter.

    With `perf` (a path, see `perf_stat`) a `CycleCounter` attaches to the solver, and `perf` in the
    result holds its counts and `effective_khz`; otherwise it is None.

    `guard` is `(comm, cmdline-substring, ceiling_kb)` for `tools/rss-guard.sh`. `should_stop` is
    polled every 0.2 s; once it returns true the child gets SIGINT, then SIGKILL after
    `stop_grace_s`. Output goes through files, not pipes, so nothing has to drain them while the
    child runs and the controller can block in `wait4`.
    """
    before = snapshot(cpus)
    with tempfile.TemporaryFile(dir=scratch_dir) as out, tempfile.TemporaryFile(dir=scratch_dir) as err, \
            tempfile.NamedTemporaryFile('r', dir=scratch_dir) as report, \
            tempfile.NamedTemporaryFile('r', dir=scratch_dir) as perf_report:
        # GNU time ignores SIGINT while it waits; `timeout` signals its whole process group, so the
        # binary still receives the INT, and time reports once it exits.
        reporter = [rss_reporter, '-f', '%M', '-o', report.name] if rss_reporter else []
        started = time.perf_counter_ns()
        child = subprocess.Popen(['taskset', '-c', cpus, 'timeout', '--signal=INT', f'--kill-after={kill_after_s}s',
                                  str(timeout_s), *reporter, *map(str, argv)], stdout=out, stderr=err,
                                 preexec_fn=_die_with_parent)
        sampler = Sampler(cpus)
        sampler.start()
        counter = None
        if perf is not None:
            wrappers = RUNNER_WRAPPERS | ({Path(rss_reporter).name[:15]} if rss_reporter else set())
            counter = CycleCounter(perf, child.pid, wrappers, perf_report.name)
            counter.start()
        watch = None
        if guard is not None:
            comm, match, ceiling_kb = guard
            # Integer seconds only: a fractional poll is an arithmetic error in the guard, which then
            # exits 1 having guarded nothing (#901's walls session records show it).
            watch = subprocess.Popen(['bash', str(ROOT / 'tools/rss-guard.sh'), comm, match, str(ceiling_kb),
                                      '--poll', '1', '--wait', '3', '--signal', 'INT'],
                                     stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
                                     preexec_fn=_die_with_parent)
        stopped, done = threading.Event(), threading.Event()

        def stopper():
            while not done.wait(0.2):
                if should_stop():
                    stopped.set()
                    child.send_signal(signal.SIGINT)
                    if not done.wait(stop_grace_s):
                        try:  # `timeout` leads its own process group; take the binary with it
                            os.killpg(child.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            child.kill()
                    return

        if should_stop is not None:
            threading.Thread(target=stopper, daemon=True).start()
        _, status, usage = os.wait4(child.pid, 0)
        wall = time.perf_counter_ns() - started
        done.set()
        # At once: with the tree reaped, a later search could only find an unrelated process.
        cycles = counter.finish() if counter is not None else None
        child.returncode = os.waitstatus_to_exitcode(status)
        guard_rc, guard_err = None, ''
        if watch is not None:
            try:
                guard_rc = watch.wait(timeout=10)
            except subprocess.TimeoutExpired:
                watch.kill()
                guard_rc = 'hung'
            guard_err = watch.stderr.read()[-500:]
        solver_kb, solver_sig = parse_time_report(report.read()) if rss_reporter else (None, None)
        if solver_sig is not None and child.returncode == 128 + solver_sig:
            child.returncode = -solver_sig
        sampler.stop.set()
        sampler.join()
        after = snapshot(cpus)
        out.seek(0)
        err.seek(0)
        return dict(cpus=cpus, process_wall_ns=wall, returncode=child.returncode,
                    cpu_seconds=usage.ru_utime + usage.ru_stime, peak_rss_bytes=usage.ru_maxrss * 1024,
                    solver_peak_rss_bytes=None if solver_kb is None else solver_kb * 1024,
                    rusage=dict(nvcsw=usage.ru_nvcsw, nivcsw=usage.ru_nivcsw, majflt=usage.ru_majflt,
                                minflt=usage.ru_minflt, inblock=usage.ru_inblock, oublock=usage.ru_oublock),
                    rss_guard_rc=guard_rc, rss_guard_stderr=guard_err, before=before, after=after,
                    freq=summarize_freq(sampler.samples), perf=cycles, stopped=stopped.is_set(),
                    stdout=out.read(), stderr=err.read())
