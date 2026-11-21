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
    # A controller started in the background inherits SIGINT ignored, and so would the binary; then
    # neither `timeout --signal=INT` nor a cancel could stop it short of `--kill-after`.
    signal.signal(signal.SIGINT, signal.SIG_DFL)
    ctypes.CDLL(None, use_errno=True).prctl(_PR_SET_PDEATHSIG, signal.SIGTERM)


def run_child(argv, cpus, timeout_s, kill_after_s=60, guard=None, should_stop=None, stop_grace_s=10,
              scratch_dir=None):
    """One child under `taskset -c cpus timeout --signal=INT`, with `cpu-context` before and after.

    `guard` is `(comm, cmdline-substring, ceiling_kb)` for `tools/rss-guard.sh`. `should_stop` is
    polled every 0.2 s; once it returns true the child gets SIGINT, then SIGKILL after
    `stop_grace_s`. Output goes through files, not pipes, so nothing has to drain them while the
    child runs and the controller can block in `wait4`.
    """
    before = snapshot(cpus)
    with tempfile.TemporaryFile(dir=scratch_dir) as out, tempfile.TemporaryFile(dir=scratch_dir) as err:
        started = time.perf_counter_ns()
        child = subprocess.Popen(['taskset', '-c', cpus, 'timeout', '--signal=INT', f'--kill-after={kill_after_s}s',
                                  str(timeout_s), *map(str, argv)], stdout=out, stderr=err,
                                 preexec_fn=_die_with_parent)
        sampler = Sampler(cpus)
        sampler.start()
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
        child.returncode = os.waitstatus_to_exitcode(status)
        guard_rc, guard_err = None, ''
        if watch is not None:
            try:
                guard_rc = watch.wait(timeout=10)
            except subprocess.TimeoutExpired:
                watch.kill()
                guard_rc = 'hung'
            guard_err = watch.stderr.read()[-500:]
        sampler.stop.set()
        sampler.join()
        after = snapshot(cpus)
        out.seek(0)
        err.seek(0)
        return dict(cpus=cpus, process_wall_ns=wall, returncode=child.returncode,
                    cpu_seconds=usage.ru_utime + usage.ru_stime, peak_rss_bytes=usage.ru_maxrss * 1024,
                    rss_guard_rc=guard_rc, rss_guard_stderr=guard_err, before=before, after=after,
                    freq=summarize_freq(sampler.samples), stopped=stopped.is_set(),
                    stdout=out.read(), stderr=err.read())
