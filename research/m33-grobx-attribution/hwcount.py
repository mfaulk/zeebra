#!/usr/bin/env python3
"""User-space hardware counters for one child process, by `perf_event_open` (#970).

    hwcount.py -- COMMAND [ARGS...]

`perf` is not installed on this host and `perf_event_paranoid` is 2, which still lets a process
count its own children in user mode. The counters attach to the child before it `exec`s
(`enable_on_exec`), follow its threads (`inherit`) and exclude the kernel, so the wrapper's own
Python start-up is not counted. The child's stdout and stderr pass through unchanged; the counts
follow on stderr as one final `hwcount {json}` line, so a bench-job journal keeps them per attempt,
and the exit status is the child's. Zen 3 has six core counters and the NMI watchdog holds one, so
five events run unmultiplexed; any that ran for less than its enabled time is recorded with the
fraction it ran.
"""
import ctypes
import json
import os
import struct
import sys

SYS_PERF_EVENT_OPEN = 298  # x86-64
ATTR_SIZE = 128
HARDWARE, HW_CACHE, RAW = 0, 3, 4
# Zen 3 core PMC 0x43 ls_dmnd_fills_from_sys: demand data-cache fills by source; umask 0x08 | 0x40 is
# local and remote DRAM.
EVENTS = (
    ('cycles', HARDWARE, 0),
    ('instructions', HARDWARE, 1),
    ('l1d_reads', HW_CACHE, 0),
    ('l1d_read_misses', HW_CACHE, 1 << 16),
    ('fills_dram', RAW, 0x4843),
)
FLAGS = (1 << 0) | (1 << 1) | (1 << 5) | (1 << 6) | (1 << 12)  # disabled inherit !kernel !hv enable_on_exec
READ_FORMAT = 1 | 2  # TOTAL_TIME_ENABLED | TOTAL_TIME_RUNNING


def attr(kind, config):
    """A zero-padded `perf_event_attr` (ABI version 7, 128 bytes) counting one event."""
    head = struct.pack('IIQQQQQ', kind, ATTR_SIZE, config, 0, 0, READ_FORMAT, FLAGS)
    return head + bytes(ATTR_SIZE - len(head))


def derived(counts):
    """IPC and per-access rates from raw counts; None where a denominator is missing or zero."""
    def ratio(a, b):
        return counts[a] / counts[b] if counts.get(a) is not None and counts.get(b) else None
    return dict(ipc=ratio('instructions', 'cycles'), l1d_miss_rate=ratio('l1d_read_misses', 'l1d_reads'),
                dram_per_l1d_miss=ratio('fills_dram', 'l1d_read_misses'))


def parse(raw):
    """One counter's `read` buffer: value, time enabled, time running."""
    value, enabled, running = struct.unpack('QQQ', raw)
    return dict(value=value, enabled_ns=enabled, running_ns=running)


def main(argv):
    if len(argv) < 3 or argv[1] != '--':
        sys.stderr.write(__doc__)
        return 64
    command = argv[2:]
    libc = ctypes.CDLL(None, use_errno=True)
    ready_r, ready_w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(ready_w)
        os.read(ready_r, 1)
        try:
            os.execvp(command[0], command)
        finally:
            os._exit(127)
    os.close(ready_r)
    fds, errors = {}, {}
    for name, kind, config in EVENTS:
        buffer = ctypes.create_string_buffer(attr(kind, config), ATTR_SIZE)
        fd = libc.syscall(SYS_PERF_EVENT_OPEN, buffer, pid, -1, -1, 0)
        if fd < 0:
            errors[name] = os.strerror(ctypes.get_errno())
        else:
            fds[name] = fd
    os.write(ready_w, b'x')
    os.close(ready_w)
    _, status = os.waitpid(pid, 0)
    counters = {name: parse(os.read(fd, 24)) for name, fd in fds.items()}
    counts = {name: c['value'] for name, c in counters.items()}
    multiplexed = {n: round(c['running_ns'] / c['enabled_ns'], 4) for n, c in counters.items()
                   if c['enabled_ns'] and c['running_ns'] < c['enabled_ns']}
    record = dict(schema='hwcount-v1', counts=counts, derived=derived(counts), multiplexed=multiplexed,
                  errors=errors, status=status)
    sys.stderr.write('hwcount ' + json.dumps(record, sort_keys=True) + '\n')
    return os.waitstatus_to_exitcode(status)


if __name__ == '__main__':
    sys.exit(main(sys.argv))
