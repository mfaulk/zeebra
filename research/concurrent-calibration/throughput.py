"""§8.3 development throughput: the reference build's wall on REST with no benchmark vs while a calibration
job runs. The jobs run beside a build are labeled `throughput` and are not deciding data.

Usage: python3 -I throughput.py <label> [--n 3]   (takes and releases the CCD 1-2 reservation itself)
"""
import argparse
import json
import shutil
import statistics
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import session as S  # noqa: E402

BUILD = ['cargo', 'build', '--release', '--tests', '-j48']


def build(s, tag):
    tgt = S.W / 'ref-build'
    shutil.rmtree(tgt, ignore_errors=True)
    t0 = time.monotonic()
    rc = subprocess.run(['taskset', '-c', S.REST, *BUILD], cwd=S.SRC, env=dict(S.ENV, CARGO_TARGET_DIR=str(tgt)),
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode
    wall = time.monotonic() - t0
    s.log(f'throughput {tag}: build rc={rc} wall={wall:.1f}s load1={s.uptime()}')
    if rc:
        raise SystemExit(f'reference build failed rc={rc}')
    return wall


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('label')
    ap.add_argument('--n', type=int, default=3)
    a = ap.parse_args()
    s = S.Session(a.label)
    S.wait_for_machine(s)
    alone = [build(s, f'alone {i}') for i in range(a.n)]
    r = subprocess.run([S.RESERVE, 'reserve', '1,2'], capture_output=True, text=True)
    s.log(f'reserve rc={r.returncode} {r.stdout.strip()}')
    beside = []
    try:
        for i in range(a.n):
            box = {}
            t = threading.Thread(target=lambda: box.setdefault('job', S.run_job(s, 'calibration', 'W0', 50 + i)))
            t.start()
            time.sleep(20)  # the job is running before the build starts
            beside.append(build(s, f'beside {i}'))
            t.join()
    finally:
        r = subprocess.run([S.RESERVE, 'release'], capture_output=True, text=True)
        s.log(f'release rc={r.returncode} {r.stdout.strip()}')
    out = dict(alone=alone, beside=beside, n=a.n, ratio=statistics.median(beside) / statistics.median(alone),
               command=' '.join(BUILD), cpus=S.REST,
               note=f'`{" ".join(BUILD)}` of `git archive {S.calib.C[:8]}` from clean on {S.REST}; '
                    'the jobs beside it are labeled throughput and not deciding')
    (s.dir / 'throughput.json').write_text(json.dumps(out, indent=1) + '\n')
    s.log(f'throughput ratio {out["ratio"]:.3f}')


if __name__ == '__main__':
    main()
