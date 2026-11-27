"""Set up $W for #1107: binaries checked against the signed hashes, the s5/m5 wrappers, comparand
inputs, and the workloads' source tree with warm W1/W3 builds. Idempotent; refuses a hash mismatch.

Usage: python3 -I prepare.py --pilot-dir /buildcache/cargo-target/zeebra-1106 --grobx <grobx-driver> --msolve <msolve>
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[1] / 'research/m33-baseline'))
import calib  # noqa: E402
import admission  # noqa: E402


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--pilot-dir', type=Path, required=True)
    p.add_argument('--grobx', type=Path, required=True)
    p.add_argument('--msolve', type=Path, required=True)
    p.add_argument('--skip-builds', action='store_true')
    a = p.parse_args()
    W, paths = calib.W, calib.Paths(calib.W)
    for d in ('bin', 'inputs', 'jobs', 'tmp', 'sessions'):
        (W / d).mkdir(parents=True, exist_ok=True)
    src = {'sig': a.pilot_dir / 'target/release/examples/sig_f4_study',
           'm29': a.pilot_dir / 'target/release/examples/m29_cost_model',
           'sweep': a.pilot_dir / 'bin/sweep', 'stream': a.pilot_dir / 'bin/stream',
           'grobx': a.grobx, 'msolve': a.msolve}
    for key, path in src.items():
        dst = paths.bin[key]
        if not dst.exists():
            shutil.copy2(path, dst)
        want = calib.SIGNED[dst.name]
        if calib.sha(dst) != want:
            raise SystemExit(f'{dst}: SHA-256 {calib.sha(dst)} is not the signed {want}')
        print(f'{dst.name}: signed hash ok')
    sig, sweep = paths.bin['sig'], paths.bin['sweep']
    # s5 exactly as #985 (research/m33-calibration/run.sh); m5 as §4.2 with the array size argument.
    paths.bin['s5'].write_text(
        f'#!/bin/sh\nt0=$(date +%s%N); "{sig}" "$@"; rc=$?; t1=$(date +%s%N)\n'
        "sleep \"$(awk -v d=$((t1 - t0)) 'BEGIN { printf \"%.6f\", d * 0.05 / 1e9 }')\"\nexit $rc\n")
    paths.bin['m5'].write_text(f'#!/bin/sh\np=$1; t=$2; m=$3; shift 3\n"{sig}" "$@"; rc=$?\n"{sweep}" "$t" "$p" "$m"\nexit $rc\n')
    for k in ('s5', 'm5'):
        paths.bin[k].chmod(0o755)
    for inst, key in calib.INPUTS.items():
        field, name = inst.split('/')
        d = W / 'inputs' / inst.replace('/', '__')
        d.mkdir(exist_ok=True)
        case = json.loads(subprocess.check_output([sig, '--field', field, '--name', name, '--engine', 'f4',
                                                   '--input-only'], text=True))
        (d / 'case.json').write_text(json.dumps(case, indent=1) + '\n')
        if key == 'ms':
            (d / 'in.ms').write_text(admission.msolve_input(case))
        else:
            base = dict(variables=case['variables'], modulus=int(case['modulus']), order='grevlex', workers=1,
                        generators=case['generators'])
            (d / 'grobx.json').write_text(json.dumps(dict(base, mode='raw', wall_ns=admission.CAP_S * 10**9,
                                                          rss_bytes=admission.CAP_BYTES)))
        print(f'{inst}: input {key} written')
    srcdir = W / 'src'
    if not (srcdir / 'Cargo.toml').exists():
        srcdir.mkdir(exist_ok=True)
        archive = subprocess.run(['git', '-C', str(HERE.parents[1]), 'archive', calib.C], check=True,
                                 capture_output=True).stdout
        subprocess.run(['tar', '-x', '-C', str(srcdir)], input=archive, check=True)
        print(f'src: git archive {calib.C[:8]} extracted')
    if a.skip_builds:
        return
    env = dict(os.environ, RUSTC_WRAPPER='', TMPDIR=str(W / 'tmp'))
    for target, cmd in (('load-w1', ['cargo', 'build', '-q', '-j8', '--tests']),
                        ('load-w3', ['cargo', 'test', '-q', '-j16', '--lib', '--no-run'])):
        subprocess.run(cmd, cwd=srcdir, env=dict(env, CARGO_TARGET_DIR=str(W / target)), check=True)
        print(f'{target}: warm build done')


if __name__ == '__main__':
    main()
