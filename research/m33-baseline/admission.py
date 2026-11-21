#!/usr/bin/env python3
"""#966 M33-0: the candidate pool, the admission rule and the held-out draw (plan §5.2, §5.4).

    admission.py pool --study BIN > candidates.json      # digests, exclusions, draw order
    admission.py run --study BIN --grobx BIN --msolve BIN --output admission.jsonl
    admission.py draw > held-out.json                    # from the two files above

`run` walks each track's candidates in draw order and stops a track once two pass (at most one
MQ). It retains pass/fail per criterion and the basis digests, never a wall: the held-out rows are
not timed for Zeebra until Gate D (plan §13), so no figure that could steer a change is recorded.
"""
import argparse
import hashlib
import json
import os
import re
import resource
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools/external'))
import basis_digest  # noqa: E402

TRACKS = {'G': ('wide64', 'goldilocks'), 'M': ('gf32003', 'm31')}
FAMILIES = ([f'katsura-{n}' for n in range(8, 13)] + [f'eco-{n}' for n in range(10, 14)]
            + [f'cyclic-{n}' for n in range(6, 9)] + [f'noon-{n}' for n in range(7, 9)]
            + [f'mq-random-{n}-s{s}' for n in range(9, 12) for s in range(1, 9)])
# Every M29–M32 table, plan and finding: a family size named in any of them is excluded at every
# field (stricter than the plan's per-instance rule, so no field-twin of a tuned row is drawn).
PRIOR = [*ROOT.glob('research/m29-*'), *ROOT.glob('research/m3[0-2]-*'), *ROOT.glob('docs/research/m29*'),
         *ROOT.glob('docs/research/m3[0-2]*'), ROOT / 'docs/MILESTONE-ADAPTIVE-F4.md']
NAMED = re.compile(r'\b(katsura|eco|cyclic|noon|mq-random)-(\d+)\b')
CAP_S, CAP_BYTES, FLOOR_NS = 180, 8 * 2**30, 300 * 10**6
CERTIFIED_CAP_S = 600
CPUS = os.environ.get('M33_ADMISSION_CPUS', '8-23')


def family_size(name):
    return re.sub(r'-s\d+$', '', name)


def prior_names(paths=PRIOR):
    named = set()
    for path in paths:
        files = [path] if path.is_file() else [p for p in path.rglob('*') if p.suffix in ('.md', '.py', '.json', '.rs')]
        for f in files:
            named.update('-'.join(m) for m in NAMED.findall(f.read_text(errors='replace')))
    return named


def draw_key(track, digest):
    return hashlib.sha256(f'M33-holdout{track}{digest}'.encode()).hexdigest()


def pool(study):
    excluded = prior_names()
    tracks = {}
    for track, fields in TRACKS.items():
        rows = []
        for field in fields:
            for name in FAMILIES:
                row = json.loads(subprocess.check_output(
                    [study, '--field', field, '--name', name, '--engine', 'f4', '--generate', '--input-only'], text=True))
                prior = family_size(name) in excluded and not name.startswith('mq-random')
                rows.append(dict(field=field, name=name, digest=row['digest'], key=draw_key(track, row['digest']),
                                 excluded='named in M29–M32' if prior else None))
        rows.sort(key=lambda r: r['key'])
        tracks[track] = rows
    return dict(issue=966, rule='plan §5.4: SHA-256("M33-holdout" ‖ track ‖ input digest), ascending',
                excluded_family_sizes=sorted(excluded), tracks=tracks)


def guarded(argv, wall_s):
    """Exit status, process wall and the child's peak RSS; the child is killed past either cap."""
    started = time.monotonic_ns()
    child = subprocess.Popen(['taskset', '-c', CPUS, *argv], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True, start_new_session=True)
    peak, stop = 0, None
    while child.poll() is None:
        try:
            for line in Path(f'/proc/{child.pid}/status').read_text().splitlines():
                if line.startswith('VmHWM:'):
                    peak = max(peak, int(line.split()[1]) * 1024)
        except (FileNotFoundError, ProcessLookupError):
            pass
        if peak > CAP_BYTES or time.monotonic_ns() - started > wall_s * 10**9:
            stop = 'rss' if peak > CAP_BYTES else 'wall'
            os.killpg(child.pid, signal.SIGKILL)
            break
        time.sleep(0.01)
    out, err = child.communicate()
    return dict(rc=child.returncode, wall_ns=time.monotonic_ns() - started, peak=peak, stop=stop, stdout=out,
                stderr=err[-2000:])


def zeebra(study, row, workers):
    r = guarded([study, '--field', row['field'], '--name', row['name'], '--generate', '--engine', 'entry',
                 '--workers', str(workers), '--digest-only', '--wall-s', str(CAP_S)], CAP_S + 5)
    report = json.loads(r['stdout']) if r['rc'] == 0 and r['stdout'].strip() else {}
    return r, report.get('status') == 'complete' and report.get('digest') == row['digest'], report.get('basis_m33')


def request(study, row):
    return json.loads(subprocess.check_output(
        [study, '--field', row['field'], '--name', row['name'], '--engine', 'f4', '--generate', '--input-only'], text=True))


def grobx(binary, case, mode, wall_s):
    with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as f:
        json.dump(dict(variables=case['variables'], modulus=int(case['modulus']), order='grevlex', workers=1,
                       generators=case['generators'], mode=mode, wall_ns=wall_s * 10**9, rss_bytes=CAP_BYTES), f)
    r = guarded([binary, f.name], wall_s + 5)
    os.unlink(f.name)
    raw = json.loads(r['stdout']) if r['rc'] == 0 and r['stdout'].strip() else {}
    ok = bool(raw.get('basis')) and not raw.get('stopped') and (mode == 'raw' or raw.get('certified'))
    digest = None
    if ok:
        texts = [t for t in re.split(r'[,\n\[\]]', raw['basis']) if t.strip()]
        digest = basis_digest.basis_digest(texts, int(case['modulus']), case['variables'])
    return r, ok, digest


def msolve(binary, case, workers):
    with tempfile.TemporaryDirectory(dir=os.environ.get('TMPDIR')) as d:
        src, out = Path(d, 'in.ms'), Path(d, 'out.ms')
        src.write_text(','.join(case['variables']) + '\n' + case['modulus'] + '\n' + ',\n'.join(case['generators']) + '\n')
        r = guarded([binary, '-f', str(src), '-o', str(out), '-t', str(workers), '-g', '2'], CAP_S + 5)
        text = out.read_text() if r['rc'] == 0 and out.exists() else ''
    body = text[text.find('[') + 1:text.rfind(']')] if '[' in text else ''
    texts = [t for t in body.replace('\n', '').split(',') if t.strip()]
    digest = basis_digest.basis_digest(texts, int(case['modulus']), case['variables']) if texts else None
    return r, digest is not None, digest


def singular(case):
    names = ','.join(case['variables'])
    script = (f"short=0;\nring r={case['modulus']},({names}),dp;\nideal i={','.join(case['generators'])};\n"
              "option(redSB);\nideal g=std(i);\nint k;\nfor(k=1;k<=size(g);k++){print(g[k]);}\nquit;\n")
    r = guarded(['Singular', '-q', '--no-rc', '-c', script], CERTIFIED_CAP_S)
    texts = [t for t in r['stdout'].splitlines() if t.strip()]
    ok = r['rc'] == 0 and bool(texts)
    return r, ok, basis_digest.basis_digest(texts, int(case['modulus']), case['variables']) if ok else None


def floor_ok(r, control):
    return r['stop'] is None and r['wall_ns'] >= 2 * control


def admit(args, track, row, controls):
    """§5.2 for one candidate: booleans per criterion and the digests; no wall is returned."""
    case = request(args.study, row)
    zeebra_runs = [zeebra(args.study, row, w) for w in ((1,) if track == 'G' else (1, 16))]
    if track == 'G':
        comp = [grobx(args.grobx, case, 'raw', CAP_S)]
        ref = grobx(args.grobx, case, 'certified', CERTIFIED_CAP_S)
    else:
        comp = [msolve(args.msolve, case, w) for w in (1, 16)]
        ref = singular(case)
    digests = {d for _, ok, d in zeebra_runs + comp if ok} | ({ref[2]} if ref[1] else set())
    checks = dict(
        zeebra_completes=all(ok for _, ok, _ in zeebra_runs),
        competitor_completes=all(ok for _, ok, _ in comp),
        bounded=all(r['stop'] is None for r, _, _ in zeebra_runs + comp),
        competitor_floor=all(r['wall_ns'] >= FLOOR_NS for r, _, _ in comp),
        startup_floor=(all(floor_ok(r, controls['zeebra']) for r, _, _ in zeebra_runs)
                       and all(floor_ok(r, controls['competitor']) for r, _, _ in comp)),
        reference_completes=ref[1],
        digests_agree=len(digests) == 1 and ref[1])
    return dict(track=track, field=row['field'], name=row['name'], digest=row['digest'], checks=checks,
                admitted=all(checks.values()), basis_m33=sorted(digests))


def control_walls(args, track):
    """The Katsura-4 startup control (`external-comparison-protocol.md` §7), median of three."""
    k4 = dict(field=TRACKS[track][0], name='katsura-4', digest=None)
    case = request(args.study, k4)
    zs = sorted(zeebra(args.study, dict(k4, digest=case['digest']), 1)[0]['wall_ns'] for _ in range(3))
    run = (lambda: grobx(args.grobx, case, 'raw', 30)) if track == 'G' else (lambda: msolve(args.msolve, case, 1))
    cs = sorted(run()[0]['wall_ns'] for _ in range(3))
    return dict(zeebra=zs[1], competitor=cs[1])


def run(args):
    candidates = json.loads((HERE / 'candidates.json').read_text())
    done = set()
    if args.output.exists():
        done = {(r['track'], r['field'], r['name']) for r in map(json.loads, args.output.read_text().splitlines())}
    with args.output.open('a') as out:
        for track, rows in candidates['tracks'].items():
            if args.track and track != args.track:
                continue
            controls = control_walls(args, track)
            prior = [json.loads(line) for line in args.output.read_text().splitlines()]
            for row in rows:
                if len(drawn(prior, track)) == 2:
                    break
                if row['excluded'] or (track, row['field'], row['name']) in done or skip_mq(prior, track, row):
                    continue
                record = admit(args, track, row, controls)
                prior.append(record)
                out.write(json.dumps(record) + '\n')
                out.flush()
                print(track, row['field'], row['name'], 'admitted' if record['admitted'] else
                      'refused: ' + ','.join(k for k, v in record['checks'].items() if not v), flush=True)


def skip_mq(records, track, row):
    return row['name'].startswith('mq-random') and any(r['name'].startswith('mq-random') for r in drawn(records, track))


def drawn(records, track):
    """The first two admitted candidates in draw order, at most one MQ (records are in draw order)."""
    out = []
    for r in records:
        if r['track'] != track or not r['admitted'] or len(out) == 2:
            continue
        if r['name'].startswith('mq-random') and any(o['name'].startswith('mq-random') for o in out):
            continue
        out.append(r)
    return out


def draw():
    records = [json.loads(line) for line in (HERE / 'admission.jsonl').read_text().splitlines()]
    return {track: [dict(field=r['field'], name=r['name'], digest=r['digest'], basis_m33=r['basis_m33'][0])
                    for r in drawn(records, track)] for track in TRACKS}


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=('pool', 'run', 'draw'))
    p.add_argument('--study', help='sig_f4_study built with --features research-sigf4')
    p.add_argument('--grobx', help='grobx-driver at the M33 pin')
    p.add_argument('--msolve')
    p.add_argument('--track', choices=sorted(TRACKS))
    p.add_argument('--output', type=Path, default=HERE / 'admission.jsonl')
    args = p.parse_args()
    if args.command == 'pool':
        print(json.dumps(pool(args.study), indent=1))
    elif args.command == 'run':
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        run(args)
    else:
        print(json.dumps(draw(), indent=1))


if __name__ == '__main__':
    main()
