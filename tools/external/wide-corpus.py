#!/usr/bin/env python3
"""Freeze and measure wide-field inputs; compare complete reduced bases before publishing ratios."""
import argparse
import gzip
import hashlib
import importlib.util
import json
import os
import platform
import re
from datetime import datetime, timezone
from pathlib import Path
import shutil
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
CATALOG = ROOT / 'research/wide-corpus/cases.json'
spec = importlib.util.spec_from_file_location('guard', Path(__file__).with_name('mq10-profile.py'))
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
COMPLETE = ('complete', 'verified')
ENGINES = ('zeebra', 'groebner.jl', 'groebner-rs', 'grobx')

REVISIONS = {'groebner-rs': 'c3e1d630fba9b2155a4c389d9022f13e0ba09218',
             'grobx': '1854835dbc25f24dc9a9ba017024d5030e99da1c'}
spec = importlib.util.spec_from_file_location('grobx_work', Path(__file__).with_name('grobx-work-study.py'))
grobx_work = importlib.util.module_from_spec(spec)
spec.loader.exec_module(grobx_work)


def canonical_polynomial(text, modulus, variables):
    terms = {}
    for term in ''.join(text.split()).replace('-', '+-').split('+'):
        if not term:
            continue
        coefficient = -1 if term.startswith('-') else 1
        exponents = [0] * len(variables)
        for factor in term.lstrip('-').split('*'):
            match = re.fullmatch(r'([A-Za-z][A-Za-z0-9_]*|[0-9]+)(?:\^([0-9]+))?', factor)
            if not match:
                raise ValueError('invalid polynomial factor: ' + factor)
            base, power = match[1], int(match[2] or 1)
            if base.isdigit():
                coefficient = coefficient * pow(int(base), power, modulus) % modulus
            elif base in variables:
                exponents[variables.index(base)] += power
            else:
                raise ValueError('unknown polynomial variable: ' + base)
        key = tuple(exponents)
        terms[key] = (terms.get(key, 0) + coefficient) % modulus
    terms = {m: c for m, c in terms.items() if c}
    if not terms:
        return ()
    leading = max(terms, key=lambda m: (sum(m), tuple(-e for e in reversed(m))))
    scale = pow(terms[leading], -1, modulus)
    return tuple(sorted((m, c * scale % modulus) for m, c in terms.items()))


def validate_native(raw, request, engine):
    contract = 2 if engine == 'groebner-rs' else 1
    if (raw.get('contract') != contract or raw.get('revision') != REVISIONS[engine]
            or raw.get('isa') != 'x86-64-v3' or not raw.get('build')):
        raise ValueError('unrecognized native driver identity')
    for setting in ('PROFILE=release;', 'OPT_LEVEL=3;', 'CARGO_PROFILE_RELEASE_LTO=fat;',
                    'CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1;'):
        if setting not in raw.get('build_metadata', ''):
            raise ValueError('native driver profile differs')
    modulus, variables = request['modulus'], request['variables']
    canonical = lambda p: canonical_polynomial(p, modulus, variables)
    if engine == 'groebner-rs':
        if any(raw.get(k) != request[k] for k in ('modulus', 'variables', 'order', 'workers')):
            raise ValueError('native driver returned a different ring')
        echoes = raw.get('generators', [])
        basis = raw.get('basis')
    else:
        if raw.get('input') != request or raw.get('flaw') is not None or raw.get('certified') is not None:
            raise ValueError('grobx changed input or objective')
        if raw.get('generator_echoes') != raw.get('checker_echoes'):
            raise ValueError('grobx generator parsers disagree')
        input_text = raw.get('input_text', '')
        if hashlib.sha256(input_text.encode()).hexdigest() != raw.get('input_sha256'):
            raise ValueError('grobx input hash mismatch')
        echoes = []
        for echo in raw.get('generator_echoes', []):
            polys = grobx_work.basis_list(echo)
            if len(polys) > 1:
                raise ValueError('grobx echoed multiple polynomials for one generator')
            echoes.append(polys[0] if polys else '0')
        if raw.get('stopped'):
            return None
        call = next((line for line in raw.get('report', '').splitlines()
                     if len(line.split()) > 1 and line.split()[1] == 'call'), '')
        if any(token not in call.split() for token in ('order=grevlex', 'seed=0', 'threads=1', 'checker=off')):
            raise ValueError('grobx actual call differs from request')
        basis = grobx_work.basis_list(raw['basis'])
    if [canonical(p) for p in echoes] != [canonical(p) for p in request['generators']]:
        raise ValueError('native driver parsed different ordered generators')
    if not isinstance(basis, list) or not basis or any(not canonical(p) for p in basis):
        raise ValueError('native driver returned a missing or zero basis')
    return basis


def enforce_peak(attempt):
    report = attempt.get('report', {})
    peak = max(attempt['observed_tree_peak_bytes'],
               attempt.get('raw', {}).get('kernel_peak_rss_bytes') or 0,
               report.get('peak_rss_bytes') or 0)
    attempt['observed_tree_peak_bytes'] = peak
    if peak > 2 * 1024**3:
        attempt['stop'] = 'rss-2GiB-kernel'
        report.update(status='stopped-by-limit', detail='kernel high water exceeds 2 GiB')


def verify_bases(attempts):
    digests = {a['digest'] for a in attempts if 'digest' in a}
    if len(digests) > 1:
        raise ValueError('oracle inputs have different identities')
    reports = [a['report'] for a in attempts if a.get('report', {}).get('status') in COMPLETE]
    bases = [sorted(canonical_polynomial(p, int(r['modulus']), r['variables']) for p in r['basis'])
             if 'modulus' in r else r['basis'] for r in reports]
    if any(not b for b in bases):
        raise ValueError('nonzero input returned an empty basis')
    if any(sorted(b) != sorted(bases[0]) for b in bases[1:]):
        raise ValueError('complete reduced bases disagree coefficient for coefficient')
    return len(bases)


def wall_ratio(ours, theirs, our_floor, their_floor):
    if min(ours, theirs, our_floor, their_floor) <= 0:
        return None
    if min(ours / our_floor, theirs / their_floor) < 2:
        return None
    return ours / theirs


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + '.tmp')
    payload = (json.dumps(data, indent=2) + '\n').encode()
    tmp.write_bytes(gzip.compress(payload, mtime=0) if path.suffix == '.gz' else payload)
    tmp.replace(path)


def load(path):
    cohort = json.loads(gzip.decompress(path.read_bytes()) if path.suffix == '.gz' else path.read_bytes())
    if cohort.get('storage') != 'wide-corpus-chunks-v1':
        return cohort
    del cohort['storage']
    attempts = []
    for entry in cohort.pop('attempt_payloads'):
        chunks = []
        for part in entry['parts']:
            payload = gzip.decompress((path.parent / part['path']).read_bytes())
            if len(payload) != part['bytes'] or hashlib.sha256(payload).hexdigest() != part['sha256']:
                raise ValueError('wide campaign payload hash/length mismatch')
            chunks.append(payload)
        attempts.append(json.loads(b''.join(chunks)))
    cohort['attempts'] = attempts
    return cohort


def pack(cohort, path, chunk_size=16*1024**2):
    payload_dir = path.parent / (path.name.removesuffix('.gz').removesuffix('.json') + '-payloads')
    payload_dir.mkdir(parents=True, exist_ok=True)
    manifest = {k: v for k, v in cohort.items() if k != 'attempts'}
    manifest.update(storage='wide-corpus-chunks-v1', attempt_payloads=[])
    for attempt in cohort['attempts']:
        data = json.dumps(attempt, separators=(',', ':'), ensure_ascii=False).encode()
        parts = []
        for start in range(0, len(data), chunk_size):
            chunk = data[start:start+chunk_size]
            digest = hashlib.sha256(chunk).hexdigest()
            payload = payload_dir / (digest + '.json-chunk.gz')
            payload.write_bytes(gzip.compress(chunk, mtime=0))
            parts.append(dict(path=str(payload.relative_to(path.parent)), sha256=digest, bytes=len(chunk)))
        manifest['attempt_payloads'].append(dict(field=attempt['field'], name=attempt['name'],
                                                 engine=attempt['engine'], parts=parts))
    write(path, manifest)
    if load(path) != cohort:
        raise ValueError('packing changed the retained campaign')


def validate_catalog(cases):
    identities = set()
    for c in cases:
        key = (c['field'], c['name'])
        if key in identities or hashlib.sha256(c['canonical'].encode()).hexdigest() != c['digest']:
            raise ValueError('duplicate or corrupt frozen input identity')
        identities.add(key)
    if not cases:
        raise ValueError('empty catalog')


def seconds(a):
    # External wall is the supervised solver process, excluding version probes; native wall
    # includes the entire executable so startup and input/output costs are not hidden.
    r = a['report']
    return (a['process_wall_ns'] if r['engine'] == 'zeebra' else r['solver_process_wall_ns']) / 1e9


def summary(cohort, target):
    grouped = {}
    for a in cohort['attempts']:
        grouped.setdefault((a['field'], a['name']), []).append(a)
    floors = {}
    for (field, name), attempts in grouped.items():
        if name == 'katsura-4':
            for a in attempts:
                if a.get('report', {}).get('status') in COMPLETE:
                    floors[field, a['engine']] = seconds(a)
    lines = ['# Hard wide-field board (#738)', '',
             '**Measured at:** `' + cohort['commit'] + '`.', '',
             'One worker, affinity ' + cohort['affinity'] + '; 60 s / 2 GiB per solver attempt. ',
             'Each attempt runs in a fresh process. Native wall includes the complete runner; external wall',
             'is the adapter-supervised solver process and excludes version probing. Wrapper wall is also retained.',
             'All completed bases are normalized in the declared field and compared coefficient for coefficient.',
             'Ratios are Zeebra/comparand wall and require both operands ≥2× their measured Katsura-4 startup control.',
             'BN254 is capability-only: it has no external oracle and no ratios. These are single observations, not medians.', '',
             '| Field | Row | Zeebra s/status | Julia s/status | groebner-rs s/status | grobx s/status | Z/Julia | Z/rs | Z/grobx | Exact bases agreeing |',
             '|---|---|---:|---:|---:|---:|---:|---:|---:|---:|']
    for (field, name), attempts in grouped.items():
        count = verify_bases(attempts)
        by_engine = {a['engine']: a for a in attempts}
        cells, ratios = [], []
        for engine in ENGINES:
            a = by_engine.get(engine)
            if not a:
                cells.append('capability-only' if field == 'bn254' else 'not run')
            elif a.get('report', {}).get('status') in COMPLETE:
                cells.append(f'{seconds(a):.3f}')
            else:
                r = a.get('report', {})
                status = a.get('stop') or r.get('status', 'runner-failure')
                if status == 'stopped-by-limit':
                    detail = r.get('detail', 'unspecified limit')
                    status = 'wall-60s' if 'WallClock' in detail else detail.replace('|', '/').replace('\n', ' ')
                cells.append(status)
        for engine in ENGINES[1:]:
            ours, theirs = by_engine.get('zeebra'), by_engine.get(engine)
            ratio = None
            if (ours and theirs and ours.get('report', {}).get('status') in COMPLETE
                    and theirs.get('report', {}).get('status') in COMPLETE and count >= 2):
                ratio = wall_ratio(seconds(ours), seconds(theirs), floors.get((field, 'zeebra'), 0), floors.get((field, engine), 0))
            ratios.append('—' if ratio is None else f'{ratio:.3f}x')
        lines.append('| ' + ' | '.join([field, name] + cells + ratios + [str(count) if field != 'bn254' else 'no external oracle']) + ' |')
    lines.extend(['', 'Raw inputs, complete bases, versions, binary hashes, limits, stderr, and watchdog stops:',
                  '[campaign.json.gz](campaign.json.gz). Frozen identities: [cases.json](cases.json).', ''])
    target.write_text('\n'.join(lines))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--binary', type=Path)
    p.add_argument('--freeze', action='store_true')
    p.add_argument('--summarize', type=Path)
    p.add_argument('--pack', type=Path, help='losslessly pack retained attempts into <=16MiB input chunks')
    p.add_argument('--output', type=Path, default=ROOT / 'research/wide-corpus/campaign.json.gz')
    p.add_argument('--scratch', type=Path)
    p.add_argument('--fields', default='wide64,goldilocks,bn254')
    p.add_argument('--rows', help='comma separated; default all frozen rows')
    args = p.parse_args()
    if args.pack:
        pack(load(args.pack), args.output)
        return
    if args.summarize:
        summary(load(args.summarize), ROOT / 'research/wide-corpus/BOARD.md')
        return
    if not args.binary:
        p.error('--binary required')
    cases = json.loads(subprocess.check_output([str(args.binary), '--list'], text=True))
    validate_catalog(cases)
    if args.freeze:
        write(CATALOG, cases)
        return
    if cases != load(CATALOG):
        raise ValueError('runner inputs differ from frozen catalog')
    affinity = ','.join(map(str, sorted(os.sched_getaffinity(0))))
    if not os.environ.get('ZEEBRA_MACHINE') or os.environ.get('ZEEBRA_AFFINITY') != affinity:
        p.error('set ZEEBRA_MACHINE and ZEEBRA_AFFINITY to actual CPU affinity')
    if not args.scratch or str(args.scratch.resolve()).startswith(str(Path.home())):
        p.error('--scratch must be outside home/worktree (use /buildcache)')
    if subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=ROOT, text=True).strip():
        p.error('commit tracked changes before measuring')
    args.scratch.mkdir(parents=True, exist_ok=True)
    cohort = dict(schema=1, commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                  base_commit=subprocess.check_output(['git', 'merge-base', 'HEAD', 'origin/main'], cwd=ROOT, text=True).strip(),
                  patch_id=subprocess.check_output(['git', 'patch-id', '--stable'], input=subprocess.check_output(['git', 'diff', 'origin/main...HEAD'], cwd=ROOT), cwd=ROOT).decode().split()[0],
                  machine=os.environ['ZEEBRA_MACHINE'], affinity=affinity, workers=1,
                  started_at=datetime.now(timezone.utc).isoformat(),
                  platform=platform.platform(),
                  cpu=next((line.split(':',1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')), 'unknown'),
                  rustc=subprocess.check_output(['rustc', '-vV'], text=True),
                  build='release; fat LTO; codegen-units=1; x86-64-v3; system allocator',
                  rustflags=os.environ.get('RUSTFLAGS'),
                  load_start=os.getloadavg(),
                  policy='60s/2GiB solver; 60s native or 65s runner /2GiB tree watchdog; direct native drivers; one process per case/engine',
                  binaries={}, attempts=[])
    for name, binary in [('zeebra', str(args.binary)), ('groebner.jl', shutil.which('julia')),
                         ('groebner-rs', shutil.which(os.environ.get('ZEEBRA_GROEBNER_RS_DRIVER', 'groebner-rs-driver'))), ('grobx', shutil.which(os.environ.get('ZEEBRA_GROBX_DRIVER', 'grobx-driver')))]:
        if binary:
            cohort['binaries'][name] = dict(path=binary, sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest())
    # Resume only an identical instrument on the same host and affinity; preserve earlier stops.
    if args.output.exists():
        previous = load(args.output)
        for key in ('commit', 'binaries', 'affinity', 'machine', 'policy'):
            if previous[key] != cohort[key]:
                raise ValueError('cannot resume a different campaign: ' + key)
        cohort = previous
    done = {(a['field'], a['name'], a['engine']) for a in cohort['attempts']}
    for c in cases:
        if c['field'] not in args.fields.split(',') or (args.rows and c['name'] not in args.rows.split(',')):
            continue
        engines = ('zeebra',) if c['field'] == 'bn254' else ENGINES
        for engine in engines:
            if (c['field'], c['name'], engine) in done:
                continue
            stem = args.scratch / str(len(cohort['attempts']))
            direct = engine in REVISIONS
            request = dict(variables=c['variables'], modulus=int(c['modulus']), order='grevlex',
                           workers=1, generators=c['generators'])
            if direct:
                if engine == 'grobx':
                    request.update(mode='raw', wall_ns=60_000_000_000, rss_bytes=2*1024**3)
                stem.with_suffix('.request').write_text(json.dumps(request))
                command = [cohort['binaries'][engine]['path'], str(stem.with_suffix('.request'))]
            else:
                command = [str(args.binary), '--field', c['field'], '--row', c['name'], '--engine', engine]
            wall_ns = 60_000_000_000 if direct else 65_000_000_000
            started, peak, stop = time.monotonic_ns(), 0, None
            with stem.with_suffix('.stdout').open('w') as out, stem.with_suffix('.stderr').open('w') as err:
                process = subprocess.Popen(command, stdout=out, stderr=err, start_new_session=True)
                while process.poll() is None:
                    peak = max(peak, guard.tree_hwm(process.pid))
                    if peak > 2*1024**3 or time.monotonic_ns()-started > wall_ns:
                        stop = 'rss-2GiB' if peak > 2*1024**3 else ('wall-60s-native' if direct else 'wall-65s-tree')
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                        break
                    time.sleep(0.005)
            a = dict(field=c['field'], name=c['name'], engine=engine, digest=c['digest'],
                     exit=process.returncode, stop=stop, process_wall_ns=time.monotonic_ns()-started,
                     observed_tree_peak_bytes=peak, stderr=stem.with_suffix('.stderr').read_text())
            if process.returncode == 0:
                raw = json.loads(stem.with_suffix('.stdout').read_text())
                if direct:
                    a['raw'] = raw
                    basis = validate_native(raw, request, engine)
                    a['report'] = dict(c, engine=engine, status='stopped-by-limit' if basis is None else 'complete',
                                       solver_process_wall_ns=a['process_wall_ns'], engine_wall_ns=raw.get('solve_ns'),
                                       version={k: raw.get(k) for k in ('contract','revision','build','build_metadata','isa')})
                    if basis is not None:
                        a['report']['basis'] = basis
                    else:
                        a['report']['detail'] = raw['stopped']
                else:
                    a['report'] = raw
                if a['report']['digest'] != c['digest']:
                    raise ValueError('runner changed input identity')
            else:
                a['stdout'] = stem.with_suffix('.stdout').read_text()
            enforce_peak(a)
            cohort['attempts'].append(a)
            write(args.output, cohort)
            print(c['field'], c['name'], engine, stop or a.get('report', {}).get('status', 'runner-failure'), flush=True)
            verify_bases([x for x in cohort['attempts'] if (x['field'], x['name']) == (c['field'], c['name'])])
            if a.get('report', {}).get('status') == 'failed':
                raise RuntimeError('solver failure retained for diagnosis')
            if process.returncode and not stop:
                raise RuntimeError('unexpected runner failure; retained for diagnosis')
    summary(cohort, ROOT / 'research/wide-corpus/BOARD.md')


if __name__ == '__main__':
    main()
