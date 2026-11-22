#!/usr/bin/env python3
"""#975 M33-I: the publication-mode campaign at F3, with F0 rebuilt beside it (plan §§9.10, 11).

    campaign.py inputs --study BIN                         # request files for every row and solver
    campaign.py references --study BIN                     # untimed references, CPUs 24-39 -> references.json
    campaign.py manifest --track G|Gc|M --f3-study BIN --f0-study BIN   # publication manifest on stdout
    campaign.py extract --job DIR --track G|Gc|M           # journal -> records-<track>-<job>.jsonl.gz
    campaign.py retain --job DIR                           # journal -> journals/<job>/
    campaign.py threads --manifest FILE --output FILE      # one census-sampled attempt per arm and cell
    campaign.py board [--append]                           # CompetitiveRecord rows from the records

The machinery is research/m33-baseline/campaign.py's, imported rather than copied: the same rows,
request files, digest parsing, extraction and thread census. What is new here is the arm set (F3 and
F0 side by side), the held-out rows, publication mode, a grobx certified reference job on the Track G
primary, references that keep their basis invariants and time, and the scoreboard adapter.
"""
import argparse
import gzip
import importlib.util
import json
import os
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
_spec = importlib.util.spec_from_file_location('m33_baseline_campaign', ROOT / 'research/m33-baseline/campaign.py')
base = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(base)
base.HERE = HERE  # extract/retain write beside this script
admission, basis_digest = base.admission, base.admission.basis_digest
base.COMPARANDS['grobx155-certified'] = base.COMPARANDS['grobx155']

F0 = base.F0
F0_HARNESS = base.HARNESS  # 9d6f16e4: src/, Cargo.toml and Cargo.lock equal F0's
F2 = 'db181c51'  # measured/974-f2
F3 = 'db181c51'  # = F2: no measured path changed between them (README §1)
HELD_OUT = json.loads((ROOT / 'research/m33-baseline/held-out.json').read_text())
ROWS = {t: dict(base.ROWS[t], **{'held-out': [(h['field'], h['name']) for h in HELD_OUT[t]]}) for t in ('G', 'M')}
ROWS['Gc'] = {'development': [('wide64', 'eco-12')]}
GENERATED = base.GENERATED | {r for t in ('G', 'M') for r in ROWS[t]['held-out']}
base.GENERATED = GENERATED
SETS = ('development', 'control', 'held-out')
CERTIFIED_CAP_S, CERTIFIED_CAP_BYTES = 600, 32 * 2**30  # M31 declared 32 GiB for Eco-12 certified (#855)
REFERENCE_CAP_S = 1800
MODULUS_NAMES = {'wide64': '2⁶⁴−353', 'goldilocks': 'Goldilocks', 'gf32003': 'GF(32003)', 'm31': 'GF(2³¹−1)'}


def rows(track):
    return [r for s in SETS for r in ROWS[track].get(s, [])]


def set_of(track, field, name):
    return next(s for s in SETS if (field, name) in ROWS[track].get(s, []))


def key(field, name):
    return base.key(field, name)


def write_inputs(study, out):
    base.ROWS = {t: {'development': rows(t), 'control': []} for t in ('G', 'M')}
    base.write_inputs(study, out)
    for t in ('G', 'M'):
        for h in HELD_OUT[t]:
            case = json.loads(Path(out, key(h['field'], h['name']), 'case.json').read_text())
            if case['digest'] != h['digest']:
                raise SystemExit(f"{h['field']}/{h['name']} does not reproduce its held-out input digest")
    d = Path(out, key('wide64', 'eco-12'))
    req = json.loads((d / 'grobx.json').read_text())
    (d / 'grobx-certified.json').write_text(json.dumps(certified_request(req)))


def certified_request(req):
    """Track Gc's request: certified, digest-only, since Eco-12's certified texts gzip to 1.7 GB (#1020)."""
    return dict(req, mode='certified', wall_ns=CERTIFIED_CAP_S * 10**9, rss_bytes=CERTIFIED_CAP_BYTES,
                digest_only=True)


def leading(poly, variables):
    """The grevlex leading monomial of a canonical element, rendered as the board writes one."""
    m = max((t for t, _ in poly), key=lambda m: (sum(m), tuple(-e for e in reversed(m))))
    parts = [v if e == 1 else f'{v}^{e}' for v, e in zip(variables, m) if e]
    return '*'.join(parts) or '1'


def invariants(texts, case):
    """Basis cardinality and sorted leading monomials of a reduced basis given as text."""
    p = int(case['modulus'])
    polys = [x for x in (basis_digest.canonical_polynomial(t, p, case['variables']) for t in texts) if x]
    return dict(basis_cardinality=len(polys), leading_monomials=sorted(leading(x, case['variables']) for x in polys))


def references(args):
    """One independent reference per row, untimed for any verdict and run off the bench CPUs: Singular
    std/redSB below 2³¹, groebner-rs at one worker on wide fields (plan §5.2.5). Each keeps its wall
    (the verification time, reported separately, §11.6) and the basis invariants the scoreboard
    rows carry. A digest that disagrees with the M33-0 reference stops the command."""
    os.environ.setdefault('M33_ADMISSION_CPUS', '24-39')
    admission.CPUS = os.environ['M33_ADMISSION_CPUS']
    prior = json.loads((ROOT / 'research/m33-baseline/references.json').read_text())
    prior.update({key(h['field'], h['name']): dict(basis_m33=h['basis_m33']) for t in HELD_OUT for h in HELD_OUT[t]})
    path = HERE / 'references.json'
    refs = json.loads(path.read_text()) if path.exists() else {}
    for track in ('G', 'M'):
        for field, name in rows(track):
            k = key(field, name)
            if k in refs:
                continue
            case = json.loads(Path(args.inputs, k, 'case.json').read_text())
            if track == 'M':
                r, ok, digest = admission.singular(case, REFERENCE_CAP_S)
                texts, ref = [t for t in r['stdout'].splitlines() if t.strip()], 'Singular std, redSB'
            else:
                req = Path(args.inputs, k, 'groebner-rs.json')
                r = admission.guarded([args.groebner_rs, str(req)], REFERENCE_CAP_S)
                texts = (json.loads(r['stdout']) if r['rc'] == 0 and r['stdout'].strip() else {}).get('basis') or []
                ok = bool(texts)
                digest = basis_digest.basis_digest(texts, int(case['modulus']), case['variables']) if ok else None
                ref = 'groebner-rs, 1 worker'
            want = prior.get(k, {}).get('basis_m33')
            if ok and want and digest != want:
                raise SystemExit(f'{k}: reference {digest} disagrees with M33-0 {want}')
            refs[k] = dict(reference=ref, input_digest=case['digest'], basis_m33=digest if ok else None,
                           m33_0_agrees=bool(ok and digest == want), wall_ms=round(r['wall_ns'] / 1e6, 1),
                           peak_rss_bytes=r['peak'], cpus=admission.CPUS,
                           invariants=invariants(texts, case) if ok else None)
            print(field, name, ref, (digest or 'FAILED')[:12], f"{r['wall_ns'] / 1e9:.1f} s", flush=True)
            path.write_text(json.dumps(refs, indent=1, sort_keys=True) + '\n')


def zeebra_arm(name, study, engine, commit, workers, version):
    tree = F3 if version == 'F3' else F0_HARNESS
    arm = base.zeebra_arm(name, study, engine, workers)
    arm['commit'] = tree
    arm['build']['recipe'] = (f'git archive {tree} | tar -x; cargo build --release --features research-sigf4 '
                              f'--example sig_f4_study' + ('' if version == 'F3' else
                                                           f' (src/, Cargo.toml, Cargo.lock identical to F0 {F0[:8]})'))
    arm['library'] = 'zeebra'
    arm['library_version'] = f'zeebra {version} {commit[:8]} sig_f4_study --engine {engine}'
    return arm


def manifest(args):
    t = args.track
    z = []
    for version, study, commit in (('F3', args.f3_study, F3), ('F0', args.f0_study, F0)):
        sfx = '' if version == 'F3' else '-f0'
        if t == 'G':
            z += [zeebra_arm('sigf4' + sfx, study, 'sigf4', commit, [1], version),
                  zeebra_arm('entry' + sfx, study, 'entry', commit, [1], version),
                  zeebra_arm('entry16' + sfx, study, 'entry', commit, [16], version)]
        elif t == 'M':
            z.append(zeebra_arm('entry' + sfx, study, 'entry', commit, None, version))
    if t == 'G':
        arms = z + [base.comparand_arm('grobx155', args.grobx155, ['{inputs[grobx]}'], [1]),
                    base.comparand_arm('groebner-rs', args.groebner_rs, ['{inputs[groebner_rs]}'], [1])]
        arms[-2].update(library='grobx', library_version='grobx 0.155.1 (raw, randomized, uncertified)')
        arms[-1].update(library='groebner-rs', library_version='groebner-rs driver c3e1d630 (verified)')
    elif t == 'Gc':
        arms = [base.comparand_arm('grobx155-certified', args.grobx155, ['{inputs[grobx_certified]}'], [1])]
        arms[0].update(library='grobx-certified', library_version='grobx 0.155.1 (certified)')
    else:
        arms = z + [base.comparand_arm('msolve', args.msolve, ['-f', '{inputs[ms]}', '-o', '/dev/stdout', '-t',
                                                               '{workers}', '-g', '2'])]
        arms[-1].update(library='msolve', library_version='msolve 0.11.0')
    files = dict(M=dict(ms='in.ms'), G=dict(grobx='grobx.json', groebner_rs='groebner-rs.json'),
                 Gc=dict(grobx_certified='grobx-certified.json'))[t]
    instances = []
    for field, name in rows(t):
        if args.rows and key(field, name) not in args.rows:
            continue
        d = Path(args.inputs, key(field, name))
        instances.append(dict(
            name=f'{field}/{name}',
            params=dict(field=field, name=name, generate='--generate' if (field, name) in GENERATED else '--digest-only'),
            inputs={k: dict(path=str(d / f), sha256=base.sha(d / f)) for k, f in files.items()}))
    workers = dict(G=[1, 16], Gc=[1], M=[1, 4, 8, 16])[t]
    cap_s, cap_b = (CERTIFIED_CAP_S, CERTIFIED_CAP_BYTES) if t == 'Gc' else (base.CAP_S, base.CAP_BYTES)
    return dict(schema='bench-job-manifest-v1', mode='publication',
                context=dict(issue=975, agent=args.agent, track=t, session=args.session),
                arms=arms, instances=instances,
                run=dict(workers=workers, cpus='8-23', repetitions=args.reps, interleave='rotate', seeds=[0],
                         retries=0, mode_wait_seconds=args.mode_wait,
                         limits=dict(wall_seconds=cap_s, kill_after_seconds=30, rss_bytes=cap_b, live_bytes=None)))


def _digest_of(arm, stdout, case):
    if arm == 'grobx155-certified':
        try:
            return admission.grobx_digest(stdout.decode(errors='replace'), case, 'certified')
        except ValueError:
            return None
    return _base_digest_of(arm, stdout, case)


_base_digest_of = base._digest_of
base._digest_of = _digest_of


# ------------------------------------------------------------------------------------------------
# Scoreboard: CompetitiveRecord rows (src/grobner/external/board.rs) from the retained records.
# ------------------------------------------------------------------------------------------------

LIBRARY = {'grobx155': ('grobx', 'grobx 0.155.1 (raw, randomized, uncertified)'),
           'grobx155-certified': ('grobx-certified', 'grobx 0.155.1 (certified)'),
           'groebner-rs': ('groebner-rs', 'groebner-rs driver c3e1d630 (verified)'),
           'msolve': ('msolve', 'msolve 0.11.0')}
# The arm each competitor row pairs with on the board: Track G scores the signature route at 1 w and
# Track M the default dispatch (as M33-0 did); every other Zeebra arm gets its own policy.
SCORED = {'G': 'sigf4', 'Gc': 'sigf4', 'M': 'entry'}


def field_block(case, field):
    p = int(case['modulus'])
    return dict(name=f'GF({p})', characteristic=p, extension_degree=1, defining_polynomial=None)


def board_rows(recs, refs, cases, sessions):
    out = []
    cells = sorted({(r['track'], r['field'], r['name'], r['arm'], r['workers']) for r in recs})
    for track, field, name, arm, w in cells:
        rs = [r for r in recs if (r['track'], r['field'], r['name'], r['arm'], r['workers'])
              == (track, field, name, arm, w)]
        clean = [r for r in rs if r['status'] == 'ok' and not r['contaminated']]
        case, ref = cases[key(field, name)], refs.get(key(field, name), {})
        zeebra = arm.split('-')[0] in ('sigf4', 'entry', 'entry16')
        version = 'F0' if arm.endswith('-f0') else 'F3'
        commit = (F0 if version == 'F0' else F3)[:8]
        lib, libv = ('zeebra', f"zeebra {version} {commit} sig_f4_study --engine {arm.split('-')[0].rstrip('16')}") \
            if zeebra else LIBRARY[arm]
        scored = arm in (SCORED[track],) or not zeebra
        label = 'G' if track == 'Gc' else track
        policy = (f'#975 publication session, Track {label}: median process wall of the clean, reference-verified '
                  'attempts, arms interleaved, one solve per fresh process') + ('' if scored else f' ({arm} arm)')
        caps = (CERTIFIED_CAP_S, CERTIFIED_CAP_BYTES) if track == 'Gc' else (base.CAP_S, base.CAP_BYTES)
        # Every measured commit is an ancestor of main, so it is its own resolvable base.
        stamp = commit if zeebra else F3[:8]
        row = dict(schema=1, problem=name, problem_digest=case['digest'],
                   family=name.rsplit('-', 1)[0] if not name.startswith('mq-random') else 'mq-random',
                   task='reduced-grobner-basis', field=field_block(case, field), order='grevlex',
                   variable_count=len(case['variables']), library=lib, library_version=libv,
                   environment=dict(commit=stamp, base_commit=stamp, patch_id='',
                                    machine='fedora', cpu=f"AMD Ryzen Threadripper PRO 5995WX 64-Cores, affinity "
                                                          f"{'8' if w == 1 else f'8-{7 + w}'}",
                                    concurrency=w, build='release, rustc 1.99.1 (fat LTO, x86-64-v3)' if zeebra
                                    else 'as provisioned (research/m33-baseline/pins.json)',
                                    policy=policy),
                   limits=dict(wall_nanos=caps[0] * 10**9, workers=w, max_rss_bytes=caps[1], tool_caps=[]))
        good = [r for r in clean if ref.get('basis_m33') and r['basis_m33'] == ref['basis_m33']]
        if not good:
            why = 'no clean complete attempt' if not clean else 'no attempt matched the independent reference'
            row.update(outcome='failed', outcome_detail=why)
        else:
            row.update(outcome='complete', invariants=ref['invariants'],
                       wall_nanos=round(statistics.median(r['wall_ns'] for r in good)),
                       cpu_basis='unavailable',
                       peak_rss_bytes=round(statistics.median(r['peak_rss_bytes'] for r in good)),
                       peak_rss_basis='wait4 ru_maxrss of the guarded child tree (an upper bound, #990)',
                       verification=dict(checked_against=ref['reference'], shared_invariants=2,
                                         note=f"m33-basis-v1 equal on {len(good)}/{len(clean)} clean attempts; "
                                              f"invariants are the reference basis's"))
        jobs = sorted({r['job'] for r in rs})
        row['reproduce'] = ('research/m33-final/campaign.py board; jobs ' + ', '.join(jobs) + ' pooled')
        out.append(row)
    return out


def board(args):
    recs, sessions = [], {}
    for path in sorted(HERE.glob('records-*.jsonl.gz')):
        recs += [json.loads(x) for x in gzip.decompress(path.read_bytes()).decode().splitlines()]
        s = json.loads(Path(str(path).replace('.jsonl.gz', '.session.json')).read_text())
        sessions[s['job']['job_id']] = f"{s['job']['context']['track']}/{s['job']['context'].get('session')}"
    of_record = json.loads((HERE / 'sessions.json').read_text())['of_record']
    recs = [r for r in recs if r['job'] in of_record]
    refs = json.loads((HERE / 'references.json').read_text())
    cases = {key(f, n): json.loads(Path(args.inputs, key(f, n), 'case.json').read_text())
             for t in ('G', 'M') for f, n in rows(t)}
    out = board_rows(recs, refs, cases, sessions)
    if args.append:
        hist = ROOT / 'research/competitive/results/history.json'
        h = json.loads(hist.read_text())
        if any('#975 publication session' in r['environment'].get('policy', '') for r in h['rows']):
            raise SystemExit('history.json already holds #975 rows (append-only: not appended twice)')
        h['rows'] += out
        h['row_count'] = len(h['rows'])
        hist.write_text(json.dumps(h, indent=2, ensure_ascii=False) + '\n')
    print(len(out), 'rows')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=('inputs', 'references', 'manifest', 'extract', 'retain', 'threads', 'board'))
    p.add_argument('--study')
    p.add_argument('--f3-study')
    p.add_argument('--f0-study')
    p.add_argument('--inputs', default='/buildcache/cargo-target/zeebra-975/inputs')
    p.add_argument('--track', choices=('G', 'Gc', 'M'))
    p.add_argument('--grobx155', default='/buildcache/cargo-target/zeebra-grobx-8005a2a1/release/grobx-driver')
    p.add_argument('--groebner-rs', default='/buildcache/cargo-target/zeebra-groebner-rs/release/groebner-rs-driver')
    p.add_argument('--msolve', default=str(Path.home() / '.local/opt/zeebra-ext/bin/msolve'))
    p.add_argument('--agent', default='')
    p.add_argument('--session', default='final')
    p.add_argument('--reps', type=int, default=9)
    p.add_argument('--mode-wait', type=int, default=1800)
    p.add_argument('--rows', nargs='*', help='field__name keys (the predeclared n = 12 extension)')
    p.add_argument('--job', type=Path)
    p.add_argument('--manifest')
    p.add_argument('--output', type=Path)
    p.add_argument('--append', action='store_true')
    args = p.parse_args()
    if args.command == 'inputs':
        write_inputs(args.study, args.inputs)
    elif args.command == 'references':
        references(args)
    elif args.command == 'manifest':
        print(json.dumps(manifest(args), indent=1))
    elif args.command == 'extract':
        base.extract(args)
    elif args.command == 'retain':
        base.retain(args)
    elif args.command == 'threads':
        base.threads(args)
    else:
        board(args)


if __name__ == '__main__':
    main()
