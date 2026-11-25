"""#1107: the signed #1106 protocol as code. Cells, manifests, gates (§6) and the H6 fit (§8.4).

Everything here is fixed by docs/research/concurrent-benchmark-calibration-protocol.md as signed on
2026-11-25; a change here after deciding data is a new analysis (§8.5), not a correction.
"""
import hashlib
import json
import random
import statistics
import sys
import time
from collections import namedtuple
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(REPO / 'tools'))
import bench_stats as bs  # noqa: E402

C = '5451e9f853c8f24bafed6875218a175de441e3f0'
W = Path('/buildcache/cargo-target/zeebra-1107')
SIGNED = {  # sign-off package item 2 (#1106); comparands from research/m33-baseline/pins.json
    'sig_f4_study': '6ffc1e8819d82327f5c01286c0e607370b8e59827d0b2ecd26a0f52a469c0bc2',
    'm29_cost_model': 'cb2c17ce7611a3cf8f1524336e5b1d9047f5b3c4ef20d7ccee000cc00ea04576',
    'sweep': '7b48f39b3b1bbe430adeea99ca203aa9ba0f9e9515ec8b3b3bd6a29912d5329f',
    'stream': 'bc0bf4ac66866fff1511b38fa26fe9115c6898a7a7d7773694299c2b423a9682',
    'grobx-driver': 'fdd6aeecac466d3702f1e459f1e1456b72f5444d3563f193b5693df44ce183bc',
    'msolve': '557470de2e13aaa214fd6380600b3fedadc05c2ed203f6afa29a8b172abb6c8d',
}
M5 = dict(passes=13, threads=1, mib=32)  # §4.2, tuned in the pilot on C-E1
N = 30  # §7.2
WORKLOADS = ['W1', 'W2', 'W3', 'W4-8', 'W4-16', 'W4-32', 'W5', 'W6']
DROPPED = {'W6'}  # optional (§2); dropped by the owner for the budget, 2026-11-25
HEAVY = {'W2', 'W4-32', 'W5'}  # #1107: announced, <= 45 min, never beside a queued or held M34 job

Cell = namedtuple('Cell', 'name cohort instance workers roles family scale')
SIG_ROLES, M29_ROLES = ('a', 'a2', 's5'), ('every', 'distinct', 'distinct2')
CELLS = [
    Cell('C-E1', 'calibration', 'wide64/eco-12', 1, SIG_ROLES + ('m5',), 'eco', 12),
    Cell('C-M1', 'calibration', 'gf32003/mq-random-10', 1, SIG_ROLES, 'random-mq', 10),
    Cell('C-M16', 'calibration', 'gf32003/mq-random-10', 16, SIG_ROLES, 'random-mq', 10),
    Cell('C-P16', 'calibration', 'mq10-32003', 16, M29_ROLES, 'random-mq', 10),
    Cell('H-K16', 'held-out', 'gf32003/katsura-11', 16, SIG_ROLES, 'katsura', 11),
    Cell('H-D16', 'held-out', 'gf31/mq-dense-15-s15', 16, SIG_ROLES, 'dense-mq', 15),
    Cell('H-C1', 'held-out', 'wide64/cyclic-7', 1, SIG_ROLES, 'cyclic', 7),
    Cell('H-P1', 'held-out', 'katsura11-m31', 1, M29_ROLES, 'katsura', 11),
    Cell('H-S16', 'held-out', 'cyclic7-wide64', 16, M29_ROLES, 'cyclic', 7),
    Cell('X-G1', 'held-out', 'wide64/katsura-11', 1, ('entry', 'entry2', 'grobx'), 'katsura', 11),
    Cell('X-M16', 'held-out', 'gf32003/katsura-11', 16, ('entry', 'entry2', 'msolve'), 'katsura', 11),
]
GENERATED = {'gf31/mq-dense-15-s15'}
INPUTS = {'wide64/katsura-11': 'grobx', 'gf32003/katsura-11': 'ms'}  # instance -> comparand input key
# (A, B) per cell for the A/A pair and for the A/B pair: ratio = B / A
AA = {'a': 'a2', 'every': 'distinct2', 'entry': 'entry2'}
AB_ROLES = {'s5': 'a', 'm5': 'a', 'distinct': 'every'}  # A/B: role / base
CROSS = {'grobx': 'entry', 'msolve': 'entry'}  # H4: entry / comparand, as Zeebra ÷ competitor


def arm_name(cell, role):
    return f'{cell.name}.{role}'


def check_disjoint(cells):
    """§3.2: the cohorts share no family and no scale."""
    by = {k: {getattr(c, k) for c in cells if c.cohort == 'calibration'} for k in ('family', 'scale')}
    for c in cells:
        if c.cohort != 'held-out':
            continue
        for k in ('family', 'scale'):
            if getattr(c, k) in by[k]:
                raise ValueError(f'{c.name}: {k} {getattr(c, k)} is also in the calibration cohort')


def session_order(seed):
    """§5.4's shuffle of all eight loaded workloads, then the dropped ones removed, between two W0s."""
    w = list(WORKLOADS)
    random.Random(seed).shuffle(w)
    return ['W0'] + [x for x in w if x not in DROPPED] + ['W0']


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class Paths:
    """The campaign's binaries and inputs. `fake()` stands in for tests: no file is read."""

    def __init__(self, w, shas=None):
        self.w = Path(w)
        b = self.w / 'bin'
        self.bin = dict(sig=b / 'sig_f4_study', m29=b / 'm29_cost_model', s5=b / 's5.sh', m5=b / 'm5.sh',
                        grobx=b / 'grobx-driver', msolve=b / 'msolve', sweep=b / 'sweep', stream=b / 'stream')
        self._shas = shas

    @classmethod
    def fake(cls):
        p = cls('/nonexistent')
        p._shas = {k: '0' * 64 for k in p.bin}
        return p

    def sha(self, key):
        return self._shas[key] if self._shas else sha(self.bin[key])

    def input(self, instance, key):
        path = self.w / 'inputs' / instance.replace('/', '__') / {'grobx': 'grobx.json', 'ms': 'in.ms'}[key]
        return dict(path=str(path), sha256='0' * 64 if self._shas else sha(path))


SIG_ARGV = ['--field', '{field}', '--name', '{name}', '{flag1}', '--engine', 'entry', '--workers', '{workers}',
            '--digest-only', '--wall-s', '600']
FLAGS = '.cargo/config.toml (x86-64-v3, fat LTO, 1 CGU); RUSTC_WRAPPER="" CARGO_INCREMENTAL=0'
SIG_RECIPE = f'git archive {C} | tar -x; cargo build --release --locked --features research-sigf4 --example sig_f4_study'
M29_RECIPE = f'git archive {C} | tar -x; cargo build --release --locked --features external-runners --example m29_cost_model'
COMPARANDS = {
    'grobx': ('8005a2a1670a7264617a6f49eeb2618d7fa21701', 'grobx 0.155.1 (M33 pin): research/m33-baseline/grobx-pin.sh, pins.json'),
    'msolve': ('b364edcb', 'msolve 0.11.0 release tarball: tools/external/provision.sh, pins.json'),
}


def arm(cell, role, paths):
    commit, recipe, comparand = C, SIG_RECIPE, None
    if role in ('a', 'a2', 'entry', 'entry2'):
        key, argv = 'sig', SIG_ARGV
    elif role == 's5':
        key, argv, recipe = 's5', SIG_ARGV, SIG_RECIPE + '; s5 wrapper sleeps 5% of the wall (#985)'
    elif role == 'm5':
        key, recipe = 'm5', SIG_RECIPE + f'; m5 wrapper + sweep (cc -O2 -pthread research/concurrent-calibration/sweep.c), {M5}'
        argv = [str(M5['passes']), str(M5['threads']), str(M5['mib']), *SIG_ARGV]
    elif role in M29_ROLES:
        key, recipe = 'm29', M29_RECIPE
        argv = ['--target', '{target}', '--workers', '{workers}', '--pair-multiples', role.rstrip('2'), '--wall-s', '600']
    elif role == 'grobx':
        key, argv = 'grobx', ['{inputs[grobx]}']
        commit, recipe = COMPARANDS['grobx']
        comparand = recipe
    elif role == 'msolve':
        key, argv = 'msolve', ['-f', '{inputs[ms]}', '-o', '/dev/stdout', '-t', '{workers}', '-g', '2']
        commit, recipe = COMPARANDS['msolve']
        comparand = recipe
    else:
        raise ValueError(role)
    a = dict(name=arm_name(cell, role), commit=commit, binary=str(paths.bin[key]), sha256=paths.sha(key),
             build=dict(profile='release', flags=FLAGS if not comparand else 'as provisioned (pins.json)',
                        recipe=recipe), argv=argv, workers=[cell.workers], instances=[cell.instance])
    if comparand:
        a['build']['comparand'] = comparand
    return a


def instance(name, paths):
    if '/' in name:
        field, nm = name.split('/')
        inst = dict(name=name, params=dict(field=field, name=nm,
                                           flag1='--generate' if name in GENERATED else '--digest-only'))
    else:
        inst = dict(name=name, params=dict(target=name))
    if name in INPUTS:
        inst['inputs'] = {INPUTS[name]: paths.input(name, INPUTS[name])}
    return inst


def manifest(cohort, workload, session, paths, *, reps=N, agent, policy='fallback (CCDs 1-2)', clock='boost'):
    cells = [c for c in CELLS if c.cohort == cohort]
    names = list(dict.fromkeys(c.instance for c in cells))
    return {'schema': 'bench-job-manifest-v1', 'mode': 'dev',
            'context': dict(issue=1107, cohort=cohort, workload=workload, session=session, agent=agent, commit=C,
                            reservation=policy, clock=clock, n=reps, submitted=time.strftime('%Y-%m-%dT%H:%M:%S%z')),
            'arms': [arm(c, r, paths) for c in cells for r in c.roles],
            'instances': [instance(n, paths) for n in names],
            'run': dict(workers=sorted({c.workers for c in cells}), cpus='8-23', repetitions=reps, interleave='rotate',
                        seeds=[0], retries=0,
                        limits=dict(wall_seconds=600, kill_after_seconds=60, rss_bytes=17179869184, live_bytes=None))}


# §6 gates ---------------------------------------------------------------------------------------
Gate = namedtuple('Gate', 'ok why')


def aa_gate(ci, workers, *, idle=None):
    band = 0.040 if workers >= 16 else 0.025
    why = []
    if abs(ci.median - 1) > 0.010:
        why.append(f'median {ci.median:.4f} outside 1 ± 0.010')
    if ci.lo < 1 - band or ci.hi > 1 + band:
        why.append(f'CI [{ci.lo:.4f}, {ci.hi:.4f}] outside 1 ± {band}')
    if idle is not None and (ci.hi - ci.lo) > 1.5 * (idle.hi - idle.lo):
        why.append(f'loaded CI width {ci.hi - ci.lo:.4f} > 1.5 × idle {idle.hi - idle.lo:.4f}')
    return Gate(not why, why)


def diff_ci(idle, loaded, seed, draws=bs.DRAWS):
    """median(loaded) − median(idle), each side resampled independently (§6, H2)."""
    rng = random.Random(bs._seed(seed))
    ni, nl = len(idle), len(loaded)
    lo, hi = bs._percentiles([statistics.median(rng.choices(loaded, k=nl)) - statistics.median(rng.choices(idle, k=ni))
                              for _ in range(draws)])
    return bs.Interval(statistics.median(loaded) - statistics.median(idle), lo, hi, nl, ni)


def ab_gate(idle, loaded, seed):
    d = diff_ci(idle, loaded, seed)
    mi, ml = statistics.median(idle), statistics.median(loaded)
    why = []
    if abs(d.median) > 0.015:
        why.append(f'shift {d.median:+.4f} beyond ±0.015')
    if d.lo < -0.025 or d.hi > 0.025:
        why.append(f'shift CI [{d.lo:+.4f}, {d.hi:+.4f}] beyond ±0.025')
    if (mi - 1) * (ml - 1) < 0:
        why.append(f'sign changed: idle {mi:.4f}, loaded {ml:.4f}')
    return Gate(not why, why)


def detected(ci):
    return ci.hi < 1 or ci.lo > 1


def cross_gate(idle_ratio, loaded_ratio):
    r = loaded_ratio / idle_ratio - 1
    return Gate(abs(r) <= 0.03, [] if abs(r) <= 0.03 else [f'loaded/idle − 1 = {r:+.4f}'])


def abs_gate(idle_walls, loaded_walls):
    r = statistics.median(loaded_walls) / statistics.median(idle_walls) - 1
    return Gate(abs(r) <= 0.02, [] if abs(r) <= 0.02 else [f'loaded/idle wall − 1 = {r:+.4f}'])


# §8.4 H6 fit -----------------------------------------------------------------------------------
def moved(ratio, idle_ratios):
    lo, hi = bs._percentiles(list(idle_ratios))
    return ratio < lo or ratio > hi


def fit_threshold(values, moved_flags):
    """L maximizing Youden's J for flagging `value > L`; ties to the lower L."""
    pos = sum(moved_flags)
    neg = len(moved_flags) - pos
    best = None
    for lim in sorted(set(values)):
        tp = sum(1 for v, m in zip(values, moved_flags) if m and v > lim)
        fp = sum(1 for v, m in zip(values, moved_flags) if not m and v > lim)
        j = (tp / pos if pos else 0) - (fp / neg if neg else 0)
        if best is None or j > best[1] + 1e-12:
            best = (lim, j)
    return best


def _j(flags, moved_flags):
    pos = sum(moved_flags)
    neg = len(moved_flags) - pos
    tp = sum(1 for f, m in zip(flags, moved_flags) if f and m)
    fp = sum(1 for f, m in zip(flags, moved_flags) if f and not m)
    return (tp / pos if pos else 0) - (fp / neg if neg else 0)


def fit_rule(signals, moved_flags):
    """§8.4: the best single signal, or the OR of the two best if that raises J by >= 0.05."""
    fits = {s: fit_threshold(v, moved_flags) for s, v in signals.items() if all(x is not None for x in v)}
    if not fits:
        return dict(signals={}, j=0.0, eligible=[])
    ranked = sorted(fits, key=lambda s: (-fits[s][1], s))
    best = ranked[0]
    rule = dict(signals={best: fits[best][0]}, j=fits[best][1], eligible=sorted(fits),
                single={s: dict(limit=fits[s][0], j=fits[s][1]) for s in ranked})
    if len(ranked) > 1:
        two = ranked[1]
        flags = [a > fits[best][0] or b > fits[two][0] for a, b in zip(signals[best], signals[two])]
        j2 = _j(flags, moved_flags)
        if j2 >= fits[best][1] + 0.05:
            rule.update(signals={best: fits[best][0], two: fits[two][0]}, j=j2)
    return rule


def apply_rule(rule, values):
    return any(values.get(s) is not None and values[s] > lim for s, lim in rule['signals'].items())


def require_cohort(records, cohort):
    other = {r['cohort'] for r in records} - {cohort}
    if other:
        raise ValueError(f'refusing {", ".join(sorted(other))} records: §8.4 fits on the {cohort} cohort only')


# Extraction -------------------------------------------------------------------------------------
BENCH_CPUS = set(range(8, 24))


def digest(role, stdout, case=None):
    """The basis digest an attempt printed: `basis_m33` (comparable with grobx's and msolve's, via
    research/m33-baseline/admission.py) for sig_f4_study, `basis_sha256` for m29_cost_model."""
    text = stdout.decode(errors='replace') if isinstance(stdout, bytes) else stdout
    if role in ('grobx', 'msolve'):
        sys.path.insert(0, str(REPO / 'research/m33-baseline'))
        import admission
        try:
            return (admission.grobx_digest if role == 'grobx' else admission.msolve_digest)(text, case)
        except ValueError:
            return None
    try:
        r = json.loads(text)
    except ValueError:
        return None
    if r.get('status') != 'complete':
        return None
    return r.get('basis_sha256') if role in M29_ROLES else r.get('basis_m33')


def _cpus(spec):
    out = set()
    for part in spec.split(','):
        lo, _, hi = part.partition('-')
        out |= set(range(int(lo), int(hi or lo) + 1))
    return out


def _avail(v):
    return v is not None and not (isinstance(v, dict) and 'unavailable' in v)


def signals(m):
    """One attempt's §8.4 candidate signals, None where unavailable (and so ineligible)."""
    psi, slice_, vm = m.get('psi'), m.get('psi_bench_slice'), m.get('vmstat')
    ccd = m.get('ccd_load')
    s = dict(bench_foreign=m.get('bench_foreign'),
             sibling_busy_max=max(m['sibling_busy'].values()) if m.get('sibling_busy') else None,
             compilers_on_bench=m.get('compilers_on_bench') if _avail(m.get('compilers_on_bench')) else None,
             runner_workers_on_bench=m.get('runner_workers_on_bench') if _avail(m.get('runner_workers_on_bench')) else None,
             # NPS1: every CCD shares the memory controllers, so the busiest non-bench CCD is both elements
             ccd_load_rest_max=max(v for k, v in ccd.items() if not _cpus(k) & BENCH_CPUS) if _avail(ccd) else None,
             mbm_bytes_per_s=m.get('mbm_bytes_per_s') if _avail(m.get('mbm_bytes_per_s')) else None)
    for name, src in (('psi', psi), ('psi_slice', slice_)):
        for res in ('cpu', 'memory'):
            for kind in ('some', 'full'):
                s[f'{name}_{res}_{kind}'] = (src.get(res) or {}).get(kind) if _avail(src) else None
    ok = _avail(vm)
    s['vmstat_majfault'] = vm.get('pgmajfault') if ok else None
    s['vmstat_reclaim'] = (vm.get('pgscan') or 0) + (vm.get('pgsteal') or 0) if ok else None
    s['vmstat_swap'] = (vm.get('pswpin') or 0) + (vm.get('pswpout') or 0) if ok else None
    return s


def pair_signals(a, b):
    """A pair is flagged when either attempt exceeds L (§8.4): the pair's value is the larger."""
    return {k: (None if a[k] is None or b[k] is None else max(a[k], b[k])) for k in a}


def drift(ratios_by_rep):
    reps = sorted(ratios_by_rep)
    k = len(reps) // 3
    first = statistics.median(ratios_by_rep[r] for r in reps[:k])
    last = statistics.median(ratios_by_rep[r] for r in reps[-k:])
    return first / last


def records(job_dir, w=W):
    """One record per attempt of one job (§8.6 extract): cell, role, rep, wall, digest, status, the
    dev and publication verdicts recomputed with tools/bench_contamination.py, and §8.4's signals."""
    sys.path.insert(0, str(REPO / 'tools/external'))
    import attempt_journal as aj
    import bench_contamination as bc
    state = aj.load(Path(job_dir) / 'journal')
    hdr = state['header']['bench_job']
    ctx, owner = hdr['context'], f"bench-job-{hdr['job_id']}"
    cells = {arm_name(c, r): (c, r) for c in CELLS for r in c.roles}
    cases = {}
    metrics = [(a['metadata'].get('contamination') or {}).get('metrics') for a in state['attempts']]
    judged = [i for i, m in enumerate(metrics) if m]
    groups = [state['attempts'][i]['cell']['workers'] for i in judged]
    verdicts = {mode: dict(zip(judged, bc.session_verdict([metrics[i] for i in judged], mode, groups, owner)['attempts']))
                for mode in ('dev', 'publication')}
    out = []
    for i, a in enumerate(state['attempts']):
        md, cell = a['metadata'], a['cell']
        c, role = cells[cell['arm']]
        case = None
        if role in ('grobx', 'msolve'):
            if c.instance not in cases:
                cases[c.instance] = json.loads((Path(w) / 'inputs' / c.instance.replace('/', '__') / 'case.json').read_text())
            case = cases[c.instance]
        v = {mode: verdicts[mode].get(i) for mode in verdicts}
        out.append(dict(
            cohort=ctx['cohort'], workload=ctx['workload'], session=ctx['session'], job=hdr['job_id'],
            reservation=ctx.get('reservation'), clock=(md.get('before') or {}).get('clock'),
            cell=c.name, role=role, instance=c.instance, workers=cell['workers'], rep=cell['rep'],
            attempt=md['attempt_id'], status=a['status'], exit=md.get('exit'),
            wall_s=md['process_wall_ns'] / 1e9 if md.get('process_wall_ns') else None,
            binary_sha256=md.get('binary_sha256'),
            digest=digest(role, a['stdout'], case) if a['status'] == 'ok' else None,
            dev=None if v['dev'] is None else v['dev']['contaminated'],
            dev_reasons=(v['dev'] or {}).get('reasons'),
            publication=None if v['publication'] is None else v['publication']['contaminated'],
            publication_reasons=(v['publication'] or {}).get('reasons'),
            signals=signals(metrics[i]) if metrics[i] else None))
    return out
