"""§8.1–§8.3, §8.5 and §9: judge H1–H6 on the held-out cohort, report both cohorts, fill the decision table.

Usage: python3 -I summarize.py --records <records.jsonl.gz ...> --limits limits.json --limits-sha <posted sha>
                               [--throughput throughput.json] --out tables.md
Refuses a limits.json whose SHA-256 is not the one posted (§8.5) and cohorts that are not disjoint (§3).
"""
import argparse
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import calib  # noqa: E402
import bench_stats as bs  # noqa: E402
from extract import read  # noqa: E402
from fit_limits import idle_ratios  # noqa: E402

CELLS = {c.name: c for c in calib.CELLS}
REAL_AB = {('H-S16', 'distinct', 'every'), ('H-P1', 'distinct', 'every'), ('C-P16', 'distinct', 'every')}
H5_ROLE = {'a': 'a', 'distinct': 'distinct', 'entry': 'entry'}  # §6 H5: arm a (or entry, or distinct)
LOADED = [w for w in calib.WORKLOADS if w not in calib.DROPPED]
CLASS = {'W4-8': 'W4', 'W4-16': 'W4', 'W4-32': 'W4'}


def fmt(x, d=4):
    return '—' if x is None else f'{x:.{d}f}'


def attempts(recs, rs, refs, rule):
    base = calib.select(recs, 'raw' if rs == 'candidate' else rs, refs)
    if rs == 'candidate':
        base = [r for r in base if not (r.get('signals') and calib.apply_rule(rule, r['signals']))]
    return base


def walls(recs):
    out = defaultdict(dict)  # (session, slot, workload, cell, role) -> rep -> wall
    for r in recs:
        out[(r['session'], r['slot'], r['workload'], r['cell'], r['role'])][r['rep']] = r['wall_s']
    return out


def slots(recs):
    return sorted({(r['session'], r['slot'], r['workload']) for r in recs})


def censored(raw_recs):
    return {(r['session'], r['slot'], r['cell']) for r in raw_recs if r['status'] in ('timeout', 'killed', 'censored')}


def judge(recs, rs, refs, rule, cohort):
    """Every unit of every hypothesis for one cohort under one rule set: list of dicts."""
    sel = attempts(recs, rs, refs, rule)
    prs = calib.pairs(sel, rule=rule if rs == 'candidate' else None)
    idle_pairs = idle_ratios(prs)
    w = walls(sel)
    cens = censored(recs)
    units = []
    by_pair = defaultdict(dict)
    for p in prs:
        by_pair[(p['session'], p['slot'], p['workload'], p['cell'], p['num'], p['den'])][p['rep']] = p['ratio']
    sessions = sorted({r['session'] for r in recs})
    for s in sessions:
        for (_s, slot, wl) in [x for x in slots(recs) if x[0] == s]:
            loaded = wl != 'W0'
            for c in (x for x in calib.CELLS if x.cohort == cohort):
                cen = (s, slot, c.name) in cens
                for num, den in calib.pair_roles(c):
                    ratios = by_pair.get((s, slot, wl, c.name, num, den), {})
                    idle = idle_pairs.get((s, c.name, num, den), [])
                    if len(ratios) < 2 or len(idle) < 2:
                        units.append(dict(h='H1' if num in calib.AA.values() else 'H2', session=s, slot=slot,
                                          workload=wl, cell=c.name, ok=False, why=['too few pairs'], value=None))
                        continue
                    ci = bs.paired_ratio(list(ratios.values()), seed=f'{s} {wl} {slot} {c.name} {num}/{den}')
                    if num in calib.AA.values():
                        ici = bs.paired_ratio(idle, seed=f'{s} idle {c.name} {num}/{den}')
                        g = calib.aa_gate(ci, c.workers, idle=ici if loaded else None)
                        units.append(dict(h='H1', session=s, slot=slot, workload=wl, cell=c.name, ok=g.ok and not cen,
                                          why=g.why + (['censored'] if cen else []), value=ci, n=ci.n))
                    elif loaded:
                        g = calib.ab_gate(idle, list(ratios.values()), f'{s} {wl} {c.name} {num}/{den}')
                        units.append(dict(h='H2', session=s, slot=slot, workload=wl, cell=c.name, pair=f'{num}/{den}',
                                          real=(c.name, num, den) in REAL_AB, ok=g.ok and not cen, why=g.why,
                                          value=ci, idle=statistics.median(idle),
                                          detected_idle=calib.detected(bs.paired_ratio(idle, seed=f'{s} det {c.name}')),
                                          detected_loaded=calib.detected(ci)))
                if not loaded:
                    continue
                if any(r in calib.CROSS for r in c.roles):
                    comp = next(r for r in c.roles if r in calib.CROSS)
                    zi, ci_ = w.get((s, 0, 'W0', c.name, 'entry'), {}), w.get((s, 0, 'W0', c.name, comp), {})
                    zl, cl = w.get((s, slot, wl, c.name, 'entry'), {}), w.get((s, slot, wl, c.name, comp), {})
                    if zi and ci_ and zl and cl:
                        ri = bs.independent_ratio(list(zi.values()), list(ci_.values()), seed=f'{s} idle {c.name} x')
                        rl = bs.independent_ratio(list(zl.values()), list(cl.values()), seed=f'{s} {wl} {c.name} x')
                        g = calib.cross_gate(ri.median, rl.median)
                        units.append(dict(h='H4', session=s, slot=slot, workload=wl, cell=c.name, ok=g.ok and not cen,
                                          why=g.why, value=rl, idle=ri.median))
                    else:
                        units.append(dict(h='H4', session=s, slot=slot, workload=wl, cell=c.name, ok=False,
                                          why=['no samples'], value=None))
                base = H5_ROLE[next(r for r in c.roles if r in calib.AA)]
                wi, wl_ = w.get((s, 0, 'W0', c.name, base), {}), w.get((s, slot, wl, c.name, base), {})
                g = calib.abs_gate(list(wi.values()), list(wl_.values()))
                units.append(dict(h='H5', session=s, slot=slot, workload=wl, cell=c.name, ok=g.ok and not cen,
                                  why=g.why, value=statistics.median(wl_.values()) / statistics.median(wi.values())
                                  if wi and wl_ else None))
    # H3 (§6): of loaded sessions where the real small pair was detected idle, >= 90% also detect it loaded
    small = 'H-S16' if cohort == 'held-out' else 'C-P16'
    for wl in LOADED:
        rows = [u for u in units if u['h'] == 'H2' and u['cell'] == small and u['workload'] == wl and u.get('real')]
        eligible = [u for u in rows if u['detected_idle']]
        frac = sum(u['detected_loaded'] for u in eligible) / len(eligible) if eligible else None
        units.append(dict(h='H3', session='pooled', slot=None, workload=wl, cell=small, ok=frac is not None and frac >= 0.9,
                          why=[] if frac is not None and frac >= 0.9 else [f'detected in {frac} of idle-detected sessions'],
                          value=frac))
    return units


def h6(recs, refs, rule, cohort):
    prs = calib.pairs(calib.select([r for r in recs if r['cohort'] == cohort], 'raw', refs))
    idle = idle_ratios(prs)
    out = {}
    for wl in LOADED:
        rows = [(calib.apply_rule(rule, p['signals']), calib.moved(p['ratio'], idle[(p['session'], p['cell'], p['num'], p['den'])]))
                for p in prs if p['workload'] == wl and p['signals'] and idle.get((p['session'], p['cell'], p['num'], p['den']))]
        out[wl] = calib.h6_score([f for f, _ in rows], [m for _, m in rows]) if rows else None
    return out


def workload_pass(units, hyps, wl):
    rel = [u for u in units if u['h'] in hyps and u['workload'] == wl and
           (u['h'] != 'H2' or u.get('real'))]  # H2 on held-out judges the real pairs (§4.2, amended)
    return bool(rel) and all(u['ok'] for u in rel)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--records', nargs='+', type=Path, required=True)
    ap.add_argument('--limits', type=Path, required=True)
    ap.add_argument('--limits-sha', required=True)
    ap.add_argument('--throughput', type=Path)
    ap.add_argument('--out', type=Path, required=True)
    a = ap.parse_args()
    calib.check_disjoint(calib.CELLS)
    if calib.sha(a.limits) != a.limits_sha:
        raise SystemExit(f'{a.limits}: SHA-256 {calib.sha(a.limits)} is not the posted {a.limits_sha} (§8.5)')
    limits = json.loads(a.limits.read_text())
    rule = dict(signals=limits['rule'])
    refs = json.loads((HERE / 'references.json').read_text())
    recs = read(a.records)
    L = [f'# #1107 concurrent-benchmark calibration: tables\n',
         f'`C` = `{calib.C}`. limits.json SHA-256 `{a.limits_sha}`, rule {limits["rule"]} (J = {limits["j"]:.3f}, '
         f'fitted on {limits["pairs"]} calibration pairs). Sessions: {", ".join(sorted({r["session"] for r in recs}))}. '
         f'Attempts: {len(recs)}.\n']
    results = {}
    for cohort in ('held-out', 'calibration'):
        cr = [r for r in recs if r['cohort'] == cohort]
        results[cohort] = {rs: judge(cr, rs, refs, rule, cohort) for rs in calib.RULE_SETS}
    ho = results['held-out']
    # §9 decision table, held-out cohort
    L += ['## Decision table (§9, held-out cohort)\n', '| Workload | 1. Correctness | 2. Dev A/B (H1, H2, H3) | '
          '3. Cross-engine (H1, H4) | 4. Publication absolute (H5) |', '|---|---|---|---|---|']
    decision = {}
    for wl in ['W0'] + LOADED:
        row = {}
        for cls, hyps in (('2', ('H1', 'H2', 'H3')), ('3', ('H1', 'H4')), ('4', ('H5',))):
            if wl == 'W0':
                row[cls] = 'reference' if cls != '2' else ('allowed' if workload_pass(ho['raw'], ('H1',), 'W0') else 'instrument failure')
                continue
            row[cls] = calib.decide({rs: workload_pass(ho[rs], hyps, wl) for rs in calib.RULE_SETS})
        decision[wl] = row
        L.append(f'| {wl} | allowed | {row["2"]} | {row["3"]} | {row["4"]} |')
    L.append('| W6 I/O | allowed | not calibrated (dropped, owner 2026-11-25) | not calibrated | not calibrated |')
    beyond = [wl for wl in LOADED if decision[wl]['2'] == 'allowed']
    narrow = [wl for wl in LOADED if decision[wl]['2'] == 'allowed under rule set candidate']
    go = ('**Go**: ' + ', '.join(beyond) + ' allowed for dev A/B on held-out data' if beyond else
          '**Narrow go**: dev A/B only under the telemetry limit, for ' + ', '.join(narrow) if narrow else
          '**No-go**: no workload beyond W0 is allowed for dev A/B on held-out data')
    L += ['', f'Go/no-go for #1108: {go}.\n']
    # hypothesis tables
    for cohort in ('held-out', 'calibration'):
        for rs in calib.RULE_SETS:
            us = results[cohort][rs]
            L += [f'## {cohort}, rule set `{rs}`\n', '| H | session | workload | cell | pair | value | idle | pass | why |',
                  '|---|---|---|---|---|---|---|---|---|']
            for u in sorted(us, key=lambda u: (u['h'], str(u['session']), str(u['slot']), u['cell'])):
                v = u['value']
                vs = (f'{v.median:.4f} [{v.lo:.4f}, {v.hi:.4f}]' if hasattr(v, 'median') else fmt(v))
                L.append(f"| {u['h']} | {u['session']} | {u['workload']} | {u['cell']} | {u.get('pair', '')} | {vs} | "
                         f"{fmt(u.get('idle'))} | {'yes' if u['ok'] else '**no**'} | {'; '.join(u['why'])} |")
            L.append('')
    # H6, contamination rates, drift, rank changes
    L += ['## H6: the frozen limit on each cohort (recall ≥ 0.9, false-flag ≤ 0.2)\n',
          '| cohort | workload | moved | flagged | recall | false-flag | pass |', '|---|---|---:|---:|---:|---:|---|']
    for cohort in ('held-out', 'calibration'):
        for wl, sc in h6(recs, refs, rule, cohort).items():
            if sc:
                L.append(f"| {cohort} | {wl} | {sc['moved']} | {sc['flagged']} | {fmt(sc['recall'], 3)} | "
                         f"{fmt(sc['false_flag'], 3)} | {'yes' if sc['ok'] else '**no**'} |")
    L += ['\n## Rejection rate per rule set (share of raw attempts dropped)\n',
          '| cohort | workload | raw attempts | dev | publication | candidate |', '|---|---|---:|---:|---:|---:|']
    for cohort in ('held-out', 'calibration'):
        for wl in ['W0'] + LOADED:
            raw = [r for r in calib.select(recs, 'raw', refs) if r['cohort'] == cohort and r['workload'] == wl]
            if not raw:
                continue
            rate = {rs: 1 - len([r for r in attempts(raw, rs, refs, rule)]) / len(raw) for rs in ('dev', 'publication', 'candidate')}
            L.append(f"| {cohort} | {wl} | {len(raw)} | {rate['dev']:.3f} | {rate['publication']:.3f} | {rate['candidate']:.3f} |")
    L += ['\n## Within-session drift of the A/A ratio (first third ÷ last third) and rank changes\n',
          '| cohort | session | workload | cell | A/A drift | rank changed (A/B pairs) |', '|---|---|---|---|---:|---|']
    prs = calib.pairs(calib.select(recs, 'raw', refs))
    by = defaultdict(dict)
    for p in prs:
        by[(p['cohort'], p['session'], p['slot'], p['workload'], p['cell'], p['num'], p['den'])][p['rep']] = p['ratio']
    idle_med = {(k[1], k[4], k[5], k[6]): statistics.median(v.values()) for k, v in by.items() if k[3] == 'W0' and k[2] == 0}
    for k, v in sorted(by.items(), key=lambda kv: tuple(map(str, kv[0]))):
        if k[5] not in calib.AA.values() or len(v) < 3:
            continue
        ranks = [f'{n}/{d}' for (co, se, sl, wl, ce, n, d), vv in by.items()
                 if (co, se, sl, wl, ce) == k[:5] and n not in calib.AA.values() and len(vv) >= 2
                 and (statistics.median(vv.values()) - 1) * (idle_med.get((se, ce, n, d), 1) - 1) < 0]
        L.append(f'| {k[0]} | {k[1]} | {k[3]}{"" if k[3] != "W0" else f" (slot {k[2]})"} | {k[4]} | '
                 f'{calib.drift(v):.4f} | {", ".join(ranks) or "none"} |')
    if a.throughput and a.throughput.exists():
        t = json.loads(a.throughput.read_text())
        L += ['\n## Development throughput (§8.3)\n', f"Reference build wall with a calibration job under W0 ÷ "
              f"without: **{t['ratio']:.3f}** (median of {t['n']} each; {t['note']}).\n"]
    a.out.write_text('\n'.join(L) + '\n')
    print(f'{a.out}: {go}')


if __name__ == '__main__':
    main()
