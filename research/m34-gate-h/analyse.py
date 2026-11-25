#!/usr/bin/env python3
"""#1012 Gate H read, exactly as declared on #1012 (2026-11-22) and refined by J1-J8 before any cell ran.

    analyse.py [--draws 20000] [--json results/gate-h.json] [--markdown results/gate-h.md]

Inputs: `results/attempts.jsonl` (collected selection records), `results/features.jsonl` (#1009's set
cost per record), `s0/cohorts.json` (development records only) and the panels' `references.json`.

Definitions (plan §9, §9.1):
- A cell is one record under one configuration; its cost is the median over its repetitions of the
  per-attempt charged wall, where every attempt that is not a verified completion costs k·C
  (PAR-2 decides; PAR-10 is a sensitivity view). cost(π, x) is the geometric mean over x's field
  variants.
- VBS⁺(record) = the cheapest cell over the arm set + the record's feature cost; per problem, the
  geometric mean over field variants.
- BF is chosen leave-one-family-out: problems of family F are scored against the arm minimizing the
  aggregate over every other family.
- Aggregate: family-weighted geometric mean (families equal, problems equal within a family).
- H = aggregate of cost(VBS⁺, x) ÷ cost(BF, x).
"""
import argparse
import json
import math
import random
import statistics
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign  # noqa: E402

C_MS = campaign.CAP_S * 1e3
CONTEXTS = {
    'W16': tuple(campaign.CONFIGS),
    'W1': ('P1', 'P4', 'P7-w1', 'P8-w1'),
}
# Narrow-go arm sets (J2): one decision each.
DECISIONS = {
    'engine@1w': ('P1', 'P4', 'P7-w1', 'P8-w1'),
    'engine@16w': ('P3', 'P6', 'P7-w16', 'P8-w16'),
    'workers@conv': ('P1', 'P2', 'P3'),
    'workers@sig': ('P4', 'P5', 'P6'),
    'workers@cap16': ('P7-w1', 'P7-w16'),
    'workers@adaptive': ('P8-w1', 'P8-w16'),
}
RULE = dict(h=0.80, upper=0.87, family=0.85, families=3, drop_one=0.85, split_half=0.85)
CONVENTIONAL = ('f4', 'cap16')


class Matrix:
    """Development cells: rep costs per (record, config) plus problem and family structure."""

    def __init__(self, records, attempts, features, refs, jobs_order=None):
        self.records = {r['id']: r for r in records}
        self.problem_of = {r['id']: r['lineage']['formulation_id'] for r in records}
        self.family_of = {}
        self.problems = defaultdict(list)
        for r in records:
            self.problems[self.problem_of[r['id']]].append(r['id'])
            self.family_of[self.problem_of[r['id']]] = r['lineage']['family_id']
        self.families = defaultdict(list)
        for p, f in sorted(self.family_of.items()):
            self.families[f].append(p)
        self.feature_ms = features
        order = {j: i for i, j in enumerate(jobs_order or [])}
        cells = defaultdict(list)
        for a in sorted(attempts, key=lambda a: (order.get(a['job'], 0), a['rep'])):
            if a['record'] in self.records:
                cells[(a['record'], a['config'])].append(a)
        self.verified_digest = self._verify(cells, refs)
        self.disqualified = sorted({c for (rid, c), xs in cells.items() for a in xs
                                    if self._incorrect(rid, a)})
        self.attempts = cells
        done = {k: v for k, v in cells.items()}
        self.ladder = campaign.ladder_censored(records, done)

    def _verify(self, cells, refs):
        """Record → the digest a completion must carry (J3): the reference, else cross-engine agreement."""
        out = {}
        for rid in self.records:
            ref = refs.get(rid, {})
            if ref.get('status') == 'reference' and ref.get('reduced_basis_digest'):
                out[rid] = ref['reduced_basis_digest']
                continue
            seen = defaultdict(set)
            for config in campaign.CONFIGS:
                for a in cells.get((rid, config), []):
                    if a['status'].startswith('completed-') and a['basis_sha256']:
                        seen[campaign.CONFIGS[config][0]].add(a['basis_sha256'])
            digests = set().union(*seen.values()) if seen else set()
            if (len(digests) == 1 and any(seen.get(e) for e in CONVENTIONAL) and seen.get('sig')):
                out[rid] = digests.pop()
        return out

    def _incorrect(self, rid, a):
        if a['status'] == 'incorrect-output':
            return True
        want = self.verified_digest.get(rid)
        return bool(a['status'].startswith('completed-') and want and a['basis_sha256'] and a['basis_sha256'] != want)

    def ok(self, rid, a):
        want = self.verified_digest.get(rid)
        return a['status'].startswith('completed-') and want is not None and a['basis_sha256'] == want

    def reps(self, rid, config, k=2, half=None):
        """Per-repetition costs (ms) of one cell; `half` 0/1 keeps odd/even-numbered repetitions."""
        xs = self.attempts.get((rid, config), [])
        clean = [a for a in xs if not a['contaminated']] or xs
        if not clean:
            return [k * C_MS]  # ladder-censored, or never run: censored by declaration
        costs = [a['wall_ms'] if self.ok(rid, a) else k * C_MS for a in clean]
        if half is not None and len(costs) > 1:
            costs = costs[half::2]
        return costs

    def cell(self, rid, config, k=2, half=None):
        return statistics.median(self.reps(rid, config, k, half))


def geo(values):
    return math.exp(sum(math.log(v) for v in values) / len(values))


def problem_costs(m, arms, k=2, half=None, cell=None):
    """{problem: {arm: cost}} and {problem: VBS⁺ cost}."""
    cell = cell or (lambda rid, c: m.cell(rid, c, k, half))
    by_arm, vbs = {}, {}
    for p, rids in m.problems.items():
        per = {rid: {c: cell(rid, c) for c in arms} for rid in rids}
        by_arm[p] = {c: geo([per[rid][c] for rid in rids]) for c in arms}
        vbs[p] = geo([min(per[rid].values()) + m.feature_ms.get(rid, 0.0) for rid in rids])
    return by_arm, vbs


def family_log_means(fam_problems, values):
    return {f: sum(math.log(values[p]) for p in ps) / len(ps) for f, ps in fam_problems.items()}


def headroom(fam_list, fam_problems, by_arm, vbs, arms):
    """H, per-family ratio and the LOFO BF arm per family, over `fam_list` (duplicates allowed)."""
    arm_fam = {a: family_log_means(fam_problems, {p: by_arm[p][a] for ps in fam_problems.values() for p in ps})
               for a in arms}
    totals = {a: sum(arm_fam[a][f] for f in fam_list) for a in arms}
    counts = defaultdict(int)
    for f in fam_list:
        counts[f] += 1
    bf, fam_ratio = {}, {}
    for f in set(fam_list):
        rest = len(fam_list) - counts[f]
        if rest == 0:
            return None
        bf[f] = min(arms, key=lambda a: ((totals[a] - counts[f] * arm_fam[a][f]) / rest, a))
        fam_ratio[f] = math.exp(sum(math.log(vbs[p] / by_arm[p][bf[f]]) for p in fam_problems[f])
                                / len(fam_problems[f]))
    h = math.exp(sum(math.log(fam_ratio[f]) for f in fam_list) / len(fam_list))
    return dict(h=h, family_ratio=fam_ratio, bf=bf)


def read(m, arms, k=2, draws=20_000, seed=1012):
    """Every clause of the Go rule for one arm set."""
    arms = tuple(a for a in arms if a not in m.disqualified)
    if len(arms) < 2:
        return dict(arms=arms, go=False, reason='fewer than two eligible arms')
    fams = dict(m.families)
    by_arm, vbs = problem_costs(m, arms, k)
    point = headroom(sorted(fams), fams, by_arm, vbs, arms)
    # Largest contributor: the family whose removal raises H the most (J7).
    drops = {}
    for f in fams:
        rest = {g: ps for g, ps in fams.items() if g != f}
        r = headroom(sorted(rest), rest, *problem_costs_sub(by_arm, vbs, rest), arms)
        drops[f] = r['h'] if r else None
    worst = max((f for f in drops if drops[f] is not None), key=lambda f: drops[f])
    halves = []
    for half in (0, 1):
        ba, vb = problem_costs(m, arms, k, half)
        halves.append(headroom(sorted(fams), fams, ba, vb, arms)['h'])
    lo, hi = bootstrap(m, arms, k, draws, seed)
    n_good = sum(1 for v in point['family_ratio'].values() if v <= RULE['family'])
    clauses = dict(h=point['h'] <= RULE['h'], upper=hi <= RULE['upper'], families=n_good >= RULE['families'],
                   drop_one=drops[worst] <= RULE['drop_one'], split_half=all(x <= RULE['split_half'] for x in halves))
    return dict(arms=arms, h=point['h'], lo=lo, hi=hi, family_ratio=point['family_ratio'], bf=point['bf'],
                families_at_or_below=n_good, largest_contributor=worst, h_without_largest=drops[worst],
                drops=drops, split_half=halves, clauses=clauses, go=all(clauses.values()))


def problem_costs_sub(by_arm, vbs, fams):
    keep = {p for ps in fams.values() for p in ps}
    return {p: v for p, v in by_arm.items() if p in keep}, {p: v for p, v in vbs.items() if p in keep}


def bootstrap(m, arms, k, draws, seed):
    """Grouped percentile bootstrap: families, then problems within each, then repetitions per cell;
    BF re-chosen leave-one-family-out in every draw. bench_stats' percentile indices."""
    rng = random.Random(seed)
    fam_names = sorted(m.families)
    rep_costs = {(rid, c): m.reps(rid, c, k) for p in m.problems for rid in m.problems[p] for c in arms}
    hs = []
    for _ in range(draws):
        fam_list = rng.choices(fam_names, k=len(fam_names))
        fam_problems, by_arm, vbs = {}, {}, {}
        for j, f in enumerate(fam_list):
            ps = m.families[f]
            picked = rng.choices(ps, k=len(ps))
            key = f'{f}#{j}'
            fam_problems[key] = []
            for i, p in enumerate(picked):
                pk = f'{p}#{j}.{i}'
                fam_problems[key].append(pk)
                per = {}
                for rid in m.problems[p]:
                    per[rid] = {}
                    for c in arms:
                        xs = rep_costs[(rid, c)]
                        per[rid][c] = statistics.median(rng.choices(xs, k=len(xs))) if len(xs) > 1 else xs[0]
                by_arm[pk] = {c: geo([per[rid][c] for rid in per]) for c in arms}
                vbs[pk] = geo([min(per[rid].values()) + m.feature_ms.get(rid, 0.0) for rid in per])
        # LOFO over family identities: a drawn duplicate of F is left out with F.
        ident = {key: key.split('#')[0] for key in fam_problems}
        r = headroom_identity(fam_problems, ident, by_arm, vbs, arms)
        if r is not None:
            hs.append(r)
    hs.sort()
    return hs[int(0.025 * len(hs))], hs[int(0.975 * len(hs)) - 1]


def headroom_identity(fam_problems, ident, by_arm, vbs, arms):
    keys = list(fam_problems)
    arm_fam = {a: {key: sum(math.log(by_arm[p][a]) for p in fam_problems[key]) / len(fam_problems[key]) for key in keys}
               for a in arms}
    totals = {a: sum(arm_fam[a].values()) for a in arms}
    by_ident = defaultdict(list)
    for key in keys:
        by_ident[ident[key]].append(key)
    logs = []
    for f, members in by_ident.items():
        rest = len(keys) - len(members)
        if rest == 0:
            return None
        bf = min(arms, key=lambda a: ((totals[a] - sum(arm_fam[a][x] for x in members)) / rest, a))
        for key in members:
            logs.append(sum(math.log(vbs[p] / by_arm[p][bf]) for p in fam_problems[key]) / len(fam_problems[key]))
    return math.exp(sum(logs) / len(logs))


def completed_intersection(m, arms):
    """H over the problems every arm completed verified on every field (sensitivity only)."""
    keep = {f: [p for p in ps if all(m.cell(rid, c) < 2 * C_MS for rid in m.problems[p] for c in arms)]
            for f, ps in m.families.items()}
    keep = {f: ps for f, ps in keep.items() if ps}
    if len(keep) < 2:
        return None
    by_arm, vbs = problem_costs(m, arms)
    r = headroom(sorted(keep), keep, *problem_costs_sub(by_arm, vbs, keep), arms)
    return dict(h=r['h'], problems=sum(len(v) for v in keep.values()), families=len(keep)) if r else None


def marginal(m, arms):
    """Hydra-style marginal contribution: aggregate VBS⁺ without each arm ÷ with it."""
    fams = dict(m.families)
    _, full = problem_costs(m, arms)
    base = geo([geo([full[p] for p in ps]) for ps in fams.values()])
    out = {}
    for a in arms:
        _, without = problem_costs(m, tuple(x for x in arms if x != a))
        out[a] = geo([geo([without[p] for p in ps]) for ps in fams.values()]) / base
    return out


def winners(m, arms):
    """Per record, the cheapest arm when some arm completed verified."""
    out = {}
    for rid in m.records:
        costs = {c: m.cell(rid, c) for c in arms}
        best = min(costs, key=lambda c: (costs[c], c))
        out[rid] = best if costs[best] < 2 * C_MS else None
    return out


def completion_counts(m, arms):
    """Per arm: verified completions, censored or failed cells, out of the development records."""
    out = {}
    for c in arms:
        done = sum(1 for rid in m.records if m.cell(rid, c) < 2 * C_MS)
        out[c] = dict(completed=done, penalized=len(m.records) - done)
    return out


def render(out, m):
    lines = [f"# Gate H read (#1012)", '',
             f"**Verdict: {out['verdict']['verdict']}.** Contexts passing: {out['verdict']['contexts_passing'] or 'none'}; "
             f"single-decision arm sets passing: {out['verdict']['decisions_passing'] or 'none'}.", '',
             f"Pilot: {out['pilot']['base_problems']} base problems, {out['pilot']['families']} families. "
             f"Development: {out['development']['records']} records, {out['development']['problems']} base problems, "
             f"{out['development']['families']} families. Disqualified arms: {out['disqualified'] or 'none'}.", '',
             'Costs are PAR-2 penalized (2C = 600 s for every attempt that is not a verified completion), not runtimes.', '',
             '| Arm set | H | 95% interval | families ≤ 0.85 | H without largest contributor | split halves | Go clauses met |',
             '|---|---:|---|---:|---|---|---|']
    rows = list(out['contexts'].items()) + list(out['decisions'].items())
    for name, r in rows:
        if 'h' not in r:
            lines.append(f"| {name} | — | — | — | — | — | {r.get('reason')} |")
            continue
        met = ', '.join(k for k, v in r['clauses'].items() if v) or 'none'
        lines.append(f"| {name} | {r['h']:.3f} | [{r['lo']:.3f}, {r['hi']:.3f}] | {r['families_at_or_below']} | "
                     f"{r['h_without_largest']:.3f} ({r['largest_contributor']}) | "
                     f"{r['split_half'][0]:.3f} / {r['split_half'][1]:.3f} | {met} |")
    for name, r in out['contexts'].items():
        lines += ['', f'## Context {name}', '',
                  f"PAR-10 H {r['par10']:.3f}; completed-intersection H "
                  + (f"{r['completed_intersection']['h']:.3f} over {r['completed_intersection']['problems']} problems "
                     f"in {r['completed_intersection']['families']} families" if r['completed_intersection'] else '—')
                  + ' (sensitivity views; they do not decide).', '',
                  '| Family | problems | LOFO best fixed | VBS⁺ ÷ BF |', '|---|---:|---|---:|']
        for f in sorted(r['family_ratio']):
            lines.append(f"| `{f}` | {len(m.families[f])} | {r['bf'][f]} | {r['family_ratio'][f]:.3f} |")
        lines += ['', '| Arm | verified cells | penalized cells | marginal (VBS⁺ without ÷ with) |', '|---|---:|---:|---:|']
        for c, v in r['completions'].items():
            lines.append(f"| {c} | {v['completed']} | {v['penalized']} | {r['marginal'][c]:.3f} |")
    wins = defaultdict(lambda: defaultdict(int))
    for rid, c in out['winners'].items():
        wins[m.family_of[m.problem_of[rid]]][c or 'none'] += 1
    lines += ['', '## Cheapest arm per record (W16 arms)', '', '| Family | wins |', '|---|---|']
    for f in sorted(wins):
        lines.append(f"| `{f}` | " + ', '.join(f'{c} {n}' for c, n in sorted(wins[f].items(), key=lambda x: -x[1])) + ' |')
    return '\n'.join(lines) + '\n'


def load(paths=None):
    rs = campaign.development()
    attempts = []
    path = campaign.RESULTS / 'attempts.jsonl'
    if path.exists():
        attempts = [json.loads(x) for x in path.read_text().splitlines()]
    features = {}
    fpath = campaign.RESULTS / 'features.jsonl'
    if fpath.exists():
        for line in fpath.read_text().splitlines():
            row = json.loads(line)
            if 'feature_costs' in row:
                features[row['id']] = sum(v['median_ns'] for v in row['feature_costs'].values()) / 1e6
    # J4 fallback: a record feature_costs cannot instantiate is charged the largest measured set cost.
    worst = max(features.values()) if features else 0.0
    features = {r['id']: features.get(r['id'], worst) for r in rs}
    jobs = [j['job'] for j in json.loads(campaign.JOBS.read_text())] if campaign.JOBS.exists() else []
    return Matrix(rs, attempts, features, campaign.references(), jobs)


def pilot_size():
    rs = campaign.records()
    return len({r['lineage']['formulation_id'] for r in rs}), len({r['lineage']['family_id'] for r in rs})


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--draws', type=int, default=20_000)
    p.add_argument('--json', default=str(campaign.RESULTS / 'gate-h.json'))
    p.add_argument('--markdown', default=str(campaign.RESULTS / 'gate-h.md'))
    args = p.parse_args(argv)
    m = load()
    problems, families = pilot_size()
    out = dict(pilot=dict(base_problems=problems, families=families,
                          readable=problems >= 60 and families >= 10),
               development=dict(records=len(m.records), problems=len(m.problems), families=len(m.families)),
               disqualified=m.disqualified, contexts={}, decisions={})
    for name, arms in CONTEXTS.items():
        r = read(m, arms, 2, args.draws)
        r['par10'] = read(m, arms, 10, 0 if args.draws == 0 else min(args.draws, 2000))['h']
        r['completed_intersection'] = completed_intersection(m, arms)
        r['marginal'] = marginal(m, arms)
        r['completions'] = completion_counts(m, arms)
        out['contexts'][name] = r
    for name, arms in DECISIONS.items():
        out['decisions'][name] = read(m, arms, 2, args.draws)
    out['winners'] = winners(m, CONTEXTS['W16'])
    go = [c for c, r in out['contexts'].items() if r['go']]
    narrow = [d for d, r in out['decisions'].items() if r['go']]
    if not out['pilot']['readable']:
        verdict = 'insufficient corpus'
    elif go:
        verdict = 'go'
    elif narrow:
        verdict = 'narrow go'
    else:
        verdict = 'no-go'
    out['verdict'] = dict(verdict=verdict, contexts_passing=go, decisions_passing=narrow,
                          scoring_context='W16' if 'W16' in go else (go[0] if go else None))
    Path(args.json).write_text(json.dumps(out, indent=1, sort_keys=True, default=list) + '\n')
    Path(args.markdown).write_text(render(out, m))
    print(json.dumps(out['verdict']))
    for name, r in out['contexts'].items():
        print(name, f"H {r['h']:.3f} [{r['lo']:.3f}, {r['hi']:.3f}]", r['clauses'])


if __name__ == '__main__':
    main()
