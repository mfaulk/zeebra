#!/usr/bin/env python3
import argparse
from collections import Counter, defaultdict
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
from statistics import median

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SPEC=importlib.util.spec_from_file_location('whole_study',ROOT/'tools/external/whole-route-study.py')
study=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(study)


def validate_plan(cohort):
    expected=[list(cell) for cell in study.plan(cohort['phase'])]
    if [list(cell) for cell in cohort['plan']]!=expected: raise ValueError('declared plan differs')
    actual=[[a[k] for k in ('repeat','problem','modulus','route','arm')] for a in cohort['attempts']]
    if actual!=expected[:len(actual)] or len(actual)>len(expected): raise ValueError('attempt order or coverage differs')
    if len(actual)!=len(expected) and not cohort.get('refusal'): raise ValueError('unfinished grid without explicit refusal')
    return len(actual)==len(expected)


def ceiling(total,part):
    if total<=0 or not 0<=part<total: raise ValueError('invalid same-attempt stage boundary')
    return total/(total-part)


def spread(values):
    values=list(values)
    return dict(median=median(values),minimum=min(values),maximum=max(values)) if values else None


def summarize(path):
    cohort=json.loads(gzip.decompress(path.read_bytes()))
    complete=validate_plan(cohort)
    refs=study.load('selective-backward-study').references()
    for reference in cohort.get('references',{}).values():
        if study.valid_proof(reference): refs[('katsura-11',2147483647)]=reference
    groups=defaultdict(list)
    for attempt in cohort['attempts']:
        decoded=study.responses(attempt['stdout'])
        if decoded!=attempt['responses']: raise ValueError('stored response does not match raw stdout')
        if attempt['compiler_before'] or attempt['compiler_after']: raise ValueError('compiler contamination')
        if attempt['status']=='failed': raise ValueError('unresolved failed attempt')
        raw=decoded['final']
        key=(attempt['problem'],attempt['modulus'])
        if attempt['status'] in ('verified','reported-resource-refusal','complete-needs-independent-basis-check'):
            if attempt['exit'] or attempt['stop'] or raw is None: raise ValueError('accepted response did not exit normally')
            study.validate_response(raw,refs.get(key),*key,attempt['route'],attempt['arm'])
            if attempt['status']=='verified' and key not in refs: raise ValueError('independent reference missing')
        elif attempt['status']=='incomplete-resource-refusal':
            if not attempt['exit'] and not attempt['stop']: raise ValueError('resource refusal lacks terminal cause')
            if attempt.get('source_basis_verified'):
                identity=decoded['identity']
                study.load('mq10-profile').check_answer(dict(decoded['source'],digest=identity['digest'],modulus=identity['modulus']),refs[key])
        else: raise ValueError('unknown attempt status')
        if raw and raw.get('point') is not None: study.check_point(raw)
        groups[(*key,attempt['route'],attempt['arm'])].append(attempt)
    rows=[]
    for (problem,modulus,route,arm),attempts in sorted(groups.items()):
        complete_attempts=[a for a in attempts if a['status'] in ('verified','complete-needs-independent-basis-check')]
        raw=[a['responses']['final'] for a in complete_attempts]
        row=dict(problem=problem,modulus=modulus,route=route,arm=arm,repetitions=len(attempts),
                 statuses=dict(Counter(a['status'] for a in attempts)),
                 outcomes=dict(Counter(a['responses']['final'].get('outcome','basis') if a['responses']['final'] else a['responses']['active_stage'] or 'basis' for a in attempts)),
                 completed_process_ms=spread(a['process_wall_ns']/1e6 for a in complete_attempts),
                 attempted_process_ms=spread(a['process_wall_ns']/1e6 for a in attempts),
                 cpu_ms=spread(a['cpu_seconds']*1000 for a in complete_attempts),
                 sampled_peak_rss_bytes=spread(a['peak_rss_bytes'] for a in complete_attempts),
                 self_peak_rss_bytes=spread(r['peak_rss_bytes'] for r in raw),
                 f4_call_ms=spread(r['f4_call_ns']/1e6 for r in raw))
        if route!='basis':
            row['whole_route_ms']=spread(r['whole_route_ns']/1e6 for r in raw)
            row['checkpoint_ms']=spread(r['checkpoint_ns']/1e6 for r in raw)
            for key in ('conversion_call_ns','recovery_call_ns','independent_substitution_ns'):
                row[key.removesuffix('_ns')+'_ms']=spread(r[key]/1e6 for r in raw if r[key] is not None)
            if arm!='stage-off':
                for key in ('symbolic','construction','forward','backward','extraction','interreduction'):
                    row[key+'_ms']=spread(r['statistics'][key+'_ns']/1e6 for r in raw)
                    row[key+'_ideal_ceiling']=spread(ceiling(r['whole_route_ns'],r['statistics'][key+'_ns']) for r in raw)
                for key in ('quotient_basis','operator','dependence','scalar_sequence','scalar_reconstruction','scalar_certificate'):
                    row[key+'_ms']=spread(r['conversion'][key+'_ns']/1e6 for r in raw if r['conversion'] is not None)
        if arm=='work':
            row['work']=[dict(forward_products=sum(b['forward']['coefficient_products'] for b in r['work']['batches']),
                              backward_products=sum(b['backward']['coefficient_products'] for b in r['work']['batches']),
                              candidate=r['statistics']['candidate_reduction']) for r in raw]
        rows.append(row)
    return dict(phase=cohort['phase'],complete=complete,archive_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                identity=cohort['identity'],limits=cohort['limits'],attempts=len(cohort['attempts']),
                statuses=dict(Counter(a['status'] for a in cohort['attempts'])),rows=rows)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    paths=[HERE/name for name in ('pilot.json.gz','native.json.gz') if (HERE/name).exists()]
    if not paths: raise ValueError('no retained cohort')
    encoded=json.dumps([summarize(path) for path in paths],indent=2)+'\n'
    output=HERE/'summary.json'
    if args.check:
        if output.read_text()!=encoded: raise ValueError('retained summary differs')
    else: output.write_text(encoded)
    print('validated frozen plans, complete basis references, points and same-attempt stage models')


if __name__=='__main__': main()
