#!/usr/bin/env python3
import argparse
import ast
from collections import defaultdict
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
NATIVE_PREFIX_CONTROLLER = '9e2017806b95cbf88a904ad9213d324c2a1f5b0e'
NATIVE_PREFIX_SHA256 = '3a733e31cf1d70ad27d322f2e950cd736676b4726ccb8004a8fa0754d6b1bd8f'
NATIVE_PRIOR_CHARGE_SECONDS = 20


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT/'tools/external'/(name+'.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def limits():
    return dict(child_wall_seconds=60, rss_bytes=2*1024**3, aggregate_wall_seconds=900, output_bytes=256*1024**2)


def child_wall(remaining):
    if remaining<1: raise ValueError('aggregate allowance exhausted')
    return min(60,int(remaining))


def plan(phase='native'):
    if phase == 'pilot':
        for modulus in (32003,2147483647):
            yield 0,'mq-random-10',modulus,'fglm','stage-on'
            yield 0,'cyclic-5',modulus,'fglm','stage-on'
        yield 0,'katsura-11',2147483647,'basis','stage-on'
        yield 0,'mq-random-10',32003,'direct','stage-on'
        return
    for repeat in range(5):
        for problem in ('mq-random-10','katsura-6','cyclic-5'):
            for modulus in (32003,2147483647):
                for arm in (('stage-off','stage-on') if repeat%2 == 0 else ('stage-on','stage-off')):
                    yield repeat,problem,modulus,'fglm',arm
        for modulus in (32003,2147483647):
            yield repeat,'mq-random-10',modulus,'fglm','work'
        yield repeat,'katsura-11',2147483647,'basis','stage-on'


def responses(stdout):
    lines = stdout.strip().splitlines()
    if not lines: return dict(source=None, final=None, identity=None, lex=None, active_stage=None)
    # Ordinary basis-mode output is pretty JSON; whole-route emits newline-delimited records.
    try:
        value=json.loads(stdout)
        lines=[stdout] if isinstance(value,dict) else lines
    except json.JSONDecodeError:
        pass
    source, final, identity, lex, active_stage = None, None, None, None, None
    for line in lines:
        value=json.loads(line)
        if value.get('checkpoint') == 'input':
            if identity is not None: raise ValueError('duplicate input checkpoint')
            identity=value
        elif value.get('checkpoint') == 'active-stage':
            active_stage=value['stage']
        elif value.get('checkpoint') == 'lex-basis':
            if lex is not None: raise ValueError('duplicate lex checkpoint')
            lex=value
        elif value.get('checkpoint') == 'source-basis':
            if source is not None: raise ValueError('duplicate source checkpoint')
            source=value
        elif value.get('outcome') or ('basis' in value and 'modulus' in value):
            if final is not None: raise ValueError('duplicate final response')
            final=value
        else: raise ValueError('unexpected response record')
    return dict(source=source, final=final, identity=identity, lex=lex, active_stage=active_stage)


def check_point(raw):
    p=raw['modulus']
    point=raw['point']
    names=raw['input']['variables']
    if len(point)!=len(names): raise ValueError('point width differs')
    values={name:int(value)%p for name,value in zip(names,point)}
    def evaluate(node):
        if isinstance(node,ast.Constant) and type(node.value) is int: return node.value%p
        if isinstance(node,ast.Name) and node.id in values: return values[node.id]
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub): return -evaluate(node.operand)%p
        if isinstance(node,ast.BinOp):
            if isinstance(node.op,ast.Pow):
                if not isinstance(node.right,ast.Constant) or type(node.right.value) is not int or not 0<=node.right.value<=2**32:
                    raise ValueError('invalid polynomial exponent')
                return pow(evaluate(node.left),node.right.value,p)
            left,right=evaluate(node.left),evaluate(node.right)
            if isinstance(node.op,ast.Add): return (left+right)%p
            if isinstance(node.op,ast.Sub): return (left-right)%p
            if isinstance(node.op,ast.Mult): return left*right%p
        raise ValueError('unsupported polynomial expression')
    for generator in raw['input']['generators']:
        if evaluate(ast.parse(generator.replace('^','**'),mode='eval').body):
            raise ValueError('point fails original equation')


def validate_response(raw, reference, problem, modulus, route, arm):
    if raw['problem'] != problem or raw['modulus'] != modulus: raise ValueError('problem identity drift')
    if route != 'direct' and reference:
        if raw.get('digest')!=reference['digest'] or raw['modulus']!=reference['modulus']: raise ValueError('reference identity drift')
        if 'generators' in reference and raw.get('input')!=dict(variables=reference['variables'],generators=reference['generators']): raise ValueError('original equations differ from reference')
        if raw.get('basis') is not None:
            if reference.get('canonical_comparison'): load('comparand-scaling').verify_basis(raw['basis'],reference['basis'],dict(modulus=modulus,variables=reference['variables']))
            else: load('mq10-profile').check_answer(raw,reference)
    if route!='basis':
        if raw['route'] != route or raw['outcome'] not in ('verified-point','no-base-field-point','inconsistent','positive-dimensional','conversion-refusal','recovery-refusal','basis-refusal'):
            raise ValueError('invalid route outcome')
        if raw['outcome']=='verified-point': check_point(raw)
        elif raw['point'] is not None: raise ValueError('unsuccessful route contains point')
    if raw['measured'] != (arm!='stage-off'): raise ValueError('stage mode drift')
    if (raw.get('work') is not None) != (arm=='work'): raise ValueError('work mode drift')


def terminal_kind(exit_code,stop,stderr):
    if stop and any(stop==kind or stop.startswith(kind+'-') for kind in ('wall','rss','output','launcher-signal')): return 'incomplete-resource-refusal'
    if exit_code and any(name in stderr for name in ('TooManyNonzeros','TooManyMatrixRows','TooManyMatrixColumns','TooManyBasisElements')):
        return 'incomplete-resource-refusal'
    return 'failed'


def references():
    refs=load('selective-backward-study').references()
    scaling=load('comparand-scaling')
    archive=ROOT/'research/comparand-scaling/singular-reference31-v1.json.gz'
    cohort=scaling.validate_cohort(scaling.load_cohort(archive))
    attempts=[a for a in cohort['attempts'] if a['engine']=='singular' and a['status']=='verified' and not a['exit'] and not a['stop']]
    if len(attempts)!=1: raise ValueError('missing independent Katsura reference')
    attempt=attempts[0]
    case=scaling.canonical_case(next(c for c in cohort['cases'] if c['digest']==attempt['digest']))
    if case['name']!='katsura-11' or int(case['modulus'])!=2147483647 or case['digest']!='03bf44d5d614a21cc8f56462aa873b7961641a2341892e3b2ef52b6cfec86a13':
        raise ValueError('Katsura reference identity differs')
    refs[('katsura-11',2147483647)]=dict(modulus=2147483647,digest=case['digest'],basis=attempt['basis'],
        variables=case['variables'],generators=case['generators'],canonical_comparison=True,
        archive=str(archive.relative_to(ROOT)),archive_sha256=sha(archive),
        controller=cohort['commit'],checker=cohort['binaries']['singular'],verification='retained independent Singular std/redSB full coefficient set')
    return refs


def repository_path(path):
    return str(path.resolve().relative_to(ROOT))


def native_remaining_seconds():
    return limits()['aggregate_wall_seconds']-NATIVE_PRIOR_CHARGE_SECONDS


def resume_prefix(previous,current,native_amendment=False):
    frozen=('binary_sha256','build_commit','cargo_lock_sha256','cargo_config_sha256','rustc','machine','affinity','build','topology')
    if (previous['phase']!=current['phase'] or [list(c) for c in previous['plan']]!=[list(c) for c in current['plan']]
            or previous.get('refusal',{}).get('reason') not in ('compiler','load-or-aggregate') or previous.get('resumptions')
            or previous['references']!=current['references']): raise ValueError('continuation identity or prior refusal differs')
    if any(previous['identity'][key]!=current['identity'][key] for key in frozen): raise ValueError('frozen executable/source/environment changed')
    if previous['phase']=='native':
        if not native_amendment or previous['identity']['commit']!=NATIVE_PREFIX_CONTROLLER or len(previous['attempts'])!=2:
            raise ValueError('native continuation requires the explicit two-cell amendment')
    elif native_amendment:
        raise ValueError('native amendment cannot resume a pilot')
    attempts=previous['attempts']
    actual=[[a[k] for k in ('repeat','problem','modulus','route','arm')] for a in attempts]
    expected=[list(cell) for cell in current['plan']]
    if actual!=expected[:len(actual)] or len(actual)>=len(expected) or any(a['status']!='verified' for a in attempts):
        raise ValueError('continuation requires an exact verified prefix and unattempted tail')
    return len(attempts)


def main():
    parser=argparse.ArgumentParser()
    for key in ('binary','scratch','output'): parser.add_argument('--'+key,type=Path,required=True)
    parser.add_argument('--phase',choices=('pilot','native'),default='pilot')
    parser.add_argument('--build-commit',required=True)
    continuation=parser.add_mutually_exclusive_group()
    continuation.add_argument('--resume-from',type=Path)
    continuation.add_argument('--native-amendment-from',type=Path)
    args=parser.parse_args()
    if args.output.exists(): parser.error('retain existing campaign and choose new output')
    if args.resume_from and args.phase!='pilot': parser.error('native grid requires its explicit one-time amendment')
    if args.native_amendment_from:
        if args.phase!='native' or repository_path(args.native_amendment_from)!='research/m28-current-baseline/native.json.gz' or sha(args.native_amendment_from)!=NATIVE_PREFIX_SHA256:
            parser.error('native amendment requires the exact pinned original prefix')
        amended=ROOT/'research/m28-current-baseline/native-completed.json.gz'
        if amended.exists() or args.output.resolve()!=amended:
            parser.error('native amendment has one immutable output and cannot be repeated')
    if subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True).strip(): parser.error('commit instruments before measuring')
    if subprocess.call(['git','diff','--quiet',args.build_commit,'--','src','examples','Cargo.toml','Cargo.lock','.cargo'],cwd=ROOT): parser.error('build tree differs')
    affinity=','.join(map(str,sorted(os.sched_getaffinity(0))))
    if os.environ.get('ZEEBRA_AFFINITY')!=affinity or not os.environ.get('ZEEBRA_MACHINE'): parser.error('declare actual affinity/machine under benchlock')
    args.scratch.mkdir(parents=True,exist_ok=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    cells=list(plan(args.phase))
    campaign_limits=limits()
    if args.phase=='pilot': campaign_limits['aggregate_wall_seconds']=480
    if args.resume_from: campaign_limits['aggregate_wall_seconds']=180
    if args.native_amendment_from: campaign_limits['aggregate_wall_seconds']=native_remaining_seconds()
    cohort=dict(schema=1,phase=args.phase,identity=dict(commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        build_commit=args.build_commit,binary_sha256=sha(args.binary),cargo_lock_sha256=sha(ROOT/'Cargo.lock'),
        cargo_config_sha256=sha(ROOT/'.cargo/config.toml'),rustc=subprocess.check_output(['rustc','-vV'],text=True),
        machine=os.environ['ZEEBRA_MACHINE'],affinity=affinity,build='release;fat-LTO;one-codegen-unit;x86-64-v3;mold;system allocator;research-work;CARGO_INCREMENTAL=0;RUSTC_WRAPPER empty',
        topology=subprocess.check_output(['lscpu','-e=CPU,CORE,SOCKET,NODE,CACHE,ONLINE'],text=True)),
        limits=campaign_limits,plan=cells,attempts=[],references={})
    refs=references()
    cohort['references']['katsura-11/2147483647']=refs[('katsura-11',2147483647)]
    prefix_archive=args.native_amendment_from or args.resume_from
    prior_archive_bytes=0
    if prefix_archive:
        import gzip
        previous=json.loads(gzip.decompress(prefix_archive.read_bytes()))
        prefix=resume_prefix(previous,cohort,native_amendment=bool(args.native_amendment_from))
        controller=cohort['identity']['commit']
        cohort=previous
        refusal=cohort.pop('refusal')
        cohort['resumptions']=[dict(controller=controller,prefix_archive=repository_path(prefix_archive),
            prefix_archive_sha256=sha(prefix_archive),accepted_prefix=prefix,refusal=refusal,aggregate_wall_seconds=campaign_limits['aggregate_wall_seconds'])]
        if args.native_amendment_from:
            prior_archive_bytes=prefix_archive.stat().st_size
            cohort['resumptions'][0].update(kind='explicit-native-amendment-v1',prior_controller_charge_seconds=NATIVE_PRIOR_CHARGE_SECONDS,
                original_aggregate_wall_seconds=limits()['aggregate_wall_seconds'],prefix_archive_bytes=prior_archive_bytes)
    guard=load('grobx-work-study')
    supervisor=load('comparand-scaling')
    def interrupted(signum,_): raise SystemExit(128+signum)
    signal.signal(signal.SIGTERM,interrupted)
    runtime=load('worker-pool-study')
    began=time.monotonic()
    for repeat,problem,modulus,route,arm in cells[len(cohort['attempts']):]:
        compilers=runtime.compiler_processes()
        remaining_wall=campaign_limits['aggregate_wall_seconds']-(time.monotonic()-began)
        if compilers or os.getloadavg()[0]>4 or remaining_wall<1:
            cohort['refusal']=dict(reason='compiler' if compilers else 'load-or-aggregate',compilers=compilers,load=os.getloadavg()[0]);guard.write(args.output,cohort);return
        if sha(args.binary)!=cohort['identity']['binary_sha256']: raise ValueError('binary changed')
        command=[str(args.binary.resolve()),str(modulus),'--problem='+problem]
        if route!='basis': command+=['--whole-route='+route]
        if arm!='stage-off': command+=['--stages']
        if arm=='work': command+=['--work']
        usage=resource.getrusage(resource.RUSAGE_CHILDREN)
        remaining=limits()['output_bytes']-prior_archive_bytes-sum(p.stat().st_size for p in args.scratch.iterdir())-(args.output.stat().st_size if args.output.exists() else 0)
        if remaining<=0: raise RuntimeError('output budget exhausted')
        result=supervisor.guarded(['timeout','--signal=KILL','185',*command],args.scratch/str(len(cohort['attempts'])),sorted(os.sched_getaffinity(0)),child_wall(remaining_wall),limits()['rss_bytes'],min(128*1024**2,remaining))
        result['observed_peak_rss_bytes']=result['observed_tree_peak_bytes']
        after=resource.getrusage(resource.RUSAGE_CHILDREN)
        result.update(repeat=repeat,problem=problem,modulus=modulus,route=route,arm=arm,load=os.getloadavg()[0],cpu_seconds=after.ru_utime+after.ru_stime-usage.ru_utime-usage.ru_stime,
            compiler_before=compilers,compiler_after=runtime.compiler_processes())
        try:
            result['responses']=responses(result['stdout'])
            raw=result['responses']['final']
            if result['compiler_after']: result['status']='contaminated'
            elif result['exit'] or result['stop']:
                result['status']=terminal_kind(result['exit'],result['stop'],result['stderr'])
                checkpoint=result['responses']['source']
                if checkpoint and (problem,modulus) in refs:
                    identity=result['responses']['identity']
                    if not identity or identity.get('problem')!=problem: raise ValueError('missing input checkpoint')
                    load('mq10-profile').check_answer(dict(checkpoint,digest=identity['digest'],modulus=identity['modulus']),refs[(problem,modulus)])
                    result['source_basis_verified']=True
            else:
                if raw is None: raise ValueError('successful process has no final response')
                validate_response(raw,refs.get((problem,modulus)),problem,modulus,route,arm)
                result['status']=('reported-resource-refusal' if raw.get('outcome') in ('basis-refusal','conversion-refusal','recovery-refusal') else
                                  'verified' if (problem,modulus) in refs and route!='direct' else 'complete-needs-independent-basis-check')
        except (ValueError,KeyError,TypeError) as error:
            result.update(status='failed',failure=str(error))
        cohort['attempts'].append(result)
        guard.write(args.output,cohort)
        print(repeat,problem,modulus,route,arm,result['status'],round(result['process_wall_ns']/1e6,2),flush=True)
        if result.get('interrupt_exit'):
            cohort['refusal']=dict(reason='launcher-signal',exit=result['interrupt_exit']);guard.write(args.output,cohort);raise SystemExit(result['interrupt_exit'])
        if result['status']=='failed': raise RuntimeError('failed validation; raw attempt retained')
        if result['status']=='contaminated': cohort['refusal']=dict(reason='compiler');guard.write(args.output,cohort);return
        if args.native_amendment_from and result['status']!='verified':
            cohort['refusal']=dict(reason='amended-child-refusal',status=result['status'],stop=result['stop']);guard.write(args.output,cohort);return
        if prior_archive_bytes+sum(p.stat().st_size for p in args.scratch.iterdir())+args.output.stat().st_size>limits()['output_bytes']: raise RuntimeError('output budget exceeded; retained attempts')


if __name__=='__main__': main()
