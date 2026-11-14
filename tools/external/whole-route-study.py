#!/usr/bin/env python3
import argparse
import ast
from collections import defaultdict
import contextlib
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
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


@contextlib.contextmanager
def deferred_signals():
    # A watchdog TERM landing mid-append would raise between write and chain update; hold it until the record is whole.
    blocked=signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGTERM,signal.SIGINT})
    try: yield
    finally: signal.pthread_sigmask(signal.SIG_SETMASK,blocked)


def open_journal(directory, cohort, window_limits):
    """Static identity and any accepted prefix go in the header once; the journal plan is the unattempted tail."""
    header={k:v for k,v in cohort.items() if k not in ('plan','limits','attempts')}
    header.update(cohort_plan=cohort['plan'],cohort_limits=cohort['limits'],prefix_attempts=cohort['attempts'])
    tail=[list(cell) for cell in cohort['plan'][len(cohort['attempts']):]]
    return load('attempt_journal').StudyJournal.create(directory,header,tail,window_limits)


def attempt_metadata(result, cell, compilers, load_average, child_wall_seconds, output_limit):
    metadata={k:v for k,v in result.items() if k not in ('stdout','stderr')}
    metadata.update(zip(('repeat','problem','modulus','route','arm'),cell))
    metadata.update(load=load_average,compiler_before=compilers,wall_seconds=result['process_wall_ns']/1e9,
        observed_peak_rss_bytes=result['observed_tree_peak_bytes'],
        guard=dict(child_wall_seconds=child_wall_seconds,rss_bytes=limits()['rss_bytes'],output_limit_bytes=output_limit,
                   interrupt_exit=result.get('interrupt_exit')))
    return metadata


def classify(stdout, stderr, metadata, cell, refs, compiler_after):
    _,problem,modulus,route,arm=cell
    details=dict(compiler_after=compiler_after)
    try:
        parsed=responses(stdout)
        raw=parsed['final']
        if compiler_after: status='contaminated'
        elif metadata['exit'] or metadata['stop']:
            status=terminal_kind(metadata['exit'],metadata['stop'],stderr)
            checkpoint=parsed['source']
            if checkpoint and (problem,modulus) in refs:
                identity=parsed['identity']
                if not identity or identity.get('problem')!=problem: raise ValueError('missing input checkpoint')
                load('mq10-profile').check_answer(dict(checkpoint,digest=identity['digest'],modulus=identity['modulus']),refs[(problem,modulus)])
                details['source_basis_verified']=True
        else:
            if raw is None: raise ValueError('successful process has no final response')
            validate_response(raw,refs.get((problem,modulus)),problem,modulus,route,arm)
            status=('reported-resource-refusal' if raw.get('outcome') in ('basis-refusal','conversion-refusal','recovery-refusal') else
                    'verified' if (problem,modulus) in refs and route!='direct' else 'complete-needs-independent-basis-check')
    except (ValueError,KeyError,TypeError) as error:
        status='failed'
        details['failure']=str(error)
    return status,details


def measure(journal, offset, refs, launch, compilers, load_average, remaining_wall, output_remaining, native_amendment=False, log=print):
    """The bounded window: each child is journaled durably before its output is parsed or checked."""
    def stop(reason, **values):
        with deferred_signals(): journal.record_stop(reason,**values)
    plan=journal.header['plan']
    for index in range(journal.next_index,len(plan)):
        cell=plan[index]
        before=compilers()
        load_before=load_average()
        wall=remaining_wall()
        if before or load_before>4 or wall<1:
            return stop('compiler' if before else 'load-or-aggregate',compilers=before,load=load_before,remaining_wall_seconds=wall)
        output_left=output_remaining()
        if output_left<=0: return stop('output-bytes',remaining_bytes=output_left)
        child_wall_seconds,output_limit=child_wall(wall),min(128*1024**2,output_left)
        result=launch(offset+index,cell,child_wall_seconds,output_limit)
        stdout,stderr=result['stdout'],result['stderr']
        metadata=attempt_metadata(result,cell,before,load_average(),child_wall_seconds,output_limit)
        with deferred_signals(): journal.record_exit(index,cell,stdout.encode(),stderr.encode(),metadata)
        status,details=classify(stdout,stderr,metadata,cell,refs,compilers())
        with deferred_signals(): journal.record_verdict(index,status,details)
        log(*cell,status,round(metadata['process_wall_ns']/1e6,2),flush=True)
        if result.get('interrupt_exit'):
            stop('launcher-signal',exit=result['interrupt_exit']);raise SystemExit(result['interrupt_exit'])
        if status=='failed':
            stop('failed-validation',index=offset+index,failure=details['failure']);raise RuntimeError('failed validation; raw attempt retained')
        if status=='contaminated': return stop('compiler',compilers=details['compiler_after'],after_child=offset+index)
        if native_amendment and status!='verified':
            return stop('amended-child-refusal',status=status,stop=metadata['stop'])
        output_left=output_remaining()
        if output_left<0: return stop('output-bytes',remaining_bytes=output_left,after_child=offset+index)


def render(directory, output):
    """Offline, deterministic repack of a whole-route journal into the cohort shape the summarizer reads."""
    journal=load('attempt_journal')
    state=journal.load(directory)
    header=dict(state['header'])
    attempts=list(header.pop('prefix_attempts'))
    for attempt in state['attempts']:
        row=dict(attempt['metadata'],stdout=attempt['stdout'].decode(),stderr=attempt['stderr'].decode())
        row.update(attempt['verdict'] or {})
        row['status']=attempt['status']
        try: row['responses']=responses(row['stdout'])
        except (ValueError,KeyError,TypeError): pass
        attempts.append(row)
    plan,cohort_limits=header.pop('cohort_plan'),header.pop('cohort_limits')
    cohort=dict(header,plan=plan,limits=cohort_limits,attempts=attempts,
        journal=dict(storage='whole-route-journal-render-v1',journal_sha256=state['journal_sha256'],
                     window_limits=state['limits'],window_plan=state['plan'],quarantined=state['quarantined']))
    if state['stop']: cohort['refusal']=state['stop']
    payload=(json.dumps(cohort,indent=2,sort_keys=True)+'\n').encode()
    output=Path(output)
    journal._atomic_write(output,gzip.compress(payload,compresslevel=9,mtime=0))
    if gzip.decompress(output.read_bytes())!=payload: raise ValueError('rendered cohort did not round-trip')
    return cohort


def scratch_bytes(scratch):
    return sum(p.stat().st_size for p in scratch.iterdir() if p.is_file())


def main():
    if sys.argv[1:2]==['render']:
        parser=argparse.ArgumentParser(prog='whole-route-study.py render',description='repack a whole-route journal offline')
        parser.add_argument('journal',type=Path)
        parser.add_argument('output',type=Path)
        args=parser.parse_args(sys.argv[2:])
        render(args.journal,args.output)
        return
    parser=argparse.ArgumentParser()
    for key in ('binary','scratch','output'): parser.add_argument('--'+key,type=Path,required=True)
    parser.add_argument('--journal',type=Path,help='durable attempt journal (default: SCRATCH/<output name>.journal)')
    parser.add_argument('--phase',choices=('pilot','native'),default='pilot')
    parser.add_argument('--build-commit',required=True)
    continuation=parser.add_mutually_exclusive_group()
    continuation.add_argument('--resume-from',type=Path)
    continuation.add_argument('--native-amendment-from',type=Path)
    args=parser.parse_args()
    args.journal=args.journal or args.scratch/(args.output.name.split('.')[0]+'.journal')
    if args.output.exists(): parser.error('retain existing campaign and choose new output')
    if args.journal.exists(): parser.error('retain existing journal and choose new output')
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
        previous=json.loads(gzip.decompress(prefix_archive.read_bytes()))
        prefix=resume_prefix(previous,cohort,native_amendment=bool(args.native_amendment_from))
        controller=cohort['identity']['commit']
        cohort=previous
        refusal=cohort.pop('refusal')
        cohort['resumptions']=[dict(controller=controller,prefix_archive=repository_path(prefix_archive),
            prefix_archive_sha256=sha(prefix_archive),accepted_prefix=prefix,refusal=refusal,aggregate_wall_seconds=campaign_limits['aggregate_wall_seconds'])]
        if 'journal' in cohort: cohort['resumptions'][0]['prefix_journal']=cohort.pop('journal')
        if args.native_amendment_from:
            prior_archive_bytes=prefix_archive.stat().st_size
            cohort['resumptions'][0].update(kind='explicit-native-amendment-v1',prior_controller_charge_seconds=NATIVE_PRIOR_CHARGE_SECONDS,
                original_aggregate_wall_seconds=limits()['aggregate_wall_seconds'],prefix_archive_bytes=prior_archive_bytes)
    supervisor=load('comparand-scaling')
    def interrupted(signum,_): raise SystemExit(128+signum)
    signal.signal(signal.SIGTERM,interrupted)
    runtime=load('worker-pool-study')
    journal=open_journal(args.journal,cohort,campaign_limits)
    began=time.monotonic()

    def launch(index,cell,wall,output_limit):
        _,problem,modulus,route,arm=cell
        if sha(args.binary)!=cohort['identity']['binary_sha256']: raise ValueError('binary changed')
        command=[str(args.binary.resolve()),str(modulus),'--problem='+problem]
        if route!='basis': command+=['--whole-route='+route]
        if arm!='stage-off': command+=['--stages']
        if arm=='work': command+=['--work']
        usage=resource.getrusage(resource.RUSAGE_CHILDREN)
        result=supervisor.guarded(['timeout','--signal=KILL','185',*command],args.scratch/str(index),sorted(os.sched_getaffinity(0)),wall,limits()['rss_bytes'],output_limit)
        after=resource.getrusage(resource.RUSAGE_CHILDREN)
        result['cpu_seconds']=after.ru_utime+after.ru_stime-usage.ru_utime-usage.ru_stime
        return result

    measure(journal,len(cohort['attempts']),refs,launch,runtime.compiler_processes,lambda: os.getloadavg()[0],
        lambda: campaign_limits['aggregate_wall_seconds']-(time.monotonic()-began),
        lambda: limits()['output_bytes']-prior_archive_bytes-scratch_bytes(args.scratch)-journal.retained_bytes,
        native_amendment=bool(args.native_amendment_from))
    # Publication runs after the measured window; if the watchdog ends it, `render` reproduces it offline.
    render(args.journal,args.output)


if __name__=='__main__': main()
