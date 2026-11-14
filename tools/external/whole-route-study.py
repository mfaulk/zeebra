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
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT/'tools/external'/(name+'.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def limits():
    return dict(child_wall_seconds=60, rss_bytes=2*1024**3, aggregate_wall_seconds=1800, output_bytes=256*1024**2)


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
        if raw.get('basis') is not None: load('mq10-profile').check_answer(raw,reference)
    if route!='basis':
        if raw['route'] != route or raw['outcome'] not in ('verified-point','no-base-field-point','inconsistent','positive-dimensional','conversion-refusal','recovery-refusal','basis-refusal'):
            raise ValueError('invalid route outcome')
        if raw['outcome']=='verified-point': check_point(raw)
        elif raw['point'] is not None: raise ValueError('unsuccessful route contains point')
    if raw['measured'] != (arm!='stage-off'): raise ValueError('stage mode drift')
    if (raw.get('work') is not None) != (arm=='work'): raise ValueError('work mode drift')


def terminal_kind(exit_code,stop,stderr):
    if stop in ('wall','rss'): return 'incomplete-resource-refusal'
    if exit_code and any(name in stderr for name in ('TooManyNonzeros','TooManyMatrixRows','TooManyMatrixColumns','TooManyBasisElements')):
        return 'incomplete-resource-refusal'
    return 'failed'


def independent_katsura(raw, scratch, guard):
    if raw['problem']!='katsura-11' or raw['modulus']!=2147483647 or raw['digest']!='03bf44d5d614a21cc8f56462aa873b7961641a2341892e3b2ef52b6cfec86a13':
        raise ValueError('new independent reference identity differs')
    script=('option(redSB); ring r=2147483647,('+','.join(raw['input']['variables'])+'),dp; short=0;\n'
            +'ideal I='+','.join(raw['input']['generators'])+'; ideal G=std(I);\n'
            +'ideal B='+','.join(raw['basis'])+'; int ok=(ncols(B)==ncols(G)); int i,j,found;\n'
            +'for(i=1;i<=ncols(B);i++){found=0;for(j=1;j<=ncols(G);j++){if(B[i]==G[j]){found++;}}if(found!=1){ok=0;}}\n'
            +'print("@match "+string(ok)); quit;\n')
    path=scratch/'katsura-11.sing'
    path.write_text(script)
    proof=guard.guarded(['Singular','-q',str(path)],scratch/'katsura-11-proof',60,limits()['rss_bytes'])
    return dict(modulus=raw['modulus'],digest=raw['digest'],basis=raw['basis'],script=script,
                script_sha256=hashlib.sha256(script.encode()).hexdigest(),singular=proof)


def valid_proof(reference):
    proof=reference['singular']
    return (hashlib.sha256(reference['script'].encode()).hexdigest()==reference['script_sha256']
            and not proof['exit'] and not proof['stop'] and '@match 1\n' in proof['stdout'])


def main():
    parser=argparse.ArgumentParser()
    for key in ('binary','scratch','output'): parser.add_argument('--'+key,type=Path,required=True)
    parser.add_argument('--phase',choices=('pilot','native'),default='pilot')
    parser.add_argument('--build-commit',required=True)
    parser.add_argument('--reference-cohort',type=Path)
    args=parser.parse_args()
    if args.output.exists(): parser.error('retain existing campaign and choose new output')
    if subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True).strip(): parser.error('commit instruments before measuring')
    if subprocess.call(['git','diff','--quiet',args.build_commit,'--','src','examples','Cargo.toml','Cargo.lock','.cargo'],cwd=ROOT): parser.error('build tree differs')
    affinity=','.join(map(str,sorted(os.sched_getaffinity(0))))
    if os.environ.get('ZEEBRA_AFFINITY')!=affinity or not os.environ.get('ZEEBRA_MACHINE'): parser.error('declare actual affinity/machine under benchlock')
    args.scratch.mkdir(parents=True,exist_ok=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    cells=list(plan(args.phase))
    campaign_limits=limits()
    if args.phase=='pilot': campaign_limits['aggregate_wall_seconds']=480
    cohort=dict(schema=1,phase=args.phase,identity=dict(commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        build_commit=args.build_commit,binary_sha256=sha(args.binary),cargo_lock_sha256=sha(ROOT/'Cargo.lock'),
        cargo_config_sha256=sha(ROOT/'.cargo/config.toml'),rustc=subprocess.check_output(['rustc','-vV'],text=True),
        machine=os.environ['ZEEBRA_MACHINE'],affinity=affinity,build='release;fat-LTO;one-codegen-unit;x86-64-v3;mold;system allocator;research-work;CARGO_INCREMENTAL=0;RUSTC_WRAPPER empty',
        topology=subprocess.check_output(['lscpu','-e=CPU,CORE,SOCKET,NODE,CACHE,ONLINE'],text=True)),
        limits=campaign_limits,plan=cells,attempts=[],references={})
    refs=load('selective-backward-study').references()
    if args.reference_cohort:
        import gzip
        prior=json.loads(gzip.decompress(args.reference_cohort.read_bytes()))
        for key,reference in prior.get('references',{}).items():
            if valid_proof(reference):
                refs[('katsura-11',2147483647)]=reference
                cohort['references'][key]=reference
    guard=load('grobx-work-study')
    runtime=load('worker-pool-study')
    began=time.monotonic()
    for repeat,problem,modulus,route,arm in cells:
        compilers=runtime.compiler_processes()
        if compilers or os.getloadavg()[0]>4 or time.monotonic()-began>campaign_limits['aggregate_wall_seconds']-60:
            cohort['refusal']=dict(reason='compiler' if compilers else 'load-or-aggregate',compilers=compilers,load=os.getloadavg()[0]);guard.write(args.output,cohort);return
        if sha(args.binary)!=cohort['identity']['binary_sha256']: raise ValueError('binary changed')
        command=[str(args.binary.resolve()),str(modulus),'--problem='+problem]
        if route!='basis': command+=['--whole-route='+route]
        if arm!='stage-off': command+=['--stages']
        if arm=='work': command+=['--work']
        usage=resource.getrusage(resource.RUSAGE_CHILDREN)
        result=guard.guarded(['timeout','--signal=KILL','185',*command],args.scratch/str(len(cohort['attempts'])),60,limits()['rss_bytes'])
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
                if problem=='katsura-11' and (problem,modulus) not in refs:
                    reference=independent_katsura(raw,args.scratch,guard)
                    cohort['references']['katsura-11/2147483647']=reference
                    if valid_proof(reference): refs[(problem,modulus)]=reference
                validate_response(raw,refs.get((problem,modulus)),problem,modulus,route,arm)
                result['status']=('reported-resource-refusal' if raw.get('outcome') in ('basis-refusal','conversion-refusal','recovery-refusal') else
                                  'verified' if (problem,modulus) in refs and route!='direct' else 'complete-needs-independent-basis-check')
        except (ValueError,KeyError,TypeError) as error:
            result.update(status='failed',failure=str(error))
        cohort['attempts'].append(result)
        guard.write(args.output,cohort)
        print(repeat,problem,modulus,route,arm,result['status'],round(result['process_wall_ns']/1e6,2),flush=True)
        if result['status']=='failed': raise RuntimeError('failed validation; raw attempt retained')
        if result['status']=='contaminated': cohort['refusal']=dict(reason='compiler');guard.write(args.output,cohort);return
        if sum(p.stat().st_size for p in args.scratch.iterdir())>limits()['output_bytes']: raise RuntimeError('output budget exceeded; retained attempts')


if __name__=='__main__': main()
