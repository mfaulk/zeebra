#!/usr/bin/env python3
"""Build separately identified GPL research drivers in a private build workspace."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import io
import importlib.util
from instrument import instrument, PIN

HERE = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--source', type=Path, required=True, help='clean local upstream git checkout')
    p.add_argument('--target', type=Path, required=True, help='private buildcache root')
    p.add_argument('--test', action='store_true', help='run driver and hand-computable counter tests')
    p.add_argument('--randomization', action='store_true', help='add isolated #714 feature gates and plain residual checks')
    args = p.parse_args()
    target = args.target.resolve()
    if not str(target).startswith('/buildcache/'):
        p.error('--target must be on /buildcache')
    target.mkdir(parents=True, exist_ok=True)
    source, driver = target / 'source', target / 'driver'
    if source.exists() or driver.exists():
        p.error('source/driver already exist; choose a new private target')
    archive = subprocess.check_output(['git', 'archive', PIN], cwd=args.source)
    source.mkdir()
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        tar.extractall(source, filter='data')
    original = {str(path.relative_to(source)): path.read_bytes() for path in source.rglob('*') if path.is_file()}
    instrument(source)
    shutil.copytree(HERE.parent, driver, ignore=shutil.ignore_patterns('research', 'target'))
    cargo = driver / 'Cargo.toml'
    cargo.write_text(cargo.read_text().replace(
        '{ git = "https://github.com/code1-de/grobx", rev = "' + PIN + '" }',
        '{ path = "../source" }', 1).replace(
        '{ git = "https://github.com/code1-de/grobx", rev = "' + PIN + '" }',
        '{ path = "../source/checker" }', 1))
    main = driver / 'src/main.rs'
    s = main.read_text()
    old = '    let outcome = grobx::groebner(&text, &params).map_err(|e| e.to_string())?;'
    assert s.count(old) == 1
    s = s.replace(old, '''    let enabled = input["research_work"].as_bool().unwrap_or(false);
    if enabled && modulus >= (1 << 31) { return Err("research counters cover Gf31 only".into()); }
    let (outcome, work) = grobx::research_work::capture(enabled, || grobx::groebner(&text, &params));
    let outcome = outcome.map_err(|e| e.to_string())?;''')
    s = s.replace('    output["solve_ns"] = json!(solve_ns);',
        '    output["solve_ns"] = json!(solve_ns);\n    output["work"] = work.map_or(Value::Null, |s| s.json());\n    output["research_identity"] = json!(include_str!("../research-identity.json"));')
    s = s.replace('\"contract\":1,\"revision\":REVISION,', '\"contract\":1,\"research_identity\":include_str!(\"../research-identity.json\"),\"revision\":REVISION,')
    s += '\n' + (HERE / 'driver-tests.rs').read_text()
    main.write_text(s)
    if args.randomization:
        spec = importlib.util.spec_from_file_location('randomization_overlay', HERE / 'randomization/overlay.py')
        overlay = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(overlay)
        overlay.apply(source, driver)
    # Hash all changed upstream bytes and the original instrumentation recipe, never just the pin.
    patch = {str(path.relative_to(source)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in source.rglob('*') if path.is_file()
        and original.get(str(path.relative_to(source))) != path.read_bytes()}
    recipes = ['instrument.py', 'work.rs', 'driver-tests.rs', 'provision.py']
    if args.randomization:
        recipes += ['randomization/overlay.py', 'randomization/policy.rs', 'randomization/driver-tests.rs']
    identity = {'upstream_revision': PIN, 'modified_upstream_files': patch,
        'recipe': {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
            for name in recipes}}
    identity['digest'] = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    (driver / 'research-identity.json').write_text(json.dumps(identity, sort_keys=True, indent=2) + '\n')
    build = driver / 'build.rs'
    b = build.read_text().replace('        "build.rs",', '        "build.rs",\n        "research-identity.json",')
    build.write_text(b)
    env = dict(os.environ, CARGO_TARGET_DIR=str(target / 'build'), TMPDIR=str(target / 'tmp'),
        RUSTC_WRAPPER='', RUSTFLAGS='-C target-cpu=x86-64-v3',
        CARGO_PROFILE_RELEASE_LTO='fat', CARGO_PROFILE_RELEASE_CODEGEN_UNITS='1')
    (target / 'tmp').mkdir(exist_ok=True)
    subprocess.run(['cargo', 'build', '--release', '--offline'], cwd=driver, env=env, check=True)
    if args.test:
        subprocess.run(['cargo', 'test', '--locked', '--offline'], cwd=driver, env=env, check=True)
        subprocess.run(['cargo', 'test', '--locked', '--manifest-path', str(source / 'Cargo.toml'),
                        '--lib', 'research_work::tests'], cwd=driver, env=env, check=True)
        if args.randomization:
            subprocess.run(['cargo', 'test', '--locked', '--manifest-path', str(source / 'Cargo.toml'),
                            '--lib', 'research_random::tests'], cwd=driver, env=env, check=True)
    print(json.dumps({'binary': str(target / 'build/release/grobx-driver'), 'identity': identity}, indent=2))


if __name__ == '__main__':
    main()
