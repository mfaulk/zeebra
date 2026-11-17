#!/usr/bin/env python3
"""Freeze #834's source and executable identities: every timed binary's path, SHA-256 and version."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PREFIX = Path(os.environ.get('ZEEBRA_EXT_PREFIX', str(Path.home() / '.local/opt/zeebra-ext')))


def sh(*cmd):
    r = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT)
    return (r.stdout + r.stderr).strip()


def identity(path, version_args=None, version_lines=3):
    p = Path(path) if path else None
    if p is None or not p.exists():
        return dict(path=str(path), present=False)
    real = p.resolve()
    out = dict(path=str(p), resolved=str(real), present=True, bytes=real.stat().st_size,
               sha256=hashlib.sha256(real.read_bytes()).hexdigest())
    if version_args is not None:
        out['version'] = '\n'.join(sh(str(p), *version_args).splitlines()[:version_lines])
    return out


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--bin', type=Path, required=True)
    p.add_argument('--exporter', type=Path, required=True)
    a = p.parse_args()
    manifests = sorted((PREFIX / 'julia-depot/environments').glob('*/Manifest.toml'))
    doc = dict(
        schema=1,
        zeebra=dict(
            head=sh('git', 'rev-parse', 'HEAD'),
            origin_main=sh('git', 'rev-parse', 'origin/main'),
            merge_base=sh('git', 'merge-base', 'HEAD', 'origin/main'),
            # The instrument adds examples, tools and research files only; production source must not move.
            production_diff_vs_merge_base=sh('git', 'diff', '--stat', 'origin/main...HEAD', '--', 'src', 'Cargo.lock'),
            rustc=sh('rustc', '-vV'),
            build='release; fat LTO; codegen-units=1; x86-64-v3 (.cargo/config.toml); RUSTC_WRAPPER=""; CARGO_INCREMENTAL=0',
            executables={name: identity(a.bin / name) for name in
                         ('m29_cost_model', 'm29_cost_model_work', 'zeebra_driver', 'wide_corpus')},
            input_exporter=identity(a.exporter),
        ),
        comparands=dict(
            msolve=identity(shutil.which('msolve'), ['-h'], 1),
            grobx_driver=identity(a.bin / 'grobx-driver', ['--version'], 1),
            groebner_rs_driver=identity(a.bin / 'groebner-rs-driver', ['--version'], 1),
            julia=identity(shutil.which('julia'), ['--version'], 1),
            julia_manifests={str(m): hashlib.sha256(m.read_bytes()).hexdigest() for m in manifests},
            singular=identity(shutil.which('Singular'), ['--version'], 1),
            sagebrush_gb_driver=identity(PREFIX / 'bin/sagebrush-gb-driver'),
            grobx_driver_source=sh('git', 'log', '-1', '--format=%H', '--', 'tools/external/grobx-driver'),
            groebner_rs_driver_source=sh('git', 'log', '-1', '--format=%H', '--', 'tools/external/groebner-driver'),
        ),
        host=dict(
            machine='5995wx',
            cpu=next((l.split(':', 1)[1].strip() for l in Path('/proc/cpuinfo').read_text().splitlines()
                      if l.startswith('model name')), 'unknown'),
            kernel=platform.release(),
            governor=Path('/sys/devices/system/cpu/cpu8/cpufreq/scaling_governor').read_text().strip(),
            boost=Path('/sys/devices/system/cpu/cpufreq/boost').read_text().strip(),
            scaling_driver=Path('/sys/devices/system/cpu/cpu8/cpufreq/scaling_driver').read_text().strip(),
        ),
    )
    print(json.dumps(doc, indent=1, sort_keys=True))


if __name__ == '__main__':
    main()
