"""Fetch pinned tools separately, then build both checkers without networking."""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
TOOLS = [
    ('lean4export', 'https://github.com/leanprover/lean4export.git',
     '076e8e57707e813375e8f9da8bf989799ace9680'),
    ('nanoda_lib', 'https://github.com/ammkrn/nanoda_lib.git',
     '418320295890faed83a96fd97907b12a3b6728c2'),
]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fetch', action='store_true', help='network preparation only; never called by tests')
    args = parser.parse_args()
    env = os.environ.copy()
    local_lake = ROOT / '.tools/elan/bin/lake'
    lake = str(local_lake) if local_lake.is_file() else shutil.which('lake')
    if local_lake.is_file():
        env['ELAN_HOME'] = str(ROOT / '.tools/elan')
    env['LEAN_ABORT_ON_PANIC'] = '1'
    env['LEAN_NUM_THREADS'] = '2'
    for name, url, revision in TOOLS:
        destination = ROOT / '.tools' / name
        if args.fetch and not destination.exists():
            destination.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(['git', 'clone', '--no-checkout', url, str(destination)], check=True)
            subprocess.run(['git', '-C', str(destination), 'checkout', '--detach', revision], check=True)
        head = subprocess.check_output(['git', '-C', str(destination), 'rev-parse', 'HEAD'], text=True).strip()
        if head != revision:
            raise ValueError(f'{name}: expected pinned revision {revision}, found {head}')
        changed = subprocess.check_output(['git', '-C', str(destination), 'diff', 'HEAD', '--name-only'], text=True).splitlines()
        if set(changed) - ({'lean-toolchain'} if name == 'lean4export' else set()):
            raise ValueError(f'{name}: checker source differs from pinned revision')
    exporter = ROOT / '.tools/lean4export'
    (exporter / 'lean-toolchain').write_text((ROOT / 'lean-toolchain').read_text())
    if args.fetch:
        subprocess.run(['cargo', 'fetch', '--manifest-path', str(ROOT / '.tools/nanoda_lib/Cargo.toml'), '--locked'], check=True)
        print('checker sources and dependencies fetched; run again without --fetch for offline build')
        return
    if lake is None:
        raise RuntimeError('lake is required')
    offline = [sys.executable, str(ROOT / 'tools/offline.py')]
    subprocess.run([*offline, lake, '-d', str(exporter), 'build'], cwd=ROOT, env=env, check=True)
    subprocess.run([*offline, 'cargo', 'build', '--manifest-path', str(ROOT / '.tools/nanoda_lib/Cargo.toml'),
                    '--locked', '--release', '--offline'], cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
