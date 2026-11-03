"""Audit the pinned Mathlib once per Mathlib version and record the result.

The routine proof check trusts Mathlib after this audit. The audit applies the same standard as the
project's own proofs: only the reviewed axioms (verification/allowed_axioms.json) may occur, the Lean
kernel replays everything (leanchecker), and an independent kernel (nanoda) checks the exported
declarations. Run it again, and commit the new log entry, whenever lake-manifest.json pins another
Mathlib revision or lean-toolchain changes, or when the module list grows.

  python3 tools/audit_mathlib.py [--modules verification/mathlib_audit_modules.txt]
"""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
LOG = ROOT / 'verification/mathlib_audit_log.json'
# Axioms of the Lean distribution itself that only its own internals mention (`Lean.trustCompiler` in the
# definitions of `Lean.reduceBool`, `lcProof` in unsafe compiler helpers). They are accepted as part of the
# environment when every constant mentioning them belongs to the core modules. The axioms that would let a
# proof use them (`Lean.ofReduceBool`, `sorryAx`) must be mentioned by nothing in Mathlib and its packages.
CORE_MODULES = ('Init', 'Std', 'Lean')


def pinned():
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    return {'mathlib_rev': mathlib['rev'], 'mathlib_input_rev': mathlib['inputRev'],
            'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip()}


def strip_axioms(source, destination, permitted):
    """Drop every exported axiom declaration that is not permitted.

    A theorem that depends on a dropped axiom (sorryAx, Lean.ofReduceBool, ...) then refers to an unknown
    constant, so the independent kernel rejects it instead of accepting an unreviewed assumption.
    """
    names = {}
    dropped = []
    kept = 0
    with open(source) as reader, open(destination, 'w') as writer:
        for line in reader:
            if line.startswith('{"in":'):
                record = json.loads(line)
                if 'str' in record:
                    names[record['in']] = (record['str']['pre'], record['str']['str'])
            elif line.startswith('{"axiom":'):
                identity = json.loads(line)['axiom']['name']
                parts = []
                while identity:
                    identity, part = names[identity]
                    parts.append(part)
                name = '.'.join(reversed(parts))
                if name not in permitted:
                    dropped.append(name)
                    continue
                kept += 1
            writer.write(line)
    return kept, sorted(dropped)


def sha256(path):
    digest = hashlib.sha256()
    with open(path, 'rb') as handle:
        for block in iter(lambda: handle.read(1 << 20), b''):
            digest.update(block)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--modules', default=str(ROOT / 'verification/mathlib_audit_modules.txt'))
    parser.add_argument('--threads', type=int, default=4)
    args = parser.parse_args()
    modules = [line.strip() for line in Path(args.modules).read_text().splitlines()
               if line.strip() and not line.startswith('#')]
    if not modules or not all(re.fullmatch(r'Mathlib(\.[A-Za-z_][A-Za-z_0-9]*)*', m) for m in modules):
        raise SystemExit('the module list must contain Mathlib module names')
    info = pinned()
    permitted = {entry['name'] for entry in json.loads((ROOT / 'verification/allowed_axioms.json').read_text())['axioms']}
    local_lake = ROOT / '.tools/elan/bin/lake'
    lake = str(local_lake) if local_lake.is_file() else shutil.which('lake')
    exporter = ROOT / '.tools/lean4export/.lake/build/bin/lean4export'
    nanoda = ROOT / '.tools/nanoda_lib/target/release/nanoda_bin'
    env = os.environ.copy()
    if local_lake.is_file():
        env['ELAN_HOME'] = str(ROOT / '.tools/elan')
    env.pop('LEAN_PATH', None)
    env['LEAN_ABORT_ON_PANIC'] = '1'
    with tempfile.TemporaryDirectory(prefix='mathlib-audit-') as directory:
        scratch = Path(directory)
        (scratch / 'lakefile.toml').write_text('name = "mathlib_audit"\ndefaultTargets = ["AuditRoot"]\n\n'
            '[[require]]\nname = "mathlib"\nscope = "leanprover-community"\n'
            f'rev = "{info["mathlib_input_rev"]}"\n\n[[lean_lib]]\nname = "AuditRoot"\n')
        shutil.copyfile(ROOT / 'lake-manifest.json', scratch / 'lake-manifest.json')
        shutil.copyfile(ROOT / 'lean-toolchain', scratch / 'lean-toolchain')
        (scratch / '.lake').mkdir()
        (scratch / '.lake/packages').symlink_to(ROOT / '.lake/packages', target_is_directory=True)
        (scratch / 'AuditRoot.lean').write_text(''.join(f'import {m}\n' for m in modules))
        run = lambda command, **kwargs: subprocess.run(command, cwd=scratch, env=env, check=True, **kwargs)
        run([lake, 'build'])
        listing = run([lake, 'env', 'lean', '--run', str(ROOT / 'verification/ListModules.lean'), 'AuditRoot'],
                      capture_output=True, text=True).stdout.split()
        covered = sorted(m for m in listing if m.startswith(('Mathlib', 'Batteries', 'Aesop', 'Qq', 'Plausible',
                         'ProofWidgets', 'ImportGraph', 'LeanSearchClient', 'Cli')))
        print(f'{len(listing)} modules in the import closure, {len(covered)} of them from Mathlib and its packages')
        users = run([lake, 'env', 'lean', '--run', str(ROOT / 'verification/AxiomUsers.lean'), 'AuditRoot', *sorted(permitted)],
                    capture_output=True, text=True).stdout.splitlines()
        parsed = [re.fullmatch(r'(\S+) <- (\S+) @ (\S+)( unsafe)?', line) for line in users]
        if any(m is None for m in parsed):
            raise SystemExit('unexpected output from AxiomUsers')
        # Safe declarations cannot refer to unsafe ones (the kernel enforces it), and the project's own check
        # rejects any proof that depends on an unsafe declaration, so unsafe users are unreachable.
        outside = sorted(f'{m[1]} <- {m[2]} @ {m[3]}' for m in parsed
                         if m[3].split('.')[0] not in CORE_MODULES and m[4] is None)
        if outside:
            raise SystemExit('constants outside the Lean core depend on unreviewed axioms:\n' + '\n'.join(outside[:50]))
        environment_axioms = {m[1] for m in parsed}
        print(f'axioms mentioned only by Lean core internals: {sorted(environment_axioms)}')
        run([lake, 'env', 'leanchecker', '--fresh', 'AuditRoot'])
        raw = scratch / 'audit.ndjson'
        with raw.open('w') as output:
            run([lake, 'env', str(exporter), 'AuditRoot'], stdout=output)
        stripped = scratch / 'audit-stripped.ndjson'
        kept, dropped = strip_axioms(raw, stripped, permitted | environment_axioms)
        print(f'axioms kept: {kept}; dropped from the export: {dropped}')
        export_digest = sha256(stripped)
        config = scratch / 'nanoda.json'
        config.write_text(json.dumps({'export_file_path': str(stripped), 'permitted_axioms': sorted(permitted | environment_axioms),
            'unpermitted_axiom_hard_error': True, 'unsafe_permit_all_axioms': False, 'nat_extension': True,
            'string_extension': True, 'num_threads': args.threads, 'print_success_message': True,
            'print_axioms': False}))
        result = subprocess.run([str(nanoda), str(config)], cwd=scratch, env=env, capture_output=True, text=True)
        if result.returncode:
            raise SystemExit(f'independent kernel failed ({result.returncode}):\n{result.stdout[-2000:]}\n{result.stderr[-3000:]}')
        match = re.fullmatch(r'Checked ([1-9][0-9]*) declarations with no errors\s*', result.stdout)
        if match is None:
            raise SystemExit(f'independent kernel did not report a clean check: {result.stdout}')
        print(result.stdout.strip())
        entry = dict(info, modules=modules, covered_modules=covered, leanchecker='passed', nanoda='passed',
                     declarations_checked=int(match.group(1)), axioms_kept=kept, axioms_dropped=dropped, environment_axioms=sorted(environment_axioms),
                     export_sha256=export_digest, date=datetime.date.today().isoformat(),
                     nanoda_commit=subprocess.check_output(['git', '-C', str(ROOT / '.tools/nanoda_lib'), 'rev-parse', 'HEAD'],
                                                          text=True).strip(),
                     lean4export_commit=subprocess.check_output(['git', '-C', str(ROOT / '.tools/lean4export'), 'rev-parse', 'HEAD'],
                                                               text=True).strip())
    log = json.loads(LOG.read_text()) if LOG.is_file() else {'schema_version': 1, 'entries': []}
    log['entries'].append(entry)
    LOG.write_text(json.dumps(log, indent=2, ensure_ascii=False) + '\n')
    print(f'logged in {LOG.relative_to(ROOT)}')


if __name__ == '__main__':
    main()
