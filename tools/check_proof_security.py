"""Check source, axioms, specification integrity and two kernels offline."""

import argparse
import gc
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

from offline import disable_network
from proof_security import (ROOT, audit_axiom_definitions, audit_contract, audit_mathlib_coverage,
    audit_dependencies, audit_source, changed_axiom_entries, contract_dependents, load_contracts, load_policy)
from public import registry

BUILTINS = ['Nat', 'String', 'String.mk', 'Char', 'Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind',
    'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div', 'Nat.mod', 'Nat.beq',
    'Nat.ble', 'Nat.land', 'Nat.lor', 'Nat.xor', 'Nat.shiftLeft', 'Nat.shiftRight',
    'String.ofList', 'Char.ofNat', 'List', 'eagerReduce']


def run(command, cwd, env, **kwargs):
    return subprocess.run(command, cwd=cwd, env=env, check=True, **kwargs)


def check_independent_kernel(nanoda, config, scratch, env):
    # Keep diagnostics even when a checker aborts before printing its result.
    # File-backed output also makes a long-running checker observable.
    stdout = scratch / 'nanoda.stdout.log'
    stderr = scratch / 'nanoda.stderr.log'
    with stdout.open('w') as out, stderr.open('w') as err:
        result = subprocess.run([str(nanoda), str(config)], cwd=scratch, env=env,
                                stdout=out, stderr=err)
    if result.returncode:
        raise RuntimeError(f'independent kernel exited {result.returncode}; '
                           f'diagnostics: {stderr}\n{stderr.read_text()[-8000:]}')
    message = stdout.read_text()
    if not re.fullmatch(r'Checked [1-9][0-9]* declarations with no errors\s*', message):
        raise ValueError(f'independent kernel did not report a clean check: {message}')
    return message.strip()


def compact_replay_targets(modules):
    """Keep the same leanchecker prefix coverage with fewer filesystem scans."""
    targets = []
    for name in sorted(set(modules)):
        if not any(name.startswith(parent + '.') for parent in targets):
            targets.append(name)
    return targets


def prune_stale_olean_parts(build_root, sources, retired_root):
    """Archive generated project modules that no longer have screened sources."""
    removed = []
    archive = None
    if not build_root.is_dir():
        return removed
    for path in sorted(build_root.rglob('*')):
        if not path.is_file():
            continue
        relative = path.relative_to(build_root)
        for suffix in ('.olean.private', '.olean.server', '.olean', '.ilean'):
            if not relative.name.endswith(suffix):
                continue
            stem = relative.name[:-len(suffix)]
            if relative.parts[0] != 'Proofs' and not (relative.parent == Path('.') and stem == 'Proofs'):
                break
            source = relative.with_name(stem + '.lean')
            if source not in sources:
                if archive is None:
                    retired_root.mkdir(parents=True, exist_ok=True)
                    archive = Path(tempfile.mkdtemp(prefix='stale-', dir=retired_root))
                destination = archive / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                path.rename(destination)
                removed.append(relative)
            break
    return removed


# The scratch project is kept between runs so that Lake rebuilds only the proof modules whose source changed. Lake
# decides by the content hash of each source file and its imports, so every artifact in it still comes from a source
# that this script copied and screened (audit_source) in the same run. Stale compiled modules are also removed:
# leanchecker scans module prefixes and could otherwise discover deleted files outside Proofs.lean's imports.
SCRATCH = ROOT / '.cache/proof-security-scratch'
MODULE_CACHE = ROOT / '.cache/proof-security-modules.json'


def sync_file(source, destination):
    data = source.read_bytes()
    if not destination.is_file() or destination.read_bytes() != data:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)


def sync_scratch(manifest_text, lakefile_text):
    SCRATCH.mkdir(parents=True, exist_ok=True)
    wanted = set()
    for source in sorted((ROOT / 'Proofs').rglob('*.lean')):
        relative = source.relative_to(ROOT)
        wanted.add(relative)
        sync_file(source, SCRATCH / relative)
    for stale in sorted((SCRATCH / 'Proofs').rglob('*.lean')):
        if stale.relative_to(SCRATCH) not in wanted:
            stale.unlink()
    for filename in ['Proofs.lean', 'lean-toolchain']:
        sync_file(ROOT / filename, SCRATCH / filename)
    removed = prune_stale_olean_parts(SCRATCH / '.lake/build/lib/lean', wanted | {Path('Proofs.lean')},
                                     SCRATCH.parent / 'proof-security-retired')
    if removed:
        print(f'archived {len(removed)} stale compiled project part(s)', flush=True)
    for filename, text in [('lake-manifest.json', manifest_text), ('lakefile.toml', lakefile_text)]:
        target = SCRATCH / filename
        if not target.is_file() or target.read_text() != text:
            target.write_text(text)
    (SCRATCH / '.lake').mkdir(exist_ok=True)
    packages = SCRATCH / '.lake/packages'
    if not packages.is_symlink():
        packages.symlink_to(ROOT / '.lake/packages', target_is_directory=True)


def project_modules():
    """Proof modules with the hash of their source and, transitively, of the proof modules they import."""
    sources = {}
    for path in [ROOT / 'Proofs.lean', *sorted((ROOT / 'Proofs').rglob('*.lean'))]:
        name = 'Proofs' if path.name == 'Proofs.lean' else '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        text = path.read_text()
        sources[name] = (text, re.findall(r'^import\s+(Proofs(?:\.[A-Za-z_0-9]+)*)\s*$', text, flags=re.M))
    keys = {}

    def key(name):
        if name not in keys:
            text, imports = sources[name]
            digest = hashlib.sha256(text.encode())
            for dependency in sorted(imports):
                digest.update(key(dependency).encode())
            keys[name] = digest.hexdigest()
        return keys[name]

    return {name: key(name) for name in sources}


def mathlib_base_key():
    """What the full replay of imported libraries (Mathlib) depends on; it is redone only when this changes."""
    digest = hashlib.sha256()
    for filename in ['lean-toolchain', 'lake-manifest.json', 'verification/mathlib_audit_modules.txt']:
        digest.update((ROOT / filename).read_bytes())
    return digest.hexdigest()


def stage(label, started):
    print(f'[{time.monotonic() - started:7.1f}s] {label}', flush=True)


def build_screened_sources(lake, env, started):
    """Build screened sources without consuming repository project artifacts."""
    for source in [ROOT / 'Proofs.lean', *sorted((ROOT / 'Proofs').rglob('*.lean'))]:
        audit_source(source)
    manifest_text = (ROOT / 'lake-manifest.json').read_text()
    manifest = json.loads(manifest_text)
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    lakefile_text = ('name = "proof_security"\n'
        'defaultTargets = ["Proofs"]\n\n[[require]]\nname = "mathlib"\nscope = "leanprover-community"\n'
        f'rev = "{mathlib["inputRev"]}"\n\n[[lean_lib]]\nname = "Proofs"\n'
        'leanOptions = {linter.unusedSimpArgs = false}\n')
    sync_scratch(manifest_text, lakefile_text)
    stage('sources synchronised', started)
    # Only sources and shared dependencies enter scratch. No repository
    # project oleans or Lake traces are copied into the independent build.
    run([lake, 'build'], SCRATCH, env)
    stage('scratch build finished', started)


def publish_test_imports(build_root, destination, sources, retired_root):
    """Copy compiled imports out of scratch; never copy build traces or hashes."""
    artifacts = []
    absent_parts = []
    for source in sorted(sources):
        stem = source.with_suffix('')
        compiled = build_root / stem.with_suffix('.olean')
        if not compiled.is_file():
            raise RuntimeError(f'screened build is missing {compiled}')
        for suffix in ('.olean', '.olean.private', '.olean.server', '.ilean'):
            relative = stem.with_suffix(suffix)
            path = build_root / relative
            if path.is_file():
                artifacts.append((path, relative))
            else:
                absent_parts.append(relative)
    prune_stale_olean_parts(destination, sources, retired_root)
    # A live module can stop emitting a private/server part after an edit.
    # Do not leave an old part available to the test compiler in that case.
    archive = None
    for relative in absent_parts:
        target = destination / relative
        if target.exists() or target.is_symlink():
            if archive is None:
                retired_root.mkdir(parents=True, exist_ok=True)
                archive = Path(tempfile.mkdtemp(prefix='parts-', dir=retired_root))
            retired = archive / relative
            retired.parent.mkdir(parents=True, exist_ok=True)
            target.rename(retired)
    for source, relative in artifacts:
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        # Replace atomically rather than writing through an old file symlink.
        with tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as output:
            temporary = Path(output.name)
        try:
            shutil.copyfile(source, temporary)
            shutil.copymode(source, temporary)
            temporary.replace(target)
        finally:
            temporary.unlink(missing_ok=True)


def prepare_test_imports():
    """Prepare imports only. The full audit must still run after the tests."""
    disable_network()
    started = time.monotonic()
    local_lake = ROOT / '.tools/elan/bin/lake'
    lake = str(local_lake) if local_lake.is_file() else shutil.which('lake')
    if lake is None:
        raise RuntimeError('lake is required for proof imports')
    env = os.environ.copy()
    if local_lake.is_file():
        env['ELAN_HOME'] = str(ROOT / '.tools/elan')
    env.pop('LEAN_PATH', None)
    env['LEAN_ABORT_ON_PANIC'] = '1'
    build_screened_sources(lake, env, started)
    sources = {Path('Proofs.lean'), *(p.relative_to(ROOT) for p in (ROOT / 'Proofs').rglob('*.lean'))}
    publish_test_imports(SCRATCH / '.lake/build/lib/lean', ROOT / '.lake/build/lib/lean',
                         sources, ROOT / '.cache/proof-test-retired')
    print('test imports prepared from screened build; full proof audit still required', flush=True)


def main():
    started = time.monotonic()
    disable_network()
    entries = load_policy(ROOT / 'verification/allowed_axioms.json')
    contracts = load_contracts(ROOT / 'verification/stl_contracts.json')
    permitted = entries + [{**c, 'reason': c['reason']} for c in contracts]
    contract = json.loads((ROOT / 'verification/statements.json').read_text())
    sources = [ROOT / 'Proofs.lean', *sorted((ROOT / 'Proofs').rglob('*.lean'))]
    for path in sources:
        audit_source(path)
    local_lake = ROOT / '.tools/elan/bin/lake'
    lake = str(local_lake) if local_lake.is_file() else shutil.which('lake')
    if lake is None:
        raise RuntimeError('lake is required for proof security checks')
    exporter = ROOT / '.tools/lean4export/.lake/build/bin/lean4export'
    nanoda = ROOT / '.tools/nanoda_lib/target/release/nanoda_bin'
    if not exporter.is_file() or not nanoda.is_file():
        raise RuntimeError('prepare pinned lean4export and nanoda first: tools/prepare_proof_checkers.py')
    env = os.environ.copy()
    if local_lake.is_file():
        env['ELAN_HOME'] = str(ROOT / '.tools/elan')
    env.pop('LEAN_PATH', None)
    env['LEAN_ABORT_ON_PANIC'] = '1'
    env['LEAN_NUM_THREADS'] = '2'
    if True:
        scratch = SCRATCH
        build_screened_sources(lake, env, started)
        listing = run([lake, 'env', 'lean', '--run', str(ROOT / 'verification/ListModules.lean'), 'Proofs'],
                      scratch, env, capture_output=True, text=True).stdout.split()
        covered = audit_mathlib_coverage(listing)
        stage('module listing and Mathlib coverage', started)
        print(f'{covered} imported modules of Mathlib and its packages are covered by the recorded audit')
        # Preserve the expensive inspection on failures and avoid retaining
        # its full text in memory alongside the parsed declaration table.
        environment_dump = scratch / 'environment.jsonl'
        with environment_dump.open('w') as output:
            run([lake, 'env', 'lean', '--run', str(ROOT / 'verification/InspectEnvironment.lean'),
                 'Proofs', *[entry['name'] for entry in permitted]],
                scratch, env, stdout=output, text=True)
        stage('environment inspected', started)
        rows = {}
        with environment_dump.open() as source:
            for line in source:
                row = json.loads(line)
                if row['name'] in rows:
                    raise ValueError('duplicate environment declarations')
                rows[row['name']] = row
        proof_modules = {entry['proof'].removesuffix('.lean').replace('/', '.')
                         for entry in registry().values()}
        expected_roots = sorted(name for name, row in rows.items()
            if row['kind'] == 'theorem' and row['module'] in proof_modules
            and name.startswith('Proofs.'))
        if contract['roots'] != expected_roots:
            missing = sorted(set(contract['roots']) - set(expected_roots))
            added = sorted(set(expected_roots) - set(contract['roots']))
            raise ValueError('public theorem declarations and reviewed contract roots differ; '
                             f'missing={missing}; added={added}')
        cache_path = ROOT / '.cache/axiom-definitions.json'
        try:
            cached = json.loads(cache_path.read_text())
        except (OSError, ValueError):
            cached = {}
        changed_entries, keys = changed_axiom_entries(permitted, rows, cached)
        if changed_entries:
            audit_axiom_definitions(changed_entries, rows)
            print('changed allowed axiom definitions checked: ' + ', '.join(entry['name'] for entry in changed_entries))
        else:
            print('allowed axiom definitions unchanged: definition audit skipped')
        stage('rows parsed, roots compared', started)
        count = audit_dependencies(permitted, rows)
        dependents = contract_dependents(contracts, rows)
        print(f'{len(dependents)} theorem(s) are proved under an STL contract' + (': ' + ', '.join(dependents[:5]) if dependents else ''))
        stage('dependency audit', started)
        audit_contract(contract, rows)
        print(f'raw axiom dependency and statement/definition checks passed: {count} declarations')
        unsupported_roots = [name for name, row in rows.items()
            if row['module'].startswith('Proofs') and name.startswith('Proofs.') and not row['internal']
            and not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', name)]
        if unsupported_roots:
            raise ValueError(f'unsupported public export names: {unsupported_roots}')
        roots = [name for name, row in rows.items() if row['module'].startswith('Proofs')
                 and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', name)]
        # No later phase needs declaration bodies. In particular, do not keep
        # them alive while either kernel builds its own expression tables.
        del rows
        gc.collect()
        stage('environment audits finished', started)
        # Kernel replay. Imported libraries (Mathlib, reviewed once per version) are replayed in full only when the
        # toolchain, the Mathlib pin or the audited module list changes. Otherwise replay prefixes covering
        # the changed proof modules; the aggregate Proofs prefix also includes unchanged project modules.
        modules = project_modules()
        base_key = mathlib_base_key()
        try:
            module_cache = json.loads(MODULE_CACHE.read_text())
        except (OSError, ValueError):
            module_cache = {}
        if module_cache.get('base') != base_key:
            stage('full kernel replay started', started)
            run([lake, 'env', 'leanchecker', '--verbose', '--fresh', 'Proofs'], scratch, env)
            stage('full kernel replay finished', started)
        else:
            recorded = module_cache.get('modules', {})
            to_replay = sorted(name for name, digest in modules.items() if recorded.get(name) != digest)
            # leanchecker scans its search path once per prefix. Proofs covers
            # all its descendants already; repeating them does not add checks.
            targets = compact_replay_targets(to_replay)
            if targets:
                stage(f'kernel replay started: {len(to_replay)} changed module(s), '
                      f'{len(targets)} covering prefix(es)', started)
                run([lake, 'env', 'leanchecker', '--verbose', *targets], scratch, env)
            stage(f'kernel replay of {len(to_replay)} changed module(s) finished', started)
        stage('export started', started)
        export = scratch / 'proofs.ndjson'
        with export.open('w') as output:
            run([lake, 'env', str(exporter), 'Proofs', '--', *BUILTINS,
                 *[entry['name'] for entry in permitted], *roots], scratch, env, stdout=output)
        config = scratch / 'nanoda.json'
        config.write_text(json.dumps({'export_file_path': str(export),
            'permitted_axioms': [entry['name'] for entry in permitted],
            'unpermitted_axiom_hard_error': True, 'unsafe_permit_all_axioms': False,
            'nat_extension': True, 'string_extension': True, 'num_threads': 2,
            'print_success_message': True, 'print_axioms': False}))
        stage('export finished; independent kernel started', started)
        print(check_independent_kernel(nanoda, config, scratch, env))
        stage('independent kernel finished', started)
        MODULE_CACHE.parent.mkdir(parents=True, exist_ok=True)
        MODULE_CACHE.write_text(json.dumps({'base': base_key, 'modules': modules}) + '\n')
        # Failed dependency/statement/kernel checks never persist an audit result.
        if not isinstance(cached, dict) or cached.get('keys') != keys:
            cache_path.parent.mkdir(parents=True, exist_ok=True)
            cache_path.write_text(json.dumps({'keys': keys}) + '\n')
    print('proof security checks passed')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare-test-imports', action='store_true',
                        help='build screened test imports; does not perform the proof audit')
    args = parser.parse_args()
    if args.prepare_test_imports:
        prepare_test_imports()
    else:
        main()
