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
from proof_security import (MATHLIB_FAMILY, ROOT, audit_axiom_definitions, audit_contract, audit_mathlib_coverage,
    audit_dependencies, audit_source, changed_axiom_entries, load_policy)
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


# Kinds whose declarations cannot reference each other in a cycle (the kernel admits a theorem, definition,
# opaque or axiom only after everything it uses). Inductive blocks are never dropped: an inductive and its
# constructors reference each other.
ACYCLIC_KINDS = {'theorem', 'definition', 'opaque', 'axiom'}


EXPORT_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def project_export_names(rows):
    """Select exporter-readable names, rejecting unsupported public names.

    Apostrophes are Lean identifier characters. Roots are passed as subprocess
    arguments to lean4export's name-literal parser, never through a shell.
    """
    unsupported = [name for name, row in rows.items()
        if row['module'].startswith('Proofs') and name.startswith('Proofs.')
        and not row['internal'] and not EXPORT_NAME.fullmatch(name)]
    if unsupported:
        raise ValueError(f'unsupported public export names: {unsupported}')
    return [name for name, row in rows.items()
            if row['module'].startswith('Proofs') and EXPORT_NAME.fullmatch(name)]


def export_roots(names, rows):
    """A subset of `names` whose export closure contains all of `names`.

    lean4export dumps every constant that occurs in the type or value of a dumped declaration, so a theorem,
    definition, opaque or axiom used by another safe declaration of `names` need not be passed itself. This
    keeps the exporter's argument list within the operating system's limit as the proof library grows;
    `exported_names` checks afterwards that the export still contains every name.
    """
    used = set()
    for name in names:
        row = rows[name]
        if not row['unsafe']:
            used.update(dependency for dependency in row['dependencies'] if dependency != name)
    return [name for name in names if not (rows[name]['kind'] in ACYCLIC_KINDS and name in used)]


def exported_names(path):
    """The names of the declarations in a lean4export NDJSON file."""
    parts = {0: None}
    declared = []
    with path.open() as export:
        for line in export:
            item = json.loads(line)
            if 'in' in item and 'str' in item:
                parts[item['in']] = (item['str']['pre'], item['str']['str'])
            elif 'in' in item and 'num' in item:
                parts[item['in']] = (item['num']['pre'], str(item['num']['i']))
            for kind in ('axiom', 'def', 'thm', 'opaque', 'quot'):
                if kind in item:
                    declared.append(item[kind]['name'])
            if 'inductive' in item:
                block = item['inductive']
                declared.extend(entry['name'] for group in ('types', 'ctors', 'recs') for entry in block[group])
    def render(index):
        components = []
        while parts.get(index) is not None:
            index, component = parts[index]
            components.append(component)
        return '.'.join(reversed(components))
    return {render(index) for index in declared}


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


def replay_required_modules(changed, imported, declaration_owners):
    """An imported module with no owned constants has no expressions to replay.

    Ownership and the loaded module list come from the screened build. Modules
    not in that loaded environment remain targets: absence of observations is
    not evidence of an empty module. Independent export/kernel coverage is unchanged.
    """
    imported = set(imported)
    declaration_owners = set(declaration_owners)
    return [name for name in changed if name not in imported or name in declaration_owners]


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
    permitted = entries
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
        # Dependency and export audits use the graph for every declaration.
        # Only the reviewed contract and allowed axioms compare expressions.
        details_path = scratch / 'environment-details.txt'
        detail_names = set(contract['declarations']) | {entry['name'] for entry in permitted}
        details_path.write_text('\n'.join(sorted(detail_names)) + '\n')
        with environment_dump.open('w') as output:
            run([lake, 'env', 'lean', '--run', str(ROOT / 'verification/InspectEnvironment.lean'),
                 'Proofs', '--details-from', str(details_path), *[entry['name'] for entry in permitted]],
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
        stage('dependency audit', started)
        audit_contract(contract, rows)
        print(f'raw axiom dependency and statement/definition checks passed: {count} declarations')
        roots = project_export_names(rows)
        exported_roots = export_roots(roots, rows)
        # The exporter skips unsafe declarations (it always did when every name was passed).
        safe_roots = {name for name in roots if not rows[name]['unsafe']}
        print(f'{len(exported_roots)} of {len(roots)} project declarations passed to the exporter as roots')
        # No later phase needs declaration bodies. In particular, do not keep
        # them alive while either kernel builds its own expression tables.
        declaration_owners = {row['module'] for row in rows.values()}
        del rows
        gc.collect()
        stage('environment audits finished', started)
        # A CI runner without a module cache replays every project declaration
        # into the pinned, reviewed dependency environment. The independent
        # kernel below still receives the entire expression closure.
        modules = project_modules()
        base_key = mathlib_base_key()
        try:
            module_cache = json.loads(MODULE_CACHE.read_text())
        except (OSError, ValueError):
            module_cache = {}
        if module_cache.get('base') != base_key:
            dependency_families = {'Init', 'Lean', 'Std', *MATHLIB_FAMILY}
            reviewed = [module for module in listing if module.partition('.')[0] in dependency_families]
            reviewed_path = scratch / 'reviewed-replay-modules.txt'
            reviewed_path.write_text('\n'.join(sorted(reviewed)) + '\n')
            stage('project kernel replay started', started)
            run([lake, 'env', 'lean', '--run', str(ROOT / 'verification/ReplayProject.lean'),
                 'Proofs', str(reviewed_path)], scratch, env)
            stage('project kernel replay finished', started)
        else:
            recorded = module_cache.get('modules', {})
            to_replay = sorted(name for name, digest in modules.items() if recorded.get(name) != digest)
            required = replay_required_modules(to_replay, listing, declaration_owners)
            skipped_empty = sorted(set(to_replay) - set(required))
            if skipped_empty:
                print('imported modules with no owned declarations: ' + ', '.join(skipped_empty))
            # Only expression-bearing (or unobserved) modules require replay.
            # Do not let an empty aggregate expand the prefix to every module.
            targets = compact_replay_targets(required)
            if targets:
                stage(f'kernel replay started: {len(required)} module(s) require checks, '
                      f'{len(targets)} covering prefix(es)', started)
                run([lake, 'env', 'leanchecker', '--verbose', *targets], scratch, env)
            stage(f'kernel replay finished: {len(required)} module(s) required checks; '
                  f'{len(skipped_empty)} imported empty module(s)', started)
        stage('export started', started)
        export = scratch / 'proofs.ndjson'
        with export.open('w') as output:
            run([lake, 'env', str(exporter), 'Proofs', '--', *BUILTINS,
                 *[entry['name'] for entry in permitted], *exported_roots], scratch, env, stdout=output)
        missing = sorted(safe_roots - exported_names(export))
        if missing:
            # Partial definitions' auxiliaries are skipped by the exporter even when passed as roots (as they were
            # when every name was passed); any other missing name means the reduced roots lost coverage.
            probe = scratch / 'skipped.ndjson'
            with probe.open('w') as output:
                run([lake, 'env', str(exporter), 'Proofs', '--', *missing], scratch, env, stdout=output)
            lost = sorted(set(missing) & exported_names(probe))
            probe.unlink()
            if lost:
                raise ValueError(f'export lacks {len(lost)} project declaration(s): {lost[:10]}')
            print(f'{len(missing)} declaration(s) skipped by the exporter itself (partial or unsafe)')
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
