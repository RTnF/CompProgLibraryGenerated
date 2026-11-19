"""Audit fresh translation of the public Ratio and its canonical proof.

This is a development audit, not the public catalog check or the final all-component gate.
The script screens and rebuilds the common modules with Lake; both kernels check
the fresh public source/proof combination or its exported dependency closure.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'verifier'), str(ROOT / 'tools')]
import lean_translate
from check_proof_security import BUILTINS, export_roots, exported_names, project_export_names
from proof_security import audit_source, audit_dependencies, audit_axiom_definitions, load_policy, audit_mathlib_coverage, lean_code


def main():
    scratch = ROOT / '.cache/wip/ratio_audit'
    scratch.mkdir(parents=True, exist_ok=True)
    inputs = [ROOT / name for name in [
        'library/number/ratio.hpp', 'library/number/ratio.toml',
        'Proofs/Cpp/Ratio.lean', 'Proofs/Cpp/Gen/Ratio.lean',
        'tools/audit_ratio.py', 'tools/check_proof_security.py', 'tools/proof_security.py',
        'verifier/lean_translate.py', 'verifier/clang_ast.py']]
    pending = [p for p in inputs if p.suffix == '.lean']
    screened = set()
    while pending:
        proof_source = pending.pop()
        if proof_source in screened:
            continue
        audit_source(proof_source)
        screened.add(proof_source)
        for line in lean_code(proof_source.read_text()).splitlines():
            if re.match(r"^\s*import\s+", line):
                for name in line.split()[1:]:
                    if name.startswith('Proofs.'):
                        dependency = ROOT / (name.replace('.', '/') + '.lean')
                        if dependency not in inputs:
                            inputs.append(dependency)
                        pending.append(dependency)
    inputs += [ROOT / 'verification/allowed_axioms.json', ROOT / 'lake-manifest.json', ROOT / 'lean-toolchain']
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    common = scratch / 'Proofs/Cpp'
    common.parent.mkdir(parents=True, exist_ok=True)
    expected_common = ROOT / '.lake/build/lib/lean/Proofs/Cpp'
    if not common.exists():
        common.symlink_to(expected_common, target_is_directory=True)
    if not common.is_symlink() or common.resolve() != expected_common.resolve():
        raise ValueError('unexpected shared module view in audit scratch')
    env = dict(os.environ)
    if (ROOT / '.tools/elan/bin/lake').is_file():
        env['ELAN_HOME'] = str(ROOT / '.tools/elan')
        env['PATH'] = str(ROOT / '.tools/elan/bin') + os.pathsep + env['PATH']

    def run(command, **kwargs):
        return subprocess.run([str(x) for x in command], cwd=ROOT, env=env,
                              check=True, timeout=600, **kwargs)

    run(['lake', 'build', 'Proofs.Cpp.Lib.RatioArithmeticSpace', 'Proofs.Cpp.Lib.RatioMath', 'Proofs.Cpp.Lib.UnsignedMagnitude'])
    path = run(['lake', 'env', 'printenv', 'LEAN_PATH'], capture_output=True, text=True).stdout.strip()
    env['LEAN_PATH'] = str(scratch) + os.pathsep + path
    model = lean_translate.translate_file(ROOT / 'library/number/ratio.hpp', [], standard='c++20')
    if model != (ROOT / 'Proofs/Cpp/Gen/Ratio.lean').read_text():
        raise ValueError('public Ratio model differs from fresh translation')
    canonical = (ROOT / 'Proofs/Cpp/Ratio.lean').read_text()
    imports = '\n'.join(line for line in canonical.splitlines() if line.startswith('import ')
                        and line != 'import Proofs.Cpp.Gen.Ratio') + '\n'
    contracts = '\n'.join(line for line in canonical.splitlines() if not line.startswith('import '))
    source = scratch / 'Proofs/RatioAudit.lean'
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text(imports + model + contracts)
    audit_source(source)
    module = 'Proofs.RatioAudit'
    run(['lean', '-R', scratch, '-o', source.with_suffix('.olean'), source])
    print('fresh public Ratio and canonical proof compiled and screened', flush=True)
    entries = load_policy(ROOT / 'verification/allowed_axioms.json')
    dump = scratch / 'environment.ndjson'
    with dump.open('w') as out:
        run(['lean', '--run', ROOT / 'verification/InspectEnvironment.lean', module,
             *[e['name'] for e in entries]], stdout=out)
    rows = {}
    with dump.open() as stream:
        for line in stream:
            row = json.loads(line)
            if row['name'] in rows:
                raise ValueError('duplicate declaration: ' + row['name'])
            rows[row['name']] = row
    modules = {r['module'] for r in rows.values()}
    for owner in modules:
        if owner.startswith('Proofs.') and owner != module:
            audit_source(ROOT / (owner.replace('.', '/') + '.lean'))
    audit_axiom_definitions(entries, rows)
    count = audit_dependencies(entries, rows)
    audit_mathlib_coverage(modules)
    roots = project_export_names(rows)
    ratio_theorems = sorted(n for n, r in rows.items()
                                if r['module'] == module and r['kind'] == 'theorem')
    if not ratio_theorems:
        raise ValueError('no Ratio theorems inspected')
    roots_to_export = export_roots(roots, rows)
    safe = {n for n in roots if not rows[n]['unsafe']}
    print(f'axiom/source audit: {count} declarations; {len(ratio_theorems)} Ratio theorems', flush=True)
    run(['leanchecker', '--verbose', '--fresh', module])
    print('Ratio leanchecker passed', flush=True)
    export = scratch / 'proofs.ndjson'
    with export.open('w') as out:
        run([ROOT / '.tools/lean4export/.lake/build/bin/lean4export', module, '--',
             *BUILTINS, *[e['name'] for e in entries], *roots_to_export], stdout=out)
    missing = safe - exported_names(export)
    if missing:
        # Same probe as the full audit: compiler-generated partial/unsafe
        # auxiliaries may be skipped even when explicitly requested. A root
        # that the exporter CAN emit must never be silently omitted.
        probe = scratch / 'missing-probe.ndjson'
        with probe.open('w') as out:
            run([ROOT / '.tools/lean4export/.lake/build/bin/lean4export', module,
                 '--', *sorted(missing)], stdout=out)
        exportable = missing & exported_names(probe)
        if exportable:
            raise ValueError(f'export omitted exportable declarations: {sorted(exportable)}')
        print(f'{len(missing)} internal auxiliaries skipped by the exporter itself', flush=True)
    config = scratch / 'nanoda.json'
    config.write_text(json.dumps(dict(export_file_path=str(export),
        permitted_axioms=[e['name'] for e in entries], unpermitted_axiom_hard_error=True,
        unsafe_permit_all_axioms=False, nat_extension=True, string_extension=True,
        num_threads=2, print_success_message=True, print_axioms=False)))
    print('export complete; independent kernel started', flush=True)
    result = run([ROOT / '.tools/nanoda_lib/target/release/nanoda_bin', config], capture_output=True, text=True)
    if not re.fullmatch(r'Checked [1-9][0-9]* declarations with no errors\s*', result.stdout):
        raise ValueError('independent kernel did not report a clean check: ' + result.stdout)
    print(result.stdout.strip(), flush=True)
    current = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    if current != hashes:
        raise ValueError('audit inputs changed while the check was running')
    (scratch / 'result.json').write_text(json.dumps(dict(
        module=module, inputs_sha256=hashes, ratio_theorems=ratio_theorems,
        project_declarations=len(safe), skipped_internal_auxiliaries=sorted(missing),
        export_sha256=hashlib.sha256(export.read_bytes()).hexdigest(),
        independent_kernel=result.stdout.strip()), indent=2) + '\n')


if __name__ == '__main__':
    main()
