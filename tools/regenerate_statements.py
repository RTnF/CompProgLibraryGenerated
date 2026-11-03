"""Regenerate verification/statements.json after a reviewed change of public theorems.

Review the diff of the proposition and definition closure before committing.
"""

import json
import os
import subprocess
import sys

from offline import disable_network
from proof_security import ROOT, load_contracts, load_policy, statement_contract
from public import registry


def main():
    disable_network()
    entries = load_policy(ROOT / 'verification/allowed_axioms.json') + load_contracts(ROOT / 'verification/stl_contracts.json')
    env = os.environ.copy()
    env['ELAN_HOME'] = str(ROOT / '.tools/elan')
    lake = str(ROOT / '.tools/elan/bin/lake')
    subprocess.run([lake, 'build'], cwd=ROOT, env=env, check=True)
    result = subprocess.run([lake, 'env', 'lean', '--run', str(ROOT / 'verification/InspectEnvironment.lean'),
        'Proofs', *[entry['name'] for entry in entries]], cwd=ROOT, env=env, check=True,
        capture_output=True, text=True)
    rows = {row['name']: row for row in map(json.loads, result.stdout.splitlines())}
    modules = {entry['proof'].removesuffix('.lean').replace('/', '.') for entry in registry().values()}
    roots = sorted(name for name, row in rows.items() if row['kind'] == 'theorem'
                   and row['module'] in modules and name.startswith('Proofs.'))
    path = ROOT / 'verification/statements.json'
    old = json.loads(path.read_text())
    new = statement_contract(rows, roots)
    changed = [name for name in old['declarations']
               if name in new['declarations'] and old['declarations'][name] != new['declarations'][name]]
    removed = len(set(old['declarations']) - set(new['declarations']))
    print(f"roots {len(old['roots'])} -> {len(new['roots'])}; declarations {len(old['declarations'])} -> {len(new['declarations'])}; removed {removed}; changed existing: {changed}")
    if changed and '--accept-changed' not in sys.argv:
        raise SystemExit('existing reviewed statements changed; review before regenerating')
    path.write_text(json.dumps(new, indent=2) + '\n')


if __name__ == '__main__':
    main()
