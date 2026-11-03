"""Reject axiom injection, weakened specifications and malformed proof terms."""

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'tools'))
from offline import disable_network
from proof_security import (audit_axiom_definitions, audit_contract, audit_dependencies,
    audit_source, changed_axiom_entries, contract_dependents, definition_digest, lean_code, load_contracts,
    statement_contract)
from check_proof_security import (BUILTINS, check_independent_kernel, compact_replay_targets,
                                  prune_stale_olean_parts)
from test_scalar_ir import lean_environment


def row(name, kind, type_, body='', dependencies=(), module='Proofs.Test'):
    return dict(name=name, kind=kind, module=module, type=type_, levels='[]', unsafe=False,
                body=body, type_dependencies=[], dependencies=list(dependencies))


class SecurityTests(unittest.TestCase):
    def test_stale_compiled_project_modules_are_removed_without_losing_live_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory) / 'build'
            archive = Path(directory) / 'archive'
            suffixes = ('.olean', '.olean.server', '.olean.private', '.ilean')
            for name in ['Proofs/Live', 'Proofs/Gone', 'Proofs/Generated/Kept',
                         'Proofs/Generated/Deleted', 'Proofs', 'Other/External']:
                for suffix in suffixes:
                    path = build / (name + suffix)
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(name)
            sources = {Path('Proofs.lean'), Path('Proofs/Live.lean'),
                       Path('Proofs/Generated/Kept.lean')}
            removed = prune_stale_olean_parts(build, sources, archive)
            expected = {Path(name + suffix) for name in ['Proofs/Gone', 'Proofs/Generated/Deleted']
                        for suffix in suffixes}
            self.assertEqual(set(removed), expected)
            self.assertEqual(sorted(p.read_text() for p in archive.rglob('*') if p.is_file()),
                             sorted(name for name in ['Proofs/Gone', 'Proofs/Generated/Deleted']
                                    for _ in suffixes))
            for name in ['Proofs/Live', 'Proofs/Generated/Kept', 'Proofs', 'Other/External']:
                for suffix in suffixes:
                    self.assertEqual((build / (name + suffix)).read_text(), name)
            self.assertEqual(prune_stale_olean_parts(build, sources, archive), [])

    def test_compact_replay_targets_preserve_module_coverage(self):
        # leanchecker uses Name.isPrefixOf, which compares complete components.
        # Exercise every subset, including ancestors, siblings and similar names.
        candidates = ['Proofs', 'Proofs.A', 'Proofs.A.B', 'Proofs.AA',
                      'Proofs.Generated', 'Proofs.Generated.Model', 'Other']
        universe = [*candidates, 'Proofs.A.C', 'Proofs.AA.B', 'Proofs.B',
                    'Proofs.Generated.Model.Child', 'Other.X', 'Mathlib.X']

        def covered(targets):
            return {name for name in universe if any(
                name.split('.')[:len(target.split('.'))] == target.split('.')
                for target in targets)}

        self.assertEqual(compact_replay_targets([]), [])
        self.assertEqual(compact_replay_targets(['Proofs.A', 'Proofs.A', 'Proofs']), ['Proofs'])
        self.assertEqual(compact_replay_targets(['Proofs.AA', 'Proofs.A']),
                         ['Proofs.A', 'Proofs.AA'])
        for mask in range(1 << len(candidates)):
            original = [name for index, name in enumerate(candidates) if mask & (1 << index)]
            reduced = compact_replay_targets(list(reversed(original)))
            self.assertLessEqual(len(reduced), len(original))
            self.assertTrue(set(reduced) <= set(original))
            self.assertEqual(covered(reduced), covered(original))

    def test_independent_kernel_diagnostics_and_success_validation(self):
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            checker = scratch / 'checker.py'
            checker.write_text('import sys\nprint("Checked 1 declarations with no errors")\n'
                               'print("checker failure detail", file=sys.stderr)\nsys.exit(1)\n')
            with self.assertRaisesRegex(RuntimeError, 'checker failure detail'):
                check_independent_kernel(sys.executable, checker, scratch, os.environ.copy())
            self.assertIn('Checked 1', (scratch / 'nanoda.stdout.log').read_text())
            self.assertIn('checker failure detail', (scratch / 'nanoda.stderr.log').read_text())
            checker.write_text('print("partial check")\n')
            with self.assertRaises(ValueError):
                check_independent_kernel(sys.executable, checker, scratch, os.environ.copy())
            checker.write_text('print("Checked 2 declarations with no errors")\n')
            self.assertEqual(check_independent_kernel(sys.executable, checker, scratch, os.environ.copy()),
                             'Checked 2 declarations with no errors')
            self.assertEqual((scratch / 'nanoda.stderr.log').read_text(), '')

    def test_stl_contracts_are_a_separate_reviewed_category(self):
        contracts = load_contracts(ROOT / 'verification/stl_contracts.json')
        self.assertTrue(contracts)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'contracts.json'
            entry = dict(contracts[0])
            for broken in [dict(entry, definition_sha256='zz'), dict(entry, clause=''), dict(entry, name='NotProofs.x'),
                           {k: v for k, v in entry.items() if k != 'reason'}]:
                path.write_text(json.dumps({'schema_version': 1, 'contracts': [broken]}))
                with self.assertRaises(ValueError):
                    load_contracts(path)
            path.write_text(json.dumps({'schema_version': 1, 'contracts': [entry, entry]}))
            with self.assertRaises(ValueError):
                load_contracts(path)
        # an axiom outside the registered contract file is still forbidden
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'Other.lean'
            source.write_text('axiom bad : False\n')
            with self.assertRaises(ValueError):
                audit_source(source)

    def test_theorems_depending_on_a_contract_are_reported(self):
        rows = {'Proofs.C.bound': row('Proofs.C.bound', 'axiom', 'Prop', module='Proofs.C'),
                'Proofs.t.uses': row('Proofs.t.uses', 'theorem', 'True', dependencies=['Proofs.helper']),
                'Proofs.helper': row('Proofs.helper', 'definition', 'Nat', dependencies=['Proofs.C.bound']),
                'Proofs.t.pure': row('Proofs.t.pure', 'theorem', 'True')}
        contracts = [dict(name='Proofs.C.bound', definition_sha256='0' * 64, clause='c', reason='r')]
        self.assertEqual(contract_dependents(contracts, rows), ['Proofs.t.uses'])
        # a contract is permitted by the dependency audit only when it is listed
        with self.assertRaises(ValueError):
            audit_dependencies([], rows)
        audit_dependencies(contracts, rows)

    def test_definition_audit_runs_only_for_changed_axioms(self):
        rows = {'first': row('first', 'axiom', 'Prop'),
                'second': row('second', 'axiom', 'Prop'),
                'Proofs.t': row('Proofs.t', 'theorem', 'True')}
        entries = [dict(name=name, definition_sha256=definition_digest(rows[name]),
                        reason='reviewed') for name in ['first', 'second']]
        changed, keys = changed_axiom_entries(entries, rows, {})
        self.assertEqual(changed, entries)
        cached = {'keys': keys}
        self.assertEqual(changed_axiom_entries(entries, rows, cached)[0], [])
        rows['Proofs.t']['body'] = 'changed proof'
        self.assertEqual(changed_axiom_entries(entries, rows, cached)[0], [])
        rows['third'] = row('third', 'axiom', 'Prop')
        added = dict(name='third', definition_sha256=definition_digest(rows['third']),
                     reason='new review')
        self.assertEqual(changed_axiom_entries([*entries, added], rows, cached)[0], [added])
        edited = copy.deepcopy(entries)
        edited[1]['reason'] = 'updated review'
        self.assertEqual(changed_axiom_entries(edited, rows, cached)[0], [edited[1]])
        rows['first']['type'] = 'False'
        self.assertEqual(changed_axiom_entries(entries, rows, cached)[0], [entries[0]])
        rows['first']['type'] = 'Prop'
        self.assertEqual(changed_axiom_entries(entries[1:], rows, cached)[0], [])
        # Removing permission still rejects a proof using that axiom.
        rows['Proofs.t']['dependencies'] = ['first']
        with self.assertRaisesRegex(ValueError, 'unpermitted axiom'):
            audit_dependencies(entries[1:], rows)
        for malformed in [None, [], {'keys': []}]:
            self.assertEqual(changed_axiom_entries(entries, rows, malformed)[0], entries)

    def test_raw_dependencies_reject_unpermitted_and_missing_constants(self):
        rows={'Proofs.t':row('Proofs.t','theorem','False',dependencies=['hidden']),
              'hidden':row('hidden','definition','False',dependencies=['cheat'],module='Std.Test'),
              'cheat':row('cheat','axiom','False',module='Std.Test')}
        with self.assertRaisesRegex(ValueError,'unpermitted axiom'):
            audit_dependencies([],rows)
        rows.pop('cheat')
        with self.assertRaisesRegex(ValueError,'missing dependency'):
            audit_dependencies([],rows)

    def test_changed_axiom_definition_and_policy_are_checked(self):
        r=row('propext','axiom','original',module='Init.Core')
        entries=[dict(name='propext',definition_sha256=definition_digest(r),reason='reviewed')]
        audit_axiom_definitions(entries,{'propext':r})
        r['type']='False'
        with self.assertRaisesRegex(ValueError,'definition differs'):
            audit_axiom_definitions(entries,{'propext':r})

    def test_statement_and_transitive_definitions_cannot_be_weakened(self):
        rows={'Proofs.t':row('Proofs.t','theorem','spec'),
              'spec':row('spec','definition','Prop',body='x = 1',dependencies=['x']),
              'x':row('x','definition','Nat',body='1')}
        rows['Proofs.t']['type_dependencies']=['spec']
        contract=statement_contract(rows,['Proofs.t'])
        audit_contract(contract,rows)
        changed=copy.deepcopy(rows);changed['Proofs.t']['type']='True'
        with self.assertRaisesRegex(ValueError,'statement or its definition'):
            audit_contract(contract,changed)
        changed=copy.deepcopy(rows);changed['x']['body']='0'
        with self.assertRaisesRegex(ValueError,'statement or its definition'):
            audit_contract(contract,changed)
        # Proof dependencies may change without changing the specification.
        changed=copy.deepcopy(rows);changed['Proofs.t']['dependencies']=['otherProof']
        audit_contract(contract,changed)

    def test_forbidden_metaprogramming_and_proof_shortcuts_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Test.lean'
            for text in ['axiom cheat : False','theorem t : False := by sorry',
                'theorem t : True := by native_decide','unsafe def x := 0',
                '@[extern "cheat"] opaque t : False','@[implemented_by cheat] def x := 0',
                'partial def x := x','run_elab pure ()','initialize x : Nat ← pure 0',
                'set_option debug.skipKernelTC true','import Lean','import Proofs.CppScalar Lean','#eval IO.println "cheat"']:
                path.write_text(text)
                with self.subTest(text=text),self.assertRaises(ValueError):audit_source(path)
            path.write_text('/- unsafe /- axiom -/ sorry -/\n-- native_decide\ndef label := "sorry"\ntheorem t : True := True.intro')
            audit_source(path)
            self.assertNotIn('unsafe',lean_code(path.read_text()))

    def test_independent_kernel_rejects_corrupted_proof_term(self):
        lake,env=lean_environment()
        exporter=ROOT/'.tools/lean4export/.lake/build/bin/lean4export'
        nanoda=ROOT/'.tools/nanoda_lib/target/release/nanoda_bin'
        env['LEAN_ABORT_ON_PANIC']='1'
        env.pop('LEAN_PATH',None)
        with tempfile.TemporaryDirectory(prefix='kernel-negative-') as directory:
            scratch=Path(directory)
            (scratch/'lean-toolchain').write_text((ROOT/'lean-toolchain').read_text())
            (scratch/'Fixture.lean').write_text('theorem tested : True := True.intro\n')
            subprocess.run([lake,'env','lean','-o','Fixture.olean','Fixture.lean'],cwd=scratch,env=env,check=True)
            # Explicit search path is limited to this new fixture plus the
            # toolchain's normal search path supplied by Lake.
            env['LEAN_PATH']=str(scratch)
            result=subprocess.run([lake,'env',str(exporter),'Fixture','--',*BUILTINS,'tested'],cwd=ROOT,env=env,
                check=True,capture_output=True,text=True)
            declarations=[json.loads(line) for line in result.stdout.splitlines()]
            export=scratch/'export.ndjson';config=scratch/'nanoda.json'
            config.write_text(json.dumps(dict(export_file_path=str(export),permitted_axioms=[e["name"] for e in json.loads((ROOT/"verification/allowed_axioms.json").read_text())["axioms"]],
                unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,
                print_axioms=False,print_success_message=True)))
            export.write_text(result.stdout)
            good=subprocess.run([str(nanoda),str(config)],capture_output=True,text=True)
            self.assertEqual(good.returncode,0,good.stderr)
            self.assertIn('with no errors',good.stdout)
            thm=next(d['thm'] for d in declarations if 'thm' in d)
            thm['value']=next(d['ie'] for d in declarations if 'sort' in d)
            export.write_text('\n'.join(json.dumps(d) for d in declarations)+'\n')
            bad=subprocess.run([str(nanoda),str(config)],capture_output=True,text=True)
            self.assertNotEqual(bad.returncode,0)

    def test_compilable_statement_and_definition_mutations_fail_contract(self):
        lake,env=lean_environment()
        env['LEAN_ABORT_ON_PANIC']='1'
        with tempfile.TemporaryDirectory(prefix='statement-negative-') as directory:
            scratch=Path(directory)
            (scratch/'lean-toolchain').write_text((ROOT/'lean-toolchain').read_text())
            source=scratch/'Fixture.lean'
            def inspect(text):
                source.write_text(text)
                subprocess.run([lake,'env','lean','-o','Fixture.olean','Fixture.lean'],cwd=scratch,env=env,check=True)
                inspect_env=env.copy();inspect_env['LEAN_PATH']=str(scratch)
                result=subprocess.run([lake,'env','lean','--run',str(ROOT/'verification/InspectEnvironment.lean'),
                    'Fixture','tested'],cwd=ROOT,env=inspect_env,check=True,capture_output=True,text=True)
                return {r['name']:r for r in map(json.loads,result.stdout.splitlines())}
            rows=inspect('def n : Nat := 1\ntheorem tested : n = n := rfl\n')
            contract=statement_contract(rows,['tested'])
            weakened=inspect('def n : Nat := 1\ntheorem tested : True := True.intro\n')
            with self.assertRaisesRegex(ValueError,'statement or its definition'):
                audit_contract(contract,weakened)
            changed=inspect('def n : Nat := 0\ntheorem tested : n = n := rfl\n')
            self.assertEqual(rows['tested']['type'],changed['tested']['type'])
            with self.assertRaisesRegex(ValueError,'statement or its definition'):
                audit_contract(contract,changed)


if __name__=='__main__':
    disable_network()
    unittest.main()
