"""Constructor-stage helper calls use allocated fields and ordinary argument capture."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests'), str(ROOT / 'verifier')]
from nested_ir import lower_source, emit_lean
from test_scalar_ir import lean_environment
from offline import disable_network

SOURCE = '''#include <vector>
struct CtorCalls {
  std::vector<int> first, second;
  int count;
  void assign(int value) { first[0] = value; second[1] = value + count; }
  CtorCalls(int value) : first(2,0), second(3,1), count(7) { assign(value); }
};
'''
CHECKS = '''
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open StageMethods
abbrev i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def stage (q : Int) : Outcome NStep := do
  let entry ← liftChecked (prepare empty CtorCalls_construct0.parameters [.value (.literal i32 q)])
  runFuel 32 CtorCalls_construct0.body entry
def summary (out : Outcome NStep) : Option (List Int × List Int × Int) := do
  let step ← match out with | .finished s => some s | _ => none
  if step.returned.isSome || step.breaking then none else do
  let v1 ← step.state.vectorSlot 1
  let v2 ← step.state.vectorSlot 2
  let b1 ← step.state.frame.bindings[v1]?
  let b2 ← step.state.frame.bindings[v2]?
  let a1 ← step.state.frame.state.storage.lookup b1.owner
  let a2 ← step.state.frame.state.storage.lookup b2.owner
  let xs ← a1.items.mapM fun x => match x with | .integer y => some y | _ => none
  let ys ← a2.items.mapM fun x => match x with | .integer y => some y | _ => none
  let (_,count) ← step.state.scalarCell 3 i32
  some (xs,ys,count.value)
'''


class ConstructorStageMethodTests(unittest.TestCase):
    def test_helper_calls_and_initializer_changes(self):
        with tempfile.TemporaryDirectory(prefix='ctor-stage-methods-') as directory:
            root = Path(directory)
            source = root / 'source.hpp'
            source.write_text(SOURCE)
            ir = lower_source(source, construction_stages=True)
            self.assertEqual([f['name'] for f in ir['functions']], ['CtorCalls_construct0'])
            self.assertEqual(ir['functions'][0]['construction_fields'],
                             [{'name': 'first', 'slot': 1}, {'name': 'second', 'slot': 2},
                              {'name': 'count', 'slot': 3}])
            baseline = ir
            for count, delta in [(7, 0), (9, 1)]:
                source.write_text(SOURCE.replace('count(7)', f'count({count})')
                                  .replace('assign(value);', f'assign(value + {delta});'))
                generated = lower_source(source, construction_stages=True)
                if delta:
                    self.assertNotEqual(generated, baseline)
                checks = [CHECKS]
                for q in [-3, 0, 5, 17]:
                    checks.append(f'#guard summary (stage ({q})) == some ([{q+delta},0],[1,{q+delta+count},1],{count})')
                proof = root / 'check.lean'
                proof.write_text(emit_lean(generated, 'StageMethods') + '\n' + '\n'.join(checks))
                lake, env = lean_environment()
                result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                                        env=env, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn('warning:', result.stdout + result.stderr)
                cpp = root / 'check.cpp'
                cpp.write_text('#include "source.hpp"\n#include <cassert>\nint main(){'
                               'for(int q : {-3,0,5,17}) { CtorCalls c(q);'
                               f'assert(c.first==std::vector<int>({{q+{delta},0}}));'
                               f'assert(c.second==std::vector<int>({{1,q+{delta+count},1}}));'
                               f'assert(c.count=={count});' + '}}')
                binary = root / 'native'
                subprocess.run(['g++', '-std=c++17', '-O1', '-fsanitize=undefined',
                                '-fno-sanitize-recover=all', str(cpp), '-o', str(binary)], check=True)
                subprocess.run([str(binary)], check=True)

    def test_beats_allocation_prefix_and_verified_body_permutation(self):
        source = ROOT / 'library/segment_tree_beats.hpp'
        full = lower_source(source, construction_stages=True)
        self.assertEqual(emit_lean(full, 'Proofs.BeatsConstructionStage'),
                         (ROOT / 'Proofs/Generated/BeatsConstructionStage.lean').read_text())
        stage = full['functions'][0]
        self.assertEqual([f['name'] for f in full['functions']], ['SegmentTreeBeats_construct0'])
        fields = stage['construction_fields']
        self.assertEqual([f['name'] for f in fields],
                         ['max_v','smax_v','max_c','min_v','smin_v','min_c','len','ladd','lval',
                          'lo','hi','st_k','st_l','st_r','ent','inf','n'])
        self.assertEqual([f['slot'] for f in fields], list(range(1, 18)))
        prefix = stage['body'][:15]
        self.assertEqual([s['kind'] for s in prefix], ['fill_vector'] * 15)
        self.assertEqual([s['element']['width'] for s in prefix], [64]*9 + [32]*6)
        for i in [11, 12, 13]:
            self.assertEqual(prefix[i]['count']['operand']['value'], 256)
        for i in [*range(11), 14]:
            self.assertEqual(prefix[i]['count'], prefix[0]['count'])
        body_only = lower_source(source)
        # The existing verified model still comes from the same default path.
        self.assertEqual(emit_lean(body_only, 'Proofs.BeatsInstance'),
                         (ROOT / 'Proofs/Generated/SegmentTreeBeats.lean').read_text())
        constructor = next(f for f in body_only['functions'] if f['name'] == 'SegmentTreeBeats_new0')
        def permute(node):
            if isinstance(node, list):
                return [permute(x) for x in node]
            if not isinstance(node, dict):
                return node
            out = {key: permute(value) for key, value in node.items()}
            if 'slot' in out and out['slot'] < 16:
                out['slot'] = (out['slot'] + 1) % 16
            return out
        self.assertEqual(stage['body'][15:], permute(constructor['body']))
        with tempfile.TemporaryDirectory(prefix='beats-construction-stage-') as directory:
            proof = Path(directory) / 'check.lean'
            proof.write_text(emit_lean(full, 'BeatsStage'))
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                                    env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_scalar_only_helper_updates_the_constructed_field(self):
        with tempfile.TemporaryDirectory(prefix='ctor-stage-scalar-') as directory:
            source = Path(directory) / 'source.hpp'
            source.write_text("#include <vector>\nstruct Counter { int x; "
                              "void bump(int d) { x += d; } "
                              "Counter(int q) : x(q) { bump(3); } };\n")
            ir = lower_source(source, construction_stages=True)
            proof = Path(directory) / 'check.lean'
            checks = CHECKS[:CHECKS.index('def stage (q : Int)')].replace('open StageMethods', 'open ScalarStage')
            checks += """
def observed (q : Int) : Option Int := do
  let entry ← prepare empty Counter_construct0.parameters [.value (.literal i32 q)]
  let step ← match runFuel 16 Counter_construct0.body entry with
    | .finished s => some s
    | _ => none
  let (_,cell) ← step.state.scalarCell 1 i32
  some cell.value
#guard observed 5 == some 8
#guard observed (-3) == some 0
"""
            proof.write_text(emit_lean(ir, 'ScalarStage') + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                                    env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_mutable_argument_aliases_the_constructed_scalar_field(self):
        with tempfile.TemporaryDirectory(prefix='ctor-stage-alias-') as directory:
            root = Path(directory)
            source = root / 'source.hpp'
            source.write_text("#include <vector>\nstruct Alias { int count, observed; "
                              "int inspect(int& value) { value=9; return count; } "
                              "Alias() : count(5), observed(0) { observed=inspect(count); } };\n")
            ir = lower_source(source, construction_stages=True)
            proof = root / 'check.lean'
            checks = CHECKS[:CHECKS.index('def stage (q : Int)')].replace('open StageMethods', 'open AliasStage')
            checks += """
def observed : Option (Int × Int) := do
  let entry ← prepare empty Alias_construct0.parameters []
  let step ← match runFuel 32 Alias_construct0.body entry with
    | .finished s => some s
    | _ => none
  let (_,count) ← step.state.scalarCell 0 i32
  let (_,seen) ← step.state.scalarCell 1 i32
  some (count.value,seen.value)
#guard observed == some (9,9)
"""
            proof.write_text(emit_lean(ir, 'AliasStage') + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                                    env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)
            cpp = root / 'check.cpp'
            cpp.write_text('#include "source.hpp"\n#include <cassert>\n'
                           'int main(){ Alias a; assert(a.count==9 && a.observed==9); }')
            binary = root / 'native'
            subprocess.run(['g++', '-std=c++17', '-fsanitize=undefined', '-fno-sanitize-recover=all',
                            str(cpp), '-o', str(binary)], check=True)
            subprocess.run([str(binary)], check=True)

    def test_recursive_constructor_helper_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix='ctor-stage-recursive-') as directory:
            source = Path(directory) / 'source.hpp'
            source.write_text(SOURCE.replace('first[0] = value;', 'assign(value);'))
            with self.assertRaisesRegex(ValueError, 'recursive calls cannot be inlined'):
                lower_source(source, construction_stages=True)


if __name__ == '__main__':
    disable_network()
    unittest.main()
