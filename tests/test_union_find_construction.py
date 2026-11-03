"""Actual constructor initializer stages: allocation, ordered fields, then body.

The stage's runFuel result retains fields. Export/retirement and a general
constructor correctness proof remain separate obligations.
"""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_original_api import SOURCE
from nested_ir import lower_source, emit_lean
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
MODEL = ROOT/'Proofs/Generated/UnionFindConstruction.lean'
NAMESPACE = 'Proofs.UnionFindConstructionInstance'
HEADER = '''
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppVectorOwnership
open Proofs.UnionFindConstructionInstance
 def i32 : Ty := ⟨32,true,false⟩
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 def stage (p : NProgram) (args : List NArgument) : Outcome NStep := do
   let entry ← liftChecked (prepare empty p.parameters args)
   runFuel 16 p.body entry
 def summary (out : Outcome NStep) (v c n : Nat) : Option (List Int × Int × Int) := do
   let step ← match out with | .finished s => some s | _ => none
   if step.returned.isSome || step.breaking then none else do
   let vi ← step.state.vectorSlot v
   let binding ← step.state.frame.bindings[vi]?
   let buffer ← step.state.frame.state.storage.lookup binding.owner
   let items ← buffer.items.mapM fun x => match x with | .integer y => some y | _ => none
   let (_,count) ← step.state.scalarCell c i32
   let (_,size) ← step.state.scalarCell n i32
   some (items,count.value,size.value)
'''

def additional_model(ir, namespace):
    return '\n'.join(line for line in emit_lean(ir,namespace).splitlines() if not line.startswith('import '))


class UnionFindConstructionTests(unittest.TestCase):
    def test_initializers_allocations_fields_and_original_body(self):
        ir = lower_source(SOURCE,[SOURCE.parent],construction_stages=True)
        self.assertEqual(emit_lean(ir,NAMESPACE),MODEL.read_text())
        self.assertEqual([f['name'] for f in ir['functions']],['UnionFind_construct0','UnionFind_construct1'])
        sized = ir['functions'][1]
        self.assertEqual([s['kind'] for s in sized['body']],['fill_vector','declare','declare','check'])
        self.assertEqual(sized['construction_fields'],[
            {'name':'_ps','slot':1},{'name':'_num_groups','slot':2},{'name':'_n','slot':3}])
        # Existing method/body-only constructor models remain byte-identical.
        self.assertEqual(emit_lean(lower_source(SOURCE,[SOURCE.parent]),'Proofs.UnionFindCandidateInstance'),
                         (ROOT/'Proofs/Generated/UnionFindCandidate.lean').read_text())
        cases = [0,1,2,17,128]
        checks = [HEADER,
          '#guard summary (stage UnionFind_construct0 []) 0 1 2 == some ([],0,0)',
          '#guard UnionFind_construct0_fields == [("_ps",0),("_num_groups",1),("_n",2)]',
          '#guard UnionFind_construct1_fields == [("_ps",1),("_num_groups",2),("_n",3)]']
        for n in cases:
            checks.append(f'#guard summary (stage UnionFind_construct1 [.value (.literal i32 {n})]) 1 2 3 == some (List.replicate {n} (-1),{n},{n})')
        # The vector allocation precedes the assert, as in the original source.
        # Negative n converts to huge size_t and fails the allocation limit;
        # no claim that the assertion happens before allocation is made.
        checks.append('#guard stage UnionFind_construct1 [.value (.literal i32 (-1))] == .fault')
        with tempfile.TemporaryDirectory(prefix='uf-construction-') as directory:
            scratch = Path(directory)
            lean = scratch/'checks.lean'
            lean.write_text(MODEL.read_text()+'\n'+'\n'.join(checks))
            lake,env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            cpp = scratch/'native.cpp'; binary = scratch/'native'
            cpp.write_text('#include "'+str(SOURCE)+'"\n#include <cassert>\nint main(){'
              'cp::UnionFind empty; assert(empty._ps.empty() && empty._n==0 && empty._num_groups==0);'
              'for(int n : {0,1,2,17,128}) {cp::UnionFind u(n);'
              'assert(u._n==n && u._num_groups==n && u._ps==std::vector<int>(n,-1));}}')
            subprocess.run(['g++','-std=c++17','-O1','-fno-access-control','-fsanitize=undefined',
                '-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_initializer_mutations_and_field_declaration_order(self):
        original = SOURCE.read_text()
        baseline = lower_source(SOURCE,[SOURCE.parent],construction_stages=True)
        executions = [MODEL.read_text(),HEADER]
        with tempfile.TemporaryDirectory(prefix='uf-construction-mutations-') as directory:
            path = Path(directory)/'source.hpp'
            for index,(old,new) in enumerate([('_ps(n, -1)','_ps(n, 0)'),('_ps(n, -1)','_ps(n+1, -1)'),
                            ('_num_groups(n)','_num_groups(n+1)'),('_n(n)','_n(n+1)'),
                            ('assert(n >= 0);','')]):
                with self.subTest(change=new):
                    self.assertIn(old,original)
                    path.write_text(original.replace(old,new))
                    changed = lower_source(path,[path.parent],construction_stages=True)
                    self.assertNotEqual(changed,baseline)
                    if index < 4:
                        executions.extend([additional_model(changed,f'Mutation{index}'),
                            f'#guard summary (stage Mutation{index}.UnionFind_construct1 [.value (.literal i32 2)]) 1 2 3 != some ([-1,-1],2,2)'])
            # C++ runs initializers in field declaration order, even if written otherwise.
            path.write_text(original.replace('_ps(n, -1), _num_groups(n), _n(n)',
                                             '_n(n), _num_groups(n), _ps(n, -1)'))
            self.assertEqual(lower_source(path,[path.parent],construction_stages=True),baseline)
            path.write_text('#include <vector>\nnamespace cp {struct C {int a,b;std::vector<int> v;'
                'C(int n): b(a+1),v(n,-1),a(n) {} };}')
            ir = lower_source(path,[path.parent],construction_stages=True)
            self.assertEqual([f['name'] for f in ir['functions'][0]['construction_fields']],['a','b','v'])
            self.assertEqual([s['kind'] for s in ir['functions'][0]['body']],['declare','declare','fill_vector'])
            executions.extend([additional_model(ir,'EarlierField'),
                '#guard summary (stage EarlierField.C_construct0 [.value (.literal i32 3)]) 3 1 2 == some ([-1,-1,-1],3,4)'])
            lean = Path(directory)/'mutations.lean'
            lean.write_text('\n'.join(executions))
            lake,env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_unsupported_constructor_shapes_fail_closed(self):
        cases = [
            'struct Base {}; struct C : Base {int n; C():n(0) {}};',
            'struct C {int n; C():C(0) {} C(int x):n(x) {}};',
            'struct C {int n; C() = default;};',
            'struct C {int n; __attribute__((annotate("unsupported"))) C():n(0) {}};',
            'struct C {std::vector<int> v; C(const std::vector<int>& x):v(x.begin(),x.end()) {}};',
            'struct C {int a,b; C():a(b),b(0) {}};',
        ]
        with tempfile.TemporaryDirectory(prefix='uf-construction-rejected-') as directory:
            path = Path(directory)/'source.hpp'
            for case in cases:
                with self.subTest(case=case):
                    path.write_text('#include <vector>\nnamespace cp {'+case+'}')
                    with self.assertRaises(ValueError):
                        lower_source(path,[path.parent],construction_stages=True)

if __name__ == '__main__':
    disable_network()
    unittest.main()
