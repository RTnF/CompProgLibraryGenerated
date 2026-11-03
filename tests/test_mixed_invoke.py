"""Mixed scalar/vector call entry, alias updates and private object retirement."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_vector_bindings import ROOT
from check_public import FLAGS, check_compiler
from offline import disable_network

HEADER = """import Proofs.CppMixedInvoke
import Proofs.Generated.DoublingBindings
open Proofs.CppScalar Proofs.CppMixedInvoke
 def i32 : Ty := ⟨32,true,false⟩
 def u64 : Ty := ⟨64,false,false⟩
 def caller : State := ⟨⟨[],[],0,0,0⟩,
   ⟨⟨[some ⟨0,[3,8],2,100,0⟩],0,0,3⟩,[⟨i32,true⟩],[⟨0,i32,true⟩],0⟩,[.vector 0],0⟩
 def entry : State := ⟨⟨[⟨⟨1,false,true⟩,0⟩,⟨u64,9⟩],[⟨1,true⟩],5,0,4⟩,
   ⟨caller.vectors.store,caller.vectors.types,[⟨0,i32,false⟩],1⟩,[.vector 0,.scalar 0],5⟩
"""

class MixedInvokeTests(unittest.TestCase):
    def lean(self, scratch, text):
        path = scratch/'checks.lean'
        path.write_text(text)
        lake, env = lean_environment()
        result = subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,
            capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_removed_guards_and_accounting_fail_existing_proofs(self):
        source = (ROOT/'Proofs/CppMixedInvoke.lean').read_text().replace(
            'Proofs.CppMixedInvoke', 'Proofs.MixedInvokeMutation')
        mutations = [
            ('caller.vectors.bindings.length+arguments.length+a.nodes', 'arguments.length+a.nodes'),
            ('List.replicate (objects.length-callerCount) none', '[]'),
            ('resultType.valid value ∧', 'True ∧'),
            ('if writable = true → binding.writable = true then', 'if True then'),
        ]
        lake, env = lean_environment()
        with tempfile.TemporaryDirectory(prefix='mixed-proof-negative-') as directory:
            scratch = Path(directory)
            self.lean(scratch, source)
            for old, new in mutations:
                with self.subTest(removed=old):
                    self.assertEqual(source.count(old), 1)
                    path = scratch/'mutation.lean'
                    path.write_text(source.replace(old, new))
                    result = subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,
                        capture_output=True,text=True)
                    self.assertNotEqual(result.returncode, 0, result.stdout+result.stderr)
                    self.assertIn('error', result.stdout)
                    self.assertNotIn('unexpected token', result.stdout)
                    self.assertNotIn('Unknown identifier', result.stdout)
        print('mixed call: four removed guard/accounting mutations rejected by existing proofs')

    def test_generated_schema_resolution_permissions_and_cost(self):
        checks = HEADER + """
#guard prepare caller DoublingBindingInstance.doubling
 [.vectorReference 0,.value (.literal u64 9)] == some entry
#guard prepare caller DoublingBindingInstance.doubling [.vectorReference 0] == none
#guard prepare caller DoublingBindingInstance.doubling
 [.vectorReference 0,.value (.literal u64 9),.vectorReference 0] == none
#guard prepare caller DoublingBindingInstance.doubling
 [.scalarReference 0,.value (.literal u64 9)] == none
#guard prepare caller DoublingBindingInstance.doubling
 [.vectorReference 1,.value (.literal u64 9)] == none
#guard prepare caller DoublingBindingInstance.doubling
 [.vectorReference 0,.value (.literal i32 9)] == none
#guard prepare caller DoublingBindingInstance.doubling
 [.vectorReference 0,.value (.literal u64 (-1))] == none
#guard entry.vectors.reserve 0 i32 5 == none
#guard entry.vectors.write ⟨0,i32,true,⟨0,0,0⟩⟩ 5 == none
#guard entry.scalars.environment == some [9]
#guard entry.work == 5
 def manyBindings : State := {caller with vectors := {caller.vectors with
  bindings := List.replicate 10 ⟨0,i32,true⟩}}
 def largeExpression : Expr := .binary u64 .add
  (.binary u64 .add (.literal u64 1) (.literal u64 2))
  (.binary u64 .add (.literal u64 3) (.literal u64 4))
#guard largeExpression.nodes == 7
#guard ((prepare manyBindings DoublingBindingInstance.doubling
 [.vectorReference 0,.value largeExpression]).map (·.peak)) == some 20
 def readOnlyCaller : State := {caller with vectors := {caller.vectors with bindings := [⟨0,i32,false⟩]}}
#guard prepare readOnlyCaller [.vector i32 true] [.vectorReference 0] == none
#guard (prepare readOnlyCaller [.vector i32 false] [.vectorReference 0]).isSome
#guard prepare caller [.vector u64 false] [.vectorReference 0] == none
 def badMetadata : State := {caller with vectors := {caller.vectors with types := []}}
#guard prepare badMetadata [] [] == none
 def dangling : State := {caller with scalars := ⟨[],[⟨0,true⟩],0,0,0⟩}
#guard prepare dangling [.scalar i32 true true] [.scalarReference 0] == none
 def scalarCaller : State := {caller with scalars := ⟨[⟨i32,7⟩],[⟨0,true⟩,⟨0,false⟩],0,1,0⟩, slots := [.scalar 0,.scalar 1,.vector 0]}
#guard prepare scalarCaller [.scalar i32 true true] [.scalarReference 1] == none
#guard (prepare scalarCaller [.scalar i32 true false] [.scalarReference 1]).isSome
#guard prepare scalarCaller [.scalar u64 true true] [.scalarReference 0] == none
#guard (resolveAll scalarCaller
 [.scalar i32 true true,.vector i32 false,.scalar i32 true false,.vector i32 true]
 [.scalarReference 0,.vectorReference 0,.scalarReference 1,.vectorReference 0]) == some
 ([.scalar ⟨i32,true,true⟩ (.reference 0),.vector 0 i32 false,
   .scalar ⟨i32,true,false⟩ (.reference 0),.vector 0 i32 true],4)
#guard ((prepare scalarCaller
 [.scalar i32 true true,.vector i32 false,.scalar i32 true false,.vector i32 true]
 [.scalarReference 0,.vectorReference 0,.scalarReference 1,.vectorReference 0]).map (·.slots)) ==
 some [.scalar 0,.vector 0,.scalar 1,.vector 1]
"""
        with tempfile.TemporaryDirectory(prefix='mixed-entry-') as directory:
            self.lean(Path(directory), checks)
        print(f'mixed entry: {checks.count("#guard")} checks including actual doubling parameter schema')

    def test_updates_return_and_private_vector_lifetimes(self):
        checks = HEADER + """
 def original : State := {caller with scalars := ⟨[⟨i32,7⟩],[⟨0,true⟩],0,1,0⟩, slots := [.scalar 0,.vector 0]}
 def entered : State := (prepare original
 [.scalar i32 true true,.vector i32 true,.scalar i32 false true]
 [.scalarReference 0,.vectorReference 0,.value (.literal i32 7)]).getD original
 def changed : Option State := do
  let step ← (Proofs.CppState.Stmt.assign 0 (.literal i32 17)).run entered.scalars
  let step ← (Proofs.CppState.Stmt.assign 1 (.literal i32 99)).run step.state
  let scalars := step.state
  let vectors ← entered.vectors.write ⟨0,i32,true,⟨0,0,0⟩⟩ 17
  let vectors ← vectors.reserve 0 i32 5
  let (vectors,_) ← vectors.construct i32 true 100 2 6
  some ({entered with scalars := scalars,vectors := vectors} : State).observe
 def returned : Option State := do
  let callee ← changed
  finishScalar original callee i32 42
#guard entered.scalars.environment == some [7,7]
#guard (changed.map (·.scalars.environment)) == some (some [17,99])
#guard (returned.map (·.scalars.environment)) == some (some [17,42])
#guard (returned.map (·.scalars.memory)) == some [⟨i32,17⟩,⟨i32,42⟩]
#guard (returned.map (·.scalars.bindings)) == some [⟨0,true⟩,⟨1,false⟩]
#guard (returned.map (·.slots)) == some [.scalar 0,.vector 0,.scalar 1]
#guard (returned.map (·.vectors.bindings)) == some original.vectors.bindings
#guard (returned.map (·.vectors.store.objects)) == some [some ⟨0,[17,8],5,100,1⟩,none]
#guard (returned.map (·.vectors.types)) == some [⟨i32,true⟩,⟨i32,true⟩]
#guard (returned.bind (fun s => s.vectors.object 1 i32)) == none
#guard (returned.bind (fun s => s.vectors.read ⟨0,i32,true,⟨0,0,0⟩⟩)) == none
#guard (returned.bind (fun s => s.vectors.elementRef 0 i32 0)) == some ⟨0,i32,true,⟨0,1,0⟩⟩
#guard (returned.bind (fun s => s.vectors.construct i32 true 100 0 0) |>.map
 (fun r => r.1.bindings.getLast?)) == some (some ⟨2,i32,true⟩)
#guard (changed.bind (fun s => finishScalar original s i32 2147483648)) == none
#guard finishScalar original caller i32 0 == none
#guard (changed.bind (fun s => finishScalar original
 {s with vectors := {s.vectors with types := [⟨u64,true⟩,⟨i32,true⟩]}} i32 0)) == none
#guard (changed.bind (fun s => finishScalar original
 {s with scalars := {s.scalars with memory := [⟨u64,17⟩]}} i32 0)) == none
#guard (changed.bind (fun s => finishScalar original
 {s with vectors := {s.vectors with store := {s.vectors.store with objects := [none,none]}}} i32 0)) == none
#guard (returned.map (fun s => s.work)) == some 20
#guard (returned.map (fun s => s.peak)) == some 15
"""
        with tempfile.TemporaryDirectory(prefix='mixed-return-') as directory:
            scratch=Path(directory);self.lean(scratch,checks)
            source=scratch/'native.cpp'
            source.write_text("""#include "experiments/library/cpp/template/small_template.hpp"
#include <vector>
#include <cassert>
int update(int& x,std::vector<int>& v,int copy){
  const int& readonly=x; const std::vector<int>& view=v;
  x=17;copy=99;v[0]=17;v.reserve(5);
  std::vector<int> local(2,6);
  assert(readonly==17 && view[0]==17 && copy==99 && local[1]==6);
  return 42;
}
int main(){int x=7;std::vector<int> v{3,8};int answer=update(x,v,x);
 assert(x==17 && answer==42 && v==std::vector<int>({17,8}) && v.capacity()==5);
 std::vector<int> subsequent;assert(subsequent.empty());}
""")
            check_compiler();executable=scratch/'native'
            subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all',
                '-I',str(ROOT),str(source),'-o',str(executable)],cwd=ROOT,check=True)
            subprocess.run([str(executable)],check=True)
        print(f'mixed return: {checks.count("#guard")} checks and C++17 UBSan alias/value/scope scenario')

if __name__ == '__main__':
    disable_network();unittest.main()
