"""Source-expression copies release row temporaries and retain the new owner."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_cpp_nested_copy import HEADER, CHECKS as FIXTURE
from test_append_row import initial
from test_scalar_ir import lean_environment
from check_public import FLAGS, check_compiler
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent

CHECKS = r'''
namespace CopyStatementChecks
open Proofs.CppNestedProgram Proofs.CppCopyStatementFacts
 def entry : NState := ⟨⟨[⟨i32,1⟩],[⟨0,true⟩],13,1,700⟩,before,
   (List.range before.bindings.length).map (fun i => .vector i) ++ [.scalar 0],9,100000000⟩
 def selected : Container := .row (.local 1) atom (.variable i32 5)
 def evaluated := (selected.eval entry).getD (entry,999)
 #guard evaluated.2 == before.bindings.length
 #guard evaluated.1.frame.bindings.length == before.bindings.length+1
 #guard (evaluated.1.release entry).frame.bindings == before.bindings
 def rowStep := Proofs.CppCopyStatement.run entry selected i32 true
 def rowOut := (rowStep.getD ⟨entry,none,false⟩).state
 #guard rowStep.isSome
 #guard rowOut.frame.state.wellFormed
 #guard rowOut.vectorSlot entry.slots.length == some before.bindings.length
 #guard rowOut.frame.bindings.length == before.bindings.length+1
 #guard rowOut.frame.bindings.take before.bindings.length == before.bindings
 #guard (rowOut.frame.bindings[before.bindings.length]?).map (fun b => (b.owner,b.writable,b.header)) ==
   some (6,true,.root 9)
 #guard (rowOut.frame.state.storage.lookup 6).map (fun b => (b.items,b.capacity,b.epoch,b.limit)) ==
   some ([.integer 11,.integer (-1)],2,0,64)
 #guard rowOut.frame.state.storage.lookup 2 == before.state.storage.lookup 2
 #guard rowOut.frame.state.storage.lookup 5 == none
 #guard rowOut.scalarCell 5 i32 == entry.scalarCell 5 i32
 #guard rowOut.work == entry.work+7
 #guard rowOut.frame.state.liveSpace == before.state.liveSpace+3
 #guard rowOut.frame.state.storage.peak == max before.state.storage.peak (before.state.liveSpace+4-17)
 #guard rowOut.scalars.baseMemory == 1
 #guard rowOut.scalars.peak == 700
 #guard rowOut.peak == 100000000
 #guard rowOut.frame.read saved == before.read saved
 def fresh := (rowOut.frame.elementRef before.bindings.length i32 1).getD saved
 #guard rowOut.frame.read fresh == some (-1)
 def changedCopy := (rowOut.frame.write fresh 42).getD before
 #guard changedCopy.read saved == some (-1)
 #guard changedCopy.read fresh == some 42
 def changedSource := (rowOut.frame.write saved 99).getD before
 #guard changedSource.read fresh == some (-1)
 #guard changedSource.read saved == some 99
 def localOut := ((Proofs.CppCopyStatement.run entry (.local 4) i32 true).getD ⟨entry,none,false⟩).state
 #guard localOut.work == entry.work+5
 #guard localOut.frame.state.storage.objects == rowOut.frame.state.storage.objects
 def constOut := ((Proofs.CppCopyStatement.run entry selected i32 false).getD ⟨entry,none,false⟩).state
 def constRef := (constOut.frame.elementRef before.bindings.length i32 1).getD saved
 #guard constOut.frame.read constRef == some (-1)
 #guard (constOut.frame.write constRef 42).isNone
 #guard constOut.frame.read saved == some (-1)
 #guard constOut.frame.state.wellFormed
 #guard constOut.frame.state.storage.objects == rowOut.frame.state.storage.objects
 #guard (Proofs.CppCopyStatement.run entry (.local 999) i32 true).isNone
 #guard (Proofs.CppCopyStatement.run entry (.local 0) i32 true).isNone
 #guard (Proofs.CppCopyStatement.run entry (.row (.local 1) atom (.literal i32 3)) i32 true).isNone
 #guard (Proofs.CppCopyStatement.run entry selected ⟨64,false,false⟩ true).isNone
 #guard (Proofs.CppCopyStatement.run {entry with frame := {before with rootWritable := []}} selected i32 true).isNone
 def emptyEntry : NState := ⟨⟨[],[],0,0,0⟩,empty,[.vector 0],3,0⟩
 def emptyStep := Proofs.CppCopyStatement.run emptyEntry (.local 0) i32 true
 def emptyState := (emptyStep.getD ⟨emptyEntry,none,false⟩).state
 #guard emptyStep.isSome
 #guard emptyState.work == emptyEntry.work+3
 #guard (emptyState.frame.state.storage.lookup 1).map (fun b => (b.items,b.capacity,b.epoch)) == some ([],0,0)
 #guard emptyState.frame.bindings.length == 2
 example := completes entry evaluated.1 selected evaluated.2
   ((evaluated.1.frame.resolve evaluated.2 atom).getD (origin,source)).1 source i32 true
   (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
 example := result_cost entry evaluated.1 source i32 true (by decide +kernel)
 example := keeps_read entry evaluated.1 selected evaluated.2
   ((evaluated.1.frame.resolve evaluated.2 atom).getD (origin,source)).1 source i32 true
   (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) saved (-1) (by decide +kernel)
 example (f : Frame) (slot : Nat) (ty : Ty) (scope : Nat) (wr : Bool)
   (b : Binding) (buf : Buffer Value) (h : f.resolve slot (.integer ty) = some (b,buf)) :=
   copy_vector_owner f slot ty scope wr b buf h
 example (caller next : NState) (buf : Buffer Value) (element ty : Ty) (wr : Bool)
   (slot : Nat) (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
   (found : next.scalarCell slot ty = some (binding,cell)) :=
   keeps_scalar caller next buf element wr slot ty binding cell found
 example (f : Frame) (bindings : List Binding) (owner : Nat) (ty : Ty) (scope : Nat) (wr : Bool) :=
   copy_owner_rebind f bindings owner ty scope wr
end CopyStatementChecks
'''

class CopyStatementTests(unittest.TestCase):
    def test_expression_temporaries_fresh_bindings_costs_and_permissions(self):
        proof = ('import Proofs.CppCopyStatementFacts\n' + HEADER +
                 f'\ndef initial := {initial(3,8)}\n' + FIXTURE + CHECKS)
        with tempfile.TemporaryDirectory(prefix='copy-statement-') as directory:
            path = Path(directory)/'checks.lean'; path.write_text(proof)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(path)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_native_const_parent_dynamic_index_and_const_target(self):
        check_compiler()
        source = r'''
#include <cassert>
#include <vector>
int main(){
  std::vector<std::vector<int>> parent{{10,0},{11,-1},{12,-2}};
  parent[1].reserve(17);
  const auto& input=parent; int index=1; int* saved=&parent[1][1];
  std::vector<int> copy(input[index]); const std::vector<int> immutable(input[index]);
  assert(copy.capacity()==2 && immutable.capacity()==2 && input[index].capacity()==17);
  copy[1]=42; assert(*saved==-1 && immutable[1]==-1);
  *saved=99; assert(copy[1]==42 && immutable[1]==-1);
  parent.clear(); assert(copy[0]==11 && immutable[0]==11);
}
'''
        with tempfile.TemporaryDirectory(prefix='copy-statement-native-') as directory:
            path = Path(directory)/'checks.cpp'; path.write_text(source)
            binary = Path(directory)/'checks'
            result = subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all',
                                     str(path),'-o',str(binary)],cwd=ROOT,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            result = subprocess.run([str(binary)],cwd=ROOT,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
