"""Fresh scalar-vector roots inside mixed forests, permissions and reference lifetimes."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_append_row import initial
from test_scalar_ir import lean_environment
from check_public import FLAGS, check_compiler
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
HEADER = '''import Proofs.CppFrameCopy
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedConstruct Proofs.CppNestedCopy Proofs.CppFrameCopy
 def i32 : Ty := ⟨32,true,false⟩
 def atom : Element := .integer i32
 def row : Element := .vector atom
'''

CHECKS = r'''
 def mutableChild := ((initial.bindChild 0 atom 1 true).map Prod.fst).getD initial
 def reserved := (mutableChild.reserve 3 atom 17).getD mutableChild
 def before := ((reserved.bindChild 1 atom 1 false).map Prod.fst).getD reserved
 def source : Buffer Value := (before.state.storage.lookup 2).getD ⟨0,[],0,64,0⟩
 def origin : Binding := (before.bindings[4]?).getD ⟨0,atom,false,.root 0⟩
 def saved := (before.elementRef 3 i32 1).getD ⟨0,i32,false,⟨0,0,0⟩⟩
 #guard before.state.wellFormed
 #guard before.state.forest.objects.length == 6
 #guard before.state.storage.lookup 5 == none
 #guard before.state.storage.baseSpace == 17
 #guard before.state.liveSpace == 32
 #guard source.items == [.integer 11,.integer (-1)]
 #guard source.capacity == 17
 #guard origin.writable == false
 #guard before.read saved == some (-1)
 example := copy_vector_runs before 4 i32 9 true origin source (by decide +kernel)
   (by decide +kernel) (by decide +kernel)
 example := copy_vector_extends before 4 i32 9 true origin source (by decide +kernel)
   (by decide +kernel) (by decide +kernel)
 example := clone_cost before.state source i32 9 (by decide +kernel)
 example := copied_resolve before source i32 9 true (by decide +kernel) (by decide +kernel)
   (by decide +kernel) (by decide +kernel)
 example := copied_element_ref before source i32 9 1 true (by decide +kernel)
   (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
 def actual := copyVector before 4 i32 9 true
 def after := (actual.getD (before,999)).1
 #guard actual == some (copiedFrame before source i32 9 true,5)
 #guard after.state.wellFormed
 #guard after.state.storage.objects.length == 7
 #guard after.state.storage.lookup 5 == none
 #guard (after.state.storage.lookup 6).map (fun b => (b.items,b.capacity,b.epoch)) ==
   some ([.integer 11,.integer (-1)],2,0)
 #guard after.state.liveSpace == 35
 #guard after.state.storage.work == before.state.storage.work+3
 #guard after.state.storage.peak == max before.state.storage.peak (before.state.liveSpace+4-17)
 #guard after.state.storage.baseSpace == before.state.storage.baseSpace
 #guard after.bindings.take 5 == before.bindings
 #guard after.rootWritable.take 6 == before.rootWritable
 example := copy_vector_success before after 4 5 i32 9 true (by decide +kernel)
 example := copy_vector_keeps_read before 4 i32 9 true origin source saved (-1)
   (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
 def fresh := (after.elementRef 5 i32 1).getD saved
 #guard fresh == ⟨5,i32,true,⟨6,0,1⟩⟩
 #guard after.read fresh == some (-1)
 #guard after.read saved == before.read saved
 #guard (after.write fresh 42).isSome
 def changed := (after.write fresh 42).getD before
 #guard changed.read fresh == some 42
 #guard changed.read saved == some (-1)
 #guard changed.state.storage.lookup 2 == before.state.storage.lookup 2
 #guard changed.state.storage.lookup 0 == before.state.storage.lookup 0
 #guard changed.state.storage.lookup 4 == before.state.storage.lookup 4
 example := copied_write_old before source i32 9 1 changed 42 2 (by decide +kernel) (by decide +kernel)
 example := copied_write_old before source i32 9 1 changed 42 5 (by decide +kernel) (by decide +kernel)
 def oldGone : Frame := {after with state := after.state.retired 0}
 #guard oldGone.state.wellFormed
 #guard (oldGone.read saved).isNone
 #guard oldGone.read fresh == some (-1)
 def copyGone : Frame := {after with state := after.state.retired 9}
 #guard copyGone.state.wellFormed
 #guard (copyGone.read fresh).isNone
 #guard copyGone.read saved == some (-1)
 #guard (copyVector before 0 i32 9 true).isNone
 #guard (copyVector before 999 i32 9 true).isNone
 #guard (copyVector {before with rootWritable := []} 4 i32 9 true).isNone
 #guard (after.read {fresh with address := {fresh.address with epoch := 1}}).isNone
 #guard (after.read {fresh with slot := saved.slot}).isNone
 def high : Frame := {before with state := {before.state with storage := {before.state.storage with peak := 100000,baseSpace := 7}}}
 def highOut := ((copyVector high 4 i32 9 true).getD (before,999)).1
 #guard highOut.state.storage.peak == 100000
 #guard highOut.state.storage.baseSpace == 7
 #guard highOut.state.liveSpace == high.state.liveSpace+3
 example := copy_vector_success high highOut 4 5 i32 9 true (by decide +kernel)
 def empty : Frame := ⟨⟨⟨[some ⟨atom,none,some 0,[]⟩]⟩,⟨[some ⟨0,[],17,64,3⟩],0,20,18⟩⟩,
   [false],[⟨0,atom,false,.root 0⟩]⟩
 def emptyOut := ((copyVector empty 0 i32 3 true).getD (empty,999)).1
 #guard emptyOut.state.wellFormed
 #guard emptyOut.state.liveSpace == 19
 #guard (emptyOut.state.storage.lookup 1).map (fun b => (b.items,b.capacity,b.epoch)) == some ([],0,0)
 #guard (emptyOut.elementRef 1 i32 0).isNone
 example := copy_vector_success empty emptyOut 0 1 i32 3 true (by decide +kernel)
 example (f out : Frame) (slot index : Nat) (ty : Ty) (scope : Nat) (writable : Bool)
   (success : copyVector f slot ty scope writable = some (out,index)) :=
   copy_vector_success f out slot index ty scope writable success
 example (f : Frame) (source : Buffer Value) (ty : Ty) (scope : Nat)
   (shape : f.state.forest.objects.length = f.state.storage.objects.length) :=
   clone_cost f.state source ty scope shape
'''

class NestedCopyTests(unittest.TestCase):
    def test_nested_root_copy_and_reference_lifetimes(self):
        checks = HEADER + f'\ndef initial := {initial(3,8)}\n' + CHECKS
        for case, (slot,owner,values) in enumerate([(4,2,[11,-1]),(2,4,[77])]):
            for writable in [False,True]:
                name=f'copy{case}_{int(writable)}'
                flag=str(writable).lower()
                checks+=f'''
 def {name} := ((copyVector before {slot} i32 9 {flag}).getD (before,999)).1
 #guard {name}.state.wellFormed
 #guard {name}.state.storage.lookup {owner} == before.state.storage.lookup {owner}
 #guard {name}.resolve 5 atom == some (copyBinding before i32 9 {flag},
   Proofs.CppVectorCopy.copied ((before.state.storage.lookup {owner}).getD source) 6)
 def {name}_ref := ({name}.elementRef 5 i32 0).getD saved
 #guard {name}.read {name}_ref == some {values[0]}
 #guard ({name}.write {name}_ref 42).isSome == {flag}
 example := copy_vector_success before {name} {slot} 5 i32 9 {flag} (by decide +kernel)
'''
        with tempfile.TemporaryDirectory(prefix='cpp-nested-copy-') as directory:
            proof = Path(directory)/'checks.lean';proof.write_text(checks)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_native_nested_source_copy(self):
        check_compiler()
        source=r'''
#include <cassert>
#include <vector>
int main(){
  std::vector<std::vector<int>> parent{{10,0},{11,-1},{12,-2}};
  parent.reserve(8); parent[1].reserve(17);
  const auto& source=parent[1];
  int* saved=&parent[1][1];
  std::vector<int> copy(source);
  assert(copy==source && copy.capacity()==2 && source.capacity()==17);
  assert(&copy[1]!=saved && *saved==-1);
  copy[1]=42; assert(*saved==-1 && source[1]==-1);
  parent.reserve(40); assert(*saved==-1 && copy[1]==42);
  parent.clear(); assert(copy[0]==11 && copy[1]==42);
  std::vector<int> empty; empty.reserve(17);
  std::vector<int> emptyCopy(empty);
  assert(emptyCopy.empty() && emptyCopy.capacity()==0 && empty.capacity()==17);
}
'''
        with tempfile.TemporaryDirectory(prefix='cpp-nested-copy-native-') as directory:
            path=Path(directory)/'checks.cpp';path.write_text(source)
            executable=Path(directory)/'checks'
            result=subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all',str(path),'-o',str(executable)],cwd=ROOT,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            result=subprocess.run([str(executable)],cwd=ROOT,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
