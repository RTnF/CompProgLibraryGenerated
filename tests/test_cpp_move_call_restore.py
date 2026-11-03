"""Non-resizing scalar call restoration and original UF methods after class move."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from check_public import check_compiler
from test_cpp_move_headers import CHECKS as HEADER_CHECKS
from test_cpp_move_frame import CHECKS as FRAME_CHECKS
from test_cpp_move_write import CHECKS as WRITE_CHECKS
from test_cpp_move_context import CHECKS as CONTEXT_CHECKS
from test_cpp_move_restore import CHECKS as RESTORE_CHECKS
from offline import disable_network

CHECKS = r'''

namespace CallRestoreExamples
open Proofs.CppMoveCallRestore Proofs.CppMoveRestore Proofs.CppMoveContext
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open HeaderMoveExamples ViewExamples FrameExamples ContextExamples

def program : NProgram := ⟨[.vector ty true,.scalar ty true true],.scalar ty,
  .sequence (.primitive (.write (.local 0) ty (.literal ty 0) (.literal ty 42)))
  (.sequence (.primitive (.assign 1 ty (.literal ty 9)))
    (.primitive (.ret (.variable ty 1))))⟩
def args : List NArgument := [.vectorReference 3,.scalarReference 1]
def result : NState × Ret := match program.callFuel 8 (project callerContext ty) args with
  | .finished pair => pair
  | _ => (project callerContext ty,.unit)
theorem ran : program.callFuel 8 (project callerContext ty) args = .finished result := by decide +kernel
#guard result.2 == .scalar 9
#guard result.1.frame.state.wellFormed
#guard result.1.scalars.memory.map (·.value) == [9]
#guard (restoreContext callerContext ty result.1).isSome
def restored := (restoreContext callerContext ty result.1).getD callerContext
#guard project restored ty == result.1
#guard Proofs.CppMoveHeaders.read restored.objects.heap ty.valid 1 == some 42
#guard restored.scalars.memory.map (·.value) == [9]
example := call_restore_ready program 8 callerContext ty ty args result.1 result.2 rfl
  (by decide) RestoreExamples.contexts transferredCovered ran

theorem restoredRun : restoreContext callerContext ty result.1 = some restored := by
  have live : (restoreContext callerContext ty result.1).isSome = true := by decide +kernel
  have nonempty : restoreContext callerContext ty result.1 ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty callerContext).symm
example := call_restore_result program 8 callerContext restored ty args result.1 result.2 ran restoredRun transferredCovered
#guard program.callFuel 0 (project callerContext ty) args == .exhausted
#guard program.callFuel 8 (project callerContext ty) [.vectorReference 0,.scalarReference 1] == .fault
end CallRestoreExamples

namespace CallRestoreRejections
open Proofs.CppMoveCallRestore Proofs.CppNestedCall Proofs.CppNestedProgram
open Proofs.CppMoveContext ContextExamples FrameExamples
 def resize : NProgram := ⟨[],.scalar ty,.sequence
   (.primitive (.reserve (.local 3) ty (.literal ty 8))) (.primitive (.ret (.literal ty 0)))⟩
 #guard eligible resize == false
 #guard (match restoreCallFuel resize 32 callerContext ty [] with | .fault => true | _ => false)
 def unit : NProgram := ⟨[],.unit,.primitive .retUnit⟩
 #guard eligible unit == false
 #guard (match restoreCallFuel unit 32 callerContext ty [] with | .fault => true | _ => false)
end CallRestoreRejections
'''

UF_CHECKS = r'''

namespace UfMoveCallExamples
open Proofs.CppMoveCallRestore Proofs.CppMoveRestore Proofs.CppMoveContext
open Proofs.CppMoveHeaders Proofs.CppMoveClass Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open Proofs.CppScalar
abbrev ty : Ty := ⟨32,true,false⟩
abbrev limit := Proofs.CppVectorBindings.sizeLimit ty

def original : Context := ⟨⟨⟨[some ⟨some 0,0,true,limit⟩,some ⟨some 1,0,true,limit⟩],
  [some ⟨⟨0,[-4,0,0,2],5,limit,0⟩,fun _ => 7⟩,some ⟨⟨1,[-1],2,limit,0⟩,fun _ => 0⟩],[],0,0,0⟩,
  [⟨0,true⟩,⟨1,true⟩]⟩,
  ⟨[⟨ty,1⟩,⟨ty,4⟩,⟨ty,1⟩,⟨ty,1⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩],0,0,0⟩,
  [.vector 0,.scalar 0,.scalar 1,.vector 1,.scalar 2,.scalar 3],1,0⟩
def capturedSource := (capture original.objects.heap ty.valid 0 3 false).getD (original.objects.heap,0)
def capturedTarget := (capture capturedSource.1 ty.valid 1 0 false).getD (capturedSource.1,0)
def before := {original with objects := {original.objects with heap := capturedTarget.1}}
def moved := (assignClass before ⟨3,[4,5]⟩ ⟨0,[1,2]⟩ Proofs.UfClassCopyBridge.profile).getD (before,⟨0,[]⟩)
#guard (assignClass before ⟨3,[4,5]⟩ ⟨0,[1,2]⟩ Proofs.UfClassCopyBridge.profile).isSome
#guard moved.1.scalars.memory.map (·.value) == [1,4,1,4]
#guard Proofs.CppMoveHeaders.read moved.1.objects.heap ty.valid 0 == some 2
#guard (Proofs.CppMoveHeaders.read moved.1.objects.heap ty.valid 1).isNone
#guard moved.1.objects.heap.header 0 == some ⟨none,0,true,limit⟩

def args : List NArgument := [.vectorReference 3,.scalarReference 4,
  .value (.variable ty 5),.value (.literal ty 3),.value (.literal ty 1)]
def result : NState × Ret := match Proofs.UnionFindCandidateInstance.UnionFind_same.callFuel 128 (project moved.1 ty) args with
  | .finished pair => pair
  | _ => (project moved.1 ty,.unit)
theorem ran : Proofs.UnionFindCandidateInstance.UnionFind_same.callFuel 128 (project moved.1 ty) args = .finished result := by decide +kernel
#guard result.2 == .scalar 1
#guard (restoreContext moved.1 ty result.1).isSome
def restored := (restoreContext moved.1 ty result.1).getD moved.1
#guard Proofs.CppMoveHeaders.read restored.objects.heap ty.valid 0 == some 0
#guard (Proofs.CppMoveHeaders.read restored.objects.heap ty.valid 1).isNone
#guard (restored.objects.heap.allocation 0).map (fun t => (t.buffer.items,t.generation 3)) == some ([-4,0,0,0],7)
#guard restored.scalars.memory.map (·.value) == [1,4,1,4]
#guard project restored ty == result.1

theorem covered : OwnsAll moved.1.objects.heap := by
  intro owner tracked found
  have bound : owner < moved.1.objects.heap.allocations.length := by
    unfold Heap.allocation at found
    cases raw : moved.1.objects.heap.allocations[owner]? with
    | none => simp [raw] at found
    | some value => exact (List.getElem?_eq_some_iff.mp raw).1
  change owner < 2 at bound
  have choices : owner = 0 ∨ owner = 1 := by omega
  rcases choices with rfl | rfl
  · exact ⟨1,⟨some 0,0,true,limit⟩,rfl,rfl⟩
  · contradiction
theorem contexts : ∀ owner scope, (project moved.1 ty).frame.state.forest.context owner = some scope → scope ≤ moved.1.scope := by
  intro owner scope found
  have forestEq : (project moved.1 ty).frame.state.forest =
    ⟨[some ⟨.integer ty,none,some 0,[]⟩,none,some ⟨.integer ty,none,some 0,[]⟩,none]⟩ := rfl
  rw [forestEq] at found
  rcases owner with _ | owner
  · have ctx := context_of_root ⟨[some ⟨.integer ty,none,some 0,[]⟩,none,some ⟨.integer ty,none,some 0,[]⟩,none]⟩ 0 ⟨.integer ty,none,some 0,[]⟩ rfl rfl
    rw [ctx] at found
    cases Option.some.inj found
    decide
  rcases owner with _ | owner
  · rw [context_of_none ⟨[some ⟨.integer ty,none,some 0,[]⟩,none,some ⟨.integer ty,none,some 0,[]⟩,none]⟩ 1 rfl] at found
    contradiction
  rcases owner with _ | owner
  · have ctx := context_of_root ⟨[some ⟨.integer ty,none,some 0,[]⟩,none,some ⟨.integer ty,none,some 0,[]⟩,none]⟩ 2 ⟨.integer ty,none,some 0,[]⟩ rfl rfl
    rw [ctx] at found
    cases Option.some.inj found
    decide
  rcases owner with _ | owner
  · rw [context_of_none ⟨[some ⟨.integer ty,none,some 0,[]⟩,none,some ⟨.integer ty,none,some 0,[]⟩,none]⟩ 3 rfl] at found
    contradiction
  · rw [context_of_none ⟨[some ⟨.integer ty,none,some 0,[]⟩,none,some ⟨.integer ty,none,some 0,[]⟩,none]⟩ (owner+4) rfl] at found
    contradiction


def buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value := ⟨0,[-4,0,0,2].map .integer,5,limit,0⟩
theorem ownerOK : Proofs.UfFindCall.VOKWF (project moved.1 ty) 3 3 0 0 buffer :=
  ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
   by decide +kernel,by decide +kernel,contexts,by decide +kernel⟩
 def parents : List Int := [-4,0,0,2]
 def ranks (i : Nat) : Nat := if i=0 then 0 else if i=2 then 1 else 2
 theorem parentForest : Proofs.UfRootCall.Forest parents ranks := by
   refine ⟨?_,?_,?_⟩
   · intro x member; simp [parents] at member
     rcases member with rfl | rfl | rfl <;> decide +kernel
   · intro i p found nonneg
     have inside := (List.getElem?_eq_some_iff.mp found).1
     have small : i < 4 := inside
     have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
     rcases choices with rfl | rfl | rfl | rfl <;> simp [parents] at found <;> subst p <;> omega
   · intro i p found nonneg
     have inside := (List.getElem?_eq_some_iff.mp found).1
     have small : i < 4 := inside
     have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
     rcases choices with rfl | rfl | rfl | rfl <;> simp [parents] at found <;> subst p <;> first | omega | decide +kernel

theorem normalTerminates : Proofs.UnionFindCandidateInstance.UnionFind_same.Terminates (project moved.1 ty) args := by
  obtain ⟨init,fuel,out,r1,r2,middle,final,_,ran,_⟩ :=
    Proofs.UfFieldsSame.same_call (cslot := 4) (project moved.1 ty) ownerOK ⟨2,true⟩ 1 (by decide +kernel) rfl
      parents ranks parentForest (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl
      (.variable ty 5) (.literal ty 3) (.literal ty 1) 3 1 rfl rfl rfl rfl rfl rfl
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨fuel,(out,_),ran⟩
example := call_restore_terminates Proofs.UnionFindCandidateInstance.UnionFind_same moved.1 ty
  Proofs.PrefixSumsCall.bT args rfl (by decide) contexts covered normalTerminates
example := call_restore_ready Proofs.UnionFindCandidateInstance.UnionFind_same 128 moved.1 ty
  Proofs.PrefixSumsCall.bT args result.1 result.2 rfl (by decide) contexts covered ran

def call := restoreCallFuel Proofs.UnionFindCandidateInstance.UnionFind_same 128 moved.1 ty args
#guard (match call with
  | .finished (out,result) => result == .scalar 1 && Proofs.CppMoveHeaders.read out.objects.heap ty.valid 0 == some 0
  | _ => false)
example := restoreCallFuel_ready Proofs.UnionFindCandidateInstance.UnionFind_same 128 moved.1 ty
  Proofs.PrefixSumsCall.bT args result.1 result.2 rfl (by decide) contexts covered ran
#guard (match restoreCallFuel Proofs.UnionFindCandidateInstance.UnionFind_root 64 restored ty
    [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3)] with
  | .finished (_,r) => r == .scalar 0
  | _ => false)
#guard (match restoreCallFuel Proofs.UnionFindCandidateInstance.UnionFind_size 64 restored ty
    [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3)] with
  | .finished (_,r) => r == .scalar 4
  | _ => false)
#guard (match restoreCallFuel Proofs.UnionFindCandidateInstance.UnionFind_unite 128 restored ty args with
  | .finished (_,r) => r == .scalar 0
  | _ => false)
#guard (match restoreCallFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups 16 restored ty
    [.vectorReference 3,.scalarReference 4,.value (.variable ty 5)] with
  | .finished (_,r) => r == .scalar 1
  | _ => false)
#guard (match restoreCallFuel Proofs.UnionFindCandidateInstance.UnionFind_root 64 moved.1 ty
    [.vectorReference 0,.scalarReference 1,.value (.variable ty 2),.value (.literal ty 3)] with
  | .fault => true
  | _ => false)
end UfMoveCallExamples
'''

NATIVE = r'''

#include <cassert>
#include <utility>
#include "experiments/verification/data_structure/union_find.hpp"
int main(){
  cp::UnionFind source(4),target(1);
  source.unite(0,1);source.unite(2,3);source.unite(0,2);
  target=std::move(source);
  assert(target.same(3,1));assert(target.root(3)==0);assert(target.size(3)==4);
  assert(target.num_groups()==1);assert(target.unite(3,1)==0);
  assert(source.num_groups()==1);
  source=cp::UnionFind(3);source.unite(0,2);
  assert(source.num_groups()==2 && source.size(2)==2 && !source.same(1,2));
  target=std::move(target);assert(target.num_groups()==1);
  target=cp::UnionFind(2);assert(target.num_groups()==2 && target.size(0)==1);
}
'''

class MoveCallRestoreTests(unittest.TestCase):
    def check_lean(self,imports,checks):
        with tempfile.TemporaryDirectory(prefix='move-call-restore-') as directory:
            proof=Path(directory)/'checks.lean';proof.write_text(imports+checks)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_scalar_call_updates_return_and_rejections(self):
        self.check_lean('import Proofs.CppMoveCallRestore\n',
            HEADER_CHECKS+FRAME_CHECKS+WRITE_CHECKS+CONTEXT_CHECKS+RESTORE_CHECKS+CHECKS)

    def test_original_uf_after_move_and_normal_termination(self):
        self.check_lean('import Proofs.CppMoveCallRestore\nimport Proofs.UfClassCopyBridge\n'
            'import Proofs.UfFieldsSame\nimport Proofs.UfFieldsSize\n'
            'import Proofs.UfFieldsUnite\nimport Proofs.UfFieldsCounter\n',UF_CHECKS)

    def test_native_original_uf_move_methods_and_reassignment(self):
        check_compiler()
        with tempfile.TemporaryDirectory(prefix='uf-move-call-native-') as directory:
            source=Path(directory)/'check.cpp';binary=Path(directory)/'check'
            source.write_text(NATIVE)
            subprocess.run(['g++','-std=c++17','-O1','-I',str(ROOT),'-fsanitize=address,undefined',
                '-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0:abort_on_error=1'
            subprocess.run([str(binary)],env=env,check=True)

if __name__=='__main__':
    disable_network()
    unittest.main()
