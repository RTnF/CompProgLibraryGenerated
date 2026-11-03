"""Actual UF assignment restores a destination and preserves disjoint receivers."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'tests'),str(ROOT/'tools')]
from test_scalar_ir import lean_environment
from offline import disable_network

CHECKS = r'''
import Proofs.UfAssignment
import Proofs.UfAssignmentView
import Proofs.UfAssignmentWork
open Proofs.CppNestedConstruct
open Proofs.CppScalar Proofs.CppVector Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish Proofs.CppLoop
open Proofs.UfReceiverState Proofs.UfFindCall Proofs.UfAssignment Proofs.CppClassAssign
open Proofs.DoublingNested (i32)
def buffer (owner n : Nat) : Buffer Value :=
  ⟨owner,List.replicate n (.integer (-1)),n,Proofs.CppVectorBindings.sizeLimit i32,0⟩
def state : NState :=
  ⟨⟨[⟨i32,-7⟩,⟨i32,99⟩,⟨i32,2⟩,⟨i32,2⟩,⟨i32,3⟩,⟨i32,3⟩],
    [⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩,⟨4,true⟩,⟨5,true⟩],0,0,0⟩,
   ⟨⟨⟨[some (flatTag i32 0),some (flatTag i32 0),some (flatTag i32 0)]⟩,
     ⟨[some (buffer 0 4),some (buffer 1 2),some (buffer 2 3)],0,0,0⟩⟩,
     [true,true,true],[⟨0,.integer i32,true,.root 0⟩,⟨1,.integer i32,true,.root 0⟩,⟨2,.integer i32,true,.root 0⟩]⟩,
   [.vector 0,.scalar 0,.scalar 1,.vector 1,.scalar 2,.scalar 3,.vector 2,.scalar 4,.scalar 5],0,0⟩
def target : Layout := ⟨0,0,0,0,1,2⟩
def source : Layout := ⟨3,1,1,0,4,5⟩
def other : Layout := ⟨6,2,2,0,7,8⟩
theorem strict : ∀ owner c, state.frame.state.forest.context owner = some c → c ≤ state.scope := by
  intro owner c found
  have inside := Proofs.UfConstructedReceiver.context_inside state.frame.state.forest owner c found
  have size : state.frame.state.forest.objects.length = 3 := rfl
  have bound : owner < 3 := by omega
  have contexts : ∀ i : Fin 3, state.frame.state.forest.context i.val = some 0 := by decide +kernel
  rw [contexts ⟨owner,bound⟩] at found
  cases found
  exact Nat.le_refl _
theorem targetOK : VOKWF state target.vectorSlot target.vectorBinding target.owner target.scope (buffer 0 4) :=
  ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
   by decide +kernel,by decide +kernel,strict,by decide +kernel⟩
theorem sourceOK : VOKWF state source.vectorSlot source.vectorBinding source.owner source.scope (buffer 1 2) :=
  ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
   by decide +kernel,by decide +kernel,strict,by decide +kernel⟩
theorem otherOK : VOKWF state other.vectorSlot other.vectorBinding other.owner other.scope (buffer 2 3) :=
  ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
   by decide +kernel,by decide +kernel,strict,by decide +kernel⟩
theorem sourceInv : Inv state source (List.replicate 2 (-1)) 2 (fun _ => 0) (buffer 1 2) ⟨2,true⟩ ⟨3,true⟩ :=
  ⟨sourceOK,rfl,by decide +kernel,rfl,rfl,Proofs.UfClassInvariant.initial_valid 2 (by decide),
   by decide +kernel,rfl,by decide +kernel,by decide +kernel⟩
theorem otherInv : Inv state other (List.replicate 3 (-1)) 3 (fun _ => 0) (buffer 2 3) ⟨4,true⟩ ⟨5,true⟩ :=
  ⟨otherOK,rfl,by decide +kernel,rfl,rfl,Proofs.UfClassInvariant.initial_valid 3 (by decide),
   by decide +kernel,rfl,by decide +kernel,by decide +kernel⟩
def assigned := (assignClass state (object target) (object source) Proofs.UfClassCopyBridge.profile).getD (state,object target)
theorem actual : assignClass state (object target) (object source) Proofs.UfClassCopyBridge.profile =
    some (assigned.1,object target) := by decide +kernel
example : ∃ out, assignClass state (object target) (object source) Proofs.UfClassCopyBridge.profile = some (out,object target) :=
  assignment_terminates state target source (buffer 0 4) (buffer 1 2) _ _ _ ⟨2,true⟩ ⟨3,true⟩ ⟨0,true⟩ ⟨1,true⟩
    ⟨i32,-7⟩ ⟨i32,99⟩ targetOK rfl sourceInv (by decide +kernel) (by decide +kernel) rfl rfl
theorem restored : Represents assigned.1 target (List.replicate 2 (-1)) 2 (fun _ => 0) :=
  assigned_represents state assigned.1 target source (buffer 0 4) (buffer 1 2) _ _ _
    ⟨2,true⟩ ⟨3,true⟩ ⟨0,true⟩ ⟨1,true⟩ ⟨i32,-7⟩ ⟨i32,99⟩ (object target) targetOK rfl sourceInv
    (by decide +kernel) (by decide +kernel) rfl (by decide) (by decide) actual
#guard assigned.1.scalars.memory.map (·.value) == ( [2,2,2,2,3,3] : List Int)
#guard (match Proofs.UnionFindCandidateInstance.UnionFind_size.callFuel 128 assigned.1
    (arguments target ++ [.value (.literal i32 0)]) with
  | .finished (_, .scalar value) => value == 1 | _ => false)
example := getter_step assigned.1 target _ _ _ restored
-- Separation concerns concrete storage addresses, including slots that alias cells.
theorem separated (address : Nat) (left : 0 ≠ address) (right : 1 ≠ address) :
    Proofs.CppClassAssignValues.Separate state (object target).scalarSlots address := by
  have a := Proofs.CppClassAssignValues.separate_single state 1 i32 ⟨0,true⟩ ⟨i32,-7⟩ address (by decide +kernel) left
  have b := Proofs.CppClassAssignValues.separate_single state 2 i32 ⟨1,true⟩ ⟨i32,99⟩ address (by decide +kernel) right
  intro slot member index binding lookup found
  have alternatives : slot = 1 ∨ slot = 2 := by simpa [object,target] using member
  rcases alternatives with rfl | rfl
  · exact a 1 (by simp) index binding lookup found
  · exact b 2 (by simp) index binding lookup found
example : Represents assigned.1 source (List.replicate 2 (-1)) 2 (fun _ => 0) :=
  preserves_other state assigned.1 target source source (buffer 0 4) (buffer 1 2) _ _ _ ⟨2,true⟩ ⟨3,true⟩
    (object target) targetOK sourceInv (by decide) (separated 2 (by decide) (by decide)) (separated 3 (by decide) (by decide)) actual
example : Represents assigned.1 other (List.replicate 3 (-1)) 3 (fun _ => 0) :=
  preserves_other state assigned.1 target source other (buffer 0 4) (buffer 2 3) _ _ _ ⟨4,true⟩ ⟨5,true⟩
    (object target) targetOK otherInv (by decide) (separated 4 (by decide) (by decide)) (separated 5 (by decide) (by decide)) actual
def selfAssigned := (assignClass state (object source) (object source) Proofs.UfClassCopyBridge.profile).getD (state,object source)
example : Represents selfAssigned.1 source (List.replicate 2 (-1)) 2 (fun _ => 0) :=
  assigned_represents state selfAssigned.1 source source (buffer 1 2) (buffer 1 2) _ _ _
    ⟨2,true⟩ ⟨3,true⟩ ⟨2,true⟩ ⟨3,true⟩ ⟨i32,2⟩ ⟨i32,2⟩ (object source) sourceOK rfl sourceInv
    (by decide +kernel) (by decide +kernel) rfl (by decide) (by decide) (by decide +kernel)
'''

READONLY_CHECKS = r'''
open Proofs.UfAssignmentView
-- Only the source view's binding permissions change; target access stays writable.
def readonly : NState := {state with
  scalars := {state.scalars with bindings := (state.scalars.bindings.set 2 ⟨2,false⟩).set 3 ⟨3,false⟩}
  frame := {state.frame with bindings := state.frame.bindings.set 1 ⟨1,.integer i32,false,.root 0⟩}}
theorem readonlyOK : VOKWF readonly target.vectorSlot target.vectorBinding target.owner target.scope (buffer 0 4) :=
  ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
   by decide +kernel,by decide +kernel,strict,by decide +kernel⟩
theorem view : SourceView readonly source (List.replicate 2 (-1)) 2 (fun _ => 0)
    (buffer 1 2) ⟨1,.integer i32,false,.root 0⟩ ⟨2,false⟩ ⟨3,false⟩ :=
  ⟨by decide +kernel,by decide +kernel,rfl,by decide +kernel,rfl,
   Proofs.UfClassInvariant.initial_valid 2 (by decide),by decide +kernel,by decide +kernel⟩
def roAssigned := (assignClass readonly (object target) (object source) Proofs.UfClassCopyBridge.profile).getD (readonly,object target)
example : ∃ out, assignClass readonly (object target) (object source) Proofs.UfClassCopyBridge.profile = some (out,object target) :=
  assign_ready readonly target source (buffer 0 4) (buffer 1 2) _ _ _ ⟨1,.integer i32,false,.root 0⟩
    ⟨2,false⟩ ⟨3,false⟩ ⟨0,true⟩ ⟨1,true⟩ ⟨i32,-7⟩ ⟨i32,99⟩ readonlyOK rfl view
    (by decide +kernel) (by decide +kernel) rfl rfl
example : Represents roAssigned.1 target (List.replicate 2 (-1)) 2 (fun _ => 0) :=
  assign_represents readonly roAssigned.1 target source (buffer 0 4) (buffer 1 2) _ _ _ ⟨1,.integer i32,false,.root 0⟩
    ⟨2,false⟩ ⟨3,false⟩ ⟨0,true⟩ ⟨1,true⟩ ⟨i32,-7⟩ ⟨i32,99⟩ (object target) readonlyOK rfl view
    (by decide +kernel) (by decide +kernel) rfl (by decide) (by decide) (by decide +kernel)
#guard roAssigned.1.scalars.memory.map (·.value) == ([2,2,2,2,3,3] : List Int)
#guard roAssigned.1.scalars.bindings == readonly.scalars.bindings
#guard (match Proofs.UnionFindCandidateInstance.UnionFind_size.callFuel 128 roAssigned.1
    (arguments target ++ [.value (.literal i32 0)]) with
  | .finished (_, .scalar value) => value == 1 | _ => false)

theorem roSeparated (address : Nat) (left : 0 ≠ address) (right : 1 ≠ address) :
    Proofs.CppClassAssignValues.Separate readonly (object target).scalarSlots address := by
  have a := Proofs.CppClassAssignValues.separate_single readonly 1 i32 ⟨0,true⟩ ⟨i32,-7⟩ address (by decide +kernel) left
  have b := Proofs.CppClassAssignValues.separate_single readonly 2 i32 ⟨1,true⟩ ⟨i32,99⟩ address (by decide +kernel) right
  intro slot member index binding lookup found
  have alternatives : slot = 1 ∨ slot = 2 := by simpa [object,target] using member
  rcases alternatives with rfl | rfl
  · exact a 1 (by simp) index binding lookup found
  · exact b 2 (by simp) index binding lookup found
example : SourceView roAssigned.1 source (List.replicate 2 (-1)) 2 (fun _ => 0)
    (buffer 1 2) ⟨1,.integer i32,false,.root 0⟩ ⟨2,false⟩ ⟨3,false⟩ :=
  preserves_view readonly roAssigned.1 target source source (buffer 0 4) (buffer 1 2) _ _ _
    ⟨1,.integer i32,false,.root 0⟩ ⟨2,false⟩ ⟨3,false⟩ (object target) readonlyOK view rfl
    (by decide) (roSeparated 2 (by decide) (by decide)) (roSeparated 3 (by decide) (by decide)) (by decide +kernel)
example := SourceView.of_inv state source _ _ _ (buffer 1 2) ⟨2,true⟩ ⟨3,true⟩ sourceInv
#guard roAssigned.1.frame.state.storage.lookup 1 == readonly.frame.state.storage.lookup 1
#guard roAssigned.1.scalarCell source.countSlot i32 == readonly.scalarCell source.countSlot i32
#guard roAssigned.1.scalarCell source.nSlot i32 == readonly.scalarCell source.nSlot i32
def blocked : NState := {readonly with frame := {readonly.frame with bindings := readonly.frame.bindings.set 0 ⟨0,.integer i32,false,.root 0⟩}}
#guard (assignClass blocked (object target) (object source) Proofs.UfClassCopyBridge.profile).isNone
'''

WORK_CHECKS = r'''
open Proofs.UfAssignmentWork Proofs.UfReceiverTrace
example : roAssigned.1.work ≤ readonly.work+4+2+6 :=
  assign_work readonly roAssigned.1 target source (buffer 0 4) (buffer 1 2) _ _ _
    ⟨1,.integer i32,false,.root 0⟩ ⟨2,false⟩ ⟨3,false⟩ (object target) readonlyOK view (by decide +kernel)
def ops : List Operation := [.root 0,.same 0 1,.size 0,.unite 0 1,.numGroups]
theorem allowed : ∀ op ∈ ops, op.allowed 2 := by
  intro op member
  simp [ops] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [Operation.allowed]
example := assignment_then_calls readonly roAssigned.1 target source (buffer 0 4) (buffer 1 2)
    (List.replicate 2 (-1)) 2 (fun _ => 0) (fun _ => 0) ⟨1,.integer i32,false,.root 0⟩
    ⟨2,false⟩ ⟨3,false⟩ ⟨0,true⟩ ⟨1,true⟩ ⟨i32,-7⟩ ⟨i32,99⟩ (object target) readonlyOK rfl view
    (by decide +kernel) (by decide +kernel) rfl (by decide) (by decide) (by decide +kernel)
    ops (Proofs.UfHistoricalRank.initial_history 2) allowed
#guard (match runCalls (List.replicate 5 128) ops roAssigned.1 target with
  | .finished (out,answers) => answers == ([0,0,1,0,1] : List Int) &&
      out.scalarCell source.countSlot i32 == readonly.scalarCell source.countSlot i32 &&
      out.scalarCell source.nSlot i32 == readonly.scalarCell source.nSlot i32
  | _ => false)
'''

class UnionFindAssignmentTests(unittest.TestCase):
    def test_native_reassignment_after_move(self):
        header = ROOT/'experiments/verification/data_structure/union_find.hpp'
        with tempfile.TemporaryDirectory(prefix='uf-assignment-native-') as directory:
            source = Path(directory)/'check.cpp'
            binary = Path(directory)/'check'
            source.write_text('#include "'+str(header)+'"\n'+r'''
#include <cassert>
#include <utility>
int main(){
  for(int n : {0,1,2,17}){
    cp::UnionFind source(n),target(4),other(3);
    if(n>1)source.unite(0,n-1);
    int groups=source.num_groups();
    cp::UnionFind saved(std::move(target));
    cp::UnionFind* returned=&(target=source);
    assert(returned==&target && target.num_groups()==groups);
    assert(saved.num_groups()==4 && other.num_groups()==3 && source.num_groups()==groups);
    if(n>0)assert(target.size(0)==source.size(0));
    returned=&(target=target);
    assert(returned==&target && target.num_groups()==groups);
  }
}
''')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',
                            '-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_actual_state_restoration_and_preservation(self):
        with tempfile.TemporaryDirectory(prefix='uf-assignment-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text(CHECKS+READONLY_CHECKS+WORK_CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
