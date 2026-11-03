"""Source-derived same/size Context call termination, semantics and resource bounds."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_call_restore import UF_CHECKS
from offline import disable_network

SAME_CHECKS = r'''

namespace UfSameCallExamples
open Proofs.CppMoveContext Proofs.CppMoveCallBindings Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.UfCompactSameCall Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame
open UfMoveCallExamples
 def sameArgs : List NArgument := [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3),.value (.literal ty 1)]
 def prepared := (prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_same.parameters sameArgs).getD moved.1
 theorem preparedRun : prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_same.parameters sameArgs = some prepared := by
   have live : (prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_same.parameters sameArgs).isSome = true := by decide +kernel
   have nonempty : prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_same.parameters sameArgs ≠ none := by intro missing; simp [missing] at live
   exact (Option.getD_of_ne_none nonempty moved.1).symm
 def initial := (compact (project prepared ty)).getD (project prepared ty)
 theorem compacted : compact (project prepared ty) = some initial := by
   have live : (compact (project prepared ty)).isSome = true := by decide +kernel
   have nonempty : compact (project prepared ty) ≠ none := by intro missing; simp [missing] at live
   exact (Option.getD_of_ne_none nonempty (project prepared ty)).symm
 def P := prepared.scalars.memory.take 11
 #guard P.length == 11
 #guard initial.frame.bindings.length == 1 && initial.scalars.memory.length == 14
 def vc : VCtx := ⟨ty,true,true,0,0,buffer,parents,by decide,fun _ => rfl,by decide,
   initial.frame.state.liveSpace,initial.frame.state.storage.work,initial.scope,initial.frame.state.storage.objects.length⟩
 theorem strict : ∀ owner sc, initial.frame.state.forest.context owner = some sc → sc < vc.sc := by
   intro owner sc found
   have state : initial.frame.state = (project moved.1 ty).frame.state := by decide +kernel
   rw [state] at found
   have bound := contexts owner sc found
   change sc < 2
   change sc ≤ 1 at bound
   omega
 theorem fw : FW vc parents buffer 0 initial.frame :=
   ⟨by decide +kernel,by decide +kernel,rfl,by simp [vc],strict,rfl,by decide +kernel,
     by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
     by decide +kernel,rfl,rfl,by decide +kernel⟩
 theorem qs : QS initial [] initial.scalars.baseMemory initial.scope
     (Proofs.UfFieldsSame.fields P ⟨2,true⟩ parents.length 3 1).mem
     (Proofs.UfFieldsSame.fields P ⟨2,true⟩ parents.length 3 1).bs
     (sl1 (Proofs.UfFieldsSame.fields P ⟨2,true⟩ parents.length 3 1).bs.length) :=
   ⟨by decide +kernel,by decide +kernel,by decide +kernel,rfl,rfl⟩
 example := same_call moved.1 prepared initial sameArgs vc parents ranks parentForest (by decide) 3 1 (by decide) (by decide)
   P ⟨2,true⟩ buffer rfl ⟨rfl,rfl⟩ preparedRun compacted qs fw (by decide +kernel) (Nat.le_refl _)
   (by decide +kernel) (by decide +kernel) contexts covered
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_same 128 moved.1 ty sameArgs with
   | .finished (out,result) => result == .scalar 1 &&
       (out.objects.heap.allocation 0).map (fun a => a.buffer.items) == some [-4,0,0,0] &&
       Proofs.CppMoveHeaders.read out.objects.heap ty.valid 0 == some 0 &&
       (Proofs.CppMoveHeaders.read out.objects.heap ty.valid 1).isNone
   | _ => false)
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_same 0 moved.1 ty sameArgs with
   | .exhausted => true | _ => false)

 def apart : Context := {moved.1 with
   objects := {moved.1.objects with heap := {moved.1.objects.heap with allocations :=
     [some ⟨⟨0,[-2,0,-2,2],5,limit,0⟩,fun _ => 7⟩,none]}},
   scalars := {moved.1.scalars with memory := moved.1.scalars.memory.set 2 ⟨ty,2⟩}}
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_same 128 apart ty sameArgs with
   | .finished (out,result) => result == .scalar 0 &&
       (out.objects.heap.allocation 0).map (fun a => a.buffer.items) == some [-2,0,-2,2] &&
       out.scalars.memory.map (·.value) == [1,4,2,4] &&
       Proofs.CppMoveHeaders.read out.objects.heap ty.valid 0 == some 2 &&
       (Proofs.CppMoveHeaders.read out.objects.heap ty.valid 1).isNone
   | _ => false)

 example := Proofs.CppMoveCallBindingsReady.compact_ready (project prepared ty) (by
   intro index member
   change index ∈ [4] at member
   have eq : index = 4 := by simpa using member
   subst index
   decide +kernel)
end UfSameCallExamples
'''

SIZE_CHECKS = r'''

namespace UfSizeCallExamples
open Proofs.CppMoveContext Proofs.CppMoveCallBindings Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.UfCompactSizeCall Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame
open UfMoveCallExamples
 def sizeArgs : List NArgument := [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3)]
 def prepared := (prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_size.parameters sizeArgs).getD moved.1
 theorem preparedRun : prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_size.parameters sizeArgs = some prepared := by
   have live : (prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_size.parameters sizeArgs).isSome = true := by decide +kernel
   have nonempty : prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_size.parameters sizeArgs ≠ none := by intro missing; simp [missing] at live
   exact (Option.getD_of_ne_none nonempty moved.1).symm
 def initial := (compact (project prepared ty)).getD (project prepared ty)
 theorem compacted : compact (project prepared ty) = some initial := by
   have live : (compact (project prepared ty)).isSome = true := by decide +kernel
   have nonempty : compact (project prepared ty) ≠ none := by intro missing; simp [missing] at live
   exact (Option.getD_of_ne_none nonempty (project prepared ty)).symm
 def P := prepared.scalars.memory.take 11
 #guard P.length == 11
 #guard initial.frame.bindings.length == 1 && initial.scalars.memory.length == 13
 def vc : VCtx := ⟨ty,true,true,0,0,buffer,parents,by decide,fun _ => rfl,by decide,
   initial.frame.state.liveSpace,initial.frame.state.storage.work,initial.scope,initial.frame.state.storage.objects.length⟩
 theorem strict : ∀ owner sc, initial.frame.state.forest.context owner = some sc → sc < vc.sc := by
   intro owner sc found
   have state : initial.frame.state = (project moved.1 ty).frame.state := by decide +kernel
   rw [state] at found
   have bound := contexts owner sc found
   change sc < 2
   change sc ≤ 1 at bound
   omega
 theorem fw : FW vc parents buffer 0 initial.frame :=
   ⟨by decide +kernel,by decide +kernel,rfl,by simp [vc],strict,rfl,by decide +kernel,
     by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
     by decide +kernel,rfl,rfl,by decide +kernel⟩
 theorem qs : QS initial [] initial.scalars.baseMemory initial.scope
     (Proofs.UfFieldsRoot.fields P ⟨2,true⟩ parents.length 3).mem
     (Proofs.UfFieldsRoot.fields P ⟨2,true⟩ parents.length 3).bs
     (sl1 (Proofs.UfFieldsRoot.fields P ⟨2,true⟩ parents.length 3).bs.length) :=
   ⟨by decide +kernel,by decide +kernel,by decide +kernel,rfl,rfl⟩

 open Proofs.UfClassInvariant Proofs.UfRootCall
 theorem parentMembers : members parents 0 = List.range 4 := by
   classical
   unfold members
   change (List.range 4).filter (fun i => decide (Reach parents i 0)) = List.range 4
   apply List.filter_eq_self.mpr
   intro i member
   have inside : i<4 := List.mem_range.mp member
   have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
   simp only [decide_eq_true_eq]
   rcases choices with rfl | rfl | rfl | rfl
   · exact Reach.refl 0
   · exact Reach.step 1 0 0 rfl (Reach.refl 0)
   · exact Reach.step 2 0 0 rfl (Reach.refl 0)
   · exact Reach.step 3 2 0 rfl (Reach.step 2 0 0 rfl (Reach.refl 0))
 theorem parentRoots : roots parents = [0] := by
   classical
   simp [roots,parents,List.range_succ]
 theorem parentValid : Valid parents 1 ranks := by
   refine ⟨parentForest,by decide,?_,?_⟩
   · intro r w found negative
     have inside : r<4 := (List.getElem?_eq_some_iff.mp found).1
     have choices : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
     rcases choices with rfl | rfl | rfl | rfl
     · have value : w = -4 := by simpa [parents] using found.symm
       rw [value,parentMembers]
       rfl
     · simp [parents] at found
       subst w
       omega
     · simp [parents] at found
       subst w
       omega
     · simp [parents] at found
       subst w
       omega
   · rw [parentRoots]
     rfl
 theorem parentWeights : Proofs.UfFieldsSize.Weights parents := parentValid.weights
 example := size_call moved.1 prepared initial sizeArgs vc parents ranks parentForest (by decide) parentWeights 3 (by decide)
   P ⟨2,true⟩ buffer rfl ⟨rfl,rfl⟩ preparedRun compacted qs fw (by decide +kernel) (Nat.le_refl _)
   (by decide +kernel) (by decide +kernel) contexts covered
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_size 128 moved.1 ty sizeArgs with
   | .finished (out,result) => result == .scalar 4 &&
       (out.objects.heap.allocation 0).map (fun a => a.buffer.items) == some [-4,0,0,0] &&
       Proofs.CppMoveHeaders.read out.objects.heap ty.valid 0 == some 0 &&
       (Proofs.CppMoveHeaders.read out.objects.heap ty.valid 1).isNone
   | _ => false)
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_size 0 moved.1 ty sizeArgs with
   | .exhausted => true | _ => false)

 example : ∃ fuel out root final,
     callFuel Proofs.UnionFindCandidateInstance.UnionFind_size fuel moved.1 ty sizeArgs =
       .finished (out,.scalar ((component parents 3).length : Int)) ∧
     Proofs.UfCompression.Compressed parents final 3 root ∧ Valid final 1 ranks := by
   obtain ⟨fuel,out,root,weight,final,ran,_,_,compressed,_,_,interpretation,_⟩ :=
     size_call moved.1 prepared initial sizeArgs vc parents ranks parentForest (by decide) parentWeights 3 (by decide)
       P ⟨2,true⟩ buffer rfl ⟨rfl,rfl⟩ preparedRun compacted qs fw (by decide +kernel) (Nat.le_refl _)
       (by decide +kernel) (by decide +kernel) contexts covered
   obtain ⟨value,newValid⟩ := interpretation 1 parentValid
   rw [value] at ran
   exact ⟨fuel,out,root,final,ran,compressed,newValid⟩
 def intMin : Context := {moved.1 with
   objects := {moved.1.objects with heap := {moved.1.objects.heap with allocations :=
     [some ⟨⟨0,[-2147483648],5,limit,0⟩,fun _ => 7⟩,none]}},
   scalars := {moved.1.scalars with memory := moved.1.scalars.memory.set 3 ⟨ty,1⟩}}
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_size 128 intMin ty
     [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 0)] with
   | .fault => true | _ => false)
end UfSizeCallExamples
'''

class UfCompactQueryTests(unittest.TestCase):
    def check_lean(self,checks):
        with tempfile.TemporaryDirectory(prefix='uf-compact-query-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppMoveCallBindingsReady\nimport Proofs.UfCompactSameCall\n'
                'import Proofs.UfCompactSizeCall\nimport Proofs.UfClassCopyBridge\n'
                'import Proofs.UfFieldsSame\nimport Proofs.UfFieldsSize\n'
                'import Proofs.UfFieldsUnite\nimport Proofs.UfFieldsCounter\n'+UF_CHECKS+checks)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_same_normal_call_connected_disconnected_and_immutable_grants(self):
        self.check_lean(SAME_CHECKS)

    def test_size_normal_call_component_cardinality_and_invalid_weight(self):
        self.check_lean(SIZE_CHECKS)

if __name__=='__main__':
    disable_network()
    unittest.main()
