"""Original UF unite/counter normal Context calls and mutation/resource contracts."""
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

UNITE_CHECKS = r'''

namespace UfUniteCallExamples
open Proofs.CppMoveContext Proofs.CppMoveCallBindings Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.UfCompactUniteCall Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame
open UfMoveCallExamples
 def uniteArgs : List NArgument := [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3),.value (.literal ty 1)]
 def prepared := (prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters uniteArgs).getD moved.1
 theorem preparedRun : prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters uniteArgs = some prepared := by
   have live : (prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters uniteArgs).isSome = true := by decide +kernel
   have nonempty : prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters uniteArgs ≠ none := by intro missing; simp [missing] at live
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
 example := unite_call moved.1 prepared initial uniteArgs vc parents ranks 1 parentValid 3 1 (by decide) (by decide)
   P 2 (by decide +kernel) buffer rfl ⟨rfl,rfl⟩ preparedRun compacted qs fw (by decide +kernel) (Nat.le_refl _)
   (by decide +kernel) (by decide +kernel) contexts covered
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_unite 128 moved.1 ty uniteArgs with
   | .finished (out,result) => result == .scalar 0 &&
       (out.objects.heap.allocation 0).map (fun a => a.buffer.items) == some [-4,0,0,0] &&
       Proofs.CppMoveHeaders.read out.objects.heap ty.valid 0 == some 0 &&
       (Proofs.CppMoveHeaders.read out.objects.heap ty.valid 1).isNone
   | _ => false)
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_unite 0 moved.1 ty uniteArgs with
   | .exhausted => true | _ => false)

 def apart : Context := {moved.1 with
   objects := {moved.1.objects with heap := {moved.1.objects.heap with allocations :=
     [some ⟨⟨0,[-2,0,-2,2],5,limit,0⟩,fun _ => 7⟩,none]}},
   scalars := {moved.1.scalars with memory := moved.1.scalars.memory.set 2 ⟨ty,2⟩}}
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_unite 128 apart ty uniteArgs with
   | .finished (out,result) => result == .scalar 2 &&
       (out.objects.heap.allocation 0).map (fun a => a.buffer.items) == some [2,0,-4,2] &&
       out.scalars.memory.map (·.value) == [1,4,1,4] &&
       Proofs.CppMoveHeaders.read out.objects.heap ty.valid 0 == some 2 &&
       (Proofs.CppMoveHeaders.read out.objects.heap ty.valid 1).isNone
   | _ => false)
end UfUniteCallExamples
'''

COUNTER_CHECKS = r'''

namespace UfCounterCallExamples
open Proofs.CppMoveContext Proofs.CppMoveCallBindings Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.UfCompactCounterCall Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame
open UfMoveCallExamples
 def counterArgs : List NArgument := [.vectorReference 3,.scalarReference 4,.value (.variable ty 5)]
 def prepared := (prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters counterArgs).getD moved.1
 theorem preparedRun : prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters counterArgs = some prepared := by
   have live : (prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters counterArgs).isSome = true := by decide +kernel
   have nonempty : prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_num_groups.parameters counterArgs ≠ none := by intro missing; simp [missing] at live
   exact (Option.getD_of_ne_none nonempty moved.1).symm
 def initial := (compact (project prepared ty)).getD (project prepared ty)
 theorem compacted : compact (project prepared ty) = some initial := by
   have live : (compact (project prepared ty)).isSome = true := by decide +kernel
   have nonempty : compact (project prepared ty) ≠ none := by intro missing; simp [missing] at live
   exact (Option.getD_of_ne_none nonempty (project prepared ty)).symm
 def P := prepared.scalars.memory.take 11
 #guard P.length == 11
 #guard initial.frame.bindings.length == 1 && initial.scalars.memory.length == 12
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
     (Proofs.UfFieldsCounter.fields P 2 4).mem
     (Proofs.UfFieldsCounter.fields P 2 4).bs
     (sl1 (Proofs.UfFieldsCounter.fields P 2 4).bs.length) :=
   ⟨by decide +kernel,by decide +kernel,by decide +kernel,rfl,rfl⟩
 example := counter_call moved.1 prepared initial counterArgs vc parents P 2 4 1 (by decide +kernel) (by decide +kernel)
   buffer rfl preparedRun compacted qs fw (by decide +kernel) (Nat.le_refl _)
   (by decide +kernel) (by decide +kernel) contexts covered
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups 128 moved.1 ty counterArgs with
   | .finished (out,result) => result == .scalar 1 &&
       (out.objects.heap.allocation 0).map (fun a => a.buffer.items) == some [-4,0,0,2] &&
       Proofs.CppMoveHeaders.read out.objects.heap ty.valid 0 == some 2 &&
       (Proofs.CppMoveHeaders.read out.objects.heap ty.valid 1).isNone
   | _ => false)
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups 0 moved.1 ty counterArgs with
   | .exhausted => true | _ => false)

 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups 16 moved.1 ty
     [.vectorReference 0,.scalarReference 1,.value (.variable ty 2)] with
   | .finished (out,result) => result == .scalar 1 && out.scalars.memory.map (·.value) == [1,4,1,4] &&
       out.objects.heap.header 0 == some ⟨none,0,true,limit⟩
   | _ => false)
 def raw (count : Int) : Context := {moved.1 with scalars :=
   {moved.1.scalars with memory := moved.1.scalars.memory.set 2 ⟨ty,count⟩}}
 #guard ([-2147483648,2147483647] : List Int).all (fun count =>
   match callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups 16 (raw count) ty counterArgs with
   | .finished (out,result) => result == .scalar count &&
       out.scalars.memory.map (·.value) == [1,4,count,4]
   | _ => false)
 def empty : Context := ⟨⟨⟨[some ⟨none,0,true,limit⟩],[],[],0,0,0⟩,[⟨0,true⟩]⟩,
   ⟨[⟨ty,0⟩,⟨ty,0⟩],[⟨0,true⟩,⟨1,true⟩],0,0,0⟩,[.vector 0,.scalar 0,.scalar 1],0,0⟩
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups 16 empty ty
     [.vectorReference 0,.scalarReference 1,.value (.variable ty 2)] with
   | .finished (out,result) => result == .scalar 0 && out.objects.heap.allocations.isEmpty
   | _ => false)

 example (rank : Nat → Nat) (validClass : Proofs.UfClassInvariant.Valid parents 1 rank) :
     ∃ fuel out, callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel moved.1 ty counterArgs =
       .finished (out,.scalar ((Proofs.UfClassInvariant.roots parents).length : Int)) := by
   obtain ⟨fuel,out,ran,_⟩ := counter_call moved.1 prepared initial counterArgs vc parents P 2 4 1
     (by decide +kernel) (by decide +kernel) buffer rfl preparedRun compacted qs fw
     (by decide +kernel) (Nat.le_refl _) (by decide +kernel) (by decide +kernel) contexts covered
   rw [validClass.count] at ran
   exact ⟨fuel,out,ran⟩
end UfCounterCallExamples
'''

class UfCompactMutationCountTests(unittest.TestCase):
    def check_lean(self,checks):
        with tempfile.TemporaryDirectory(prefix='uf-compact-mutation-count-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfCompactUniteCall\nimport Proofs.UfCompactCounterCall\n'
                'import Proofs.UfClassCopyBridge\nimport Proofs.UfFieldsSame\n'
                'import Proofs.UfFieldsSize\nimport Proofs.UfFieldsUnite\nimport Proofs.UfFieldsCounter\n'+UF_CHECKS+checks)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_unite_normal_call_compression_merge_counter_and_grants(self):
        self.check_lean(UNITE_CHECKS)

    def test_counter_normal_call_empty_moved_from_and_full_i32(self):
        self.check_lean(COUNTER_CHECKS)

if __name__=='__main__':
    disable_network()
    unittest.main()
