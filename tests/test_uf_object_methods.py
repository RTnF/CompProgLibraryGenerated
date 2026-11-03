"""Source UF same/size/unite ObjectRef calls, wrappers and precise counter mutation."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'verifier'), str(ROOT / 'tools'), str(ROOT / 'tests')]
from context_method_ir import emit_context_methods
from test_scalar_ir import lean_environment
from test_cpp_move_object_receiver import CHECKS as OBJECT_CHECKS
from test_cpp_move_receiver_layout import UF_CHECKS, RECEIVER_CHECKS
from test_uf_receiver_layout import CHECKS as FRAME_CHECKS
from offline import disable_network

CHECKS = r'''

namespace UfObjectFutureExamples
open Proofs.CppMoveContext Proofs.CppMoveFrame Proofs.CppMoveReceiverResolve
open Proofs.UfClassInvariant Proofs.UfRootCall
open UfMoveCallExamples ObjectReceiverExamples UfReceiverLayoutExamples
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

example := Proofs.UfObjectMethods.same_call moved.1 moved.2 target ⟨0,parents,5,limit,0⟩ rfl rfl
  ranks parentForest (by decide +kernel) 3 (by decide +kernel) 1 (by decide +kernel)
  (.binary ty .add (.literal ty 2) (.literal ty 1)) rfl rfl (by decide +kernel)
  (.literal ty 1) rfl rfl (by decide +kernel)
  (by decide +kernel) unique covered allocationsValid rfl (by decide +kernel) contexts
example := Proofs.UfObjectMethods.size_call moved.1 moved.2 target ⟨0,parents,5,limit,0⟩ rfl rfl
  ranks parentForest (by decide +kernel) parentValid.weights 3 (by decide +kernel)
  (.literal ty 3) rfl rfl (by decide +kernel)
  (by decide +kernel) unique covered allocationsValid rfl (by decide +kernel) contexts
example := Proofs.UfObjectMethods.unite_call moved.1 moved.2 target ⟨0,parents,5,limit,0⟩ rfl rfl
  ranks parentValid 3 (by decide +kernel) 1 (by decide +kernel)
  (.literal ty 3) rfl rfl (by decide +kernel) (.literal ty 1) rfl rfl (by decide +kernel)
  (by decide +kernel) unique covered allocationsValid rfl (by decide +kernel) contexts
end UfObjectFutureExamples

namespace UfObjectGeneratedMethodExamples
open Proofs.CppMoveContext Proofs.CppMoveFrame Proofs.CppVector
open UfMoveCallExamples ObjectReceiverExamples UfReceiverLayoutExamples UfObjectFutureExamples

example : ∃ (fuel : Nat) (out : Context) (r1 r2 : Nat),
    ObjectReceiverMethods.«UnionFind_same_callFuel» fuel moved.1 moved.2
      [.value (.literal ty 3),.value (.literal ty 1)] = .finished (out,.scalar (if r1=r2 then 1 else 0)) := by
  obtain ⟨prepared,initial,vc,fuel,out,r1,r2,middle,final,run,compacted,fw,actual,rest⟩ :=
    Proofs.UfObjectMethods.same_call moved.1 moved.2 target ⟨0,parents,5,limit,0⟩ rfl rfl
      ranks parentForest (by decide +kernel) 3 (by decide +kernel) 1 (by decide +kernel)
      (.literal ty 3) rfl rfl (by decide +kernel) (.literal ty 1) rfl rfl (by decide +kernel)
      (by decide +kernel) unique covered allocationsValid rfl (by decide +kernel) contexts
  have mapped := ObjectReceiverMethods.«UnionFind_same_arguments_of_fields» moved.2
    [.value (.literal ty 3),.value (.literal ty 1)] target.counter.slot target.size.slot target.fields rfl
  refine ⟨fuel,out,r1,r2,?_⟩
  rw [ObjectReceiverMethods.«UnionFind_same_call_of_arguments» fuel moved.1 moved.2 _ _ mapped]
  exact actual

example : ∃ (fuel : Nat) (out : Context) (weight : Int),
    ObjectReceiverMethods.«UnionFind_size_callFuel» fuel moved.1 moved.2
      [.value (.literal ty 3)] = .finished (out,.scalar (-weight)) ∧ weight < 0 := by
  obtain ⟨prepared,initial,vc,fuel,out,r,weight,final,run,compacted,fw,actual,atRoot,negative,rest⟩ :=
    Proofs.UfObjectMethods.size_call moved.1 moved.2 target ⟨0,parents,5,limit,0⟩ rfl rfl
      ranks parentForest (by decide +kernel) parentValid.weights 3 (by decide +kernel)
      (.literal ty 3) rfl rfl (by decide +kernel)
      (by decide +kernel) unique covered allocationsValid rfl (by decide +kernel) contexts
  have mapped := ObjectReceiverMethods.«UnionFind_size_arguments_of_fields» moved.2
    [.value (.literal ty 3)] target.counter.slot target.size.slot target.fields rfl
  refine ⟨fuel,out,weight,?_,negative⟩
  rw [ObjectReceiverMethods.«UnionFind_size_call_of_arguments» fuel moved.1 moved.2 _ _ mapped]
  exact actual

example : ∃ (fuel : Nat) (out : Context) (result : Int),
    ObjectReceiverMethods.«UnionFind_unite_callFuel» fuel moved.1 moved.2
      [.value (.literal ty 3),.value (.literal ty 1)] = .finished (out,.scalar result) := by
  obtain ⟨prepared,initial,vc,fuel,out,r1,r2,middle,two,final,run,compacted,fw,actual,rest⟩ :=
    Proofs.UfObjectMethods.unite_call moved.1 moved.2 target ⟨0,parents,5,limit,0⟩ rfl rfl
      ranks parentValid 3 (by decide +kernel) 1 (by decide +kernel)
      (.literal ty 3) rfl rfl (by decide +kernel) (.literal ty 1) rfl rfl (by decide +kernel)
      (by decide +kernel) unique covered allocationsValid rfl (by decide +kernel) contexts
  have mapped := ObjectReceiverMethods.«UnionFind_unite_arguments_of_fields» moved.2
    [.value (.literal ty 3),.value (.literal ty 1)] target.counter.slot target.size.slot target.fields rfl
  refine ⟨fuel,out,(Proofs.UfUniteCall.uniteX two r1 r2 : Int),?_⟩
  rw [ObjectReceiverMethods.«UnionFind_unite_call_of_arguments» fuel moved.1 moved.2 _ _ mapped]
  exact actual
end UfObjectGeneratedMethodExamples
'''

APART_CHECKS = r'''

namespace UfObjectApartExamples
open Proofs.CppMoveContext Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppMoveObjectReceiver
open Proofs.UfClassInvariant Proofs.UfRootCall Proofs.UfMergeInvariant
open UfMoveCallExamples UfReceiverLayoutExamples

def apartParents : List Int := [-2,0,-2,2]
def apart : Context := {moved.1 with
  objects := {moved.1.objects with heap := {moved.1.objects.heap with allocations :=
    [some ⟨⟨0,apartParents,5,limit,0⟩,fun _ => 7⟩,none]}},
  scalars := {moved.1.scalars with memory := moved.1.scalars.memory.set 2 ⟨ty,2⟩}}
def receiver : Receiver apart moved.2 ty :=
  ⟨⟨4,2,2,true,2,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    ⟨5,3,3,true,4,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    rfl,rfl,1,⟨1,true⟩,⟨some 0,0,true,limit⟩,by decide +kernel,by decide +kernel,rfl⟩

theorem apartValid : ∃ rank, Valid apartParents 2 rank := by
  have start := initial_valid 4 (by decide +kernel)
  obtain ⟨first,v1⟩ := start.unite_vec 0 1 ⟨-1,rfl,by decide +kernel⟩ ⟨-1,rfl,by decide +kernel⟩
  change Valid [-2,0,-1,-1] 3 first at v1
  obtain ⟨second,v2⟩ := v1.unite_vec 2 3 ⟨-1,rfl,by decide +kernel⟩ ⟨-1,rfl,by decide +kernel⟩
  change Valid apartParents 2 second at v2
  exact ⟨second,v2⟩

theorem apartCovered : OwnsAll apart.objects.heap := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside apart.objects.heap owner tracked found
  change owner < 2 at inside
  have choices : owner=0 ∨ owner=1 := by omega
  rcases choices with rfl | rfl
  · exact ⟨1,⟨some 0,0,true,limit⟩,rfl,rfl⟩
  · have missing : apart.objects.heap.allocation 1 = none := rfl
    rw [missing] at found
    contradiction

theorem apartAllocations : AllocationsValid apart.objects.heap ty := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside apart.objects.heap owner tracked found
  change owner < 2 at inside
  have choices : owner=0 ∨ owner=1 := by omega
  rcases choices with rfl | rfl
  · have slot : apart.objects.heap.allocation 0 = some ⟨⟨0,apartParents,5,limit,0⟩,fun _ => 7⟩ := rfl
    rw [slot] at found
    cases Option.some.inj found
    decide +kernel
  · have missing : apart.objects.heap.allocation 1 = none := rfl
    rw [missing] at found
    contradiction

theorem apartContexts : ∀ owner sc, (project apart ty).frame.state.forest.context owner = some sc → sc ≤ apart.scope := by
  intro owner sc found
  have forestEq : (project apart ty).frame.state.forest = (project moved.1 ty).frame.state.forest := rfl
  rw [forestEq] at found
  exact contexts owner sc found

theorem notConnected : ¬Proofs.UfFieldsSame.Connected apartParents 3 1 := by
  rintro ⟨z,first,second,root⟩
  have path3 : Reach apartParents 3 2 := Reach.step 3 2 2 rfl (Reach.refl 2)
  have path1 : Reach apartParents 1 0 := Reach.step 1 0 0 rfl (Reach.refl 0)
  have x := Proofs.UfCompression.root_unique first path3 root ⟨-2,rfl,by decide +kernel⟩
  have y := Proofs.UfCompression.root_unique second path1 root ⟨-2,rfl,by decide +kernel⟩
  omega

example : ∃ (fuel : Nat) (out : Context) (result : Int),
    ObjectReceiverMethods.«UnionFind_unite_callFuel» fuel apart moved.2
      [.value (.literal ty 3),.value (.literal ty 1)] = .finished (out,.scalar result) ∧
    out.scalars.memory.map (·.value) = [1,4,1,4] := by
  obtain ⟨rank,validUF⟩ := apartValid
  obtain ⟨prepared,initial,vc,fuel,out,r1,r2,middle,two,final,run,compacted,fw,actual,c1,c2,finalEq,newValid,connected,cost,memory,rest⟩ :=
    Proofs.UfObjectMethods.unite_call apart moved.2 receiver ⟨0,apartParents,5,limit,0⟩ rfl rfl
      rank validUF 3 (by decide +kernel) 1 (by decide +kernel)
      (.literal ty 3) rfl rfl (by decide +kernel) (.literal ty 1) rfl rfl (by decide +kernel)
      (by decide +kernel) unique apartCovered apartAllocations rfl (by decide +kernel) apartContexts
  have different : r1 ≠ r2 := fun equal => notConnected (connected.mp equal)
  have update : Proofs.UfFieldsUnite.updatedMemory apart.scalars.memory 2 2 r1 r2 =
      [⟨ty,1⟩,⟨ty,4⟩,⟨ty,1⟩,⟨ty,4⟩] := by
    simp only [Proofs.UfFieldsUnite.updatedMemory,ite_eq_right different]
    rfl
  change out.scalars.memory = Proofs.UfFieldsUnite.updatedMemory apart.scalars.memory 2 2 r1 r2 at memory
  rw [update] at memory
  have mapped := ObjectReceiverMethods.«UnionFind_unite_arguments_of_fields» moved.2
    [.value (.literal ty 3),.value (.literal ty 1)] receiver.counter.slot receiver.size.slot receiver.fields rfl
  refine ⟨fuel,out,(Proofs.UfUniteCall.uniteX two r1 r2 : Int),?_,?_⟩
  · rw [ObjectReceiverMethods.«UnionFind_unite_call_of_arguments» fuel apart moved.2 _ _ mapped]
    exact actual
  · rw [memory]
    rfl
end UfObjectApartExamples
'''


class UfObjectMethodsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.generated = emit_context_methods(ROOT / 'experiments/verification/data_structure/union_find.hpp',
            'cp::UnionFind', 'ObjectReceiverMethods')

    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-methods-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectMethods\nimport Proofs.UfClassCopyBridge\n' +
                self.generated + UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS + OBJECT_CHECKS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_normal_queries_and_union_from_object_fields_and_generated_wrappers(self):
        self.check_lean(CHECKS)

    def test_apart_components_union_updates_only_counter(self):
        self.check_lean(APART_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
