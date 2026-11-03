"""Normal UF state closure for all methods and non-precomputed method sequences."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_call_layout import APART_DEFINITIONS
from test_cpp_move_receiver_layout import UF_CHECKS, RECEIVER_CHECKS
from test_uf_receiver_layout import CHECKS as FRAME_CHECKS
from test_cpp_move_object_receiver import CHECKS as OBJECT_CHECKS
from offline import disable_network

CHECKS = r'''

namespace UfObjectStateExamples
open Proofs.UfObjectState Proofs.UfClassInvariant Proofs.UfRootCall
open Proofs.CppMoveContext Proofs.CppMoveObjectReceiver Proofs.CppNestedProgram
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


def start : State moved.1 moved.2 :=
  ⟨target,⟨0,parents,5,limit,0⟩,rfl,ranks,parentValid,rfl,by decide +kernel,
    by decide +kernel,unique,covered,allocationsValid,rfl,by decide +kernel,contexts⟩

example := root_step moved.1 moved.2 start 3 (by decide +kernel) (.literal ty 3) rfl rfl rfl

example : ∃ (fuel : Nat) (first : Context) (r1 : Nat) (next : State first moved.2)
    (nextFuel : Nat) (second : Context) (r2 : Nat),
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_root fuel moved.1 ty
      (Proofs.UfObjectCall.arguments moved.1 moved.2 start.receiver [(.literal ty 3,3)]) = .finished (first,.scalar (r1 : Int)) ∧
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_root nextFuel first ty
      (Proofs.UfObjectCall.arguments first moved.2 next.receiver [(.literal ty 3,3)]) = .finished (second,.scalar (r2 : Int)) ∧
    Nonempty (State second moved.2) := by
  obtain ⟨prepared,initial,vc,fuel,first,r1,vec1,post,next,rankEq,countEq,sizeEq,itemsEq⟩ :=
    root_step moved.1 moved.2 start 3 (by decide +kernel) (.literal ty 3) rfl rfl rfl
  have actual := post.2.2.2.1
  have compressed := post.2.2.2.2.1
  have inside : 3 < next.data.items.length := by rw [itemsEq,compressed.length]; decide +kernel
  obtain ⟨prepared2,initial2,vc2,fuel2,second,r2,vec2,post2,next2,rankEq2,countEq2,sizeEq2,itemsEq2⟩ :=
    root_step first moved.2 next 3 inside (.literal ty 3) rfl rfl rfl
  exact ⟨fuel,first,r1,next,fuel2,second,r2,actual,post2.2.2.2.1,⟨next2⟩⟩
end UfObjectStateExamples

namespace UfObjectStateMethodExamples
open Proofs.UfObjectState Proofs.UfObjectStateMethods Proofs.CppMoveContext
open UfMoveCallExamples ObjectReceiverExamples UfReceiverLayoutExamples UfObjectStateExamples
example := counter_step moved.1 moved.2 start
example := same_step moved.1 moved.2 start 3 (by decide +kernel) 1 (by decide +kernel)
  (.literal ty 3) rfl rfl rfl (.literal ty 1) rfl rfl rfl
example := size_step moved.1 moved.2 start 3 (by decide +kernel) (.literal ty 3) rfl rfl rfl
example := unite_step moved.1 moved.2 start 3 (by decide +kernel) 1 (by decide +kernel)
  (.literal ty 3) rfl rfl rfl (.literal ty 1) rfl rfl rfl
end UfObjectStateMethodExamples
'''

MIXED_CHECKS = r'''

namespace UfObjectStateMixedExamples
open Proofs.UfObjectState Proofs.UfObjectStateMethods Proofs.CppMoveContext Proofs.CppNestedProgram
open UfMoveCallExamples UfReceiverLayoutExamples UfObjectApartExamples

def start (rank : Nat → Nat) (math : Proofs.UfClassInvariant.Valid apartParents 2 rank) : State apart moved.2 :=
  ⟨receiver,⟨0,apartParents,5,limit,0⟩,rfl,rank,math,rfl,by decide +kernel,
    by decide +kernel,unique,apartCovered,apartAllocations,rfl,by decide +kernel,apartContexts⟩

theorem length_four (s : Context) (state : State s moved.2) (size : state.receiver.size.value = 4) :
    state.data.items.length = 4 := by
  have relation := state.size
  omega

example : ∃ (f1 : Nat) (s1 : Context) (value1 : Int) (state1 : State s1 moved.2)
    (f2 : Nat) (s2 : Context) (value2 : Int) (state2 : State s2 moved.2)
    (f3 : Nat) (s3 : Context) (value3 : Int) (state3 : State s3 moved.2)
    (f4 : Nat) (s4 : Context) (state4 : State s4 moved.2),
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_unite f1 apart ty
      [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3),.value (.literal ty 1)] =
      .finished (s1,.scalar value1) ∧
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_size f2 s1 ty
      (Proofs.UfObjectCall.arguments s1 moved.2 state1.receiver [(.literal ty 3,3)]) = .finished (s2,.scalar value2) ∧
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_same f3 s2 ty
      (Proofs.UfObjectCall.arguments s2 moved.2 state2.receiver [(.literal ty 3,3),(.literal ty 1,1)]) = .finished (s3,.scalar value3) ∧
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups f4 s3 ty
      (Proofs.UfObjectCall.arguments s3 moved.2 state3.receiver []) = .finished (s4,.scalar 1) ∧
    state4.receiver.counter.value = 1 ∧ state4.receiver.size.value = 4 := by
  obtain ⟨rank,math⟩ := apartValid
  let original := start rank math
  obtain ⟨p1,i1,vc1,f1,s1,r1,r2,middle,two,final,post1,state1,countEq1,sizeEq1,itemsEq1⟩ :=
    unite_step apart moved.2 original 3 (by change 3 < 4; decide +kernel) 1 (by change 1 < 4; decide +kernel)
      (.literal ty 3) rfl rfl rfl (.literal ty 1) rfl rfl rfl
  have full1 := post1
  obtain ⟨prep1,compacted1,fw1,actual1,c1,c2,finalEq,newValid,connected,cost1,memory1,rest1⟩ := post1
  have different : r1 ≠ r2 := fun same => notConnected (connected.mp same)
  have one1 : state1.receiver.counter.value = 1 := by
    change state1.receiver.counter.value = Proofs.UfFieldsUnite.countAfter 2 r1 r2 at countEq1
    simpa [Proofs.UfFieldsUnite.countAfter,different] using countEq1
  have four1 : state1.receiver.size.value = 4 := sizeEq1
  have len1 := length_four s1 state1 four1
  have inside1 : 3 < state1.data.items.length := by rw [len1]; decide +kernel
  obtain ⟨p2,i2,vc2,f2,s2,root2,weight2,final2,post2,state2,rankEq2,countEq2,sizeEq2,itemsEq2⟩ :=
    size_step s1 moved.2 state1 3 inside1 (.literal ty 3) rfl rfl rfl
  have actual2 := post2.2.2.2.1
  have one2 : state2.receiver.counter.value = 1 := countEq2.trans one1
  have four2 : state2.receiver.size.value = 4 := sizeEq2.trans four1
  have len2 := length_four s2 state2 four2
  have insideA : 3 < state2.data.items.length := by rw [len2]; decide +kernel
  have insideB : 1 < state2.data.items.length := by rw [len2]; decide +kernel
  obtain ⟨p3,i3,vc3,f3,s3,rootA,rootB,middle3,final3,post3,state3,rankEq3,countEq3,sizeEq3,itemsEq3⟩ :=
    same_step s2 moved.2 state2 3 insideA 1 insideB (.literal ty 3) rfl rfl rfl (.literal ty 1) rfl rfl rfl
  have actual3 := post3.2.2.2.1
  have one3 : state3.receiver.counter.value = 1 := countEq3.trans one2
  have four3 : state3.receiver.size.value = 4 := sizeEq3.trans four2
  obtain ⟨p4,i4,vc4,f4,s4,post4,state4,rankEq4,countEq4,sizeEq4,itemsEq4⟩ := counter_step s3 moved.2 state3
  have actual4 := post4.2.2.2.2.1
  rw [one3] at actual4
  exact ⟨f1,s1,(Proofs.UfUniteCall.uniteX two r1 r2 : Int),state1,f2,s2,-weight2,state2,
    f3,s3,(if rootA=rootB then 1 else 0),state3,f4,s4,state4,
    actual1,actual2,actual3,actual4,countEq4.trans one3,sizeEq4.trans four3⟩
end UfObjectStateMixedExamples
'''


class UfObjectStateTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-state-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectStateMethods\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] + APART_DEFINITIONS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_all_methods_close_state_and_root_runs_twice(self):
        self.check_lean(CHECKS)

    def test_apart_union_size_same_and_getter_from_result_states(self):
        self.check_lean(MIXED_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
