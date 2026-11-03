"""Interleaved actual UF calls retain both normal states and separation."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from test_uf_object_construction_preserve import (
    EMPTY_CHECKS, PREFIX_CHECKS, UF_CHECKS, RECEIVER_CHECKS, FRAME_CHECKS, OBJECT_CHECKS,
    APART_DEFINITIONS, STATE_CHECKS, TRACE_CHECKS, MEANING_CHECKS, ROOT_CHECKS, HEAP_CHECKS, MOVED_CHECKS, EMPTY_HEADER_CHECKS,
)
from test_uf_object_initial_amortized import EMPTY_CHECKS as INITIAL_EMPTY
from test_uf_object_values import SETUP
from offline import disable_network

CHECKS = r'''namespace UfObjectPairExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.UfObjectState Proofs.UfObjectTrace
open Proofs.UfObjectPair UfObjectValuesExamples

def initial : Pair two oldObject freshObject :=
  ⟨old,fresh,by exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩

example : ∃ (firstFuel secondFuel : Nat) (middle out : Context) (firstResult secondResult : Ret)
    (mid : Pair middle oldObject freshObject) (final : Pair out oldObject freshObject),
    Step two freshObject initial.right (.unite 0 1) firstFuel middle firstResult mid.right ∧
    Step middle oldObject mid.left (.root 3) secondFuel out secondResult final.left ∧
    final.right.receiver.counter.value = 3 ∧ final.right.data.items = mid.right.data.items := by
  obtain ⟨firstFuel,middle,firstResult,mid,joined,leftRank,leftItems,leftCount,leftSize⟩ :=
    step_right two oldObject freshObject initial (.unite 0 1) (by change 0 < 4 ∧ 1 < 4; decide +kernel)
  have nextReady : (Operation.root 3).Valid mid.left.data.items.length := by
    change 3 < mid.left.data.items.length
    rw [leftItems]
    decide +kernel
  obtain ⟨secondFuel,out,secondResult,final,rooted,rightRank,rightItems,rightCount,rightSize⟩ :=
    step_left middle oldObject freshObject mid (.root 3) nextReady
  obtain ⟨r1,r2,path,twice,resultEq,compressed1,compressed2,finalEq,connected,nextCount⟩ := joined.meaning
  have firstRoot : r1 = 0 := (Proofs.UfClassInvariant.initial_reach 4 0 r1 (by decide +kernel)).mp compressed1.reach
  have secondRoot : r2 = 1 := (Proofs.UfClassInvariant.initial_reach 4 1 r2 (by decide +kernel)).mp
    (Proofs.UfCompression.reach_backward compressed1 compressed2.reach)
  have three : mid.right.receiver.counter.value = 3 := by
    simpa [firstRoot,secondRoot,Proofs.UfFieldsUnite.countAfter,initial,fresh,freshReceiver] using nextCount
  exact ⟨firstFuel,secondFuel,middle,out,firstResult,secondResult,mid,final,joined,rooted,rightCount.trans three,rightItems⟩

open Proofs.UfObjectPairTrace
example (actions : List Action) (ready : ∀ action ∈ actions, action.Valid 4 4) :=
  Proofs.UfObjectPairTrace.execute two oldObject freshObject initial actions ready

example := Proofs.UfObjectPairTrace.execute two oldObject freshObject initial
    [.right (.unite 0 1),.left (.root 3),.right (.size 1),.left (.same 0 3),
     .right (.unite 2 3),.right (.same 0 3),.left .groups,.right .groups] (by
  intro action member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Action.Valid,Operation.Valid,initial,old,fresh,UfMoveCallExamples.parents])

end UfObjectPairExamples
'''

EMPTY_CHECKS_PAIR = r'''namespace UfObjectPairEmptyExamples
open Proofs.CppMoveContext Proofs.CppMoveObjectReceiver Proofs.CppNestedProgram Proofs.DoublingNested
open Proofs.UfObjectState Proofs.UfObjectPair Proofs.UfObjectPairTrace
open UfMoveCallExamples UfReceiverLayoutExamples UfObjectFresh0Examples UfEmptyHeaderPreserveExamples

def targetReceiver : Receiver vacant moved.2 i32 :=
  ⟨⟨4,2,2,true,0,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
   ⟨5,3,3,true,0,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
   rfl,rfl,1,⟨1,true⟩,⟨some 0,0,true,limit⟩,by decide +kernel,by decide +kernel,rfl⟩
def targetState : State vacant moved.2 :=
  ⟨targetReceiver,⟨0,[],5,limit,0⟩,rfl,(fun _ => 0),Proofs.UfClassInvariant.initial_valid 0 (by decide +kernel),
   rfl,by decide +kernel,by decide +kernel,unique,freshCovered,freshAllocations,rfl,by decide +kernel,freshContexts⟩
def pair : Pair vacant object moved.2 :=
  ⟨initial,targetState,by exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩

example := execute vacant object moved.2 pair [] (by simp)
example (actions : List Action) (ready : ∀ action ∈ actions, action.Valid 0 0) :=
  execute vacant object moved.2 pair actions ready

example (k : Nat) := execute vacant object moved.2 pair
    (List.replicate k (.left .groups) ++ List.replicate k (.right .groups)) (by
  intro action member
  rcases List.mem_append.mp member with left | right
  · have same := List.eq_of_mem_replicate left
    subst action
    trivial
  · have same := List.eq_of_mem_replicate right
    subst action
    trivial)

example : ¬ (Action.left (.root 0)).Valid 0 0 := by
  change ¬ 0 < 0
  omega

end UfObjectPairEmptyExamples
'''

class UfObjectPairTraceTests(unittest.TestCase):
    def check_lean(self, checks):
        fixtures = (EMPTY_CHECKS + PREFIX_CHECKS + UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
            OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] + APART_DEFINITIONS +
            STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS + MOVED_CHECKS + INITIAL_EMPTY + EMPTY_HEADER_CHECKS + SETUP)
        with tempfile.TemporaryDirectory(prefix='uf-object-pair-trace-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectPairTrace\nimport Proofs.UfObjectConstructionPreserve\nimport Proofs.UfClassCopyBridge\n' + fixtures + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_interleaved_updates_arbitrary_finite_actions_and_mixed_eight_operations(self):
        self.check_lean(CHECKS)

    def test_empty_objects_zero_actions_and_arbitrarily_many_getters(self):
        self.check_lean(EMPTY_CHECKS_PAIR)

if __name__ == '__main__':
    disable_network()
    unittest.main()
