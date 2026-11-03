"""Arbitrary finite UF method histories with actual calls, meanings, and body costs."""
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
from test_uf_object_state import CHECKS as STATE_CHECKS
from offline import disable_network

CHECKS = r'''
namespace UfObjectTraceExamples
open Proofs.UfObjectTrace Proofs.CppMoveContext
open UfMoveCallExamples UfObjectStateExamples

def plan : List Operation := [.groups,.unite 3 1,.size 3,.same 3 1,.root 1,.groups]
theorem planReady : ∀ op ∈ plan, op.Valid start.data.items.length := by
  intro op member
  simp only [plan,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Operation.Valid] <;> decide +kernel
example := execute moved.1 moved.2 start plan planReady

-- The induction theorem also runs a universally quantified number of calls.
example (count : Nat) := execute moved.1 moved.2 start (List.replicate count (.root 3)) (by
  intro op member
  have same : op = Operation.root 3 := List.eq_of_mem_replicate member
  subst op
  change 3 < 4
  decide +kernel)
#guard (expand ⟨3,[]⟩ .groups).isNone
#guard (expand ⟨3,[4,5,6]⟩ .groups).isNone
example : run moved.1 moved.2 [] = .finished (moved.1,[]) := rfl
end UfObjectTraceExamples
'''

MEANING_CHECKS = r'''
namespace UfObjectTraceMeaningExamples
open Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish
open UfMoveCallExamples UfReceiverLayoutExamples UfObjectApartExamples UfObjectTraceExamples

def apartStart (rank : Nat → Nat) (math : Proofs.UfClassInvariant.Valid apartParents 2 rank) : State apart moved.2 :=
  ⟨receiver,⟨0,apartParents,5,limit,0⟩,rfl,rank,math,rfl,by decide +kernel,
    by decide +kernel,unique,apartCovered,apartAllocations,rfl,by decide +kernel,apartContexts⟩

-- This starts from two components, so unite changes the physical counter.
example (rank : Nat → Nat) (math : Proofs.UfClassInvariant.Valid apartParents 2 rank) :=
  execute apart moved.2 (apartStart rank math) plan (by exact planReady)

example (s out : Context) (object : ObjectRef) (state : State s object) (next : State out object) (result : Ret)
    (history : History object s state [.groups] out [result] next) :
    result = .scalar state.receiver.counter.value := by
  cases history with
  | cons ready fuel first rest => exact first.meaning.1

example (s out : Context) (object : ObjectRef) (state : State s object) (next : State out object)
    (a : Nat) (result : Ret) (history : History object s state [.size a] out [result] next) :
    result = .scalar ((Proofs.UfClassInvariant.component state.data.items a).length : Int) := by
  cases history with
  | cons ready fuel first rest => exact first.meaning.1
end UfObjectTraceMeaningExamples
'''

class UfObjectTraceTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-trace-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectTrace\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                APART_DEFINITIONS + STATE_CHECKS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_mixed_plan_arbitrary_repetitions_and_invalid_object_shape(self):
        self.check_lean(CHECKS)

    def test_apart_plan_and_observable_meanings_from_history(self):
        self.check_lean(CHECKS + MEANING_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
