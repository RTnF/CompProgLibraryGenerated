"""Work bounds including argument setup for actual UF calls and finite traces."""
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
from test_uf_object_trace import CHECKS as TRACE_CHECKS, MEANING_CHECKS
from offline import disable_network

CHECKS = r'''
namespace UfObjectTraceWorkExamples
open Proofs.UfObjectTraceWork Proofs.UfObjectTrace
open UfMoveCallExamples UfObjectStateExamples UfObjectTraceExamples
example := execute_work moved.1 moved.2 start plan planReady
example (count : Nat) := execute_work moved.1 moved.2 start (List.replicate count (.root 3)) (by
  intro op member
  have same : op = Operation.root 3 := List.eq_of_mem_replicate member
  subst op
  change 3 < 4
  decide +kernel)
example (rank : Nat → Nat) (math : Proofs.UfClassInvariant.Valid UfObjectApartExamples.apartParents 2 rank) :=
  execute_work UfObjectApartExamples.apart moved.2 (UfObjectTraceMeaningExamples.apartStart rank math) plan (by exact planReady)
end UfObjectTraceWorkExamples
'''

STEP_CHECKS = r'''
namespace UfObjectStepWorkExamples
open Proofs.UfObjectTraceWork Proofs.UfObjectTrace Proofs.UfObjectState
open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram
open UfMoveCallExamples UfObjectStateExamples

example (s : Context) (object : ObjectRef) (state : State s object) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (_next : State out object),
      invoke fuel s object .groups = .finished (out,result) ∧ result = .scalar state.receiver.counter.value ∧
      work out ≤ work s + 10 := by
  obtain ⟨fuel,out,result,next,first⟩ := step s object state .groups trivial
  have cost := step_work s out object state next .groups fuel result first
  refine ⟨fuel,out,result,next,first.actual,first.meaning.1,?_⟩
  simpa only [arity,bodyWork,Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using cost

example : ∃ (fuel : Nat) (out : Context) (result : Ret) (_next : State out moved.2),
    invoke fuel moved.1 moved.2 (.root 3) = .finished (out,result) ∧ work out ≤ work moved.1 + 272 := by
  obtain ⟨fuel,out,result,next,first⟩ := step moved.1 moved.2 start (.root 3) (by change 3 < 4; decide +kernel)
  have cost := step_work moved.1 out moved.2 start next (.root 3) fuel result first
  refine ⟨fuel,out,result,next,first.actual,?_⟩
  change work out ≤ work moved.1 + (7+2*1) + (91*2+81) at cost
  omega
end UfObjectStepWorkExamples
'''

class UfObjectTraceWorkTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-trace-work-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectTraceWork\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                APART_DEFINITIONS + STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_finite_mixed_traces_and_arbitrary_repetitions_include_setup_work(self):
        self.check_lean(CHECKS)

    def test_getter_and_root_have_concrete_inclusive_work_bounds(self):
        self.check_lean(STEP_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
