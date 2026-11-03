"""Certificates for supplied successful compact ObjectRef calls and UF fuel scripts."""
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
from test_uf_object_trace import CHECKS as TRACE_CHECKS
from offline import disable_network

CHECKS = r'''
namespace UfObjectActualExamples
open Proofs.UfObjectTraceActual Proofs.UfObjectTrace Proofs.UfObjectTraceWork
open Proofs.UfObjectState Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram
open UfMoveCallExamples UfObjectStateExamples UfObjectTraceExamples

-- More fuel executes the same source methods and retains the actual work/meanings.
example : ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret)
    (next : State out moved.2) (charge : Nat),
    script.map Prod.snd = plan ∧ run moved.1 moved.2 script = .finished (out,results) ∧
    History moved.2 moved.1 start plan out results next ∧
    Charges moved.2 moved.1 start plan out results next charge ∧ work out ≤ work moved.1+charge := by
  obtain ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound⟩ :=
    execute_work moved.1 moved.2 start plan planReady
  let more := script.map (fun entry => (entry.1+17,entry.2))
  have moreMapped : more.map Prod.snd = plan := by
    simpa only [more,List.map_map,Function.comp_def] using mapped
  have moreRun := run_success_mono moved.1 moved.2 script 17 out results ran
  obtain ⟨actualNext,actualCharge,actualHistory,actualCharges,actualBound,actualCount,actualSize⟩ :=
    actual_work moved.1 out moved.2 start more results (by rw [moreMapped]; exact planReady) moreRun
  rw [moreMapped] at actualHistory actualCharges
  exact ⟨more,out,results,actualNext,actualCharge,moreMapped,moreRun,actualHistory,actualCharges,actualBound⟩

-- Every successful supplied fuel script is covered, including the empty script.
example (s : Context) (object : ObjectRef) (state : State s object) :=
  actual_work s s object state [] [] (by simp) rfl
end UfObjectActualExamples
'''

WEAK_CHECKS = r'''
namespace UfObjectActualWeakExamples
open Proofs.CppMoveCallUnique Proofs.CppMoveContext Proofs.CppNestedProgram
open UfMoveCallExamples ObjectReceiverExamples UfReceiverLayoutExamples

-- The source vector is empty after move, while its scalar size remains four.
example : ∃ (fuel : Nat) (out : Context),
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel moved.1 ty
      (Proofs.UfObjectCall.arguments moved.1 source empty []) = .finished (out,.scalar 1) ∧
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups (fuel+37) moved.1 ty
      (Proofs.UfObjectCall.arguments moved.1 source empty []) = .finished (out,.scalar 1) ∧
    (∀ otherFuel otherOut value,
      Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups otherFuel moved.1 ty
        (Proofs.UfObjectCall.arguments moved.1 source empty []) = .finished (otherOut,value) →
      (otherOut,value) = (out,.scalar 1)) := by
  obtain ⟨prepared,initial,vc,data,fuel,out,post⟩ :=
    Proofs.UfObjectCall.counter_call moved.1 source empty (by decide +kernel)
      unique covered allocationsValid rfl (by decide +kernel) contexts
  have actual := post.2.2.2.2.1
  have more := call_success_mono _ fuel 37 moved.1 ty _ _ actual
  refine ⟨fuel,out,actual,more,?_⟩
  intro otherFuel otherOut value another
  exact call_unique _ otherFuel fuel moved.1 ty _ _ _ another actual
end UfObjectActualWeakExamples
'''

ROOT_CHECKS = r'''
namespace UfObjectActualRootExamples
open Proofs.UfObjectTraceActual Proofs.UfObjectTrace Proofs.UfObjectState
open Proofs.CppMoveContext Proofs.CppNestedProgram
open UfMoveCallExamples UfObjectStateExamples
example : ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out moved.2),
    invoke fuel moved.1 moved.2 (.root 3) = .finished (out,result) ∧
    Effect start.data.items next.data.items start.receiver.counter.value next.receiver.counter.value (.root 3) result := by
  obtain ⟨fuel,out,result,next,first⟩ := step moved.1 moved.2 start (.root 3) (by change 3 < 4; decide +kernel)
  have more := invoke_success_mono moved.1 moved.2 (.root 3) fuel 19 _ first.actual
  obtain ⟨actualNext,certificate⟩ := actual_step moved.1 out moved.2 start (.root 3)
    (by change 3 < 4; decide +kernel) (fuel+19) result more
  exact ⟨fuel+19,out,result,actualNext,certificate.actual,certificate.meaning⟩
end UfObjectActualRootExamples
'''

class UfObjectTraceActualTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-trace-actual-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectTraceActual\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                APART_DEFINITIONS + STATE_CHECKS + TRACE_CHECKS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_mixed_script_with_more_fuel_retains_actual_meanings_and_work(self):
        self.check_lean(CHECKS)

    def test_moved_from_getter_results_are_unique_for_all_successful_fuels(self):
        self.check_lean(WEAK_CHECKS)

    def test_actual_root_certificate_uses_supplied_successful_fuel(self):
        self.check_lean(ROOT_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
