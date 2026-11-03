"""Uniform scalar peaks, raw baseline range, and joint actual UF trace resources."""
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
from test_uf_object_root_scalar_peak import CHECKS as ROOT_CHECKS
from test_uf_object_trace import CHECKS as TRACE_CHECKS, MEANING_CHECKS
from test_uf_object_heap_peak import CHECKS as HEAP_CHECKS
from offline import disable_network

CHECKS = r'''
namespace UfObjectUniformScalarExamples
open Proofs.UfObjectUniformScalarPeak Proofs.UfObjectTrace Proofs.UfObjectTraceWork
open Proofs.UfObjectState Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppMoveObjectReceiver
open UfMoveCallExamples UfObjectStateExamples UfReceiverLayoutExamples UfObjectRootScalarExamples

#guard budget historical == 111
example (ops : List Operation) (ready : ∀ op ∈ ops, op.Valid initial.data.items.length) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret) (next : State out moved.2) (charge : Nat),
      script.map Prod.snd = ops ∧ run historical moved.2 script = .finished (out,results) ∧
      History moved.2 historical initial ops out results next ∧ Charges moved.2 historical initial ops out results next charge ∧
      work out ≤ work historical+charge ∧ out.scalars.peak ≤ 111 := by
  obtain ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound⟩ :=
    execute_work historical moved.2 initial ops ready
  have peak := history_peak moved.2 historical out initial next ops results history
  exact ⟨script,out,results,next,charge,mapped,ran,history,charges,bound,peak⟩

-- The original State permits a baseline inside the prepared prefix, beyond caller memory.
def rebased : Context := {historical with scalars := {historical.scalars with baseMemory := 9,peak := 0}}
def rebasedReceiver : Receiver rebased moved.2 ty :=
  ⟨⟨4,2,2,true,1,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    ⟨5,3,3,true,4,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    rfl,rfl,1,⟨1,true⟩,⟨some 0,0,true,limit⟩,by decide +kernel,by decide +kernel,rfl⟩
def rebasedState : State rebased moved.2 :=
  ⟨rebasedReceiver,⟨0,parents,5,limit,0⟩,rfl,ranks,parentValid,rfl,by decide +kernel,
    by decide +kernel,unique,covered,allocationsValid,rfl,by decide +kernel,contexts⟩
#guard rebased.scalars.memory.length < rebased.scalars.baseMemory
#guard budget rebased == 102
example (ops : List Operation) (ready : ∀ op ∈ ops, op.Valid rebasedState.data.items.length) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret),
      script.map Prod.snd = ops ∧ run rebased moved.2 script = .finished (out,results) ∧ out.scalars.peak ≤ 102 := by
  obtain ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound⟩ :=
    execute_work rebased moved.2 rebasedState ops ready
  have peak := actual_peak rebased out moved.2 rebasedState script results (by rw [mapped]; exact ready) ran
  exact ⟨script,out,results,mapped,ran,peak⟩
end UfObjectUniformScalarExamples
'''

JOINT_CHECKS = r'''
namespace UfObjectJointResourceExamples
open Proofs.UfObjectUniformScalarPeak Proofs.UfObjectTrace Proofs.UfObjectTraceWork
open Proofs.UfObjectState Proofs.CppMoveContext Proofs.CppNestedProgram
open UfMoveCallExamples UfObjectRootScalarExamples
example (ops : List Operation) (ready : ∀ op ∈ ops, op.Valid initial.data.items.length) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret) (next : State out moved.2) (charge : Nat),
      script.map Prod.snd = ops ∧ run historical moved.2 script = .finished (out,results) ∧
      History moved.2 historical initial ops out results next ∧ Charges moved.2 historical initial ops out results next charge ∧
      work out ≤ work historical+charge ∧ out.scalars.peak ≤ 111 ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget historical ∧
      out.objects.heap.liveSpace = historical.objects.heap.liveSpace ∧
      out.objects.heap.baseSpace = historical.objects.heap.baseSpace ∧
      Proofs.CppMoveSpace.HeadersLive out.objects.heap := by
  have live : Proofs.CppMoveSpace.HeadersLive historical.objects.heap := UfObjectHeapPeakExamples.headerLive
  obtain ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound,scalar,heap⟩ :=
    execute_resources historical moved.2 initial live ops ready
  exact ⟨script,out,results,next,charge,mapped,ran,history,charges,bound,scalar,heap⟩
end UfObjectJointResourceExamples
'''

class UfObjectUniformScalarPeakTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-uniform-scalar-peak-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectUniformScalarPeak\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                APART_DEFINITIONS + STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_arbitrary_traces_and_baseline_beyond_original_memory(self):
        self.check_lean(CHECKS)

    def test_actual_meanings_work_scalar_and_heap_bounds_hold_together(self):
        self.check_lean(JOINT_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
