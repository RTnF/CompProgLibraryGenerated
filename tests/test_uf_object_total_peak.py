"""Joint functional/work/component/total peak bounds for arbitrary finite UF traces."""
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
namespace UfObjectTotalPeakExamples
open Proofs.UfObjectTotalPeak Proofs.UfObjectTrace Proofs.UfObjectTraceWork
open Proofs.UfObjectState Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppMoveObjectReceiver
open UfMoveCallExamples UfObjectStateExamples UfReceiverLayoutExamples UfObjectRootScalarExamples

def measured : Context :=
  {historical with
    peak := 0,
    scalars := {historical.scalars with baseMemory := historical.scalars.memory.length,peak := 0},
    objects := {historical.objects with heap := {historical.objects.heap with baseSpace := historical.objects.heap.liveSpace,peak := 0}}}
def measuredReceiver : Receiver measured moved.2 ty :=
  ⟨⟨4,2,2,true,1,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    ⟨5,3,3,true,4,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    rfl,rfl,1,⟨1,true⟩,⟨some 0,0,true,limit⟩,by decide +kernel,by decide +kernel,rfl⟩
def measuredState : State measured moved.2 :=
  ⟨measuredReceiver,⟨0,parents,5,limit,0⟩,rfl,ranks,parentValid,rfl,by decide +kernel,
    by decide +kernel,unique,covered,allocationsValid,rfl,by decide +kernel,contexts⟩
theorem live : Proofs.CppMoveSpace.HeadersLive measured.objects.heap := UfObjectHeapPeakExamples.headerLive
#guard scalarBudget measured == 107
#guard heapBudget measured == 1
#guard budget measured == 108

example (ops : List Operation) (ready : ∀ op ∈ ops, op.Valid measuredState.data.items.length) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret) (next : State out moved.2) (charge : Nat),
      script.map Prod.snd = ops ∧ run measured moved.2 script = .finished (out,results) ∧
      History moved.2 measured measuredState ops out results next ∧ Charges moved.2 measured measuredState ops out results next charge ∧
      work out ≤ work measured+charge ∧ out.scalars.peak ≤ 107 ∧ out.objects.heap.peak ≤ 1 ∧ out.peak ≤ 108 := by
  obtain ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound,scalar,total,heap,space,base,headers⟩ :=
    execute_resources measured moved.2 measuredState live ops ready
  exact ⟨script,out,results,next,charge,mapped,ran,history,charges,bound,scalar,heap,total⟩

-- Apply the generic new-measurement theorem to the actual supplied script.
example (script : List (Nat × Operation)) (out : Context) (results : List Ret)
    (ready : ∀ op ∈ script.map Prod.snd, op.Valid measuredState.data.items.length)
    (actual : run measured moved.2 script = .finished (out,results)) : out.peak ≤ 108 := by
  exact actual_additional measured out moved.2 measuredState live rfl rfl rfl rfl rfl script results ready actual
end UfObjectTotalPeakExamples
'''

HISTORICAL_CHECKS = r'''
namespace UfObjectHistoricalTotalExamples
open Proofs.UfObjectTotalPeak Proofs.UfObjectTrace Proofs.UfObjectTraceWork
open Proofs.UfObjectState Proofs.CppMoveContext Proofs.CppNestedProgram
open UfMoveCallExamples UfObjectRootScalarExamples
#guard budget historical == 1000000
example (ops : List Operation) (ready : ∀ op ∈ ops, op.Valid initial.data.items.length) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret) (next : State out moved.2) (charge : Nat),
      script.map Prod.snd = ops ∧ run historical moved.2 script = .finished (out,results) ∧
      History moved.2 historical initial ops out results next ∧ Charges moved.2 historical initial ops out results next charge ∧
      work out ≤ work historical+charge ∧ out.peak ≤ 1000000 := by
  have live : Proofs.CppMoveSpace.HeadersLive historical.objects.heap := UfObjectHeapPeakExamples.headerLive
  obtain ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound,scalar,total,heap⟩ :=
    execute_resources historical moved.2 initial live ops ready
  exact ⟨script,out,results,next,charge,mapped,ran,history,charges,bound,total⟩
end UfObjectHistoricalTotalExamples
'''

class UfObjectTotalPeakTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-total-peak-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectTotalPeak\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                APART_DEFINITIONS + STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_new_baseline_arbitrary_traces_keep_meanings_work_and_total_peak_108(self):
        self.check_lean(CHECKS)

    def test_historical_total_peak_does_not_grow_with_operation_count(self):
        self.check_lean(HISTORICAL_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
