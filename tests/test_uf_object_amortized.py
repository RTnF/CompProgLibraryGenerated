"""Binary UF calls preserve actual meanings, historical potential and all peak bounds."""
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

from test_uf_object_query_amortized import FIXTURES
from test_uf_object_binary_amortized import BINARY_FIXTURES
CHECKS = r'''
namespace UfObjectAmortizedExamples
open Proofs.UfObjectAmortized Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppNestedProgram UfMoveCallExamples UfObjectStateExamples UfObjectRootAmortizedExamples
example (ops : List Operation) (ready : ∀ op ∈ ops, op.Valid 4) :
    ∃ (rho : Nat → Nat) (script : List (Nat × Operation)) (out : Context) (results : List Ret)
      (next : State out moved.2) (nextRho : Nat → Nat),
      script.map Prod.snd = ops ∧ run moved.1 moved.2 script = .finished (out,results) ∧
      History moved.2 moved.1 inflated ops out results next ∧ Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out+91*Proofs.UfForestPotential.forestPotential next.data.items nextRho ≤
        work moved.1+91*Proofs.UfForestPotential.forestPotential parents rho+718*ops.length*(Proofs.UfPotential.alpha 4+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget moved.1 ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget moved.1 ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget moved.1 := by
  obtain ⟨rho,mathHistory⟩ := parentHistory
  obtain ⟨script,out,results,next,nextRho,mapped,ran,count,size,history,mathNext,bound,scalar,heap,total⟩ :=
    execute_resources moved.1 moved.2 inflated UfObjectHeapPeakExamples.headerLive rho mathHistory ops ready
  exact ⟨rho,script,out,results,next,nextRho,mapped,ran,history,mathNext,bound,scalar,heap,total⟩

-- Empty operations require no calls and preserve the original work and potential.
example (rho : Nat → Nat) (history : Proofs.UfHistoricalRank.History parents rho) :=
  execute_amortized moved.1 moved.2 inflated rho history [] (by simp)
end UfObjectAmortizedExamples
'''

MERGE_CHECKS = r'''
namespace UfObjectMergeTraceAmortizedExamples
open Proofs.UfObjectAmortized Proofs.UfObjectTrace Proofs.UfObjectTraceActual Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppNestedProgram UfMoveCallExamples UfObjectApartExamples UfObjectBinaryAmortizedExamples UfObjectTraceExamples
example : ∃ (rank rho : Nat → Nat) (math : Proofs.UfClassInvariant.Valid apartParents 2 rank)
    (script : List (Nat × Operation)) (out : Context) (results : List Ret)
    (next : State out moved.2) (nextRho : Nat → Nat),
    script.map Prod.snd = plan ∧
    run apart moved.2 (script.map (fun entry => (entry.1+17,entry.2))) = .finished (out,results) ∧
    History moved.2 apart (UfObjectTraceMeaningExamples.apartStart rank math) plan out results next ∧
    Proofs.UfHistoricalRank.History next.data.items nextRho ∧
    work out+91*Proofs.UfForestPotential.forestPotential next.data.items nextRho ≤
      work apart+91*Proofs.UfForestPotential.forestPotential apartParents rho+718*6*(Proofs.UfPotential.alpha 4+1) ∧
    out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget apart ∧
    out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget apart ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget apart := by
  obtain ⟨rank,math⟩ := apartValid
  obtain ⟨rho,mathHistory⟩ := apartHistory
  let state := UfObjectTraceMeaningExamples.apartStart rank math
  obtain ⟨script,out,results,next,nextRho,mapped,ran,count,size,history,mathNext,bound,scalar,heap,total⟩ :=
    execute_resources apart moved.2 state UfObjectHeapPeakExamples.apartHeaderLive rho mathHistory plan planReady
  have more := run_success_mono apart moved.2 script 17 out results ran
  have moreMapped : (script.map (fun entry => (entry.1+17,entry.2))).map Prod.snd = plan := by
    simpa only [List.map_map,Function.comp_def] using mapped
  have moreReady : ∀ op ∈ (script.map (fun entry => (entry.1+17,entry.2))).map Prod.snd, op.Valid state.data.items.length := by
    rw [moreMapped]
    exact planReady
  obtain ⟨after,afterRho,actualHistory,actualMath,actualBound⟩ :=
    actual_amortized apart out moved.2 state rho mathHistory _ results moreReady more
  rw [moreMapped] at actualHistory
  have scriptLength : script.length = 6 := by
    have same := congrArg List.length mapped
    simpa only [List.length_map,plan,List.length_cons,List.length_nil] using same
  simp only [List.length_map,scriptLength] at actualBound
  exact ⟨rank,rho,math,script,out,results,after,afterRho,mapped,more,actualHistory,actualMath,actualBound,scalar,heap,total⟩
end UfObjectMergeTraceAmortizedExamples
'''

class UfObjectAmortizedTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-amortized-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectAmortized\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                APART_DEFINITIONS + STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS + FIXTURES + BINARY_FIXTURES + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_arbitrary_operations_and_empty_trace_keep_amortized_resources(self):
        self.check_lean(CHECKS)

    def test_mixed_merge_trace_with_extra_fuel_preserves_actual_amortized_certificate(self):
        self.check_lean(MERGE_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
