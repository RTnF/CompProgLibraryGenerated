"""Independent scalar peak bounds for all original ObjectRef UF methods."""
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
from test_uf_object_trace import MEANING_CHECKS as TRACE_MEANING_CHECKS, CHECKS as TRACE_CHECKS
from test_uf_object_root_scalar_peak import CHECKS as ROOT_CHECKS
from offline import disable_network

CHECKS = r'''
namespace UfObjectMethodScalarExamples
open Proofs.UfObjectMethodScalarPeak Proofs.UfObjectTrace Proofs.UfObjectState
open Proofs.CppMoveContext Proofs.CppMoveReceiverLayout Proofs.CppNestedProgram
open UfMoveCallExamples UfObjectRootScalarExamples

def operations : List Operation := [.root 3,.same 3 1,.size 3,.unite 3 1,.groups]
def argsFor (op : Operation) := Proofs.UfObjectCall.arguments historical moved.2 initial.receiver op.expressions
def prepFor (op : Operation) := (prepareArguments historical ty op.program.parameters (argsFor op)).getD historical

theorem allReady : ∀ op ∈ operations, op.Valid initial.data.items.length := by
  intro op member
  simp only [operations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> simp only [Operation.Valid] <;> decide +kernel

theorem allBudgets : ∀ op ∈ operations,
    max (max historical.scalars.peak
      (max (prepFor op).scalars.peak ((receiverPrefix historical).length+100-historical.scalars.baseMemory)))
      (historical.scalars.memory.length-historical.scalars.baseMemory+historical.scalars.bindings.length) ≤ 111 := by
  intro op member
  simp only [operations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

example : ∀ op ∈ operations, ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out moved.2),
    invoke fuel historical moved.2 op = .finished (out,result) ∧
    Effect initial.data.items next.data.items initial.receiver.counter.value next.receiver.counter.value op result ∧
    out.scalars.peak ≤ 111 ∧ 1000000 ≤ out.peak := by
  intro op member
  obtain ⟨fuel,out,result,next,first⟩ := step historical moved.2 initial op (allReady op member)
  obtain ⟨prepared,prep,scalar⟩ := call_peak historical out moved.2 initial op (allReady op member) fuel result first.actual
  have same : prepFor op = prepared := by
    simp only [prepFor,argsFor,prep,Option.getD]
  rw [← same] at scalar
  have actual := first.actual
  rw [invoke_state fuel historical moved.2 initial op] at actual
  obtain ⟨p,i,body,after,pRun,iRun,bRun,breaking,finished,restored⟩ :=
    Proofs.CppCompactScalarPeak.call_parts op.program fuel historical out ty _ result actual
  have ret : ∃ retType : Proofs.CppScalar.Ty, op.program.result = .scalar retType := by
    cases op <;> exact ⟨_,rfl⟩
  obtain ⟨retType,retEq⟩ := ret
  rw [retEq] at finished
  have counters := Proofs.CppMovePreparedCall.restored_finish_counters historical out ty retType body.state after
    body.returned result finished restored initial.covered
  have outer : 1000000 ≤ out.peak := by
    rw [counters.2.2]
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  exact ⟨fuel,out,result,next,first.actual,first.meaning,scalar.trans (allBudgets op member),outer⟩
end UfObjectMethodScalarExamples
'''

APART_CHECKS = r'''
namespace UfObjectApartScalarExamples
open Proofs.UfObjectMethodScalarPeak Proofs.UfObjectTrace Proofs.UfObjectState
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppMoveReceiverLayout
open UfMoveCallExamples UfObjectApartExamples UfObjectTraceMeaningExamples
example (rank : Nat → Nat) (math : Proofs.UfClassInvariant.Valid apartParents 2 rank) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out moved.2) (prepared : Context),
      invoke fuel apart moved.2 (.unite 3 1) = .finished (out,result) ∧
      Effect apartParents next.data.items 2 next.receiver.counter.value (.unite 3 1) result ∧
      prepareArguments apart ty Proofs.UnionFindCandidateInstance.UnionFind_unite.parameters
        (Proofs.UfObjectCall.arguments apart moved.2 (apartStart rank math).receiver
          [(.literal ty 3,3),(.literal ty 1,1)]) = some prepared ∧
      out.scalars.peak ≤ max (max apart.scalars.peak
        (max prepared.scalars.peak ((receiverPrefix apart).length+100-apart.scalars.baseMemory)))
        (apart.scalars.memory.length-apart.scalars.baseMemory+apart.scalars.bindings.length) := by
  let original := apartStart rank math
  have ready : (Operation.unite 3 1).Valid original.data.items.length := by change 3 < 4 ∧ 1 < 4; decide +kernel
  obtain ⟨fuel,out,result,next,first⟩ := step apart moved.2 original (.unite 3 1) ready
  obtain ⟨prepared,prep,scalar⟩ := call_peak apart out moved.2 original (.unite 3 1) ready fuel result first.actual
  exact ⟨fuel,out,result,next,prepared,first.actual,first.meaning,prep,scalar⟩
end UfObjectApartScalarExamples
'''

class UfObjectMethodScalarPeakTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-method-scalar-peak-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectMethodScalarPeak\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                APART_DEFINITIONS + STATE_CHECKS + TRACE_CHECKS + TRACE_MEANING_CHECKS + ROOT_CHECKS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_all_source_methods_keep_scalar_peak_independent_of_historical_outer_peak(self):
        self.check_lean(CHECKS)

    def test_distinct_component_union_meaning_and_scalar_bound_share_actual_result(self):
        self.check_lean(APART_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
