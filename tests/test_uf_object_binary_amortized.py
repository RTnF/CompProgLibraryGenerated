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
BINARY_FIXTURES = r'''
namespace UfObjectBinaryAmortizedExamples
open Proofs.UfHistoricalRank Proofs.UfRootCall Proofs.UfFindCall Proofs.UfClassInvariant
open UfObjectApartExamples UfMoveCallExamples UfObjectStateExamples UfObjectRootAmortizedExamples

theorem apartHistory : ∃ rho, Proofs.UfHistoricalRank.History apartParents rho := by
  have start := initial_history 4
  obtain ⟨rho1,one⟩ := unite_history start 0 1
    ⟨-1,by decide +kernel,by decide +kernel⟩ ⟨-1,by decide +kernel,by decide +kernel⟩
  obtain ⟨rho2,two⟩ := unite_history one 2 3
    ⟨-1,by decide +kernel,by decide +kernel⟩ ⟨-1,by decide +kernel,by decide +kernel⟩
  exact ⟨rho2,two⟩

theorem connectedSelf : Proofs.UfFieldsSame.Connected parents 3 3 :=
  ⟨0,path.reaches,path.reaches,-4,rfl,by decide +kernel⟩
end UfObjectBinaryAmortizedExamples
'''

SAME_CHECKS = r'''namespace UfObjectSameAmortizedExamples
open Proofs.UfObjectSameAmortized Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppNestedProgram UfMoveCallExamples UfObjectStateExamples UfObjectRootAmortizedExamples
example : ∃ (rho : Nat → Nat) (fuel : Nat) (out : Context) (result : Ret) (next : State out moved.2),
    invoke fuel moved.1 moved.2 (.same 3 1) = .finished (out,result) ∧
    Step moved.1 moved.2 inflated (.same 3 1) fuel out result next ∧
    Proofs.UfHistoricalRank.History next.data.items rho ∧
    work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
      work moved.1+91*Proofs.UfForestPotential.forestPotential parents rho+556*(Proofs.UfPotential.alpha 4+1) := by
  obtain ⟨rho,history⟩ := parentHistory
  obtain ⟨fuel,out,result,next,first⟩ := step moved.1 moved.2 inflated (.same 3 1)
    (by change 3 < 4 ∧ 1 < 4; decide +kernel)
  obtain ⟨after,certificate,hist,bound⟩ := actual_same_amortized moved.1 out moved.2 inflated rho history 3 1
    (by change 3 < 4; decide +kernel) (by change 1 < 4; decide +kernel) fuel result first.actual
  exact ⟨rho,fuel,out,result,after,first.actual,certificate,hist,bound⟩

example : ∃ (rho : Nat → Nat) (fuel : Nat) (out : Context) (result : Ret) (next : State out moved.2),
    invoke fuel moved.1 moved.2 (.same 3 1) = .finished (out,result) ∧
    Step moved.1 moved.2 inflated (.same 3 1) fuel out result next ∧
    Proofs.UfHistoricalRank.History next.data.items rho ∧
    work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
      work moved.1+91*Proofs.UfForestPotential.forestPotential parents rho+556*(Proofs.UfPotential.alpha 4+1) ∧
    out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget moved.1 ∧
    out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget moved.1 ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget moved.1 := by
  obtain ⟨rho,history⟩ := parentHistory
  obtain ⟨fuel,out,result,next,ran,certificate,hist,bound,scalar,heap,total⟩ := same_amortized_resources
    moved.1 moved.2 inflated UfObjectHeapPeakExamples.headerLive rho history 3 1
      (by change 3 < 4; decide +kernel) (by change 1 < 4; decide +kernel)
  exact ⟨rho,fuel,out,result,next,ran,certificate,hist,bound,scalar,heap,total⟩

end UfObjectSameAmortizedExamples

namespace UfObjectSameApartAmortizedExamples
open Proofs.UfObjectSameAmortized Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppNestedProgram UfMoveCallExamples UfObjectApartExamples UfObjectBinaryAmortizedExamples
example : ∃ (rank rho : Nat → Nat) (_math : Proofs.UfClassInvariant.Valid apartParents 2 rank)
    (fuel : Nat) (out : Context) (next : State out moved.2),
    invoke fuel apart moved.2 (.same 3 1) = .finished (out,.scalar 0) ∧
    next.receiver.counter.value = 2 ∧ Proofs.UfHistoricalRank.History next.data.items rho ∧
    work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
      work apart+91*Proofs.UfForestPotential.forestPotential apartParents rho+556*(Proofs.UfPotential.alpha 4+1) := by
  obtain ⟨rank,math⟩ := apartValid
  obtain ⟨rho,history⟩ := apartHistory
  let state := UfObjectTraceMeaningExamples.apartStart rank math
  obtain ⟨fuel,out,result,next,ran,first,hist,bound⟩ := same_amortized_step apart moved.2 state rho history 3 1
    (by change 3 < 4; decide +kernel) (by change 1 < 4; decide +kernel)
  obtain ⟨r1,r2,middle,returned,c1,c2,connected,countEq⟩ := first.meaning
  have different : r1 ≠ r2 := fun equal => notConnected (connected.mp equal)
  have resultEq : result = .scalar 0 := by simpa [different] using returned
  rw [resultEq] at ran
  exact ⟨rank,rho,math,fuel,out,next,ran,countEq,hist,bound⟩
end UfObjectSameApartAmortizedExamples
'''

UNITE_CHECKS = r'''
namespace UfObjectUniteMergeAmortizedExamples
open Proofs.UfObjectUniteAmortized Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppNestedProgram UfMoveCallExamples UfObjectApartExamples UfObjectStateExamples
open UfObjectBinaryAmortizedExamples UfObjectRootAmortizedExamples
example : ∃ (rank rho : Nat → Nat) (_math : Proofs.UfClassInvariant.Valid apartParents 2 rank) (fuel : Nat) (out : Context) (result : Ret)
    (next : State out moved.2) (nextRho : Nat → Nat),
    invoke fuel apart moved.2 (.unite 3 1) = .finished (out,result) ∧
    next.receiver.counter.value = 1 ∧ Proofs.UfHistoricalRank.History next.data.items nextRho ∧
    work out+91*Proofs.UfForestPotential.forestPotential next.data.items nextRho ≤
      work apart+91*Proofs.UfForestPotential.forestPotential apartParents rho+718*(Proofs.UfPotential.alpha 4+1) ∧
    out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget apart ∧
    out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget apart ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget apart := by
  obtain ⟨rank,math⟩ := apartValid
  obtain ⟨rho,history⟩ := apartHistory
  obtain ⟨fuel,out,result,next,nextRho,ran,first,hist,bound,scalar,heap,total⟩ :=
    unite_amortized_resources apart moved.2 (UfObjectTraceMeaningExamples.apartStart rank math) UfObjectHeapPeakExamples.apartHeaderLive rho history 3 1
      (by change 3 < 4; decide +kernel) (by change 1 < 4; decide +kernel)
  obtain ⟨r1,r2,middle,two,returned,c1,c2,nextEq,connected,countEq⟩ := first.meaning
  have different : r1 ≠ r2 := fun equal => notConnected (connected.mp equal)
  change next.receiver.counter.value = Proofs.UfFieldsUnite.countAfter 2 r1 r2 at countEq
  have countValue : next.receiver.counter.value = 1 := by simpa [Proofs.UfFieldsUnite.countAfter,different] using countEq
  exact ⟨rank,rho,math,fuel,out,result,next,nextRho,ran,countValue,hist,bound,scalar,heap,total⟩
end UfObjectUniteMergeAmortizedExamples

namespace UfObjectUniteSameAmortizedExamples
open Proofs.UfObjectUniteAmortized Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppNestedProgram UfMoveCallExamples UfObjectApartExamples UfObjectStateExamples
open UfObjectBinaryAmortizedExamples UfObjectRootAmortizedExamples
example : ∃ (rho : Nat → Nat) (fuel : Nat) (out : Context) (result : Ret)
    (next : State out moved.2) (nextRho : Nat → Nat),
    invoke fuel moved.1 moved.2 (.unite 3 3) = .finished (out,result) ∧
    next.receiver.counter.value = 1 ∧ Proofs.UfHistoricalRank.History next.data.items nextRho ∧
    work out+91*Proofs.UfForestPotential.forestPotential next.data.items nextRho ≤
      work moved.1+91*Proofs.UfForestPotential.forestPotential parents rho+718*(Proofs.UfPotential.alpha 4+1) ∧
    out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget moved.1 ∧
    out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget moved.1 ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget moved.1 := by
  obtain ⟨rho,history⟩ := parentHistory
  obtain ⟨fuel,out,result,next,nextRho,ran,first,hist,bound,scalar,heap,total⟩ :=
    unite_amortized_resources moved.1 moved.2 (inflated) UfObjectHeapPeakExamples.headerLive rho history 3 3
      (by change 3 < 4; decide +kernel) (by change 3 < 4; decide +kernel)
  obtain ⟨r1,r2,middle,two,returned,c1,c2,nextEq,connected,countEq⟩ := first.meaning
  have equal : r1 = r2 := connected.mpr connectedSelf
  change next.receiver.counter.value = Proofs.UfFieldsUnite.countAfter 1 r1 r2 at countEq
  have countValue : next.receiver.counter.value = 1 := by simpa [Proofs.UfFieldsUnite.countAfter,equal] using countEq
  exact ⟨rho,fuel,out,result,next,nextRho,ran,countValue,hist,bound,scalar,heap,total⟩
end UfObjectUniteSameAmortizedExamples
'''

class UfObjectBinaryAmortizedTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-binary-amortized-') as directory:
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

    def test_same_connected_and_disconnected_preserve_amortized_meanings(self):
        self.check_lean(SAME_CHECKS)

    def test_unite_merges_and_existing_component_keeps_resources(self):
        self.check_lean(UNITE_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
