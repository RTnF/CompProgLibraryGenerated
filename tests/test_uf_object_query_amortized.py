"""Path based root/size work, historical potential and existing space certificates."""
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

FIXTURES = r'''
namespace UfObjectRootAmortizedExamples
open Proofs.UfObjectRootAmortized Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppNestedProgram Proofs.UfClassInvariant Proofs.UfPathAmortized
open UfMoveCallExamples UfObjectStateExamples

theorem parentHistory : ∃ rho, Proofs.UfHistoricalRank.History parents rho := by
  have start := Proofs.UfHistoricalRank.initial_history 4
  obtain ⟨rho1,one⟩ := Proofs.UfHistoricalRank.unite_history start 0 1
    ⟨-1,by decide +kernel,by decide +kernel⟩ ⟨-1,by decide +kernel,by decide +kernel⟩
  obtain ⟨rho2,two⟩ := Proofs.UfHistoricalRank.unite_history one 2 3
    ⟨-1,by decide +kernel,by decide +kernel⟩ ⟨-1,by decide +kernel,by decide +kernel⟩
  obtain ⟨rho3,three⟩ := Proofs.UfHistoricalRank.unite_history two 0 2
    ⟨-2,by decide +kernel,by decide +kernel⟩ ⟨-2,by decide +kernel,by decide +kernel⟩
  change Proofs.UfHistoricalRank.History parents rho3 at three
  exact ⟨rho3,three⟩

theorem path : Trace parents 3 0 [3,2] :=
  .step 3 2 0 [2] rfl (.step 2 0 0 [] rfl (.done 0 (-4) rfl (by decide +kernel)))

theorem inflatedValid : Valid parents 1 (fun i => ranks i+1000) := by
  refine ⟨⟨parentValid.forest.valid,parentValid.forest.inside,?_⟩,parentValid.length,parentValid.sizes,parentValid.count⟩
  intro i p found nonnegative
  have smaller := parentValid.forest.decrease i p found nonnegative
  omega

def inflated : State moved.1 moved.2 := {start with rank := fun i => ranks i+1000,math := inflatedValid}

end UfObjectRootAmortizedExamples
'''

ROOT_AMORTIZED_CHECKS = r'''namespace UfObjectRootAmortizedExamples
open Proofs.UfObjectRootAmortized Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppNestedProgram Proofs.UfClassInvariant Proofs.UfPathAmortized
open UfMoveCallExamples UfObjectStateExamples

-- The work bound follows the path length, even with a loose termination rank.
example : ∃ (fuel : Nat) (out : Context) (result : Ret) (_next : State out moved.2),
    invoke fuel moved.1 moved.2 (.root 3) = .finished (out,result) ∧ work out ≤ work moved.1+272 := by
  obtain ⟨fuel,out,result,next,first⟩ := step moved.1 moved.2 inflated (.root 3) (by change 3 < 4; decide +kernel)
  have bound := root_trace_work moved.1 out moved.2 inflated 3 0 [3,2] path fuel result first.actual
  exact ⟨fuel,out,result,next,first.actual,by simpa using bound⟩

example : ∃ (rho : Nat → Nat) (fuel : Nat) (out : Context) (result : Ret) (next : State out moved.2),
    invoke fuel moved.1 moved.2 (.root 3) = .finished (out,result) ∧
    Step moved.1 moved.2 inflated (.root 3) fuel out result next ∧ Proofs.UfHistoricalRank.History next.data.items rho ∧
    work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
      work moved.1+91*Proofs.UfForestPotential.forestPotential parents rho+272*(Proofs.UfPotential.alpha 4+1) := by
  obtain ⟨rho,history⟩ := parentHistory
  obtain ⟨fuel,out,result,next,ran,first,historyAfter,bound⟩ := root_amortized_step moved.1 moved.2 inflated rho history 3
    (by change 3 < 4; decide +kernel)
  exact ⟨rho,fuel,out,result,next,ran,first,historyAfter,bound⟩
example : ∃ (rho : Nat → Nat) (fuel : Nat) (out : Context) (result : Ret) (next : State out moved.2),
    invoke fuel moved.1 moved.2 (.root 3) = .finished (out,result) ∧
    Step moved.1 moved.2 inflated (.root 3) fuel out result next ∧ Proofs.UfHistoricalRank.History next.data.items rho ∧
    work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
      work moved.1+91*Proofs.UfForestPotential.forestPotential parents rho+272*(Proofs.UfPotential.alpha 4+1) ∧
    out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget moved.1 ∧
    out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget moved.1 ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget moved.1 := by
  obtain ⟨rho,history⟩ := parentHistory
  obtain ⟨fuel,out,result,next,ran,first,historyAfter,bound,scalar,heap,total⟩ :=
    root_amortized_resources moved.1 moved.2 inflated UfObjectHeapPeakExamples.headerLive rho history 3
      (by change 3 < 4; decide +kernel)
  exact ⟨rho,fuel,out,result,next,ran,first,historyAfter,bound,scalar,heap,total⟩
end UfObjectRootAmortizedExamples
'''

SIZE_AMORTIZED_CHECKS = r'''namespace UfObjectSizeAmortizedExamples
open Proofs.UfObjectSizeAmortized Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppNestedProgram Proofs.UfClassInvariant Proofs.UfPathAmortized
open UfMoveCallExamples UfObjectStateExamples UfObjectRootAmortizedExamples

-- The work bound follows the path length, even with a loose termination rank.
example : ∃ (fuel : Nat) (out : Context) (result : Ret) (_next : State out moved.2),
    invoke fuel moved.1 moved.2 (.size 3) = .finished (out,result) ∧ work out ≤ work moved.1+292 := by
  obtain ⟨fuel,out,result,next,first⟩ := step moved.1 moved.2 inflated (.size 3) (by change 3 < 4; decide +kernel)
  have bound := size_trace_work moved.1 out moved.2 inflated 3 0 [3,2] path fuel result first.actual
  exact ⟨fuel,out,result,next,first.actual,by simpa using bound⟩

example : ∃ (rho : Nat → Nat) (fuel : Nat) (out : Context) (result : Ret) (next : State out moved.2),
    invoke fuel moved.1 moved.2 (.size 3) = .finished (out,result) ∧
    Step moved.1 moved.2 inflated (.size 3) fuel out result next ∧ Proofs.UfHistoricalRank.History next.data.items rho ∧
    work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
      work moved.1+91*Proofs.UfForestPotential.forestPotential parents rho+292*(Proofs.UfPotential.alpha 4+1) := by
  obtain ⟨rho,history⟩ := parentHistory
  obtain ⟨fuel,out,result,next,ran,first,historyAfter,bound⟩ := size_amortized_step moved.1 moved.2 inflated rho history 3
    (by change 3 < 4; decide +kernel)
  exact ⟨rho,fuel,out,result,next,ran,first,historyAfter,bound⟩
example : ∃ (rho : Nat → Nat) (fuel : Nat) (out : Context) (result : Ret) (next : State out moved.2),
    invoke fuel moved.1 moved.2 (.size 3) = .finished (out,result) ∧
    Step moved.1 moved.2 inflated (.size 3) fuel out result next ∧ Proofs.UfHistoricalRank.History next.data.items rho ∧
    work out+91*Proofs.UfForestPotential.forestPotential next.data.items rho ≤
      work moved.1+91*Proofs.UfForestPotential.forestPotential parents rho+292*(Proofs.UfPotential.alpha 4+1) ∧
    out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget moved.1 ∧
    out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget moved.1 ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget moved.1 := by
  obtain ⟨rho,history⟩ := parentHistory
  obtain ⟨fuel,out,result,next,ran,first,historyAfter,bound,scalar,heap,total⟩ :=
    size_amortized_resources moved.1 moved.2 inflated UfObjectHeapPeakExamples.headerLive rho history 3
      (by change 3 < 4; decide +kernel)
  exact ⟨rho,fuel,out,result,next,ran,first,historyAfter,bound,scalar,heap,total⟩
end UfObjectSizeAmortizedExamples
'''

class UfObjectQueryAmortizedTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-query-amortized-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectSizeAmortized\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                APART_DEFINITIONS + STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS + FIXTURES + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_root_path_work_ignores_loose_rank_and_preserves_resources(self):
        self.check_lean(ROOT_AMORTIZED_CHECKS)

    def test_size_path_work_ignores_loose_rank_and_preserves_resources(self):
        self.check_lean(SIZE_AMORTIZED_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
