"""Sharp scalar peaks through actual compact root calls and restoration."""
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
namespace UfObjectRootScalarExamples
open Proofs.UfObjectRootScalarPeak Proofs.CppCompactScalarPeak
open Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext Proofs.CppMoveObjectReceiver
open Proofs.CppNestedProgram Proofs.CppMoveCallBindings Proofs.CppMoveReceiverLayout
open UfMoveCallExamples UfObjectStateExamples UfReceiverLayoutExamples

-- Keep a large historical total peak while retaining the same real scalar/heap data.
def historical : Context := {moved.1 with peak := 1000000}
def receiver : Receiver historical moved.2 ty :=
  ⟨⟨4,2,2,true,1,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    ⟨5,3,3,true,4,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    rfl,rfl,1,⟨1,true⟩,⟨some 0,0,true,limit⟩,by decide +kernel,by decide +kernel,rfl⟩
def initial : State historical moved.2 :=
  ⟨receiver,⟨0,parents,5,limit,0⟩,rfl,ranks,parentValid,rfl,by decide +kernel,
    by decide +kernel,unique,covered,allocationsValid,rfl,by decide +kernel,contexts⟩
def args := Proofs.UfObjectCall.arguments historical moved.2 receiver [(.literal ty 3,3)]
def prepared := (prepareArguments historical ty Proofs.UnionFindCandidateInstance.UnionFind_root.parameters args).getD historical
theorem preparedRun : prepareArguments historical ty Proofs.UnionFindCandidateInstance.UnionFind_root.parameters args = some prepared := by
  have nonempty : (prepareArguments historical ty Proofs.UnionFindCandidateInstance.UnionFind_root.parameters args).isSome = true := by decide +kernel
  have found : prepareArguments historical ty Proofs.UnionFindCandidateInstance.UnionFind_root.parameters args ≠ none := by
    intro missing
    simp [missing] at nonempty
  exact (Option.getD_of_ne_none found historical).symm

example : ∃ (fuel : Nat) (out : Context) (result : Ret) (_next : State out moved.2),
    invoke fuel historical moved.2 (.root 3) = .finished (out,result) ∧
    out.scalars.peak ≤ 91 ∧ 1000000 ≤ out.peak := by
  obtain ⟨fuel,out,result,next,first⟩ := step historical moved.2 initial (.root 3) (by change 3 < 4; decide +kernel)
  obtain ⟨actualPrepared,prep,scalar⟩ := root_call_peak historical out moved.2 initial 3
    (by change 3 < 4; decide +kernel) fuel result first.actual
  have same := Option.some.inj (prep.symm.trans preparedRun)
  subst actualPrepared
  have bound : max (max historical.scalars.peak
      (max prepared.scalars.peak ((receiverPrefix historical).length+80-historical.scalars.baseMemory)))
      (historical.scalars.memory.length-historical.scalars.baseMemory+historical.scalars.bindings.length) ≤ 91 := by decide +kernel
  have actual := first.actual
  rw [invoke_state fuel historical moved.2 initial (.root 3)] at actual
  obtain ⟨p,i,body,after,pRun,iRun,bRun,breaking,finished,restored⟩ :=
    call_parts Proofs.UnionFindCandidateInstance.UnionFind_root fuel historical out ty _ result actual
  have counters := Proofs.CppMovePreparedCall.restored_finish_counters historical out ty ty body.state after
    body.returned result finished restored covered
  have outer : 1000000 ≤ out.peak := by
    rw [counters.2.2]
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  exact ⟨fuel,out,result,next,first.actual,scalar.trans bound,outer⟩
end UfObjectRootScalarExamples
'''

MEANING_CHECKS = r'''
namespace UfObjectRootScalarMeaningExamples
open Proofs.UfObjectRootScalarPeak Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppNestedProgram Proofs.CppMoveReceiverLayout
open UfMoveCallExamples UfObjectStateExamples
example : ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out moved.2) (prepared : Context),
    invoke fuel moved.1 moved.2 (.root 3) = .finished (out,result) ∧
    Effect start.data.items next.data.items start.receiver.counter.value next.receiver.counter.value (.root 3) result ∧
    prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_root.parameters
      (Proofs.UfObjectCall.arguments moved.1 moved.2 start.receiver [(.literal ty 3,3)]) = some prepared ∧
    out.scalars.peak ≤ max (max moved.1.scalars.peak
      (max prepared.scalars.peak ((receiverPrefix moved.1).length+80-moved.1.scalars.baseMemory)))
      (moved.1.scalars.memory.length-moved.1.scalars.baseMemory+moved.1.scalars.bindings.length) := by
  obtain ⟨fuel,out,result,next,first⟩ := step moved.1 moved.2 start (.root 3) (by change 3 < 4; decide +kernel)
  obtain ⟨prepared,prep,peak⟩ := root_call_peak moved.1 out moved.2 start 3
    (by change 3 < 4; decide +kernel) fuel result first.actual
  exact ⟨fuel,out,result,next,prepared,first.actual,first.meaning,prep,peak⟩
end UfObjectRootScalarMeaningExamples
'''

class UfObjectRootScalarPeakTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-root-scalar-peak-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectRootScalarPeak\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                APART_DEFINITIONS + STATE_CHECKS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_historical_outer_peak_does_not_inflate_root_scalar_peak(self):
        self.check_lean(CHECKS)

    def test_functional_root_meaning_and_scalar_bound_hold_for_same_actual_result(self):
        self.check_lean(MEANING_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
