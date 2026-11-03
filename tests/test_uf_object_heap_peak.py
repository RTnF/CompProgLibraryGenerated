"""Resident heap preservation and uniform UF method-trace heap peak bounds."""
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
namespace UfObjectHeapPeakExamples
open Proofs.UfObjectHeapPeak Proofs.UfObjectTrace Proofs.UfObjectTraceWork
open Proofs.UfObjectState Proofs.CppMoveContext Proofs.CppMoveHeaders Proofs.CppMoveSpace
open UfMoveCallExamples UfObjectStateExamples UfObjectTraceExamples

theorem headerLive : HeadersLive moved.1.objects.heap := by
  intro id header owner found owns
  change (([some (⟨none,0,true,limit⟩ : Header),some ⟨some 0,0,true,limit⟩][id]?).join) = some header at found
  cases id with
  | zero =>
    have same : header = ⟨none,0,true,limit⟩ := by simpa using found.symm
    subst header
    cases owns
  | succ id => cases id with
    | zero =>
      have same : header = ⟨some 0,0,true,limit⟩ := by simpa using found.symm
      subst header
      have zero : owner = 0 := by simpa using owns.symm
      subst owner
      decide +kernel
    | succ id => simp at found

theorem apartHeaderLive : HeadersLive UfObjectApartExamples.apart.objects.heap := by
  intro id header owner found owns
  change (([some (⟨none,0,true,limit⟩ : Header),some ⟨some 0,0,true,limit⟩][id]?).join) = some header at found
  cases id with
  | zero =>
    have same : header = ⟨none,0,true,limit⟩ := by simpa using found.symm
    subst header
    cases owns
  | succ id => cases id with
    | zero =>
      have same : header = ⟨some 0,0,true,limit⟩ := by simpa using found.symm
      subst header
      have zero : owner = 0 := by simpa using owns.symm
      subst owner
      decide +kernel
    | succ id => simp at found

example : ∃ (script : List (Nat × Operation)) (out : Context) (results : List Proofs.CppNestedProgram.Ret) (_next : State out moved.2),
    script.map Prod.snd = plan ∧ run moved.1 moved.2 script = .finished (out,results) ∧
    out.objects.heap.peak ≤ max moved.1.objects.heap.peak (moved.1.objects.heap.liveSpace+1-moved.1.objects.heap.baseSpace) ∧
    out.objects.heap.liveSpace = moved.1.objects.heap.liveSpace ∧
    out.objects.heap.baseSpace = moved.1.objects.heap.baseSpace ∧ HeadersLive out.objects.heap := by
  obtain ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound⟩ :=
    execute_work moved.1 moved.2 start plan planReady
  exact ⟨script,out,results,next,mapped,ran,history_peak moved.2 moved.1 out start next plan results history headerLive⟩

-- The same heap upper bound applies to any finite number of root calls.
example (count : Nat) : ∃ (script : List (Nat × Operation)) (out : Context) (results : List Proofs.CppNestedProgram.Ret) (_next : State out moved.2),
    script.map Prod.snd = List.replicate count (.root 3) ∧
    run moved.1 moved.2 script = .finished (out,results) ∧ out.objects.heap.peak ≤ budget moved.1 := by
  obtain ⟨script,out,results,next,charge,mapped,ran,num,size,history,charges,bound⟩ :=
    execute_work moved.1 moved.2 start (List.replicate count (.root 3)) (by
      intro op member
      have same : op = Operation.root 3 := List.eq_of_mem_replicate member
      subst op
      change 3 < 4
      decide +kernel)
  have peak := actual_peak moved.1 out moved.2 start headerLive script results (by
    rw [mapped]
    intro op member
    have same : op = Operation.root 3 := List.eq_of_mem_replicate member
    subst op
    change 3 < 4
    decide +kernel) ran
  exact ⟨script,out,results,next,mapped,ran,peak.1⟩
example (rank : Nat → Nat) (math : Proofs.UfClassInvariant.Valid UfObjectApartExamples.apartParents 2 rank) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Proofs.CppNestedProgram.Ret),
      script.map Prod.snd = plan ∧ run UfObjectApartExamples.apart moved.2 script = .finished (out,results) ∧
      out.objects.heap.peak ≤ budget UfObjectApartExamples.apart := by
  let original := UfObjectTraceMeaningExamples.apartStart rank math
  obtain ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound⟩ :=
    execute_work UfObjectApartExamples.apart moved.2 original plan (by exact planReady)
  have peak := history_peak moved.2 UfObjectApartExamples.apart out original next plan results history apartHeaderLive
  exact ⟨script,out,results,mapped,ran,peak.1⟩
end UfObjectHeapPeakExamples
'''

ADDITIONAL_CHECKS = r'''
namespace UfObjectAdditionalHeapExamples
open Proofs.UfObjectHeapPeak Proofs.UfObjectTrace Proofs.UfObjectTraceWork
open Proofs.UfObjectState Proofs.CppMoveContext Proofs.CppMoveObjectReceiver Proofs.CppMoveSpace
open UfMoveCallExamples UfObjectStateExamples UfReceiverLayoutExamples UfObjectTraceExamples UfObjectHeapPeakExamples

-- Begin an additional-heap measurement at the actual current resident amount.
def reset : Context := {moved.1 with objects := {moved.1.objects with heap :=
  {moved.1.objects.heap with baseSpace := moved.1.objects.heap.liveSpace,peak := 0}}}
def receiver : Receiver reset moved.2 ty :=
  ⟨⟨4,2,2,true,1,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    ⟨5,3,3,true,4,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    rfl,rfl,1,⟨1,true⟩,⟨some 0,0,true,limit⟩,by decide +kernel,by decide +kernel,rfl⟩
def initial : State reset moved.2 :=
  ⟨receiver,⟨0,parents,5,limit,0⟩,rfl,ranks,parentValid,rfl,by decide +kernel,
    by decide +kernel,unique,covered,allocationsValid,rfl,by decide +kernel,contexts⟩
theorem live : HeadersLive reset.objects.heap := headerLive
#guard reset.objects.heap.liveSpace == 7
#guard reset.objects.heap.baseSpace == 7 && reset.objects.heap.peak == 0

example : ∃ (script : List (Nat × Operation)) (out : Context) (results : List Proofs.CppNestedProgram.Ret)
    (next : State out moved.2) (charge : Nat),
    script.map Prod.snd = plan ∧ run reset moved.2 script = .finished (out,results) ∧
    History moved.2 reset initial plan out results next ∧ Charges moved.2 reset initial plan out results next charge ∧
    work out ≤ work reset+charge ∧ out.objects.heap.peak ≤ 1 := by
  obtain ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound,peak,space,base,headers⟩ :=
    execute_peak_work reset moved.2 initial live plan (by exact planReady)
  have additional := actual_additional_peak reset out moved.2 initial live rfl script results
    (by rw [mapped]; exact planReady) ran
  refine ⟨script,out,results,next,charge,mapped,ran,history,charges,bound,?_⟩
  exact additional
end UfObjectAdditionalHeapExamples
'''

class UfObjectHeapPeakTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-heap-peak-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectHeapPeak\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                APART_DEFINITIONS + STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_mixed_apart_and_arbitrary_length_root_traces_preserve_heap_bounds(self):
        self.check_lean(CHECKS)

    def test_new_measurement_baseline_bounds_additional_heap_with_work_and_meanings(self):
        self.check_lean(CHECKS + ADDITIONAL_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
