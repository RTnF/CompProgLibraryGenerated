"""Initial singleton and empty UF states give work bounds without initial potential."""
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

SINGLETON_CHECKS = r'''

namespace UfObjectFresh4Examples
open Proofs.CppMoveContext Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppMoveObjectReceiver
open Proofs.UfClassInvariant Proofs.UfRootCall Proofs.UfMergeInvariant
open UfMoveCallExamples UfReceiverLayoutExamples

def freshParents : List Int := List.replicate 4 (-1)
def fresh : Context := {moved.1 with
  objects := {moved.1.objects with heap := {moved.1.objects.heap with allocations :=
    [some ⟨⟨0,freshParents,5,limit,0⟩,fun _ => 7⟩,none]}},
  scalars := {moved.1.scalars with memory := moved.1.scalars.memory.set 2 ⟨ty,4⟩}}
def receiver : Receiver fresh moved.2 ty :=
  ⟨⟨4,2,2,true,4,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    ⟨5,3,3,true,4,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    rfl,rfl,1,⟨1,true⟩,⟨some 0,0,true,limit⟩,by decide +kernel,by decide +kernel,rfl⟩

theorem freshCovered : OwnsAll fresh.objects.heap := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside fresh.objects.heap owner tracked found
  change owner < 2 at inside
  have choices : owner=0 ∨ owner=1 := by omega
  rcases choices with rfl | rfl
  · exact ⟨1,⟨some 0,0,true,limit⟩,rfl,rfl⟩
  · have missing : fresh.objects.heap.allocation 1 = none := rfl
    rw [missing] at found
    contradiction

theorem freshAllocations : AllocationsValid fresh.objects.heap ty := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside fresh.objects.heap owner tracked found
  change owner < 2 at inside
  have choices : owner=0 ∨ owner=1 := by omega
  rcases choices with rfl | rfl
  · have slot : fresh.objects.heap.allocation 0 = some ⟨⟨0,freshParents,5,limit,0⟩,fun _ => 7⟩ := rfl
    rw [slot] at found
    cases Option.some.inj found
    decide +kernel
  · have missing : fresh.objects.heap.allocation 1 = none := rfl
    rw [missing] at found
    contradiction

theorem freshContexts : ∀ owner sc, (project fresh ty).frame.state.forest.context owner = some sc → sc ≤ fresh.scope := by
  intro owner sc found
  have forestEq : (project fresh ty).frame.state.forest = (project moved.1 ty).frame.state.forest := rfl
  rw [forestEq] at found
  exact contexts owner sc found

end UfObjectFresh4Examples

namespace UfObjectInitial4Examples
open Proofs.UfObjectInitialAmortized Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppNestedProgram Proofs.UfClassInvariant
open UfMoveCallExamples UfReceiverLayoutExamples UfObjectFresh4Examples

def initialState : State fresh moved.2 :=
  ⟨receiver,⟨0,freshParents,5,limit,0⟩,rfl,(fun _ => 0),initial_valid 4 (by decide +kernel),
    rfl,by decide +kernel,by decide +kernel,unique,freshCovered,freshAllocations,rfl,by decide +kernel,freshContexts⟩
theorem headersLive : Proofs.CppMoveSpace.HeadersLive fresh.objects.heap := by
  intro id header owner found allocation
  have slot := Proofs.CppMoveHeaders.header_lookup fresh.objects.heap id header found
  have inside := (List.getElem?_eq_some_iff.mp slot).1
  change id < 2 at inside
  have choices : id=0 ∨ id=1 := by omega
  rcases choices with rfl | rfl
  · change some ⟨none,0,true,limit⟩ = some header at found
    cases Option.some.inj found
    contradiction
  · change some ⟨some 0,0,true,limit⟩ = some header at found
    cases Option.some.inj found
    have same : owner = 0 := Option.some.inj allocation.symm
    subst owner
    decide +kernel

example (ops : List Operation) (ready : ∀ op ∈ ops, op.Valid 4) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret)
      (next : State out moved.2) (nextRho : Nat → Nat),
      script.map Prod.snd = ops ∧ run fresh moved.2 script = .finished (out,results) ∧
      History moved.2 fresh initialState ops out results next ∧ Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out ≤ work fresh+718*ops.length*(Proofs.UfPotential.alpha 4+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget fresh ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget fresh ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget fresh := by
  obtain ⟨script,out,results,next,nextRho,mapped,ran,count,size,history,mathNext,bound,scalar,heap,total⟩ :=
    initialized_resources fresh moved.2 initialState headersLive 4 rfl ops ready
  exact ⟨script,out,results,next,nextRho,mapped,ran,history,mathNext,bound,scalar,heap,total⟩
end UfObjectInitial4Examples
'''

EMPTY_CHECKS = r'''

namespace UfObjectFresh0Examples
open Proofs.CppMoveContext Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppMoveObjectReceiver
open Proofs.UfClassInvariant Proofs.UfRootCall Proofs.UfMergeInvariant
open UfMoveCallExamples UfReceiverLayoutExamples

def freshParents : List Int := List.replicate 0 (-1)
def fresh : Context := {moved.1 with
  objects := {moved.1.objects with heap := {moved.1.objects.heap with allocations :=
    [some ⟨⟨0,freshParents,5,limit,0⟩,fun _ => 7⟩,none]}},
  scalars := {moved.1.scalars with memory := (moved.1.scalars.memory.set 2 ⟨ty,0⟩).set 3 ⟨ty,0⟩}}
def receiver : Receiver fresh moved.2 ty :=
  ⟨⟨4,2,2,true,0,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    ⟨5,3,3,true,0,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    rfl,rfl,1,⟨1,true⟩,⟨some 0,0,true,limit⟩,by decide +kernel,by decide +kernel,rfl⟩

theorem freshCovered : OwnsAll fresh.objects.heap := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside fresh.objects.heap owner tracked found
  change owner < 2 at inside
  have choices : owner=0 ∨ owner=1 := by omega
  rcases choices with rfl | rfl
  · exact ⟨1,⟨some 0,0,true,limit⟩,rfl,rfl⟩
  · have missing : fresh.objects.heap.allocation 1 = none := rfl
    rw [missing] at found
    contradiction

theorem freshAllocations : AllocationsValid fresh.objects.heap ty := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside fresh.objects.heap owner tracked found
  change owner < 2 at inside
  have choices : owner=0 ∨ owner=1 := by omega
  rcases choices with rfl | rfl
  · have slot : fresh.objects.heap.allocation 0 = some ⟨⟨0,freshParents,5,limit,0⟩,fun _ => 7⟩ := rfl
    rw [slot] at found
    cases Option.some.inj found
    decide +kernel
  · have missing : fresh.objects.heap.allocation 1 = none := rfl
    rw [missing] at found
    contradiction

theorem freshContexts : ∀ owner sc, (project fresh ty).frame.state.forest.context owner = some sc → sc ≤ fresh.scope := by
  intro owner sc found
  have forestEq : (project fresh ty).frame.state.forest = (project moved.1 ty).frame.state.forest := rfl
  rw [forestEq] at found
  exact contexts owner sc found

end UfObjectFresh0Examples

namespace UfObjectInitial0Examples
open Proofs.UfObjectInitialAmortized Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppNestedProgram Proofs.UfClassInvariant
open UfMoveCallExamples UfReceiverLayoutExamples UfObjectFresh0Examples

def initialState : State fresh moved.2 :=
  ⟨receiver,⟨0,freshParents,5,limit,0⟩,rfl,(fun _ => 0),initial_valid 0 (by decide +kernel),
    rfl,by decide +kernel,by decide +kernel,unique,freshCovered,freshAllocations,rfl,by decide +kernel,freshContexts⟩
theorem headersLive : Proofs.CppMoveSpace.HeadersLive fresh.objects.heap := by
  intro id header owner found allocation
  have slot := Proofs.CppMoveHeaders.header_lookup fresh.objects.heap id header found
  have inside := (List.getElem?_eq_some_iff.mp slot).1
  change id < 2 at inside
  have choices : id=0 ∨ id=1 := by omega
  rcases choices with rfl | rfl
  · change some ⟨none,0,true,limit⟩ = some header at found
    cases Option.some.inj found
    contradiction
  · change some ⟨some 0,0,true,limit⟩ = some header at found
    cases Option.some.inj found
    have same : owner = 0 := Option.some.inj allocation.symm
    subst owner
    decide +kernel

example (ops : List Operation) (ready : ∀ op ∈ ops, op.Valid 0) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret)
      (next : State out moved.2) (nextRho : Nat → Nat),
      script.map Prod.snd = ops ∧ run fresh moved.2 script = .finished (out,results) ∧
      History moved.2 fresh initialState ops out results next ∧ Proofs.UfHistoricalRank.History next.data.items nextRho ∧
      work out ≤ work fresh+718*ops.length*(Proofs.UfPotential.alpha 0+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget fresh ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget fresh ∧ out.peak ≤ Proofs.UfObjectTotalPeak.budget fresh := by
  obtain ⟨script,out,results,next,nextRho,mapped,ran,count,size,history,mathNext,bound,scalar,heap,total⟩ :=
    initialized_resources fresh moved.2 initialState headersLive 0 rfl ops ready
  exact ⟨script,out,results,next,nextRho,mapped,ran,history,mathNext,bound,scalar,heap,total⟩

example (count : Nat) := initialized_resources fresh moved.2 initialState headersLive 0 rfl
  (List.replicate count .groups) (by
    intro op member
    have same : op = Operation.groups := List.eq_of_mem_replicate member
    subst op
    trivial)
example : ¬(Operation.root 0).Valid 0 := by change ¬(0 < 0); decide +kernel
end UfObjectInitial0Examples
'''

class UfObjectInitialAmortizedTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-initial-amortized-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectInitialAmortized\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                APART_DEFINITIONS + STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_singletons_arbitrary_operations_without_initial_potential(self):
        self.check_lean(SINGLETON_CHECKS)

    def test_empty_state_arbitrary_getters_and_index_rejection(self):
        self.check_lean(EMPTY_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
