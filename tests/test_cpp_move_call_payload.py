"""Actual result vector payload, continued UF validity and empty moved-from headers."""
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
from offline import disable_network

CHECKS = r'''

namespace CallPayloadExamples
open Proofs.CppMoveCallPayload Proofs.CppMoveCallLayout Proofs.CppMoveContext
open Proofs.CppMoveObjectReceiver Proofs.CppMoveReceiverLayout Proofs.CppNestedProgram
open Proofs.CppMoveFrame Proofs.CppVector
open UfMoveCallExamples UfReceiverLayoutExamples UfObjectApartExamples

example : ∃ (fuel rootFuel : Nat) (out finalState : Context) (result : Int) (r : Nat)
    (nextData : Buffer Int) (finalVec : List Int) (rank' : Nat → Nat),
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_unite fuel apart ty
      [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3),.value (.literal ty 1)] =
      .finished (out,.scalar result) ∧
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_root rootFuel out ty
      [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3)] =
      .finished (finalState,.scalar (r : Int)) ∧
    currentBuffer out.objects.heap 1 ⟨some 0,0,true,limit⟩ = some nextData ∧
    Proofs.UfCompression.Compressed nextData.items finalVec 3 r ∧
    Proofs.UfClassInvariant.Valid finalVec 1 rank' ∧ finalState.scalars.memory.map (·.value) = [1,4,1,4] := by
  obtain ⟨rank,validUF⟩ := apartValid
  obtain ⟨prepared,initial,vc,fuel,out,r1,r2,middle,two,final,run,compacted,fw,actual,c1,c2,finalEq,newValid,connected,cost,memory,rest⟩ :=
    Proofs.UfObjectMethods.unite_call apart moved.2 receiver ⟨0,apartParents,5,limit,0⟩ rfl rfl
      rank validUF 3 (by decide +kernel) 1 (by decide +kernel)
      (.literal ty 3) rfl rfl (by decide +kernel) (.literal ty 1) rfl rfl (by decide +kernel)
      (by decide +kernel) unique apartCovered apartAllocations rfl (by decide +kernel) apartContexts
  have different : r1 ≠ r2 := fun equal => notConnected (connected.mp equal)
  have update : Proofs.UfFieldsUnite.updatedMemory apart.scalars.memory 2 2 r1 r2 =
      [⟨ty,1⟩,⟨ty,4⟩,⟨ty,1⟩,⟨ty,4⟩] := by
    simp only [Proofs.UfFieldsUnite.updatedMemory,ite_eq_right different]
    rfl
  change out.scalars.memory = Proofs.UfFieldsUnite.updatedMemory apart.scalars.memory 2 2 r1 r2 at memory
  rw [update] at memory
  have layout := call_layout Proofs.UnionFindCandidateInstance.UnionFind_unite fuel apart out ty
    (Proofs.UfObjectCall.arguments apart moved.2 receiver [(.literal ty 3,3),(.literal ty 1,1)])
    (.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) actual
  have counter : out.scalars.memory[receiver.counter.address]? = some ⟨ty,1⟩ := by rw [memory]; rfl
  have size : out.scalars.memory[receiver.size.address]? = some ⟨ty,4⟩ := by rw [memory]; rfl
  let next := Receiver.update apart out moved.2 ty receiver layout 1 4 counter (by decide +kernel) size (by decide +kernel)

  let program := Proofs.UnionFindCandidateInstance.UnionFind_unite
  let args := Proofs.UfObjectCall.arguments apart moved.2 receiver [(.literal ty 3,3),(.literal ty 1,1)]
  let result : Ret := .scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)
  have afterUnique := call_unique program fuel apart out ty args result actual unique
  have afterCovered := call_ownsAll program fuel apart out ty args result actual apartCovered
  have afterAllocations := call_allocationsValid program fuel apart out ty args result actual
  have afterReadable := call_readable program fuel apart out ty args result actual receiver.header (by decide +kernel)
  have afterContexts := call_contexts program fuel apart out ty args result actual apartCovered apartContexts
  have afterBaseline := Layout.baseline_fits apart out layout (by decide +kernel)

  obtain ⟨buffer,lookup,items⟩ := rest.2.2.2
  have owner : (0 : Nat) = vc.R := fw.owner
  have lookupZero : (project out ty).frame.state.storage.lookup 0 = some buffer := by rw [owner]; exact lookup
  obtain ⟨nextData,currentData,dataItems⟩ := call_payload program fuel apart out ty args result actual
    1 receiver.header (by decide +kernel) (by decide +kernel) unique apartCovered
    ⟨0,apartParents,5,limit,0⟩ rfl final buffer lookupZero items
  obtain ⟨nextRank,nextMath⟩ := newValid
  change Proofs.UfClassInvariant.Valid final (Proofs.UfFieldsUnite.countAfter 2 r1 r2) nextRank at nextMath
  have nextValid : Proofs.UfClassInvariant.Valid nextData.items 1 nextRank := by
    rw [dataItems]
    simpa [Proofs.UfFieldsUnite.countAfter,different] using nextMath
  have finalLength : final.length = 4 := by
    rw [finalEq]
    unfold Proofs.UfUniteCall.uniteVec
    split <;> simp [c2.length,c1.length,apartParents]
  have sizeEq : next.size.value = (nextData.items.length : Int) := by
    change (4 : Int) = _
    norm_num [dataItems,finalLength]
  have inside : 3 < nextData.items.length := by rw [dataItems,finalLength]; decide +kernel
  obtain ⟨prepared2,initial2,vc2,rootFuel,finalState,r,rootFinal,run2,compact2,fw2,actual2,c3,forest3,cost2,memory2,rest2⟩ :=
    Proofs.UfObjectCall.root_call out moved.2 next nextData currentData sizeEq nextRank nextValid.forest nextValid.length
      3 inside (.literal ty 3) rfl rfl rfl afterReadable afterUnique afterCovered afterAllocations rfl afterBaseline afterContexts
  refine ⟨fuel,rootFuel,out,finalState,(Proofs.UfUniteCall.uniteX two r1 r2 : Int),r,nextData,rootFinal,nextRank,
    actual,actual2,currentData,c3,nextValid.compressed c3,?_⟩
  rw [memory2,memory]
  rfl
end CallPayloadExamples
'''

EMPTY_CHECKS = r'''

namespace EmptyCallPayloadExamples
open Proofs.CppMoveContext Proofs.CppMoveCallPayload Proofs.CppMoveCallLayout
open Proofs.CppMoveFrame Proofs.CppMoveHeaders Proofs.CppMoveRestore Proofs.CppVector
open UfMoveCallExamples UfReceiverLayoutExamples ObjectReceiverExamples

example : ∃ (fuel : Nat) (out : Context) (nextData : Buffer Int),
    Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_num_groups fuel moved.1 ty
      [.vectorReference 0,.scalarReference 1,.value (.variable ty 2)] = .finished (out,.scalar 1) ∧
    currentBuffer out.objects.heap 0 ⟨none,0,true,limit⟩ = some nextData ∧
    nextData.items = [] ∧ nextData.owner = 2 ∧ nextData.capacity = 0 ∧
    Proofs.CppMoveHeaders.read out.objects.heap ty.valid 1 = none := by
  obtain ⟨prepared,initial,vc,data,fuel,out,run,compacted,current,fw,actual,cost,memory,rest⟩ :=
    Proofs.UfObjectCall.counter_call moved.1 source empty (by decide +kernel)
      unique covered allocationsValid rfl (by decide +kernel) contexts
  let program := Proofs.UnionFindCandidateInstance.UnionFind_num_groups
  let args := Proofs.UfObjectCall.arguments moved.1 source empty []
  obtain ⟨buffer,lookup,items⟩ := rest.2.2.2
  have owner : data.owner = vc.R := fw.owner
  have lookupOwner : (project out ty).frame.state.storage.lookup data.owner = some buffer := by rw [owner]; exact lookup
  obtain ⟨nextData,currentNext,nextItems⟩ := call_payload program fuel moved.1 out ty args (.scalar 1) actual
    0 empty.header (by decide +kernel) (by decide +kernel) unique covered data current data.items buffer lookupOwner items
  have before : currentBuffer moved.1.objects.heap 0 ⟨none,0,true,limit⟩ =
      some (⟨2,[],0,limit,0⟩ : Buffer Int) := rfl
  have original : data = (⟨2,[],0,limit,0⟩ : Buffer Int) := Option.some.inj (current.symm.trans before)
  have shape : nextData = (⟨out.objects.heap.allocations.length,[],0,limit,0⟩ : Buffer Int) :=
    Option.some.inj currentNext.symm
  have layout := call_layout program fuel moved.1 out ty args (.scalar 1) actual
  obtain ⟨after,restored⟩ := call_objects program fuel moved.1 out ty args (.scalar 1) actual
  have dead := restore_dead moved.1.objects out.objects ty after.frame restored 1 (by decide +kernel)
  have grant : out.objects.heap.grants[1]? = some ⟨⟨⟨1,0,0⟩,0⟩,false⟩ := by rw [layout.grants]; rfl
  refine ⟨fuel,out,nextData,actual,currentNext,?_,?_,?_,?_⟩
  · simpa [original] using nextItems
  · rw [shape,layout.allocations]
    rfl
  · rw [shape]
  · simp [Proofs.CppMoveHeaders.read,grant,dead]
end EmptyCallPayloadExamples
'''


class CallPayloadTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='call-payload-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.CppMoveCallPayload\nimport Proofs.UfObjectMethods\n'
                'import Proofs.UfClassCopyBridge\n' + UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] + APART_DEFINITIONS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_union_payload_and_validity_support_next_root_call(self):
        self.check_lean(CHECKS)

    def test_empty_source_header_payload_and_old_target_grant_stays_dead(self):
        self.check_lean(EMPTY_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
