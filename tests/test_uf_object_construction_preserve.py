"""Constructing another UF preserves live objects and empty-header identity."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from test_uf_object_constructed_state import (
    EMPTY_CHECKS, PREFIX_CHECKS, UF_CHECKS, RECEIVER_CHECKS, FRAME_CHECKS, OBJECT_CHECKS,
    APART_DEFINITIONS, STATE_CHECKS, TRACE_CHECKS, MEANING_CHECKS, ROOT_CHECKS, HEAP_CHECKS, MOVED_CHECKS,
)
from test_uf_object_initial_amortized import EMPTY_CHECKS as INITIAL_EMPTY
from offline import disable_network

PAIR_CHECKS = r'''
namespace UfConstructionPreserveExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.DoublingNested
open Proofs.UfObjectConstructionExport Proofs.UfObjectConstructionContext Proofs.UfObjectConstructionPreserve
open UfMoveCallExamples UfReceiverLayoutExamples UfObjectStateExamples UfObjectConstructedMovedStateExamples
example (n : Nat) (small : n < 2147483648) :
    ∃ (after : NState) (old : Proofs.UfObjectState.State (exported moved.1 after n) moved.2)
      (new : Proofs.UfObjectState.State (exported moved.1 after n) (Proofs.CppConstructorFinish.reference (project moved.1 i32) 2)),
      old.data.items = parents ∧ old.rank = ranks ∧ old.receiver.counter.value = 1 ∧ old.receiver.size.value = 4 ∧
      new.data.items = List.replicate n (-1) := by
  have wf := Proofs.CppMoveFrame.materialize_ready moved.1.objects i32 (by decide +kernel) allocationsValid
  have lengths : (project moved.1 i32).frame.rootWritable.length = (project moved.1 i32).frame.state.forest.objects.length := by
    simp [project,Proofs.CppMoveFrame.materialize]
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,valid⟩ := sized_export moved.1 modelHeap
    wf model lengths contexts (by decide +kernel) unique covered UfObjectHeapPeakExamples.headerLive allocationsValid
    (.literal i32 (n : Int)) n small rfl rfl (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])
  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct1 8
    (project moved.1 i32) after [.value (.literal i32 (n : Int))] (Proofs.UfConstructionExport.vectorField true)
    (.integer i32) (Proofs.UfConstructionExport.fields true) (Proofs.CppConstructorFinish.reference (project moved.1 i32) 2) rfl ran
  obtain ⟨old,items,rank,count,size⟩ := old_state moved.1 after n small moved.2 start UfObjectHeapPeakExamples.headerLive
    (by decide +kernel) initialized layout
  obtain ⟨new,newItems,live⟩ := Proofs.UfObjectConstructedState.initialized_state moved.1 after n small initialized layout
    unique covered UfObjectHeapPeakExamples.headerLive allocationsValid (by decide +kernel) contexts
  exact ⟨after,old,new,items,rank,count,size,newItems⟩

example (n : Nat) (small : n < 2147483648) :=
  construct_sized_pair moved.1 modelHeap moved.2 start model UfObjectHeapPeakExamples.headerLive (by decide +kernel)
    (.literal i32 (n : Int)) n small rfl rfl (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])
example := construct_default_pair moved.1 modelHeap moved.2 start model UfObjectHeapPeakExamples.headerLive (by decide +kernel)
end UfConstructionPreserveExamples

'''

EMPTY_HEADER_CHECKS = r'''namespace UfEmptyHeaderPreserveExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.DoublingNested Proofs.CppMoveObjectReceiver
open Proofs.UfObjectConstructionExport Proofs.UfObjectConstructionContext Proofs.UfObjectConstructionPreserve
open UfMoveCallExamples UfReceiverLayoutExamples UfObjectFresh0Examples

def vacant : Context := {fresh with scalars := {fresh.scalars with memory := [⟨i32,0⟩,⟨i32,0⟩,⟨i32,0⟩,⟨i32,0⟩]}}
def object : Proofs.CppConstructorFinish.ObjectRef := ⟨0,[1,2]⟩
def receiver : Receiver vacant object i32 :=
  ⟨⟨1,0,0,true,0,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
   ⟨2,1,1,true,0,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
   rfl,rfl,0,⟨0,true⟩,⟨none,0,true,limit⟩,by decide +kernel,by decide +kernel,rfl⟩
def initial : Proofs.UfObjectState.State vacant object :=
  ⟨receiver,⟨2,[],0,limit,0⟩,rfl,(fun _ => 0),Proofs.UfClassInvariant.initial_valid 0 (by decide +kernel),rfl,
    by decide +kernel,by decide +kernel,unique,freshCovered,freshAllocations,rfl,by decide +kernel,freshContexts⟩
theorem emptyModel : Proofs.CppRootModel.HeapModels (project vacant i32).frame.state UfObjectConstructedMovedStateExamples.modelHeap := by
  intro owner view found
  simp [UfObjectConstructedMovedStateExamples.modelHeap] at found

example (n : Nat) (small : n < 2147483648) :
    ∃ (after : NState) (old : Proofs.UfObjectState.State (exported vacant after n) object)
      (new : Proofs.UfObjectState.State (exported vacant after n) (Proofs.CppConstructorFinish.reference (project vacant i32) 2)),
      old.data.items = [] ∧ old.receiver.counter.value = 0 ∧ old.receiver.size.value = 0 ∧
      new.data.items = List.replicate n (-1) ∧ old.data.owner = 3 := by
  have wf := Proofs.CppMoveFrame.materialize_ready vacant.objects i32 (by decide +kernel) freshAllocations
  have lengths : (project vacant i32).frame.rootWritable.length = (project vacant i32).frame.state.forest.objects.length := by
    simp [project,Proofs.CppMoveFrame.materialize]
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,valid⟩ := sized_export vacant UfObjectConstructedMovedStateExamples.modelHeap
    wf emptyModel lengths freshContexts (by decide +kernel) unique freshCovered UfObjectInitial0Examples.headersLive freshAllocations
    (.literal i32 (n : Int)) n small rfl rfl (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])
  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct1 8
    (project vacant i32) after [.value (.literal i32 (n : Int))] (Proofs.UfConstructionExport.vectorField true)
    (.integer i32) (Proofs.UfConstructionExport.fields true) (Proofs.CppConstructorFinish.reference (project vacant i32) 2) rfl ran
  obtain ⟨old,items,rank,count,size⟩ := old_state vacant after n small object initial UfObjectInitial0Examples.headersLive
    (by decide +kernel) initialized layout
  obtain ⟨new,newItems,live⟩ := Proofs.UfObjectConstructedState.initialized_state vacant after n small initialized layout
    unique freshCovered UfObjectInitial0Examples.headersLive freshAllocations (by decide +kernel) freshContexts
  refine ⟨after,old,new,items,count,size,newItems,?_⟩
  let receiver := old.receiver
  have viewSlot : receiver.viewSlot = 0 := by
    have located := receiver.located
    change Proofs.CppMoveContext.vectorView (exported vacant after n) 0 = some receiver.viewSlot at located
    unfold Proofs.CppMoveContext.vectorView at located
    rw [old_slot vacant after n 0 layout (by decide +kernel)] at located
    change some 0 = some receiver.viewSlot at located
    exact (Option.some.inj located).symm
  have resolved := receiver.resolved
  rw [viewSlot] at resolved
  have kept := old_resolve vacant after n 0 ⟨0,true⟩ ⟨none,0,true,limit⟩ (by decide +kernel)
  have equal := Prod.mk.inj (Option.some.inj (kept.symm.trans resolved))
  have current := old.current
  change Proofs.CppMoveFrame.currentBuffer (exported vacant after n).objects.heap receiver.view.header receiver.header = some old.data at current
  rw [← equal.1,← equal.2] at current
  have allocationLength : (exported vacant after n).objects.heap.allocations.length = 3 := by
    simp [exported,exportedHeap,Proofs.CppMoveAppendOwned.appended,vacant,fresh]
  have bufferEq : (⟨3,[],0,limit,0⟩ : Proofs.CppVector.Buffer Int) = old.data := by
    simpa only [Proofs.CppMoveFrame.currentBuffer,Option.some.injEq,allocationLength,Nat.add_zero] using current
  rw [← bufferEq]

example (n : Nat) (small : n < 2147483648) :=
  construct_sized_pair vacant UfObjectConstructedMovedStateExamples.modelHeap object initial emptyModel
    UfObjectInitial0Examples.headersLive (by decide +kernel) (.literal i32 (n : Int)) n small rfl rfl
    (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])
example := construct_default_pair vacant UfObjectConstructedMovedStateExamples.modelHeap object initial emptyModel
  UfObjectInitial0Examples.headersLive (by decide +kernel)
end UfEmptyHeaderPreserveExamples
'''

class UfObjectConstructionPreserveTests(unittest.TestCase):
    def check_lean(self, checks):
        fixtures = (EMPTY_CHECKS + PREFIX_CHECKS + UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
            OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] + APART_DEFINITIONS +
            STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS + MOVED_CHECKS + INITIAL_EMPTY)
        with tempfile.TemporaryDirectory(prefix='uf-construction-preserve-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectConstructionPreserve\nimport Proofs.UfClassCopyBridge\n' + fixtures + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_existing_compressed_forest_and_new_object_remain_normal_for_both_constructors(self):
        self.check_lean(PAIR_CHECKS)

    def test_empty_header_keeps_data_and_fields_while_owner_changes_from_2_to_3(self):
        self.check_lean(EMPTY_HEADER_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
