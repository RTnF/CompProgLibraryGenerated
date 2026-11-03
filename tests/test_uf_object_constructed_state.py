"""Actual UF constructors produce normal Context states and amortized method traces."""
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from test_uf_object_construction_export import EMPTY_CHECKS, PREFIX_CHECKS
from test_uf_object_query_amortized import (
    UF_CHECKS, RECEIVER_CHECKS, FRAME_CHECKS, OBJECT_CHECKS, APART_DEFINITIONS,
    STATE_CHECKS, TRACE_CHECKS, MEANING_CHECKS, ROOT_CHECKS, HEAP_CHECKS,
)
from offline import disable_network

TRACE_CHECKS_NEW = r'''
namespace UfObjectConstructedStateExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.DoublingNested
open Proofs.UfObjectConstructionExport Proofs.UfObjectConstructedState Proofs.UfObjectConstructionContext
open UfObjectConstructionExportExamples
example (n : Nat) (small : n < 2147483648) :
    ∃ (after : NState) (state : Proofs.UfObjectState.State (exported caller after n)
        (Proofs.CppConstructorFinish.reference (project caller i32) 2)),
      state.data.items = List.replicate n (-1) ∧ Proofs.CppMoveSpace.HeadersLive (exported caller after n).objects.heap := by
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,valid⟩ := sized_export caller heap
    (by decide +kernel) models rfl strict (by decide +kernel) unique covered live allocations
    (.literal i32 (n : Int)) n small rfl rfl
    (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])
  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct1 8
    (project caller i32) after [.value (.literal i32 (n : Int))] (Proofs.UfConstructionExport.vectorField true)
    (.integer i32) (Proofs.UfConstructionExport.fields true) (Proofs.CppConstructorFinish.reference (project caller i32) 2) rfl ran
  obtain ⟨state,items,live⟩ := initialized_state caller after n small initialized layout unique covered live allocations
    (by decide +kernel) strict
  exact ⟨after,state,items,live⟩

example (n : Nat) (small : n < 2147483648) (ops : List Proofs.UfObjectTrace.Operation)
    (ready : ∀ op ∈ ops, op.Valid n) :
    ∃ (after : NState) (script : List (Nat × Proofs.UfObjectTrace.Operation))
      (out : Context) (results : List Ret),
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 (project caller i32)
        [.value (.literal i32 (n : Int))] (Proofs.UfConstructionExport.vectorField true) (.integer i32)
        (Proofs.UfConstructionExport.fields true) =
          .finished (after,Proofs.CppConstructorFinish.reference (project caller i32) 2) ∧
      script.map Prod.snd = ops ∧
      Proofs.UfObjectTrace.run (exported caller after n) (Proofs.CppConstructorFinish.reference (project caller i32) 2) script =
        .finished (out,results) ∧
      work out ≤ work caller+1+n+30+718*ops.length*(Proofs.UfPotential.alpha n+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget (exported caller after n) ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget (exported caller after n) ∧
      out.peak ≤ Proofs.UfObjectTotalPeak.budget (exported caller after n) := by
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,valid⟩ := sized_export caller heap
    (by decide +kernel) models rfl strict (by decide +kernel) unique covered live allocations
    (.literal i32 (n : Int)) n small rfl rfl
    (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])
  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct1 8
    (project caller i32) after [.value (.literal i32 (n : Int))] (Proofs.UfConstructionExport.vectorField true)
    (.integer i32) (Proofs.UfConstructionExport.fields true) (Proofs.CppConstructorFinish.reference (project caller i32) 2) rfl ran
  obtain ⟨state,items,liveAfter⟩ := initialized_state caller after n small initialized layout unique covered live allocations
    (by decide +kernel) strict
  obtain ⟨script,out,results,next,nextRho,mapped,called,count,size,history,mathNext,bound,scalar,heapBound,total⟩ :=
    Proofs.UfObjectInitialAmortized.initialized_resources (exported caller after n) _ state liveAfter n items ops ready
  obtain ⟨other,otherRun,strong,cost⟩ := Proofs.UfConstructionWork.construct_sized_work (project caller i32) heap
    (by decide +kernel) models rfl strict (by decide +kernel) (.literal i32 (n : Int)) n small rfl rfl
    (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])
  have same : other = after := congrArg Prod.fst (Proofs.CppLoop.Outcome.finished.inj (otherRun.symm.trans ran))
  subst other
  change after.work ≤ work caller+1+n+30 at cost
  change work out ≤ after.work+718*ops.length*(Proofs.UfPotential.alpha n+1) at bound
  exact ⟨after,script,out,results,ran,mapped,called,bound.trans (Nat.add_le_add_right cost _),scalar,heapBound,total⟩

example (count : Nat) :
    ∃ (after : NState) (script : List (Nat × Proofs.UfObjectTrace.Operation))
      (out : Context) (results : List Ret),
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 (project caller i32) []
        (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
          .finished (after,Proofs.CppConstructorFinish.reference (project caller i32) 2) ∧
      script.map Prod.snd = List.replicate count .groups ∧
      Proofs.UfObjectTrace.run (exported caller after 0) (Proofs.CppConstructorFinish.reference (project caller i32) 2) script =
        .finished (out,results) ∧
      work out ≤ work caller+12+718*count*(Proofs.UfPotential.alpha 0+1) ∧
      out.scalars.peak ≤ Proofs.UfObjectUniformScalarPeak.budget (exported caller after 0) ∧
      out.objects.heap.peak ≤ Proofs.UfObjectHeapPeak.budget (exported caller after 0) ∧
      out.peak ≤ Proofs.UfObjectTotalPeak.budget (exported caller after 0) := by
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,valid⟩ :=
    default_export caller heap (by decide +kernel) models rfl strict (by decide +kernel) unique covered live allocations
  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct0 8
    (project caller i32) after [] (Proofs.UfConstructionExport.vectorField false)
    (.integer i32) (Proofs.UfConstructionExport.fields false) (Proofs.CppConstructorFinish.reference (project caller i32) 2) rfl ran
  obtain ⟨state,items,liveAfter⟩ := initialized_state caller after 0 (by decide +kernel) initialized layout unique covered live allocations
    (by decide +kernel) strict
  have ready : ∀ op ∈ List.replicate count Proofs.UfObjectTrace.Operation.groups, op.Valid 0 := by
    intro op member
    have same : op = Proofs.UfObjectTrace.Operation.groups := List.eq_of_mem_replicate member
    subst op
    trivial
  obtain ⟨script,out,results,next,nextRho,mapped,called,resultCount,size,history,mathNext,bound,scalar,heapBound,total⟩ :=
    Proofs.UfObjectInitialAmortized.initialized_resources (exported caller after 0) _ state liveAfter 0 items _ ready
  obtain ⟨other,otherRun,strong,cost⟩ := Proofs.UfConstructionWork.construct_default_work (project caller i32) heap
    (by decide +kernel) models rfl strict (by decide +kernel)
  have same : other = after := congrArg Prod.fst (Proofs.CppLoop.Outcome.finished.inj (otherRun.symm.trans ran))
  subst other
  change after.work ≤ work caller+12 at cost
  simp only [List.length_replicate] at bound
  change work out ≤ after.work+718*count*(Proofs.UfPotential.alpha 0+1) at bound
  exact ⟨after,script,out,results,ran,mapped,called,bound.trans (Nat.add_le_add_right cost _),scalar,heapBound,total⟩

example (n : Nat) (small : n < 2147483648) (ops : List Proofs.UfObjectTrace.Operation)
    (ready : ∀ op ∈ ops, op.Valid n) :=
  construct_sized_resources caller heap (by decide +kernel) models rfl strict (by decide +kernel)
    unique covered live allocations (.literal i32 (n : Int)) n small rfl rfl
    (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small]) ops ready

example (ops : List Proofs.UfObjectTrace.Operation) (ready : ∀ op ∈ ops, op.Valid 0) :=
  construct_default_resources caller heap (by decide +kernel) models rfl strict (by decide +kernel)
    unique covered live allocations ops ready
end UfObjectConstructedStateExamples
'''

MOVED_CHECKS = r'''
namespace UfObjectConstructedMovedStateExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.DoublingNested
open Proofs.UfObjectConstructionExport Proofs.UfObjectConstructedState Proofs.UfObjectConstructionContext
open UfMoveCallExamples UfReceiverLayoutExamples

def modelHeap : Proofs.CppRootModel.Heap := fun _ => none
theorem model : Proofs.CppRootModel.HeapModels (project moved.1 i32).frame.state modelHeap := by
  intro owner view found
  simp [modelHeap] at found

example (n : Nat) (small : n < 2147483648) :
    ∃ (after : NState) (state : Proofs.UfObjectState.State (exported moved.1 after n)
        (Proofs.CppConstructorFinish.reference (project moved.1 i32) 2)),
      state.data.items = List.replicate n (-1) ∧
      Proofs.CppMoveSpace.HeadersLive (exported moved.1 after n).objects.heap ∧
      Proofs.CppMoveHeaders.read (exported moved.1 after n).objects.heap i32.valid 0 = some 2 ∧
      Proofs.CppMoveHeaders.read (exported moved.1 after n).objects.heap i32.valid 1 = none := by
  have wellFormed := Proofs.CppMoveFrame.materialize_ready moved.1.objects i32 (by decide +kernel) allocationsValid
  have lengths : (project moved.1 i32).frame.rootWritable.length = (project moved.1 i32).frame.state.forest.objects.length := by
    simp [project,Proofs.CppMoveFrame.materialize]
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,valid⟩ := sized_export moved.1 modelHeap
    wellFormed model lengths contexts (by decide +kernel) unique covered UfObjectHeapPeakExamples.headerLive allocationsValid
    (.literal i32 (n : Int)) n small rfl rfl
    (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])
  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct1 8
    (project moved.1 i32) after [.value (.literal i32 (n : Int))] (Proofs.UfConstructionExport.vectorField true)
    (.integer i32) (Proofs.UfConstructionExport.fields true) (Proofs.CppConstructorFinish.reference (project moved.1 i32) 2) rfl ran
  obtain ⟨state,items,liveAfter⟩ := initialized_state moved.1 after n small initialized layout unique covered
    UfObjectHeapPeakExamples.headerLive allocationsValid (by decide +kernel) contexts
  have first := Proofs.UfObjectConstructionExport.old_read moved.1 after n 0
    ⟨⟨⟨0,0,3⟩,7⟩,false⟩ (by decide +kernel) (by decide +kernel)
  have second := Proofs.UfObjectConstructionExport.old_read moved.1 after n 1
    ⟨⟨⟨1,0,0⟩,0⟩,false⟩ (by decide +kernel) (by decide +kernel)
  refine ⟨after,state,items,liveAfter,?_,?_⟩
  · change Proofs.CppMoveHeaders.read (exportedHeap moved.1 after n) i32.valid 0 = some 2
    rw [first]
    decide +kernel
  · change Proofs.CppMoveHeaders.read (exportedHeap moved.1 after n) i32.valid 1 = none
    rw [second]
    decide +kernel

example (n : Nat) (small : n < 2147483648) (ops : List Proofs.UfObjectTrace.Operation)
    (ready : ∀ op ∈ ops, op.Valid n) :=
  construct_sized_resources moved.1 modelHeap
    (Proofs.CppMoveFrame.materialize_ready moved.1.objects i32 (by decide +kernel) allocationsValid)
    model (by simp [project,Proofs.CppMoveFrame.materialize]) contexts (by decide +kernel)
    unique covered UfObjectHeapPeakExamples.headerLive allocationsValid (.literal i32 (n : Int)) n small rfl rfl
    (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small]) ops ready
end UfObjectConstructedMovedStateExamples
'''

class UfObjectConstructedStateTests(unittest.TestCase):
    def check_lean(self, checks):
        fixtures = (EMPTY_CHECKS + PREFIX_CHECKS + UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
            OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
            APART_DEFINITIONS + STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS)
        with tempfile.TemporaryDirectory(prefix='uf-object-constructed-state-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectConstructedState\nimport Proofs.UfClassCopyBridge\n' + fixtures + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_sized_default_constructors_and_arbitrary_traces_include_construction_work(self):
        self.check_lean(TRACE_CHECKS_NEW)

    def test_existing_heap_with_live_and_stale_grants_keeps_state_and_read_results(self):
        self.check_lean(MOVED_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
