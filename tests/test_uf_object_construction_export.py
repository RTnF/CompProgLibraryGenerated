"""Actual sized/default UF construction exports its buffer and scalar layout."""
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from offline import disable_network

EMPTY_CHECKS = r'''
namespace UfObjectConstructionExportExamples
open Proofs.UfObjectConstructionExport Proofs.CppMoveContext Proofs.CppNestedProgram
open Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppMoveSpace Proofs.DoublingNested

def caller : Context := ⟨⟨⟨[],[],[],0,0,0⟩,[]⟩,⟨[],[],0,0,0⟩,[],0,0⟩
def heap : Proofs.CppRootModel.Heap := fun _ => none

theorem models : Proofs.CppRootModel.HeapModels (project caller i32).frame.state heap := by
  intro owner view found
  simp [heap] at found

theorem strict : ∀ owner sc, (project caller i32).frame.state.forest.context owner = some sc →
    sc ≤ (project caller i32).scope := by
  intro owner sc found
  have missing : (project caller i32).frame.state.forest.lookup owner = none := by
    simp [caller,project,materialize,entries,Proofs.CppVectorOwnership.Forest.lookup]
  have absent := Proofs.CppMoveRestore.context_of_none (project caller i32).frame.state.forest owner missing
  rw [absent] at found
  contradiction

theorem unique : Unique caller.objects.heap := by
  intro i j hi hj owner found rest first second
  simp [caller,Proofs.CppMoveHeaders.Heap.header] at found

theorem covered : OwnsAll caller.objects.heap := by
  intro owner tracked found
  simp [caller,Proofs.CppMoveHeaders.Heap.allocation] at found

theorem live : HeadersLive caller.objects.heap := by
  intro id header owner found allocation
  simp [caller,Proofs.CppMoveHeaders.Heap.header] at found

theorem allocations : AllocationsValid caller.objects.heap i32 := by
  intro owner tracked found
  simp [caller,Proofs.CppMoveHeaders.Heap.allocation] at found

example (n : Nat) (small : n < 2147483648) :
    ∃ after : NState,
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 (project caller i32)
        [.value (.literal i32 (n : Int))] (Proofs.UfConstructionExport.vectorField true) (.integer i32)
        (Proofs.UfConstructionExport.fields true) =
        .finished (after,Proofs.CppConstructorFinish.reference (project caller i32) 2) ∧
      Proofs.CppConstructorLayout.Layout (project caller i32) after (Proofs.CppConstructorFinish.reference (project caller i32) 2) ∧
      after.slots = (project caller i32).slots++[.vector 0]++Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 2 ∧
      after.scalars.bindings.length = caller.scalars.bindings.length+2 ∧
      after.scalars.memory = [⟨i32,(n : Int)⟩,⟨i32,(n : Int)⟩] ∧
      currentBuffer (exportedHeap caller after n) 0 ⟨some 0,0,true,Proofs.CppVectorBindings.sizeLimit i32⟩ = some (payload n) ∧
      Unique (exportedHeap caller after n) ∧ OwnsAll (exportedHeap caller after n) ∧
      HeadersLive (exportedHeap caller after n) ∧ AllocationsValid (exportedHeap caller after n) i32 := by
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,valid⟩ := sized_export caller heap
    (by decide +kernel) models rfl strict (by decide +kernel) unique covered live allocations
    (.literal i32 (n : Int)) n small rfl rfl
    (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])

  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct1 8
    (project caller i32) after [.value (.literal i32 (n : Int))] (Proofs.UfConstructionExport.vectorField true)
    (.integer i32) (Proofs.UfConstructionExport.fields true) (Proofs.CppConstructorFinish.reference (project caller i32) 2) rfl ran
  have fullLayout := layout
  obtain ⟨oldCells,values,oldLength,oldTypes,memory,bindings,slots,scope,base,objectEq⟩ := layout
  have countSame := congrArg (fun object : Proofs.CppConstructorFinish.ObjectRef => object.scalarSlots.length) objectEq
  have fieldCount : values.length = 2 := by simpa [Proofs.CppConstructorFinish.reference] using countSame.symm
  have slotsEq : after.slots = (project caller i32).slots++[.vector 0]++Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 2 := by
    rw [fieldCount] at slots
    change after.slots = (project caller i32).slots++[.vector 0]++Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 2 at slots
    exact slots
  have bindingsCount : after.scalars.bindings.length = caller.scalars.bindings.length+2 := by
    have counts := congrArg List.length bindings
    simp only [List.length_append,Proofs.CppConstructorPeak.scalarBindings_length,fieldCount] at counts
    change after.scalars.bindings.length = caller.scalars.bindings.length+2 at counts
    exact counts
  exact ⟨after,ran,fullLayout,slotsEq,bindingsCount,initialized.2.1,newBuffer,owned,allOwned,headers,valid⟩

example := default_export caller heap (by decide +kernel) models rfl strict (by decide +kernel) unique covered live allocations
end UfObjectConstructionExportExamples
'''

PREFIX_CHECKS = r'''
namespace UfObjectConstructionNonemptyExportExamples
open Proofs.UfObjectConstructionExport Proofs.CppMoveContext Proofs.CppNestedProgram
open Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppMoveSpace Proofs.DoublingNested

def caller : Context := ⟨⟨⟨[],[],[],0,0,0⟩,[]⟩,⟨[⟨i32,7⟩],[⟨0,true⟩],0,0,0⟩,[.scalar 0],0,0⟩
def heap : Proofs.CppRootModel.Heap := fun _ => none

theorem models : Proofs.CppRootModel.HeapModels (project caller i32).frame.state heap := by
  intro owner view found
  simp [heap] at found

theorem strict : ∀ owner sc, (project caller i32).frame.state.forest.context owner = some sc →
    sc ≤ (project caller i32).scope := by
  intro owner sc found
  have missing : (project caller i32).frame.state.forest.lookup owner = none := by
    simp [caller,project,materialize,entries,Proofs.CppVectorOwnership.Forest.lookup]
  have absent := Proofs.CppMoveRestore.context_of_none (project caller i32).frame.state.forest owner missing
  rw [absent] at found
  contradiction

theorem unique : Unique caller.objects.heap := by
  intro i j hi hj owner found rest first second
  simp [caller,Proofs.CppMoveHeaders.Heap.header] at found

theorem covered : OwnsAll caller.objects.heap := by
  intro owner tracked found
  simp [caller,Proofs.CppMoveHeaders.Heap.allocation] at found

theorem live : HeadersLive caller.objects.heap := by
  intro id header owner found allocation
  simp [caller,Proofs.CppMoveHeaders.Heap.header] at found

theorem allocations : AllocationsValid caller.objects.heap i32 := by
  intro owner tracked found
  simp [caller,Proofs.CppMoveHeaders.Heap.allocation] at found

example (n : Nat) (small : n < 2147483648) :
    ∃ after : NState,
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 (project caller i32)
        [.value (.literal i32 (n : Int))] (Proofs.UfConstructionExport.vectorField true) (.integer i32)
        (Proofs.UfConstructionExport.fields true) =
        .finished (after,Proofs.CppConstructorFinish.reference (project caller i32) 2) ∧
      Proofs.CppConstructorLayout.Layout (project caller i32) after (Proofs.CppConstructorFinish.reference (project caller i32) 2) ∧
      after.slots = (project caller i32).slots++[.vector 0]++Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 2 ∧
      after.scalars.bindings.length = caller.scalars.bindings.length+2 ∧
      after.scalars.memory = [⟨i32,7⟩,⟨i32,(n : Int)⟩,⟨i32,(n : Int)⟩] ∧
      currentBuffer (exportedHeap caller after n) 0 ⟨some 0,0,true,Proofs.CppVectorBindings.sizeLimit i32⟩ = some (payload n) ∧
      Unique (exportedHeap caller after n) ∧ OwnsAll (exportedHeap caller after n) ∧
      HeadersLive (exportedHeap caller after n) ∧ AllocationsValid (exportedHeap caller after n) i32 := by
  obtain ⟨after,ran,initialized,extension,reads,buffer,newBuffer,owned,allOwned,headers,valid⟩ := sized_export caller heap
    (by decide +kernel) models rfl strict (by decide +kernel) unique covered live allocations
    (.literal i32 (n : Int)) n small rfl rfl
    (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])

  have layout := Proofs.CppConstructorLayout.construct_layout Proofs.UnionFindConstructionInstance.UnionFind_construct1 8
    (project caller i32) after [.value (.literal i32 (n : Int))] (Proofs.UfConstructionExport.vectorField true)
    (.integer i32) (Proofs.UfConstructionExport.fields true) (Proofs.CppConstructorFinish.reference (project caller i32) 2) rfl ran
  have fullLayout := layout
  obtain ⟨oldCells,values,oldLength,oldTypes,memory,bindings,slots,scope,base,objectEq⟩ := layout
  have countSame := congrArg (fun object : Proofs.CppConstructorFinish.ObjectRef => object.scalarSlots.length) objectEq
  have fieldCount : values.length = 2 := by simpa [Proofs.CppConstructorFinish.reference] using countSame.symm
  have slotsEq : after.slots = (project caller i32).slots++[.vector 0]++Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 2 := by
    rw [fieldCount] at slots
    change after.slots = (project caller i32).slots++[.vector 0]++Proofs.CppConstructorFinish.scalarLocations caller.scalars.bindings.length 2 at slots
    exact slots
  have bindingsCount : after.scalars.bindings.length = caller.scalars.bindings.length+2 := by
    have counts := congrArg List.length bindings
    simp only [List.length_append,Proofs.CppConstructorPeak.scalarBindings_length,fieldCount] at counts
    change after.scalars.bindings.length = caller.scalars.bindings.length+2 at counts
    exact counts
  exact ⟨after,ran,fullLayout,slotsEq,bindingsCount,initialized.2.1,newBuffer,owned,allOwned,headers,valid⟩

example := default_export caller heap (by decide +kernel) models rfl strict (by decide +kernel) unique covered live allocations
end UfObjectConstructionNonemptyExportExamples
'''

class UfObjectConstructionExportTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-object-construction-export-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectConstructionExport\nimport Proofs.CppConstructorLayout\nimport Proofs.CppMoveRestore\n' + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_empty_caller_all_sized_constructors_and_default_keep_layout_and_owned_heap(self):
        self.check_lean(EMPTY_CHECKS)

    def test_existing_scalar_prefix_all_sized_constructors_and_default_keep_layout(self):
        self.check_lean(PREFIX_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
