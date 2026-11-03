"""Actual constructors create independent UF states and interleaved call histories."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from test_uf_object_construction_preserve import (
    EMPTY_CHECKS, PREFIX_CHECKS, UF_CHECKS, RECEIVER_CHECKS, FRAME_CHECKS, OBJECT_CHECKS,
    APART_DEFINITIONS, STATE_CHECKS, TRACE_CHECKS, MEANING_CHECKS, ROOT_CHECKS, HEAP_CHECKS, MOVED_CHECKS, EMPTY_HEADER_CHECKS,
)
from test_uf_object_initial_amortized import EMPTY_CHECKS as INITIAL_EMPTY
from offline import disable_network

CHECKS = r'''namespace UfObjectConstructedPairExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.DoublingNested
open Proofs.UfObjectPair Proofs.UfObjectPairTrace Proofs.UfObjectConstructionContext Proofs.UfObjectConstructedPair
open UfMoveCallExamples UfObjectStateExamples UfObjectConstructedMovedStateExamples

example (n : Nat) (small : n < 2147483648) (actions : List Action)
    (ready : ∀ action ∈ actions, action.Valid 4 n) :
    ∃ (after : NState) (initial : Pair (exported moved.1 after n) moved.2 (reference (project moved.1 i32) 2))
      (script : List (Nat × Action)) (out : Context) (results : List Ret)
      (final : Pair out moved.2 (reference (project moved.1 i32) 2)),
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 (project moved.1 i32) [.value (.literal i32 (n : Int))]
        (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
          .finished (after,reference (project moved.1 i32) 2) ∧
      initial.left.data.items = parents ∧ initial.right.data.items = List.replicate n (-1) ∧
      script.map Prod.snd = actions ∧
      run (exported moved.1 after n) moved.2 (reference (project moved.1 i32) 2) script = .finished (out,results) ∧
      results.length = actions.length ∧ History moved.2 (reference (project moved.1 i32) 2)
        (exported moved.1 after n) initial actions out results final := by
  obtain ⟨after,initial,constructed,oldItems,oldRank,oldCount,oldSize,newItems,live⟩ :=
    construct_sized moved.1 modelHeap moved.2 start model UfObjectHeapPeakExamples.headerLive (by decide +kernel)
      (.literal i32 (n : Int)) n small rfl rfl (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])
  have readyPair : ∀ action ∈ actions, action.Valid initial.left.data.items.length initial.right.data.items.length := by
    intro action member
    rw [oldItems,newItems,List.length_replicate]
    exact ready action member
  obtain ⟨script,out,results,final,mapped,ran,count,leftSize,rightSize,history⟩ :=
    execute (exported moved.1 after n) moved.2 (reference (project moved.1 i32) 2) initial actions readyPair
  exact ⟨after,initial,script,out,results,final,constructed,oldItems,newItems,mapped,ran,count,history⟩

example := construct_default moved.1 modelHeap moved.2 start model UfObjectHeapPeakExamples.headerLive (by decide +kernel)

example (n : Nat) (small : n < 2147483648) (actions : List Action)
    (ready : ∀ action ∈ actions, action.Valid 4 n) :=
  construct_sized_trace moved.1 modelHeap moved.2 start model UfObjectHeapPeakExamples.headerLive (by decide +kernel)
    (.literal i32 (n : Int)) n small rfl rfl (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small]) actions ready
example (actions : List Action) (ready : ∀ action ∈ actions, action.Valid 4 0) :=
  construct_default_trace moved.1 modelHeap moved.2 start model UfObjectHeapPeakExamples.headerLive (by decide +kernel) actions ready
end UfObjectConstructedPairExamples

'''

EMPTY_PAIR = r'''namespace UfObjectConstructedEmptyPairExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.DoublingNested
open Proofs.UfObjectConstructedPair UfEmptyHeaderPreserveExamples
example (n : Nat) (small : n < 2147483648) :=
  construct_sized vacant UfObjectConstructedMovedStateExamples.modelHeap object initial emptyModel
    UfObjectInitial0Examples.headersLive (by decide +kernel) (.literal i32 (n : Int)) n small rfl rfl
    (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])
example := construct_default vacant UfObjectConstructedMovedStateExamples.modelHeap object initial emptyModel
  UfObjectInitial0Examples.headersLive (by decide +kernel)
example (actions : List Proofs.UfObjectPairTrace.Action) (ready : ∀ action ∈ actions, action.Valid 0 0) :=
  construct_default_trace vacant UfObjectConstructedMovedStateExamples.modelHeap object initial emptyModel
    UfObjectInitial0Examples.headersLive (by decide +kernel) actions ready
end UfObjectConstructedEmptyPairExamples
'''

class UfObjectConstructedPairTests(unittest.TestCase):
    def check_lean(self, checks):
        fixtures = (EMPTY_CHECKS + PREFIX_CHECKS + UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
            OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] + APART_DEFINITIONS +
            STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS + MOVED_CHECKS + INITIAL_EMPTY + EMPTY_HEADER_CHECKS)
        with tempfile.TemporaryDirectory(prefix='uf-object-constructed-pair-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectConstructedPair\nimport Proofs.UfObjectConstructionPreserve\nimport Proofs.UfClassCopyBridge\n' + fixtures + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_both_constructors_and_arbitrary_interleaving_with_existing_moved_uf(self):
        self.check_lean(CHECKS)

    def test_existing_empty_header_gets_independent_owner_and_fields_for_both_constructors(self):
        self.check_lean(EMPTY_PAIR)

if __name__ == '__main__':
    disable_network()
    unittest.main()
