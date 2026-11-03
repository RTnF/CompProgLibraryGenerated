"""Getter preserves all buffer contents and every coexisting normal UF state."""
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
    APART_DEFINITIONS, STATE_CHECKS, TRACE_CHECKS, MEANING_CHECKS, ROOT_CHECKS, HEAP_CHECKS, MOVED_CHECKS, PAIR_CHECKS, EMPTY_HEADER_CHECKS,
)
from test_uf_object_initial_amortized import EMPTY_CHECKS as INITIAL_EMPTY
from offline import disable_network

PAIR_GETTERS = r'''
namespace UfGetterPairExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.DoublingNested Proofs.UfObjectTrace
open Proofs.UfObjectConstructionExport Proofs.UfObjectConstructionContext Proofs.UfObjectGetterFrame
open UfMoveCallExamples UfObjectStateExamples UfObjectConstructedMovedStateExamples

example (n : Nat) (small : n < 2147483648) :
    ∃ (after : NState) (firstFuel secondFuel : Nat) (middle out : Context)
      (old : Proofs.UfObjectState.State out moved.2)
      (new : Proofs.UfObjectState.State out (Proofs.CppConstructorFinish.reference (project moved.1 i32) 2)),
      invoke firstFuel (exported moved.1 after n) moved.2 .groups = .finished (middle,.scalar 1) ∧
      invoke secondFuel middle (Proofs.CppConstructorFinish.reference (project moved.1 i32) 2) .groups = .finished (out,.scalar (n : Int)) ∧
      old.data.items = parents ∧ new.data.items = List.replicate n (-1) ∧
      old.receiver.counter.value = 1 ∧ new.receiver.counter.value = (n : Int) ∧
      work out ≤ work (exported moved.1 after n)+20 := by
  obtain ⟨after,old,new,ran,oldItems,oldRank,oldCount,oldSize,newItems,live⟩ :=
    Proofs.UfObjectConstructionPreserve.construct_sized_pair moved.1 modelHeap moved.2 start model
      UfObjectHeapPeakExamples.headerLive (by decide +kernel) (.literal i32 (n : Int)) n small rfl rfl
      (by simp [NExpr.denote,Proofs.UfConstructionStage.nat_i32 n small])
  have newCount : new.receiver.counter.value = (n : Int) := by
    have actual := new.math.count
    rw [newItems] at actual
    exact actual.trans (Proofs.UfClassInvariant.initial_valid n small).count.symm
  obtain ⟨firstFuel,middle,oldMiddle,newMiddle,first,rank1,count1,size1,items1,rankOther,countOther,sizeOther,itemsOther,work1⟩ :=
    getter_pair_step (exported moved.1 after n) moved.2 _ old new
  obtain ⟨secondFuel,out,newOut,oldOut,second,rank2,count2,size2,items2,rankOld,countOld,sizeOld,itemsOld,work2⟩ :=
    getter_pair_step middle _ moved.2 newMiddle oldMiddle
  rw [oldCount] at first
  rw [countOther,newCount] at second
  refine ⟨after,firstFuel,secondFuel,middle,out,oldOut,newOut,first,second,
    itemsOld.trans (items1.trans oldItems),items2.trans (itemsOther.trans newItems),
    countOld.trans (count1.trans oldCount),count2.trans (countOther.trans newCount),?_⟩
  clear * - work1 work2
  omega
end UfGetterPairExamples
'''

ALIAS_GETTER = r'''namespace UfGetterAliasExamples
open Proofs.UfObjectGetterFrame UfEmptyHeaderPreserveExamples
example := getter_pair_step vacant object object initial initial
end UfGetterAliasExamples
'''

class UfObjectGetterFrameTests(unittest.TestCase):
    def check_lean(self, checks):
        fixtures = (EMPTY_CHECKS + PREFIX_CHECKS + UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
            OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] + APART_DEFINITIONS +
            STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS + MOVED_CHECKS + INITIAL_EMPTY + PAIR_CHECKS + EMPTY_HEADER_CHECKS)
        with tempfile.TemporaryDirectory(prefix='uf-getter-frame-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectGetterFrame\nimport Proofs.UfObjectConstructionPreserve\nimport Proofs.UfClassCopyBridge\n' + fixtures + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_two_distinct_objects_alternate_getters_after_actual_construction(self):
        self.check_lean(PAIR_GETTERS)

    def test_empty_object_alias_preserves_both_state_witnesses(self):
        self.check_lean(ALIAS_GETTER)

if __name__ == '__main__':
    disable_network()
    unittest.main()
