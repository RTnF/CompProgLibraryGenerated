"""Actual compact calls preserve separate UF buffers and scalar fields."""
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
    APART_DEFINITIONS, STATE_CHECKS, TRACE_CHECKS, MEANING_CHECKS, ROOT_CHECKS, HEAP_CHECKS, MOVED_CHECKS,
)
from test_uf_object_initial_amortized import EMPTY_CHECKS as INITIAL_EMPTY
from offline import disable_network

SETUP = r'''namespace UfObjectValuesExamples
open Proofs.CppMoveContext Proofs.CppMoveObjectReceiver Proofs.CppNestedProgram Proofs.CppMoveFrame
open Proofs.CppMoveHeaders Proofs.CppMoveFrameScopes Proofs.UfObjectState Proofs.UfObjectTrace
open Proofs.UfObjectValues Proofs.DoublingNested
open UfMoveCallExamples UfObjectStateExamples

def two : Context := ⟨⟨⟨[some ⟨some 0,0,true,limit⟩,some ⟨some 1,0,true,limit⟩],
  [some ⟨⟨0,parents,5,limit,0⟩,fun _ => 7⟩,
   some ⟨⟨1,List.replicate 4 (-1),4,limit,0⟩,fun _ => 0⟩],[],0,0,0⟩,
  [⟨0,true⟩,⟨1,true⟩]⟩,
  ⟨[⟨i32,1⟩,⟨i32,4⟩,⟨i32,4⟩,⟨i32,4⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩],0,0,0⟩,
  [.vector 0,.scalar 0,.scalar 1,.vector 1,.scalar 2,.scalar 3],1,0⟩
def oldObject : Proofs.CppConstructorFinish.ObjectRef := ⟨0,[1,2]⟩
def freshObject : Proofs.CppConstructorFinish.ObjectRef := ⟨3,[4,5]⟩

theorem headerFacts (id : Nat) (header : Header) (found : two.objects.heap.header id = some header) :
    header.allocation = some id ∧ header.scope = 0 := by
  have inside := (List.getElem?_eq_some_iff.mp (header_lookup _ _ _ found)).1
  change id < 2 at inside
  have choices : id=0 ∨ id=1 := by omega
  rcases choices with rfl | rfl
  · have atZero : two.objects.heap.header 0 = some ⟨some 0,0,true,limit⟩ := rfl
    rw [atZero] at found
    cases Option.some.inj found
    exact ⟨rfl,rfl⟩
  · have atOne : two.objects.heap.header 1 = some ⟨some 1,0,true,limit⟩ := rfl
    rw [atOne] at found
    cases Option.some.inj found
    exact ⟨rfl,rfl⟩

theorem unique : Unique two.objects.heap := by
  intro i j hi hj owner fi fj oi oj
  have left := (headerFacts i hi fi).1
  have right := (headerFacts j hj fj).1
  exact Option.some.inj (left.symm.trans (oi.trans (oj.symm.trans right)))

theorem covered : OwnsAll two.objects.heap := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside two.objects.heap owner tracked found
  change owner < 2 at inside
  have choices : owner=0 ∨ owner=1 := by omega
  rcases choices with rfl | rfl
  · exact ⟨0,⟨some 0,0,true,limit⟩,rfl,rfl⟩
  · exact ⟨1,⟨some 1,0,true,limit⟩,rfl,rfl⟩

theorem allocations : AllocationsValid two.objects.heap i32 := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside two.objects.heap owner tracked found
  change owner < 2 at inside
  have choices : owner=0 ∨ owner=1 := by omega
  rcases choices with rfl | rfl
  · have atZero : two.objects.heap.allocation 0 = some ⟨⟨0,parents,5,limit,0⟩,fun _ => 7⟩ := rfl
    rw [atZero] at found
    cases Option.some.inj found
    decide +kernel
  · have atOne : two.objects.heap.allocation 1 = some ⟨⟨1,List.replicate 4 (-1),4,limit,0⟩,fun _ => 0⟩ := rfl
    rw [atOne] at found
    cases Option.some.inj found
    decide +kernel

theorem contexts : ∀ owner scope, (project two i32).frame.state.forest.context owner = some scope → scope ≤ two.scope := by
  apply contexts_of_headers two.objects i32 two.scope
  intro id header found
  rw [(headerFacts id header found).2]
  decide +kernel

def oldReceiver : Receiver two oldObject i32 :=
  ⟨⟨1,0,0,true,1,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
   ⟨2,1,1,true,4,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
   rfl,rfl,0,⟨0,true⟩,⟨some 0,0,true,limit⟩,rfl,rfl,rfl⟩
def freshReceiver : Receiver two freshObject i32 :=
  ⟨⟨4,2,2,true,4,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
   ⟨5,3,3,true,4,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,
   rfl,rfl,1,⟨1,true⟩,⟨some 1,0,true,limit⟩,rfl,rfl,rfl⟩

def old : State two oldObject :=
  ⟨oldReceiver,⟨0,parents,5,limit,0⟩,rfl,ranks,parentValid,rfl,by decide +kernel,
   by decide +kernel,unique,covered,allocations,rfl,by decide +kernel,contexts⟩
def fresh : State two freshObject :=
  ⟨freshReceiver,⟨1,List.replicate 4 (-1),4,limit,0⟩,rfl,(fun _ => 0),
   Proofs.UfClassInvariant.initial_valid 4 (by decide +kernel),rfl,by decide +kernel,
   by decide +kernel,unique,covered,allocations,rfl,by decide +kernel,contexts⟩

end UfObjectValuesExamples
'''

ALL_OPERATIONS = r'''namespace UfObjectValuesExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram
open Proofs.UfObjectTrace Proofs.UfObjectState Proofs.UfObjectValues
open UfMoveCallExamples UfObjectStateExamples
example (op : Operation) (ready : op.Valid 4) :=
  pair_step two freshObject oldObject fresh old op ready (by decide +kernel) (by decide +kernel) (by decide +kernel)
example (op : Operation) (ready : op.Valid 4) :=
  pair_step two oldObject freshObject old fresh op ready (by decide +kernel) (by decide +kernel) (by decide +kernel)

end UfObjectValuesExamples
'''

UNITE = r'''namespace UfObjectValuesExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram
open Proofs.UfObjectTrace Proofs.UfObjectState Proofs.UfObjectValues
open UfMoveCallExamples UfObjectStateExamples
example : ∃ (fuel : Nat) (out : Context) (result : Ret) (next : State out freshObject) (other : State out oldObject),
    Step two freshObject fresh (.unite 0 1) fuel out result next ∧
    next.receiver.counter.value = 3 ∧ other.data.items = parents ∧ other.receiver.counter.value = 1 ∧ other.receiver.size.value = 4 := by
  obtain ⟨fuel,out,result,next,other,step,rank,count,size,items⟩ :=
    pair_step two freshObject oldObject fresh old (.unite 0 1) (by change 0 < 4 ∧ 1 < 4; decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨r1,r2,middle,twice,resultEq,compressed1,compressed2,finalEq,connected,nextCount⟩ := step.meaning
  have firstRoot : r1 = 0 := (Proofs.UfClassInvariant.initial_reach 4 0 r1 (by decide +kernel)).mp compressed1.reach
  have secondRoot : r2 = 1 := (Proofs.UfClassInvariant.initial_reach 4 1 r2 (by decide +kernel)).mp
    (Proofs.UfCompression.reach_backward compressed1 compressed2.reach)
  have three : next.receiver.counter.value = 3 := by
    simpa [firstRoot,secondRoot,Proofs.UfFieldsUnite.countAfter,fresh,freshReceiver] using nextCount
  exact ⟨fuel,out,result,next,other,step,three,items,count,size⟩

end UfObjectValuesExamples
'''

class UfObjectValuesTests(unittest.TestCase):
    def check_lean(self, checks):
        fixtures = (EMPTY_CHECKS + PREFIX_CHECKS + UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
            OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] + APART_DEFINITIONS +
            STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS + MOVED_CHECKS + INITIAL_EMPTY + SETUP)
        with tempfile.TemporaryDirectory(prefix='uf-object-values-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectValues\nimport Proofs.UfObjectConstructionPreserve\nimport Proofs.UfClassCopyBridge\n' + fixtures + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_every_valid_operation_keeps_the_other_object_in_both_directions(self):
        self.check_lean(ALL_OPERATIONS)

    def test_unite_changes_only_selected_count_from_four_to_three(self):
        self.check_lean(UNITE)

if __name__ == '__main__':
    disable_network()
    unittest.main()
