"""Readonly source copies retain raw members and create normal copies when the source is normal."""
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

SETUP = r'''
namespace UfObjectReadSourceExamples
open Proofs.CppMoveContext Proofs.CppMoveObjectReceiver Proofs.CppMoveHeaders Proofs.CppMoveFrame
open Proofs.CppNestedProgram Proofs.CppMoveReadReceiver Proofs.UfObjectReadSource Proofs.DoublingNested
open UfMoveCallExamples UfObjectStateExamples

def context (ownerWritable : Bool) : Context := {moved.1 with
  objects := {moved.1.objects with
    heap := {moved.1.objects.heap with headers :=
      [some ⟨none,0,true,limit⟩,some ⟨some 0,0,ownerWritable,limit⟩]}
    views := [⟨0,true⟩,⟨1,false⟩]}
  scalars := {moved.1.scalars with bindings := [⟨0,true⟩,⟨1,true⟩,⟨2,false⟩,⟨3,false⟩]}}

theorem headers (w : Bool) (id : Nat) (header : Header) (found : (context w).objects.heap.header id = some header) :
    (id=0 ∧ header=⟨none,0,true,limit⟩) ∨ (id=1 ∧ header=⟨some 0,0,w,limit⟩) := by
  have inside := (List.getElem?_eq_some_iff.mp (header_lookup _ _ _ found)).1
  change id < 2 at inside
  have choices : id=0 ∨ id=1 := by omega
  rcases choices with rfl | rfl
  · have atZero : (context w).objects.heap.header 0 = some ⟨none,0,true,limit⟩ := rfl
    rw [atZero] at found
    exact Or.inl ⟨rfl,(Option.some.inj found).symm⟩
  · have atOne : (context w).objects.heap.header 1 = some ⟨some 0,0,w,limit⟩ := rfl
    rw [atOne] at found
    exact Or.inr ⟨rfl,(Option.some.inj found).symm⟩

theorem onlyOwner (w : Bool) (id : Nat) (header : Header) (owner : Nat)
    (found : (context w).objects.heap.header id = some header) (owns : header.allocation = some owner) : id=1 := by
  rcases headers w id header found with ⟨rfl,rfl⟩ | ⟨same,headerEq⟩
  · contradiction
  · exact same

theorem unique (w : Bool) : Unique (context w).objects.heap := by
  intro i j hi hj owner fi fj oi oj
  exact (onlyOwner w i hi owner fi oi).trans (onlyOwner w j hj owner fj oj).symm

theorem covered (w : Bool) : OwnsAll (context w).objects.heap := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside (context w).objects.heap owner tracked found
  change owner < 2 at inside
  have choices : owner=0 ∨ owner=1 := by omega
  rcases choices with rfl | rfl
  · exact ⟨1,⟨some 0,0,w,limit⟩,rfl,rfl⟩
  · have atOne : (context w).objects.heap.allocation 1 = none := rfl
    rw [atOne] at found
    contradiction

theorem contexts (w : Bool) : ∀ owner scope, (project (context w) i32).frame.state.forest.context owner = some scope → scope ≤ (context w).scope := by
  apply Proofs.CppMoveFrameScopes.contexts_of_headers (context w).objects i32 (context w).scope
  intro id header found
  rcases headers w id header found with ⟨idEq,rfl⟩ | ⟨idEq,rfl⟩ <;> change 0 ≤ 1 <;> omega

def receiver (w : Bool) : ReadReceiver (context w) moved.2 i32 :=
  ⟨⟨4,2,2,false,1,rfl,rfl,rfl,by decide +kernel⟩,
   ⟨5,3,3,false,4,rfl,rfl,rfl,by decide +kernel⟩,
   rfl,1,⟨1,false⟩,⟨some 0,0,w,limit⟩,rfl,rfl⟩
def data : Proofs.CppVector.Buffer Int := ⟨0,parents,5,limit,0⟩

theorem readable (w : Bool) : Proofs.CppMoveHeaders.readable (context w).objects.heap (receiver w).header i32.valid = true := by
  exact (by decide +kernel : Proofs.CppMoveHeaders.readable moved.1.objects.heap ⟨some 0,0,true,limit⟩ i32.valid = true)

theorem view (w : Bool) : Proofs.UfAssignmentView.SourceView (project (context w) i32)
    (layout (context w) moved.2 (receiver w) data) parents 1 ranks (box data)
    ⟨0,.integer i32,false,.root 0⟩ ⟨2,false⟩ ⟨3,false⟩ := source_view (context w) moved.2 (receiver w) data ranks rfl parentValid rfl
  (readable w) (unique w) (covered w) UfReceiverLayoutExamples.allocationsValid rfl

'''

NORMAL = r'''example (w : Bool) := copy_raw (context w) moved.2 (receiver w) data rfl
  (readable w) (unique w) (covered w) UfReceiverLayoutExamples.allocationsValid

example (w : Bool) : Proofs.UfReceiverState.Represents
    (Proofs.UfCopyReceiver.state (project (context w) i32) (box data) 1 4)
    (Proofs.UfReceiverState.layoutOf (project (context w) i32)) parents 1 ranks := by
  apply copy_represents (project (context w) i32) _ parents 1 ranks (box data) _ _ _ (view w)
  · exact materialize_ready (context w).objects i32 (by decide +kernel) UfReceiverLayoutExamples.allocationsValid
  · simp [project,materialize]
  · exact contexts w
  · change 0 ≤ 4
    omega

example (w : Bool) := copy_correct (context w) moved.2 (receiver w) data ranks rfl parentValid rfl
  (readable w) (unique w) (covered w) UfReceiverLayoutExamples.allocationsValid rfl (by change 0 ≤ 4; omega) (contexts w)

example (w : Bool) (ref : Proofs.CppNestedVectorBindings.Reference) (value : Int)
    (read : (project (context w) i32).frame.read ref = some value) :
    (Proofs.UfCopyReceiver.state (project (context w) i32) (box data) 1 4).frame.read ref = some value := by
  have complete := copy_correct (context w) moved.2 (receiver w) data ranks rfl parentValid rfl
    (readable w) (unique w) (covered w) UfReceiverLayoutExamples.allocationsValid rfl (by change 0 ≤ 4; omega) (contexts w)
  exact Proofs.CppFrameExtension.read_kept _ _ complete.2.2.1 ref value read

example (w : Bool) :
    (Proofs.UfCopyReceiver.state (project (context w) i32) (box data) 1 4).scalarCell 4 i32 =
      some (⟨2,false⟩,⟨i32,1⟩) :=
  Proofs.UfCopyFields.fields_old_scalar (project (context w) i32)
    (Proofs.CppFrameCopy.copiedFrame (project (context w) i32).frame (box data) i32 (context w).scope true)
    1 4 4 i32 ⟨2,false⟩ ⟨i32,1⟩ (view w).countCell

end UfObjectReadSourceExamples
'''

MOVED = r'''def emptyContext (w : Bool) : Context := {context w with
  objects := {(context w).objects with views := [⟨0,false⟩,⟨1,false⟩]}
  scalars := {(context w).scalars with bindings := [⟨0,false⟩,⟨1,false⟩,⟨2,false⟩,⟨3,false⟩]}}
def emptyObject : Proofs.CppConstructorFinish.ObjectRef := ⟨0,[1,2]⟩
def emptyReceiver (w : Bool) : ReadReceiver (emptyContext w) emptyObject i32 :=
  ⟨⟨1,0,0,false,1,rfl,rfl,rfl,by decide +kernel⟩,
   ⟨2,1,1,false,4,rfl,rfl,rfl,by decide +kernel⟩,
   rfl,0,⟨0,false⟩,⟨none,0,true,limit⟩,rfl,rfl⟩
def emptyData : Proofs.CppVector.Buffer Int := ⟨2,[],0,limit,0⟩

-- Copying the moved-from source is legal even though its UF mathematical invariant no longer holds.
example (w : Bool) : Proofs.CppClassCopy.copyClass (project (emptyContext w) i32) emptyObject Proofs.UfClassCopyBridge.profile =
    some (Proofs.UfCopyReceiver.state (project (emptyContext w) i32) (box emptyData) 1 4,
      Proofs.CppConstructorFinish.reference (project (emptyContext w) i32) 2) :=
  copy_raw (emptyContext w) emptyObject (emptyReceiver w) emptyData rfl rfl (unique w) (covered w) UfReceiverLayoutExamples.allocationsValid

end UfObjectReadSourceExamples
'''

class UfObjectReadSourceTests(unittest.TestCase):
    def check_lean(self, checks):
        fixtures = (EMPTY_CHECKS + PREFIX_CHECKS + UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
            OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] + APART_DEFINITIONS +
            STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS + MOVED_CHECKS + INITIAL_EMPTY + SETUP)
        with tempfile.TemporaryDirectory(prefix='uf-object-read-source-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfObjectReadSource\nimport Proofs.CppMoveFrameScopes\nimport Proofs.UfObjectConstructedPair\nimport Proofs.UfObjectConstructionPreserve\nimport Proofs.UfClassCopyBridge\n' + fixtures + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_readonly_borrow_and_readonly_owner_copy_into_mutable_uf_preserving_reads(self):
        self.check_lean(NORMAL)

    def test_readonly_moved_from_copy_keeps_empty_data_count_one_and_size_four(self):
        self.check_lean(MOVED)

if __name__ == '__main__':
    disable_network()
    unittest.main()
