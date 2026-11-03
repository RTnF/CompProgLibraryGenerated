"""Typed move views, captured grants, Frame projection and resource correspondence."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_headers import CHECKS as HEADER_CHECKS
from offline import disable_network

CHECKS = r'''
namespace ViewExamples
open Proofs.CppMoveViews HeaderMoveExamples
-- Slots 0 and 2 denote the same mutable object; slot 1 is its const view.
def initial : State Int := ⟨second.1,[⟨0,true⟩,⟨0,false⟩,⟨0,true⟩,⟨1,true⟩]⟩
#guard (resolve initial 1).map (fun pair => pair.1.writable) == some false
#guard (assign initial allow 1 3).isNone
#guard (assign initial allow 3 1).isNone
#guard (construct initial allow 1 0 true).isNone
#guard (Proofs.CppMoveViews.capture initial allow 1 0 true).isNone
#guard (Proofs.CppMoveViews.capture initial allow 1 0 false).isSome
#guard (bind initial 999 true).isNone
-- Different view slots still select the same physical header: self move clears.
def self := (assign initial allow 0 2).getD initial
#guard self.heap.header 0 == some ⟨none,1,true,8⟩
#guard self.views == initial.views
#guard (read self allow first.2).isNone
#guard (resolve self 1).map (fun pair => pair.2.allocation) == some none
-- Nonself move changes the allocation reached by all destination object aliases.
def transferred := (assign initial allow 3 0).getD initial
#guard (resolve transferred 0).map (fun pair => pair.2.allocation) == some none
#guard (resolve transferred 1).map (fun pair => pair.2.allocation) == some none
#guard (resolve transferred 3).map (fun pair => pair.2.allocation) == some (some 0)
#guard read transferred allow first.2 == some 11
-- Const destination ownership does not revoke old mutable element references.
def constructed := (construct initial allow 0 0 false).getD (initial,0)
#guard constructed.2 == 4
#guard (resolve constructed.1 4).map (fun pair => pair.1.writable) == some false
#guard (Proofs.CppMoveViews.capture constructed.1 allow 4 0 true).isNone
#guard (Proofs.CppMoveViews.capture constructed.1 allow 4 0 false).isSome
#guard read constructed.1 allow first.2 == some 11
#guard (Proofs.CppMoveHeaders.write constructed.1.heap allow first.2 42).isSome
#guard (Proofs.CppMoveHeaders.write constructed.1.heap allow first.2 42).bind (fun h => Proofs.CppMoveHeaders.read h allow first.2) == some 42
example : assign initial allow 1 3 = none :=
  readonly_assign_target initial allow 1 3 ⟨0,false⟩ ⟨some 0,1,true,8⟩ rfl rfl
example : construct initial allow 1 0 true = none :=
  readonly_construct initial allow 1 0 true ⟨0,false⟩ ⟨some 0,1,true,8⟩ rfl rfl
example : Proofs.CppMoveViews.capture initial allow 1 0 true = none :=
  readonly_capture initial allow 1 0 ⟨0,false⟩ ⟨some 0,1,true,8⟩ rfl rfl

theorem transferredRun : assign initial allow 3 0 = some transferred := by rfl
example : transferred.heap.work = initial.heap.work + 2 := by rfl
example := assign_resources initial transferred allow 3 0 transferredRun
example : Unique transferred.heap :=
  assign_unique initial transferred allow 3 0 transferredRun initialUnique
example := assign_ready initial allow 3 0 ⟨1,true⟩ ⟨0,true⟩
  ⟨some 1,0,true,8⟩ ⟨some 0,1,true,8⟩ rfl rfl rfl rfl (by decide) (by decide) rfl initialUnique
theorem constructedRun : construct initial allow 0 0 false = some constructed := by rfl
example := construct_resources initial constructed.1 allow 0 0 constructed.2 false constructedRun
example (reference : Nat) : read constructed.1 allow reference = read initial allow reference :=
  construct_read initial constructed.1 allow 0 0 constructed.2 reference false constructedRun
example := construct_ready initial allow 0 0 false ⟨0,true⟩ ⟨some 0,1,true,8⟩ rfl rfl (by decide)
example := readonly_assign_source initial allow 3 1 ⟨0,false⟩ ⟨some 0,1,true,8⟩ rfl rfl
example := bind_runs initial 0 ⟨some 0,1,true,8⟩ false rfl (by simp)
example := bind_old_view initial 0 false 3 ⟨1,true⟩ rfl

def captured := (Proofs.CppMoveViews.capture initial allow 1 0 false).getD (initial,0)
theorem capturedRun : Proofs.CppMoveViews.capture initial allow 1 0 false = some captured := by rfl
example := capture_metadata initial captured.1 allow 1 0 false captured.2 capturedRun
example (other : Nat) : resolve captured.1 other = resolve initial other :=
  capture_resolve initial captured.1 allow 1 0 false captured.2 other capturedRun
example : read captured.1 allow first.2 = read initial allow first.2 :=
  capture_read_old initial captured.1 allow 1 0 false captured.2 first.2
    ⟨⟨⟨0,2,1⟩,7⟩,true⟩ capturedRun rfl
example : Unique constructed.1.heap :=
  construct_unique initial constructed.1 allow 0 0 constructed.2 false constructedRun initialUnique
example := construct_destination initial constructed.1 allow 0 0 constructed.2 false constructedRun
end ViewExamples


namespace FrameExamples
open Proofs.CppMoveFrame ViewExamples
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.CppFrameCopyAssign
 def ty : Proofs.CppScalar.Ty := ⟨64,true,false⟩
def before := materialize initial ty
def after := materialize transferred ty
def constAfter := materialize constructed.1 ty
def selfAfter := materialize self ty
#guard before.frame.state.wellFormed
#guard after.frame.state.wellFormed
#guard constAfter.frame.state.wellFormed
#guard selfAfter.frame.state.wellFormed
#guard before.frame.state.liveSpace == initial.heap.liveSpace
#guard after.frame.state.liveSpace == transferred.heap.liveSpace
#guard constAfter.frame.state.liveSpace == constructed.1.heap.liveSpace
#guard selfAfter.frame.state.liveSpace == self.heap.liveSpace
-- View slots follow immutable element-grant slots in the transient frame.
#guard (before.frame.resolve 2 (.integer ty)).map (fun pair => pair.2.items) == some [.integer 10,.integer 11]
#guard (after.frame.resolve 2 (.integer ty)).map (fun pair => pair.2.items) == some []
#guard (after.frame.resolve 5 (.integer ty)).map (fun pair => pair.2.items) == some [.integer 10,.integer 11]
#guard (reference initial.heap ty 0).bind (read after) == some 11
#guard (reference initial.heap ty 0).bind (read constAfter) == some 11
#guard (reference initial.heap ty 0).bind (read selfAfter) == none
#guard ((reference initial.heap ty 0).bind (fun r => write constAfter r 42)).isSome
#guard ((reference initial.heap ty 1).bind (fun r => write constAfter r 42)).isNone
#guard (constAfter.frame.elementRef 6 ty 0).map (fun r => r.writable) == some false

def capturedTarget := (Proofs.CppMoveHeaders.capture initial.heap HeaderMoveExamples.allow 1 0 true).getD (initial.heap,0)
def withTarget : Proofs.CppMoveViews.State Int := ⟨capturedTarget.1,initial.views⟩
def withTargetMoved := (Proofs.CppMoveViews.assign withTarget HeaderMoveExamples.allow 3 0).getD withTarget
#guard capturedTarget.2 == 2
#guard (reference withTarget.heap ty 2).bind (read (materialize withTarget ty)) == some 99
#guard (reference withTarget.heap ty 2).bind (read (materialize withTargetMoved ty)) == none
#guard (reference withTarget.heap ty 0).bind (read (materialize withTargetMoved ty)) == some 11
#guard (after.frame.state.forest.lookup 0).map (fun tag => tag.scope) == some (some 0)
#guard (after.frame.state.forest.lookup 2).map (fun tag => tag.scope) == some (some 1)
#guard (reference initial.heap ty 0).bind (fun r => read after {r with generation := r.generation+1}) == none
example := entries_allocation initial.heap ty 0 ⟨⟨0,[10,11],4,8,2⟩,fun _ => 7⟩
  ⟨some 0,1,true,8⟩ rfl rfl
example := entries_empty transferred.heap ty 0 ⟨none,1,true,8⟩ rfl rfl
example := materialize_resources transferred ty
example := materialize_maximum initial ty 0 1 ⟨0,[.integer 10,.integer 11],4,8,2⟩ rfl

theorem initialAllocValid : AllocationsValid initial.heap ty := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside initial.heap owner tracked found
  change owner < 2 at inside
  have cases : owner = 0 ∨ owner = 1 := by omega
  rcases cases with eq | eq <;> subst owner
  · have slot : initial.heap.allocation 0 = some ⟨⟨0,[10,11],4,8,2⟩,fun _ => 7⟩ := rfl
    rw [slot] at found
    cases Option.some.inj found
    decide
  · have slot : initial.heap.allocation 1 = some ⟨⟨1,[99],1,8,0⟩,fun _ => 0⟩ := rfl
    rw [slot] at found
    cases Option.some.inj found
    decide
example := materialize_ready initial ty (by decide) initialAllocValid
example := materialize_ready transferred ty (by decide)
  (assign_allocationsValid initial transferred ty HeaderMoveExamples.allow 3 0 transferredRun initialAllocValid)
example := materialize_ready constructed.1 ty (by decide)
  (construct_allocationsValid initial constructed.1 ty HeaderMoveExamples.allow 0 0 constructed.2 false constructedRun initialAllocValid)
example := ownerHeader_unique initial.heap 0 0 ⟨some 0,1,true,8⟩ HeaderMoveExamples.initialUnique rfl rfl ⟨_,rfl⟩

example := materialize_read initial ty 0 ⟨⟨⟨0,2,1⟩,7⟩,true⟩ rfl (by decide)
  HeaderMoveExamples.secondCovered (by decide) initialAllocValid
example := materialize_read transferred ty 0 ⟨⟨⟨0,2,1⟩,7⟩,true⟩ rfl (by decide)
  (Proofs.CppMoveViews.assign_ownsAll initial transferred HeaderMoveExamples.allow 3 0 transferredRun HeaderMoveExamples.secondCovered)
  (by decide)
  (assign_allocationsValid initial transferred ty HeaderMoveExamples.allow 3 0 transferredRun initialAllocValid)
example := materialize_dead_read withTargetMoved ty 2 ⟨⟨⟨1,0,0⟩,0⟩,true⟩ rfl (by decide) rfl
example := materialize_dead_read self ty 0 ⟨⟨⟨0,2,1⟩,7⟩,true⟩ rfl (by decide) rfl

theorem transferredValid : AllocationsValid transferred.heap ty :=
  assign_allocationsValid initial transferred ty HeaderMoveExamples.allow 3 0 transferredRun initialAllocValid
theorem transferredUnique : Proofs.CppMoveHeaders.Unique transferred.heap :=
  Proofs.CppMoveViews.assign_unique initial transferred HeaderMoveExamples.allow 3 0 transferredRun HeaderMoveExamples.initialUnique
theorem transferredCovered : Proofs.CppMoveHeaders.OwnsAll transferred.heap :=
  Proofs.CppMoveViews.assign_ownsAll initial transferred HeaderMoveExamples.allow 3 0 transferredRun HeaderMoveExamples.secondCovered
example := materialize_view_ready initial ty 0 ⟨0,true⟩ ⟨some 0,1,true,8⟩ rfl (by decide)
  HeaderMoveExamples.initialUnique HeaderMoveExamples.secondCovered (by decide) initialAllocValid
example := materialize_view_ready initial ty 1 ⟨0,false⟩ ⟨some 0,1,true,8⟩ rfl (by decide)
  HeaderMoveExamples.initialUnique HeaderMoveExamples.secondCovered (by decide) initialAllocValid
example := materialize_view_ready transferred ty 1 ⟨0,false⟩ ⟨none,1,true,8⟩ rfl (by decide)
  transferredUnique transferredCovered (by decide) transferredValid
example := materialize_view_ready transferred ty 3 ⟨1,true⟩ ⟨some 0,0,true,8⟩ rfl (by decide)
  transferredUnique transferredCovered (by decide) transferredValid
end FrameExamples


namespace SpaceExamples
open Proofs.CppMoveSpace ViewExamples FrameExamples
#guard (allocatedHeaders initial.heap).card == 2
#guard (liveAllocations initial.heap).card == 2
#guard (allocatedHeaders transferred.heap).card == 1
#guard (liveAllocations transferred.heap).card == 1
#guard (allocatedHeaders self.heap).card == 1
#guard (liveAllocations self.heap).card == 1

#guard (liveHeaders initial.heap).card == 2 && (emptyHeaders initial.heap).card == 0
#guard (liveHeaders transferred.heap).card == 2 && (emptyHeaders transferred.heap).card == 1
#guard (liveHeaders self.heap).card == 2 && (emptyHeaders self.heap).card == 1
theorem initialHeadersLive : HeadersLive initial.heap := by
  intro id header owner found owns
  have inside := Proofs.CppMoveHeaders.source_inside initial.heap id header found
  change id < 2 at inside
  have cases : id = 0 ∨ id = 1 := by omega
  rcases cases with eq | eq <;> subst id
  · have slot : initial.heap.header 0 = some ⟨some 0,1,true,8⟩ := rfl
    rw [slot] at found
    cases Option.some.inj found
    simp only [Option.some.injEq] at owns
    subst owner
    decide
  · have slot : initial.heap.header 1 = some ⟨some 1,0,true,8⟩ := rfl
    rw [slot] at found
    cases Option.some.inj found
    simp only [Option.some.injEq] at owns
    subst owner
    decide
example := owner_count initial.heap HeaderMoveExamples.initialUnique HeaderMoveExamples.secondCovered initialHeadersLive
example := header_allocation_count initial.heap HeaderMoveExamples.initialUnique HeaderMoveExamples.secondCovered initialHeadersLive
example := header_partition transferred.heap
example := header_partition self.heap

example := materialize_liveSpace initial ty HeaderMoveExamples.initialUnique HeaderMoveExamples.secondCovered initialHeadersLive
example := materialize_space_sum transferred ty
example := materialize_space_sum self ty
example := projection_weights transferred.heap ty transferredCovered
example := liveHeaders_countP transferred.heap
example := liveAllocations_countP transferred.heap
example := emptyHeaders_weight transferred.heap

theorem transferredLive : HeadersLive transferred.heap :=
  assign_headersLive initial transferred HeaderMoveExamples.allow 3 0 transferredRun HeaderMoveExamples.initialUnique initialHeadersLive
example := materialize_liveSpace transferred ty transferredUnique transferredCovered transferredLive
example := materialize_liveSpace constructed.1 ty
  (Proofs.CppMoveViews.construct_unique initial constructed.1 HeaderMoveExamples.allow 0 0 constructed.2 false constructedRun HeaderMoveExamples.initialUnique)
  (Proofs.CppMoveViews.construct_ownsAll initial constructed.1 HeaderMoveExamples.allow 0 0 constructed.2 false constructedRun HeaderMoveExamples.secondCovered)
  (construct_headersLive initial constructed.1 HeaderMoveExamples.allow 0 0 constructed.2 false constructedRun initialHeadersLive)
end SpaceExamples
'''

class MoveFrameTests(unittest.TestCase):
    def test_views_projection_references_and_resources(self):
        with tempfile.TemporaryDirectory(prefix='move-frame-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppMoveSpace\n'+HEADER_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__=='__main__':
    disable_network()
    unittest.main()
