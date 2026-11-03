"""Typed Frame writes round-trip to the move heap with matching outcomes and resources."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_headers import CHECKS as HEADER_CHECKS
from test_cpp_move_frame import CHECKS as FRAME_CHECKS
from offline import disable_network

CHECKS = r'''
namespace WriteExamples
open Proofs.CppMoveWrite ViewExamples FrameExamples
-- All examples use actual existing Frame.write execution and a decoded result.
def written := (restoreWrite constructed.1 ty 0 42).getD constructed.1
#guard (restoreWrite constructed.1 ty 0 42).isSome
#guard Proofs.CppMoveHeaders.read written.heap ty.valid 0 == some 42
#guard written.heap.headers == constructed.1.heap.headers
#guard written.views == constructed.1.views
#guard written.heap.grants == constructed.1.heap.grants
#guard written.heap.work == constructed.1.heap.work+1
#guard written.heap.liveSpace == constructed.1.heap.liveSpace
#guard written.heap.peak == max constructed.1.heap.peak (constructed.1.heap.liveSpace+1-constructed.1.heap.baseSpace)
#guard (restoreWrite constructed.1 ty 1 42).isNone
#guard (restoreWrite self ty 0 42).isNone
#guard (restoreWrite withTargetMoved ty 2 42).isNone
#guard (restoreWrite constructed.1 ty 0 (2^63)).isNone
#guard (restoreWrite constructed.1 ty 999 42).isNone
#guard (unbox ⟨0,[.child 0],1,8,0⟩).isNone
#guard (writeEvent constructed.1 ty 0 42).map (fun s => (s.heap.work,s.heap.peak,s.heap.liveSpace)) ==
  (restoreWrite constructed.1 ty 0 42).map (fun s => (s.heap.work,s.heap.peak,s.heap.liveSpace))

theorem writtenRun : restoreWrite constructed.1 ty 0 42 = some written := by
  have live : (restoreWrite constructed.1 ty 0 42).isSome = true := by decide +kernel
  have nonempty : restoreWrite constructed.1 ty 0 42 ≠ none := by
    intro missing
    simp [missing] at live
  exact (Option.getD_of_ne_none nonempty constructed.1).symm
example := restoreWrite_metadata constructed.1 written ty 0 42 writtenRun
example := box_write (⟨0,[10,11],4,8,2⟩ : Proofs.CppVector.Buffer Int) ty true ⟨0,2,1⟩ 42
example := unbox_box (⟨0,[10,42],4,8,2⟩ : Proofs.CppVector.Buffer Int)

example := materialized_write_runs initial ty 0 ⟨⟨⟨0,2,1⟩,7⟩,true⟩
  ⟨⟨0,[10,11],4,8,2⟩,fun _ => 7⟩ 42 ⟨⟨0,[10,42],4,8,2⟩,(),1,6⟩
  rfl rfl HeaderMoveExamples.secondCovered (by decide) initialAllocValid rfl (by decide +kernel)
example := restoreWrite_primitive initial ty 0 ⟨⟨⟨0,2,1⟩,7⟩,true⟩
  ⟨⟨0,[10,11],4,8,2⟩,fun _ => 7⟩ 42 ⟨⟨0,[10,42],4,8,2⟩,(),1,6⟩
  rfl rfl HeaderMoveExamples.initialUnique HeaderMoveExamples.secondCovered SpaceExamples.initialHeadersLive
  (by decide) initialAllocValid rfl (by decide +kernel)

theorem initialGrantBounds : GrantBounds initial.heap := by
  intro id grant found
  have inside := (List.getElem?_eq_some_iff.mp found).1
  change id < 2 at inside
  have cases : id = 0 ∨ id = 1 := by omega
  rcases cases with eq | eq <;> subst id
  · have slot : initial.heap.grants[0]? = some ⟨⟨⟨0,2,1⟩,7⟩,true⟩ := rfl
    rw [slot] at found
    cases Option.some.inj found
    decide
  · have slot : initial.heap.grants[1]? = some ⟨⟨⟨0,2,0⟩,7⟩,false⟩ := rfl
    rw [slot] at found
    cases Option.some.inj found
    decide
example (id : Nat) (value : Int) : restoreWrite initial ty id value = writeEvent initial ty id value :=
  restoreWrite_eq_event initial ty id value HeaderMoveExamples.initialUnique HeaderMoveExamples.secondCovered
    SpaceExamples.initialHeadersLive (by decide) initialAllocValid initialGrantBounds
example (id : Nat) (value : Int) : restoreWrite transferred ty id value = writeEvent transferred ty id value :=
  restoreWrite_eq_event transferred ty id value transferredUnique transferredCovered SpaceExamples.transferredLive
    (by decide) transferredValid (assign_grantBounds initial transferred HeaderMoveExamples.allow 3 0 transferredRun initialGrantBounds)
example := construct_grantBounds initial constructed.1 HeaderMoveExamples.allow 0 0 constructed.2 false constructedRun initialGrantBounds

example := capture_grantBounds initial captured.1 HeaderMoveExamples.allow 1 0 false captured.2 capturedRun initialGrantBounds
def eventWritten := (writeEvent initial ty 0 42).getD initial
theorem eventRun : writeEvent initial ty 0 42 = some eventWritten := by
  have live : (writeEvent initial ty 0 42).isSome = true := by decide +kernel
  have nonempty : writeEvent initial ty 0 42 ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty initial).symm
example := writeEvent_resources initial eventWritten ty 0 42 eventRun
example := writeEvent_other initial eventWritten ty 0 42 ⟨⟨⟨0,2,1⟩,7⟩,true⟩ 1 rfl (by decide) eventRun
example := Proofs.CppMoveFrame.materialize_ready eventWritten ty (by decide)
  (writeEvent_allocationsValid initial eventWritten ty 0 42 eventRun initialAllocValid)
example (id : Nat) (value : Int) : restoreWrite eventWritten ty id value = writeEvent eventWritten ty id value :=
  restoreWrite_eq_event eventWritten ty id value
    (writeEvent_unique initial eventWritten ty 0 42 eventRun HeaderMoveExamples.initialUnique)
    (writeEvent_ownsAll initial eventWritten ty 0 42 eventRun HeaderMoveExamples.secondCovered)
    (writeEvent_headersLive initial eventWritten ty 0 42 eventRun SpaceExamples.initialHeadersLive)
    (by decide) (writeEvent_allocationsValid initial eventWritten ty 0 42 eventRun initialAllocValid)
    (writeEvent_grantBounds initial eventWritten ty 0 42 eventRun initialGrantBounds)
end WriteExamples
'''

class MoveWriteTests(unittest.TestCase):
    def test_write_outcomes_invariants_resources_and_capture(self):
        with tempfile.TemporaryDirectory(prefix='move-write-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppMoveWrite\n'+HEADER_CHECKS+FRAME_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__=='__main__':
    disable_network()
    unittest.main()
