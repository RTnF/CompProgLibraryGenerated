"""Source UF receiver preparation, exact field states, normal frames and root call."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_receiver_layout import UF_CHECKS, RECEIVER_CHECKS
from offline import disable_network

CHECKS = r'''

namespace UfReceiverLayoutExamples
open Proofs.CppMoveContext Proofs.CppMoveReceiverLayout Proofs.CppMoveCallBindings
open Proofs.UfReceiverLayout Proofs.QuotientFrame Proofs.VecExpr
open UfMoveCallExamples ReceiverLayoutExamples

example : ∃ prepared initial,
    prepareArguments moved.1 ty root.program.parameters root.arguments = some prepared ∧
    compact (project prepared ty) = some initial ∧
    QS initial [] initial.scalars.baseMemory initial.scope
      (Proofs.UfFieldsRoot.fields (receiverPrefix moved.1) ⟨2,true⟩ 4 3).mem (Proofs.UfFieldsRoot.fields (receiverPrefix moved.1) ⟨2,true⟩ 4 3).bs (sl1 (Proofs.UfFieldsRoot.fields (receiverPrefix moved.1) ⟨2,true⟩ 4 3).bs.length) := by
  obtain ⟨prepared,initial,run,compacted,qs,base,scope,state,roots,bindings⟩ :=
    prepare_qs moved.1 root.resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
      (by decide +kernel) (fun h => h) 2 1 (by decide +kernel) (by decide +kernel)
      [4,3] (by intro value member; simp at member; rcases member with rfl | rfl <;> decide +kernel)
      root.program.parameters root.arguments root.resolvedRun
  exact ⟨prepared,initial,run,compacted,qs_two initial (receiverPrefix moved.1) 2 4 3 qs⟩

example : ∃ prepared initial,
    prepareArguments moved.1 ty size.program.parameters size.arguments = some prepared ∧
    compact (project prepared ty) = some initial ∧
    QS initial [] initial.scalars.baseMemory initial.scope
      (Proofs.UfFieldsRoot.fields (receiverPrefix moved.1) ⟨2,true⟩ 4 3).mem (Proofs.UfFieldsRoot.fields (receiverPrefix moved.1) ⟨2,true⟩ 4 3).bs (sl1 (Proofs.UfFieldsRoot.fields (receiverPrefix moved.1) ⟨2,true⟩ 4 3).bs.length) := by
  obtain ⟨prepared,initial,run,compacted,qs,base,scope,state,roots,bindings⟩ :=
    prepare_qs moved.1 size.resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
      (by decide +kernel) (fun h => h) 2 1 (by decide +kernel) (by decide +kernel)
      [4,3] (by intro value member; simp at member; rcases member with rfl | rfl <;> decide +kernel)
      size.program.parameters size.arguments size.resolvedRun
  exact ⟨prepared,initial,run,compacted,qs_two initial (receiverPrefix moved.1) 2 4 3 qs⟩

example : ∃ prepared initial,
    prepareArguments moved.1 ty same.program.parameters same.arguments = some prepared ∧
    compact (project prepared ty) = some initial ∧
    QS initial [] initial.scalars.baseMemory initial.scope
      (Proofs.UfFieldsSame.fields (receiverPrefix moved.1) ⟨2,true⟩ 4 3 1).mem (Proofs.UfFieldsSame.fields (receiverPrefix moved.1) ⟨2,true⟩ 4 3 1).bs (sl1 (Proofs.UfFieldsSame.fields (receiverPrefix moved.1) ⟨2,true⟩ 4 3 1).bs.length) := by
  obtain ⟨prepared,initial,run,compacted,qs,base,scope,state,roots,bindings⟩ :=
    prepare_qs moved.1 same.resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
      (by decide +kernel) (fun h => h) 2 1 (by decide +kernel) (by decide +kernel)
      [4,3,1] (by intro value member; simp at member; rcases member with rfl | rfl | rfl <;> decide +kernel)
      same.program.parameters same.arguments same.resolvedRun
  exact ⟨prepared,initial,run,compacted,qs_three initial (receiverPrefix moved.1) 2 4 3 1 qs⟩

example : ∃ prepared initial,
    prepareArguments moved.1 ty unite.program.parameters unite.arguments = some prepared ∧
    compact (project prepared ty) = some initial ∧
    QS initial [] initial.scalars.baseMemory initial.scope
      (Proofs.UfFieldsSame.fields (receiverPrefix moved.1) ⟨2,true⟩ 4 3 1).mem (Proofs.UfFieldsSame.fields (receiverPrefix moved.1) ⟨2,true⟩ 4 3 1).bs (sl1 (Proofs.UfFieldsSame.fields (receiverPrefix moved.1) ⟨2,true⟩ 4 3 1).bs.length) := by
  obtain ⟨prepared,initial,run,compacted,qs,base,scope,state,roots,bindings⟩ :=
    prepare_qs moved.1 unite.resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
      (by decide +kernel) (fun h => h) 2 1 (by decide +kernel) (by decide +kernel)
      [4,3,1] (by intro value member; simp at member; rcases member with rfl | rfl | rfl <;> decide +kernel)
      unite.program.parameters unite.arguments unite.resolvedRun
  exact ⟨prepared,initial,run,compacted,qs_three initial (receiverPrefix moved.1) 2 4 3 1 qs⟩

example : ∃ prepared initial,
    prepareArguments moved.1 ty num_groups.program.parameters num_groups.arguments = some prepared ∧
    compact (project prepared ty) = some initial ∧
    QS initial [] initial.scalars.baseMemory initial.scope
      (Proofs.UfFieldsCounter.fields (receiverPrefix moved.1) 2 4).mem (Proofs.UfFieldsCounter.fields (receiverPrefix moved.1) 2 4).bs (sl1 (Proofs.UfFieldsCounter.fields (receiverPrefix moved.1) 2 4).bs.length) := by
  obtain ⟨prepared,initial,run,compacted,qs,base,scope,state,roots,bindings⟩ :=
    prepare_qs moved.1 num_groups.resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
      (by decide +kernel) (fun h => h) 2 1 (by decide +kernel) (by decide +kernel)
      [4] (by intro value member; simp at member; subst value; decide +kernel)
      num_groups.program.parameters num_groups.arguments num_groups.resolvedRun
  exact ⟨prepared,initial,run,compacted,qs_one initial (receiverPrefix moved.1) 2 4 qs⟩

open Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppMoveReceiverFrame
open Proofs.CppVector Proofs.CppNestedProgram Proofs.VecWrite

theorem onlyOwner (id : Nat) (header : Proofs.CppMoveHeaders.Header) (owner : Nat)
    (found : moved.1.objects.heap.header id = some header)
    (owns : header.allocation = some owner) : id = 1 := by
  have inside := (List.getElem?_eq_some_iff.mp (header_lookup moved.1.objects.heap id header found)).1
  change id < 2 at inside
  have choices : id=0 ∨ id=1 := by omega
  rcases choices with rfl | equal
  · have atZero : moved.1.objects.heap.header 0 = some ⟨none,0,true,limit⟩ := rfl
    rw [atZero] at found
    cases Option.some.inj found
    contradiction
  · exact equal

theorem unique : Unique moved.1.objects.heap := by
  intro i j hi hj owner foundI foundJ ownsI ownsJ
  exact (onlyOwner i hi owner foundI ownsI).trans (onlyOwner j hj owner foundJ ownsJ).symm

theorem allocationsValid : AllocationsValid moved.1.objects.heap ty := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside moved.1.objects.heap owner tracked found
  change owner < 2 at inside
  have choices : owner=0 ∨ owner=1 := by omega
  rcases choices with rfl | rfl
  · have atZero : moved.1.objects.heap.allocation 0 = some ⟨⟨0,[-4,0,0,2],5,limit,0⟩,fun _ => 7⟩ := rfl
    rw [atZero] at found
    cases Option.some.inj found
    decide +kernel
  · have atOne : moved.1.objects.heap.allocation 1 = none := rfl
    rw [atOne] at found
    contradiction

example := prepare_qs_fw moved.1 root.resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
  (by decide +kernel) (fun h => h) (by decide +kernel) unique covered allocationsValid rfl
  2 1 (by decide +kernel) (by decide +kernel) [4,3]
  (by intro value member; simp at member; rcases member with rfl | rfl <;> decide +kernel)
  root.program.parameters root.arguments root.resolvedRun contexts

example := prepare_qs_fw moved.1 size.resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
  (by decide +kernel) (fun h => h) (by decide +kernel) unique covered allocationsValid rfl
  2 1 (by decide +kernel) (by decide +kernel) [4,3]
  (by intro value member; simp at member; rcases member with rfl | rfl <;> decide +kernel)
  size.program.parameters size.arguments size.resolvedRun contexts

example := prepare_qs_fw moved.1 same.resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
  (by decide +kernel) (fun h => h) (by decide +kernel) unique covered allocationsValid rfl
  2 1 (by decide +kernel) (by decide +kernel) [4,3,1]
  (by intro value member; simp at member; rcases member with rfl | rfl | rfl <;> decide +kernel)
  same.program.parameters same.arguments same.resolvedRun contexts

example := prepare_qs_fw moved.1 unite.resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
  (by decide +kernel) (fun h => h) (by decide +kernel) unique covered allocationsValid rfl
  2 1 (by decide +kernel) (by decide +kernel) [4,3,1]
  (by intro value member; simp at member; rcases member with rfl | rfl | rfl <;> decide +kernel)
  unite.program.parameters unite.arguments unite.resolvedRun contexts

example := prepare_qs_fw moved.1 num_groups.resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
  (by decide +kernel) (fun h => h) (by decide +kernel) unique covered allocationsValid rfl
  2 1 (by decide +kernel) (by decide +kernel) [4]
  (by intro value member; simp at member; subst value; decide +kernel)
  num_groups.program.parameters num_groups.arguments num_groups.resolvedRun contexts

-- All preparation, QS and FW assumptions for root_call come from the new bridge.
example : ∃ (fuel : Nat) (out : Context) (r : Nat) (final : List Int),
    callFuel root.program fuel moved.1 ty root.arguments = .finished (out,.scalar (r : Int)) ∧
    Proofs.UfCompression.Compressed parents final 3 r := by
  obtain ⟨prepared,initial,vc,buffer,run,compacted,qs,fw,tyEq,writable,flag,sc,current,base,scope⟩ :=
    prepare_qs_fw moved.1 root.resolved.1 ⟨1,true⟩ ⟨some 0,0,true,limit⟩
      (by decide +kernel) (fun h => h) (by decide +kernel) unique covered allocationsValid rfl
      2 1 (by decide +kernel) (by decide +kernel) [4,3]
      (by intro value member; simp at member; rcases member with rfl | rfl <;> decide +kernel)
      root.program.parameters root.arguments root.resolvedRun contexts
  have actual : currentBuffer moved.1.objects.heap 1 ⟨some 0,0,true,limit⟩ =
      some (⟨0,parents,5,limit,0⟩ : Buffer Int) := rfl
  rw [actual] at current
  cases Option.some.inj current
  obtain ⟨fuel,out,r,final,ran,compressed,rest⟩ :=
    Proofs.UfCompactRootCall.root_call moved.1 prepared initial root.arguments vc parents ranks parentForest
      (by decide +kernel) 3 (by decide +kernel) (receiverPrefix moved.1) ⟨2,true⟩ _ tyEq
      ⟨writable,flag⟩ run compacted (qs_two initial _ 2 4 3 qs) fw
      (by rw [base]; decide +kernel) (Nat.le_of_eq sc) (prefix_length moved.1) (prefix_take moved.1) contexts covered
  exact ⟨fuel,out,r,final,ran,compressed⟩

-- Empty source object after move still has _n=4 and count=1.
namespace EmptySource
 def arguments : List Proofs.CppNestedCall.NArgument :=
   [.vectorReference 0,.scalarReference 1,.value (.variable ty 2)]
 def program := Proofs.UnionFindCandidateInstance.UnionFind_num_groups
 def resolved := (resolveArguments moved.1 ty program.parameters arguments).getD (moved.1,[])
 theorem resolvedRun : resolveArguments moved.1 ty program.parameters arguments =
     some (resolved.1,receiverArguments ⟨0,true⟩ ty 0 true [4]) := by
   have live : (resolveArguments moved.1 ty program.parameters arguments).isSome = true := by decide +kernel
   have nonempty : resolveArguments moved.1 ty program.parameters arguments ≠ none := by intro missing; simp [missing] at live
   exact (Option.getD_of_ne_none nonempty (moved.1,[])).symm
 example := prepare_qs_fw moved.1 resolved.1 ⟨0,true⟩ ⟨none,0,true,limit⟩
   (by decide +kernel) (fun h => h) (by decide +kernel) unique covered allocationsValid rfl
   0 1 (by decide +kernel) (by decide +kernel) [4]
   (by intro value member; simp at member; subst value; decide +kernel)
   program.parameters arguments resolvedRun contexts

 example : ∃ fuel out, callFuel program fuel moved.1 ty arguments = .finished (out,.scalar 1) := by
   obtain ⟨prepared,initial,vc,buffer,run,compacted,qs,fw,tyEq,writable,flag,sc,current,base,scope⟩ :=
     prepare_qs_fw moved.1 resolved.1 ⟨0,true⟩ ⟨none,0,true,limit⟩
       (by decide +kernel) (fun h => h) (by decide +kernel) unique covered allocationsValid rfl
       0 1 (by decide +kernel) (by decide +kernel) [4]
       (by intro value member; simp at member; subst value; decide +kernel)
       program.parameters arguments resolvedRun contexts
   obtain ⟨fuel,out,ran,rest⟩ := Proofs.UfCompactCounterCall.counter_call moved.1 prepared initial arguments vc
     buffer.items (receiverPrefix moved.1) 0 4 1 (prefix_cell moved.1 0 ⟨ty,1⟩ (by decide +kernel))
     (by decide +kernel) (box buffer) tyEq run compacted (qs_one initial _ 0 4 qs) fw
     (by rw [base]; decide +kernel) (Nat.le_of_eq sc) (prefix_length moved.1) (prefix_take moved.1) contexts covered
   exact ⟨fuel,out,ran⟩
end EmptySource

namespace Readonly
 def parameters : List Proofs.CppVectorBindings.Parameter :=
   [.vector ty false,.scalar ty true true,.scalar ty false true]
 def arguments : List Proofs.CppNestedCall.NArgument :=
   [.vectorReference 3,.scalarReference 4,.value (.variable ty 5)]
 def resolved := (resolveArguments moved.1 ty parameters arguments).getD (moved.1,[])
 theorem resolvedRun : resolveArguments moved.1 ty parameters arguments =
     some (resolved.1,receiverArguments ⟨1,false⟩ ty 2 true [4]) := by
   have live : (resolveArguments moved.1 ty parameters arguments).isSome = true := by decide +kernel
   have nonempty : resolveArguments moved.1 ty parameters arguments ≠ none := by intro missing; simp [missing] at live
   exact (Option.getD_of_ne_none nonempty (moved.1,[])).symm
 example : ∃ prepared initial vc buffer,
     prepareArguments moved.1 ty parameters arguments = some prepared ∧
     compact (project prepared ty) = some initial ∧
     FW vc buffer.items (box buffer) 0 initial.frame ∧ vc.wV = false ∧ vc.flag = true := by
   obtain ⟨prepared,initial,vc,buffer,run,compacted,qs,fw,tyEq,writable,flag,sc,current,base,scope⟩ :=
     prepare_qs_fw moved.1 resolved.1 ⟨1,false⟩ ⟨some 0,0,true,limit⟩
       (by decide +kernel) (by simp) (by decide +kernel) unique covered allocationsValid rfl
       2 1 (by decide +kernel) (by decide +kernel) [4]
       (by intro value member; simp at member; subst value; decide +kernel)
       parameters arguments resolvedRun contexts
   exact ⟨prepared,initial,vc,buffer,run,compacted,fw,writable,flag⟩
end Readonly

-- Both writable and readonly views preserve the entry and its buffer validity.
example := current_entry moved.1.objects.heap ty 1 ⟨some 0,0,true,limit⟩
  (by decide +kernel) (by decide +kernel) unique covered
example := current_entry moved.1.objects.heap ty 0 ⟨none,0,true,limit⟩
  (by decide +kernel) (by decide +kernel) unique covered
example := prefix_cell moved.1 2 ⟨ty,1⟩ (by decide +kernel)
example := prefix_take moved.1
example := prefix_length moved.1
end UfReceiverLayoutExamples
'''


class UfReceiverLayoutTests(unittest.TestCase):
    def test_all_methods_construct_fields_and_frame_from_source_conditions(self):
        with tempfile.TemporaryDirectory(prefix='uf-receiver-layout-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.UfReceiverLayout\nimport Proofs.UfCompactRootCall\nimport Proofs.UfCompactCounterCall\n'
                'import Proofs.UfClassCopyBridge\nimport Proofs.UfFieldsSize\n'
                'import Proofs.UfFieldsUnite\n' + UF_CHECKS + RECEIVER_CHECKS + CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
