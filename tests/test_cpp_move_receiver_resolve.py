"""Pure receiver argument evaluation and source UF calls from scalar semantics."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_receiver_layout import UF_CHECKS, RECEIVER_CHECKS
from test_uf_receiver_layout import CHECKS as FRAME_CHECKS
from offline import disable_network

CHECKS = r'''

namespace ReceiverResolveExamples
open Proofs.CppMoveReceiverResolve Proofs.CppMoveReceiverLayout
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppNestedEval
open UfMoveCallExamples

def expressions : List (NExpr × Int) :=
  [(.variable ty 5,4),(.binary ty .add (.literal ty 2) (.literal ty 1),3),(.literal ty 1,1)]
theorem ready : Ready moved.1 ty expressions := by
  intro expression value member
  simp [expressions] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    exact ⟨rfl,rfl,by decide +kernel⟩
example := ready_values_valid moved.1 ty expressions ready
example := resolve_values moved.1 ty expressions ready
example := resolve_receiver moved.1 ty 3 4 ⟨1,true⟩ ⟨2,true⟩ 1
  (by decide +kernel) (by decide +kernel) rfl expressions ready
example := stable_environment moved.1 moved.1 ty ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
#guard values expressions == [4,3,1]
#guard ((NExpr.binary ty .add (.literal ty 2147483647) (.literal ty 1)).denote (envOf (project moved.1 ty))).isNone

-- Moved-from getter: the empty vector and preserved _n=4 resolve independently.
def emptyExpressions : List (NExpr × Int) := [(.variable ty 2,4)]
theorem emptyReady : Ready moved.1 ty emptyExpressions := by
  intro expression value member
  simp only [emptyExpressions,List.mem_singleton,Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩
  exact ⟨rfl,rfl,by decide +kernel⟩
example := resolve_receiver moved.1 ty 0 1 ⟨0,true⟩ ⟨0,true⟩ 1
  (by decide +kernel) (by decide +kernel) rfl emptyExpressions emptyReady
end ReceiverResolveExamples

namespace ReceiverFieldsResolveExamples
open Proofs.CppMoveReceiverResolve Proofs.CppMoveReceiverLayout Proofs.CppMoveContext
open Proofs.CppNestedProgram Proofs.UfReceiverLayout Proofs.CppMoveFrame Proofs.CppMoveCallBindings
open Proofs.CppNestedEval Proofs.QuotientFrame Proofs.CppVector
open UfMoveCallExamples ReceiverLayoutExamples UfReceiverLayoutExamples

namespace root
def external : List (NExpr × Int) := [(.literal ty 3,3)]
theorem ready : Ready moved.1 ty external := by
  intro expression value member
  simp [external] at member; rcases member with ⟨rfl,rfl⟩; exact ⟨rfl,rfl,by decide +kernel⟩
example : ∃ last, resolveArguments moved.1 ty ReceiverLayoutExamples.root.program.parameters
    ReceiverLayoutExamples.root.arguments =
    some (last,receiverArguments ⟨1,true⟩ ty 2 true (4::values external)) := by
  exact resolve_fields moved.1 ty 3 4 5 ⟨1,true⟩ ⟨2,true⟩ ⟨3,true⟩ 1 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl external ready
end root

namespace size
def external : List (NExpr × Int) := [(.literal ty 3,3)]
theorem ready : Ready moved.1 ty external := by
  intro expression value member
  simp [external] at member; rcases member with ⟨rfl,rfl⟩; exact ⟨rfl,rfl,by decide +kernel⟩
example : ∃ last, resolveArguments moved.1 ty ReceiverLayoutExamples.size.program.parameters
    ReceiverLayoutExamples.size.arguments =
    some (last,receiverArguments ⟨1,true⟩ ty 2 true (4::values external)) := by
  exact resolve_fields moved.1 ty 3 4 5 ⟨1,true⟩ ⟨2,true⟩ ⟨3,true⟩ 1 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl external ready
end size

namespace same
def external : List (NExpr × Int) := [(.literal ty 3,3),(.literal ty 1,1)]
theorem ready : Ready moved.1 ty external := by
  intro expression value member
  simp [external] at member; rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> exact ⟨rfl,rfl,by decide +kernel⟩
example : ∃ last, resolveArguments moved.1 ty ReceiverLayoutExamples.same.program.parameters
    ReceiverLayoutExamples.same.arguments =
    some (last,receiverArguments ⟨1,true⟩ ty 2 true (4::values external)) := by
  exact resolve_fields moved.1 ty 3 4 5 ⟨1,true⟩ ⟨2,true⟩ ⟨3,true⟩ 1 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl external ready
end same

namespace unite
def external : List (NExpr × Int) := [(.literal ty 3,3),(.literal ty 1,1)]
theorem ready : Ready moved.1 ty external := by
  intro expression value member
  simp [external] at member; rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> exact ⟨rfl,rfl,by decide +kernel⟩
example : ∃ last, resolveArguments moved.1 ty ReceiverLayoutExamples.unite.program.parameters
    ReceiverLayoutExamples.unite.arguments =
    some (last,receiverArguments ⟨1,true⟩ ty 2 true (4::values external)) := by
  exact resolve_fields moved.1 ty 3 4 5 ⟨1,true⟩ ⟨2,true⟩ ⟨3,true⟩ 1 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl external ready
end unite

namespace num_groups
def external : List (NExpr × Int) := []
theorem ready : Ready moved.1 ty external := by
  intro expression value member
  simp [external] at member
example : ∃ last, resolveArguments moved.1 ty ReceiverLayoutExamples.num_groups.program.parameters
    ReceiverLayoutExamples.num_groups.arguments =
    some (last,receiverArguments ⟨1,true⟩ ty 2 true (4::values external)) := by
  exact resolve_fields moved.1 ty 3 4 5 ⟨1,true⟩ ⟨2,true⟩ ⟨3,true⟩ 1 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl external ready
end num_groups

-- Derive normal root execution from field cells and a nontrivial pure argument.
def external : List (NExpr × Int) := [(.binary ty .add (.literal ty 2) (.literal ty 1),3)]
theorem externalReady : Ready moved.1 ty external := by
  intro expression value member
  simp [external] at member
  rcases member with ⟨rfl,rfl⟩
  exact ⟨rfl,rfl,by decide +kernel⟩
def args : List Proofs.CppNestedCall.NArgument :=
  [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),
    .value (.binary ty .add (.literal ty 2) (.literal ty 1))]
example : ∃ (fuel : Nat) (out : Context) (r : Nat) (final : List Int),
    callFuel ReceiverLayoutExamples.root.program fuel moved.1 ty args = .finished (out,.scalar (r : Int)) ∧
    Proofs.UfCompression.Compressed parents final 3 r := by
  obtain ⟨last,resolved⟩ := resolve_fields moved.1 ty 3 4 5 ⟨1,true⟩ ⟨2,true⟩ ⟨3,true⟩ 1 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl external externalReady
  have fullReady := ready_field moved.1 ty 5 ⟨3,true⟩ 4 (by decide +kernel) external externalReady
  have valid := ready_values_valid moved.1 ty _ fullReady
  obtain ⟨prepared,initial,vc,buffer,run,compacted,qs,fw,tyEq,writable,flag,sc,current,base,scope⟩ :=
    prepare_qs_fw moved.1 last ⟨1,true⟩ ⟨some 0,0,true,limit⟩
      (by decide +kernel) (fun h => h) (by decide +kernel) unique covered allocationsValid rfl
      2 1 (by decide +kernel) (by decide +kernel) [4,3] valid
      ReceiverLayoutExamples.root.program.parameters args resolved contexts
  have actual : currentBuffer moved.1.objects.heap 1 ⟨some 0,0,true,limit⟩ =
      some (⟨0,parents,5,limit,0⟩ : Buffer Int) := rfl
  rw [actual] at current
  cases Option.some.inj current
  obtain ⟨fuel,out,r,final,ran,compressed,rest⟩ :=
    Proofs.UfCompactRootCall.root_call moved.1 prepared initial args vc parents ranks parentForest
      (by decide +kernel) 3 (by decide +kernel) (receiverPrefix moved.1) ⟨2,true⟩ _ tyEq
      ⟨writable,flag⟩ run compacted (qs_two initial _ 2 4 3 qs) fw
      (by rw [base]; decide +kernel) (Nat.le_of_eq sc) (prefix_length moved.1) (prefix_take moved.1) contexts covered
  exact ⟨fuel,out,r,final,ran,compressed⟩

#guard (resolveArguments moved.1 ty ReceiverLayoutExamples.root.program.parameters
  [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),
   .value (.binary ty .add (.literal ty 2147483647) (.literal ty 1))]).isNone
#guard (resolveArguments moved.1 ty ReceiverLayoutExamples.root.program.parameters
  [.vectorReference 3,.scalarReference 999,.value (.variable ty 5),.value (.literal ty 3)]).isNone

abbrev u32 : Proofs.CppScalar.Ty := ⟨32,false,false⟩
def unsigned : List (NExpr × Int) := [(.binary u32 .add (.literal u32 4294967295) (.literal u32 1),0)]
example := resolve_values moved.1 u32 unsigned (by
  intro expression value member
  simp [unsigned] at member
  rcases member with ⟨rfl,rfl⟩
  exact ⟨rfl,rfl,by decide +kernel⟩)
end ReceiverFieldsResolveExamples
'''


class ReceiverResolveTests(unittest.TestCase):
    def test_source_fields_pure_expressions_and_normal_root_call(self):
        with tempfile.TemporaryDirectory(prefix='receiver-resolve-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.CppMoveReceiverResolve\nimport Proofs.UfReceiverLayout\n'
                'import Proofs.UfCompactRootCall\nimport Proofs.UfCompactCounterCall\n'
                'import Proofs.UfClassCopyBridge\nimport Proofs.UfFieldsSize\n'
                'import Proofs.UfFieldsUnite\n' + UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS + CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
