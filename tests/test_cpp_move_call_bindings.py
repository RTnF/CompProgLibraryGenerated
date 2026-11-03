"""Callee binding resolution and original UF root normal termination/resources after move."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_call_restore import UF_CHECKS
from test_cpp_move_prepared_call import CHECKS as PREPARED_CHECKS
from offline import disable_network

BINDING_CHECKS = r'''

namespace CallBindingExamples
open Proofs.CppMoveCallBindings Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppNestedCall
open UfMoveCallExamples PreparedCallExamples
 def original := project initial ty
 #guard (compact original).isSome
 def normalized := (compact original).getD original
 theorem actual : compact original = some normalized := by
   have live : (compact original).isSome = true := by decide +kernel
   have nonempty : compact original ≠ none := by intro missing; simp [missing] at live
   exact (Option.getD_of_ne_none nonempty original).symm
 #guard normalized.frame.bindings.length == 1
 #guard normalized.slots == [.vector 0,.scalar 0,.scalar 1,.scalar 2,.scalar 3]
 #guard normalized.scalars.memory == original.scalars.memory
 example := compact_metadata original normalized actual
 example := compact_scalarCell original normalized actual 1 ty
 example := compact_resolve original normalized actual 0 4 (by decide +kernel) (.integer ty)
 example := compact_one_vector original 4 ⟨0,.integer ty,true,.root 0⟩ [0,1,2,3] (by decide +kernel) (by decide +kernel)
 def step : NStep := match Proofs.CppNestedProgram.runFuel 128 program.body normalized with
   | .finished step => step
   | _ => ⟨normalized,none,false⟩
 theorem bodyRun : Proofs.CppNestedProgram.runFuel 128 program.body normalized = .finished step := by decide +kernel
 #guard Proofs.CppNestedCall.finish (project moved.1 ty) step.state program.result step.returned == some ended
 #guard (compact {original with slots := [.vector 999]}).isNone
 def aliasing := {original with slots := [.vector 4,.scalar 0,.vector 4]}
 #guard (compact aliasing).map (fun s => s.frame.bindings.length) == some 2
 #guard (compact aliasing).map (fun s => s.slots) == some [.vector 0,.scalar 0,.vector 1]
end CallBindingExamples
'''

ROOT_CHECKS = r'''

namespace UfRootCallExamples
open Proofs.CppMoveContext Proofs.CppMoveCallBindings Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.UfCompactRootCall Proofs.VecExpr Proofs.VecWrite Proofs.QuotientFrame
open UfMoveCallExamples
 def rootArgs : List NArgument := [.vectorReference 3,.scalarReference 4,.value (.variable ty 5),.value (.literal ty 3)]
 def prepared := (prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_root.parameters rootArgs).getD moved.1
 theorem preparedRun : prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_root.parameters rootArgs = some prepared := by
   have live : (prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_root.parameters rootArgs).isSome = true := by decide +kernel
   have nonempty : prepareArguments moved.1 ty Proofs.UnionFindCandidateInstance.UnionFind_root.parameters rootArgs ≠ none := by intro missing; simp [missing] at live
   exact (Option.getD_of_ne_none nonempty moved.1).symm
 def initial := (compact (project prepared ty)).getD (project prepared ty)
 theorem compacted : compact (project prepared ty) = some initial := by
   have live : (compact (project prepared ty)).isSome = true := by decide +kernel
   have nonempty : compact (project prepared ty) ≠ none := by intro missing; simp [missing] at live
   exact (Option.getD_of_ne_none nonempty (project prepared ty)).symm
 def P := prepared.scalars.memory.take 11
 #guard P.length == 11
 #guard initial.frame.bindings.length == 1 && initial.scalars.memory.length == 13
 def vc : VCtx := ⟨ty,true,true,0,0,buffer,parents,by decide,fun _ => rfl,by decide,
   initial.frame.state.liveSpace,initial.frame.state.storage.work,initial.scope,initial.frame.state.storage.objects.length⟩
 theorem strict : ∀ owner sc, initial.frame.state.forest.context owner = some sc → sc < vc.sc := by
   intro owner sc found
   have state : initial.frame.state = (project moved.1 ty).frame.state := by decide +kernel
   rw [state] at found
   have bound := contexts owner sc found
   change sc < 2
   change sc ≤ 1 at bound
   omega
 theorem fw : FW vc parents buffer 0 initial.frame :=
   ⟨by decide +kernel,by decide +kernel,rfl,by simp [vc],strict,rfl,by decide +kernel,
     by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
     by decide +kernel,rfl,rfl,by decide +kernel⟩
 theorem qs : QS initial [] initial.scalars.baseMemory initial.scope
     (Proofs.UfFieldsRoot.fields P ⟨2,true⟩ parents.length 3).mem
     (Proofs.UfFieldsRoot.fields P ⟨2,true⟩ parents.length 3).bs
     (sl1 (Proofs.UfFieldsRoot.fields P ⟨2,true⟩ parents.length 3).bs.length) :=
   ⟨by decide +kernel,by decide +kernel,by decide +kernel,rfl,rfl⟩
 example := root_call moved.1 prepared initial rootArgs vc parents ranks parentForest (by decide) 3 (by decide)
   P ⟨2,true⟩ buffer rfl ⟨rfl,rfl⟩ preparedRun compacted qs fw (by decide +kernel) (Nat.le_refl _)
   (by decide +kernel) (by decide +kernel) contexts covered
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_root 128 moved.1 ty rootArgs with
   | .finished (out,result) => result == .scalar 0 &&
       (out.objects.heap.allocation 0).map (fun a => a.buffer.items) == some [-4,0,0,0] &&
       Proofs.CppMoveHeaders.read out.objects.heap ty.valid 0 == some 0 &&
       (Proofs.CppMoveHeaders.read out.objects.heap ty.valid 1).isNone
   | _ => false)
 #guard (match callFuel Proofs.UnionFindCandidateInstance.UnionFind_root 0 moved.1 ty rootArgs with
   | .exhausted => true | _ => false)
end UfRootCallExamples
'''

class MoveCallBindingsTests(unittest.TestCase):
    def check_lean(self,checks):
        with tempfile.TemporaryDirectory(prefix='move-call-bindings-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppMoveCallBindings\nimport Proofs.UfCompactRootCall\n'
                'import Proofs.UfClassCopyBridge\nimport Proofs.UfFieldsSame\n'
                'import Proofs.UfFieldsSize\nimport Proofs.UfFieldsUnite\nimport Proofs.UfFieldsCounter\n'+checks)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_bindings_scalar_vector_resolution_aliases_and_actual_body(self):
        self.check_lean(UF_CHECKS+PREPARED_CHECKS+BINDING_CHECKS)

    def test_original_root_normal_termination_compression_and_resources(self):
        self.check_lean(UF_CHECKS+ROOT_CHECKS)

if __name__=='__main__':
    disable_network()
    unittest.main()
