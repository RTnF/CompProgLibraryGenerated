"""GroupAffine apply retains the original const-reference and alias semantics."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
PROOF = '''import Proofs.GroupCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppVectorOwnership Proofs.GroupCall Proofs.DoublingCall
 def ty : Ty := ⟨64,true,false⟩
 def caller : NState := {
   scalars := ⟨[⟨ty,2⟩,⟨ty,3⟩],[⟨0,true⟩,⟨1,true⟩,⟨0,true⟩],0,0,0⟩,
   frame := ⟨⟨⟨[]⟩,{}⟩,[],[]⟩,
   slots := [.scalar 0,.scalar 1,.scalar 2]}
 theorem strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope := by
   intro owner c found
   have missing : caller.frame.state.forest.lookup owner = none := by simp [caller,Forest.lookup]
   rw [Forest.context,Forest.rootOwner,missing] at found
   contradiction
 example := affine_apply_correct caller 0 1 2 ⟨0,true⟩ ⟨1,true⟩ ⟨0,true⟩ 2 3 2
   (by decide +kernel) (by decide +kernel) (by decide +kernel)
   (by decide +kernel) (by decide +kernel) (by decide +kernel)
   (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl strict (by decide +kernel)
 def args : List NArgument := [.scalarReference 0,.scalarReference 1,.scalarReference 2]
 def entry := (prepare caller Proofs.GroupInstance.GroupAffine_long_long_apply.parameters args).getD caller
 #guard entry.scalars.memory == callerP caller
 #guard entry.scalars.bindings == [⟨0,false⟩,⟨1,false⟩,⟨0,false⟩]
 #guard Proofs.GroupInstance.GroupAffine_long_long_apply.parameters == [.scalar ty true false,.scalar ty true false,.scalar ty true false]
 def result := Proofs.GroupInstance.GroupAffine_long_long_apply.callFuel 20 caller args
 #guard (match result with | .finished (s,.scalar x) => x == 7 && s.scalars.memory == caller.scalars.memory && s.scalars.bindings == caller.scalars.bindings && s.scope == caller.scope | _ => false)
 def allAlias := Proofs.GroupInstance.GroupAffine_long_long_apply.callFuel 20 caller [.scalarReference 0,.scalarReference 0,.scalarReference 0]
 #guard (match allAlias with | .finished (s,.scalar x) => x == 6 && s.scalars.memory == caller.scalars.memory | _ => false)
 def reordered := Proofs.GroupInstance.GroupAffine_long_long_apply.callFuel 20 caller [.scalarReference 1,.scalarReference 0,.scalarReference 1]
 #guard (match reordered with | .finished (s,.scalar x) => x == 11 && s.scalars.memory == caller.scalars.memory | _ => false)
'''

class GroupApplyReferenceTests(unittest.TestCase):
    def test_reference_call_theorem_and_aliases(self):
        with tempfile.TemporaryDirectory(prefix='group-apply-reference-') as directory:
            proof = Path(directory)/'checks.lean'; proof.write_text(PROOF)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network(); unittest.main()
