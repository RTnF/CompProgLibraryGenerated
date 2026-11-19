"""GroupAffine apply retains the original const-reference and alias semantics."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from lean_env import lean_environment
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
PROOF = '''import Proofs.Cpp.Group
open Proofs.Cpp.Gen
example (a b x : Int) (t : Nat) :
    (cp.GroupAffine.apply (⟨a, b⟩ : cp.GroupAffine Int) x).run t =
      some (a * x + b, t + 1) := Proofs.Cpp.Group.affine_apply a b x t
-- The old field-reference ABI is gone. Check the same observations as pure
-- values, including equal inputs and permutations, for arbitrary initial ticks.
example (a b : Int) (t : Nat) :
    (cp.GroupAffine.apply (⟨a, b⟩ : cp.GroupAffine Int) a).run t =
      some (a * a + b, t + 1) := Proofs.Cpp.Group.affine_apply a b a t
#guard (cp.GroupAffine.apply (⟨2, 3⟩ : cp.GroupAffine Int) 2).run 0 == some (7, 1)
#guard (cp.GroupAffine.apply (⟨2, 2⟩ : cp.GroupAffine Int) 2).run 0 == some (6, 1)
#guard (cp.GroupAffine.apply (⟨3, 2⟩ : cp.GroupAffine Int) 3).run 0 == some (11, 1)
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
