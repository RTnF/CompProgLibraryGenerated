"""Multiple constructor member roots move before the callee scope is retired."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'tools'), str(ROOT/'tests')]
from offline import disable_network
from test_scalar_ir import lean_environment


class ConstructorRootsTests(unittest.TestCase):
    def test_owned_members_nested_children_and_caller_roots(self):
        with tempfile.TemporaryDirectory(prefix='constructor-roots-') as directory:
            proof = Path(directory)/'check.lean'
            proof.write_text('import Proofs.CppConstructorRetirement\n' +
                             (ROOT/'tests/lean/cpp_constructor_roots.lean').read_text()+'\n'+
                             (ROOT/'tests/lean/cpp_constructor_retirement.lean').read_text())
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                                    env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            self.assertNotIn('warning:', result.stdout+result.stderr)


if __name__ == '__main__':
    disable_network()
    unittest.main()
