"""Original getNum source calls: preparation, restoration and caller-only resource bounds."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_call_restore import UF_CHECKS
from offline import disable_network

class DisjointSetGetterCallTests(unittest.TestCase):
    def check_lean(self,checks):
        with tempfile.TemporaryDirectory(prefix='disjoint-set-getter-call-') as directory:
            proof=Path(directory)/'check.lean'
            proof.write_text('import Proofs.DisjointSetGetterCall\nimport Proofs.UfClassCopyBridge\n'+checks)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertNotIn('warning:',result.stdout+result.stderr)

    def test_scalar_body_and_fuel_two_normal_empty_moved_from(self):
        self.check_lean((ROOT/'tests/lean/disjoint_set_getter.lean').read_text()+
            (ROOT/'tests/lean/disjoint_set_getter_call_body.lean').read_text())

    def test_source_resource_theorem_and_permissions(self):
        self.check_lean(UF_CHECKS+(ROOT/'tests/lean/disjoint_set_getter_call_source.lean').read_text())

if __name__=='__main__':
    disable_network()
    unittest.main()
