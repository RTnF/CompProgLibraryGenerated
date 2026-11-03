"""Bridge verified discovery-order properties to rerooting DP, retaining graph premises."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from offline import disable_network


class TreeOrderDpTests(unittest.TestCase):
    def test_bridge_valid_tree_and_extra_edge_counterexample(self):
        with tempfile.TemporaryDirectory(prefix='tree-order-dp-') as directory:
            proof = Path(directory)/'check.lean'
            proof.write_text('import Proofs.TreeOrderToDp\n'+(ROOT/'tests/lean/tree_order_dp.lean').read_text())
            lake,env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertNotIn('warning:',result.stdout+result.stderr)


if __name__ == '__main__':
    disable_network()
    unittest.main()
