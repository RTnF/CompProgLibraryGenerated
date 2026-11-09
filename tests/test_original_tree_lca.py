"""Original Tree LCA regression and all-table-row mathematical specification.

The whole templated Tree class still has separate translation/lifetime obligations.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tests'),str(ROOT/'tools')]
from offline import disable_network
import test_scalar_class_delegation as scalar_checks

SOURCE=ROOT/'experiments/library/cpp/tree/tree.hpp'
CASE=ROOT/'tests/imports/tree_lca_source.cpp'

class OriginalTreeLcaTests(unittest.TestCase):
    def test_original_lca_table_bound_and_old_overrun(self):
        before={p:hashlib.sha256(p.read_bytes()).hexdigest() for p in (SOURCE,CASE)}
        current=SOURCE.read_text()
        bound='for (int k = (int)ancestor_.size() - 1; k >= 0; k--)'
        self.assertEqual(current.count(bound),1)
        with tempfile.TemporaryDirectory(prefix='original-tree-lca-') as tmp:
            directory=Path(tmp)
            common=['g++','-std=c++20','-O1','-D_GLIBCXX_ASSERTIONS','-fsanitize=undefined',
                '-fno-sanitize-recover=all','-I',str(ROOT/'experiments/library/cpp')]
            native=directory/'current'
            subprocess.run([*common,str(CASE),'-o',str(native)],check=True,timeout=60)
            subprocess.run([str(native)],check=True,timeout=30)
            subprocess.run([str(native),'four-node-regression'],check=True,timeout=10)
            old=directory/'old.hpp'
            old.write_text(current.replace(bound,'for (int k = bit_width((unsigned)du); k >= 0; k--)'))
            control=directory/'old'
            subprocess.run([*common,'-DTREE_SOURCE_HEADER="'+str(old)+'"',str(CASE),'-o',str(control)],
                check=True,timeout=60)
            failed=subprocess.run([str(control),'four-node-regression'],capture_output=True,text=True,timeout=10)
            self.assertNotEqual(failed.returncode,0)
            self.assertIn('__n < this->size()',failed.stderr)
        for p,digest in before.items():self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),digest)

    def test_all_rows_mathematical_specification(self):
        with tempfile.TemporaryDirectory(prefix='original-tree-lca-proof-') as tmp:
            scalar_checks.ScalarDelegationTests().kernel(Path(tmp),'Proofs.TreeLcaCall',[
                'Proofs.TreeLcaMath.lca_all_rows_spec','Proofs.TreeLcaMath.all_rows_indices',
                'Proofs.TreeLcaMath.all_rows_lca_correct',
                'Proofs.TreeLcaCall.tree_lca_same_depth_correct'])

if __name__=='__main__':
    disable_network()
    unittest.main()
