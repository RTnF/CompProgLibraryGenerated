"""General const query body proofs applied to the actual AST-generated bodies."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'verifier'), str(ROOT/'tools'), str(ROOT/'tests')]
from context_method_ir import emit_context_methods
from test_scalar_ir import lean_environment
from offline import disable_network


class UfReadQueriesTests(unittest.TestCase):
    def test_source_bodies_general_postconditions_and_boundaries(self):
        generated = emit_context_methods(ROOT/'tests/imports/union_find_public_compat.hpp',
            'cp::UnionFind', 'UnionFindPublicCompat')
        checks = (ROOT/'tests/lean/union_find_read_queries.lean').read_text()
        with tempfile.TemporaryDirectory(prefix='uf-read-queries-') as directory:
            proof = Path(directory)/'check.lean'
            proof.write_text('import Proofs.UfReadQueries\n'+generated+checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            self.assertNotIn('warning:', result.stdout+result.stderr)


if __name__ == '__main__':
    disable_network()
    unittest.main()
