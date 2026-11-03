"""Readonly source receivers construct actual const calls and finish/restore."""
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


class UfReadCallTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='uf-read-call-') as directory:
            proof = Path(directory)/'check.lean'
            proof.write_text('import Proofs.UfReadValues\nimport Proofs.CppMoveFrameScopes\n'+checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            self.assertNotIn('warning:', result.stdout+result.stderr)

    def test_generated_programs_mapping_and_readonly_source_calls(self):
        generated = emit_context_methods(ROOT/'tests/imports/union_find_public_compat.hpp',
            'cp::UnionFind', 'UnionFindPublicCompat')
        checks = (ROOT/'tests/lean/union_find_read_call.lean').read_text()
        checks = '\n'.join(line for line in checks.splitlines() if not line.startswith('import '))
        self.check_lean(generated+(ROOT/'tests/lean/union_find_read_call_mapping.lean').read_text()+checks+'\n'+(ROOT/'tests/lean/union_find_read_call_budget.lean').read_text())

    def test_readonly_world_and_multiple_owner_lifetimes(self):
        setup = (ROOT/'tests/lean/union_find_read_call.lean').read_text().split('namespace UfReadGeneratedCallChecks')[0]
        parts = [setup, (ROOT/'tests/lean/union_find_read_values.lean').read_text(),
            (ROOT/'tests/lean/union_find_read_multi_owner.lean').read_text()]
        self.check_lean('\n'.join('\n'.join(line for line in part.splitlines()
            if not line.startswith('import ')) for part in parts))

    def test_moved_from_readonly_preparation_and_permission_rejection(self):
        self.check_lean((ROOT/'tests/lean/union_find_read_receiver.lean').read_text())


if __name__ == '__main__':
    disable_network()
    unittest.main()
