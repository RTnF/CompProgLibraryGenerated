"""Read-only root cursor with extra fields and a public compatibility prototype."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'verifier'), str(ROOT/'tools'), str(ROOT/'tests')]
from context_method_ir import emit_context_methods, lower_context_methods
from check_public import check_compiler
from test_scalar_ir import lean_environment
from offline import disable_network

SOURCE = ROOT/'tests/imports/union_find_public_compat.hpp'


class UfReadCursorTests(unittest.TestCase):
    def test_generated_root_and_inlined_query_loops(self):
        ir = lower_context_methods(SOURCE, 'cp::UnionFind')
        self.assertEqual(len(ir['methods']), 9)
        readonly = [m for m in ir['methods'] if not m['fields'][0]['writable']]
        self.assertEqual(len(readonly), 4)

        def check_statements(statements):
            for statement in statements:
                self.assertIn(statement['kind'],
                    {'assign', 'return', 'scope', 'while', 'check', 'declare'})
                if statement['kind'] == 'assign':
                    self.assertGreater(statement['slot'], 2)
                for key in ('body', 'then', 'else'):
                    check_statements(statement.get(key, []))

        for method in readonly:
            # Scalar values are writable callee copies. Receiver references
            # retain their const permissions independently of those copies.
            self.assertTrue(all(not field['writable'] for field in method['fields']
                if field['kind'] == 'vector' or field['reference']))
            check_statements(method['program']['body'])
        generated = emit_context_methods(SOURCE, 'cp::UnionFind', 'UnionFindPublicCompat')
        checks = (ROOT/'tests/lean/union_find_read_cursor.lean').read_text()
        with tempfile.TemporaryDirectory(prefix='uf-read-cursor-') as directory:
            proof = Path(directory)/'check.lean'
            proof.write_text('import Proofs.UfReadCursor\nimport Proofs.UfFieldsCounter\n'+generated+checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            self.assertNotIn('warning:', result.stdout+result.stderr)

    def test_original_and_const_api_against_partition_oracle(self):
        check_compiler()
        with tempfile.TemporaryDirectory(prefix='uf-compat-native-') as directory:
            binary = Path(directory)/'native'
            subprocess.run(['g++', '-std=c++17', '-O1', '-Wall', '-Wextra',
                '-fsanitize=address,undefined', '-fno-sanitize-recover=all',
                str(ROOT/'tests/imports/union_find_public_compat.cpp'), '-o', str(binary)],
                check=True)
            env = dict(os.environ, ASAN_OPTIONS='detect_leaks=0:halt_on_error=1',
                UBSAN_OPTIONS='halt_on_error=1:print_stacktrace=1')
            subprocess.run([str(binary)], env=env, check=True)


if __name__ == '__main__':
    disable_network()
    unittest.main()
