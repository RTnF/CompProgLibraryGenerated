"""Failed extraction cannot read an indeterminate original ModInt temporary."""
from pathlib import Path
import os
import runpy
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent


class OriginalModIntStreamTests(unittest.TestCase):
    def test_stream_states_and_formatting_in_both_stack_initialization_modes(self):
        generator = runpy.run_path(str(ROOT / 'tests/diff/modint_original_stream.py'))
        with tempfile.TemporaryDirectory(prefix='original-modint-stream-') as directory:
            for mode in ('zero', 'pattern'):
                with self.subTest(mode=mode):
                    binary = Path(directory) / ('driver-'+mode)
                    subprocess.run(['g++', '-std=c++17', '-O1', '-fsanitize=address,undefined',
                                    '-fno-sanitize-recover=all', '-ftrivial-auto-var-init='+mode,
                                    '-I', str(ROOT / 'experiments/library/cpp'),
                                    str(ROOT / 'tests/imports/original_modint_stream.cpp'),
                                    '-o', str(binary)], check=True, timeout=60)
                    env = dict(os.environ, ASAN_OPTIONS='detect_leaks=0:halt_on_error=1',
                               UBSAN_OPTIONS='halt_on_error=1')
                    for modulus in generator['MODULI']:
                        cases, expected = generator['cases_for_modulus'](modulus)
                        actual = subprocess.run([str(binary), str(modulus)], input=cases,
                                                text=True, capture_output=True, check=True,
                                                timeout=30, env=env)
                        self.assertEqual(actual.stdout.splitlines(), expected, f'{mode}, m={modulus}')


if __name__ == '__main__':
    unittest.main()
