"""Staging Euclidean helpers: fresh proof and independent native/value checks."""
import math
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import diff_harness
import lean_translate

SOURCE = ROOT / 'tests/fixtures/ratio_numeric.hpp'


class RatioNumericTests(unittest.TestCase):
    def test_generated_euclid_proof(self):
        model = lean_translate.translate_file(SOURCE, [])
        with tempfile.TemporaryDirectory() as directory:
            proof = Path(directory) / 'Proof.lean'
            proof.write_text('import Proofs.Cpp.Lib.Basic\nimport Proofs.Cpp.Lib.RatioMath\n' + model +
                             (ROOT / 'tests/lean/ratio_numeric_contract.lean').read_text())
            result = subprocess.run([str(ROOT / '.tools/elan/bin/lake'), 'env', 'lean', str(proof)],
                                    cwd=ROOT, env=dict(os.environ, ELAN_HOME=str(ROOT / '.tools/elan')),
                                    capture_output=True, text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_signed_helpers_against_python(self):
        rng = random.Random(20261115)
        pairs = [(a, b) for a in [-120, -1, 0, 1, 120] for b in [-120, -1, 0, 1, 120]]
        pairs += [(rng.randrange(-120, 121), rng.randrange(-120, 121)) for _ in range(160)]
        pairs += [(89, 144), (144, 89), (32767, 1), (-32767, 1), (0, -32767)]
        commands, expected = [], []
        for a, b in pairs:
            commands += [f'call ratio_gcd {a} {b}', f'call ratio_lcm {a} {b}',
                         f'call ratio_gcd_nonnegative {abs(a)} {abs(b)}']
            expected += [f'ok {math.gcd(a, b)}', f'ok {math.lcm(a, b)}', f'ok {math.gcd(a, b)}']
        commands = '\n'.join(commands) + '\n'
        model = lean_translate.translate_file(SOURCE, [])
        env = dict(os.environ, ELAN_HOME=str(ROOT / '.tools/elan'),
                   ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
        for scalar in ['short', 'int', 'long long']:
            with self.subTest(scalar=scalar), tempfile.TemporaryDirectory() as directory:
                scratch = Path(directory)
                harness = diff_harness.Harness(SOURCE, {'T': scalar}, 'Unused')
                cpp = scratch / 'driver.cpp'
                cpp.write_text(harness.cpp_driver())
                binary = scratch / 'driver'
                subprocess.run(['g++', '-std=c++17', '-O1', '-fsanitize=address,undefined',
                                '-I', str(ROOT / 'tests/diff'), str(cpp), '-o', str(binary)],
                               check=True, timeout=60)
                native = subprocess.run([str(binary)], input=commands, capture_output=True,
                                        text=True, check=True, env=env, timeout=30)
                self.assertEqual(native.stdout.splitlines(), expected)
                lean = scratch / 'Driver.lean'
                lean.write_text(harness.lean_driver().replace('import Unused\n', model, 1))
                actual = subprocess.run([str(ROOT / '.tools/elan/bin/lake'), 'env', 'lean', '--run', str(lean)],
                                        input=commands, capture_output=True, text=True, env=env,
                                        cwd=ROOT, timeout=60)
                self.assertEqual(actual.returncode, 0, actual.stdout + actual.stderr)
                self.assertEqual(actual.stdout, native.stdout)


if __name__ == '__main__':
    unittest.main()
