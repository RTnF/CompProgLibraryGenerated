"""The original Ratio scalar-left overloads compile and match exact rational arithmetic."""
from fractions import Fraction
from pathlib import Path
import os
import random
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent


def fraction_text(q):
    return str(q.numerator) if q.denominator == 1 else f'{q.numerator}/{q.denominator}'


class RatioOriginalApiTests(unittest.TestCase):
    def test_scalar_left_operations(self):
        rng = random.Random(20261114)
        cases = [(a, p, d) for a in (-7, -1, 0, 2, 9) for p in (-3, -1, 1, 3) for d in (1, 2, 5)]
        cases += [(rng.randrange(-100, 101), rng.choice([p for p in range(-50, 51) if p]), rng.randrange(1, 51)) for _ in range(300)]
        text = ''.join(f'{a} {p} {d}\n' for a, p, d in cases)
        expected = []
        for a, p, d in cases:
            q = Fraction(p, d)
            expected.append(' '.join(fraction_text(v) for v in (a + q, a - q, a * q, a / q, Fraction(1))))
        env = dict(os.environ, ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
        with tempfile.TemporaryDirectory() as directory:
            binary = Path(directory) / 'driver'
            for scalar in ('int', 'long long'):
                with self.subTest(scalar=scalar):
                    subprocess.run(['g++', '-std=c++23', '-O1', '-fsanitize=address,undefined',
                                    '-fno-omit-frame-pointer', f'-DRATIO_TEST_TYPE={scalar}',
                                    '-I', str(ROOT / 'experiments/library/cpp'),
                                    str(ROOT / 'tests/imports/ratio_scalar_left.cpp'), '-o', str(binary)],
                                   check=True, timeout=60)
                    result = subprocess.run([str(binary)], input=text, text=True, capture_output=True,
                                            check=True, env=env, timeout=30)
                    self.assertEqual(result.stdout.splitlines(), expected)


if __name__ == '__main__':
    unittest.main()
