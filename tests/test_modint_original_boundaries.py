"""Original ModInt keeps its template API at signed and modulus boundaries."""
from pathlib import Path
import math
import os
import runpy
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent


class OriginalModIntBoundaryTests(unittest.TestCase):
    def test_original_full_factorial_table(self):
        with tempfile.TemporaryDirectory(prefix='original-modint-factorial-') as directory:
            binary = Path(directory) / 'factorial'
            subprocess.run(['g++', '-std=c++17', '-O1', '-fsanitize=address,undefined',
                            '-fno-sanitize-recover=all', '-I', str(ROOT / 'experiments/library/cpp'),
                            str(ROOT / 'tests/imports/original_modint_factorial.cpp'),
                            '-o', str(binary)], check=True, timeout=60)
            subprocess.run([str(binary)], check=True, timeout=30,
                           env=dict(os.environ, ASAN_OPTIONS='detect_leaks=0:halt_on_error=1',
                                    UBSAN_OPTIONS='halt_on_error=1'))

    def test_constexpr_and_public_power_signatures(self):
        generator = runpy.run_path(str(ROOT / 'tests/diff/modint_original.py'))
        source = ['#include "template/small_template.hpp"', '#include "modint/modint.hpp"',
                  '#include <type_traits>', 'using M = ModInt<7, nullptr>;',
                  'static_assert(std::is_same_v<decltype(&M::pow), M (M::*)(ll) const>);',
                  'static_assert(std::is_same_v<decltype(&M::inv), M (M::*)() const>);',
                  'static_assert(sizeof(M) == sizeof(uint32_t));',
                  'template<class T, class = void> struct HasHelper : std::false_type {};',
                  'template<class T> struct HasHelper<T, std::void_t<decltype(&T::pow_nonnegative)>> : std::true_type {};',
                  'static_assert(!HasHelper<M>::value);',
                  *generator['constexpr_power_assertions']()]
        with tempfile.TemporaryDirectory(prefix='modint-constexpr-') as directory:
            cpp = Path(directory) / 'Constexpr.cpp'
            cpp.write_text('\n'.join(source)+'\n')
            subprocess.run(['g++', '-std=c++17', '-fsyntax-only',
                            '-I', str(ROOT / 'experiments/library/cpp'), str(cpp)],
                           check=True, timeout=60)

    def test_arithmetic_and_signed_exponents(self):
        generator = runpy.run_path(str(ROOT / 'tests/diff/modint_original.py'))
        with tempfile.TemporaryDirectory(prefix='original-modint-boundaries-') as directory:
            binary = Path(directory) / 'driver'
            subprocess.run(['g++', '-std=c++17', '-O1', '-fsanitize=address,undefined',
                            '-fno-sanitize-recover=all', '-I', str(ROOT / 'experiments/library/cpp'),
                            str(ROOT / 'tests/imports/original_modint_boundaries.cpp'),
                            '-o', str(binary)], check=True, timeout=60)
            env = dict(os.environ, ASAN_OPTIONS='detect_leaks=0:halt_on_error=1',
                       UBSAN_OPTIONS='halt_on_error=1')
            for modulus in generator['MODULI']:
                with self.subTest(modulus=modulus):
                    self.assertTrue(all(modulus % d for d in range(2, math.isqrt(modulus)+1)))
                    cases, expected = generator['cases_for_modulus'](modulus)
                    actual = subprocess.run([str(binary), str(modulus)], input=cases,
                                            text=True, capture_output=True, check=True,
                                            env=env, timeout=30)
                    self.assertEqual(list(map(int, actual.stdout.split())), expected)


if __name__ == '__main__':
    unittest.main()
