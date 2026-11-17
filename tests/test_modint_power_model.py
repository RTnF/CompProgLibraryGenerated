"""The complete ModInt class, including I/O, has no recursive call dependency."""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import lean_translate
import test_lean_model_friend as friends


class ModIntPowerModelTests(unittest.TestCase):
    def class_source(self):
        original = (ROOT / 'experiments/library/cpp/modint/modint.hpp').read_text()
        source = original.replace('#include "template/small_template.hpp"',
            '#include "' + str(ROOT / 'experiments/library/cpp/template/small_template.hpp') + '"')
        source = source.replace('\n/**', '\nnamespace cp {\n/**', 1)
        for name in ('enable_if_t', 'is_signed_v'):
            source = re.sub(r'(?<!\w)(?<!::)' + name + r'\b', 'std::' + name, source)
        # This test covers every class method and friend. Globals are retained in
        # the canonical original and require their own state translation next.
        source = source[:source.index('\nusing mint =')] + '\n}\n'
        return source

    def test_complete_class_and_binary_power_contract(self):
        source = self.class_source()
        with tempfile.TemporaryDirectory(dir=ROOT / 'tests/diff', prefix='.modint-power-') as directory:
            header = Path(directory) / 'OriginalClass.hpp'
            header.write_text(source)
            model = lean_translate.translate_file(header, ['Proofs.Cpp.PowMod', 'Proofs.Cpp.Lib.ModIntMath'])
            self.assertIn('def cp.ModInt.pow_nonnegative', model)
            self.assertIn('def cp.op_shr_istream_ModInt', model)
            self.assertIn('def cp.op_shl_ostream_ModInt', model)
            lean = Path(directory) / 'Contract.lean'
            lean.write_text(model + (ROOT / 'tests/lean/modint_power_contract.lean').read_text()
                            + (ROOT / 'tests/lean/modint_stream_contract.lean').read_text())
            subprocess.run([str(ROOT / '.tools/elan/bin/lake'), 'env', 'lean', str(lean)],
                           check=True, cwd=ROOT, timeout=60,
                           env=dict(os.environ, ELAN_HOME=str(ROOT / '.tools/elan')))

    def test_public_power_matches_cpp_and_integer_oracle(self):
        source = self.class_source().rsplit('}', 1)[0]
        commands, expected, calls = [], [], []
        for modulus in (2, 7, 998244353, 2147483647, 4294967291):
            name = 'power_' + str(modulus)
            calls.append(name)
            source += (f'uint32_t {name}(uint32_t base, ll exponent) {{ '
                       f'return ModInt<{modulus}u>(base).pow(exponent).get(); }}\n')
            for base in (0, 1, 2, modulus-1, 2**32-1):
                for exponent in (-(2**63), -1, 0, 1, 17, 2**63-1):
                    if exponent < 0 and base % modulus == 0:
                        continue
                    commands.append(f'call {name} {base} {exponent}')
                    expected.append(f'ok {pow(base, exponent, modulus)}')
            inverse = 'inverse_' + str(modulus)
            self_divide = 'self_divide_' + str(modulus)
            calls += [inverse, self_divide]
            source += (f'uint32_t {inverse}(uint32_t value) {{ return ModInt<{modulus}u>(value).inv().get(); }}\n'
                       f'uint32_t {self_divide}(uint32_t value) {{ ModInt<{modulus}u> a(value); a /= a; return a.get(); }}\n')
            values = sorted({0, 1, 2, modulus-1, modulus, 2**31, 2**32-1})
            for value in values:
                if value % modulus != 0:
                    commands += [f'call {inverse} {value}', f'call {self_divide} {value}']
                    expected += [f'ok {pow(value, -1, modulus)}', 'ok 1']
            for compound in (False, True):
                name = ('quotient_assign_' if compound else 'quotient_') + str(modulus)
                calls.append(name)
                source += (f'uint32_t {name}(uint32_t x, uint32_t y) {{ '
                           f'ModInt<{modulus}u> a(x), b(y); ')
                source += 'a /= b; return a.get(); }\n' if compound else 'return (a / b).get(); }\n'
                for x in values:
                    for y in values:
                        if y % modulus != 0:
                            commands.append(f'call {name} {x} {y}')
                            expected.append(f'ok {(x * pow(y, -1, modulus)) % modulus}')
        source += '}\n'
        # Compile the shared class and driver once for all modulus bindings.
        friends.FriendTranslationTests().compare(source, '\n'.join(commands)+'\n', expected,
            instance={'m': '7u'}, calls=calls)


if __name__ == '__main__':
    unittest.main()
