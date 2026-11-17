"""Full-width ModInt field arithmetic is linked to the canonical generated class."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import lean_translate
import test_lean_model_friend as friends


class ModIntArithmeticModelTests(unittest.TestCase):
    def test_canonical_operators_against_integer_oracle(self):
        from test_modint_power_model import ModIntPowerModelTests
        source = ModIntPowerModelTests().class_source().rsplit('}', 1)[0]
        commands, expected, calls = [], [], []
        for modulus in (2, 7, 998244353, 2147483647, 4294967291, 4294967294, 4294967295):
            values = sorted({0, 1, 2, modulus-1, modulus, 2**31, 2**32-1})
            for operation, symbol in (('add', '+'), ('sub', '-'), ('mul', '*')):
                for compound in (False, True):
                    name = operation + ('_assign_' if compound else '_') + str(modulus)
                    calls.append(name)
                    source += (f'uint32_t {name}(uint32_t x, uint32_t y) {{ '
                               f'ModInt<{modulus}u> a(x), b(y); ')
                    source += (f'a {symbol}= b; return a.get(); }}\n' if compound else
                               f'return (a {symbol} b).get(); }}\n')
                    for x in values:
                        for y in values:
                            value = x+y if operation == 'add' else x-y if operation == 'sub' else x*y
                            commands.append(f'call {name} {x} {y}')
                            expected.append(f'ok {value % modulus}')
                name = 'self_' + operation + '_' + str(modulus)
                calls.append(name)
                source += (f'uint32_t {name}(uint32_t x) {{ ModInt<{modulus}u> a(x); '
                           f'a {symbol}= a; return a.get(); }}\n')
                for x in values:
                    value = x+x if operation == 'add' else 0 if operation == 'sub' else x*x
                    commands.append(f'call {name} {x}')
                    expected.append(f'ok {value % modulus}')
            for operation, symbol in (('increment', '++'), ('decrement', '--')):
                for mode in ('prefix', 'postfix_old', 'postfix_new'):
                    name = operation + '_' + mode + '_' + str(modulus)
                    calls.append(name)
                    source += f'uint32_t {name}(uint32_t x) {{ ModInt<{modulus}u> a(x); '
                    if mode == 'prefix':
                        source += f'{symbol}a; return a.get(); }}\n'
                    elif mode == 'postfix_old':
                        source += f'ModInt<{modulus}u> b = a{symbol}; return b.get(); }}\n'
                    else:
                        source += f'a{symbol}; return a.get(); }}\n'
                    for x in values:
                        value = x if mode == 'postfix_old' else x + (1 if operation == 'increment' else -1)
                        commands.append(f'call {name} {x}')
                        expected.append(f'ok {value % modulus}')
            for operation, symbol in (('equal', '=='), ('unequal', '!=')):
                name = operation + '_' + str(modulus)
                calls.append(name)
                source += (f'bool {name}(uint32_t x, uint32_t y) {{ '
                           f'return ModInt<{modulus}u>(x) {symbol} ModInt<{modulus}u>(y); }}\n')
                for x in values:
                    for y in values:
                        equal = x % modulus == y % modulus
                        commands.append(f'call {name} {x} {y}')
                        expected.append(f'ok {int(equal if operation == "equal" else not equal)}')
            name = 'negate_' + str(modulus)
            calls.append(name)
            source += f'uint32_t {name}(uint32_t x) {{ return (-ModInt<{modulus}u>(x)).get(); }}\n'
            for x in values:
                commands.append(f'call {name} {x}')
                expected.append(f'ok {(-x) % modulus}')
        source += '}\n'
        friends.FriendTranslationTests().compare(source, '\n'.join(commands)+'\n', expected,
                                                instance={'m': '7u'}, calls=calls)

    def test_canonical_arithmetic_contracts(self):
        from test_modint_power_model import ModIntPowerModelTests
        with tempfile.TemporaryDirectory() as directory:
            header = Path(directory) / 'Original.hpp'
            header.write_text(ModIntPowerModelTests().class_source())
            model = lean_translate.translate_file(header, ['Proofs.Cpp.Lib.ModIntMath'])
            lean = Path(directory) / 'Contract.lean'
            lean.write_text(model + (ROOT / 'tests/lean/modint_arithmetic_contract.lean').read_text())
            result = subprocess.run([str(ROOT / '.tools/elan/bin/lake'), 'env', 'lean', str(lean)],
                                    cwd=ROOT, env=dict(os.environ, ELAN_HOME=str(ROOT / '.tools/elan')),
                                    text=True, capture_output=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
