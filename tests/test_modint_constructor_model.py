"""Constructors and set use C++ integral promotions without narrowing the modulus."""
from pathlib import Path
import copy
import os
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import test_lean_model_friend as friends
import diff_harness
import lean_translate


class ModIntConstructorModelTests(unittest.TestCase):
    def test_constructor_and_set_contracts(self):
        from test_modint_power_model import ModIntPowerModelTests
        with tempfile.TemporaryDirectory() as directory:
            header = Path(directory) / 'Source.hpp'
            header.write_text(ModIntPowerModelTests().class_source())
            model = lean_translate.translate_file(header, ['Proofs.Cpp.Lib.ModIntMath'])
            driver = Path(directory) / 'Contract.lean'
            driver.write_text(model + (ROOT / 'tests/lean/modint_constructor_contract.lean').read_text())
            result = subprocess.run([str(ROOT / '.tools/elan/bin/lake'), 'env', 'lean', str(driver)],
                                    text=True, capture_output=True, cwd=ROOT, timeout=60,
                                    env=dict(os.environ, ELAN_HOME=str(ROOT / '.tools/elan')))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_full_signed_and_unsigned_128_bit_inputs(self):
        from test_modint_power_model import ModIntPowerModelTests
        source = ModIntPowerModelTests().class_source().rsplit('}', 1)[0]
        calls, commands, expected = [], [], []
        for modulus in (7, 4294967291):
            for signed in (True, False):
                suffix = ('s' if signed else 'u') + str(modulus)
                high_type = 'll' if signed else 'ull'
                wide_type = '__int128' if signed else 'unsigned __int128'
                for operation in ('construct', 'set'):
                    name = operation + '_' + suffix
                    calls.append(name)
                    source += (f'uint32_t {name}({high_type} high, ull low) {{ '
                               f'{wide_type} value = ({wide_type})high * (({wide_type})1 << 64) + ({wide_type})low; ')
                    if operation == 'construct':
                        source += f'return ModInt<{modulus}u>(value).get(); }}\n'
                    else:
                        source += f'ModInt<{modulus}u> result; result.set(value); return result.get(); }}\n'
                    highs = ([-2**63, -1, 0, 2**63-1] if signed else [0, 1, 2**63, 2**64-1])
                    for high in highs:
                        for low in (0, 1, 2**64-1):
                            value = high * 2**64 + low
                            commands.append(f'call {name} {high} {low}')
                            expected.append(f'ok {value % modulus}')
        source += '}\n'
        friends.FriendTranslationTests().compare(source, '\n'.join(commands)+'\n', expected,
                                                instance={'m': '7u'}, calls=calls)

    def test_integral_bindings_without_reparsing_the_same_header(self):
        from test_modint_power_model import ModIntPowerModelTests
        source = ModIntPowerModelTests().class_source()
        bindings = [('char', 8, True), ('signed char', 8, True), ('short', 16, True),
                    ('int', 32, True), ('long', 64, True), ('long long', 64, True),
                    ('__int128', 64, True), ('unsigned char', 8, False),
                    ('unsigned short', 16, False), ('unsigned int', 32, False),
                    ('unsigned long', 64, False), ('unsigned long long', 64, False),
                    ('bool', 1, False), ('wchar_t', 32, True),
                    ('char16_t', 16, False), ('char32_t', 32, False)]
        with tempfile.TemporaryDirectory(dir=ROOT / 'tests/diff', prefix='.modint-ctors-') as directory:
            scratch = Path(directory)
            header = scratch / 'Source.hpp'
            header.write_text(source)
            declarations = lean_translate.source_decls(header)
            def unchanged_ast(path, standard='c++17'):
                self.assertEqual(Path(path).resolve(), header.resolve())
                self.assertEqual(standard, 'c++17')
                self.assertEqual(header.read_text(), source)
                return copy.deepcopy(declarations)
            env = dict(os.environ, ELAN_HOME=str(ROOT / '.tools/elan'),
                       ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
            # Each binding gets its own native and Lean driver. The same frozen
            # canonical class AST is parsed once for all these instantiations.
            with patch.object(lean_translate, 'source_decls', side_effect=unchanged_ast):
                model = lean_translate.translate_file(header, [])
                for cpp, bits, signed in bindings:
                    for modulus in (7, 4294967291):
                        with self.subTest(cpp=cpp, modulus=modulus):
                            parameter = 'T' if signed else 'U'
                            ctor, setter = 'ModInt.init_'+parameter, 'ModInt.set__'+parameter
                            maximum = 2**(bits-int(signed))-1
                            minimum = -2**(bits-1) if signed else 0
                            values = sorted({minimum, maximum, 0, 1, min(maximum, modulus),
                                             max(minimum, -modulus) if signed else maximum//2})
                            commands, expected = [], []
                            for i, value in enumerate(values):
                                other = values[-i-1]
                                commands += [f'new {ctor} {value}', f'do ModInt.get_ {i}',
                                             f'do {setter} {i} {other}', f'do ModInt.get_ {i}']
                                expected += ['new', f'ok {value % modulus}', 'ok', f'ok {other % modulus}']
                            h = diff_harness.Harness(header, {'m': str(modulus)+'u', parameter: cpp}, 'Unused',
                                                     calls=[ctor, setter, 'ModInt.get_'])
                            native_source, binary = scratch / 'driver.cpp', scratch / 'driver'
                            native_source.write_text(h.cpp_driver())
                            subprocess.run(['g++', '-std=c++17', '-O1', '-fsanitize=address,undefined',
                                            '-I', str(ROOT / 'tests/diff'), str(native_source), '-o', str(binary)],
                                           check=True, timeout=60)
                            inputs = '\n'.join(commands)+'\n'
                            native = subprocess.run([str(binary)], input=inputs, text=True, capture_output=True,
                                                    check=True, env=env, timeout=20)
                            driver = scratch / 'Driver.lean'
                            driver.write_text(h.lean_driver().replace('import Unused\n', model, 1))
                            lean = subprocess.run([str(ROOT / '.tools/elan/bin/lake'), 'env', 'lean', '--run', str(driver)],
                                                  input=inputs, text=True, capture_output=True, cwd=ROOT,
                                                  env=env, timeout=60)
                            self.assertEqual(lean.returncode, 0, lean.stdout + lean.stderr)
                            self.assertEqual(native.stdout.splitlines(), expected)
                            self.assertEqual(lean.stdout, native.stdout)

    def test_bool_constructor_and_set(self):
        from test_modint_power_model import ModIntPowerModelTests
        source = ModIntPowerModelTests().class_source().rsplit('}', 1)[0] + '''
uint32_t construct_bool(bool value) { return ModInt<7u>(value).get(); }
uint32_t set_bool(bool value) { ModInt<7u> result; result.set(value); return result.get(); }
}
'''
        friends.FriendTranslationTests().compare(source,
            'call construct_bool 0\ncall construct_bool 1\ncall set_bool 0\ncall set_bool 1\n',
            ['ok 0', 'ok 1', 'ok 0', 'ok 1'], instance={'m': '7u'},
            calls=['construct_bool', 'set_bool'])


if __name__ == '__main__':
    unittest.main()
