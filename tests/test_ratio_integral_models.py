"""Arithmetic-only bindings of the public Ratio, with explicit coverage."""
from fractions import Fraction
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import diff_harness
import lean_translate
from lean_env import lean_environment
LAKE, LAKE_ENV = lean_environment()

SOURCE = ROOT / 'library/number/ratio.hpp'


def arithmetic_cases():
    commands, expected, selected = [], [], {'Ratio.init_T_T', 'Ratio.op_eq', 'Ratio.op_cmp'}
    count = 0

    def new(value):
        nonlocal count
        index = count
        count += 1
        commands.append(f'new Ratio.init_T_T {value.numerator} {value.denominator}')
        expected.append('new')
        return index

    def check(index, value):
        canonical = new(value)
        commands.append(f'do Ratio.op_eq {index} {canonical}')
        expected.append('ok 1')

    a, b = Fraction(3, 2), Fraction(1, 2)
    ia, ib = new(a), new(b)
    for op, compute in [('add', lambda x, y: x + y), ('sub', lambda x, y: x - y),
                        ('mul', lambda x, y: x * y), ('div', lambda x, y: x / y)]:
        for form, args, value in [('Ratio_Ratio', f'{ia} {ib}', compute(a, b)),
                                  ('Ratio_T', f'{ia} 1', compute(a, 1)),
                                  ('T_Ratio', f'1 {ib}', compute(1, b))]:
            name = f'op_{op}_{form}'
            selected.add(name)
            result = count
            count += 1
            commands.append(f'call {name} {args}')
            expected.append('ok obj')
            check(result, value)
        receiver = new(a)
        name = f'Ratio.op_{op}_assign'
        selected.add(name)
        result = count
        count += 1
        commands.append(f'do {name} {receiver} {ib}')
        expected.append('ok obj')
        check(result, compute(a, b))
        check(receiver, compute(a, b))
    commands += [f'do Ratio.op_cmp {ia} {ib}', f'do Ratio.op_cmp {ib} {ia}']
    expected += ['ok 1', 'ok -1']
    return '\n'.join(commands) + '\n', expected, selected


class RatioIntegralTests(unittest.TestCase):
    def test_explicit_selection_rejects_unknown_and_private_calls(self):
        for name in ['Ratio.not_a_method', 'Ratio.numeric_gcd']:
            with self.subTest(name=name), self.assertRaisesRegex(lean_translate.Unsupported, 'non-public differential calls'):
                diff_harness.Harness(SOURCE, {'T': 'int'}, 'Unused', standard='c++20', calls={name})

    def compare_binding(self, scalar, commands, expected, selected, model):
        env = dict(LAKE_ENV,
                   ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
        with self.subTest(scalar=scalar), tempfile.TemporaryDirectory(dir=ROOT / 'tests/diff') as directory:
            scratch = Path(directory)
            harness = diff_harness.Harness(SOURCE, {'T': scalar}, 'Unused', standard='c++20', calls=selected)
            self.assertFalse(harness.has_streams)
            cpp = scratch / 'driver.cpp'
            cpp.write_text(harness.cpp_driver())
            binary = scratch / 'driver'
            subprocess.run(['g++', '-std=c++20', '-O1', '-fsanitize=address,undefined',
                            '-I', str(ROOT / 'tests/diff'), str(cpp), '-o', str(binary)],
                           check=True, timeout=60)
            native = subprocess.run([str(binary)], input=commands, capture_output=True, text=True,
                                    check=True, env=env, timeout=30)
            self.assertEqual(native.stdout.splitlines(), expected)
            lean = scratch / 'Driver.lean'
            lean.write_text(harness.lean_driver().replace('import Unused\n', model, 1))
            actual = subprocess.run([LAKE, 'env', 'lean', '--run', str(lean)],
                                    input=commands, capture_output=True, text=True, env=env,
                                    cwd=ROOT, timeout=60)
            self.assertEqual(actual.returncode, 0, actual.stdout + actual.stderr)
            self.assertEqual(actual.stdout, native.stdout)

    def test_integral_arithmetic_against_fraction(self):
        commands, expected, selected = arithmetic_cases()
        model = lean_translate.translate_file(SOURCE, [], standard='c++20')
        for scalar in ['signed char', 'char', 'short', 'int', 'long', 'long long', 'unsigned', 'unsigned long long']:
            self.compare_binding(scalar, commands, expected, selected, model)

    def test_narrow_unsigned_template_promotions(self):
        model = lean_translate.translate_file(SOURCE, [], standard='c++20')
        for scalar, bits in [('unsigned char', 8), ('unsigned short', 16)]:
            commands, expected, selected = arithmetic_cases()
            count = sum(value in ('new', 'ok obj') for value in expected)
            # Both comparison products are int expressions. The left product
            # is 2**bits: narrowing each operator to T would reverse the result.
            commands += (f'new Ratio.init_T_T {2 ** (bits - 1)} 1\n'
                         'new Ratio.init_T_T 1 2\n'
                         f'do Ratio.op_cmp {count} {count + 1}\n'
                         f'do Ratio.op_cmp {count + 1} {count}\n')
            expected += ['new', 'new', 'ok 1', 'ok -1']
            self.compare_binding(scalar, commands, expected, selected, model)

    def test_narrow_unsigned_concrete_sources_still_require_cast_semantics(self):
        for scalar in ['unsigned char', 'unsigned short']:
            with self.subTest(scalar=scalar), tempfile.TemporaryDirectory() as directory:
                source = Path(directory) / 'narrow.hpp'
                source.write_text(f'namespace cp {{ {scalar} f({scalar} x) {{ return x * 2; }} }}')
                with self.assertRaisesRegex(lean_translate.Unsupported, 'type'):
                    lean_translate.translate_file(source, [])

    def test_unsigned_full_range_normalization(self):
        model = lean_translate.translate_file(SOURCE, [], standard='c++20')
        selected = {'Ratio.init_T_T', 'Ratio.op_eq'}
        for scalar, bits in [('unsigned', 32), ('unsigned long long', 64)]:
            hi = 2 ** bits - 1
            pairs = [(0, hi), (hi, hi), (hi, 1), (1, hi), (hi, hi - 2),
                     (hi, hi // 3), (hi - 1, (hi - 1) // 2), (2 * (hi // 3), hi // 3)]
            commands, expected = [], []
            for i, (n, d) in enumerate(pairs):
                q = Fraction(n, d)
                commands += [f'new Ratio.init_T_T {n} {d}',
                             f'new Ratio.init_T_T {q.numerator} {q.denominator}',
                             f'do Ratio.op_eq {2 * i} {2 * i + 1}']
                expected += ['new', 'new', 'ok 1']
            self.compare_binding(scalar, '\n'.join(commands) + '\n', expected, selected, model)

    def test_unsigned_lcm_boundary_arithmetic(self):
        model = lean_translate.translate_file(SOURCE, [], standard='c++20')
        selected = {'Ratio.init_T_T', 'Ratio.op_eq', 'op_add_Ratio_Ratio'}
        for scalar, bits in [('unsigned', 32), ('unsigned long long', 64)]:
            hi = 2 ** bits - 1
            # LCM is representable, although multiplying the denominators first
            # would overflow. The result numerator is also representable.
            denominators = [(hi, hi), (hi, hi // 3), (hi - 1, (hi - 1) // 2)]
            commands, expected = [], []
            for i, (d, e) in enumerate(denominators):
                q = Fraction(1, d) + Fraction(1, e)
                commands += [f'new Ratio.init_T_T 1 {d}', f'new Ratio.init_T_T 1 {e}',
                             f'call op_add_Ratio_Ratio {4 * i} {4 * i + 1}',
                             f'new Ratio.init_T_T {q.numerator} {q.denominator}',
                             f'do Ratio.op_eq {4 * i + 2} {4 * i + 3}']
                expected += ['new', 'new', 'ok obj', 'new', 'ok 1']
            self.compare_binding(scalar, '\n'.join(commands) + '\n', expected, selected, model)

    def test_unsigned_cross_cancel_boundary(self):
        model = lean_translate.translate_file(SOURCE, [], standard='c++20')
        selected = {'Ratio.init_T_T', 'Ratio.op_eq', 'op_mul_Ratio_Ratio'}
        for scalar, bits in [('unsigned', 32), ('unsigned long long', 64)]:
            hi = 2 ** bits - 1
            pairs = [(Fraction(hi, hi - 1), Fraction(hi - 1, hi)),
                     (Fraction(hi, 2), Fraction(2, hi)),
                     (Fraction(hi, 1), Fraction(1, hi)),
                     (Fraction(hi // 3, 2), Fraction(6, hi))]
            commands, expected = [], []
            for i, (a, b) in enumerate(pairs):
                q = a * b
                commands += [f'new Ratio.init_T_T {a.numerator} {a.denominator}',
                             f'new Ratio.init_T_T {b.numerator} {b.denominator}',
                             f'call op_mul_Ratio_Ratio {4 * i} {4 * i + 1}',
                             f'new Ratio.init_T_T {q.numerator} {q.denominator}',
                             f'do Ratio.op_eq {4 * i + 2} {4 * i + 3}']
                expected += ['new', 'new', 'ok obj', 'new', 'ok 1']
            self.compare_binding(scalar, '\n'.join(commands) + '\n', expected, selected, model)

    def test_unsigned_division_cross_cancel_and_alias(self):
        model = lean_translate.translate_file(SOURCE, [], standard='c++20')
        selected = {'Ratio.init_T_T', 'Ratio.op_eq', 'op_div_Ratio_Ratio', 'Ratio.op_div_assign'}
        for scalar, bits in [('unsigned', 32), ('unsigned long long', 64)]:
            hi = 2 ** bits - 1
            pairs = [(Fraction(hi, hi - 1), Fraction(hi, hi - 1)),
                     (Fraction(hi, 2), Fraction(hi, 2)),
                     (Fraction(hi, 1), Fraction(hi, 2)),
                     (Fraction(1, hi), Fraction(2, hi))]
            commands, expected = [], []
            for i, (a, b) in enumerate(pairs):
                q = a / b
                commands += [f'new Ratio.init_T_T {a.numerator} {a.denominator}',
                             f'new Ratio.init_T_T {b.numerator} {b.denominator}',
                             f'call op_div_Ratio_Ratio {4 * i} {4 * i + 1}',
                             f'new Ratio.init_T_T {q.numerator} {q.denominator}',
                             f'do Ratio.op_eq {4 * i + 2} {4 * i + 3}']
                expected += ['new', 'new', 'ok obj', 'new', 'ok 1']
            k = 4 * len(pairs)
            commands += [f'new Ratio.init_T_T {hi} {hi - 1}', f'do Ratio.op_div_assign {k} {k}',
                         'new Ratio.init_T_T 1 1', f'do Ratio.op_eq {k} {k + 2}',
                         f'do Ratio.op_eq {k + 1} {k + 2}']
            expected += ['new', 'ok obj', 'new', 'ok 1', 'ok 1']
            self.compare_binding(scalar, '\n'.join(commands) + '\n', expected, selected, model)

    def test_unsigned_add_subtract_boundaries(self):
        model = lean_translate.translate_file(SOURCE, [], standard='c++20')
        selected = {'Ratio.init_T_T', 'Ratio.op_eq', 'Ratio.op_add_assign', 'Ratio.op_sub_assign'}
        for scalar, bits in [('unsigned', 32), ('unsigned long long', 64)]:
            hi = 2 ** bits - 1
            cases = [('add', Fraction(hi - 1), Fraction(1)),
                     ('add', Fraction(hi // 3), Fraction(2 * (hi // 3))),
                     ('add', Fraction(1, hi), Fraction(2, hi)),
                     ('sub', Fraction(hi), Fraction(hi - 1)),
                     ('sub', Fraction(hi, hi - 1), Fraction(1, hi - 1)),
                     ('sub', Fraction(hi, 2), Fraction(hi, 2))]
            commands, expected = [], []
            for i, (op, a, b) in enumerate(cases):
                q = a + b if op == 'add' else a - b
                commands += [f'new Ratio.init_T_T {a.numerator} {a.denominator}',
                             f'new Ratio.init_T_T {b.numerator} {b.denominator}',
                             f'do Ratio.op_{op}_assign {4 * i} {4 * i + 1}',
                             f'new Ratio.init_T_T {q.numerator} {q.denominator}',
                             f'do Ratio.op_eq {4 * i + 2} {4 * i + 3}',
                             f'do Ratio.op_eq {4 * i} {4 * i + 3}']
                expected += ['new', 'new', 'ok obj', 'new', 'ok 1', 'ok 1']
            k = 4 * len(cases)
            commands += [f'new Ratio.init_T_T {hi} {hi - 1}', f'do Ratio.op_sub_assign {k} {k}',
                         'new Ratio.init_T_T 0 1', f'do Ratio.op_eq {k} {k + 2}',
                         f'do Ratio.op_eq {k + 1} {k + 2}']
            expected += ['new', 'ok obj', 'new', 'ok 1', 'ok 1']
            self.compare_binding(scalar, '\n'.join(commands) + '\n', expected, selected, model)

    def test_unsigned_comparison_after_denominator_cancellation(self):
        model = lean_translate.translate_file(SOURCE, [], standard='c++20')
        selected = {'Ratio.init_T_T', 'Ratio.op_cmp'}
        for scalar, bits in [('unsigned', 32), ('unsigned long long', 64)]:
            hi = 2 ** bits - 1
            # Unreduced cross products can exceed the type capacity. The source
            # cancels the shared denominator factor before either multiplication.
            pairs = [(Fraction(hi, hi - 1), Fraction(hi - 2, hi - 1)),
                     (Fraction(1, hi), Fraction(1, hi // 3)),
                     (Fraction(hi), Fraction(hi - 1)),
                     (Fraction(0), Fraction(1, hi)),
                     (Fraction(hi, hi - 1), Fraction(hi, hi - 1))]
            commands, expected = [], []
            for i, (a, b) in enumerate(pairs):
                order = (a > b) - (a < b)
                commands += [f'new Ratio.init_T_T {a.numerator} {a.denominator}',
                             f'new Ratio.init_T_T {b.numerator} {b.denominator}',
                             f'do Ratio.op_cmp {2 * i} {2 * i + 1}',
                             f'do Ratio.op_cmp {2 * i + 1} {2 * i}',
                             f'do Ratio.op_cmp {2 * i} {2 * i}']
                expected += ['new', 'new', f'ok {order}', f'ok {-order}', 'ok 0']
            self.compare_binding(scalar, '\n'.join(commands) + '\n', expected, selected, model)

    def test_integral_prefix_postfix_boundaries(self):
        model = lean_translate.translate_file(SOURCE, [], standard='c++20')
        selected = {'Ratio.init_T_T', 'Ratio.op_eq', 'Ratio.op_inc_0', 'Ratio.op_inc_int',
                    'Ratio.op_dec_0', 'Ratio.op_dec_int'}
        for scalar, bits in [('signed char', 8), ('char', 8), ('short', 16), ('int', 32),
                             ('long', 64), ('long long', 64), ('unsigned', 32),
                             ('unsigned long long', 64)]:
            unsigned = scalar.startswith('unsigned')
            hi = 2 ** (bits if unsigned else bits - 1) - 1
            cases = [('inc', Fraction(hi - 1)), ('inc', Fraction(hi - 2, 2)),
                     ('inc', Fraction(0)), ('dec', Fraction(hi, 2)),
                     ('dec', Fraction(1)), ('dec', Fraction(hi, hi - 1))]
            if not unsigned and scalar != 'char':
                cases += [('inc', Fraction(-hi + 1)), ('dec', Fraction(-hi + 2, 2)),
                          ('dec', Fraction(0))]
            commands, expected = [], []
            count = 0
            for op, value in cases:
                updated = value + 1 if op == 'inc' else value - 1
                for postfix in [False, True]:
                    returned = value if postfix else updated
                    name = f'Ratio.op_{op}_int' if postfix else f'Ratio.op_{op}_0'
                    tag = ' 0' if postfix else ''
                    commands += [f'new Ratio.init_T_T {value.numerator} {value.denominator}',
                                 f'do {name} {count}{tag}',
                                 f'new Ratio.init_T_T {returned.numerator} {returned.denominator}',
                                 f'new Ratio.init_T_T {updated.numerator} {updated.denominator}',
                                 f'do Ratio.op_eq {count + 1} {count + 2}',
                                 f'do Ratio.op_eq {count} {count + 3}']
                    expected += ['new', 'ok obj', 'new', 'new', 'ok 1', 'ok 1']
                    count += 4
            self.compare_binding(scalar, '\n'.join(commands) + '\n', expected, selected, model)

    def test_integral_unary_boundaries(self):
        model = lean_translate.translate_file(SOURCE, [], standard='c++20')
        selected = {'Ratio.init_T_T', 'Ratio.op_eq', 'Ratio.op_add', 'Ratio.op_sub'}
        for scalar, bits in [('signed char', 8), ('char', 8), ('short', 16), ('int', 32),
                             ('long', 64), ('long long', 64), ('unsigned', 32),
                             ('unsigned long long', 64)]:
            unsigned = scalar.startswith('unsigned')
            hi = 2 ** (bits if unsigned else bits - 1) - 1
            values = [Fraction(0), Fraction(hi), Fraction(hi, 2), Fraction(1, hi)]
            if not unsigned and scalar != 'char':
                values += [Fraction(-hi), Fraction(-hi, 2)]
            commands, expected = [], []
            count = 0
            for value in values:
                ops = ['add', 'sub'] if value == 0 or not unsigned and scalar != 'char' else ['add']
                for op in ops:
                    result = value if op == 'add' else -value
                    commands += [f'new Ratio.init_T_T {value.numerator} {value.denominator}',
                                 f'do Ratio.op_{op} {count}',
                                 f'new Ratio.init_T_T {result.numerator} {result.denominator}',
                                 f'new Ratio.init_T_T {value.numerator} {value.denominator}',
                                 f'do Ratio.op_eq {count + 1} {count + 2}',
                                 f'do Ratio.op_eq {count} {count + 3}']
                    expected += ['new', 'ok obj', 'new', 'new', 'ok 1', 'ok 1']
                    count += 4
            self.compare_binding(scalar, '\n'.join(commands) + '\n', expected, selected, model)


if __name__ == '__main__':
    unittest.main()
