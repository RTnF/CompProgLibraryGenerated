"""Hidden friend definitions retain ADL and generic record semantics."""
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


class FriendTranslationTests(unittest.TestCase):
    def compare(self, header, cases, expected_values, standard="c++23", instance=None, calls=None,
                rejected_standard=None):
        with tempfile.TemporaryDirectory(dir=ROOT / 'tests/diff', prefix='.friend-') as directory:
            scratch = Path(directory)
            source = scratch / 'friend.hpp'
            source.write_text(header)
            if rejected_standard is not None:
                with self.assertRaises(subprocess.CalledProcessError):
                    lean_translate.translate_file(source, [], standard=rejected_standard)
            model = lean_translate.translate_file(source, [], standard=standard)
            h = diff_harness.Harness(source, instance or {'T': 'long long'}, 'Unused', standard=standard, calls=calls)
            cpp = scratch / 'driver.cpp'
            cpp.write_text(h.cpp_driver())
            binary = scratch / 'driver'
            subprocess.run(['g++', f'-std={standard}', '-O1', '-fsanitize=address,undefined',
                            '-I', str(ROOT / 'tests/diff'), str(cpp), '-o', str(binary)], check=True, timeout=60)
            env = dict(LAKE_ENV,
                       ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
            expected = subprocess.run([str(binary)], input=cases, text=True, capture_output=True,
                                      check=True, timeout=60, env=env).stdout
            lean = scratch / 'Driver.lean'
            lean.write_text(h.lean_driver().replace('import Unused\n', model, 1))
            actual = subprocess.run([LAKE, 'env', 'lean', '--run', str(lean)],
                                    input=cases, text=True, capture_output=True, cwd=ROOT,
                                    env=env, timeout=120)
            self.assertEqual(actual.returncode, 0, actual.stdout + actual.stderr)
            self.assertEqual(actual.stdout, expected)
            self.assertEqual(expected.splitlines(), expected_values)

    def test_template_hidden_friend_cpp_and_lean(self):
        self.compare('''#pragma once
namespace cp {
template<class T> class Box {
  T value;
public:
  Box(T x) : value(x) {}
  friend T reveal(const Box<T>& x) { return x.value; }
};
long long ordinary(long long x) { return x + 3; }
}
''',
                     'new Box.init -17\ncall reveal 0\ncall ordinary 4\n',
                     ['new', 'ok -17', 'ok 7'])

    def test_original_ratio_arithmetic_translation(self):
        # Transitional coverage: streams stay in the original file, but are not
        # translated yet. No reduced header is published by this test.
        from fractions import Fraction
        header = (ROOT / 'experiments/library/cpp/number/ratio.hpp').read_text()
        header = header.replace('#include "template/small_template.hpp"',
                                '#include <numeric>\n#include <compare>\n#include <cassert>\n'
                                '#include <iostream>\n#include <cstdint>\nusing namespace std;\n'
                                'using ll = int64_t;\nnamespace cp {')
        header = header.replace('gcd(', 'std::gcd(').replace('lcm(', 'std::lcm(')
        header = header[:header.index('  friend istream')] + '};\n}\n'
        lines, expected = [], []
        count = 0

        def new(q):
            nonlocal count
            obj = count
            count += 1
            lines.append(f'new Ratio.init_T_T {q.numerator} {q.denominator}')
            expected.append('new')
            return obj

        def call(label, args, method=False):
            nonlocal count
            obj = count
            count += 1
            lines.append(('do ' if method else 'call ') + label + ' ' + ' '.join(map(str, args)))
            expected.append('ok obj')
            return obj

        def check(obj, q):
            want = new(q)
            lines.append(f'do Ratio.op_eq {obj} {want}')
            expected.append('ok 1')

        for a, b in [(Fraction(1, 2), Fraction(2, 3)),
                     (Fraction(1, 2), Fraction(-2, 3)),
                     (Fraction(-3, 4), Fraction(-2, 3))]:
            ia, ib = new(a), new(b)
            ops = [('add', lambda x, y: x + y), ('sub', lambda x, y: x - y),
                   ('mul', lambda x, y: x * y), ('div', lambda x, y: x / y)]
            for name, op in ops:
                check(call(f'op_{name}_Ratio_Ratio', [ia, ib]), op(a, b))
                check(call(f'op_{name}_Ratio_T', [ia, 3]), op(a, 3))
                check(call(f'op_{name}_T_Ratio', [3, ib]), op(Fraction(3), b))
                receiver = new(a)
                check(call(f'Ratio.op_{name}_assign', [receiver, ib], True), op(a, b))
                check(receiver, op(a, b))
            check(call('Ratio.op_add', [ia], True), a)
            check(call('Ratio.op_sub', [ia], True), -a)
            for op, delta in [('inc', 1), ('dec', -1)]:
                for suffix in ['0', 'int']:
                    receiver = new(a)
                    result = call(f'Ratio.op_{op}_{suffix}', [receiver] + ([0] if suffix == 'int' else []), True)
                    check(result, a if suffix == 'int' else a + delta)
                    check(receiver, a + delta)
            lines.append(f'do Ratio.op_cmp {ia} {ib}')
            expected.append('ok -1' if a < b else 'ok 1' if a > b else 'ok 0')
            receiver = new(a)
            check(call('Ratio.op_div_assign', [receiver, receiver], True), Fraction(1))
            check(receiver, Fraction(1))
        self.compare(header, '\n'.join(lines) + '\n', expected, standard='c++23')

    def test_user_defined_copy_is_not_silently_replaced(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'copy.hpp'
            source.write_text("""namespace cp {
template<class T> struct Copy {
  T value;
  Copy(T x) : value(x) {}
  Copy(const Copy &r) : value(r.value + 1) {}
};
}
""")
            with self.assertRaisesRegex(lean_translate.Unsupported, 'user-defined record copy'):
                lean_translate.translate_file(source, [])

    def test_copy_and_compound_assignment_of_temporary(self):
        self.compare("""#pragma once
namespace cp {
template<class T> class Box {
  T value;
public:
  Box(T x) : value(x) {}
  Box &operator+=(const Box &r) { value += r.value; return *this; }
  friend T add_value(const Box &a, const Box &b) { return (Box(a) += b).value; }
  friend T add_scalar(const Box &a, T b) { return (Box(a) += b).value; }
  T get() const { return value; }
};
}
""", 'new Box.init 17\nnew Box.init -3\ncall add_value 0 1\n'
     'call add_scalar 0 5\ndo Box.get_ 0\ndo Box.get_ 1\n',
     ['new', 'new', 'ok 14', 'ok 22', 'ok 17', 'ok -3'])

    def test_standard_numeric_contract_and_same_named_user_function(self):
        self.compare("""#pragma once
#include <numeric>
namespace cp {
template<class T> T gcd_value(T a, T b) { return std::gcd(a, b); }
template<class T> T lcm_value(T a, T b) { return std::lcm(a, b); }
unsigned long long mixed_gcd(unsigned a, unsigned long long b) { return std::gcd(a, b); }
unsigned mixed_sign_gcd(int a, unsigned b) { return std::gcd(a, b); }
unsigned mixed_sign_lcm(int a, unsigned b) { return std::lcm(a, b); }
long long gcd(long long a, long long b) { return a + b + 100; }
}
""", 'call gcd_value -42 56\ncall lcm_value -42 56\n'
     'call gcd_value 0 0\ncall lcm_value 0 -7\n'
     'call mixed_gcd 4294967295 18446744073709551615\ncall gcd 1 2\ncall mixed_sign_gcd -42 56\ncall mixed_sign_lcm -42 56\n',
     ['ok 14', 'ok 168', 'ok 0', 'ok 0', 'ok 4294967295', 'ok 103', 'ok 14', 'ok 168'])

    def test_cpp23_uses_same_standard_for_ast_and_cpp(self):
        self.compare("""#pragma once
#if __cplusplus <= 202002L
#error C++23 required
#endif
namespace cp {
constexpr long long answer(long long x) { return x + 20; }
}
""", 'call answer 22\n', ['ok 42'], rejected_standard="c++20")

    def test_standard_bit_operations_keep_unsigned_word_width(self):
        self.compare("""#include <bit>
namespace cp {
int width32(unsigned x) { return std::bit_width(x >> 1); }
int trailing32(unsigned x) { return ::std::countr_zero(x); }
int trailing64(unsigned long long x) { return std::countr_zero(x); }
}
""", 'call width32 0\ncall width32 4294967295\n'
     'call trailing32 0\ncall trailing32 2147483648\n'
     'call trailing64 0\ncall trailing64 9223372036854775808\n',
     ['ok 0', 'ok 31', 'ok 32', 'ok 31', 'ok 64', 'ok 63'])

    def test_cpp20_spaceship_and_defaulted_field_equality(self):
        self.compare("""#pragma once
#include <compare>
namespace cp {
template<class T> class Fraction {
  T n, d;
public:
  Fraction(T x, T y) : n(x), d(y) {}
  std::strong_ordering operator<=>(const Fraction &r) const {
    return n * r.d <=> r.n * d;
  }
  bool operator==(const Fraction &r) const = default;
};
}
""", 'new Fraction.init -3 2\nnew Fraction.init 1 2\n'
     'new Fraction.init -3 2\nnew Fraction.init -6 4\n'
     'do Fraction.op_cmp 0 1\ndo Fraction.op_cmp 1 0\ndo Fraction.op_cmp 0 3\n'
     'do Fraction.op_eq 0 1\ndo Fraction.op_eq 0 2\ndo Fraction.op_eq 0 3\n',
     ['new', 'new', 'new', 'new', 'ok -1', 'ok 1', 'ok 0', 'ok 0', 'ok 1', 'ok 0'],
     rejected_standard="c++17")

    def test_prefix_and_postfix_receiver_and_return(self):
        self.compare("""#pragma once
namespace cp {
template<class T> class Counter {
  T n, d;
public:
  Counter(T x, T y) : n(x), d(y) {}
  Counter operator++(int) { Counter r = *this; ++*this; return r; }
  Counter &operator++() { n += d; return *this; }
  Counter operator--(int) { Counter r = *this; --*this; return r; }
  Counter &operator--() { n -= d; return *this; }
  T value() const { return n; }
};
}
""", 'new Counter.init 10 3\n'
     'do Counter.op_inc_int 0 0\ndo Counter.value 0\ndo Counter.value 1\n'
     'do Counter.op_inc_0 0\ndo Counter.value 0\ndo Counter.value 2\n'
     'do Counter.op_dec_int 0 0\ndo Counter.value 0\ndo Counter.value 3\n'
     'do Counter.op_dec_0 0\ndo Counter.value 0\ndo Counter.value 4\n',
     ['new', 'ok obj', 'ok 13', 'ok 10', 'ok obj', 'ok 16', 'ok 16',
      'ok obj', 'ok 13', 'ok 16', 'ok obj', 'ok 10', 'ok 10'])


if __name__ == '__main__':
    unittest.main()
