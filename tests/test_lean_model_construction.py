"""Converting returns and Group's default-factory construction preserve calls."""
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


class ConstructionTranslationTests(unittest.TestCase):
    def test_public_monoid_full_model_contract(self):
        source = ROOT / 'library/algebraic_structure/monoid.hpp'
        model = lean_translate.translate_file(source, [])
        model = model.replace('import Proofs.Cpp.Prelude',
                              'import Proofs.Cpp.Prelude\nimport Proofs.Cpp.Lib.MonoidMath', 1)
        contract = (ROOT / 'Proofs/Cpp/Monoid.lean').read_text().split('namespace Proofs.Cpp.Monoid', 1)[1]
        with tempfile.TemporaryDirectory() as directory:
            proof = Path(directory) / 'Monoid.lean'
            proof.write_text(model + '\nnamespace Proofs.Cpp.Monoid' + contract)
            result = subprocess.run([str(ROOT / '.tools/elan/bin/lake'), 'env', 'lean', str(proof)],
                cwd=ROOT, env=dict(os.environ, ELAN_HOME=str(ROOT / '.tools/elan')),
                text=True, capture_output=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, '')

    def test_public_monoid_public_fields_and_both_friends(self):
        header = (ROOT / 'library/algebraic_structure/monoid.hpp').read_text()
        cases = subprocess.check_output([sys.executable, str(ROOT / 'tests/diff/monoid.py')], text=True)
        values = [1, 0, 1, 3, 7, 11]
        for cpp, lo, hi in [('int', -(2**31), 2**31-1),
                            ('long long', -(2**63), 2**63-1),
                            ('unsigned long long', 0, 2**64-1)]:
            expected = []
            for cls, identity in [('MonoidMul', 1), ('MonoidMax', lo), ('MonoidMin', hi)]:
                data = [identity, *values[1:]]
                expected += ['new'] * 6 + [f'ok {v}' for v in data]
                for a in data:
                    for b in data:
                        result = a * b if cls == 'MonoidMul' else max(a, b) if cls == 'MonoidMax' else min(a, b)
                        expected += ['ok obj', f'ok {result}'] * 2
            with self.subTest(cpp=cpp):
                friends.FriendTranslationTests().compare(header, cases, expected, instance={'T': cpp})

    def test_public_field_observation_respects_access(self):
        header = '''#pragma once
namespace cp {
template<class T> struct Box {
  T a;
private:
  T b;
protected:
  T c;
public:
  T d;
  Box(T x) : a(x), b(x + 1), c(x + 2), d(x + 3) {}
};
}
'''
        friends.FriendTranslationTests().compare(header,
            'new Box.init 5\nfield Box.a 0\nfield Box.d 0\nfield Box.a 0\n',
            ['new', 'ok 5', 'ok 8', 'ok 5'])
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'fields.hpp'
            source.write_text(header)
            h = friends.diff_harness.Harness(source, {'T': 'long long'}, 'Unused')
            self.assertEqual(h.tr.classes['Box'].public_fields, {'a', 'd'})
            for driver in (h.cpp_driver(), h.lean_driver()):
                self.assertNotIn('"Box.b"', driver)
                self.assertNotIn('"Box.c"', driver)

    def test_numeric_traits_integral_bindings(self):
        header = '''#pragma once
#include <limits>
#include <type_traits>
namespace cp {
template<class T> class Bounds {
  T value;
public:
  Bounds(T x) : value(x) {}
  Bounds() : Bounds(e()) {}
  static Bounds e() {
    if constexpr (std::is_floating_point_v<T>) {
      return std::numeric_limits<T>::has_infinity
        ? -std::numeric_limits<T>::infinity() : std::numeric_limits<T>::lowest();
    } else { return std::numeric_limits<T>::min(); }
  }
  T get() const { return value; }
};
template<class T> T upper(T x) { return std::numeric_limits<T>::max(); }
template<class T> T lowest(T x) { return std::numeric_limits<T>::lowest(); }
template<class T> bool floating(T x) { return std::is_floating_point_v<T>; }
template<class T> bool infinity(T x) { return std::numeric_limits<T>::has_infinity; }
}
'''
        for cpp, bits, signed in [('signed char', 8, True), ('unsigned char', 8, False),
                                 ('short', 16, True), ('unsigned short', 16, False),
                                 ('int', 32, True), ('unsigned int', 32, False),
                                 ('long', 64, True), ('unsigned long', 64, False),
                                 ('long long', 64, True), ('unsigned long long', 64, False)]:
            lo = -(2 ** (bits - 1)) if signed else 0
            hi = 2 ** (bits - int(signed)) - 1
            with self.subTest(cpp=cpp):
                friends.FriendTranslationTests().compare(header,
                    'new Bounds.init_0\ndo Bounds.get_ 0\ncall upper 1\ncall lowest 1\n'
                    'call floating 1\ncall infinity 1\n',
                    ['new', f'ok {lo}', f'ok {hi}', f'ok {lo}', 'ok 0', 'ok 0'],
                    instance={'T': cpp})

    def test_numeric_traits_distinguish_parameters_with_same_carrier(self):
        friends.FriendTranslationTests().compare('''#pragma once
#include <limits>
namespace cp {
template<class T, class U> class Bounds {
  T lower;
  U upper;
public:
  Bounds(T a, U b) : lower(std::numeric_limits<T>::min()), upper(std::numeric_limits<U>::max()) {}
  T low() const { return lower; }
  U high() const { return upper; }
};
}
''', 'new Bounds.init 1 1\ndo Bounds.low 0\ndo Bounds.high 0\n',
            ['new', 'ok -2147483648', 'ok 9223372036854775807'],
            instance={'T': 'int', 'U': 'long long'})

    def test_numeric_traits_floating_and_discarded_negation(self):
        header = '''#include <limits>
#include <type_traits>
struct NoNeg { int value; NoNeg() : value(7) {} };
namespace cp {
template<class T> class Bounds {
  T value;
public:
  Bounds(T x) : value(x) {}
  Bounds() : Bounds(e()) {}
  static Bounds e() {
    if constexpr (std::is_floating_point_v<T>) {
      return std::numeric_limits<T>::has_infinity
        ? -std::numeric_limits<T>::infinity() : std::numeric_limits<T>::lowest();
    } else { return std::numeric_limits<T>::min(); }
  }
  static Bounds high() {
    if constexpr (std::is_floating_point_v<T>) {
      return std::numeric_limits<T>::has_infinity
        ? std::numeric_limits<T>::infinity() : std::numeric_limits<T>::max();
    } else { return std::numeric_limits<T>::max(); }
  }
  T get() const { return value; }
};
}
'''
        model = self.model(header)
        self.assertNotIn('[Neg T]', model)
        proof = '''
inductive Extended where
  | finite : Int → Extended
  | negInf
  | posInf
  deriving BEq, Inhabited

instance : Proofs.Cpp.NumericTraits "T" Extended where
  isFloatingPoint := true
  hasInfinity := true
  minimum := .finite 1
  maximum := .finite 100
  lowest := .finite (-100)
  infinity := .posInf
  negativeInfinity := .negInf

structure NoNeg where
  value : Int
  deriving BEq, Inhabited

instance : Proofs.Cpp.NumericTraits "T" NoNeg where
  isFloatingPoint := false
  hasInfinity := false
  minimum := ⟨7⟩
  maximum := ⟨7⟩
  lowest := ⟨7⟩
  infinity := ⟨7⟩
  negativeInfinity := ⟨7⟩

#guard ((Proofs.Cpp.Gen.cp.Bounds.init_0 (T := Extended)).run 0).map
  (fun r => (r.1.value, r.2)) == some (.negInf, 3)
#guard ((Proofs.Cpp.Gen.cp.Bounds.high (T := Extended)).run 0).map
  (fun r => (r.1.value, r.2)) == some (.posInf, 2)
#guard ((Proofs.Cpp.Gen.cp.Bounds.init_0 (T := NoNeg)).run 0).map
  (fun r => (r.1.value.value, r.2)) == some (7, 3)
#guard ((Proofs.Cpp.Gen.cp.Bounds.high (T := NoNeg)).run 0).map
  (fun r => (r.1.value.value, r.2)) == some (7, 2)

-- Exercise the fallback branch independently of the infinity branch.
@[instance_reducible] def finiteTraits : Proofs.Cpp.NumericTraits "T" Extended :=
  { (inferInstance : Proofs.Cpp.NumericTraits "T" Extended) with hasInfinity := false }
#guard ((@Proofs.Cpp.Gen.cp.Bounds.e Extended finiteTraits).run 0).map
  (fun r => (r.1.value, r.2)) == some (.finite (-100), 2)
#guard ((@Proofs.Cpp.Gen.cp.Bounds.high Extended finiteTraits).run 0).map
  (fun r => (r.1.value, r.2)) == some (.finite 100, 2)
'''
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            cpp = scratch / 'traits.cpp'
            cpp.write_text(header + '''
#include <cmath>
#include <iostream>
int main() {
  const auto low = cp::Bounds<double>().get();
  const auto high = cp::Bounds<double>::high().get();
  std::cout << (std::isinf(low) && std::signbit(low)) << " "
    << (std::isinf(high) && !std::signbit(high)) << " "
    << cp::Bounds<NoNeg>().get().value << " "
    << cp::Bounds<NoNeg>::high().get().value << "\\n";
}
''')
            binary = scratch / 'traits'
            subprocess.run(['g++', '-std=c++17', '-O1', '-fsanitize=address,undefined',
                            str(cpp), '-o', str(binary)], check=True, timeout=60)
            env = dict(os.environ, ELAN_HOME=str(ROOT / '.tools/elan'),
                       ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
            native = subprocess.run([str(binary)], text=True, capture_output=True,
                                    check=True, timeout=60, env=env)
            self.assertEqual(native.stdout, '1 1 7 7\n')
            lean = scratch / 'Traits.lean'
            lean.write_text(model + proof)
            result = subprocess.run([str(ROOT / '.tools/elan/bin/lake'), 'env', 'lean', str(lean)],
                                    cwd=ROOT, env=env, text=True, capture_output=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, '')

    def test_negative_infinity_outside_floating_constexpr_needs_negation(self):
        model = self.model('''#include <limits>
namespace cp { template<class T> T f(T x) { return -std::numeric_limits<T>::infinity(); } }
''')
        self.assertIn('[Neg T]', model)
        self.assertNotIn('NumericTraits.negativeInfinity', model)

    def test_standard_extrema_using_and_user_functions_are_distinct(self):
        friends.FriendTranslationTests().compare('''#pragma once
#include <algorithm>
namespace cp {
template<class T> T max(T a, T b) { return a + b + 100; }
long long min() { return 73; }
template<class T> T own(T a, T b) { return max(a, b); }
template<class T> T standard(T a, T b) {
  using std::max;
  using std::min;
  return max(a, b) + min(a, b);
}
template<class T> T qualified(T a, T b) { return std::max(a, b); }
long long fixed(long long a, long long b) { using std::max; return max(a, b); }
template<class T> T scoped(T a, T b) {
  if (a < b) { using std::max; a = max(a, b); }
  return max(a, b);
}
long long own_zero() { return min(); }
}
''', 'call own 3 8\ncall standard 3 8\ncall qualified 3 8\ncall fixed 3 8\n'
     'call scoped 3 8\ncall scoped 8 3\ncall own_zero\n',
            ['ok 111', 'ok 11', 'ok 8', 'ok 8', 'ok 116', 'ok 111', 'ok 73'])

    def test_unsupported_using_is_rejected(self):
        with self.assertRaisesRegex(lean_translate.Unsupported, 'using declaration'):
            self.model('''#include <algorithm>
namespace cp { template<class T> T f(T a, T b) {
  using std::swap; return a + b;
} }
''')

    def test_explicit_standard_extrema_not_rebound_to_user_function(self):
        with self.assertRaisesRegex(lean_translate.Unsupported, 'explicit template arguments'):
            self.model('''#include <algorithm>
namespace cp {
template<class T> T max(T a, T b) { return a + b; }
template<class T> T f(T a, T b) { return std::max<T>(a, b); }
}
''')

    def model(self, header):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'construction.hpp'
            source.write_text(header)
            return lean_translate.translate_file(source, [])

    def test_dependent_conversion_evaluates_argument_once(self):
        header = '''#pragma once
namespace cp {
template<class T> T scalar(T x) { return x + 1; }
template<class T> class Box {
  T value;
public:
  Box(T x) : value(x) {}
  Box() : Box(e()) {}
  static Box e() { return scalar(T(0)); }
  T get() const { return value; }
  friend Box op(const Box& a, const Box& b) {
    return scalar(a.value + b.value);
  }
};
}
'''
        friends.FriendTranslationTests().compare(header,
            'new Box.init_0\nnew Box.init_T 3\ncall op 0 1\ndo Box.get_ 0\ndo Box.get_ 2\n',
            ['new', 'new', 'ok obj', 'ok 1', 'ok 5'])
        # Four calls: default constructor, e, scalar, value constructor.
        # A second evaluation of scalar cannot pass this work assertion.
        model = self.model(header)
        with tempfile.TemporaryDirectory() as directory:
            proof = Path(directory) / 'Work.lean'
            proof.write_text(model + '''
#guard ((Proofs.Cpp.Gen.cp.Box.init_0 (T := Int)).run 0).map
  (fun r => (r.1.value, r.2)) == some (1, 4)
''')
            result = subprocess.run([str(ROOT / '.tools/elan/bin/lake'), 'env', 'lean', str(proof)],
                cwd=ROOT, env=dict(os.environ, ELAN_HOME=str(ROOT / '.tools/elan')),
                text=True, capture_output=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_hidden_and_qualified_functions_keep_distinct_bodies(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
template<class T> class Box;
template<class T> Box<T> op(const Box<T>& a);
template<class T> class Box {
  T value;
public:
  Box(T x) : value(x) {}
  T get() const { return value; }
  friend Box op<T>(const Box& a);
  friend Box op(const Box& a) { return a.value + 1; }
};
template<class T> Box<T> op(const Box<T>& a) {
  return Box<T>(a.value + 100);
}
}
''', 'new Box.init 7\ncall op_Box_hidden 0\ncall op_Box_qualified 0\n'
     'do Box.get_ 1\ndo Box.get_ 2\n',
            ['new', 'ok obj', 'ok obj', 'ok 8', 'ok 107'])

    def test_braced_record_return_calls_the_constructor(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
template<class T> class Pair {
  T a, b;
public:
  Pair(T x, T y) : a(x + 1), b(y + 2) {}
  Pair() : Pair(e()) {}
  static Pair e() { return {0, 1}; }
  T first() const { return a; }
  T second() const { return b; }
};
}
''', 'new Pair.init_0\ndo Pair.first 0\ndo Pair.second 0\n',
            ['new', 'ok 1', 'ok 3'])

    def test_explicit_constructor_is_not_an_implicit_return(self):
        for result in ['x', '{x}']:
            with self.subTest(result=result), self.assertRaises(lean_translate.Unsupported):
                self.model('''#pragma once
namespace cp {
template<class T> class Box {
  T value;
public:
  explicit Box(T x) : value(x) {}
  static Box invalid(T x) { return ''' + result + '''; }
};
}
''')

    def test_other_delegation_forms_are_rejected(self):
        for constructor in ['Box() : Box(e()) { value += 1; }',
                            'Box(T x) : Box(e()) {}',
                            'Box() : Box(T(7)) {}']:
            with self.subTest(constructor=constructor), self.assertRaises(lean_translate.Unsupported):
                self.model('''#pragma once
namespace cp {
template<class T> class Box {
  T value;
public:
  Box(T x, T y) : value(x + y) {}
  static Box e() { return {0, 1}; }
  ''' + constructor + '''
};
}
''')

    def test_custom_copy_and_inheritance_stay_rejected(self):
        for declaration in ['Box(const Box& other) : value(other.value + 9) {}',
                            '~Box() { value = 0; }']:
            with self.subTest(declaration=declaration), self.assertRaises(lean_translate.Unsupported):
                self.model('''#pragma once
namespace cp {
template<class T> class Box {
  T value;
public:
  Box(T x) : value(x) {}
  ''' + declaration + '''
  Box() : Box(e()) {}
  static Box e() { return T(0); }
};
}
''')
        with self.assertRaises(lean_translate.Unsupported):
            self.model('namespace cp { struct Base {}; struct Derived : Base {}; }')

    def test_public_group_preserves_three_classes_and_qualified_operations(self):
        header = (ROOT / 'library/algebraic_structure/group.hpp').read_text()
        cases = '''new GroupSum.init_T 7
new GroupSum.init_0
do GroupSum.x 0
do GroupSum.x 1
do GroupSum.inv 0
do GroupSum.x 2
call op_GroupSum_GroupSum_hidden 0 2
do GroupSum.x 3
new GroupMul.init_T 2
new GroupMul.init_0
do GroupMul.x 1
do GroupMul.inv 1
do GroupMul.x 2
call op_GroupMul_GroupMul_hidden 0 1
do GroupMul.x 3
new GroupAffine.init_T_T 2 3
new GroupAffine.init_0
do GroupAffine.a 1
do GroupAffine.b 1
call op_GroupAffine_GroupAffine_hidden 0 1
do GroupAffine.a 2
do GroupAffine.b 2
do GroupAffine.inv 1
do GroupAffine.a 3
do GroupAffine.b 3
do GroupAffine.apply 0 4
call op_GroupSum_GroupSum_qualified 0 2
do GroupSum.x 4
call op_GroupMul_GroupMul_qualified 0 1
do GroupMul.x 4
call op_GroupAffine_GroupAffine_qualified 0 1
do GroupAffine.apply 4 4
do GroupAffine.inv 0
do GroupAffine.a 5
do GroupAffine.b 5
'''
        expected = ['new', 'new', 'ok 7', 'ok 0', 'ok obj', 'ok -7', 'ok obj', 'ok 0',
                    'new', 'new', 'ok 1', 'ok obj', 'ok 1', 'ok obj', 'ok 2',
                    'new', 'new', 'ok 1', 'ok 0', 'ok obj', 'ok 2', 'ok 3',
                    'ok obj', 'ok 1', 'ok 0', 'ok 11',
                    'ok obj', 'ok 0', 'ok obj', 'ok 2', 'ok obj', 'ok 11',
                    'ok obj', 'ok 0', 'ok -1']
        friends.FriendTranslationTests().compare(header, cases, expected)

    def test_signed_template_division_and_remainder_truncate_toward_zero(self):
        cases, expected = [], []
        for a in [-7, -1, 0, 1, 7]:
            for b in [-3, -2, -1, 1, 2, 3]:
                quotient = abs(a) // abs(b) * (-1 if (a < 0) != (b < 0) else 1)
                for name, result in [('quotient', quotient), ('remainder', a - quotient * b)]:
                    cases.append(f'call {name} {a} {b}')
                    expected.append(f'ok {result}')
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
template<class T> T quotient(T a, T b) { return a / b; }
template<class T> T remainder(T a, T b) { return a % b; }
}
''', '\n'.join(cases) + '\n', expected)

    def test_fresh_group_translation_satisfies_pure_model_contracts(self):
        texts = [lean_translate.translate_file(ROOT / 'library/algebraic_structure/group.hpp', []),
                 (ROOT / 'Proofs/Cpp/Lib/GroupMath.lean').read_text(),
                 (ROOT / 'Proofs/Cpp/Group.lean').read_text()]
        imports = list(dict.fromkeys(line for text in texts for line in text.splitlines()
                                    if line.startswith('import ') and line not in
                                    ('import Proofs.Cpp.Gen.Group', 'import Proofs.Cpp.Lib.GroupMath')))
        body = '\n'.join('\n'.join(line for line in text.splitlines()
                                   if not line.startswith('import ')) for text in texts)
        with tempfile.TemporaryDirectory() as directory:
            proof = Path(directory) / 'Group.lean'
            proof.write_text('\n'.join(imports) + '\n' + body)
            result = subprocess.run([str(ROOT / '.tools/elan/bin/lake'), 'env', 'lean', str(proof)],
                cwd=ROOT, env=dict(os.environ, ELAN_HOME=str(ROOT / '.tools/elan')),
                text=True, capture_output=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
