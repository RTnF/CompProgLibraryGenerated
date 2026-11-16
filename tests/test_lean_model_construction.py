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
