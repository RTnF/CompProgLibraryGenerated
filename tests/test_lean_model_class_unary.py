"""Resolved class unary operators call their selected source declaration once."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import lean_translate
import test_lean_model_friend as friends


class ClassUnaryTests(unittest.TestCase):
    def test_const_member_unary_operators_and_single_evaluation(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
template<unsigned N> struct Box {
  int x;
  Box(int value) : x(value) {}
  Box operator-() const { return Box(-x - (int)N); }
  Box operator+() const { return Box(x + 1); }
  int operator~() const { return x + (int)N; }
  bool operator!() const { return x == 0; }
};
Box<7> make(int& count) { count++; return Box<7>(5); }
int single() { int count=0; Box<7> result = -make(count); return result.x + count*100; }
int all() { Box<7> zero(0); Box<7> positive = +zero; return positive.x*100 + (~zero)*10 + (!zero ? 1 : 0); }
}
''', 'call single\ncall all\n', ['ok 88', 'ok 171'], instance={'N': '7u'}, calls=['single', 'all'])

    def test_free_unary_operators_keep_their_own_semantics(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
struct Box { int x; Box(int value) : x(value) {} };
int operator-(const Box& value) { return value.x + 29; }
Box operator+(const Box& value) { return Box(value.x * 2); }
int run() { Box value(6); Box doubled = +value; return -value + doubled.x; }
}
''', 'call run\n', ['ok 47'], calls=['run'])

    def test_reject_mutation_reference_returns_and_type_parameters(self):
        for source in (
            'struct Box { int x; Box(int v):x(v){} Box operator-(){x++;return *this;} }; '
            'int f(){Box v(1); return (-v).x;}',
            'struct Box { int x; Box(int v):x(v){} const Box& operator-()const{return *this;} }; '
            'int f(){Box v(1); return (-v).x;}',
            'struct Box { int x; Box(int v):x(v){} }; '
            'Box operator-(Box& v){v.x++;return v;} int f(){Box v(1);return (-v).x;}',
            'template<class T> struct Box { T x; Box(T v):x(v){} Box operator-()const{return Box(-x);} }; '
            'int f(){Box<int> v(1);return (-v).x;}',
        ):
            with self.subTest(source=source), tempfile.TemporaryDirectory() as directory:
                header = Path(directory) / 'Source.hpp'
                header.write_text('namespace cp {'+source+'}')
                with self.assertRaises(lean_translate.Unsupported):
                    lean_translate.translate_file(header, [])


if __name__ == '__main__':
    unittest.main()
