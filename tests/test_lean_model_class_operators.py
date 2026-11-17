"""Record binary expressions call the selected operator body exactly once."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import lean_translate
import test_lean_model_friend as friends

BOX = '''#pragma once
namespace cp {
template<unsigned N> struct Box {
  unsigned x;
  Box(unsigned value) : x(value) {}
  friend Box operator*(const Box& a, const Box& b) { return Box(a.x * b.x); }
  Box product(const Box& other) const { return *this * other; }
};
Box<7> make(unsigned& calls, unsigned value) { ++calls; return Box<7>(value); }
unsigned run() { Box<7> a(2), b(3); return a.product(b).x; }
unsigned once() {
  unsigned calls = 0;
  auto product = make(calls, 2) * make(calls, 3);
  return calls * 100u + product.x;
}
}
'''


class ClassOperatorTests(unittest.TestCase):
    def model(self, header):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'Operators.hpp'
            source.write_text(header)
            return lean_translate.translate_file(source, [])

    def test_value_template_friend_and_evaluation_count(self):
        friends.FriendTranslationTests().compare(BOX,
            'call run\ncall once\n', ['ok 6', 'ok 206'],
            instance={'N': '9'}, calls=['run', 'once'])

    def test_resolved_member_and_free_operators(self):
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
struct Box {
  unsigned x;
  Box(unsigned value) : x(value) {}
  unsigned operator*(unsigned other) const { return x + other; }
  friend unsigned operator*(const Box& a, const Box& b) { return 100u + a.x + b.x; }
};
unsigned member() { Box a(2); return a * 3u; }
unsigned free() { Box a(2), b(3); return a * b; }
}
''', 'call member\ncall free\n', ['ok 5', 'ok 105'], calls=['member', 'free'])

    def test_unresolved_member_and_free_competition_is_rejected(self):
        header = BOX[:BOX.index('Box<7> make')] + '}\n'
        header = header.replace('  Box product(',
            '  Box operator*(const Box& other) const { return Box(1); }\n  Box product(')
        with self.assertRaisesRegex(lean_translate.Unsupported, 'member candidates'):
            self.model(header)

    def test_explicit_specialization_is_not_replaced_by_primary_template(self):
        header = '''namespace cp {
template<unsigned N> struct Box { unsigned x; Box(unsigned value) : x(value) {} };
template<> struct Box<7> { unsigned x; Box(unsigned value) : x(value + 100) {} };
}
'''
        with self.assertRaisesRegex(lean_translate.Unsupported, 'explicit class template specialization'):
            self.model(header)

    def test_explicit_instantiation_keeps_the_primary_model(self):
        instantiated = BOX.replace('Box<7> make', 'template struct Box<7>;\nBox<7> make')
        self.assertEqual(self.model(instantiated), self.model(BOX))


if __name__ == '__main__':
    unittest.main()
