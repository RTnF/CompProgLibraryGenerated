"""Value SFINAE conditions survive translation as explicit Lean proof inputs."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import lean_translate
import test_lean_model_friend as friends
from lean_env import lean_environment
LAKE, LAKE_ENV = lean_environment()

HEADER = '''#pragma once
#include <type_traits>
namespace cp {
template<unsigned N, std::enable_if_t<(2 <= N)> * = nullptr>
struct Box {
  unsigned x;
  Box(unsigned value) : x(value) {}
  unsigned get() const { return x + N; }
  friend unsigned read(const Box& box) { return box.x; }
};
unsigned fixed(unsigned value) { Box<7, nullptr> box(value); return box.get(); }
template<unsigned N> unsigned argument(const Box<N>& box) { return box.x; }
}
'''


class ClassConstraintTests(unittest.TestCase):
    def model(self, header):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'constraint.hpp'
            source.write_text(header)
            return lean_translate.translate_file(source, [])

    def test_constraint_in_structure_and_function_signatures(self):
        model = self.model(HEADER)
        self.assertIn('structure cp.Box (N : UInt32) [Cpp.TemplateConstraint ((2 : UInt32) ≤ N)]', model)
        self.assertIn('[Cpp.TemplateConstraint ((2 : UInt32) ≤ (7 : UInt32))]', model)

    def test_cpp_lean_and_proved_conditions(self):
        for n in (2, 9, 2**32 - 1):
            with self.subTest(n=n):
                friends.FriendTranslationTests().compare(HEADER,
                    'new Box.init 3\ndo Box.get_ 0\ncall read 0\ncall argument 0\ncall fixed 5\n',
                    ['new', f'ok {(3+n) % 2**32}', 'ok 3', 'ok 3', 'ok 12'],
                    instance={'N': str(n)+'u'})

    def test_other_constraint_forms_are_rejected(self):
        for condition in ('2 <= N && N < 10', 'N + 1 > 2'):
            with self.subTest(condition=condition), self.assertRaises(lean_translate.Unsupported):
                self.model(HEADER.replace('Box<7', 'Box<9').replace('2 <= N', condition))

    def test_invalid_binding_is_rejected_by_cpp_and_lean(self):
        model = self.model(HEADER)
        with tempfile.TemporaryDirectory(dir=ROOT / 'tests/diff', prefix='.constraint-') as directory:
            source = Path(directory) / 'Invalid.cpp'
            source.write_text(HEADER + '\ncp::Box<1> invalid(0);\n')
            cpp = subprocess.run(['g++', '-std=c++23', '-fsyntax-only', str(source)],
                                 capture_output=True, text=True, timeout=60)
            self.assertNotEqual(cpp.returncode, 0)
            self.assertIn('enable_if', cpp.stderr)
            lean = Path(directory) / 'Invalid.lean'
            lean.write_text(model + '\nopen Proofs.Cpp.Gen\n'
                            'def invalid : cp.Box (1 : UInt32) := ⟨0⟩\n')
            checked = subprocess.run([LAKE, 'env', 'lean', str(lean)],
                                     capture_output=True, text=True, cwd=ROOT, timeout=60,
                                     env=LAKE_ENV)
            self.assertNotEqual(checked.returncode, 0)
            self.assertIn('TemplateConstraint', checked.stdout + checked.stderr)
            self.assertIn('failed to synthesize', checked.stdout + checked.stderr)

    def test_clang_canonicalizes_octal_value_before_translation(self):
        header = HEADER.replace('Box<7', 'Box<9').replace('2 <= N', '010 <= N')
        self.assertIn('[Cpp.TemplateConstraint ((8 : UInt32) ≤ N)]', self.model(header))
        friends.FriendTranslationTests().compare(header,
            'new Box.init 3\ndo Box.get_ 0\ncall fixed 5\n',
            ['new', 'ok 12', 'ok 14'], instance={'N': '9'})


if __name__ == '__main__':
    unittest.main()
