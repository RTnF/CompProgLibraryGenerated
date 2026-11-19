"""SFINAE trait predicates use tagged packets rather than guessing from Lean Int."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import test_lean_model_friend as friends
import diff_harness
import lean_translate
import unittest
from lean_env import lean_environment
LAKE, LAKE_ENV = lean_environment()

CONDITION_T = '(std::is_signed_v<T> || std::is_same_v<std::remove_cv_t<T>, __int128>)'
CONDITION_U = CONDITION_T.replace('<T>', '<U>')
FUNCTIONS = '''#pragma once
#include <type_traits>
namespace cp {
template<class T, std::enable_if_t<CONDITION_T>* = nullptr>
unsigned signed_kind() { return 1u; }
template<class U, std::enable_if_t<!CONDITION_U>* = nullptr>
unsigned unsigned_kind() { return 2u; }
}
'''.replace('CONDITION_T', CONDITION_T).replace('CONDITION_U', CONDITION_U)


MARKER = '''#pragma once
#include <type_traits>
namespace cp {
struct Marker {
  unsigned x;
  template<class T, std::enable_if_t<CONDITION_T>* = nullptr>
  Marker(T value) : x(1u) {}
  template<class U, std::enable_if_t<!CONDITION_U>* = nullptr>
  Marker(U value) : x(2u) {}
  template<class T, std::enable_if_t<CONDITION_T>* = nullptr>
  void set(T value) { x = 3u; }
  template<class U, std::enable_if_t<!CONDITION_U>* = nullptr>
  void set(U value) { x = 4u; }
};
}
'''.replace('CONDITION_T', CONDITION_T).replace('CONDITION_U', CONDITION_U)

class TypeConstraintTests(unittest.TestCase):
    def test_unresolved_member_on_explicit_dependent_receiver(self):
        header = MARKER.replace('struct Marker {',
            'template<unsigned N, std::enable_if_t<(2 <= N)>* = nullptr> struct Marker {')
        header = header.rsplit('}', 1)[0] + '''
template<unsigned N> void update(Marker<N>& target) { target.set(1ll); }
unsigned run() { Marker<7> target(3u); update(target); return target.x; }
}
'''
        friends.FriendTranslationTests().compare(header, 'call run\n', ['ok 3'],
            instance={'N': '9', 'T': 'unsigned short', 'U': 'long long'}, calls=['run'])

    def test_implicit_construction_inside_value_template_class(self):
        header = MARKER.replace('struct Marker {', 'template<unsigned N> struct Marker {')
        header = header.replace('};',
            '  Marker from() const { Marker result = 1; return result; }\n};')
        header = header.rsplit('}', 1)[0] + '''
unsigned run() { Marker<7> marker(3u); return marker.from().x; }
}
'''
        friends.FriendTranslationTests().compare(header, 'call run\n', ['ok 1'],
            instance={'N': '9', 'T': 'unsigned short', 'U': 'long long'}, calls=['run'])

    def test_mixed_implicit_constructor_ranking_is_not_guessed(self):
        header = MARKER.replace('struct Marker {', 'template<unsigned N> struct Marker {')
        header = header.replace('};', '''
  Marker(long long value) : x(99u) {}
  Marker from() const { Marker result = 1; return result; }
};''')
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'Mixed.hpp'
            source.write_text(header)
            with self.assertRaisesRegex(lean_translate.Unsupported, 'competing implicit conversion'):
                lean_translate.translate_file(source, [])

    def test_dependent_compound_free_candidate_is_not_forced_to_member(self):
        for body in ('*this += other; return *this;', 'return *this += other;'):
            source_text = '''#pragma once
namespace cp {
template<unsigned N> struct Box {
  unsigned x;
  Box(unsigned value) : x(value) {}
  Box& operator+=(const Box& other) { x += 1; return *this; }
  friend Box& operator+=(Box& a, Box& b) { a.x += 100; return a; }
  Box& combine(Box& other) { BODY }
};
unsigned run() { Box<7> a(0), b(0); a.combine(b); return a.x; }
}
'''.replace('BODY', body)
            with self.subTest(body=body), tempfile.TemporaryDirectory() as directory:
                source = Path(directory) / 'Compound.hpp'
                source.write_text(source_text)
                with self.assertRaisesRegex(lean_translate.Unsupported, 'free overload candidates'):
                    lean_translate.translate_file(source, [])

    def test_calls_choose_overloads_and_supply_each_call_packet(self):
        wrappers = """
unsigned run() {
  Marker a(-7); Marker b(7u);
  a.set(0u); b.set(-9);
  return a.x * 10u + b.x;
}
unsigned kinds128() {
  Marker a((__int128)1); Marker b((unsigned __int128)1);
  return a.x * 10u + b.x;
}
unsigned kinds64() {
  Marker a(1ll); Marker b(1ull);
  return a.x * 10u + b.x;
}
unsigned boolean() { Marker a(true); a.set(false); return a.x; }
unsigned chain() { Marker a(-1); Marker b(1u); a.accumulate(b); return a.x; }
unsigned statement() { Marker a(-1); Marker b(1u); a += b; return a.x; }
"""
        marker = MARKER.replace('};', '''
  Marker& operator+=(const Marker& other) { x += other.x; return *this; }
  Marker& accumulate(const Marker& other) { return *this += other; }
};''')
        header = marker.rsplit('}', 1)[0] + wrappers + '}\n'
        friends.FriendTranslationTests().compare(header,
            'call run\ncall kinds128\ncall kinds64\ncall boolean\ncall chain\ncall statement\n',
            ['ok 43', 'ok 12', 'ok 12', 'ok 4', 'ok 3', 'ok 3'],
            instance={'T': 'unsigned short', 'U': 'long long'},
            calls=['run', 'kinds128', 'kinds64', 'boolean', 'chain', 'statement'])

    def test_unknown_dependent_type_is_not_guessed(self):
        header = MARKER.rsplit('}', 1)[0] + '''
template<class V> unsigned unknown(V value) { Marker marker(value); return marker.x; }
}
'''
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'Unknown.hpp'
            source.write_text(header)
            with self.assertRaisesRegex(lean_translate.Unsupported, 'cannot resolve'):
                lean_translate.translate_file(source, [])

    def test_unselected_opposite_condition_does_not_require_false_proof(self):
        header = FUNCTIONS.replace('class U', 'class T').replace('<U>', '<T>')
        for binding, call, expected in [('long long', 'signed_kind', 'ok 1'),
                                        ('unsigned long long', 'unsigned_kind', 'ok 2')]:
            with self.subTest(binding=binding):
                friends.FriendTranslationTests().compare(header,
                    f'call {call}\n', [expected], instance={'T': binding}, calls=[call])

    def test_unsigned_binding_cannot_prove_signed_constraint(self):
        with tempfile.TemporaryDirectory(dir=ROOT / 'tests/diff', prefix='.trait-') as directory:
            source = Path(directory) / 'Trait.hpp'
            source.write_text(FUNCTIONS)
            model = lean_translate.translate_file(source, [])
            harness = diff_harness.Harness(source,
                {'T': 'unsigned long long', 'U': 'unsigned long long'}, 'Unused')
            cpp = Path(directory) / 'Invalid.cpp'
            cpp.write_text(harness.cpp_driver())
            checked_cpp = subprocess.run(['g++', '-std=c++17', '-fsyntax-only',
                                         '-I', str(ROOT / 'tests/diff'), str(cpp)],
                                        capture_output=True, text=True, timeout=60)
            self.assertNotEqual(checked_cpp.returncode, 0)
            self.assertIn('signed_kind', checked_cpp.stderr)
            lean = Path(directory) / 'Invalid.lean'
            lean.write_text(harness.lean_driver().replace('import Unused\n', model, 1))
            checked_lean = subprocess.run([LAKE, 'env', 'lean', str(lean)],
                                         capture_output=True, text=True, cwd=ROOT, timeout=60,
                                         env=LAKE_ENV)
            self.assertNotEqual(checked_lean.returncode, 0)
            self.assertIn('decide', checked_lean.stdout + checked_lean.stderr)

    def test_signed_and_unsigned_int128_have_same_carrier_and_distinct_traits(self):
        for signed, unsigned in [('long long', 'unsigned short'),
                                 ('__int128', 'unsigned __int128'),
                                 ('const __int128', 'unsigned long long')]:
            with self.subTest(signed=signed, unsigned=unsigned):
                friends.FriendTranslationTests().compare(FUNCTIONS,
                    'call signed_kind\ncall unsigned_kind\n', ['ok 1', 'ok 2'],
                    instance={'T': signed, 'U': unsigned})

    def test_plain_standard_trait_does_not_treat_int128_as_signed(self):
        friends.FriendTranslationTests().compare('''#pragma once
#include <type_traits>
namespace cp {
template<class T, std::enable_if_t<!std::is_signed_v<T>>* = nullptr>
unsigned plain() { return 3u; }
}
''', 'call plain\n', ['ok 3'], instance={'T': '__int128'})

    def test_constructor_and_set_overloads_retain_their_conditions(self):
        header = MARKER
        friends.FriendTranslationTests().compare(header,
            'new Marker.init_T 3\nfield Marker.x 0\nnew Marker.init_U 4\nfield Marker.x 1\n'
            'do Marker.set__T 0 5\nfield Marker.x 0\ndo Marker.set__U 0 6\nfield Marker.x 0\n',
            ['new', 'ok 1', 'new', 'ok 2', 'ok', 'ok 3', 'ok', 'ok 4'],
            instance={'T': 'long long', 'U': 'unsigned short'})


if __name__ == '__main__':
    unittest.main()
