"""Global state is explicit, shared by callees, and independent of local names."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import lean_translate
from lean_env import lean_environment
LAKE, LAKE_ENV = lean_environment()


class GlobalStateTests(unittest.TestCase):
    def test_balanced_prime_certificate_examples(self):
        source = '''import Proofs.Cpp.Lib.PrimeCertificate
open Proofs.Cpp.PrimeCertificate
example : Proofs.Fermat.IsPrime 998244353 := modint_prime
example : oddChecks 9 0 0 = false := by decide
example : oddChecks 25 0 1 = false := by decide
example : oddChecks 49 0 2 = false := by decide
example : oddChecks 32761 0 7 = false := by decide
example : oddChecks 997 0 4 = true := by decide
'''
        with tempfile.TemporaryDirectory() as directory:
            lean = Path(directory) / 'Certificate.lean'
            lean.write_text(source)
            result = subprocess.run([LAKE, 'env', 'lean', str(lean)],
                                    text=True, capture_output=True, cwd=ROOT, timeout=30,
                                    env=LAKE_ENV)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_differential_protocol_keeps_global_state(self):
        import test_lean_model_friend as friends
        friends.FriendTranslationTests().compare('''#pragma once
namespace cp {
struct Box { int value; Box(int x) : value(x) {} int get() const { return value; } };
int counter;
unsigned table[3];
void add(int amount) { counter += amount; table[1] = (unsigned)(counter + 1); }
int read() { return counter + (int)table[1]; }
}
''', 'new Box.init 41\ncall read\ndo Box.get_ 0\ncall add 4\ncall read\n'
            'call add -2\ncall read\ndo Box.get_ 0\n',
            ['new', 'ok 0', 'ok 41', 'ok', 'ok 9', 'ok', 'ok 5', 'ok 41'])

    def test_stateless_commands_do_not_materialize_unused_large_globals(self):
        import test_lean_model_friend as friends
        friends.FriendTranslationTests().compare('''namespace cp {
unsigned unused[20000003];
int successor(int x) { return x + 1; }
unsigned read() { return unused[0]; }
}
''', 'call successor 41\ncall successor -1\n', ['ok 42', 'ok 0'])

    def test_methods_share_independent_scalar_global_state(self):
        import test_lean_model_friend as friends
        friends.FriendTranslationTests().compare('''namespace cp {
int counter;
int advance(int amount) { counter += amount; return counter; }
struct Box {
  int value;
  Box(int x) : value(x) {}
  int read() const { return counter + value; }
  int step() { return advance(value); }
};
}
''', 'new Box.init 2\nnew Box.init 7\ndo Box.read 0\ndo Box.step 0\n'
            'do Box.read 1\ncall advance -5\ndo Box.step 1\ndo Box.read 0\n',
            ['new', 'new', 'ok 2', 'ok 2', 'ok 9', 'ok -3', 'ok 4', 'ok 6'])

    def test_same_named_child_namespace_function_keeps_its_state(self):
        import clang_ast
        import test_lean_model_friend as friends
        header = """namespace cp {
int choose(int x) { return x + 1; }
namespace runtime {
int choose(int x) {
  static unsigned calls = 0;
  ++calls;
  return x + (int)calls;
}
}
int through(int x) { return runtime::choose(x); }
}
"""
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'Source.hpp'
            source.write_text(header)
            self.assertEqual(clang_ast.public_declarations(source),
                             ['FunctionDecl:choose', 'FunctionDecl:runtime::choose', 'FunctionDecl:through'])
        friends.FriendTranslationTests().compare(
            header, 'call choose 41\ncall runtime.choose 1\ncall through 10\ncall choose 8\n',
            ['ok 42', 'ok 2', 'ok 12', 'ok 9'])

    def model(self, source, imports=()):
        with tempfile.TemporaryDirectory() as directory:
            header = Path(directory) / 'Source.hpp'
            header.write_text(source)
            return lean_translate.translate_file(header, list(imports))

    def test_local_static_vectors_and_markers_persist_independently(self):
        import test_lean_model_friend as friends
        friends.FriendTranslationTests().compare("""#include <vector>
namespace cp {
int first(int value) {
  static unsigned calls = 0;
  static std::vector<int> values;
  ++calls;
  values.push_back(value);
  return values[0] + (int)calls;
}
int second(int value) {
  static unsigned calls = 0;
  static std::vector<int> values;
  ++calls;
  values.push_back(value);
  return values[0] + (int)calls;
}
int through(int value) { return first(value); }
}
""", 'call first 10\ncall second 20\ncall through 40\ncall second -7\n',
            ['ok 11', 'ok 21', 'ok 12', 'ok 22'])

    def test_local_static_rejects_lazy_initializers_and_reference_returns(self):
        for definition in (
            'unsigned f(unsigned x) { static unsigned counter = x; return counter; }',
            'unsigned f() { static volatile unsigned counter = 0; return counter; }',
            'unsigned &f() { static unsigned counter = 0; return counter; }',
            'int f() { static std::vector<int> values(1, 7); return values[0]; }',
        ):
            with self.subTest(definition=definition):
                with self.assertRaisesRegex(lean_translate.Unsupported, 'local static'):
                    self.model('#include <vector>\nnamespace cp {' + definition + '}')

    def test_class_static_scalar_is_shared_by_constructors_methods_and_callers(self):
        import test_lean_model_friend as friends
        friends.FriendTranslationTests().compare("""namespace cp {
struct Number {
  static unsigned modulus;
  unsigned value;
  Number(unsigned input) : value(input % modulus) {}
  void add(unsigned input) { value = (value + input) % modulus; }
  unsigned get() const { return value; }
};
unsigned Number::modulus = 7;
void change(unsigned input) { Number::modulus = input; }
unsigned wrapped(unsigned input) { return Number(input).get(); }
}
""", 'new Number.init 16\ndo Number.get_ 0\ncall change 11\n'
            'do Number.add 0 16\ndo Number.get_ 0\ncall wrapped 16\n',
            ['new', 'ok 2', 'ok', 'ok', 'ok 7', 'ok 5'])

    def test_class_static_rejects_alias_and_unsequenced_reads(self):
        declarations = """namespace cp {
struct Number {
  static unsigned modulus;
  unsigned set(unsigned value) { modulus = value; return modulus; }
};
unsigned Number::modulus = 7;
"""
        for function, error in (
            ('unsigned f(unsigned &ref) { return ref + Number::modulus; }', 'may alias'),
            ('unsigned f(Number x) { return Number::modulus + x.set(9); }', 'separate full expressions'),
            ('unsigned f(Number x) { return x.modulus; }', 'evaluate the receiver'),
        ):
            with self.subTest(function=function):
                with self.assertRaisesRegex(lean_translate.Unsupported, error):
                    self.model(declarations + function + '}')

    def test_canonical_modint_with_original_global_api(self):
        from test_modint_power_model import ModIntPowerModelTests
        original = (ROOT / 'experiments/library/cpp/modint/modint.hpp').read_text()
        source = (ModIntPowerModelTests().class_source().rsplit('}', 1)[0]
                  + '\nusing mint =' + original.split('\nusing mint =', 1)[1] + '\n}\n')
        model = self.model(source, ['Proofs.Cpp.PowMod', 'Proofs.Cpp.Lib.ModIntFactorial'])
        for declaration in ('def cp.MAX_FAC : Int := 20000003',
                            'abbrev cp.mint ', 'abbrev cp.mint17 ',
                            'structure cp.GlobalState ', 'def cp.C ', 'def cp.init ',
                            'def cp.initializeGlobals '):
            self.assertIn(declaration, model)
        self.assertIn('cppGlobals.fac.size = 20000003', model)
        self.assertIn('for _ in [:(20000003 : Nat)]', model)
        # Compile the unchanged 20,000,003-element API. Runtime tests use
        # separate small fixtures, without evaluating this large startup loop.
        with tempfile.TemporaryDirectory() as directory:
            lean = Path(directory) / 'Canonical.lean'
            lean.write_text(model + (ROOT / 'tests/lean/modint_constructor_contract.lean').read_text()
                            + (ROOT / 'tests/lean/modint_arithmetic_contract.lean').read_text()
                            + (ROOT / 'tests/lean/modint_power_contract.lean').read_text()
                            + (ROOT / 'tests/lean/modint_globals_contract.lean').read_text())
            result = subprocess.run([LAKE, 'env', 'lean', str(lean)],
                                    text=True, capture_output=True, cwd=ROOT, timeout=60,
                                    env=LAKE_ENV)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_class_array_default_construction_and_assignment(self):
        source = '''namespace cp {
template<unsigned N> struct Cell {
  unsigned x;
  Cell() : x(N) {}
  Cell(unsigned value) : x(value) {}
};
using cell = Cell<7u>;
cell cells[4];
cell last;
unsigned total() {
  unsigned result = last.x;
  for (int i=0; i<4; i++) result += cells[i].x;
  return result;
}
void init() {
  for (int i=0; i<4; i++) cells[i] = cell((unsigned)i + 1u);
  last = cells[3];
}
}
'''
        model = self.model(source)
        main = '''
open Proofs.Cpp.Gen
def main : IO Unit := do
  match cp.initializeGlobals.run 0 with
  | none => throw (IO.userError "startup failed")
  | some (state, _) =>
    match (cp.total state).run 0 with
    | none => throw (IO.userError "total failed")
    | some ((value, _), _) => IO.println value
    match (cp.init state).run 0 with
    | none => throw (IO.userError "init failed")
    | some (state, _) =>
      match (cp.total state).run 0 with
      | none => throw (IO.userError "total after init failed")
      | some ((value, state), _) =>
        IO.println value
        IO.println state.last.x
'''
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            driver = scratch / 'Driver.lean'
            driver.write_text(model + main)
            lean = subprocess.run([LAKE, 'env', 'lean', '--run', str(driver)],
                                  text=True, capture_output=True, cwd=ROOT, timeout=60,
                                  env=LAKE_ENV)
            self.assertEqual(lean.returncode, 0, lean.stdout + lean.stderr)
            self.assertEqual(lean.stdout, '35\n14\n4\n')
            cpp = scratch / 'driver.cpp'
            cpp.write_text(source + '\n#include <iostream>\nint main() { std::cout<<cp::total()<<"\\n";'
                           'cp::init();std::cout<<cp::total()<<"\\n"<<cp::last.x<<"\\n";}')
            binary = scratch / 'driver'
            subprocess.run(['g++', '-std=c++23', '-O1', '-fsanitize=address,undefined', str(cpp), '-o', str(binary)],
                           check=True, timeout=60)
            native = subprocess.run([str(binary)], text=True, capture_output=True, check=True, timeout=20,
                                    env=dict(os.environ, ASAN_OPTIONS='detect_leaks=0:halt_on_error=1',
                                             UBSAN_OPTIONS='halt_on_error=1'))
            self.assertEqual(native.stdout, lean.stdout)

    def test_shared_scalar_array_state_and_aliases(self):
        source = '''#pragma once
namespace cp {
using index = int;
using word = unsigned;
const int SIZE = 5;
index counter;
word table[SIZE];
void add(index amount) {
  counter += amount;
  table[2] = table[2] + 3u;
}
index read() { return counter + (index)table[2]; }
index session(index counter) {
  index cppGlobal_counter = 100;
  add(counter);
  add(1);
  return read() + cppGlobal_counter;
}
index unrelated(index value) { return value + 1; }
}
'''
        lean_main = '''
open Proofs.Cpp.Gen
def main : IO Unit := do
  let initial : cp.GlobalState := { counter := 0, table := #[0, 0, 0, 0, 0] }
  match (cp.session 4 initial).run 0 with
  | none => throw (IO.userError "session failed")
  | some ((value, state), _) =>
    IO.println s!"{value} {state.counter} {state.table[2]!}"
    match (cp.session (-2) state).run 0 with
    | none => throw (IO.userError "second session failed")
    | some ((value, state), _) =>
      IO.println s!"{value} {state.counter} {state.table[2]!}"
  match (cp.read { counter := 0, table := #[] }).run 0 with
  | none => IO.println "invalid size rejected"
  | some _ => throw (IO.userError "invalid fixed array size accepted")
'''
        with tempfile.TemporaryDirectory(dir=ROOT / 'tests/diff', prefix='.globals-') as directory:
            scratch = Path(directory)
            header = scratch / 'Source.hpp'
            header.write_text(source)
            model = lean_translate.translate_file(header, [])
            self.assertIn('def cp.unrelated (value : Int) : Cpp.M Int', model)
            driver = scratch / 'Driver.lean'
            driver.write_text(model + lean_main)
            env = dict(LAKE_ENV,
                       ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
            lean = subprocess.run([LAKE, 'env', 'lean', '--run', str(driver)],
                                  text=True, capture_output=True, cwd=ROOT, env=env, timeout=60)
            self.assertEqual(lean.returncode, 0, lean.stdout + lean.stderr)
            cpp = scratch / 'driver.cpp'
            cpp.write_text('#include "Source.hpp"\n#include <iostream>\nint main() {\n'
                           'for (int n : {4,-2}) { auto r=cp::session(n); '
                           'std::cout<<r<<" "<<cp::counter<<" "<<cp::table[2]<<"\\n"; }\n}\n')
            binary = scratch / 'driver'
            subprocess.run(['g++', '-std=c++23', '-O1', '-fsanitize=address,undefined', str(cpp), '-o', str(binary)],
                           check=True, timeout=60)
            native = subprocess.run([str(binary)], text=True, capture_output=True, env=env, check=True, timeout=20)
            self.assertEqual(native.stdout, '111 5 6\n116 4 12\n')
            self.assertEqual(lean.stdout, native.stdout + 'invalid size rejected\n')

    def test_reject_unsupported_global_effects_and_aliases(self):
        declarations = (
            'thread_local int value;',
            'extern int value;',
            'volatile int value;',
            'int value = 7;',
            'using ref = int&;',
            'using cv = const int;',
            'int value; int f(const int& x) { value++; return x; }',
            'int value[2]; struct X { int f() { return value[0]; } };',
            'int value; int change() { value++; return value; } '
            'int f() { return value + change(); }',
            'int value; int change() { value++; return value; } '
            'int f() { return change() + change(); }',
            'int value[2]; struct GlobalState { int x; };',
            'int value[2]; const int GlobalState = 3;',
            'int value; int f() { static int cached; value++; return ++cached; }',
            'struct X { int x; X():x(0){} '
            'X& operator=(const X& y) { x=y.x+1; return *this; } }; '
            'X value; void f() { value=X(); }',
        )
        for declaration in declarations:
            with self.subTest(declaration=declaration):
                with self.assertRaises(lean_translate.Unsupported):
                    self.model('namespace cp { ' + declaration + ' }')


if __name__ == '__main__':
    unittest.main()
