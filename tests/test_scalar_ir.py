"""End-to-end scalar generation, mutation and refusal tests."""

import copy
import os
import shutil
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
sys.path.insert(0, str(ROOT / "tools"))
import scalar_ir
from offline import disable_network


def lean_environment():
    environment = os.environ.copy()
    local = ROOT / ".tools/elan/bin/lake"
    if local.is_file():
        environment["ELAN_HOME"] = str(ROOT / ".tools/elan")
        return str(local), environment
    lake = shutil.which("lake")
    if lake is None:
        raise RuntimeError("lake is required for scalar verification tests")
    return lake, environment


class ScalarTests(unittest.TestCase):
    def lower(self, text):
        with tempfile.TemporaryDirectory(prefix="scalar-source-") as directory:
            source = Path(directory) / "source.cpp"
            source.write_text("namespace cp { " + text + " }")
            return scalar_ir.lower_source(source)

    def test_names_do_not_select_semantics(self):
        original = self.lower("unsigned int first(unsigned int a) { const auto x = a + 1U; return x; }")
        renamed = self.lower("unsigned int different(unsigned int z) { const auto local = z + 1U; return local; }")
        lhs, rhs = copy.deepcopy(original), copy.deepcopy(renamed)
        lhs["functions"][0]["name"] = rhs["functions"][0]["name"]
        self.assertEqual(lhs, rhs)
        changed = self.lower("unsigned int first(unsigned int a) { const auto x = a - 2U; return x; }")
        self.assertNotEqual(original["functions"][0]["locals"], changed["functions"][0]["locals"])

    def test_return_alias_uses_clang_type_and_never_alias_spelling(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'alias.cpp'
            for underlying, width, signed in [('unsigned int',32,False), ('long',64,True)]:
                source.write_text(f'using ll={underlying}; namespace cp {{ ll f(ll a){{return a;}} }}')
                function = scalar_ir.lower_source(source)['functions'][0]
                self.assertEqual(function['result']['type'], {'width':width,'signed':signed,'boolean':False})
                self.assertEqual(function['parameters'][0], function['result']['type'])
            source.write_text('using alias=int; namespace cp {alias f(){return 1;}}')
            with self.assertRaises(ValueError):
                scalar_ir.lower_source(source)

    def test_unsupported_nodes_are_refused(self):
        for text in ["int f(int *p) { return *p; }", "float f(float a) { return a / 2; }",
                     "int &f(int a) { return a; }",
                     "int f(int a) { while (a > 0) --a; return a; }",
                     "int f(int a) { a = 2; return a; }", "int f(int a) { return a << 1; }",
                     "int f(int a) { return a && true; }", "int f(int a) { return a ? 1 : 2; }",
                     "template<class T> T f(T x) { return x; }", "int x; int f() { return x; }",
                     "int f(int a) { return a; } int f(long a) { return a; }",
                     "int f() { static int local = 1; return local; }",
                     "int f() { volatile int local = 1; return local; }"]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                self.lower(text)

    def test_generated_lean_and_cpp_agree_and_overflow_is_refused(self):
        text = """unsigned int wrap(unsigned int a) { const unsigned int x = a + 1U; return x * 2U; }
int signed_add(int a, int b) { return a + b; }
bool less(int a, int b) { return a < b; }
unsigned long long wide(unsigned long long a) { return a - 1ULL; }
bool truth(int a) { return a; }
int negative(int a) { return -a; }
"""
        ir = self.lower(text)
        with tempfile.TemporaryDirectory(prefix="scalar-check-") as directory:
            scratch = Path(directory)
            source = scratch / "source.cpp"
            source.write_text('#include <iostream>\nnamespace cp { ' + text + ''' }
int main() {
  std::cout << cp::wrap(4294967295U) << ' ' << cp::wrap(7U) << ' '
            << cp::signed_add(-3, 7) << ' ' << cp::less(-3, 7) << ' '
            << cp::wide(0) << ' ' << cp::truth(-7) << ' ' << cp::negative(-7);
}
''')
            binary = scratch / "cpp"
            subprocess.run(["g++", "-std=c++17", "-O2", str(source), "-o", str(binary)], check=True)
            values = subprocess.check_output([str(binary)], text=True).split()
            calls = ["wrap.call [4294967295]", "wrap.call [7]", "signed_add.call [-3, 7]",
                     "less.call [-3, 7]", "wide.call [0]", "truth.call [-7]", "negative.call [-7]"]
            lean = scalar_ir.emit_lean(ir, "ScalarTest")
            lean += "\nopen ScalarTest\n"
            for call, value in zip(calls, values):
                lean += f"#guard ({call}).map (·.value) == some ({value})\n"
            lean += """#guard signed_add.call [2147483647, 1] == none
#guard negative.call [-2147483648] == none
#guard wrap.call [-1] == none
#guard wrap.call [] == none
#guard signed_add.call [1, 2, 3] == none
#guard (wrap.call [7]).map (·.work) == some 8
"""
            proof = scratch / "test.lean"
            proof.write_text(lean)
            lake, environment = lean_environment()
            subprocess.run([lake, "env", "lean", str(proof)],
                           cwd=ROOT, env=environment, check=True)
            # A changed operator must violate a specification for the old source.
            mutated = self.lower("unsigned int wrap(unsigned int a) { const auto x = a + 1U; return x + 2U; }")
            proof.write_text(scalar_ir.emit_lean(mutated, "MutationTest") +
                             "\n#guard (MutationTest.wrap.call [7]).map (·.value) == some 16\n")
            result = subprocess.run([lake, "env", "lean", str(proof)],
                                    cwd=ROOT, env=environment, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("did not evaluate to `true`", result.stdout + result.stderr)
            boundary = self.lower("bool less(int a, int b) { return a <= b; }")
            proof.write_text(scalar_ir.emit_lean(boundary, "BoundaryTest") +
                             "\n#guard (BoundaryTest.less.call [0, 0]).map (·.value) == some 0\n")
            result = subprocess.run([lake, "env", "lean", str(proof)], cwd=ROOT, env=environment,
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("did not evaluate to `true`", result.stdout + result.stderr)

    def test_every_supported_arithmetic_and_comparison_operation(self):
        operators = ["a + b", "a - b", "a * b", "a < b", "a <= b", "a > b",
                     "a >= b", "a == b", "a != b", "+a", "-a", "!a"]
        declarations = "\n".join(f"int op{i}(int a, int b) {{ return {op}; }}"
                                  for i, op in enumerate(operators))
        ir = self.lower(declarations)
        with tempfile.TemporaryDirectory(prefix="scalar-operators-") as directory:
            scratch = Path(directory)
            inputs = [(a, b) for a in range(-3, 4) for b in range(-3, 4)]
            calls = [(f"op{i}", a, b) for i in range(len(operators)) for a, b in inputs]
            source = scratch / "test.cpp"
            source.write_text("#include <iostream>\nnamespace cp {\n" + declarations +
                              "\n}\nint main() {\n" + "\n".join(
                                  f"std::cout << cp::{name}({a}, {b}) << '\\n';"
                                  for name, a, b in calls) + "\n}\n")
            binary = scratch / "test"
            subprocess.run(["g++", "-std=c++17", "-O2", str(source), "-o", str(binary)], check=True)
            values = subprocess.check_output([str(binary)], text=True).splitlines()
            self.assertEqual(len(values), len(calls))
            proof = scratch / "test.lean"
            proof.write_text(scalar_ir.emit_lean(ir, "OperatorTest") + "\n" + "\n".join(
                f"#guard (OperatorTest.{name}.call [{a}, {b}]).map (·.value) == some ({value})"
                for (name, a, b), value in zip(calls, values)))
            lake, environment = lean_environment()
            subprocess.run([lake, "env", "lean", str(proof)], cwd=ROOT, env=environment, check=True)

    def test_division_remainder_signs_boundaries_and_faults(self):
        types = [('s32', 'int', 32, True), ('u32', 'unsigned int', 32, False),
                 ('s64', 'long long', 64, True), ('u64', 'unsigned long long', 64, False)]
        declarations = '\n'.join(
            f'{ty} {name}{op}({ty} a, {ty} b) {{ return a {symbol} b; }}'
            for name, ty, _, _ in types for op, symbol in [('q', '/'), ('r', '%')])
        declarations += '\nunsigned int mixed(int a, unsigned int b){return a / b;}'
        ir = self.lower(declarations)
        calls, expected, invalid = [], [], []
        for name, ty, width, signed in types:
            minimum = -(1 << (width - 1)) if signed else 0
            maximum = (1 << (width - int(signed))) - 1
            values = sorted(set(list(range(-7 if signed else 0, 8)) +
                                [minimum, minimum + 1, maximum - 1, maximum]))
            for a in values:
                for b in values:
                    for op in ['q', 'r']:
                        if b == 0 or (signed and a == minimum and b == -1):
                            invalid.append(f'{name}{op}.call [{a}, {b}]')
                            continue
                        quotient = abs(a) // abs(b) * (-1 if (a < 0) != (b < 0) else 1)
                        calls.append((name + op, ty, a, b))
                        expected.append(quotient if op == 'q' else a - quotient * b)
        for a, b in [(-1, 2), (-2147483648, 3), (7, 2)]:
            calls.append(('mixed', 'int', a, b))
            expected.append((a % (1 << 32)) // b)

        def literal(v):
            if v == -(1 << 63):
                return '(-9223372036854775807LL - 1LL)'
            return f'(-{-v}LL)' if v < 0 else f'{v}ULL'

        with tempfile.TemporaryDirectory(prefix='scalar-divrem-') as directory:
            scratch = Path(directory)
            source, binary, proof = scratch / 'test.cpp', scratch / 'test', scratch / 'test.lean'
            source.write_text('#include <iostream>\nnamespace cp {\n' + declarations +
                '\n}\nint main(){\n' + '\n'.join(
                    f"std::cout << cp::{name}(static_cast<{ty}>({literal(a)}), "
                    f"static_cast<{ty}>({literal(b)})) << '\\n';" for name, ty, a, b in calls) + '\n}\n')
            subprocess.run(['g++', '-std=c++17', '-O1', '-fsanitize=undefined',
                '-fno-sanitize-recover=all', str(source), '-o', str(binary)], check=True)
            actual = [int(v) for v in subprocess.check_output([str(binary)], text=True).splitlines()]
            self.assertEqual(actual, expected)
            guards = [f'#guard (DivisionTest.{name}.call [{a}, {b}]).map (·.value) == some ({value})'
                      for (name, _, a, b), value in zip(calls, expected)]
            guards += [f'#guard DivisionTest.{call} == none' for call in invalid]
            guards += ['#guard (DivisionTest.s32q.call [-7, 3]).map (·.work) == some 4']
            proof.write_text(scalar_ir.emit_lean(ir, 'DivisionTest') + '\n' + '\n'.join(guards))
            lake, environment = lean_environment()
            subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=environment, check=True)
            mutated = self.lower('int q(int a, int b){return a % b;}')
            proof.write_text(scalar_ir.emit_lean(mutated, 'MutationTest') +
                '\n#guard (MutationTest.q.call [-7, 3]).map (·.value) == some (-2)\n')
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=environment, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('did not evaluate to `true`', result.stdout + result.stderr)


if __name__ == "__main__":
    disable_network()
    lake, environment = lean_environment()
    subprocess.run([lake, "build", "Proofs.CppScalar"],
                   cwd=ROOT, env=environment, check=True)
    unittest.main()
