"""Generate the complete original Ratio, prove its stream contracts and compare real I/O."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
import lean_translate
import diff_harness
from lean_env import lean_environment
LAKE, LAKE_ENV = lean_environment()


CONCRETE_STREAMS = r'''
namespace StreamTest
open Proofs.Cpp Proofs.Cpp.Gen
structure Input where
  tokens : List (Option Int)
  eof : Bool := false
  failed : Bool := false
  deriving DecidableEq
instance streams : Streams where
  Input := Input
  Output := String
instance : @StreamRead Int streams where
  read input old := do
    if input.failed then return (old, input)
    if input.eof then return (old, { input with failed := true })
    match input.tokens with
    | [] => return (old, { input with eof := true, failed := true })
    | none :: rest => return (0, { input with tokens := rest, failed := true })
    | some value :: rest => return (value, { input with tokens := rest, eof := rest.isEmpty })
instance : @StreamWrite Int streams where
  write output value := pure (String.append output (toString value))
instance : @StreamWrite StreamChar streams where
  write output value := pure ((output : String).push (Char.ofNat value.code.toNat))

def showCase (tokens : List (Option Int)) : IO Unit := do
  let input : Input := { tokens }
  let r : cp.Ratio Int := ⟨7, 3⟩
  let some ((returned, finalInput, result), _) := (cp.op_shr_istream_Ratio input r).run 0
    | throw (IO.userError "extraction failed")
  let some ((text, finalOutput), _) := (cp.op_shl_ostream_Ratio "" result).run 0
    | throw (IO.userError "insertion failed")
  let flags := s!"|{if finalInput.eof then 1 else 0}|{if finalInput.failed then 1 else 0}|{if decide (Eq (α := Input) returned finalInput) then 1 else 0}|{if decide (Eq (α := String) text finalOutput) then 1 else 0}"
  IO.println (String.append text flags)
end StreamTest

def main : IO Unit := do
  StreamTest.showCase [some 2, some 4]
  StreamTest.showCase [some (-5), some 7]
  StreamTest.showCase [some 2]
  StreamTest.showCase []
  StreamTest.showCase [none]
  StreamTest.showCase [some 2, none]
  StreamTest.showCase [some 0, some 0]
'''


CANDIDATE = ROOT / 'tests/fixtures/ratio_reference.hpp'


def complete_header():
    return CANDIDATE.read_text()


class RatioStreamModelTests(unittest.TestCase):
    def test_candidate_preserves_original_api_and_bodies(self):
        original = (ROOT / 'experiments/library/cpp/number/ratio.hpp').read_text()
        body = original[original.index('template <typename T = ll>'):]
        body = body.replace('typename T = ll', 'typename T = std::int64_t')
        body = body.replace('gcd(', 'std::gcd(').replace('lcm(', 'std::lcm(')
        body = body.replace('strong_ordering', 'std::strong_ordering')
        body = body.replace('istream &', 'std::istream &').replace('ostream &', 'std::ostream &')
        candidate = complete_header()
        self.assertEqual(candidate.split('namespace cp {\n\n', 1)[1], body + '\n} // namespace cp\n')

    def test_candidate_standalone_include_and_default_type(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'standalone.cpp'
            source.write_text('#include "' + str(CANDIDATE) + '"\n#include <type_traits>\n#include <sstream>\n'
                'static_assert(std::is_same_v<cp::Ratio<>, cp::Ratio<std::int64_t>>);\n'
                'int main() { cp::Ratio<> r(7, 3); r /= r; std::ostringstream out; out << r;\n'
                'return out.str() != "1"; }\n')
            binary = Path(directory) / 'driver'
            subprocess.run(['g++', '-std=c++20', '-O1', '-fsanitize=address,undefined',
                            '-fno-omit-frame-pointer', str(source), '-o', str(binary)], check=True, timeout=60)
            env = dict(os.environ, ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
            subprocess.run([str(binary)], check=True, env=env, timeout=30)

    def test_concrete_types_require_distinct_stream_contracts(self):
        # Int also models long/long long/char in other contexts. Their stream
        # overloads must not silently share one formatted-I/O contract.
        for body in [
                'std::istream &f(std::istream &s, char &x) { s >> x; return s; }',
                "std::ostream &f(std::ostream &s) { return s << 'ab'; }"]:
            with self.subTest(body=body), tempfile.TemporaryDirectory() as directory:
                source = Path(directory) / 'stream.hpp'
                source.write_text('#include <iostream>\nnamespace cp { ' + body + ' }\n')
                with self.assertRaisesRegex(lean_translate.Unsupported, 'stream'):
                    lean_translate.translate_file(source, [])

    def test_stream_operators_from_separate_headers_can_coexist(self):
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            models = []
            for name in ['First', 'Second']:
                source = scratch / f'{name}.hpp'
                source.write_text('#include <ostream>\nnamespace cp {\n'
                    f'template<class T> struct {name} {{\nT value;\n'
                    f'friend std::ostream &operator<<(std::ostream &out, const {name}& x) {{\n'
                    'return out << x.value; }\n};\n}\n')
                models.append(lean_translate.translate_file(source, []))
            lean = scratch / 'Combined.lean'
            lean.write_text('import Proofs.Cpp.Prelude\n' + '\n'.join(
                '\n'.join(line for line in model.splitlines() if not line.startswith('import '))
                for model in models))
            env = dict(LAKE_ENV)
            result = subprocess.run([LAKE, 'env', 'lean', str(lean)],
                                    cwd=ROOT, capture_output=True, text=True, env=env, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_stream_protocol_rejects_unsupported_numeric_types(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'ratio.hpp'
            source.write_text(complete_header())
            for scalar in ['bool', '__int128']:
                with self.subTest(scalar=scalar), self.assertRaisesRegex(lean_translate.Unsupported, 'stream differential'):
                    diff_harness.Harness(source, {'T': scalar}, 'Unused', standard='c++20')

    def test_generic_harness_stream_arguments_and_object_writeback(self):
        env = dict(LAKE_ENV,
                   ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
        for scalar, bits in [('short', 16), ('int', 32), ('long long', 64)]:
            with self.subTest(scalar=scalar), tempfile.TemporaryDirectory() as directory:
                scratch = Path(directory)
                source = scratch / 'ratio.hpp'
                source.write_text(complete_header())
                model = lean_translate.translate_file(source, [], standard='c++20')
                harness = diff_harness.Harness(source, {'T': scalar}, 'Unused', standard='c++20')
                lo, hi = -(2 ** (bits - 1)), 2 ** (bits - 1) - 1
                cases = [([], 7, 3, True, True), (['x'], 0, 3, False, True),
                         (['2'], 2, 3, True, True), (['2', '4'], 2, 4, True, False),
                         (['2', 'x'], 2, 0, False, True), (['0', '0'], 0, 0, True, False),
                         ([str(hi + 1)], hi, 3, True, True), ([str(lo - 1)], lo, 3, True, True),
                         (['-5', '7'], -5, 7, True, False)]
                commands, expected = [], []
                for i, (tokens, n, d, eof, failed) in enumerate(cases):
                    commands += ['new Ratio.init_T_T 7 3',
                                 ' '.join(['call op_shr_istream_Ratio', str(len(tokens)), *tokens, str(i)]),
                                 f'call op_shl_ostream_Ratio {i}']
                    flags = f' {int(eof)} {int(failed)}'
                    text = str(n) + (f'/{d}' if d > 1 else '')
                    encoded = ' ' + ' '.join([str(len(text)), *[str(ord(c)) for c in text]])
                    expected += ['new', 'ok' + flags + flags + ' objref', 'ok' + encoded + encoded]
                # Extraction preserves raw 2/4: field equality differs from value comparison.
                canonical = len(cases)
                commands += ['new Ratio.init_T_T 1 2',
                             f'do Ratio.op_eq 3 {canonical}',
                             f'do Ratio.op_cmp 3 {canonical}',
                             f'do Ratio.op_cmp 8 {canonical}',
                             f'do Ratio.op_cmp {canonical} 8']
                expected += ['new', 'ok 0', 'ok 0', 'ok -1', 'ok 1']
                cpp = scratch / 'driver.cpp'
                cpp.write_text(harness.cpp_driver())
                binary = scratch / 'driver'
                subprocess.run(['g++', '-std=c++20', '-O1', '-fsanitize=address,undefined',
                                '-fno-omit-frame-pointer', '-I', str(ROOT / 'tests/diff'),
                                str(cpp), '-o', str(binary)], check=True, timeout=60)
                command_text = '\n'.join(commands) + '\n'
                native = subprocess.run([str(binary)], input=command_text, text=True, capture_output=True,
                                        check=True, timeout=30, env=env)
                self.assertEqual(native.stdout.splitlines(), expected)
                lean = scratch / 'Driver.lean'
                lean.write_text(harness.lean_driver().replace('import Unused\n', model, 1))
                actual = subprocess.run([LAKE, 'env', 'lean', '--run', str(lean)],
                                        input=command_text, text=True, capture_output=True, cwd=ROOT,
                                        env=env, timeout=120)
                self.assertEqual(actual.returncode, 0, actual.stdout + actual.stderr)
                self.assertEqual(actual.stdout, native.stdout)

    def test_unsigned_numeric_stream_boundaries(self):
        env = dict(LAKE_ENV,
                   ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
        source = ROOT / 'library/number/ratio.hpp'
        model = lean_translate.translate_file(source, [], standard='c++20')
        for scalar, bits in [('unsigned short', 16), ('unsigned', 32), ('unsigned long long', 64)]:
            hi = 2 ** bits - 1
            cases = [([], 7, 3, True, True), (['x'], 0, 3, False, True),
                     (['2'], 2, 3, True, True), (['2', '4'], 2, 4, True, False),
                     (['2', 'x'], 2, 0, False, True), (['0', '0'], 0, 0, True, False),
                     ([str(hi), '1'], hi, 1, True, False),
                     ([str(hi + 1), '1'], hi, 3, False, True),
                     (['-1', '2'], hi, 2, True, False),
                     ([str(-hi), '1'], 1, 1, True, False),
                     ([str(-hi - 1), '1'], hi, 3, False, True),
                     ([str(-hi + 1), str(hi)], 2, hi, True, False),
                     (['1', str(hi + 1)], 1, hi, True, True),
                     (['1', '-1'], 1, hi, True, False),
                     (['x', '2'], 0, 3, False, True)]
            with self.subTest(scalar=scalar), tempfile.TemporaryDirectory() as directory:
                scratch = Path(directory)
                harness = diff_harness.Harness(source, {'T': scalar}, 'Unused', standard='c++20')
                commands, expected = [], []
                for i, (tokens, n, d, eof, failed) in enumerate(cases):
                    commands += ['new Ratio.init_T_T 7 3',
                                 ' '.join(['call op_shr_istream_Ratio', str(len(tokens)), *tokens, str(i)]),
                                 f'call op_shl_ostream_Ratio {i}']
                    flags = f' {int(eof)} {int(failed)}'
                    text = str(n) + (f'/{d}' if d > 1 else '')
                    encoded = ' ' + ' '.join([str(len(text)), *[str(ord(c)) for c in text]])
                    expected += ['new', 'ok' + flags + flags + ' objref', 'ok' + encoded + encoded]
                commands += ['new Ratio.init_T_T 1 2', f'do Ratio.op_eq 3 {len(cases)}',
                             f'do Ratio.op_cmp 3 {len(cases)}']
                expected += ['new', 'ok 0', 'ok 0']
                cpp = scratch / 'driver.cpp'
                cpp.write_text(harness.cpp_driver())
                binary = scratch / 'driver'
                subprocess.run(['g++', '-std=c++20', '-O1', '-fsanitize=address,undefined',
                                '-fno-omit-frame-pointer', '-I', str(ROOT / 'tests/diff'),
                                str(cpp), '-o', str(binary)], check=True, timeout=60)
                command_text = '\n'.join(commands) + '\n'
                native = subprocess.run([str(binary)], input=command_text, text=True, capture_output=True,
                                        check=True, timeout=30, env=env)
                self.assertEqual(native.stdout.splitlines(), expected)
                lean = scratch / 'Driver.lean'
                lean.write_text(harness.lean_driver().replace('import Unused\n', model, 1))
                actual = subprocess.run([LAKE, 'env', 'lean', '--run', str(lean)],
                                        input=command_text, text=True, capture_output=True, cwd=ROOT,
                                        env=env, timeout=120)
                self.assertEqual(actual.returncode, 0, actual.stdout + actual.stderr)
                self.assertEqual(actual.stdout, native.stdout)

    def test_character_stream_extraction_and_insertion(self):
        env = dict(LAKE_ENV,
                   ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
        source = ROOT / 'library/number/ratio.hpp'
        model = lean_translate.translate_file(source, [], standard='c++20')
        cases = [([], 7, 3, True, True), (['x'], 120, 3, True, True),
                 (['2'], 50, 3, True, True), (['2', '4'], 50, 52, False, False),
                 (['24'], 50, 52, False, False), (['2', 'x'], 50, 120, False, False),
                 (['0', '0'], 48, 48, False, False), (['-1'], 45, 49, False, False),
                 (['123'], 49, 50, False, False), (['x', '2'], 120, 50, False, False),
                 (['2', '400'], 50, 52, False, False), (['0'], 48, 3, True, True)]
        for scalar in ['char', 'signed char', 'unsigned char']:
            with self.subTest(scalar=scalar), tempfile.TemporaryDirectory() as directory:
                scratch = Path(directory)
                harness = diff_harness.Harness(source, {'T': scalar}, 'Unused', standard='c++20')
                commands, expected = [], []
                for i, (tokens, n, d, eof, failed) in enumerate(cases):
                    commands += ['new Ratio.init_T_T 7 3',
                                 ' '.join(['call op_shr_istream_Ratio', str(len(tokens)), *tokens, str(i)]),
                                 f'call op_shl_ostream_Ratio {i}']
                    flags = f' {int(eof)} {int(failed)}'
                    codes = [n] + ([47, d] if d > 1 else [])
                    encoded = ' ' + ' '.join(map(str, [len(codes), *codes]))
                    expected += ['new', 'ok' + flags + flags + ' objref', 'ok' + encoded + encoded]
                commands += ['new Ratio.init_T_T 50 52', f'do Ratio.op_eq 3 {len(cases)}',
                             f'do Ratio.op_cmp 3 {len(cases)}']
                expected += ['new', 'ok 0', 'ok 0']
                # Character insertion emits byte values, including zero and 255,
                # rather than their decimal integer spellings.
                slot = len(cases) + 1
                for value in [0, 1, 47, 127, -1]:
                    if value < 0 and scalar in ('char', 'unsigned char'):
                        continue
                    commands += [f'new Ratio.init_T_T {value} 1', f'call op_shl_ostream_Ratio {slot}']
                    codes = f' 1 {value % 256}'
                    expected += ['new', 'ok' + codes + codes]
                    slot += 1
                cpp = scratch / 'driver.cpp'
                cpp.write_text(harness.cpp_driver())
                binary = scratch / 'driver'
                subprocess.run(['g++', '-std=c++20', '-O1', '-fsanitize=address,undefined',
                                '-fno-omit-frame-pointer', '-I', str(ROOT / 'tests/diff'),
                                str(cpp), '-o', str(binary)], check=True, timeout=60)
                command_text = '\n'.join(commands) + '\n'
                native = subprocess.run([str(binary)], input=command_text, text=True, capture_output=True,
                                        check=True, timeout=30, env=env)
                self.assertEqual(native.stdout.splitlines(), expected)
                lean = scratch / 'Driver.lean'
                lean.write_text(harness.lean_driver().replace('import Unused\n', model, 1))
                actual = subprocess.run([LAKE, 'env', 'lean', '--run', str(lean)],
                                        input=command_text, text=True, capture_output=True, cwd=ROOT,
                                        env=env, timeout=120)
                self.assertEqual(actual.returncode, 0, actual.stdout + actual.stderr)
                self.assertEqual(actual.stdout, native.stdout)

    def test_character_stream_all_input_bytes(self):
        env = dict(LAKE_ENV,
                   ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
        source = ROOT / 'library/number/ratio.hpp'
        model = lean_translate.translate_file(source, [], standard='c++20')
        whitespace = {9, 10, 11, 12, 13, 32}
        cases = []
        for byte in range(256):
            if byte in whitespace:
                cases.append(([byte, 65], 65, 3, True, True))
            else:
                cases.append(([byte, 65], byte if byte < 128 else byte - 256, 65, False, False))
        cases += [([], 7, 3, True, True), ([32, 9], 7, 3, True, True),
                  ([128], -128, 3, True, True), ([0, 0], 0, 0, False, False),
                  ([9, 10, 11, 12, 13, 32, 128, 9, 255], -128, -1, False, False),
                  ([65, 32, 128], 65, -128, False, False),
                  ([65, 9, 10, 11, 12, 13, 32, 66], 65, 66, False, False),
                  ([65, 66, 67], 65, 66, False, False)]
        for scalar in ['char', 'signed char', 'unsigned char']:
            with self.subTest(scalar=scalar), tempfile.TemporaryDirectory() as directory:
                scratch = Path(directory)
                harness = diff_harness.Harness(source, {'T': scalar}, 'Unused', standard='c++20')
                commands, expected = [], []
                typed_cases = [(payload, n % 256 if n < 0 and scalar == 'unsigned char' else n,
                                d % 256 if d < 0 and scalar == 'unsigned char' else d, eof, failed)
                               for payload, n, d, eof, failed in cases]
                for i, (payload, n, d, eof, failed) in enumerate(typed_cases):
                    commands += ['new Ratio.init_T_T 7 3',
                                 ' '.join(['call op_shr_istream_Ratio bytes', str(len(payload)),
                                           *map(str, payload), str(i)]),
                                 f'call op_shl_ostream_Ratio {i}']
                    flags = f' {int(eof)} {int(failed)}'
                    codes = [n % 256] + ([47, d % 256] if d > 1 else [])
                    encoded = ' ' + ' '.join(map(str, [len(codes), *codes]))
                    expected += ['new', 'ok' + flags + flags + ' objref', 'ok' + encoded + encoded]
                commands.append('new Ratio.init_T_T 0 1')
                expected.append('new')
                for i, (_, n, _, _, _) in enumerate(typed_cases[:256]):
                    # A sign-sensitive consumer distinguishes signed extraction
                    # from merely round-tripping the same output byte.
                    commands.append(f'do Ratio.op_cmp {i} {len(cases)}')
                    expected.append(f'ok {(n > 0) - (n < 0)}')
                cpp = scratch / 'driver.cpp'
                cpp.write_text(harness.cpp_driver())
                binary = scratch / 'driver'
                subprocess.run(['g++', '-std=c++20', '-O1', '-fsanitize=address,undefined',
                                '-fno-omit-frame-pointer', '-I', str(ROOT / 'tests/diff'),
                                str(cpp), '-o', str(binary)], check=True, timeout=60)
                command_text = '\n'.join(commands) + '\n'
                native = subprocess.run([str(binary)], input=command_text, text=True, capture_output=True,
                                        check=True, timeout=30, env=env)
                self.assertEqual(native.stdout.splitlines(), expected)
                lean = scratch / 'Driver.lean'
                lean.write_text(harness.lean_driver().replace('import Unused\n', model, 1))
                actual = subprocess.run([LAKE, 'env', 'lean', '--run', str(lean)],
                                        input=command_text, text=True, capture_output=True, cwd=ROOT,
                                        env=env, timeout=120)
                self.assertEqual(actual.returncode, 0, actual.stdout + actual.stderr)
                self.assertEqual(actual.stdout, native.stdout)

    def test_stream_protocol_rejects_mixed_numeric_models(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'ratio.hpp'
            source.write_text(complete_header() + '\nnamespace cp { template <typename U> U identity(U x) { return x; } }\n')
            for other in ['int', 'unsigned long long', 'char']:
                with self.subTest(other=other), self.assertRaisesRegex(lean_translate.Unsupported, 'stream differential'):
                    diff_harness.Harness(source, {'T': 'unsigned', 'U': other}, 'Unused', standard='c++20')

    def test_complete_model_streams_and_contracts(self):
        original = ROOT / 'experiments/library/cpp/number/ratio.hpp'
        header = complete_header()
        cases = ['2 4', '-5 7', '2', '', 'x', '2 x', '0 0']
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            source = scratch / 'ratio.hpp'
            source.write_text(header)
            model = lean_translate.translate_file(source, [], standard='c++20')
            lean = scratch / 'Driver.lean'
            lean.write_text('import Proofs.Cpp.Lib.RatioMath\nimport Proofs.Cpp.Lib.RatioArithmeticSpace\n' + model
                            + (ROOT / 'tests/lean/ratio_arithmetic_contract.lean').read_text()
                            + (ROOT / 'tests/lean/ratio_stream_contract.lean').read_text() + CONCRETE_STREAMS)
            cpp = scratch / 'driver.cpp'
            cpp.write_text('#include "' + str(original) + '"\n#include <sstream>\n#include <string>\n'
                'int main() { std::string line; while (std::getline(std::cin, line)) {\n'
                '  Ratio<long long> r(7, 3); std::istringstream input(line);\n'
                '  bool in_alias = &(input >> r) == &input;\n'
                '  std::ostringstream output; bool out_alias = &(output << r) == &output;\n'
                '  std::cout << output.str() << "|" << input.eof() << "|" << input.fail()\n'
                '            << "|" << in_alias << "|" << out_alias << "\\n";\n'
                '} }\n')
            binary = scratch / 'driver'
            subprocess.run(['g++', '-std=c++20', '-O1', '-fsanitize=address,undefined',
                            '-fno-omit-frame-pointer', '-I', str(ROOT / 'experiments/library/cpp'),
                            str(cpp), '-o', str(binary)], check=True, timeout=60)
            env = dict(LAKE_ENV,
                       ASAN_OPTIONS='detect_leaks=0:halt_on_error=1', UBSAN_OPTIONS='halt_on_error=1')
            expected = subprocess.run([str(binary)], input='\n'.join(cases) + '\n', text=True,
                                      capture_output=True, check=True, timeout=30, env=env).stdout
            actual = subprocess.run([LAKE, 'env', 'lean', '--run', str(lean)],
                                    cwd=ROOT, capture_output=True, text=True, env=env, timeout=120)
            self.assertEqual(actual.returncode, 0, actual.stdout + actual.stderr)
            self.assertEqual(actual.stdout, expected)
            self.assertEqual(len(expected.splitlines()), len(cases))


if __name__ == '__main__':
    unittest.main()
