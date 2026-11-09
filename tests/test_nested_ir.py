"""Nested vector generation from the real doubling source, oracle and mutation checks."""
import itertools
import json
import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
sys.path.insert(0, str(ROOT / 'tools'))
import nested_ir
from test_scalar_ir import lean_environment
from check_public import FLAGS, check_compiler
from offline import disable_network

DIRECTORY = ROOT / 'library'
SOURCE = DIRECTORY / 'array/doubling.hpp'
FIXTURE = ROOT / 'experiments/verification/array/doubling_nested_ir.json'
MAXIMA = [1, 2, 3, 4, 5, 7, 8, 9, 31, 32, 33, 2**32, 2**63, 2**64-1]

HEADER = '''import Proofs.Generated.DoublingNested
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppVectorOwnership Proofs.CppMixedInvoke Proofs.CppLoop
def i32 : Ty := ⟨32,true,false⟩
def u64 : Ty := ⟨64,false,false⟩
def atom : Element := .integer i32
def caller (items : List Int) (kmax : Int) : NState :=
  let buffer : Proofs.CppVector.Buffer Value := ⟨0,items.map Value.integer,items.length+1,64,0⟩
  let state : Proofs.CppNestedVectorStore.State := ⟨⟨[some ⟨atom,none,some 0,[]⟩]⟩,⟨[some buffer],0,0,0⟩⟩
  { scalars := ⟨[⟨u64,kmax⟩],[⟨0,false⟩],0,0,0⟩,
    frame := ⟨state,[false],[⟨0,atom,false,.root 0⟩]⟩,
    slots := [Location.vector 0,Location.scalar 0],scope := 0,peak := 0 }
def ints : List Value → List Int := List.filterMap fun
  | .integer value => some value
  | .child _ => none
def table (fuel : Nat) (items : List Int) (kmax : Int) : Option (List (List Int)) :=
  match Proofs.DoublingNestedInstance.doubling.callFuel fuel (caller items kmax)
      [.vectorReference 0,.value (.variable u64 1)] with
  | .finished (state,.vector owner _) => do
      let root ← state.frame.state.storage.lookup owner
      root.items.mapM fun
        | .child row => (state.frame.state.storage.lookup row).map fun b => ints b.items
        | .integer _ => none
  | _ => none
'''


def reference(items, kmax):
    n, w = len(items), kmax.bit_length()
    rows = [list(items)]
    for _ in range(1, w):
        rows.append([rows[-1][rows[-1][j]] for j in range(n)])
    return rows[:w]


def valid_inputs():
    cases = []
    for n in range(4):
        for items in itertools.product(range(n), repeat=n):
            for kmax in MAXIMA:
                cases.append((list(items), kmax))
    rng = random.Random(20260929)
    for n in (4, 5, 8):
        for _ in range(6):
            items = [rng.randrange(n) for _ in range(n)]
            for kmax in (1, 5, 33, 2**63, 2**64-1):
                cases.append((items, kmax))
    return cases


def lean_list(values):
    return '[' + ','.join(str(v) for v in values) + ']'


class NestedIrTests(unittest.TestCase):
    def compile(self, path, text):
        path.write_text(text)
        lake, env = lean_environment()
        return subprocess.run([lake, 'env', 'lean', str(path)], cwd=ROOT, env=env,
                              capture_output=True, text=True)

    def test_regeneration_and_independent_oracle(self):
        ir = nested_ir.lower_source(SOURCE, [DIRECTORY])
        self.assertEqual(ir, json.loads(FIXTURE.read_text()))
        generated = nested_ir.emit_lean(ir, 'Proofs.DoublingNestedInstance')
        self.assertEqual(generated, (ROOT / 'Proofs/Generated/DoublingNested.lean').read_text())
        # All cases are checked by one evaluation of one table: the Lean elaborator would otherwise compile a
        # separate definition for each of the hundreds of #guard commands, which dominates the running time.
        cases = []
        for items, kmax in valid_inputs():
            expected = '[' + ','.join(lean_list(row) for row in reference(items, kmax)) + ']'
            cases.append(f'({lean_list(items)}, {kmax}, some {expected})')
        # Violated preconditions fail closed in the model, like a failed assert.
        for items, kmax in [([], 0), ([0], 0), ([1], 3), ([-1, 0], 5), ([0, 2], 5), ([3, 0, 1], 4)]:
            cases.append(f'({lean_list(items)}, {kmax}, none)')
        # The cases can be split into parts (NESTED_IR_PART=i of NESTED_IR_PARTS=n) so that each part stays within the
        # time limit of a single check; the parts together are exactly the full set.
        parts = int(os.environ.get('NESTED_IR_PARTS', '1'))
        part = int(os.environ.get('NESTED_IR_PART', '0'))
        cases = cases[part::parts]
        checks = [HEADER]
        size = 40
        for number, start in enumerate(range(0, len(cases), size)):
            checks.append(f'def oracleCases{number} : List (List Int × Int × Option (List (List Int))) := [\n  '
                          + ',\n  '.join(cases[start:start + size]) + ']\n')
            checks.append(f'#guard oracleCases{number}.all fun (items, kmax, expected) => table 5000 items kmax == expected\n')
        checks.append('#guard table 5 [0] 1 == none\n')
        with tempfile.TemporaryDirectory(prefix='nested-doubling-') as directory:
            result = self.compile(Path(directory) / 'oracle.lean', ''.join(checks))
            self.assertEqual(result.returncode, 0, result.stdout[:3000] + result.stderr[:3000])
        print(f'nested doubling: {len(cases)} cases against the independent oracle in Lean')

    def test_native_cpp17_matches_the_same_oracle(self):
        cases = valid_inputs()
        lines = []
        for items, kmax in cases:
            lines.append(' '.join(str(v) for row in reference(items, kmax) for v in row))
        text = ['#include "experiments/library/cpp/template/small_template.hpp"\n',
                '#include "library/array/doubling.hpp"\n#include <cstdint>\n#include <iostream>\n',
                'int main(){\n']
        for items, kmax in cases:
            values = ','.join(str(v) for v in items)
            text.append(f'{{ std::vector<int> v{{{values}}}; auto t=cp::doubling(v,{kmax}ull);\n'
                        ' bool first=true; for(auto&r:t)for(int x:r){if(!first)std::cout<<\' \';first=false;std::cout<<x;}\n'
                        ' std::cout<<\'\\n\'; }\n')
        text.append('}\n')
        with tempfile.TemporaryDirectory(prefix='nested-doubling-native-') as directory:
            scratch = Path(directory)
            (scratch / 'native.cpp').write_text(''.join(text))
            check_compiler()
            subprocess.run(['g++', *FLAGS, '-fsanitize=address,undefined', '-fno-omit-frame-pointer',
                            '-I', str(ROOT), '-I', str(DIRECTORY), str(scratch / 'native.cpp'),
                            '-o', str(scratch / 'native')], cwd=ROOT, check=True)
            environment = os.environ.copy()
            environment['ASAN_OPTIONS'] = 'detect_leaks=0:halt_on_error=1'
            environment['UBSAN_OPTIONS'] = 'halt_on_error=1:print_stacktrace=1'
            result = subprocess.run([str(scratch / 'native')], env=environment, capture_output=True,
                                    text=True, check=True)
            self.assertEqual(result.stdout.splitlines(), lines)
            # Each failed precondition aborts the real implementation as well.
            for items, kmax in [([], 0), ([0], 0), ([1], 3), ([-1, 0], 5), ([0, 2], 5)]:
                values = ','.join(str(v) for v in items)
                (scratch / 'abort.cpp').write_text(
                    '#include "library/array/doubling.hpp"\n'
                    f'int main(){{ std::vector<int> v{{{values}}}; cp::doubling(v,{kmax}ull); }}\n')
                subprocess.run(['g++', *FLAGS, '-I', str(ROOT), '-I', str(DIRECTORY),
                                str(scratch / 'abort.cpp'), '-o', str(scratch / 'abort')],
                               cwd=ROOT, check=True)
                aborted = subprocess.run([str(scratch / 'abort')], capture_output=True)
                self.assertNotEqual(aborted.returncode, 0)
        print(f'nested doubling: {len(cases)} native C++17 ASan/UBSan tables and 5 aborts')

    def test_renaming_and_source_changes(self):
        original = SOURCE.read_text()
        baseline = nested_ir.lower_source(SOURCE, [DIRECTORY])
        with tempfile.TemporaryDirectory(prefix='nested-doubling-mutations-') as directory:
            scratch = Path(directory) / 'array'
            scratch.mkdir()
            dependencies = Path(directory) / 'number_theory'
            dependencies.mkdir()
            shutil.copy(DIRECTORY / 'number_theory/bit_width_u64.hpp',
                        dependencies / 'bit_width_u64.hpp')
            renamed = original
            for old_name, new_name in [('doubling', 'other_name'), ('ret', 'table'), ('kmax', 'limit'),
                                       ('v', 'graph')]:
                renamed = re.sub(rf'\b{old_name}\b', new_name, renamed)
            (scratch / 'renamed.hpp').write_text(renamed)
            other = nested_ir.lower_source(scratch / 'renamed.hpp', [scratch])
            expected = json.loads(json.dumps(baseline))
            expected['functions'][0]['name'] = 'other_name'
            self.assertEqual(other, expected)
            oracle = []
            for items, kmax in [([1, 2, 0], 5), ([1, 0, 2, 2], 9), ([2, 0, 1, 3, 3], 33)]:
                expected_rows = '[' + ','.join(lean_list(row) for row in reference(items, kmax)) + ']'
                oracle.append(f'#guard table 5000 {lean_list(items)} {kmax} == some {expected_rows}\n')
            changes = [
                ('ret[i - 1][ret[i - 1][j]]', 'ret[i - 1][j]'),
                ('ret[0].assign(v.begin(), v.end());', 'ret[0].assign(v.begin(), v.begin());'),
                ('for (int i = 1; i < w; ++i)', 'for (int i = 1; i <= w; ++i)'),
                ('ret[i].reserve(n);', 'ret[i].reserve(0);'),
                ('std::vector<std::vector<int>> ret(w);', 'std::vector<std::vector<int>> ret(w + 1);'),
            ]
            for old, new in changes:
                with self.subTest(change=new):
                    self.assertIn(old, original)
                    (scratch / 'changed.hpp').write_text(original.replace(old, new))
                    ir = nested_ir.lower_source(scratch / 'changed.hpp', [scratch])
                    self.assertNotEqual(ir, baseline)
                    text = nested_ir.emit_lean(ir, 'Proofs.DoublingNestedInstance')
                    # reserve(0) preserves table values now that append can grow a
                    # buffer. It still changes the allocation/copying costs.
                    preserves_values = old == 'ret[i].reserve(n);'
                    resources = ''
                    if preserves_values:
                        baseline_text = nested_ir.emit_lean(baseline, 'BaselineDoubling')
                        text += '\n' + '\n'.join(line for line in baseline_text.splitlines()
                                                  if not line.startswith('import '))
                        resources = '''
def resources (p : NProgram) : Option (Nat × Nat) :=
  match p.callFuel 5000 (caller [1,2,0] 5)
      [.vectorReference 0,.value (.variable u64 1)] with
  | .finished (state,.vector _ _) => some (state.frame.state.storage.work,state.frame.state.storage.peak)
  | _ => none
#guard (resources BaselineDoubling.doubling).isSome
#guard (resources Proofs.DoublingNestedInstance.doubling).isSome
#guard resources BaselineDoubling.doubling != resources Proofs.DoublingNestedInstance.doubling
'''
                    result = self.compile(scratch / 'changed.lean',
                        text
                        + '\n' + HEADER.replace('import Proofs.Generated.DoublingNested\n', '')
                        + ''.join(oracle) + resources)
                    if preserves_values:
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    else:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn('error', result.stdout + result.stderr)

    def test_unsupported_shapes_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix='nested-unsupported-') as directory:
            scratch = Path(directory)
            prelude = '#include <vector>\n#include <cstdint>\nnamespace cp {\n'
            cases = {
                'parameter return': 'std::vector<int> f(std::vector<int> v) { return v; }',
                'copy of a local': ('std::vector<std::vector<int>> f(int n) { std::vector<std::vector<int>> a(n);'
                                    ' auto b = a; return a; }'),
                'row of a const root assigned': ('void g(const std::vector<std::vector<int>> &a) {'
                                                 ' a[0].reserve(1); }'),
                'user vector lookalike': ('namespace std2 { template<class T> struct vector { T operator[](int) const; }; }'
                                          ' int f(const std2::vector<int> &v) { return v[0]; }'),
            }
            for name, body in cases.items():
                with self.subTest(name):
                    path = scratch / 'case.hpp'
                    path.write_text(prelude + body + '\n}\n')
                    with self.assertRaises(Exception):
                        nested_ir.lower_source(path, [scratch])


if __name__ == '__main__':
    disable_network()
    unittest.main()
