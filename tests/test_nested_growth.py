"""Growing integer rows through nested bindings, without double-counted headers."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'tools'))
sys.path.insert(0, str(ROOT / 'verifier'))
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network
from test_scalar_ir import lean_environment

HEADER = '''import Proofs.CppNestedProgram
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedProgram Proofs.CppScalar
def i32 : Ty := ⟨32,true,false⟩
def atom : Element := .integer i32
def initial (items : List Value) (capacity limit : Nat) : Frame :=
  ⟨⟨⟨[some ⟨.vector atom,none,some 0,[1,2]⟩,
        some ⟨atom,some 0,none,[]⟩,some ⟨atom,some 0,none,[]⟩]⟩,
      ⟨[some ⟨0,[.child 1,.child 2],2,64,0⟩,
         some ⟨1,items,capacity,limit,0⟩,some ⟨2,[.integer 99],1,64,0⟩],0,0,capacity+4⟩⟩,
     [true,false,false],
     [⟨0,.vector atom,true,.root 0⟩,⟨1,atom,true,.child ⟨0,0,0⟩⟩,
      ⟨1,atom,false,.child ⟨0,0,0⟩⟩,⟨2,atom,true,.child ⟨0,0,1⟩⟩]⟩
'''


def items(xs):
    return '[' + ','.join(f'Value.integer ({x})' for x in xs) + ']'


class NestedGrowthTests(unittest.TestCase):
    def test_growing_rows_lifetimes_and_nested_accounting(self):
        checks, native, expected = [HEADER], [
            '#include "experiments/library/cpp/template/small_template.hpp"',
            '#include <vector>', '#include <iostream>', '#include <cassert>', 'int main(){'], []
        for case, (size, spare) in enumerate((n, s) for n in [0, 1, 2, 3] for s in [0, 2]):
            values = list(range(size))
            capacity, epoch, work, peak = size + spare, 0, 0, 0
            base = capacity + 4
            name = f'f{case}_0'
            checks += [f'def {name} := initial {items(values)} {capacity} 64',
                       f'#guard {name}.state.wellFormed']
            native += ['{std::vector<std::vector<int>> g(2);',
                       'g[0]={' + ','.join(map(str, values)) + '};g[1]={99};',
                       f'g[0].reserve({capacity});auto* sibling=&g[1][0];']
            for step in range(8):
                old = name
                value = values[0] if values else 17
                full = len(values) == capacity
                newcap = max(1, 2 * len(values)) if full else capacity
                localpeak = capacity + newcap + 2 if full else capacity + 2
                work += len(values) + 3 if full else 2
                peak = max(peak, capacity + 4 + localpeak - (capacity + 1) - base, 0)
                name = f'f{case}_{step+1}'
                checks += [f'#guard ({old}.append 1 i32 ({value})).isSome',
                           f'def {name} := ({old}.append 1 i32 ({value})).getD {old}',
                           f'#guard {name}.state.wellFormed',
                           f'#guard {name}.state.forest == {old}.state.forest',
                           f'#guard {name}.bindings == {old}.bindings',
                           f'#guard {name}.state.storage.work == {work}',
                           f'#guard {name}.state.storage.peak == {peak}',
                           f'#guard {name}.state.liveSpace == {newcap+4}',
                           f'#guard ({name}.resolve 1 atom |>.map (·.2.capacity)) == some {newcap}',
                           f'#guard {name}.read ⟨3,i32,true,⟨2,0,0⟩⟩ == some 99',
                           f'#guard {name}.append 2 i32 0 == none',
                           f'#guard {name}.append 0 i32 0 == none']
                if values:
                    checks += [f'#guard {name}.read ⟨1,i32,true,⟨1,{epoch},0⟩⟩ == '
                               + ('none' if full else f'some ({values[0]})')]
                values.append(value)
                epoch += int(full)
                capacity = newcap
                checks += [f'#guard ({name}.state.storage.lookup 1 |>.map (·.items)) == some {items(values)}']
                native += ['if(g[0].empty())g[0].emplace_back(17);else g[0].emplace_back(g[0][0]);',
                           'assert(sibling==&g[1][0] && *sibling==99);',
                           'std::cout<<g[0].capacity();for(int x:g[0])std::cout<<" "<<x;std::cout<<"\\n";']
                expected.append([capacity, *values])
            native.append('}')
        native.append('}')
        # Logical max_size saturation and failure, plus permission/type checks.
        checks += ['def capped := initial [.integer 1,.integer 2,.integer 3] 3 5',
                   'def capped1 := (capped.append 1 i32 4).getD capped',
                   '#guard (capped1.resolve 1 atom |>.map (·.2.capacity)) == some 5',
                   'def capped2 := (capped1.append 1 i32 5).getD capped1',
                   '#guard capped2.state.wellFormed',
                   '#guard capped2.append 1 i32 6 == none',
                   '#guard capped.append 1 i32 2147483648 == none',
                   '#guard capped.append 1 i32 (-2147483649) == none',
                   '#guard capped.append 99 i32 0 == none']
        # Exercise the actual statement runtime used by generated AST models.
        checks += ['def ns : NState := {scalars := ⟨[],[],0,0,0⟩,frame := initial [] 0 64,slots := [.vector 0],scope := 0,peak := 0}',
                   'def statement := NStmt.append (.row (.local 0) atom (.literal i32 0)) i32 (.literal i32 17)',
                   '#guard (statement.run ns |>.map (·.state.frame.state.wellFormed)) == some true',
                   '#guard (statement.run ns |>.bind fun r => r.state.frame.state.storage.lookup 1 |>.map (·.items)) == some [.integer 17]']
        with tempfile.TemporaryDirectory(prefix='nested-growth-') as directory:
            scratch = Path(directory)
            source = scratch / 'source.hpp'
            source.write_text('#include <vector>\nnamespace cp {int append_row(std::vector<std::vector<int>>& g,int i,int x){g[i].emplace_back(x);return 0;}}\n')
            generated = emit_lean(lower_source(source), 'GrowthSource')
            checks[0] = generated + HEADER.replace('import Proofs.CppNestedProgram\n', '')
            checks += [
                'def astCall := GrowthSource.append_row.callFuel 40 ns [.vectorReference 0,.value (.literal i32 0),.value (.literal i32 17)]',
                '#guard (match astCall with | .finished (s,_) => (s.frame.state.storage.lookup 1).map (·.items) | _ => none) == some [.integer 17]',
                '#guard (match astCall with | .finished (s,_) => s.frame.state.wellFormed | _ => false)',
            ]
            native.insert(1, '#include "source.hpp"')
            native.insert(-1, '{std::vector<std::vector<int>> g(1);assert(cp::append_row(g,0,17)==0);assert(g[0]==std::vector<int>{17});}')
            lean = scratch / 'checks.lean'
            lean.write_text('\n'.join(checks))
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(lean)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            check_compiler()
            cpp, executable = scratch / 'native.cpp', scratch / 'native'
            cpp.write_text('\n'.join(native))
            subprocess.run(['g++', *FLAGS, '-fsanitize=undefined', '-fno-sanitize-recover=all',
                            '-I', str(ROOT), str(cpp), '-o', str(executable)], cwd=ROOT, check=True)
            result = subprocess.run([str(executable)], check=True, capture_output=True, text=True)
            self.assertEqual([list(map(int, row.split())) for row in result.stdout.splitlines()], expected)


if __name__ == '__main__':
    disable_network()
    unittest.main()
