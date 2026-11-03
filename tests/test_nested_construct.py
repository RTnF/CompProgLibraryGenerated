"""Nested vector construction (`vector<vector<int>> ret(w)`) and child operations."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'tools'))
from test_scalar_ir import lean_environment
from check_public import FLAGS, check_compiler
from offline import disable_network

HEADER = '''import Proofs.CppNestedOps
open Proofs.CppNestedOps Proofs.CppNestedConstruct Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppVectorOwnership Proofs.CppVector
def i32 : Proofs.CppScalar.Ty := ⟨32,true,false⟩
def atom : Element := .integer i32
def row : Element := .vector atom
'''
VALUES = [3, -4, 9, 0]


def caller(k):
    """A caller-owned const vector<int> `v` of length k and capacity k+1."""
    items = ','.join(f'Value.integer ({v})' for v in VALUES[:k])
    return ('⟨⟨[some ⟨atom,none,some 0,[]⟩]⟩,'
            f'⟨[some ⟨0,[{items}],{k+1},64,0⟩],0,0,0⟩⟩')


def scenario(k, w, capacity):
    """Lean guards for: ret(w); ret[0].assign(v.begin(),v.end()); fill ret[i]."""
    name = f'c{k}_{w}_{capacity}'
    lines = [
        f'def {name} : Frame.State := {caller(k)}'.replace('Frame.State', 'State'),
        f'#guard {name}.wellFormed',
        f'def built_{name} := {name}.constructRows i32 1 {w}',
        f'#guard (built_{name}.map (·.wellFormed)) == some true',
        f'#guard (built_{name}.map (·.storage.objects.length)) == some {w+2}',
        f'#guard (built_{name}.map (·.storage.work)) == some {w+1}',
        f'#guard (built_{name}.map (·.liveSpace)) == some {w+1+k+2}',
        f'#guard ({name}.constructRows i32 1 {w} |>.map (·.storage.lookup 1 |>.map (·.items))) == '
        f'some (some [{",".join(f"Value.child {2+j}" for j in range(w))}])',
        f'#guard {name}.constructRows i32 1 {2**60} == none',
    ]
    frame = (f'(⟨(built_{name}.getD {name}),[false,true{",false"*w}],'
             '[⟨0,atom,false,.root 0⟩]⟩ : Frame)')
    lines.append(f'def f0_{name} : Frame := {frame}')
    lines.append(f'def f1_{name} := (f0_{name}.bindRoot 1 row 1 true)')
    current = f'(f1_{name}.map Prod.fst).getD f0_{name}'
    lines.append(f'def g1_{name} : Frame := {current}')
    expected = []
    state = f'g1_{name}'
    slots = 2
    for j in range(w):
        lines.append(f'def b{j}_{name} := {state}.bindChild 1 atom {j} true')
        lines.append(f'def h{j}_{name} : Frame := (b{j}_{name}.map Prod.fst).getD {state}')
        lines.append(f'#guard (b{j}_{name}.map Prod.snd) == some {slots}')
        state = f'h{j}_{name}'
        slots += 1
    # ret[0].assign(v.begin(), v.end())
    lines.append(f'def r_{name} := {state}.iteratorRange 0 0 i32 false true')
    lines.append(f'#guard (r_{name}.map (fun r => (r.first, r.last))) == some (0, {k})')
    lines.append(f'def a_{name} : Frame := '
                 f'(r_{name}.bind fun r => {state}.assign 2 0 i32 r).getD {state}')
    lines.append(f'#guard (a_{name}.state.storage.lookup 2 |>.map (·.items)) == '
                 f'some [{",".join(f"Value.integer ({v})" for v in VALUES[:k])}]')
    lines.append(f'#guard a_{name}.state.wellFormed')
    lines.append(f'#guard ({state}.assign 0 2 i32 ⟨2,0,0,0⟩ |>.isSome) == false')
    state = f'a_{name}'
    for j in range(1, w):
        slot = 2+j
        lines.append(f'def k{j}_{name} : Frame := ({state}.reserve {slot} atom {capacity}).getD {state}')
        lines.append(f'#guard ({state}.reserve {slot} atom {capacity} |>.isSome) == true')
        state = f'k{j}_{name}'
        values = [(VALUES[(j+t) % 4]) for t in range(capacity)]
        for t, value in enumerate(values):
            lines.append(f'def p{j}_{t}_{name} : Frame := ({state}.append {slot} i32 ({value})).getD {state}')
            lines.append(f'#guard ({state}.append {slot} i32 ({value}) |>.isSome) == true')
            state = f'p{j}_{t}_{name}'
        lines.append(f'#guard ({state}.append {slot} i32 0 |>.isSome) == true')
        lines.append(f'#guard ({state}.state.storage.lookup {slot+0} |>.map (·.items)) == '
                     f'some [{",".join(f"Value.integer ({v})" for v in values)}]')
        lines.append(f'#guard {state}.state.wellFormed')
    # size and const protection of the caller's vector
    lines.append(f'#guard ({state}.size 0 atom |>.map Prod.snd) == some {k}')
    lines.append(f'#guard ({state}.append 0 i32 1 |>.isSome) == false')
    lines.append(f'#guard ({state}.reserve 0 atom 99 |>.isSome) == false')
    return '\n'.join(lines), name


NATIVE = '''#include "experiments/library/cpp/template/small_template.hpp"
#include <vector>
#include <iostream>
int main(){
  const int vals[4]={3,-4,9,0};
  for(int k=0;k<=4;++k)for(int w=1;w<=3;++w){
    std::vector<int> v(vals,vals+k);
    std::vector<std::vector<int>> ret(w);
    for(int i=0;i<w;++i) if(!ret[i].empty()||ret[i].capacity()!=0) return 1;
    ret[0].assign(v.begin(),v.end());
    std::cout<<k<<' '<<w<<' '<<ret.size()<<' '<<ret[0].size();
    for(int x:ret[0]) std::cout<<' '<<x;
    std::cout<<'\\n';
  }
}
'''


class NestedConstructTests(unittest.TestCase):
    def lean(self, scratch, text, succeeds=True):
        path = scratch / 'checks.lean'
        path.write_text(text)
        lake, env = lean_environment()
        result = subprocess.run([lake, 'env', 'lean', str(path)], cwd=ROOT, env=env,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, succeeds, result.stdout + result.stderr)

    def test_construction_and_child_operations(self):
        with tempfile.TemporaryDirectory(prefix='nested-construct-') as directory:
            scratch = Path(directory)
            checks = [HEADER]
            expected = []
            for k in range(5):
                for w in range(1, 4):
                    text, _ = scenario(k, w, 2)
                    checks.append(text)
                    expected.append(f'{k} {w} {w} {k}' + ''.join(f' {v}' for v in VALUES[:k]))
            self.lean(scratch, '\n'.join(checks))
            cpp = scratch / 'native.cpp'
            cpp.write_text(NATIVE)
            binary = scratch / 'native'
            check_compiler()
            subprocess.run(['g++', *FLAGS, '-fsanitize=address,undefined', '-fno-omit-frame-pointer',
                            '-I', str(ROOT), str(cpp), '-o', str(binary)], cwd=ROOT, check=True)
            environment = os.environ.copy()
            environment['ASAN_OPTIONS'] = 'detect_leaks=0:halt_on_error=1'
            environment['UBSAN_OPTIONS'] = 'halt_on_error=1:print_stacktrace=1'
            result = subprocess.run([str(binary)], env=environment, capture_output=True, text=True, check=True)
            self.assertEqual(result.stdout.splitlines(), expected)
            print(f'nested construct: {sum(x.count("#guard") for x in checks)} Lean guards, '
                  f'{len(expected)} native constructions')

    def test_mutations_are_rejected(self):
        with tempfile.TemporaryDirectory(prefix='nested-construct-mutation-') as directory:
            scratch = Path(directory)
            baseline = (ROOT / 'Proofs/CppNestedConstruct.lean').read_text()
            baseline = baseline.replace('namespace Proofs.CppNestedConstruct', 'namespace Proofs.NestedConstructMutation')
            baseline = baseline.replace('end Proofs.CppNestedConstruct', 'end Proofs.NestedConstructMutation')
            self.lean(scratch, baseline)
            for original, changed in [
                ('(List.range count).map fun j => root+1+j', '(List.range count).map fun j => root+j'),
                ('⟨.integer ty,some root,none,[]⟩', '⟨.integer ty,none,none,[]⟩'),
                ('⟨root,(rowIds root count).map Value.child,count,rowLimit,0⟩',
                 '⟨root,(rowIds root count).map Value.child,count+1,rowLimit,0⟩'),
                ('CppVectorBindings.supported ty ∧ count ≤ rowLimit then',
                 'CppVectorBindings.supported ty ∧ True then'),
            ]:
                self.assertEqual(baseline.count(original), 1, original)
                self.lean(scratch, baseline.replace(original, changed), False)


if __name__ == '__main__':
    disable_network()
    unittest.main()
