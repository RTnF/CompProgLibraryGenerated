"""Nested header lifetimes, captured integer references and const grants."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'tools'))
from test_scalar_ir import lean_environment
from test_nested_vector_store import state, buffers
from test_vector_ownership import forest_tags
from check_public import FLAGS, check_compiler
from offline import disable_network

HEADER = '''import Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppVectorOwnership
def i32 : Proofs.CppScalar.Ty := ⟨32,true,false⟩
def atom : Element := .integer i32
def row : Element := .vector atom
'''


class NestedBindingTests(unittest.TestCase):
    def lean(self, scratch, text, succeeds=True):
        path = scratch / 'checks.lean'
        path.write_text(text)
        lake, env = lean_environment()
        result = subprocess.run([lake, 'env', 'lean', str(path)], cwd=ROOT, env=env,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, succeeds, result.stdout+result.stderr)

    def test_nested_reference_lifetimes_and_native_reserve(self):
        with tempfile.TemporaryDirectory(prefix='nested-bindings-') as directory:
            scratch = Path(directory)
            checks = [HEADER]
            expected = []
            for n in range(5):
                for k in range(4):
                    name = f'f{n}_{k}'
                    permissions = ['true']*(n+5)
                    bindings = ['⟨0,atom,false,.root 0⟩', '⟨1,row,true,.root 1⟩',
                                '⟨1,row,false,.root 1⟩', f'⟨{n+2},(.vector row),true,.root 1⟩']
                    checks.extend([
                        f'def {name} : Frame := ⟨{state(forest_tags(n), buffers(n,k))},[{",".join(permissions)}],[{",".join(bindings)}]⟩',
                        f'#guard {name}.state.wellFormed',
                        f'#guard ({name}.bindRoot 1 row 1 true |>.map Prod.snd) == some 4',
                        f'#guard {name}.bindRoot 1 row 0 true == none',
                        f'#guard {name}.bindRoot 1 atom 1 true == none',
                        f'#guard {name}.bindRoot {n+3} row 1 true == none',
                        f'#guard {name}.reserve 2 row {n+5} == none',
                        f'#guard {name}.reserve 1 row 65 == none',
                        f'#guard {name}.bindChild 1 atom (-1) true == none',
                        f'#guard {name}.bindChild 1 atom {n} true == none',
                        f'#guard {name}.bindChild 2 atom 0 true == none',
                        f'def grown_{name} := {name}.reserve 1 row {n+5}',
                        f'#guard (grown_{name}.map (·.state.wellFormed)) == some true',
                        f'#guard (grown_{name}.map (·.state.storage.work)) == some {n+8}',
                        f'#guard (grown_{name}.map (·.state.storage.peak)) == some {n*(k+3)+n+25}',
                        f'#guard (grown_{name}.map (·.state.liveSpace)) == some {n*(k+3)+22}',
                        f'#guard (grown_{name}.bind (·.resolve 1 row) |>.map (·.2.capacity)) == some {n+5}',
                        # Capture a deeper header whose immediate parent's allocation survives outer reserve.
                        f'def deep_{name} := ({name}.bindChild 3 row 0 true).bind fun p => p.1.bindChild p.2 atom 0 true',
                        f'def deepRef_{name} := deep_{name}.bind fun p => p.1.elementRef p.2 i32 0',
                        f'def deepGrown_{name} := deep_{name}.bind fun p => p.1.reserve 3 (.vector row) 8',
                        f'#guard (deepGrown_{name}.bind (·.resolve 4 row)) == none',
                        f'#guard (deepGrown_{name}.bind (·.resolve 5 atom) |>.map (·.1.owner)) == some {n+4}',
                        f'#guard ((deepGrown_{name}.bind fun f => deepRef_{name}.bind f.read)) == some 91',
                        f'#guard ((deepGrown_{name}.bind fun f => deepRef_{name}.bind fun r => f.write r 92).bind fun f => deepRef_{name}.bind f.read) == some 92',
                    ])
                    for i in range(n):
                        borrow = f'b{n}_{k}_{i}'
                        checks.extend([
                            f'def {borrow} := ({name}.bindChild 1 atom {i} true).map Prod.fst',
                            f'def readonly_{borrow} := ({name}.bindChild 2 atom {i} false).map Prod.fst',
                            f'#guard ({borrow}.bind (·.resolve 4 atom) |>.map (·.1.owner)) == some {i+2}',
                            f'#guard (readonly_{borrow}.bind (·.reserve 4 atom {k+5})) == none',
                            f'#guard ({borrow}.bind (·.elementRef 4 i32 {k})) == none',
                        ])
                        for j, value in enumerate([i, 7, -2][:k]):
                            ref = f'r{n}_{k}_{i}_{j}'
                            checks.extend([
                                f'def {ref} := {borrow}.bind (·.elementRef 4 i32 {j})',
                                f'def outer_{ref} := {borrow}.bind (·.reserve 1 row {n+5})',
                                f'#guard (outer_{ref}.bind (·.resolve 4 atom)) == none',
                                f'#guard (outer_{ref}.bind fun f => {ref}.bind f.read) == some ({value})',
                                f'#guard ((outer_{ref}.bind fun f => {ref}.bind fun r => f.write r ({value+1})).bind fun f => {ref}.bind f.read) == some ({value+1})',
                                f'#guard ({borrow}.bind (·.reserve 4 atom {k+5}) |>.bind fun f => {ref}.bind f.read) == none',
                                f'#guard ({borrow}.bind (·.reserve 4 atom {k+2}) |>.bind fun f => {ref}.bind f.read) == some ({value})',
                                f'#guard (readonly_{borrow}.bind fun f => (f.elementRef 4 i32 {j}).bind fun r => f.write r 99) == none',
                                f'#guard (readonly_{borrow}.bind fun f => (f.elementRef 4 i32 {j}).bind fun r => f.write {{r with writable := true}} 99) == none',
                                f'#guard ({borrow}.bind fun f => {ref}.bind fun r => f.read {{r with address := {{r.address with owner := 0}}}}) == none',
                                f'#guard ({borrow}.bind fun f => {ref}.bind fun r => f.read {{r with element := ⟨64,true,false⟩}}) == none',
                                f'#guard ({borrow}.bind fun f => {ref}.bind fun r => f.write r 2147483648) == none',
                                f'#guard ({borrow}.bind fun f => {ref}.bind fun r => f.write r (-2147483649)) == none',
                            ])
                            expected.append(f'{n} {k} {i} {j} {value} {value+1}')
                    checks.extend([
                        f'#guard ({{{name} with rootWritable := []}} : Frame).resolve 1 row == none',
                        f'#guard ({{{name} with rootWritable := List.replicate {n+5} false}} : Frame).resolve 1 row == none',
                        f'#guard ({{{name} with rootWritable := List.replicate {n+5} false}} : Frame).grant ⟨1,i32,true,⟨1,2,0⟩⟩ == none',
                    ])
            self.lean(scratch, '\n'.join(checks))
            cpp = scratch / 'native.cpp'
            cpp.write_text('''#include "experiments/library/cpp/template/small_template.hpp"
#include <vector>
#include <cassert>
#include <iostream>
#include <cstdint>
int main(){for(unsigned n=0;n<=4;++n)for(unsigned k=0;k<=3;++k){
 std::vector<std::vector<int>> v(n);v.reserve(n+2);
 for(unsigned i=0;i<n;++i){v[i].reserve(k+2);int a[]={int(i),7,-2};for(unsigned j=0;j<k;++j)v[i].push_back(a[j]);}
 auto* root=&v;std::vector<int*> refs;std::vector<std::uintptr_t> headers;
 const auto& cv=v;for(unsigned i=0;i<n;++i){headers.push_back(reinterpret_cast<std::uintptr_t>(&v[i]));
  for(unsigned j=0;j<k;++j){assert(cv[i][j]==v[i][j]);refs.push_back(&v[i][j]);}}
 v.reserve(n+5);assert(root==&v);
 for(unsigned i=0;i<n;++i){assert(headers[i]!=reinterpret_cast<std::uintptr_t>(&v[i]));
  for(unsigned j=0;j<k;++j){auto* p=refs[i*k+j];assert(p==&v[i][j]);int before=*p;*p=before+1;
   std::cout<<n<<' '<<k<<' '<<i<<' '<<j<<' '<<before<<' '<<v[i][j]<<'\\n';}}
 std::vector<std::vector<std::vector<int>>> deep(1,std::vector<std::vector<int>>(1,std::vector<int>{91}));
 auto* row=&deep[0][0];auto* scalar=&(*row)[0];deep.reserve(8);
 assert(row==&deep[0][0] && row->size()==1 && scalar==&deep[0][0][0]);*scalar=92;assert(deep[0][0][0]==92);
}}
''')
            binary = scratch / 'native'
            check_compiler()
            subprocess.run(['g++', *FLAGS, '-fsanitize=address,undefined', '-fno-omit-frame-pointer',
                            '-I', str(ROOT), str(cpp), '-o', str(binary)], cwd=ROOT, check=True)
            environment = os.environ.copy()
            environment['ASAN_OPTIONS'] = 'detect_leaks=0:halt_on_error=1'
            environment['UBSAN_OPTIONS'] = 'halt_on_error=1:print_stacktrace=1'
            result = subprocess.run([str(binary)], env=environment, capture_output=True, text=True, check=True)
            self.assertEqual(result.stdout.splitlines(), expected)
            print(f'nested binding: {sum(x.count("#guard") for x in checks)} Lean guards, {len(expected)} native integer-reference cases and twenty deep-header lifetimes')

    def test_mutations_reject_stale_headers_and_const_escalation(self):
        with tempfile.TemporaryDirectory(prefix='nested-binding-mutation-') as directory:
            scratch = Path(directory)
            baseline = (ROOT / 'Proofs/CppNestedVectorBindings.lean').read_text().replace(
                'namespace Proofs.CppNestedVectorBindings', 'namespace Proofs.NestedBindingMutation').replace(
                'end Proofs.CppNestedVectorBindings', 'end Proofs.NestedBindingMutation')
            self.lean(scratch, baseline)
            for original, changed in [
                ('let result ← readRef parent (accepts (.vector binding.element)) address',
                 'let result ← readRef parent (accepts (.vector binding.element)) {address with epoch := parent.epoch}'),
                ('if writable = true → origin.writable = true then', 'if True then'),
                ('if reference.writable = true ∧ writable = true then', 'if writable = true then'),
            ]:
                self.assertEqual(baseline.count(original), 1)
                self.lean(scratch, baseline.replace(original, changed), False)


if __name__ == '__main__':
    disable_network()
    unittest.main()
