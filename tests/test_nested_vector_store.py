"""Nested payload/ownership agreement, scope destruction and root transfer."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'tools'))
from test_scalar_ir import lean_environment
from test_vector_ownership import forest_tags, tag
from check_public import FLAGS, check_compiler
from offline import disable_network

HEADER = '''import Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorStore Proofs.CppVectorOwnership
def i32 : Proofs.CppScalar.Ty := ⟨32,true,false⟩
def atom : Element := .integer i32
def row : Element := .vector atom
'''


def buffer(owner, items, capacity):
    items = [f'(Value.integer ({item[len(".integer "):]}))' if item.startswith('.integer ') else item for item in items]
    return f'some ⟨{owner},[{",".join(items)}],{capacity},64,{owner+1}⟩'


def buffers(n, k):
    return [buffer(0, ['.integer 19'], 4),
            buffer(1, [f'.child {i}' for i in range(2, n+2)], n+2),
            *[buffer(i+2, [f'.integer {v}' for v in [i, 7, -2][:k]], k+2) for i in range(n)],
            buffer(n+2, [f'.child {n+3}'], 2),
            buffer(n+3, [f'.child {n+4}'], 3),
            buffer(n+4, ['.integer 91'], 5)]


def state(tags, objects):
    return f'⟨⟨[{",".join(tags)}]⟩,⟨[{",".join(objects)}],7,0,0⟩⟩'


class NestedStoreTests(unittest.TestCase):
    def lean(self, scratch, text, succeeds=True):
        path = scratch / 'checks.lean'
        path.write_text(text)
        lake, env = lean_environment()
        result = subprocess.run([lake, 'env', 'lean', str(path)], cwd=ROOT, env=env,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, succeeds, result.stdout + result.stderr)

    def test_payload_retirement_and_native_return(self):
        with tempfile.TemporaryDirectory(prefix='nested-store-') as directory:
            scratch = Path(directory)
            checks = [HEADER]
            expected = []
            for n in range(9):
                for k in range(4):
                    name = f's{n}_{k}'
                    tags, objects = forest_tags(n), buffers(n, k)
                    kept = objects[:n+2] + ['none']*3
                    checks.extend([
                        f'def {name} : State := {state(tags, objects)}',
                        f'#guard {name}.wellFormed',
                        f'#guard {name}.liveSpace == {n*(k+3)+19}',
                        f'#guard {name}.destroyWork 1 == {2*n+6}',
                        f'#guard ({name}.retireScope 1 |>.map (·.storage.objects)) == some [{objects[0]},{",".join(["none"]*(n+4))}]',
                        f'#guard ({name}.retireScope 1 |>.map (·.storage.work)) == some {2*n+13}',
                        f'def moved_{name} := ({name}.transfer 1 row 1 0).bind (·.retireScope 1)',
                        f'#guard (moved_{name}.map (·.wellFormed)) == some true',
                        f'#guard (moved_{name}.map (·.storage.objects)) == some [{",".join(kept)}]',
                        f'#guard (moved_{name}.map (·.storage.work)) == some 12',
                        f'#guard (moved_{name}.map (·.storage.peak)) == some {n*(k+3)+19}',
                        f'#guard (moved_{name}.map (·.liveSpace)) == some {n*(k+3)+8}',
                        f'#guard (moved_{name}.bind (·.retireScope 0) |>.map (·.storage.objects)) == some [{",".join(["none"]*(n+5))}]',
                        f'#guard (moved_{name}.bind (·.retireScope 0) |>.map (·.storage.work)) == some {2*n+14}',
                        f'#guard {name}.transfer 1 row 0 2 == none',
                        f'#guard {name}.transfer {n+3} row 1 0 == none',
                        f'#guard {name}.transfer 1 atom 1 0 == none',
                        f'#guard ({name}.retired 1).storage.readReference (accepts atom) ⟨{n+4},{n+5},0⟩ == none',
                        f'#guard ({name}.retired 1).storage.readReference (accepts atom) ⟨0,1,0⟩ == {name}.storage.readReference (accepts atom) ⟨0,1,0⟩',
                        f'#guard ({name}.retireScope 99 |>.map (·.storage.objects)) == some {name}.storage.objects',
                    ])
                    for i in range(n):
                        checks.append(f'#guard (moved_{name}.bind fun s => s.storage.readReference (accepts atom) ⟨{i+2},{i+3},0⟩ |>.map (·.value)) == ' +
                                      (f'some (Value.integer {i})' if k else 'none'))
                    expected.append(f'{n} {k} 19 ' + ' '.join(str(v) for i in range(n) for v in [i, 7, -2][:k]))
            baseline_tags, baseline_buffers = forest_tags(2), buffers(2, 3)
            malformed = []
            for index, replacement in [
                (1, buffer(1, ['.child 3', '.child 2'], 4)),
                (1, buffer(1, ['.child 2'], 4)),
                (1, buffer(1, ['.child 2', '.child 99'], 4)),
                (1, buffer(1, ['.integer 2', '.integer 3'], 4)),
                (2, buffer(2, ['.child 3'], 4)),
                (2, buffer(99, ['.integer 0'], 4)),
                (2, buffer(2, ['.integer 2147483648'], 4)),
                (2, buffer(2, ['.integer (-2147483649)'], 4)),
                (2, buffer(2, ['.integer 0', '.integer 7'], 1)),
                (2, buffer(2, ['.integer 0'], 65)),
                (2, 'none'),
            ]:
                bad = baseline_buffers.copy()
                bad[index] = replacement
                malformed.append(state(baseline_tags, bad))
            malformed.append(state(baseline_tags, baseline_buffers[:-1]))
            malformed.append(state(baseline_tags, baseline_buffers + ['none']))
            bad_tags = baseline_tags.copy()
            bad_tags[2] = 'none'
            malformed.append(state(bad_tags, baseline_buffers))
            for i, bad in enumerate(malformed):
                checks.extend([f'def bad{i} : State := {bad}',
                               f'#guard !bad{i}.wellFormed',
                               f'#guard bad{i}.retireScope 1 == none',
                               f'#guard bad{i}.transfer 1 row 1 0 == none'])
            self.lean(scratch, '\n'.join(checks))
            source = scratch / 'native.cpp'
            source.write_text('''#include "experiments/library/cpp/template/small_template.hpp"
#include <vector>
#include <cassert>
#include <utility>
#include <iostream>
std::vector<std::vector<int>> make(unsigned n,unsigned k){
 std::vector<std::vector<int>> ret(n);ret.reserve(n+2);
 std::vector<std::vector<std::vector<int>>> scratch(1,std::vector<std::vector<int>>(1,std::vector<int>{91}));
 for(unsigned i=0;i<n;++i){ret[i].reserve(k+2);int a[]={int(i),7,-2};for(unsigned j=0;j<k;++j)ret[i].push_back(a[j]);}
 assert(scratch[0][0][0]==91);return ret;
}
int main(){for(unsigned n=0;n<=8;++n)for(unsigned k=0;k<=3;++k){
 std::vector<int> caller{19};auto ret=make(n,k);
 std::vector<const int*> addresses;for(auto& r:ret)addresses.push_back(r.data());
 auto moved=std::move(ret);assert(moved.size()==n && caller[0]==19);
 std::cout<<n<<' '<<k<<' '<<caller[0]<<' ';
 bool first=true;for(unsigned i=0;i<n;++i){assert(moved[i].data()==addresses[i]);assert(moved[i].size()==k);
  for(int v:moved[i]){if(!first)std::cout<<' ';first=false;std::cout<<v;}}
 std::cout<<'\\n';
}}
''')
            check_compiler()
            for flags in [[], ['-fno-elide-constructors']]:
                binary = scratch / 'native'
                subprocess.run(['g++', *FLAGS, *flags, '-fsanitize=address,undefined',
                                '-fno-omit-frame-pointer', '-I', str(ROOT), str(source), '-o', str(binary)],
                               cwd=ROOT, check=True)
                environment = os.environ.copy()
                environment['ASAN_OPTIONS'] = 'detect_leaks=0:halt_on_error=1'
                environment['UBSAN_OPTIONS'] = 'halt_on_error=1:print_stacktrace=1'
                result = subprocess.run([str(binary)], env=environment, capture_output=True, text=True, check=True)
                self.assertEqual(result.stdout.splitlines(), expected)
            print(f'nested store: {sum(x.count("#guard") for x in checks)} Lean guards, 72 native return/move cases, {len(malformed)} malformed payloads')

    def test_mutations_reject_payload_drift_and_buffer_leaks(self):
        with tempfile.TemporaryDirectory(prefix='nested-store-mutation-') as directory:
            scratch = Path(directory)
            baseline = (ROOT / 'Proofs/CppNestedVectorStore.lean').read_text().replace(
                'namespace Proofs.CppNestedVectorStore', 'namespace Proofs.NestedStoreMutation').replace(
                'end Proofs.CppNestedVectorStore', 'end Proofs.NestedStoreMutation')
            self.lean(scratch, baseline)
            for original, changed in [
                ('buffer.items = tag.children.map Value.child', 'True'),
                ('if s.forest.context owner = some scope then none else buffer', 'buffer'),
            ]:
                self.assertEqual(baseline.count(original), 1)
                self.lean(scratch, baseline.replace(original, changed), False)


if __name__ == '__main__':
    disable_network()
    unittest.main()
