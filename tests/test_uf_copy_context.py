"""Copy export, source retention, permissions and comparison with the C++ fixture."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'verifier'),str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from check_public import check_compiler
from offline import disable_network


class UfCopyContextTests(unittest.TestCase):
    def test_multiple_owners_permissions_moved_from_and_actual_source_calls(self):
        setup = (ROOT/'tests/lean/union_find_read_multi_owner.lean').read_text().split('namespace UfReadMultiOwnerWorldExamples')[0]
        setup = '\n'.join(line for line in setup.splitlines() if not line.startswith('import '))
        needle = '⟨0,parents,4,limit,0⟩'
        self.assertEqual(setup.count(needle),1)
        setup = setup.replace(needle,'⟨0,parents,9,limit,5⟩')
        parts = ['import Proofs.UfCopyContext', 'import Proofs.UfCopyContextPreserve',
            'import Proofs.UfCopyNewState', 'import Proofs.UfCopyCounterCall', 'import Proofs.UfCopyReadQueries', setup,
            (ROOT/'tests/lean/union_find_copy_context.lean').read_text(),
            (ROOT/'tests/lean/union_find_read_receiver.lean').read_text(),
            (ROOT/'tests/lean/union_find_copy_moved.lean').read_text()]
        with tempfile.TemporaryDirectory(prefix='uf-copy-context-') as directory:
            proof = Path(directory)/'check.lean'
            proof.write_text('\n'.join(parts))
            lake,env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertNotIn('warning:',result.stdout+result.stderr)

    def test_native_copy_independence_const_source_and_moved_from_scalars(self):
        check_compiler()
        with tempfile.TemporaryDirectory(prefix='uf-copy-context-native-') as directory:
            source = Path(directory)/'native.cpp'
            binary = Path(directory)/'native'
            source.write_text('#include "'+str(ROOT/'experiments/library/cpp/template/small_template.hpp')+'"\n'+
                NATIVE.replace('SOURCE_HEADER',str(ROOT/'tests/imports/union_find_public_compat.hpp')))
            subprocess.run(['g++','-std=c++17','-O1','-g','-fno-access-control',
                '-fsanitize=address,undefined','-fno-sanitize-recover=all','-fno-omit-frame-pointer',
                '-fno-pie','-no-pie',str(source),'-o',str(binary)],cwd=ROOT,check=True)
            env = os.environ.copy()
            env['ASAN_OPTIONS']='detect_leaks=0:halt_on_error=1'
            env['UBSAN_OPTIONS']='halt_on_error=1:print_stacktrace=1'
            subprocess.run([str(binary)],cwd=ROOT,env=env,check=True)


NATIVE = r'''
#include <cassert>
#include <utility>
#include <vector>
#include "SOURCE_HEADER"
int main() {
  cp::UnionFind source(4), other(2);
  source.unite(0,1); source.unite(2,3);
  source._ps.reserve(9); source._n=99;
  const std::vector<int> parents=source._ps;
  const int* element=&source._ps[0];
  const cp::UnionFind& borrowed=source;
  cp::UnionFind target(borrowed);
  const cp::UnionFind readonly(borrowed);
  assert(target._ps==parents && readonly._ps==parents);
  assert(target._ps.capacity()==4 && readonly._ps.capacity()==4);
  assert(target._n==99 && readonly._n==99);
  assert(target._num_groups==2 && readonly.num_groups()==2);
  assert(target.size(3)==2 && readonly.size(3)==2);
  const cp::UnionFind& targetRead=target;
  assert(targetRead.same(0,1) && !targetRead.same(1,3));
  assert(readonly.same(3,2) && readonly.same(3,3) && !readonly.same(0,3));
  assert(target._ps==parents && readonly._ps==parents);
  assert(target._ps.data()!=source._ps.data());
  assert(target.unite(0,2)==0 && target.num_groups()==1);
  assert((target._ps==std::vector<int>{-4,0,0,2}));
  assert(targetRead.same(1,3) && !readonly.same(1,3));
  assert(readonly._ps==parents && readonly._num_groups==2 && readonly._n==99);
  assert(source._ps==parents && source._n==99 && source._num_groups==2);
  assert(source._ps.capacity()>=9 && *element==-2);
  assert(other._ps==std::vector<int>(2,-1) && other.num_groups()==2);
  cp::UnionFind moving(4);
  moving.unite(0,1); moving.unite(2,3); moving.unite(0,2);
  cp::UnionFind owner(std::move(moving));
  assert(moving._ps.empty() && moving._n==4 && moving._num_groups==1);
  const cp::UnionFind& weak=moving;
  cp::UnionFind empty(weak); const cp::UnionFind emptyConst(weak);
  assert(empty._ps.empty() && emptyConst._ps.empty());
  assert(empty._n==4 && emptyConst._n==4);
  assert(empty.num_groups()==1 && emptyConst.num_groups()==1);
  assert(owner.size(3)==4 && owner.num_groups()==1);
}
'''

if __name__ == '__main__':
    disable_network()
    unittest.main()
