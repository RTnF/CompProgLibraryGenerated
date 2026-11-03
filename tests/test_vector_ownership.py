"""Typed nested ownership metadata, root transfer and descendant retirement."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'tools'))
from test_scalar_ir import lean_environment
from check_public import FLAGS,check_compiler
from offline import disable_network

HEADER='''import Proofs.CppVectorOwnership
open Proofs.CppVectorOwnership
 def i32 : Proofs.CppScalar.Ty := ⟨32,true,false⟩
 def atom : Element := .integer i32
 def row : Element := .vector atom
'''

def tag(element,parent,scope,children=()):
    option=lambda n:'none' if n is None else f'some {n}'
    return f'some ⟨{element},{option(parent)},{option(scope)},[{",".join(map(str,children))}]⟩'

def forest_tags(n):
    return [tag('atom',None,0),tag('row',None,1,range(2,n+2)),
            *[tag('atom',1,None) for _ in range(n)],
            tag('(.vector row)',None,1,[n+3]),tag('row',n+2,None,[n+4]),tag('atom',n+3,None)]

class OwnershipTests(unittest.TestCase):
    def lean(self,scratch,text,succeeds=True):
        path=scratch/'checks.lean';path.write_text(text)
        lake,env=lean_environment()
        result=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,capture_output=True,text=True)
        self.assertEqual(result.returncode==0,succeeds,result.stdout+result.stderr)

    def test_transfer_retirement_types_and_native_move(self):
        with tempfile.TemporaryDirectory(prefix='nested-ownership-') as directory:
            scratch=Path(directory);checks=[HEADER]
            for n in range(17):
                tags=forest_tags(n);initial='['+','.join(tags)+']'
                exported=tags.copy();exported[1]=tag('row',None,0,range(2,n+2))
                kept=exported[:n+2]+['none']*3
                checks.extend([
                    f'def f{n} : Forest := ⟨{initial}⟩',
                    f'#guard f{n}.wellFormed',
                    f'#guard f{n}.rootOwner {n+4} == some {n+2}',
                    f'#guard f{n}.context {n+4} == some 1',
                    f'#guard (f{n}.retireScope 1 |>.map (·.objects)) == some [{tags[0]},{",".join(["none"]*(n+4))}]',
                    f'#guard (f{n}.transfer 1 row 1 0 |>.map (·.objects)) == some [{",".join(exported)}]',
                    f'#guard ((f{n}.transfer 1 row 1 0).bind (·.retireScope 1) |>.map (·.objects)) == some [{",".join(kept)}]',
                    f'#guard ((f{n}.transfer 1 row 1 0).bind (·.retireScope 1) |>.bind (·.context 1)) == some 0',
                    f'#guard f{n}.transfer 1 row 0 2 == none',
                    f'#guard f{n}.transfer {n+3} row 1 0 == none',
                    f'#guard f{n}.transfer 1 atom 1 0 == none',
                ])
                for owner in range(2,n+2):
                    checks.extend([
                        f'#guard f{n}.rootOwner {owner} == some 1',
                        f'#guard ((f{n}.transfer 1 row 1 0).bind (·.retireScope 1) |>.bind (·.context {owner})) == some 0',
                    ])
            baseline=forest_tags(2)
            malformed=[]
            for index,replacement in [
                (1,tag('row',None,1,[2,2,3])),
                (1,tag('row',None,1,[2,99])),
                (2,tag('atom',4,None)),
                (2,tag('atom',1,1)),
                (2,tag('row',1,None)),
                (0,tag('atom',None,None)),
                (0,tag('atom',None,0,[2])),
                (2,tag('atom',2,None)),
                (2,tag('atom',3,None)),
                (3,tag('atom',2,None)),
                (2,'none'),
                (0,tag('(.integer ⟨1,false,true⟩)',None,0)),
            ]:
                bad=baseline.copy();bad[index]=replacement;malformed.append(bad)
            for index,bad in enumerate(malformed):
                checks.extend([f'def bad{index} : Forest := ⟨[{",".join(bad)}]⟩',
                    f'#guard !bad{index}.wellFormed',f'#guard bad{index}.retireScope 1 == none',
                    f'#guard bad{index}.transfer 1 row 1 0 == none'])
            checks.extend(['#guard f2.rootOwner 100 == none',
                '#guard (f2.retired 1).objects.length == f2.objects.length',
                '#guard (f2.retired 1).lookup 2 == none',
                '#guard (f2.retired 1).lookup 0 == f2.lookup 0'])
            self.lean(scratch,'\n'.join(checks))
            cpp=scratch/'native.cpp';cpp.write_text('''#include "experiments/library/cpp/template/small_template.hpp"
#include <vector>
#include <cassert>
#include <utility>
std::vector<std::vector<int>> make(unsigned n){
 std::vector<std::vector<int>> result(n);
 std::vector<std::vector<std::vector<int>>> scratch(1,std::vector<std::vector<int>>(1,std::vector<int>{91}));
 for(unsigned i=0;i<n;++i)result[i]={int(i),7,-2};
 assert(scratch[0][0][0]==91);
 return result;
}
int main(){for(unsigned n=0;n<=16;++n){
 std::vector<int> caller{19};auto result=make(n);
 std::vector<const int*> addresses;for(auto& r:result)addresses.push_back(r.data());
 auto moved=std::move(result);
 assert(caller==std::vector<int>{19} && moved.size()==n);
 for(unsigned i=0;i<n;++i){assert(moved[i].data()==addresses[i]);assert(moved[i]==std::vector<int>({int(i),7,-2}));}
}}
''')
            check_compiler()
            for elision in [[],['-fno-elide-constructors']]:
                binary=scratch/'native'
                subprocess.run(['g++',*FLAGS,*elision,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(cpp),'-o',str(binary)],cwd=ROOT,check=True)
                environment=os.environ.copy()
                environment["ASAN_OPTIONS"]="detect_leaks=0:halt_on_error=1"
                environment["UBSAN_OPTIONS"]="halt_on_error=1:print_stacktrace=1"
                subprocess.run([str(binary)],env=environment,check=True)
            print(f'ownership: {sum(x.count("#guard") for x in checks)} Lean guards, 34 native return/move sequences, 12 invalid forests')

    def test_model_mutations_reject_lost_descendants_and_wrong_scope(self):
        with tempfile.TemporaryDirectory(prefix='ownership-mutation-') as directory:
            scratch=Path(directory)
            baseline=(ROOT/'Proofs/CppVectorOwnership.lean').read_text().replace('namespace Proofs.CppVectorOwnership','namespace Proofs.OwnershipMutation').replace('end Proofs.CppVectorOwnership','end Proofs.OwnershipMutation')
            self.lean(scratch,baseline)
            retire='if f.context owner = some scope then none else tag'
            transfer='tag.scope = some fromScope ∧ tag.element = expected'
            self.assertEqual(baseline.count(retire),1);self.assertEqual(baseline.count(transfer),1)
            self.lean(scratch,baseline.replace(retire,'if (tag.bind (·.scope)) = some scope then none else tag'),False)
            self.lean(scratch,baseline.replace(transfer,'tag.scope.isSome = true ∧ tag.element = expected'),False)

if __name__=='__main__':disable_network();unittest.main()
