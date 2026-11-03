"""Whole straight-line C++ bodies generated from audited vector operations."""
import copy
import itertools
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
from vector_ir import lower_source,emit_lean
from test_scalar_ir import lean_environment
from check_public import FLAGS,check_compiler
from offline import disable_network

SOURCE='''#include <vector>
namespace cp {
unsigned long mutate(std::vector<int>& v,unsigned long n,int x,int& counter){
 int old=v[0];v.reserve(n);v[0]=x;v.push_back(old);counter=old;return v.size();
}
unsigned long count(const std::vector<int>& v){return v.size();}
int read(const std::vector<int>& v,unsigned long i){return v[i];}
int twice(const std::vector<int>& v){return v[0]+v[0];}
}'''
HEADER='''
open Proofs.CppScalar Proofs.CppMixedInvoke
 def i32 : Ty := ⟨32,true,false⟩
 def u64 : Ty := ⟨64,false,false⟩
 def caller (values : List Int) : State := ⟨⟨[⟨i32,123⟩],[⟨0,true⟩],0,1,0⟩,
  ⟨⟨[some ⟨0,values,values.length,100,0⟩],0,0,values.length+1⟩,[⟨i32,true⟩],[⟨0,i32,true⟩],0⟩,
  [.scalar 0,.vector 0],0⟩
 def mutate (values : List Int) (n : Nat) (x : Int) : Option State :=
  VectorProgramInstances.mutate.call (caller values)
  [.vectorReference 0,.value (.literal u64 n),.value (.literal i32 x),.scalarReference 0]
'''

class VectorIRTests(unittest.TestCase):
    def lean(self,scratch,text,succeeds=True):
        path=scratch/'checks.lean';path.write_text(text)
        lake,env=lean_environment()
        result=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,capture_output=True,text=True)
        self.assertEqual(result.returncode==0,succeeds,result.stdout+result.stderr)

    def test_generated_bodies_native_results_costs_and_rejections(self):
        with tempfile.TemporaryDirectory(prefix='vector-body-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            ir=lower_source(source)
            self.assertEqual(ir['coverage'],'straight_line_scalar_return')
            checks=[emit_lean(ir),HEADER]
            native=['#include "experiments/library/cpp/template/small_template.hpp"',
                    '#include "source.hpp"','#include <cassert>','int main(){']
            count=0
            for length in range(1,5):
                for values in itertools.product([-3,0,7],repeat=length):
                    # All small value tuples; exercise both spare capacities.
                    for extra in [1,3]:
                        n=length+extra;x=[-2147483648,17,2147483647][count%3]
                        old=values[0];expected=[x,*values[1:],old]
                        lean_values='['+','.join(map(str,values))+']'
                        checks.append(f'def result{count} := mutate {lean_values} {n} ({x})')
                        checks.append(f'#guard (result{count}.map (·.scalars.memory)) == some [⟨i32,({old})⟩,⟨u64,{length+1}⟩]')
                        expected_values='['+','.join(map(str,expected))+']'
                        checks.append(f'#guard (result{count}.map (·.vectors.store.objects)) == some [some ⟨0,{expected_values},{n},100,1⟩]')
                        checks.append(f'#guard (result{count}.map (·.work)) == some {length+32}')
                        checks.append(f'#guard (result{count}.map (·.peak)) == some {n+17}')
                        cpp_values=','.join(map(str,values));cpp_expected=','.join(map(str,expected))
                        native.append(f'{{std::vector<int> v{{{cpp_values}}};int counter=123;'
                            f'assert(cp::mutate(v,{n}UL,{x},counter)=={length+1}UL);'
                            f'assert(counter=={old} && v==std::vector<int>({{{cpp_expected}}}) && v.capacity()=={n});'
                            f'assert(cp::count(v)=={length+1}UL && cp::read(v,0)=={x});}}')
                        count+=1
            checks.extend(['#guard mutate [] 3 7 == none',
                '#guard mutate [3,8] 2 7 == none',
                '#guard mutate [3,8] 101 7 == none',
                '#guard mutate [3,8] 5 2147483648 == none',
                '#guard VectorProgramInstances.read.call (caller [3,8]) [.vectorReference 0,.value (.literal u64 2)] == none',
                '#guard VectorProgramInstances.read.call (caller [3,8]) [.vectorReference 0,.value (.literal u64 18446744073709551615)] == none',
                '#guard (VectorProgramInstances.count.call (caller []) [.vectorReference 0] |>.map (·.scalars.environment)) == some (some [123,0])',
                '#guard (VectorProgramInstances.twice.call (caller [7]) [.vectorReference 0] |>.map (·.scalars.environment)) == some (some [123,14])',
                '#guard VectorProgramInstances.twice.call (caller [2147483647]) [.vectorReference 0] == none'])
            self.lean(scratch,'\n'.join(checks))
            native.append('}')
            cpp=scratch/'native.cpp';cpp.write_text('\n'.join(native));executable=scratch/'native'
            check_compiler()
            subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all',
                            '-I',str(ROOT),str(cpp),'-o',str(executable)],cwd=ROOT,check=True)
            subprocess.run([str(executable)],check=True)
        print(f'vector body: {count*4+9} Lean checks and {count} C++17 UBSan call sequences')

    def test_names_mutations_and_unsupported_nodes(self):
        with tempfile.TemporaryDirectory(prefix='vector-body-mutation-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            original=lower_source(source)
            renamed_text=SOURCE.replace('mutate','renamed').replace(' old',' previous').replace('(old)','(previous)').replace('=old','=previous')
            source.write_text(renamed_text)
            renamed=lower_source(source);expected=copy.deepcopy(original);expected['functions'][0]['name']='renamed'
            self.assertEqual(renamed,expected)
            guard='\n#guard (mutate [3,8] 5 17 |>.map (·.vectors.store.objects)) == some [some ⟨0,[17,8,3],5,100,1⟩]\n'
            self.lean(scratch,emit_lean(original)+HEADER+guard)
            for before,after in [('v[0]=x','v[0]=x+1'),('v.push_back(old)','v.push_back(x)'),('int old=v[0]','int old=v[1]')]:
                with self.subTest(mutation=after):
                    source.write_text(SOURCE.replace(before,after));changed=lower_source(source)
                    self.assertNotEqual(changed,original)
                    self.lean(scratch,emit_lean(changed)+HEADER+guard,False)
            negatives=[
                'unsigned long f(std::vector<int>& v){while(v.size()>0){continue;}return v.size();}',
                'unsigned long f(std::vector<int>& v){if(int x=1;v.size()>0)return x;return 0;}',
                'unsigned long f(std::vector<int>& v){std::vector<int> copy(v);return copy.size();}',
                'int f(std::vector<int>& v){int& ref=v[0];return ref;}',
                'int f(std::vector<int>& v){return ++v[0];}',
                'int f(std::vector<int>& v){return v[0]++;}',
                'int f(std::vector<int>& v){return (v[0]=1);}',
                'unsigned long helper(){return 1;} unsigned long f(std::vector<int>& v){return v.size()+helper();}',
                'int f(std::vector<int>& v){return v.at(0);}',
                'std::vector<int> f(const std::vector<int>& v){return v;}',
            ]
            for text in negatives:
                source.write_text('#include <vector>\n'+text)
                with self.subTest(source=text),self.assertRaises(ValueError):lower_source(source)
            with self.assertRaises(ValueError):
                lower_source(ROOT/'library/doubling.hpp')
        print('vector body: rename invariance, three source mutations rejected, 11 unsupported body profiles (compound assignment is desugared by verifier/inline_ast.py)')

if __name__=='__main__':
    disable_network();unittest.main()
