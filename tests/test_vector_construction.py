"""Audited fill constructors, canonical local types and lexical destruction."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'));sys.path.insert(0,str(ROOT/'tools'))
from vector_ir import lower_source,emit_lean
from test_scalar_ir import lean_environment
from check_public import FLAGS,check_compiler
from offline import disable_network

SOURCE='''#include <vector>
unsigned long fill(unsigned long n,int value){std::vector<int> local(n,value);return local.size();}
unsigned long scoped(unsigned long n,int value,int& out){
 {std::vector<int> a(n,value);out=a[0];}
 {const std::vector<int> b(n+1,value+1);out=b[0];}
 return n;
}
unsigned long early(unsigned long n,int value){
 {std::vector<int> a(n,value);return a.size();}return 0;
}
'''
HEADER='''
open Proofs.CppScalar Proofs.CppMixedInvoke
 def i32 : Ty := ⟨32,true,false⟩
 def u64 : Ty := ⟨64,false,false⟩
 def empty : State := ⟨⟨[],[],0,0,0⟩,⟨⟨[],0,0,0⟩,[],[],0⟩,[],0⟩
 def caller : State := {empty with scalars := ⟨[⟨i32,123⟩],[⟨0,true⟩],0,1,0⟩,slots := [.scalar 0]}
 def args (n : Nat) (value : Int) : List Argument := [.value (.literal u64 n),.value (.literal i32 value)]
'''

class ConstructionTests(unittest.TestCase):
    def lean(self,scratch,text):
        path=scratch/'checks.lean';path.write_text(text);lake,env=lean_environment()
        result=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_fill_scopes_returns_costs_and_tombstones(self):
        repeated='unsigned long repeated(unsigned long n,int value,int& out){'+(
            '{std::vector<int> local(n,value);out=local[0];}'*20)+'return n;}'
        with tempfile.TemporaryDirectory(prefix='vector-construction-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE+repeated)
            ir=lower_source(source);checks=[emit_lean(ir),HEADER]
            native=['#include "experiments/library/cpp/template/small_template.hpp"',
                    '#include "source.hpp"','#include <cassert>','int main(){']
            count=0
            # fill: scalar work13 + vector (n+3); peak scalar8 +
            # vector (n+4), including Frame.size's temporary.
            for n in range(9):
                for value in [-2147483648,-3,0,7,2147483647]:
                    name=f'r{count}'
                    checks.append(f'def {name} := VectorProgramInstances.fill.call empty (args {n} ({value}))')
                    checks.append(f'#guard ({name}.map (·.scalars.environment)) == some (some [{n}])')
                    checks.append(f'#guard ({name}.map (·.vectors.store.objects)) == some [none]')
                    checks.append(f'#guard ({name}.map (·.work)) == some {n+16}')
                    checks.append(f'#guard ({name}.map (·.peak)) == some {n+12}')
                    native.append(f'assert(fill({n}UL,{value})=={n}UL);')
                    count+=1
            # scoped: scalar work35 + vector (2*n+7). The unsigned n+1
            # has Clang's extra literal conversion. Peak scalar15 + vector(n+5).
            for n in range(1,9):
                for value in [-3,0,7]:
                    name=f's{count}'
                    checks.append(f'def {name} := VectorProgramInstances.scoped.call caller (args {n} ({value}) ++ [.scalarReference 0])')
                    checks.append(f'#guard ({name}.map (·.scalars.memory)) == some [⟨i32,({value+1})⟩,⟨u64,{n}⟩]')
                    checks.append(f'#guard ({name}.map (·.vectors.store.objects)) == some [none,none]')
                    checks.append(f'#guard ({name}.map (·.vectors.types)) == some [⟨i32,true⟩,⟨i32,false⟩]')
                    checks.append(f'#guard ({name}.map (·.work)) == some {2*n+42}')
                    checks.append(f'#guard ({name}.map (·.peak)) == some {n+20}')
                    native.append(f'{{int out=123;assert(scoped({n}UL,{value},out)=={n}UL && out=={value+1});}}')
                    count+=1
            checks.extend([
                'def earlyResult := VectorProgramInstances.early.call empty (args 3 7)',
                '#guard (earlyResult.map (·.scalars.environment)) == some (some [3])',
                '#guard (earlyResult.map (·.vectors.store.objects)) == some [none]',
                '#guard (earlyResult.map (·.work)) == some 20',
                '#guard (earlyResult.map (·.peak)) == some 15',
                'def repeatedResult := VectorProgramInstances.repeated.call caller (args 2 7 ++ [.scalarReference 0])',
                '#guard (repeatedResult.map (·.vectors.store.objects)) == some (List.replicate 20 none)',
                '#guard (repeatedResult.map (fun s => s.vectors.types.length)) == some 20',
                '#guard (repeatedResult.map (·.peak)) == some 16',
                '#guard VectorProgramInstances.scoped.call caller (args 0 7 ++ [.scalarReference 0]) == none',
                '#guard VectorProgramInstances.fill.call empty (args 2305843009213693952 7) == none',
                '#guard VectorProgramInstances.fill.call empty (args 3 2147483648) == none'])
            native.append('assert(early(3,7)==3);int out=123;assert(repeated(2,7,out)==2 && out==7);}')
            self.lean(scratch,'\n'.join(checks))
            cpp=scratch/'native.cpp';cpp.write_text('\n'.join(native));exe=scratch/'native'
            check_compiler()
            subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all',
                '-I',str(ROOT),str(cpp),'-o',str(exe)],cwd=ROOT,check=True)
            subprocess.run([str(exe)],check=True)
        print('constructors/scopes: 310 Lean checks, 71 C++17 UBSan calls and twenty lexical lifetimes')

    def test_specializations_fake_types_and_macro_probes_are_rejected(self):
        negatives=[
            '#include <vector>\ntemplate<> std::vector<int>::vector(size_type n,const value_type& v,const allocator_type& a){}\n'+SOURCE.split('\n',1)[1],
            '#include <vector>\ntemplate<> void std::vector<int>::_M_fill_initialize(size_type n,const value_type& v){}\n'+SOURCE.split('\n',1)[1],
            '#include <vector>\ntemplate<> std::vector<int>::~vector(){}\n'+SOURCE.split('\n',1)[1],
            '#include <vector>\n#define __is_same(...) true\n'+SOURCE.split('\n',1)[1],
            '#include <vector>\nnamespace fake{template<class T>struct vector{using size_type=unsigned long;using value_type=T;using allocator_type=::std::allocator<T>;vector(size_type,const value_type&,const allocator_type& = allocator_type()){} };}\nnamespace cp{namespace std=fake;int f(){std::vector<int> v(2,7);return 0;}}',
            '#include <vector>\nunsigned long f(){std::vector<int> v{2,7};return v.size();}',
            '#include <vector>\nunsigned long f(){std::vector<int> v(2,7,std::allocator<int>());return v.size();}',
        ]
        with tempfile.TemporaryDirectory(prefix='vector-constructor-negative-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp'
            for text in negatives:
                source.write_text(text)
                with self.subTest(source=text),self.assertRaises(ValueError):lower_source(source)
        print('constructor identity: seven specialization/type/macro/overload/allocator negatives')

if __name__=='__main__':
    disable_network();unittest.main()
